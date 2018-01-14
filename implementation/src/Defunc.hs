{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Defunc ( StaticVal(..)
              , defunc
              , runDefM
              , defuncStr
              , defuncExpr
              ) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Parser
import Syntax

-- Type of data storing additional information about the result of
-- defunctionalization of an expression, aside from the residual expression.
data StaticVal = Dynamic Tp
               | Lambda Name Tp Expr Env
               | Tuple StaticVal StaticVal
               | Rcd [(Name, StaticVal)]
  deriving (Show, Eq)

isDynamic :: StaticVal -> Bool
isDynamic (Dynamic _) = True
isDynamic _           = False

-- Environment mapping variable names to their associated static value.
type Env = [(Name, StaticVal)]

emptyEnv :: Env
emptyEnv = []

extendEnv :: Name -> StaticVal -> Env -> Env
extendEnv x sv env = (x, sv) : env

extendEnvList :: [(Name, StaticVal)] -> Env -> Env
extendEnvList = (++)

-- Generates a nested sequence of let-bindings, binding the free
-- variables to the corresponding fields in a record.
letBindFV :: Name -> Env -> Expr -> Expr
letBindFV _ []            e = e
letBindFV x ((y, _) : ys) e = Let y [] (Select (Var x) y) $ letBindFV x ys e


-- Defunctionalization monad.
newtype DefM a = DefM (ReaderT Env
                        (WriterT [Expr -> Expr]
                          (State Int)) a)
  deriving (Monad, Functor, Applicative,
            MonadReader Env,
            MonadWriter [Expr -> Expr],
            MonadState Int)

runDefM :: DefM (Expr, StaticVal) -> Expr
runDefM (DefM m) = foldr (.) id bindings expr
  where ((expr, _), bindings) = evalState (runWriterT $ runReaderT m emptyEnv) 0

-- Looks up the associated static value and type of a given name.
lookupVar :: Name -> DefM StaticVal
lookupVar x = do env <- ask
                 case lookup x env of
                   Just v  -> return v
                   Nothing -> error $ "variable " ++ x ++ " is out of scope"

-- Generates a fresh variable name based on a given name.
freshVar :: Name -> DefM Name
freshVar x = do s <- get
                put (s+1)
                return $ x ++ show s

-- Given a static value, compute the type of the residual expression.
typeFromSV :: StaticVal -> Tp
typeFromSV (Dynamic tp)       = tp
typeFromSV (Lambda _ _ _ env) = TpRecord $ map (\(x, sv) -> (x, typeFromSV sv)) env
typeFromSV (Tuple sv1 sv2)    = TpPair (typeFromSV sv1) (typeFromSV sv2)
typeFromSV (Rcd ls)           = TpRecord $ map (\(x, sv) -> (x, typeFromSV sv)) ls


-- Main defunctionalization function. Given an expression, returns an equivalent
-- expression without any higher-order subexpression, and the associated static
-- value in the DefM monad. The input expression is expected to be well typed.
defunc :: Expr -> DefM (Expr, StaticVal)
defunc expr = case expr of
  Var x             -> do sv <- lookupVar x
                          return (expr, sv)

  Num _             -> return (expr, Dynamic TpInt)
  TrueLit           -> return (expr, Dynamic TpBool)
  FalseLit          -> return (expr, Dynamic TpBool)

  Add e1 e2         -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          unless (isDynamic sv1 && isDynamic sv2)
                                 (error $ "binary operation \"" ++ show (pretty expr)
                                       ++ "\" expected dynamic operands")
                          return (Add e1' e2', Dynamic TpInt)

  LEq e1 e2         -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          unless (isDynamic sv1 && isDynamic sv2)
                                 (error $ "binary operation \"" ++ show (pretty expr)
                                       ++ "\" expected dynamic operands")
                          return (LEq e1' e2', Dynamic TpBool)


  If e1 e2 e3       -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          (e3', sv3) <- defunc e3
                          unless (all isDynamic [sv1, sv2, sv3])
                                 (error $ "conditional \"" ++ show (pretty expr)
                                       ++ "\" expected dynamic operands")
                          return (If e1' e2' e3', sv2)

  Lam x tp e0       -> do let fv = freeVars expr
                          svsTps <- mapM lookupVar fv
                          return (Record $ map (\v -> (v, Var v)) fv,
                                  Lambda x tp e0 $ zip fv svsTps)

  App e1 e2         -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          case sv1 of
                            Lambda x tp e0 fv -> do
                              (e0', sv) <- local (extendEnv x sv2
                                                   . extendEnvList fv) (defunc e0)
                              -- Lift lambda to top-level function with a fresh name.
                              f <- freshVar "_f"
                              tell [ Let f [("env", typeFromSV sv1), (x, tp)]
                                         (letBindFV "env" fv e0')
                                   ]
                              return (App (App (Var f) e1') e2', sv)

                            _ -> error $ "application of an expression that is neither a "
                                      ++ "static lambda nor a dynamic functions, but a "
                                      ++ show sv1 ++ ": " ++ show (pretty expr)

  Let x _ e1 e2     -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- local (extendEnv x sv1) (defunc e2)
                          return (Let x [] e1' e2', sv2)

  Pair e1 e2        -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          return (Pair e1' e2', Tuple sv1 sv2)

  Fst e0            -> do (e0', sv0) <- defunc e0
                          case sv0 of
                            Tuple sv1 _ -> return (Fst e0', sv1)
                            Dynamic _   -> return (Fst e0', sv0)
                            _ -> error $ "projection of an expression that is neither "
                                      ++ "dynamic nor a statically known pair"

  Snd e0            -> do (e0', sv0) <- defunc e0
                          case sv0 of
                            Tuple _ sv2 -> return (Snd e0', sv2)
                            Dynamic _   -> return (Snd e0', sv0)
                            _ -> error $ "projection of an expression that is neither "
                                      ++ "dynamic nor a statically known pair"

  Select e0 l       -> do (e0', sv0) <- defunc e0
                          case sv0 of
                            Dynamic _ -> return (expr, sv0)
                            Rcd svs   -> case lookup l svs of
                              Just sv -> return (Select e0' l, sv)
                              Nothing -> error "invalid record selection"
                            _ -> error $ "record selection of a " ++ show sv0

  Record ls         -> do ls'' <- mapM (\(x,e) -> do (e', sv) <- defunc e
                                                     return ((x, e'), (x, sv))
                                       ) ls
                          let (ls', svs) = unzip ls''
                          return (Record ls', Rcd svs)

  ArrayLit es       -> do (es', svs) <- unzip <$> mapM defunc es
                          unless (all isDynamic svs)
                            $ error "array literal with static element(s)"
                          case svs of
                            (Dynamic tp : _) -> return (ArrayLit es', Dynamic (TpArray tp))
                            _                -> error $ "type error: " ++ show (pretty expr)

  Index e1 e2       -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          unless (isDynamic sv1 && isDynamic sv2)
                                 (error $ "binary operation \"" ++ show (pretty expr)
                                       ++ "\" expected dynamic operands")
                          case sv1 of
                            Dynamic (TpArray tp) ->
                              return (Index e1' e2', Dynamic tp)
                            _ -> error $ "type error: " ++ show (pretty expr)

  Update e1 e2 e3   -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          (e3', sv3) <- defunc e3
                          unless (all isDynamic [sv1, sv2, sv3])
                                 (error $ "array update \"" ++ show (pretty expr)
                                       ++ "\" expected dynamic operands")
                          return (Update e1' e2' e3', sv1)

  Length e1         -> do (e1', sv1) <- defunc e1
                          unless (isDynamic sv1)
                            $ error "non-dynamic argument to length"
                          return (Length e1', Dynamic TpInt)

  Loop x e1 y e2 e3 -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          (e3', sv3) <- defunc e3
                          unless (all isDynamic [sv1, sv2, sv3])
                            $ error "loop with static operand(s)"
                          return (Loop x e1' y e2' e3', sv3)

defuncExpr :: Expr -> Expr
defuncExpr = runDefM . defunc

-- Skips type checking. Convenient for testing.
defuncStr :: String -> IO ()
defuncStr s = case parseString s of
  Left parseErr -> print parseErr
  Right e       -> print . pretty . runDefM $ defunc e
