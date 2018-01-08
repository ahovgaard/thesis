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
import TypeChecker

-- Type of data storing additional information about the result of
-- defunctionalization of an expression, aside from the residual expression.
data StaticVal = Dynamic
               | Lambda Name Tp Expr Env
               | Tuple StaticVal StaticVal
               | Rcd [(Name, StaticVal)]
               | DynamicFun (Expr, StaticVal) StaticVal
  deriving (Show, Eq)

-- Environment mapping variable names to their associated static value and type.
type Env = [(Name, (StaticVal, Tp))]

emptyEnv :: Env
emptyEnv = []

extendEnv :: Name -> StaticVal -> Tp -> Env -> Env
extendEnv x sv tp env = (x, (sv, tp)) : env

extendEnvList :: [(Name, (StaticVal, Tp))] -> Env -> Env
extendEnvList = (++)

-- Generates a nested sequence of let-bindings, binding the free
-- variables to the corresponding fields in a record.
letBindFV :: Name -> Env -> Expr -> Expr
letBindFV _ []            e = e
letBindFV x ((y, _) : ys) e = Let y (Select (Var x) y) $ letBindFV x ys e


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
lookupVar :: Name -> DefM (StaticVal, Tp)
lookupVar x = do env <- ask
                 case lookup x env of
                   Just v  -> return v
                   Nothing -> error $ "variable " ++ x ++ " is out of scope"

-- Looks up a variable in the environment and returns the associated residual
-- expression along with its static value and its type. If the variable denotes
-- a first-order let-bound function, the corresponding closure and its static
-- value is returned, instead of the static value of the function variable.
lookupFV :: Name -> DefM (Expr, StaticVal, Tp)
lookupFV x = do (sv, tp) <- lookupVar x
                case sv of
                  DynamicFun (e, sv')  _ -> return (e, sv', tp)
                  _                      -> return (Var x, sv, tp)

-- Generates a fresh variable name based on a given name.
freshVar :: Name -> DefM Name
freshVar x = do s <- get
                put (s+1)
                return $ x ++ show s

-- Given an environment, construct a corresponding record type for storing the
-- values of the environment.
typeFromEnv :: Env -> Tp
typeFromEnv = TpRecord . map (\(x, (_, tp)) -> (x, tp))

-- Main defunctionalization function. Given an expression, returns an equivalent
-- expression without any higher-order subexpression, and the associated static
-- value in the DefM monad. The input expression is expected to be well typed.
defunc :: Expr -> DefM (Expr, StaticVal)
defunc expr = case expr of
  Var x             -> do (sv, _) <- lookupVar x
                          case sv of
                            -- A variable denoting a dynamic function translates
                            -- to the corresponding closure reresentation, while
                            -- any other variable stays unchanged.
                            DynamicFun clsr _ -> return clsr
                            _                 -> return (expr, sv)

  Num _             -> return (expr, Dynamic)
  TrueLit           -> return (expr, Dynamic)
  FalseLit          -> return (expr, Dynamic)

  Add e1 e2         -> defuncBinOp  Add e1 e2
  LEq e1 e2         -> defuncBinOp  LEq e1 e2
  If e1 e2 e3       -> defuncTernOp If  e1 e2 e3

  Lam x tp e0       -> do let fv  = freeVars expr
                          (envVals, svs, tps) <- unzip3 <$> mapM lookupFV fv
                          return (Record (zip fv envVals),
                                  Lambda x tp e0 (zip fv (zip svs tps)))

  App e1 e2         -> do (e1', sv1) <- defuncDynFunVar e1
                          (e2', sv2) <- defunc e2
                          case sv1 of
                            Lambda x tp e0 fv -> do
                              (e0', sv) <- local (extendEnv x sv2 tp
                                                   . extendEnvList fv) (defunc e0)
                              -- Lift lambda to top-level function with a fresh name.
                              f <- freshVar "_f"
                              tell [Let f
                                     $ Lam "env" (typeFromEnv fv)
                                     $ Lam x tp (letBindFV "env" fv e0')
                                   ]
                              return (App (App (Var f) e1') e2', sv)

                            -- In the case of an application of a first-order
                            -- let-bound function, just leave the application in place.
                            DynamicFun _ sv ->
                              case sv2 of Dynamic -> return (App e1' e2', sv)
                                          _ -> error $ "expected dynamic argument to "
                                                    ++ "let-bound first-order function, "
                                                    ++ "but received a " ++ show sv2

                            _ -> error $ "application of an expression that is neither a "
                                      ++ "static lambda nor a dynamic functions, but a "
                                      ++ show sv1

  Let x e1 e2       -> do (e1', sv1) <- defuncLet e1
                          env <- ask
                          -- If x is a first-order function and it is captured,
                          -- then its type will be that of its closure
                          -- representation rather than its functional type.
                          let tp1 = typeOf (map (\(y, (_, tp)) -> (y, tp)) env)
                                           (case sv1 of
                                              DynamicFun (clsr, _) _ -> clsr
                                              _                      -> e1')
                          case tp1 of
                            Left tpErr -> error $ "type error: " ++ show tpErr
                            Right tp1' -> do
                              (e2', sv)  <- local (extendEnv x sv1 tp1') (defunc e2)
                              return (Let x e1' e2', sv)

  Pair e1 e2        -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          return (Pair e1' e2', Tuple sv1 sv2)

  Fst e0            -> do (e0', sv0) <- defunc e0
                          case sv0 of
                            Tuple sv1 _ -> return (Fst e0', sv1)
                            Dynamic     -> return (Fst e0', sv0)
                            _ -> error $ "projection of an expression that is neither "
                                      ++ "dynamic nor a statically known pair"

  Snd e0            -> do (e0', sv0) <- defunc e0
                          case sv0 of
                            Tuple _ sv2 -> return (Snd e0', sv2)
                            Dynamic     -> return (Snd e0', sv0)
                            _ -> error $ "projection of an expression that is neither "
                                      ++ "dynamic nor a statically known pair"

  Select e0 l       -> do (e0', sv0) <- defunc e0
                          case sv0 of
                            Dynamic -> return (expr, Dynamic)
                            Rcd svs -> case lookup l svs of
                              Just sv -> return (Select e0' l, sv)
                              Nothing -> error "invalid record selection"
                            _ -> error $ "record selection of a " ++ show sv0

  Record ls         -> do ls'' <- mapM (\(x,e) -> do (e', sv) <- defunc e
                                                     return ((x, e'), (x, sv))
                                       ) ls
                          let (ls', svs) = unzip ls''
                          return (Record ls', Rcd svs)

  ArrayLit es       -> do (es', svs) <- unzip <$> mapM defunc es
                          unless (all (== Dynamic) svs)
                            $ error "array literal with static element(s)"
                          return (ArrayLit es', Dynamic)

  Index e1 e2       -> defuncBinOp  Index  e1 e2
  Update e1 e2 e3   -> defuncTernOp Update e1 e2 e3

  Length e1         -> do (e1', sv1) <- defunc e1
                          unless (sv1 == Dynamic)
                            $ error "non-dynamic argument to length"
                          return (Length e1', Dynamic)

  Loop x e1 y e2 e3 -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          (e3', sv3) <- defunc e3
                          unless (all (== Dynamic) [sv1, sv2, sv3])
                            $ error "loop with static operand(s)"
                          return (Loop x e1' y e2' e3', Dynamic)

defuncBinOp :: (Expr -> Expr -> Expr) -> Expr -> Expr -> DefM (Expr, StaticVal)
defuncBinOp cons e1 e2 = do
  (e1', sv1) <- defunc e1
  (e2', sv2) <- defunc e2
  unless (sv1 == Dynamic && sv2 == Dynamic)
         (error $ "binary operation \"" ++ show (cons e1 e2)
               ++ "\" expected dynamic operands")
  return (cons e1' e2', Dynamic)

defuncTernOp :: (Expr -> Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
             -> DefM (Expr, StaticVal)
defuncTernOp cons e1 e2 e3 = do
  (e1', sv1) <- defunc e1
  (e2', sv2) <- defunc e2
  (e3', sv3) <- defunc e3
  unless (sv1 == Dynamic && sv2 == Dynamic && sv3 == Dynamic)
         (error $ "ternary operation \"" ++ show (pretty (cons e1 e2 e3))
               ++ "\" expected dynamic operands")
  return (cons e1' e2' e3', Dynamic)

-- Keep let-bound first-order lambdas intact.
defuncLet :: Expr -> DefM (Expr, StaticVal)
defuncLet expr@(Lam x tp e0)
  | order tp == 0 = do (e0', sv0) <- local (extendEnv x Dynamic tp) (defuncLet e0)
                       clsr       <- defunc expr
                       return (Lam x tp e0', DynamicFun clsr sv0)
defuncLet expr    = defunc expr

-- Avoid translating a dynamic function variable into its static
-- closure. Used in the case for application.
defuncDynFunVar :: Expr -> DefM (Expr, StaticVal)
defuncDynFunVar expr = case expr of
                         Var x -> do (sv, _) <- lookupVar x
                                     return (expr, sv)
                         _     -> defunc expr

defuncExpr :: Expr -> Expr
defuncExpr = runDefM . defunc

-- Skips type checking. Convenient for testing.
defuncStr :: String -> IO ()
defuncStr s = case parseString s of
  Left parseErr -> print parseErr
  Right e       -> print . pretty . runDefM $ defunc e
