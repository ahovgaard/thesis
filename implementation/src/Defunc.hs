{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Defunc where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Parser
import Syntax

data StaticVal = Dynamic
               | Lambda Name Tp Expr [(Name, StaticVal)]
               | Tuple StaticVal StaticVal
               | Rcd [(Name, StaticVal)]
               | DynamicFun (Expr, StaticVal) StaticVal
  deriving (Show, Eq)

-- Environment mapping variable names to static values.
type Env = [(Name, StaticVal)]

emptyEnv :: Env
emptyEnv = []

extendEnv :: Name -> StaticVal -> Env -> Env
extendEnv x sv env = (x, sv) : env

extendEnvList :: [(Name, StaticVal)] -> Env -> Env
extendEnvList = (++)

-- Generates a nested sequence of let-bindings, binding the free
-- variables to the corresponding fields in a record.
letBindFV :: Name -> [Name] -> Expr -> Expr
letBindFV _ []     e = e
letBindFV x (y:ys) e = Let y (Select (Var x) y) $ letBindFV x ys e


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

execDefM :: DefM (Expr, StaticVal) -> StaticVal
execDefM (DefM m) = sv
  where ((_, sv), _) = evalState (runWriterT $ runReaderT m emptyEnv) 0

lookupStaticVal :: Name -> DefM StaticVal
lookupStaticVal x = do env <- ask
                       case lookup x env of
                         Just sv -> return sv
                         Nothing -> error $ "variable " ++ x ++ " is out of scope"

freshVar :: Name -> DefM Name
freshVar x = do s <- get
                put (s+1)
                return $ x ++ show s

defunc :: Expr -> DefM (Expr, StaticVal)
defunc expr = case expr of
  Var x             -> do sv <- lookupStaticVal x
                          case sv of
                            -- A variable denoting a dynamic function translates
                            -- to the corresponding closure reresentation, while
                            -- any other variable stays unchanged.
                            DynamicFun clsr _ -> return clsr
                            _                 -> return (expr, sv)

  Num _             -> return (expr, Dynamic)
  TrueLit           -> return (expr, Dynamic)
  FalseLit          -> return (expr, Dynamic)

  Add e1 e2         -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          unless (sv1 == Dynamic && sv2 == Dynamic)
                            $ error "addition with static operand(s)"
                          return (Add e1' e2', Dynamic)

  LEq e1 e2         -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          unless (sv1 == Dynamic && sv2 == Dynamic)
                            $ error "less-than or equal with static operand(s)"
                          return (LEq e1' e2', Dynamic)

  If e1 e2 e3       -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          (e3', sv3) <- defunc e3
                          unless (sv1 == Dynamic && sv2 == Dynamic && sv3 == Dynamic)
                            $ error "conditional with static operand(s)"
                          return (If e1' e2' e3', Dynamic)

  Lam x tp e0       -> do let fv  = freeVars expr
                          (envVals, svs) <- unzip <$> mapM (defunc . Var) fv
                          return (Record (zip fv envVals),
                                  Lambda x tp e0 (zip fv svs))

  App e1 e2         -> do (e1', sv1) <- defuncDynFunVar e1
                          (e2', sv2) <- defunc e2
                          case sv1 of
                            Lambda x tp e0 fv -> do
                              (e0', sv) <- local (extendEnv x sv2 . extendEnvList fv)
                                                 (defunc e0)
                              -- Lift lambda to top-level function with a fresh name.
                              f <- freshVar "_f"
                              tell [Let f
                                     $ Lam "env" TpInt  -- TODO: type of env
                                     $ Lam x tp (letBindFV "env" (map fst fv) e0')
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
                          (e2', sv)  <- local (extendEnv x sv1) (defunc e2)
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

  Index e1 e2       -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          unless (sv1 == Dynamic && sv2 == Dynamic)
                            $ error "array indexing with static operand(s)"
                          return (Index e1' e2', Dynamic)

  Update e1 e2 e3   -> do (e1', sv1) <- defunc e1
                          (e2', sv2) <- defunc e2
                          (e3', sv3) <- defunc e3
                          unless (all (== Dynamic) [sv1, sv2, sv3])
                            $ error "array update with static operand(s)"
                          return (Update e1' e2' e3', Dynamic)

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

-- Keep let-bound first-order lambdas intact.
defuncLet :: Expr -> DefM (Expr, StaticVal)
defuncLet expr@(Lam x tp e0)
  | order tp == 0 = do (e0', sv0) <- local (extendEnv x Dynamic) (defuncLet e0)
                       clsr       <- defunc expr
                       return (Lam x tp e0', DynamicFun clsr sv0)
defuncLet expr    = defunc expr

-- Avoid translating a dynamic function variable into its static
-- closure. Used in the case for application.
defuncDynFunVar :: Expr -> DefM (Expr, StaticVal)
defuncDynFunVar expr = case expr of
                         Var x -> do sv <- lookupStaticVal x
                                     return (expr, sv)
                         _     -> defunc expr

defuncExpr :: Expr -> Expr
defuncExpr = runDefM . defunc

-- Skips type checking. Convenient for testing.
defuncStr :: String -> IO ()
defuncStr s = case parseString s of
  Left parseErr -> print parseErr
  Right e       -> print . pretty . runDefM $ defunc e
