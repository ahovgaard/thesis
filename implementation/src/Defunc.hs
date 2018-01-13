{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Defunc ( StaticVal(..)
              , defunc
              , runDefM
              , execDefM
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
newtype DefM a = DefM (ReaderT (Env, Int)
                        (WriterT [Expr -> Expr]
                          (State Int)) a)
  deriving (Monad, Functor, Applicative,
            MonadReader (Env, Int),
            MonadWriter [Expr -> Expr],
            MonadState Int)

runDefM :: DefM (Expr, StaticVal) -> Expr
runDefM (DefM m) = foldr (.) id bindings expr
  where ((expr, _), bindings) = evalState (runWriterT $ runReaderT m (emptyEnv, 0)) 0

execDefM :: DefM (Expr, StaticVal) -> (Expr, StaticVal)
execDefM (DefM m) = (foldr (.) id bindings expr, sv)
  where ((expr, sv), bindings) = evalState (runWriterT $ runReaderT m (emptyEnv, 0)) 0

-- Looks up the associated static value and type of a given name.
lookupVar :: Name -> DefM (StaticVal, Tp)
lookupVar x = do (env, _) <- ask
                 case lookup x env of
                   Just v  -> return v
                   Nothing -> error $ "variable " ++ x ++ " is out of scope"

-- Looks up a variable in the environment and returns the associated residual
-- expression along with its static value and its type. If the variable denotes
-- a first-order let-bound function, the corresponding closure representation is
-- returned instead of the function variable.
lookupFV :: Name -> DefM (Expr, (StaticVal, Tp))
lookupFV x = do (sv, tp) <- lookupVar x
                case sv of
                  DynamicFun (e, sv')  _ -> return (e, (sv', tp))
                  _                      -> return (Var x, (sv, tp))

-- Generates a fresh variable name based on a given name.
freshVar :: Name -> DefM Name
freshVar x = do s <- get
                put (s+1)
                return $ x ++ show s

-- Given an environment, construct a corresponding record type for storing the
-- values of the environment.
typeFromEnv :: Env -> Tp
typeFromEnv = TpRecord . map (\(x, (_, tp)) -> (x, tp))

-- Increase the depth of function application.
incrDepth :: DefM a -> DefM a
incrDepth = local (\(env, depth) -> (env, depth + 1))

-- Locally extend the environment in a subcomputation.
localEnv :: (Env -> Env) -> DefM a -> DefM a
localEnv f = local $ \(env, d) -> (f env, d)


-- Main defunctionalization function. Given an expression, returns an equivalent
-- expression without any higher-order subexpression, and the associated static
-- value in the DefM monad. The input expression is expected to be well typed.
defunc :: Expr -> DefM (Expr, StaticVal)
defunc expr = case expr of
  Var x             -> do (e, (sv, _)) <- lookupFV x
                          return (e, sv)

  Num _             -> return (expr, Dynamic)
  TrueLit           -> return (expr, Dynamic)
  FalseLit          -> return (expr, Dynamic)

  Add e1 e2         -> defuncBinOp  Add e1 e2
  LEq e1 e2         -> defuncBinOp  LEq e1 e2
  If e1 e2 e3       -> defuncTernOp If  e1 e2 e3

  Lam x tp e0       -> do let fv  = freeVars expr
                          (envVals, svsTps) <- unzip <$> mapM lookupFV fv
                          return (Record $ zip fv envVals,
                                  Lambda x tp e0 $ zip fv svsTps)

  App e1 e2         -> do (e1', sv1) <- incrDepth $ defuncDynFunVar e1
                          (e2', sv2) <- defunc e2
                          case sv1 of
                            Lambda x tp e0 fv -> do
                              (e0', sv) <- localEnv (extendEnv x sv2 tp
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
                                      ++ show sv1 ++ ": " ++ show (pretty expr)

  Let x e1 e2       -> do (e1', sv1) <- defuncLet e1
                          -- (env, _) <- ask
                          -- If x is a first-order function and it is captured,
                          -- then its type will be that of its closure
                          -- representation rather than its functional type.
                          let tp1 = Right TpInt :: Either TypeError Tp
                                    -- typeOf (map (\(y, (_, tp)) -> (y, tp)) env)
                                    --        (case sv1 of
                                    --           DynamicFun (clsr, _) _ -> clsr
                                    --           _                      -> e1')
                          case tp1 of
                            Left tpErr -> error $ "type error: " ++ show tpErr
                            Right tp1' -> do
                              (e2', sv)  <- localEnv (extendEnv x sv1 tp1') (defunc e2)
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
  | order tp == 0 = do (e0', sv0) <- localEnv (extendEnv x Dynamic tp) (defuncLet e0)
                       clsr       <- defunc expr
                       return (Lam x tp e0', DynamicFun clsr sv0)
defuncLet expr    = defunc expr

-- Avoid translating a dynamic function variable into its static closure.
-- Used in the case for application. If the dynamic function is only
-- partially applied, a new lifted function is created.
defuncDynFunVar :: Expr -> DefM (Expr, StaticVal)
defuncDynFunVar expr =
  case expr of
    Var f -> do (sv, _) <- lookupVar f
                case sv of
                  DynamicFun _ _ -> do
                    (_, depth) <- ask  -- Get the depth of application.
                    if fullyApplied sv depth
                      then -- If fully applied, just return the variable unchanged.
                           return (expr, sv)
                      else -- If not fully applied, lift the dynamic function.
                           do f' <- freshVar $ '_' : f
                              let (e0, sv') = liftDynFun sv depth
                              tell [Let f' e0]
                              return (Var f', replNthDynFun sv sv' depth)
                  _ -> return (expr, sv)
    _     -> defunc expr


-- Converts a dynamic function StaticVal into a function expression.
liftDynFun :: StaticVal -> Int -> (Expr, StaticVal)
liftDynFun (DynamicFun clsr _) 0 = clsr
liftDynFun (DynamicFun (_, Lambda x tp _ _) sv) i
  | i > 0 =  let (e', sv') = liftDynFun sv (i-1)
             in (Lam x tp e', sv')
liftDynFun sv _ = error $ "Tried to lift a StaticVal " ++ show sv
                       ++ ", but expected a dynamic function."

-- Replace the n'th StaticVal in a sequence of DynamicFun's.
replNthDynFun :: StaticVal -> StaticVal -> Int -> StaticVal
replNthDynFun _                    sv' 0 = sv'
replNthDynFun (DynamicFun clsr sv) sv' d = DynamicFun clsr $ replNthDynFun sv sv' (d-1)
replNthDynFun sv _ n = error $ "Tried to replace the " ++ show n
                             ++ "'th StaticVal in " ++ show sv

-- Checks if a StaticVal and a given application depth correspond
-- to a fully applied dynamic function.
fullyApplied :: StaticVal -> Int -> Bool
fullyApplied Dynamic           0         = True
fullyApplied (Lambda _ _ _ _)  _         = True
fullyApplied (DynamicFun _ sv) d | d > 0 = fullyApplied sv (d-1)
fullyApplied _ _                         = False


defuncExpr :: Expr -> Expr
defuncExpr = runDefM . defunc

-- Skips type checking. Convenient for testing.
defuncStr :: String -> IO ()
defuncStr s = case parseString s of
  Left parseErr -> print parseErr
  Right e       -> print . pretty . runDefM $ defunc e
