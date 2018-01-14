{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Defunc ( defuncExpr
              , defuncStr
              ) where

import Control.Monad.RWS

import Parser
import Syntax

-- Type of data storing additional information about the result of
-- defunctionalization of an expression, aside from the residual expression.
data StaticVal = Dynamic Tp
               | Lambda Name Tp Expr Env
               | Tuple StaticVal StaticVal
               | Rcd [(Name, StaticVal)]
               | DynamicFun (Expr, StaticVal) StaticVal
  deriving (Show, Eq)

-- Environment mapping variable names to their associated static value.
type Env = [(Name, StaticVal)]

emptyEnv :: Env
emptyEnv = []

extendEnv :: Name -> StaticVal -> Env -> Env
extendEnv x sv env = (x, sv) : env

combineEnvs :: Env -> Env -> Env
combineEnvs = (++)

-- Generates a nested sequence of let-bindings, binding the free
-- variables to the corresponding fields in a record.
letBindFV :: Name -> Env -> Expr -> Expr
letBindFV x = flip $ foldr (\(y, _) -> Let y [] $ Select (Var x) y)


-- Defunctionalization monad.
newtype DefM a = DefM (RWS Env [Expr -> Expr] Int a)
  deriving (Monad, Functor, Applicative,
            MonadReader Env,
            MonadWriter [Expr -> Expr],
            MonadState Int)

runDefM :: DefM (Expr, StaticVal) -> Expr
runDefM (DefM m) = foldr (.) id bindings expr
  where ((expr, _), bindings) = evalRWS m emptyEnv 0

defuncExpr :: Expr -> Expr
defuncExpr = runDefM . defunc

-- Looks up the associated static value and type of a given name.
lookupVar :: Name -> DefM StaticVal
lookupVar x = do env <- ask
                 case lookup x env of
                   Just sv -> return sv
                   Nothing -> error $ "variable " ++ x ++ " is out of scope"

-- Generates a fresh variable name based on a given name.
freshVar :: Name -> DefM Name
freshVar x = do s <- get
                put (s+1)
                return $ x ++ show s

-- Given a static value, compute the type of the corresponding
-- residual expression.
typeFromSV :: StaticVal -> Tp
typeFromSV (Dynamic tp)           = tp
typeFromSV (Lambda _ _ _ env)     = typeFromNameSVs env
typeFromSV (Tuple sv1 sv2)        = TpPair (typeFromSV sv1) (typeFromSV sv2)
typeFromSV (Rcd ls)               = typeFromNameSVs ls
typeFromSV (DynamicFun (_, sv) _) = typeFromSV sv

typeFromNameSVs :: [(Name, StaticVal)] -> Tp
typeFromNameSVs = TpRecord . map (\(x, sv) -> (x, typeFromSV sv))

-- Looks up a variable in the environment and returns the associated residual
-- expression along with its static value. If the variable denotes a first-order
-- dynamic function, the corresponding closure representation is returned
-- instead of the function variable.
lookupFV :: Name -> DefM (Expr, StaticVal)
lookupFV x = do sv <- lookupVar x
                case sv of
                  DynamicFun (e, sv')  _ -> return (e, sv')
                  _                      -> return (Var x, sv)


-- Main defunctionalization function. Given an expression, returns an equivalent
-- expression without any higher-order subexpression, and the associated static
-- value in the DefM monad. The input expression is expected to be well typed.
defunc :: Expr -> DefM (Expr, StaticVal)
defunc expr = case expr of
  Var x             -> lookupFV x

  Num _             -> return (expr, Dynamic TpInt)
  TrueLit           -> return (expr, Dynamic TpBool)
  FalseLit          -> return (expr, Dynamic TpBool)

  Add e1 e2         -> do (e1', _) <- defuncDynamic e1
                          (e2', _) <- defuncDynamic e2
                          return (Add e1' e2', Dynamic TpInt)

  LEq e1 e2         -> do (e1', _) <- defuncDynamic e1
                          (e2', _) <- defuncDynamic e2
                          return (LEq e1' e2', Dynamic TpBool)

  If e1 e2 e3       -> do (e1', _  ) <- defuncDynamic e1
                          (e2', sv2) <- defuncDynamic e2
                          (e3', _  ) <- defuncDynamic e3
                          return (If e1' e2' e3', sv2)

  Lam x tp e0       -> do let fv = freeVars expr
                          (envVals, svs) <- unzip <$> mapM lookupFV fv
                          return (Record $ zip fv envVals,
                                  Lambda x tp e0 $ zip fv svs)

  App _ _           -> defuncApp 0 expr

  Let x ps e1 e2    -> do (pats, e1', sv1) <- defuncLet $ foldr (uncurry Lam) e1 ps
                          (e2', sv2)       <- local (extendEnv x sv1) (defunc e2)
                          return (Let x pats e1' e2', sv2)

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

  ArrayLit es       -> do (es', svs) <- unzip <$> mapM defuncDynamic es
                          case svs of
                            (Dynamic tp : _) -> return (ArrayLit es', Dynamic (TpArray tp))
                            _                -> error $ "type error: " ++ show (pretty expr)

  Index e1 e2       -> do (e1', sv1) <- defuncDynamic e1
                          (e2', _  ) <- defuncDynamic e2
                          case sv1 of
                            Dynamic (TpArray tp) ->
                              return (Index e1' e2', Dynamic tp)
                            _ -> error $ "type error: " ++ show (pretty expr)

  Update e1 e2 e3   -> do (e1', sv1) <- defuncDynamic e1
                          (e2', _  ) <- defuncDynamic e2
                          (e3', _  ) <- defuncDynamic e3
                          return (Update e1' e2' e3', sv1)

  Length e1         -> do (e1', _) <- defuncDynamic e1
                          return (Length e1', Dynamic TpInt)

  Loop x e1 y e2 e3 -> do (e1', _  ) <- defuncDynamic e1
                          (e2', _  ) <- defuncDynamic e2
                          (e3', sv3) <- defuncDynamic e3
                          return (Loop x e1' y e2' e3', sv3)


-- Ensures that the static value resulting from defunctionalization is dynamic
-- and causes an error otherwise.
defuncDynamic :: Expr -> DefM (Expr, StaticVal)
defuncDynamic e = do
  (e', sv) <- defunc e
  case sv of
    Dynamic _ -> return (e', sv)
    _         -> error $ "expected static value of expression \""
                      ++ show (pretty e)
                      ++ "\" to be dynamic, but got: " ++ show sv

-- Defunctionalizes an application expression at a given depth of application.
-- Calls to dynamic functions are preserved at much as possible, but a new
-- lifted function is created if a dynamic function is only partially applied.
defuncApp :: Int -> Expr -> DefM (Expr, StaticVal)
defuncApp depth expr = case expr of
  App e1 e2 -> do (e1', sv1) <- defuncApp (depth+1) e1
                  (e2', sv2) <- defunc              e2
                  case sv1 of
                    Lambda x _ e0 env -> do
                      (e0', sv) <- local (extendEnv x sv2
                                           . combineEnvs env) (defunc e0)
                      -- Lift lambda to top-level function with a fresh name.
                      f <- freshVar "_f"
                      tell [ Let f [ ("env", typeFromSV sv1)
                                   , (x,     typeFromSV sv2) ]
                                 (letBindFV "env" env e0')
                           ]
                      return (App (App (Var f) e1') e2', sv)

                    DynamicFun _ sv ->
                      case sv2 of
                        Dynamic _ -> return (App e1' e2', sv)
                        _ -> error $ "expected a dynamic argument to "
                                  ++ "a dynamic function, but received: "
                                  ++ show sv2

                    _ -> error $ "application of an expression that is neither a "
                              ++ "static lambda nor a dynamic functions, but a "
                              ++ show sv1 ++ ": " ++ show (pretty expr)

  Var f     -> do sv <- lookupVar f
                  case sv of
                    DynamicFun _ _
                      | not (fullyApplied sv depth) -> do
                          f' <- freshVar $ '_' : f
                          let (pats, e0, sv') = liftDynFun sv depth
                          tell [Let f' pats e0]
                          return (Var f', replNthDynFun sv sv' depth)

                    _ -> return (Var f, sv)

  _         -> defunc expr


---- Keep let-bound first-order functions intact.
defuncLet :: Expr -> DefM ([Pat], Expr, StaticVal)
defuncLet expr@(Lam x tp e0)
  | order tp == 0 = do (pats, e0', sv0) <- local (extendEnv x (Dynamic tp))
                                                 (defuncLet e0)
                       clsr             <- defunc expr
                       return ((x, tp) : pats, e0', DynamicFun clsr sv0)
defuncLet expr    = do (e, sv) <- defunc expr
                       return ([], e, sv)

-- Converts a dynamic function StaticVal into a list of parameters, a function
-- body, and the static value that results from applying the function at a given
-- depth of partial application.
liftDynFun :: StaticVal -> Int -> ([Pat], Expr, StaticVal)
liftDynFun (DynamicFun (e, sv) _) 0 = ([], e, sv)
liftDynFun (DynamicFun (_, Lambda x tp _ _) sv) i
  | i > 0 =  let (pats, e', sv') = liftDynFun sv (i-1)
             in ((x, tp) : pats, e', sv')
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
fullyApplied (Dynamic _)       0         = True
fullyApplied Lambda{}          _         = True
fullyApplied (DynamicFun _ sv) d | d > 0 = fullyApplied sv (d-1)
fullyApplied _ _                         = False

-- Skips type checking. Convenient for testing.
defuncStr :: String -> IO ()
defuncStr s = case parseString s of
  Left parseErr -> print parseErr
  Right e       -> print . pretty . runDefM $ defunc e
