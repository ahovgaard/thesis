module MiniFuthark where

import Control.Monad
import Control.Monad.Trans
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.Haskeline

import Syntax
import Parser

data TypeError = UndefinedVariableError Name
               | TypeMismatchError Tp Tp
               | HigherOrderError
               | TypeError String
  deriving (Show)

-- Typing context.
type Context = [(Name, Tp)]

emptyCtx :: Context
emptyCtx = []

extend :: Context -> Name -> Tp -> Context
extend ctx s tp = (s, tp) : ctx

lookupVar :: Context -> Name -> Either TypeError Tp
lookupVar ctx x = case lookup x ctx of
                    Just tp -> return tp
                    Nothing -> Left $ UndefinedVariableError x

order :: Tp -> Int
order TpInt             = 0
order TpBool            = 0
order (TpArrow tp1 tp2) = max (order tp1 + 1) (order tp2)
order (TpPair  tp1 tp2) = max (order tp1) (order tp2)
order (TpArray tp)      = order tp

checkMatch :: Tp -> Tp -> Either TypeError ()
checkMatch tp1 tp2 = when (tp1 /= tp2) $ Left (TypeMismatchError tp1 tp2)

-- Type checking.
typeOf :: Context -> Expr -> Either TypeError Tp
typeOf ctx expr = case expr of
  Var x             -> lookupVar ctx x
  Num _             -> return TpInt
  TrueLit           -> return TpBool
  FalseLit          -> return TpBool

  Add e1 e2         -> do tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          checkMatch tp1 TpInt
                          checkMatch tp2 TpInt
                          return TpInt

  LEq e1 e2         -> do tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          checkMatch tp1 TpInt
                          checkMatch tp2 TpInt
                          return TpBool

  If e1 e2 e3       -> do tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          tp3 <- typeOf ctx e3
                          checkMatch tp1 TpBool
                          checkMatch tp2 tp3
                          when (order tp2 /= 0) $ Left HigherOrderError
                          return tp2

  Lam x tp1 e2      -> do let ctx' = extend ctx x tp1
                          tp2 <- typeOf ctx' e2
                          return $ TpArrow tp1 tp2

  App e1 e2         -> do tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          case tp1 of
                            TpArrow tp2' tp
                              | tp2 == tp2' -> return tp
                              | otherwise   -> Left $ TypeMismatchError tp2 tp2'
                            _ -> Left $ TypeError "function type expected"

  Let x e1 e2       -> do tp1 <- typeOf ctx e1
                          let ctx' = extend ctx x tp1
                          typeOf ctx' e2

  Pair e1 e2        -> do tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          return $ TpPair tp1 tp2

  Fst e0            -> do tp0 <- typeOf ctx e0
                          case tp0 of
                            TpPair tp1 _ -> return tp1
                            _            -> Left $ TypeError "product type expected"

  Snd e0            -> do tp0 <- typeOf ctx e0
                          case tp0 of
                            TpPair _ tp2 -> return tp2
                            _            -> Left $ TypeError "product type expected"

  ArrayLit es       -> do tps <- mapM (typeOf ctx) es
                          case tps of
                            [] -> Left $ TypeError "unknown type of empty array"
                            (tp : tps') | all (== tp) tps' ->
                                            if order tp == 0
                                            then return $ TpArray tp
                                            else Left HigherOrderError
                            _ -> Left $ TypeError "type mismatch in array"

  Index e0 e1       -> do tp0 <- typeOf ctx e0
                          tp1 <- typeOf ctx e1
                          checkMatch tp1 TpInt
                          when (order tp0 /= 0) $ Left HigherOrderError
                          case tp0 of
                            TpArray tp -> return tp
                            _          -> Left $ TypeError "type mismatch"

  Update e0 e1 e2   -> do tp0 <- typeOf ctx e0
                          tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          when (order tp2 /= 0) $ Left HigherOrderError
                          checkMatch tp1 TpInt
                          case tp0 of
                            tp@(TpArray tp')
                              | tp2 == tp' -> return tp
                            _              -> Left $ TypeMismatchError tp0 (TpArray tp2)

  Length e0         -> do tp0 <- typeOf ctx e0
                          when (order tp0 /= 0) $ Left HigherOrderError
                          case tp0 of
                            TpArray _ -> return TpInt
                            _         -> Left $ TypeError "expected array type"

  Loop x e1 y e2 e3 -> do tp1 <- typeOf ctx e1
                          tp2 <- typeOf ctx e2
                          when (order tp1 /= 0) $ Left HigherOrderError
                          checkMatch tp2 TpInt
                          let ctx' = extend (extend ctx x tp1) y tp2
                          tp3 <- typeOf ctx' e3
                          checkMatch tp1 tp3
                          return tp3

-- Substitutes s for x in t.
-- Assumes that variables are unique for now.
subst :: Name -> Expr -> Expr -> Expr
subst x s t = case t of
  Var y
    | x == y           -> s
    | otherwise        -> t
  Num _                -> t
  TrueLit              -> t
  FalseLit             -> t
  Add e1 e2            -> Add (subst x s e1) (subst x s e2)
  LEq e1 e2            -> LEq (subst x s e1) (subst x s e2)
  If e1 e2 e3          -> If (subst x s e1) (subst x s e2) (subst x s e3)
  Lam y tp e0
    | x == y           -> t
    | otherwise        -> Lam y tp (subst x s e0)
  App e1 e2            -> App (subst x s e1) (subst x s e2)
  Let y e1 e2
    | x == y           -> Let y (subst x s e1) e2
    | otherwise        -> Let y (subst x s e1) (subst x s e2)
  Pair e1 e2           -> Pair (subst x s e1) (subst x s e2)
  Fst e0               -> Fst (subst x s e0)
  Snd e0               -> Snd (subst x s e0)
  ArrayLit es          -> ArrayLit $ map (subst x s) es
  Index e0 e1          -> Index (subst x s e0) (subst x s e1)
  Update e0 e1 e2      -> Update (subst x s e0) (subst x s e1) (subst x s e2)
  Length e0            -> Length (subst x s e0)
  Loop y e1 z e2 e3    -> Loop y (subst x s e1) z (subst x s e2)
                               (if x == y || x == z then e3 else subst x s e3)



data StaticVal = Dynamic
               | Lambda Name Tp Expr [Name]
               | Tuple StaticVal StaticVal
  deriving (Show)

type Env = [(Name, StaticVal)]

emptyEnv = []

-- Computes the free variables of an expression in deterministic order.
freeVars :: Expr -> [Name]
freeVars = Set.elems . fvSet
  where fvSet expr = case expr of
          Var x       -> Set.singleton x
          Num _       -> Set.empty
          TrueLit     -> Set.empty
          FalseLit    -> Set.empty
          Add e1 e2   -> fvSet e1 `Set.union` fvSet e2
          LEq e1 e2   -> fvSet e1 `Set.union` fvSet e2
          Lam x tp e0 -> Set.delete x (fvSet e0)
          App e1 e2   -> fvSet e1 `Set.union` fvSet e2
          Let x e1 e2 -> fvSet e1 `Set.union` Set.delete x (fvSet e2)
          -- todo: finish

-- Generates a nested sequence of let-bindings, binding the free
-- variables to the corresponding fields in a record.
letBindFV :: Name -> [Name] -> Expr -> Expr
letBindFV _ []     e = e
letBindFV x (y:ys) e = Let y (Select (Var x) y) $ letBindFV x ys e



defunc :: Env -> Expr -> (Expr, StaticVal)
defunc env expr = case expr of
  Var x          -> case lookup x env of
                      Just sv -> (expr, sv)
                      Nothing -> error $ "variable " ++ x ++ " out of scope"

  Num n          -> (Num n,    Dynamic)
  TrueLit        -> (TrueLit,  Dynamic)
  FalseLit       -> (FalseLit, Dynamic)

  Add e1 e2      -> case defunc env e1 of
                      (e1', Dynamic) -> case defunc env e2 of
                                          (e2', Dynamic) -> (Add e1' e2', Dynamic)
                      _ -> error "addition of static expressions"

  Lam x tp e0    -> let fv = freeVars expr
                    in (Record $ map (\s -> (s, Var s)) fv, Lambda x tp e0 fv)

  App (Var f) e2 -> case lookup f env of
                      Just (Lambda x tp e0 fv) ->
                        case defunc env e2 of
                          (e2', Dynamic) -> defunc env (letBindFV f fv (subst x e2' e0))
                          _ -> error "application with static argument"
                      Nothing -> error $ "variable " ++ f ++ " out of scope"

  App e1 e2      -> case defunc env e1 of
                      (e1', Lambda x tp e0 fv) ->
                        case defunc env e2 of
                          (e2', Dynamic) ->
                            defunc env $ Let "env" e1' (letBindFV "env" fv (subst x e2' e0))
                      _ -> error $ "applied non-function: " ++ show e1

  Let x e1 e2    -> let (e1', sv1) = defunc env e1
                        (e2', sv)  = defunc ((x, sv1) : env) e2
                    in (Let x e1' e2', sv)

  Pair e1 e2     -> let (e1', sv1) = defunc env e1
                        (e2', sv2) = defunc env e2
                    in (Pair e1' e2', Tuple sv1 sv2)

  Fst e0         -> case defunc env e0 of
                      (e0', Tuple sv1 _) -> (Fst e0', sv1)
                      (e0', Dynamic)     -> (Fst e0', Dynamic)
                      _ -> error $ "projection of an expression that is neither "
                                ++ "dynamic nor a statically known pair"

  Snd e0         -> case defunc env e0 of
                      (e0', Tuple _ sv2) -> (Snd e0', sv2)
                      (e0', Dynamic)     -> (Snd e0', Dynamic)
                      _ -> error $ "projection of an expression that is neither "
                                ++ "dynamic nor a statically known pair"

  Select e0 l    -> (Select e0 l, Dynamic)
  --Select e0 l    -> case defunc env e0 of
  --                    (e0', Dynamic) -> (e0', Dynamic)
  --                    e -> error $ "not handled in select: " ++ show e

  Record xs      -> let f (x, e) =
                          case defunc env e of
                            (e', Dynamic) -> (x, e')
                            _ -> error "static expression in record"
                    in (Record $ map f xs, Dynamic)


  _ -> error $ "missing case for: " ++ show expr


-- Simple haskeline REPL
process :: String -> IO ()
process s = case parseString s of
  Left  err  -> putStrLn "Parse error:" >> print err
  Right expr ->
    case typeOf emptyCtx expr of
      Left tpErr -> putStrLn $ "Type error: " ++ show tpErr
      Right tp   -> do
        putStrLn $ "Type:\n\t"   ++ show tp
        putStrLn $ "Result:\n\t" ++ show (defunc emptyEnv expr)

main :: IO ()
main = runInputT defaultSettings loop
  where loop = do
          input <- getInputLine "> "
          case input of
            Nothing -> return ()
            Just "" -> loop
            Just s  -> liftIO (process s) >> loop
