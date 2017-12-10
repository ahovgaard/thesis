module MiniFuthark where

import Control.Monad
import Control.Monad.Trans
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


-- Defunctionalization.
defunc :: Expr -> Expr
defunc expr = case expr of
  Var x             -> expr
  Num n             -> expr
  TrueLit           -> expr
  FalseLit          -> expr
  Add e1 e2         -> Add (defunc e1) (defunc e2)
  LEq e1 e2         -> LEq (defunc e1) (defunc e2)
  If e1 e2 e3       -> If (defunc e1) (defunc e2) (defunc e3)
  Lam x tp e0
    | order tp == 0 -> Lam x tp (defunc e0)
    | otherwise     -> expr
  App e1 e2         -> case defunc e1 of
                         Lam x tp2 e0 -> defunc $ subst x (defunc e2) e0
                         -- should not be possible if expression is well-typed
                         _ -> error "application could not be specialized"
  Let x e1 e2       -> let e1' = defunc e1
                       in defunc $ subst x e1' e2
  Pair e1 e2        -> Pair (defunc e1) (defunc e2)
  Fst e0            -> case defunc e0 of
                         Pair e1 _ -> e1
                         e0'       -> Fst e0'
  Snd e0            -> case defunc e0 of
                         Pair _ e2 -> e2
                         e0'       -> Snd e0'
  ArrayLit es       -> ArrayLit $ map defunc es
  Index e0 e1       -> Index (defunc e0) (defunc e1)
  Update e0 e1 e2   -> Update (defunc e0) (defunc e1) (defunc e2)
  Length e0         -> Length (defunc e0)
  Loop x e1 y e2 e3 -> Loop x (defunc e1) y (defunc e2) (defunc e3)


-- Simple haskeline REPL
process :: String -> IO ()
process s = case parseString s of
  Left  err  -> putStrLn "Parse error:" >> print err
  Right expr ->
    case typeOf emptyCtx expr of
      Left tpErr -> putStrLn $ "Type error: " ++ show tpErr
      Right tp   -> do
        putStrLn $ "Type:\n\t"   ++ show tp
        putStrLn $ "Result:\n\t" ++ show (defunc expr)

main :: IO ()
main = runInputT defaultSettings loop
  where loop = do
          input <- getInputLine "> "
          case input of
            Nothing -> return ()
            Just "" -> loop
            Just s  -> liftIO (process s) >> loop
