module TypeChecker ( TypeError(..)
                   , Context
                   , emptyCtx
                   , order
                   , typeOf
                   ) where

import Control.Monad

import Syntax

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

  Record _          -> undefined

  Select _ _        -> undefined

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
