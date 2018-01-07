module Test where

import Defunc
import Eval
import Parser
import Syntax
import TypeChecker

tests :: [String]
tests = [
    "let f = \\x:int. x+x \
    \in f 1 + f 2"

  , "let f = \\x:int. let a = 1 \
    \                 in \\y:int. x+y+a \
    \in f 1 2 + f 3 4"

  , "let f = let g = (let a = 1 \
    \                 in \\x:int. x+a) \
    \        in \\y:int. g 2 + y \
    \in f 3"

  , "let f = \\x:int. x+x \
    \in let g = f \
    \   in g 5"

  , "let f = let b = 2 in                  \
    \        let g = let a = 1 in          \
    \                let h = \\x:int. x+a  \
    \                in \\z:int. h b + z   \
    \        in \\y:int. g y + b           \
    \in f 42"
  ]

-- Tests that a program and its defunctionalized version evaluates to the same.
runTest :: String -> IO Bool
runTest input =
  case parseString input of
    Left parseErr -> error $ "parse error: " ++ show parseErr
    Right expr    ->
      case typeOf emptyCtx expr of
        Left typeErr -> error $ "type error: " ++ show typeErr
        Right tp     ->
          do let expr' = defuncExpr expr
             putStrLn "Input program:\n"
             print $ pretty expr
             putStrLn "\nType:"
             print $ pretty tp
             putStrLn "\nTransformed program:\n"
             print $ pretty expr'

             putStrLn "\nType:"
             case typeOf emptyCtx expr' of
               Left typeErr -> putStrLn $ "type error: " ++ show typeErr
               Right tp'    -> print $ pretty tp'

             case (eval expr, eval expr') of
               (Just e, Just e')
                 | e == e' -> do putStr "\nEvaluates to the same value: "
                                 print $ pretty e
                                 return True
               _           -> do putStrLn "\nEvaluates to distinct values."
                                 return False

main :: IO ()
main = do ls <- mapM (\s -> runTest s <* line) tests
          let numTests = length ls
              passed   = length $ filter id ls
          putStrLn $ "Passed " ++ show passed   ++ " out of "
                               ++ show numTests ++ " tests."
  where line = putStrLn $ "\n" ++ replicate 70 '-' ++ "\n"
