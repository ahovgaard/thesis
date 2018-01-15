import Data.Char
import Data.List.Split

import Defunc
import Eval
import Parser
import Syntax
import TypeChecker

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
             putStrLn input
             putStrLn "\nType:"
             print $ pretty tp
             putStrLn "\nTransformed program:\n"
             print $ pretty expr'

             putStrLn "\nType:"
             case typeOf emptyCtx expr' of
               Left typeErr -> error $ "type error: " ++ show typeErr
               Right tp'    -> print $ pretty tp'

             case (eval expr, eval expr') of
               (Just e, Just e')
                 | e == e' -> do putStr "\nEvaluates to the same value: "
                                 print $ pretty e
                                 return True
               _           -> do putStrLn "\nEvaluates to distinct values."
                                 return False

main :: IO ()
main = do progs <- map (dropWhile isSpace) <$> splitOn "\n\n"
                                           <$> readFile "test/tests.txt"
          ls <- mapM (\s -> runTest s <* line) progs
          let numTests = length ls
              passed   = length $ filter id ls
          putStrLn $ "Passed " ++ show passed   ++ " out of "
                               ++ show numTests ++ " tests."
  where line = putStrLn $ "\n" ++ replicate 70 '-' ++ "\n"
