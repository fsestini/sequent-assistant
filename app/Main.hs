module Main where

import Proof
import Parser
import System.IO

main :: IO ()
main = do
  putStr "Enter sequent: "
  hFlush stdout
  line <- getLine
  case parseSequent line of
    Left err -> putStrLn $ "Error: " ++ (show err)
    Right sequent -> do pt <- prove sequent
                        putStrLn "No more goals. Proof tree:"
                        putStrLn . show $ pt
                        main
