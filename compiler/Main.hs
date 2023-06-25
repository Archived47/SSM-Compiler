module Main where

import qualified Compiler.Main as Compiler

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  Compiler.main
