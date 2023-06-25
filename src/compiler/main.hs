module Compiler.Main where

import Compiler.Scanner ( scan )
import Compiler.Parser ( parse )
import Compiler.AST (prettyPrintAST, AST (AST))
import Compiler.TypedAST ( prettyPrinter )
import Compiler.Unification ( runUnifyEntireAST )
import Compiler.Graph (createGraph, printGraph, buildRootOrder, printRoots)
import Data.Maybe (fromMaybe, isNothing, fromJust)
import Compiler.SSM (compileAST)

main = do
  let fileName = "demo"
  let custom = True
  let location = if custom then "custom/" ++ fileName else fileName

  content <- readFile ("spl_examples/" ++ location ++ ".spl")
  let (tokens, tokenErrs) = scan content

  putStrLn "Lexer:"
  -- putStr $ concatMap (\x -> show x ++ "\n") tokens

  if null tokenErrs then putStr "No errors\n" else putStr $ concatMap (\x -> show x ++ "\n") tokenErrs

  let (res, errs) = parse tokens
  let ast = fromMaybe (AST []) res

  putStrLn "Parser:"

  if null errs then putStr "No errors\n" else putStr $ concatMap (\x -> show x ++ "\n") errs

  -- putStrLn "String representation of AST:"
  -- putStr $ show res ++ "\n"

  putStrLn "Pretty printed AST:"
  putStr $ prettyPrintAST ast ++ "\n"

  putStrLn "Graph:"
  let (graph, graphErr) = createGraph ast
  if null graphErr then putStr "No errors\n" else putStr $ concatMap (\x -> show x ++ "\n") graphErr
  if isNothing graph then putStr "No graph\n" else do

    putStrLn $ printGraph (fromJust graph) ++ "\n"

    let rootOrder = buildRootOrder (fromJust graph) ast
    -- putStrLn "RootOrder:"
    putStr $ printRoots rootOrder ++ "\n"

    putStrLn "Unification result:\n"
    let (typeRes, typeErrs) = runUnifyEntireAST (AST rootOrder)

    putStrLn "Type errors:"
    if null typeErrs then putStr "No errors\n" else putStr $ concatMap (\x -> show x ++ "\n") typeErrs
    
    case typeRes of
      Nothing -> putStrLn "No typed AST"
      Just typeRes -> do
        putStrLn "Pretty printed typed AST:"
        putStrLn $ prettyPrinter typeRes

        case typeErrs of
          [] -> do
            putStrLn "SSM:"
            compileAST fileName typeRes
            putStrLn "SSM compiled!"
          _ -> return ()
