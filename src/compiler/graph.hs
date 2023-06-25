{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Compiler.Graph where

import Compiler.AST
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad (when, foldM, unless, ap, liftM)
import Control.Monad.State ( StateT(StateT, runStateT), MonadState(put, get) )
import Control.Exception (throw, Exception)
import Data.Maybe (fromMaybe, isJust, fromJust, catMaybes, mapMaybe)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT, catchError, lift)
import qualified Control.Monad.Identity as MIdentity
import Control.Monad.Identity (runIdentity)
import Data.List (isPrefixOf, foldl', nub)
import Compiler.Token (getTokened, Tokened (..))

-- In this module we make a caling graph of the Compiler.AST to check for the following:
-- 1. All functions are defined
-- 2. All variables are defined
-- 3. Which variable calls which function
-- 4. Which function calls which function
-- 5. Which function calls which variable
-- 6. Which variable calls which variable
-- 7. Which function calls which function with which arguments

type Result a = (a, [Error])
newtype GraphTraversal a = GraphTraversal { runGraphTraversal :: StateT State (ExceptT [Error] MIdentity.Identity) (Result a) }

instance Functor GraphTraversal where
  fmap = liftM

instance Applicative GraphTraversal where
  pure = return
  (<*>) = ap

instance Monad GraphTraversal where
  return x = GraphTraversal $ return (x, [])
  m >>= f = GraphTraversal $ do
    (x, errs) <- runGraphTraversal m
    (y, errs') <- runGraphTraversal (f x)
    return (y, errs ++ errs')

instance MonadState State GraphTraversal where
  get = GraphTraversal $ get >>= \s -> return (s, [])
  put s = GraphTraversal $ put s >> return ((), [])

instance MonadError [Error] GraphTraversal where
  throwError err = GraphTraversal $ lift $ throwError err
  catchError (GraphTraversal x) f = GraphTraversal $ catchError x (runGraphTraversal . f)

type State = (RootMap, Graph, Visited, FuncState)

type RootMap = Map.Map String Root
type Graph = Map.Map String [String]
type Visited = [String]
type FuncState = (String, [String], [String])

data VarDeclType = GLOBAL | LOCAL

data Error = Exception String | CycleException String Visited

instance Show Error where
  show (Exception msg) = msg
  show (CycleException id set) = "Cycle detected: " ++ id ++ " -> " ++ show (reverse (id : set))

instance Exception Error

emptyGraph :: Graph
emptyGraph = Map.empty

emptyFuncState :: FuncState
emptyFuncState = ("", [], [])

getVisited :: GraphTraversal Visited
getVisited = do
  (_, _, visited, _) <- get
  return visited

putVisited :: Visited -> GraphTraversal ()
putVisited visited = do
  (rootMap, graph, _, funcState) <- get
  put (rootMap, graph, visited, funcState)

getFuncState :: GraphTraversal FuncState
getFuncState = do
  (_, _, _, funcState) <- get
  return funcState

putFuncState :: FuncState -> GraphTraversal ()
putFuncState funcState = do
  (rootMap, graph, visited, _) <- get
  put (rootMap, graph, visited, funcState)

getGraph :: GraphTraversal Graph
getGraph = do
  (_, graph, _, _) <- get
  return graph

putGraph :: Graph -> GraphTraversal ()
putGraph graph = do
  (rootMap, _, visited, funcState) <- get
  put (rootMap, graph, visited, funcState)

getRootMap :: GraphTraversal RootMap
getRootMap = do
  (rootMap, _, _, _) <- get
  return rootMap

putRootMap :: RootMap -> GraphTraversal ()
putRootMap rootMap = do
  (_, graph, visited, funcState) <- get
  put (rootMap, graph, visited, funcState)

getEdges :: String -> GraphTraversal [String]
getEdges id = fromMaybe [] . Map.lookup id <$> getGraph

isInEdges :: String -> String -> GraphTraversal Bool
isInEdges origin target = do
  edges <- getEdges origin
  return $ target `elem` edges

addEdge :: String -> String -> GraphTraversal ()
addEdge origin target = do
  graph <- getGraph
  visited <- getVisited
  isInEdges' <- isInEdges target origin
  if isInEdges' then return () else do
    let edges = fromMaybe [] (Map.lookup origin graph)
    putGraph (Map.insert origin (nub $ target:edges) graph)

originExists :: String -> GraphTraversal Bool
originExists origin = Map.member origin <$> getGraph

addToVisited :: String -> GraphTraversal ()
addToVisited id = do
  visited <- getVisited
  isInVisited <- isInVisited id
  if isInVisited then throwError [CycleException id visited] `catchError` (\err -> GraphTraversal $ return ((), err)) else do putVisited (id : visited)

addFuncToVisited :: String -> GraphTraversal ()
addFuncToVisited id = addToVisited (id ++ "()")

setFuncName :: String -> GraphTraversal ()
setFuncName name = do
  (id, args, vars) <- getFuncState
  putFuncState (name, args, vars)

getFuncName :: GraphTraversal String
getFuncName = do
  (id, args, vars) <- getFuncState
  return id

addFuncArgAsArg :: FArg -> GraphTraversal ()
addFuncArgAsArg arg = do
  (id, args, vars) <- getFuncState
  name <- getFuncArgName (getTokened arg)
  addEdge id name

addFuncArg :: String -> GraphTraversal ()
addFuncArg arg = do
  (id, args, vars) <- getFuncState
  name <- getFuncArgName arg
  putFuncState (id, name:args, vars)

addFuncVar :: String -> GraphTraversal ()
addFuncVar var = do
  (id, args, vars) <- getFuncState
  name <- getFuncVarName var
  putFuncState (id, args, name:vars)

getFunDecl :: String -> GraphTraversal FuncDeclaration
getFunDecl id = do
  rootMap <- getRootMap
  case Map.lookup id rootMap of
    Just (FunDecl funDecl) -> return funDecl
    _ -> throwError [Exception $ "Function not found: " ++ id] `catchError` (\err -> GraphTraversal $ return (Tokened (FuncDeclaration [] Nothing Nothing [] []) [], err))

getFuncArgName :: String -> GraphTraversal String
getFuncArgName arg = do
  (id, args, vars) <- getFuncState
  return ("#" ++ id ++ "_" ++ arg)

getFuncVarName :: String -> GraphTraversal String
getFuncVarName arg = do
  (id, args, vars) <- getFuncState
  return ("##" ++ id ++ "_" ++ arg)

isInFuncArgs :: String -> GraphTraversal Bool
isInFuncArgs arg = do
  (id, args, vars) <- getFuncState
  funcArgName <- getFuncArgName arg
  return (funcArgName `elem` args)

isInFuncVars :: String -> GraphTraversal Bool
isInFuncVars var = do
  (id, args, vars) <- getFuncState
  funcVarName <- getFuncVarName var
  return (funcVarName `elem` vars)

isInVisited :: String -> GraphTraversal Bool
isInVisited id = do
  visited <- getVisited
  return (id `elem` visited)

getRootName :: Root -> String
getRootName (VarDecl varDecl) = getVarDeclName varDecl
getRootName (FunDecl func) = getFuncDeclname func
getRootName (EmptyRoot _) = undefined

dfs :: AST -> GraphTraversal Graph
dfs (AST []) = getGraph
dfs (AST (root:xs)) = do
  visited <- getVisited
  case root of
    VarDecl varDecl -> do
      let id = getRootName root
      handleVarDecl varDecl id GLOBAL
      putVisited visited
      dfs (AST xs)
    FunDecl funDecl -> do
      let id = getRootName root
      handleFunDecl funDecl id
      putVisited visited
      dfs (AST xs)
    EmptyRoot _ -> undefined

handleFuncArgs :: FArgs -> String -> GraphTraversal ()
handleFuncArgs Nothing _ = return ()
handleFuncArgs (Just []) _ = return ()
handleFuncArgs (Just (arg:args)) origin = do
  addFuncArgAsArg arg
  handleFuncArgs (Just args) origin

handleFuncVarDecls :: [VarDeclaration] -> String -> VarDeclType -> GraphTraversal ()
handleFuncVarDecls [] _ _ = return ()
handleFuncVarDecls (varDecl:varDecls) origin t = do
  visited <- getVisited
  handleVarDecl varDecl origin t
  handleFuncVarDecls varDecls origin t
  putVisited visited

handleVarDecl :: VarDeclaration -> String -> VarDeclType -> GraphTraversal ()
handleVarDecl varDecl origin t = do
  fName <- getFuncName
  let expr = getVarDeclExpr varDecl
  case t of
    GLOBAL -> do
      handleExpression expr origin
    LOCAL -> do
      addFuncVar (getVarDeclName varDecl)
      handleExpression expr origin

getVarName :: String -> GraphTraversal String
getVarName id = do
  isInFuncArgs <- isInFuncArgs id
  isInFuncVars <- isInFuncVars id

  case (isInFuncArgs, isInFuncVars) of
    (_, True) -> getFuncVarName id
    (True, _) -> getFuncArgName id
    _ -> return id

handleExpression :: Expression -> String -> GraphTraversal ()
handleExpression expr origin = case getTokened expr of
  ExprId id _ -> do
    name <- getVarName id
    addEdge origin name
  BinaryExpr _ expr1 expr2 -> handleExpression expr1 origin >> handleExpression expr2 origin
  UnaryExpr _ expr -> handleExpression expr origin
  BracedExpression expr -> handleExpression expr origin
  ExprFunCall funCall -> handleFunCall funCall origin
  PairExpression (expr1, expr2) -> handleExpression expr1 origin >> handleExpression expr2 origin
  ListExpr exprs final -> handleExpressions exprs origin >> handleExpression final origin
  _ -> return ()


handleExpressions :: [Expression] -> String -> GraphTraversal ()
handleExpressions [] _ = return ()
handleExpressions (expr:exprs) origin = handleExpression expr origin >> handleExpressions exprs origin

handleFunDecl :: FuncDeclaration -> String -> GraphTraversal ()
handleFunDecl (Tokened (FuncDeclaration id args _ vars stmts) _) origin = do
  fState <- getFuncState
  setFuncName id
  if origin == id then return () else addEdge origin id >> addToVisited id
  addFuncToVisited id
  handleFuncArgs args origin
  handleFuncVarDecls vars origin LOCAL
  handleStatements stmts origin
  putFuncState fState

handleStatements :: [Statement] -> String -> GraphTraversal ()
handleStatements [] _ = return ()
handleStatements (stmt:stmts) origin = handleStatement stmt origin >> handleStatements stmts origin

handleStatement :: Statement -> String -> GraphTraversal ()
handleStatement stmt origin = handleStatement' (getTokened stmt) origin
  where
    handleStatement' :: HiddenStatement -> String -> GraphTraversal ()
    handleStatement' (If expr ifStmts Nothing)  origin = handleStatements ifStmts origin
    handleStatement' (If expr ifStmts (Just elseStmts))  origin = handleStatements ifStmts origin >> handleStatements elseStmts origin
    handleStatement' (While expr stmts)  origin = handleStatements stmts origin
    handleStatement' (VarAssign id _ expr)  origin = do
      name <- getVarName id
      addEdge origin name
      handleExpression expr origin
    handleStatement' (StatementFunCall funCall) origin = handleFunCall funCall origin
    handleStatement' (Return (Just expr))  origin = handleExpression expr origin
    handleStatement' _ origin = return ()

handleFunCall :: FunctionCall -> String -> GraphTraversal ()
handleFunCall funCall origin = handleFunCall' (getTokened funCall) origin
  where
    handleFunCall' :: HiddenFunctionCall -> String -> GraphTraversal ()
    handleFunCall' (FunCall id exprs) origin = if origin == id then return () else do
      funDecl <- getFunDecl id
      handleExpressions exprs origin
      addEdge origin id
      exists <- originExists id
      if exists then addFuncToVisited id else handleFunDecl funDecl id
    handleFunCall' (PrintFunCall exprs) origin = do
      handleExpression exprs origin
    handleFunCall' (IsEmptyFunCall exprs) origin = do
      handleExpression exprs origin

removeLocals :: Graph -> Graph
removeLocals = Map.map (filter (not . isPrefixOf "#"))

removeExtra :: Graph -> [String] -> Graph
removeExtra = foldl (flip Map.delete)

removeEmptyGraphs :: Graph -> Graph
removeEmptyGraphs = Map.filter (not . null)

createGraph :: AST -> (Maybe Graph, [Error])
createGraph ast = case runIdentity . runExceptT . flip runStateT (getRootMapFromAST ast, Map.empty, [], emptyFuncState) . runGraphTraversal $ dfs ast of
  Left ce -> (Nothing, ce)
  Right ((g, err), _) -> (Just $ (removeEmptyGraphs . removeLocals) g, err)

getRootMapFromAST :: AST -> RootMap
getRootMapFromAST (AST []) = Map.empty
getRootMapFromAST (AST (root:xs)) = Map.insert (getRootName root) root (getRootMapFromAST (AST xs))

getRootsNotInGraph :: Graph -> RootMap -> [Root]
getRootsNotInGraph graph rootMap = let
    graphKeys = Map.keys graph
    graphValues = concat $ Map.elems graph
    values = foldr Set.insert Set.empty (graphValues <> graphKeys)
    rootMapKeys = Map.keys rootMap
  in
    foldr (\key acc -> if key `Set.member` values then acc else fromJust (Map.lookup key rootMap) : acc) [] rootMapKeys

buildRootOrder :: Graph -> AST -> [Root]
buildRootOrder graph roots =
  let
    rootMap = getRootMapFromAST roots
    rootsNotInGraph = getRootsNotInGraph graph rootMap
    rootKeys = Map.keys rootMap
    elements = concatMap (\x -> fromMaybe [] (Map.lookup x graph)) rootKeys

    finalElements = foldr Set.insert Set.empty (elements <> rootKeys)
  in
    mapMaybe (`Map.lookup` rootMap) (srt graph (Set.toList finalElements))

-- Very naive sorting algorithm lol
srt :: Graph -> [String] -> [String]
srt graph [] = []
srt graph (x:xs) = let
    edges = fromMaybe [] (Map.lookup x graph)
    edges' = filter (`elem` xs) edges
  in if null edges' then x : srt graph xs else srt graph (xs ++ [x])

printGraph :: Graph -> String
printGraph = Map.foldlWithKey (\acc key val -> acc ++ key ++ " -> " ++ show val ++ "\n") ""

printRoots :: [Root] -> String
printRoots = foldl (\acc root -> acc ++ printRoot root ++ "\n") ""

printRoot :: Root -> String
printRoot ((VarDecl varDecl)) = prettyPrintVarDecl (getTokened varDecl)
printRoot ((FunDecl funcDecl)) = prettyPrintFunDecl (getTokened funcDecl)
printRoot (EmptyRoot _) = ""