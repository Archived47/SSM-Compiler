module Compiler.TypedAST where

import qualified Data.Map as Map
import qualified Compiler.AST (BasicType(..), Type(..), Field(..), Op1(..), Op2(..), prettyPrintField, prettyPrintOp2, prettyPrintOp1)
import Data.Map (toList, Map)
import Compiler.Token (PositionedToken, Tokened (..), getTokenRange, getTokenedTokens)
import Data.Maybe
import Compiler.Position (Position(..), isInRange, PositionRange (..))

data Typed a = Typed a GenericType [PositionedToken]
  deriving (Eq, Show)

getTyped :: Typed a -> a
getTyped (Typed x _ _) = x

setTyped :: a -> Typed a -> Typed a
setTyped x (Typed _ gType tokens) = Typed x gType tokens

getType :: Typed a -> GenericType
getType (Typed _ x _) = x

typedToTokens :: Typed a -> [PositionedToken]
typedToTokens (Typed _ _ tokens) = tokens

type Identity = String
type VariableMap = Map.Map String Variable
type FunctionMap = Map.Map String Function

data GenericType =
    GenericType
  | Basic Compiler.AST.BasicType
  | Pair GenericType GenericType
  | List GenericType
  | Var String
  | TypeId String Bool
  | Void
  deriving (Eq, Show)

instance Ord GenericType where
  compare GenericType GenericType = EQ
  compare GenericType _ = LT
  compare _ GenericType = GT
  compare (Basic x) (Basic y) = compare x y
  compare (Basic _) _ = LT
  compare _ (Basic _) = GT
  compare (Pair x y) (Pair x' y') = case compare x x' of
    EQ -> compare y y'
    x -> x
  compare (Pair _ _) _ = LT
  compare _ (Pair _ _) = GT
  compare (List x) (List y) = compare x y
  compare (List _) _ = LT
  compare _ (List _) = GT
  compare (Var x) (Var y) = compare x y
  compare (Var _) _ = LT
  compare _ (Var _) = GT
  compare (TypeId x _) (TypeId y _) = compare x y
  compare (TypeId _ _) _ = LT
  compare _ (TypeId _ _) = GT
  compare Void Void = EQ

data TypedRoot = RootVar Variable | RootFunc Function
  deriving (Eq, Show)

type Variable = Typed Variable'
data Variable' =
    GlobalVariable Identity TypedExpression
  | LocalVariable Identity TypedExpression
  | FunctionVariable Identity
  deriving (Eq, Show)

type FuncTypeMap = Map [GenericType] Function
type FuncMap = Map String FuncTypeMap

type Function = Typed Function'
data Function' = Function Identity [Variable] [Variable] [Statement]
  deriving (Eq, Show)

getFunctionName :: Function -> String
getFunctionName (Typed func _ _) = getFunctionName' func

getFunctionName' :: Function' -> String
getFunctionName' (Function name _ _ _) = name

type Statement = Tokened HiddenStatement
data HiddenStatement =
    If TypedExpression [Statement] (Maybe [Statement])
  | While TypedExpression [Statement]
  | VarAssign String (Maybe Compiler.AST.Field) TypedExpression
  | StatementFunCall FunctionCall
  | Return (Maybe TypedExpression)
  deriving (Eq, Show)

type TypedExpression = Typed Expression'
data Expression' =
    ExprId String (Maybe Compiler.AST.Field)
  | ListExpr [TypedExpression] TypedExpression
  | BinaryExpr Compiler.AST.Op2 TypedExpression TypedExpression
  | UnaryExpr Compiler.AST.Op1 TypedExpression
  | IntValue Integer
  | CharValue Char
  | BoolValue Bool
  | BracedExpression TypedExpression
  | ExprFunCall FunctionCall
  | EmptyList
  | PairExpression (TypedExpression, TypedExpression)
  deriving (Eq, Show)

type FunctionCall = Typed FunctionCall'
data FunctionCall' = FunCall String [ActArg] | PrintFunCall ActArg | IsEmptyFunCall ActArg
  deriving (Eq, Show)

getFuncallName :: FunctionCall -> String
getFuncallName (Typed (FunCall name _) _ _) = name
getFuncallName (Typed (PrintFunCall _) _ _) = "print"
getFuncallName (Typed (IsEmptyFunCall _) _ _) = "isEmpty"

type ActArg = TypedExpression

data TypedAST = TypedAST [Variable] FuncMap
  deriving (Eq, Show)

getFuncName :: String -> [GenericType] -> String
getFuncName name types = "__" <> name <> "_____" <> concatMap typeToString types

functionMapToFunctions :: FuncMap -> Bool -> [(String, Function)]
functionMapToFunctions mp rename = handleFuncTypes $ Map.elems mp
  where
    handleFuncTypes :: [FuncTypeMap] -> [(String, Function)]
    handleFuncTypes [] = []
    handleFuncTypes (x:xs) = map (uncurry setFuncName) (Map.toList x) <> handleFuncTypes xs

    setFuncName :: [GenericType] -> Function -> (String, Function)
    setFuncName types (Typed (Function name args rets stmts) gType tokens) = (name, Typed (Function (if rename && name /= "main" then getFuncName name types else name) args rets stmts) gType tokens)

typeToString :: GenericType -> String
typeToString (Basic Compiler.AST.INT) = "Int"
typeToString (Basic Compiler.AST.BOOL) = "Bool"
typeToString (Basic Compiler.AST.CHAR) = "Char"
typeToString (List t) = "List_" ++ typeToString t ++ ""
typeToString (Pair left right) = "Pair_" ++ typeToString left ++ "_" ++ typeToString right ++ ""
typeToString _ = undefined

getPrettyPrintedPosition :: TypedAST -> Position -> Maybe String
getPrettyPrintedPosition (TypedAST [] x) _ -- TODO: check if this is correct
  | null x = Nothing
getPrettyPrintedPosition (TypedAST vars funcs) pos = getPrettyPrintedPositionVars vars pos <> getPrettyPrintedPositionFuncs (map snd $ functionMapToFunctions funcs False) pos

tokensToRange :: [PositionedToken] -> PositionRange
tokensToRange tokens = if null tokens then PositionRange (Position 0 0) (Position 0 0) else fromJust $ getTokenRange tokens

getPrettyPrintedPositionVars :: [Variable] -> Position -> Maybe String
getPrettyPrintedPositionVars [] _ = Nothing
getPrettyPrintedPositionVars (x:xs) pos = let res = getPrettyPrintedPositionVar x pos in case res of
  Nothing -> getPrettyPrintedPositionVars xs pos
  Just str -> Just str

getPrettyPrintedPositionFuncs :: [Function] -> Position -> Maybe String
getPrettyPrintedPositionFuncs [] _ = Nothing
getPrettyPrintedPositionFuncs (x:xs) pos = let res = getPrettyPrintedPositionFunc x pos in case res of
  Nothing -> getPrettyPrintedPositionFuncs xs pos
  Just str -> Just str

getPrettyPrintedPositionVar :: Variable -> Position -> Maybe String
getPrettyPrintedPositionVar var@(Typed (GlobalVariable _ expr) _ tokens) pos = if isInRange pos (tokensToRange tokens)
  then let res = getPrettyPrintedPositionExpr expr pos in case res of
    Nothing -> Just $ prettyPrintVariable var
    Just str -> Just str
  else Nothing
getPrettyPrintedPositionVar var@(Typed (LocalVariable _ expr) _ tokens) pos = if isInRange pos (tokensToRange tokens)
  then let res = getPrettyPrintedPositionExpr expr pos in case res of
    Nothing -> Just $ prettyPrintVariable var
    Just str -> Just str
  else Nothing
getPrettyPrintedPositionVar var@(Typed (FunctionVariable _) _ tokens) pos = if isInRange pos (tokensToRange tokens) then Just $ prettyPrintVariable var else Nothing

getPrettyPrintedPositionFunc :: Function -> Position -> Maybe String
getPrettyPrintedPositionFunc func@(Typed (Function name args vars stmts) gType tokens) pos = if isInRange pos (tokensToRange tokens)
  then
    let
      argsInRange = isInRange pos (tokensToRange $ concatMap typedToTokens args)
      varsInRange = isInRange pos (tokensToRange $ concatMap typedToTokens vars)
      stmtsInRange = isInRange pos (tokensToRange $ concatMap getTokenedTokens stmts)
    in case (argsInRange, varsInRange, stmtsInRange) of
      (True, _, _) -> Just $ prettyPrintFunction func
      (_, True, _) -> getPrettyPrintedPositionVars vars pos
      (_, _, True) -> getPrettyPrintedPositionStmts stmts pos
      (_, _, _) -> Just $ name <> "(" <> prettyPrintFuncArgs args <> ")" <> " :: " <> prettyPrintType gType  -- TODO: print pretty
  else Nothing

getPrettyPrintedPositionStmts :: [Statement] -> Position -> Maybe String
getPrettyPrintedPositionStmts [] _ = Nothing
getPrettyPrintedPositionStmts (x:xs) pos = let res = getPrettyPrintedPositionStmt x pos in case res of
  Nothing -> getPrettyPrintedPositionStmts xs pos
  Just str -> Just str

getPrettyPrintedPositionStmt :: Statement -> Position -> Maybe String
getPrettyPrintedPositionStmt stmt@(Tokened (If expr stmts1 stmts2) tokens) pos = if isInRange pos (tokensToRange tokens)
  then
    let
      exprInRange = isInRange pos (tokensToRange $ typedToTokens expr)
      stmts1InRange = isInRange pos (tokensToRange $ concatMap getTokenedTokens stmts1)
      stmts2InRange = case stmts2 of
        Nothing -> False
        Just stmts -> isInRange pos (tokensToRange $ concatMap getTokenedTokens stmts)
    in case (exprInRange, stmts1InRange, stmts2InRange) of
      (True, _, _) -> Just $ prettyPrintStatement stmt 0
      (_, True, _) -> getPrettyPrintedPositionStmts stmts1 pos
      (_, _, True) -> getPrettyPrintedPositionStmts (fromJust stmts2) pos
      (_, _, _) -> Nothing
  else Nothing
getPrettyPrintedPositionStmt stmt@(Tokened (While expr stmts) tokens) pos = if isInRange pos (tokensToRange tokens)
  then
    let
      exprInRange = isInRange pos (tokensToRange $ typedToTokens expr)
      stmtsInRange = isInRange pos (tokensToRange $ concatMap getTokenedTokens stmts)
    in case (exprInRange, stmtsInRange) of
      (True, _) -> Just $ prettyPrintStatement stmt 0
      (_, True) -> getPrettyPrintedPositionStmts stmts pos
      (_, _) -> Nothing
  else Nothing
getPrettyPrintedPositionStmt stmt@(Tokened (VarAssign name _ expr) tokens) pos = if isInRange pos (tokensToRange tokens)
  then
    let exprInRange = isInRange pos (tokensToRange $ typedToTokens expr)
    in if exprInRange then Just $ prettyPrintStatement stmt 0 else Just name -- TODO: print as variable (Need a monad to go through this, NOOOOOO)
  else Nothing
getPrettyPrintedPositionStmt stmt@(Tokened (StatementFunCall funCall) tokens) pos = if isInRange pos (tokensToRange tokens)
  then
    let funCallInRange = isInRange pos (tokensToRange $ typedToTokens funCall)
    in if funCallInRange then Just $ prettyPrintStatement stmt 0 else Just (getFuncallName funCall) -- TODO: print as function (Need a monad to go through this, NOOOOOO)
  else Nothing
getPrettyPrintedPositionStmt stmt@(Tokened (Return expr) tokens) pos = if isInRange pos (tokensToRange tokens)
  then
    let
      exprInRange = case expr of
        Nothing -> False
        Just expr -> isInRange pos (tokensToRange $ typedToTokens expr)
    in if exprInRange then Just $ prettyPrintStatement stmt 0 else Nothing
  else Nothing

getPrettyPrintedPositionExprs :: [TypedExpression] -> Position -> Maybe String
getPrettyPrintedPositionExprs [] _ = Nothing
getPrettyPrintedPositionExprs (x:xs) pos = let res = getPrettyPrintedPositionExpr x pos in case res of
  Nothing -> getPrettyPrintedPositionExprs xs pos
  Just str -> Just str

getPrettyPrintedPositionExpr :: TypedExpression -> Position -> Maybe String
getPrettyPrintedPositionExpr (Typed _ _ []) _ = Nothing
getPrettyPrintedPositionExpr (Typed e t tokens) pos = getPrettyPrintedPositionExpr' e t pos (tokensToRange tokens)

getPrettyPrintedPositionExpr' :: Expression' -> GenericType -> Position -> PositionRange -> Maybe String
getPrettyPrintedPositionExpr' expr@(ExprId _ _) t pos range = if isInRange pos range then Just $ prettyPrintExpression' expr t True else Nothing
getPrettyPrintedPositionExpr' expr@(ListExpr exprs final) t pos range = if isInRange pos range then getPrettyPrintedPositionExprs (exprs ++ [final]) pos else Nothing
getPrettyPrintedPositionExpr' expr@(BinaryExpr _ expr1 expr2) t pos range = if isInRange pos range then getPrettyPrintedPositionExprs [expr1, expr2] pos else Nothing
getPrettyPrintedPositionExpr' expr@(UnaryExpr _ expr1) t pos range = if isInRange pos range then getPrettyPrintedPositionExpr expr1 pos else Nothing
getPrettyPrintedPositionExpr' expr@(IntValue _) t pos range = if isInRange pos range then Just $ prettyPrintExpression' expr t True else Nothing
getPrettyPrintedPositionExpr' expr@(CharValue _) t pos range = if isInRange pos range then Just $ prettyPrintExpression' expr t True else Nothing
getPrettyPrintedPositionExpr' expr@(BoolValue _) t pos range = if isInRange pos range then Just $ prettyPrintExpression' expr t True else Nothing
getPrettyPrintedPositionExpr' expr@(BracedExpression expr1) t pos range = if isInRange pos range then getPrettyPrintedPositionExpr expr1 pos else Nothing
getPrettyPrintedPositionExpr' expr@(ExprFunCall _) t pos range = if isInRange pos range then Just $ prettyPrintExpression' expr t True else Nothing
getPrettyPrintedPositionExpr' expr@EmptyList t pos range = if isInRange pos range then Just $ prettyPrintExpression' expr t False else Nothing
getPrettyPrintedPositionExpr' expr@(PairExpression (expr1, expr2)) t pos range = if isInRange pos range then getPrettyPrintedPositionExprs [expr1, expr2] pos else Nothing

getVariables :: TypedAST -> [Variable]
getVariables (TypedAST variables _) = variables

getFunctions :: TypedAST -> FuncMap
getFunctions (TypedAST _ funcs) = funcs

prettyPrinter :: TypedAST -> String
prettyPrinter (TypedAST variables funcs) = unlines (map prettyPrintVariable variables <> map (prettyPrintFunction . snd) (functionMapToFunctions funcs False))

prettyPrintVariable :: Variable -> String
prettyPrintVariable (Typed var gType _) = prettyPrintVariable' var gType

prettyPrintVariable' :: Variable' -> GenericType -> String
prettyPrintVariable' (GlobalVariable name expr) gType = name <> " : " <> prettyPrintType gType <> " = " <> prettyPrintExpression expr False
prettyPrintVariable' (LocalVariable name expr) gType = name <> " : " <> prettyPrintType gType <> " = " <> prettyPrintExpression expr False
prettyPrintVariable' (FunctionVariable name) gType = name <> " : " <> prettyPrintType gType

prettyPrintFunction :: Function -> String
prettyPrintFunction (Typed func gType _) = prettyPrintFunction' func gType

prettyPrintFunction' :: Function' -> GenericType -> String
prettyPrintFunction' (Function name args vars body) retType = name <> " (" <> prettyPrintFuncArgs args <> ") : " <> prettyPrintType retType <> " {\n" <> prettyPrintLocalVariables vars <> unlines (map (`prettyPrintStatement` 1) body) <> "}\n"

prettyPrintVariableMap :: VariableMap -> String
prettyPrintVariableMap varMap = unlines (map (prettyPrintVariable . snd) (toList varMap))

prettyPrintFuncArgs :: [Variable] -> String
prettyPrintFuncArgs [] = ""
prettyPrintFuncArgs [arg] = prettyPrintVariable arg
prettyPrintFuncArgs (arg:args) = prettyPrintVariable arg <> ", " <> prettyPrintFuncArgs args

prettyPrintLocalVariables :: [Variable] -> String
prettyPrintLocalVariables [] = ""
prettyPrintLocalVariables (var:vars) = "\t" <> prettyPrintVariable var <> "\n" <> prettyPrintLocalVariables vars

prettyPrintType :: GenericType -> String
prettyPrintType (Basic Compiler.AST.INT) = "Int"
prettyPrintType (Basic Compiler.AST.CHAR) = "Char"
prettyPrintType (Basic Compiler.AST.BOOL) = "Bool"
prettyPrintType (List gType) = "[" <> prettyPrintType gType <> "]"
prettyPrintType (Pair gType1 gType2) = "(" <> prettyPrintType gType1 <> ", " <> prettyPrintType gType2 <> ")"
prettyPrintType GenericType = "?"
prettyPrintType (Var x) = "Var " ++ x
prettyPrintType (TypeId x _) = x
prettyPrintType Void = "Void"

prettyPrintExpression :: TypedExpression -> Bool -> String
prettyPrintExpression (Typed expr gType _) = prettyPrintExpression' expr gType

prettyPrintexpressionType :: GenericType -> Bool -> String
prettyPrintexpressionType gType True = " : " <> prettyPrintType gType
prettyPrintexpressionType _ False = ""

prettyPrintExpression' :: Expression' -> GenericType -> Bool -> String
prettyPrintExpression' (ExprId name (Just fld)) gType doPrint = name <> "." <> Compiler.AST.prettyPrintField fld <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' (ExprId name Nothing) gType doPrint = name <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' (ListExpr exprs final) gType doPrint = "[" <> prettyPrintListExpr exprs <> " (" <> prettyPrintExpression final False <> ")" <> "]"  <> prettyPrintexpressionType gType False
prettyPrintExpression' (BinaryExpr op e1 e2) gType doPrint = prettyPrintExpression e1 doPrint <> " " <> Compiler.AST.prettyPrintOp2 op <> " " <> prettyPrintExpression e2 doPrint <> prettyPrintexpressionType gType False
prettyPrintExpression' (UnaryExpr op e) gType doPrint = Compiler.AST.prettyPrintOp1 op <> prettyPrintExpression e doPrint <> prettyPrintexpressionType gType False
prettyPrintExpression' (IntValue i) gType doPrint = show i  <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' (CharValue c) gType doPrint = show c  <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' (BoolValue b) gType doPrint = show b  <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' (BracedExpression e) gType doPrint = "(" <> prettyPrintExpression e doPrint <> ")" <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' (ExprFunCall funcall) gType doPrint = prettyPrintFunCall funcall <> prettyPrintexpressionType gType doPrint
prettyPrintExpression' EmptyList gType doPrint = "[] : " <> prettyPrintType gType
prettyPrintExpression' (PairExpression (e1, e2)) gType doPrint = "(" <> prettyPrintExpression e1 doPrint <> ", " <> prettyPrintExpression e2 doPrint <> ")" <> prettyPrintexpressionType gType doPrint

prettyPrintListExpr :: [TypedExpression] -> String
prettyPrintListExpr [] = ""
prettyPrintListExpr [expr] = prettyPrintExpression expr False
prettyPrintListExpr (expr:exprs) = prettyPrintExpression expr False <> ", " <> prettyPrintListExpr exprs

prettyPrintStatement :: Statement -> Int -> String
prettyPrintStatement (Tokened stmt _) = prettyPrintStatement' stmt

prettyPrintStatement' :: HiddenStatement -> Int -> String
prettyPrintStatement' (VarAssign name (Just fld) expr) cnt = concat (replicate cnt "\t") <> name <> "." <> Compiler.AST.prettyPrintField fld <> " = " <> prettyPrintExpression expr False
prettyPrintStatement' (VarAssign name Nothing expr) cnt = concat (replicate cnt "\t") <> name <> " = " <> prettyPrintExpression expr False
prettyPrintStatement' (StatementFunCall funcall) cnt = concat (replicate cnt "\t") <> prettyPrintFunCall funcall
prettyPrintStatement' (If expr stmts (Just elseStmts)) cnt = concat (replicate cnt "\t") <> "if (" <> prettyPrintExpression expr False <> ") {\n" <> unlines (map (`prettyPrintStatement` (cnt + 1)) stmts) <> "\n" <> concat (replicate cnt "\t") <>"} else {\n" <> unlines (map (`prettyPrintStatement` (cnt + 1)) elseStmts) <> concat (replicate cnt "\t") <> "}"
prettyPrintStatement' (If expr stmts Nothing) cnt =concat (replicate cnt "\t") <>  "if (" <> prettyPrintExpression expr False <> ") {\n" <> unlines (map (`prettyPrintStatement` (cnt + 1)) stmts) <> concat (replicate cnt "\t") <> concat (replicate cnt "\t") <> "}"
prettyPrintStatement' (While expr stmts)  cnt= concat (replicate cnt "\t") <> "while (" <> prettyPrintExpression expr False <> ") {\n"  <> unlines (map (`prettyPrintStatement` (cnt + 1)) stmts) <> concat (replicate cnt "\t") <> "}"
prettyPrintStatement' (Return (Just expr)) cnt = concat (replicate cnt "\t") <> "return " <> prettyPrintExpression expr False
prettyPrintStatement' (Return Nothing) cnt = concat (replicate cnt "\t") <> "return"

prettyPrintFunCall :: FunctionCall -> String
prettyPrintFunCall (Typed funcall gType _) = prettyPrintFunCall' funcall

prettyPrintFunCall' :: FunctionCall' -> String
prettyPrintFunCall' (FunCall name args) = name <> " (" <> unwords (map (`prettyPrintExpression` True) args) <> ")"
prettyPrintFunCall' (PrintFunCall arg) = "print " <> prettyPrintExpression arg False
prettyPrintFunCall' (IsEmptyFunCall arg) = "isEmpty " <> prettyPrintExpression arg False