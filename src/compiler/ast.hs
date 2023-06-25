module Compiler.AST where

import Compiler.Scanner as Lexer
import Compiler.Token (Tokened (..), getTokenRange)
import Data.List (intercalate)
import Compiler.Position
import Data.Maybe (isNothing, fromJust)

type VarDeclaration = Tokened HiddenVarDeclaration
data HiddenVarDeclaration = VarDeclaration Type String Expression
  deriving (Eq, Show)

type FuncDeclaration = Tokened HiddenFuncDeclaration
data HiddenFuncDeclaration = FuncDeclaration String FArgs (Maybe FunType) [VarDeclaration] [Statement]
  deriving (Eq, Show)

type RetType = Tokened HiddenRetType
data HiddenRetType =
    RetType Type
  | Void
  deriving (Eq, Show)

type FunType = Tokened HiddenFunType
data HiddenFunType = FunType FTypes RetType
  deriving (Eq, Show)

type FTypes = Maybe [FType]
data FType = FType Type
  deriving (Eq, Show)

type Type = Tokened HiddenType
data HiddenType =
    Basic BasicType
  | Pair Type Type
  | List Type
  | Var String
  | TypeId String
  deriving (Eq, Show)


data BasicType = INT | CHAR | BOOL
  deriving (Eq, Show, Ord)

type FArgs = Maybe [FArg]

type FArg = Tokened HiddenFArg
type HiddenFArg = String

type Statement = Tokened HiddenStatement
data HiddenStatement =
    If Expression [Statement] (Maybe [Statement])
  | While Expression [Statement]
  | VarAssign String (Maybe Field) Expression
  | StatementFunCall FunctionCall
  | Return (Maybe Expression)
  deriving (Eq, Show)

type Expression = Tokened HiddenExpression
data HiddenExpression =
    ExprId String (Maybe Field)
  | ListExpr [Expression] Expression
  | BinaryExpr Op2 Expression Expression
  | UnaryExpr Op1 Expression
  | IntValue Integer
  | CharValue Char
  | BoolValue Bool
  | BracedExpression Expression
  | ExprFunCall FunctionCall
  | EmptyList
  | BadList
  | PairExpression (Expression, Expression)
  deriving (Eq, Show)

type Field = Tokened HiddenField
data HiddenField = HD (Maybe Field) | TL (Maybe Field) | FST (Maybe Field) | SND (Maybe Field)
  deriving (Eq, Show)

type FunctionCall  = Tokened HiddenFunctionCall
data HiddenFunctionCall = FunCall String [ActArg] | PrintFunCall ActArg | IsEmptyFunCall ActArg
  deriving (Eq, Show)

type ActArg = Expression

data Root =
    VarDecl VarDeclaration
  | FunDecl FuncDeclaration
  | EmptyRoot Bool
  deriving (Eq, Show)

type Op2 = Tokened HiddenOp2
data HiddenOp2 =
  Plus |
  Minus |
  Multiply |
  Divide |
  Modulo |
  Equal |
  SmallerThan |
  BiggerThan |
  SmallerEqualThan |
  BiggerEqualThan |
  NotEqual |
  And |
  Or |
  Constructor
  deriving (Eq, Ord, Show)

type Op1 = Tokened HiddenOp1
data HiddenOp1 =
  Not |
  Negative
  deriving (Eq, Ord, Show)

newtype AST = AST [Root]
  deriving (Eq, Show)

-- TODO go as deep as possible
getPrettyPrintedPosition :: AST -> Position -> Maybe String
getPrettyPrintedPosition (AST []) _ = Nothing
getPrettyPrintedPosition (AST (x:xs)) pos
  | isNothing (getRootPosition x) = getPrettyPrintedPosition (AST xs) pos
  | otherwise = if isInRange pos (fromJust $ getRootPosition x) then Just $ prettyPrintRoot x else getPrettyPrintedPosition (AST xs) pos

getRootPosition :: Root -> Maybe PositionRange
getRootPosition (VarDecl (Tokened _ pos)) = getTokenRange pos
getRootPosition (FunDecl (Tokened _ pos)) = getTokenRange pos
getRootPosition (EmptyRoot _) = Nothing

getVarDeclName :: VarDeclaration -> String
getVarDeclName (Tokened (VarDeclaration _ name _) _) = name

getVarDeclExpr :: VarDeclaration -> Expression
getVarDeclExpr (Tokened (VarDeclaration _ _ expr) _) = expr

getFuncDeclname :: FuncDeclaration -> String
getFuncDeclname (Tokened (FuncDeclaration name _ _ _ _) _) = name

prettyPrintAST :: AST -> String
prettyPrintAST (AST []) = ""
prettyPrintAST (AST (x:xs)) = prettyPrintRoot x <> "\n" <> prettyPrintAST (AST xs)

prettyPrintRoot :: Root -> String
prettyPrintRoot (VarDecl varDecl) = prettyPrintVarDecl' varDecl
prettyPrintRoot (FunDecl funDecl) = prettyPrintFunDecl' funDecl
prettyPrintRoot (EmptyRoot _) = undefined

prettyPrintVarDecl' :: VarDeclaration -> String
prettyPrintVarDecl' (Tokened v _) = prettyPrintVarDecl v

prettyPrintVarDecl :: HiddenVarDeclaration -> String
prettyPrintVarDecl (VarDeclaration typ ident expr) = prettyPrintType' typ <> " " <> ident <> " = " <> prettyPrintExpr' expr <> ";"

prettyPrintFunDecl' :: FuncDeclaration -> String
prettyPrintFunDecl' (Tokened f _) = prettyPrintFunDecl f

prettyPrintFunDecl :: HiddenFuncDeclaration -> String
prettyPrintFunDecl (FuncDeclaration ident fArgs fType varDecls stmts) = "fun " <> ident <> "(" <> prettyPrintFArgs fArgs <> ")" <> " :: " <> prettyPrintFunType' fType <> " {\n" <> prettyPrintVarDecls varDecls <> "\n" <> prettyPrintStmts' stmts <> "\n}"

prettyPrintFunType' :: Maybe FunType -> String
prettyPrintFunType' (Just (Tokened (FunType fTypes retType) _)) = prettyPrintFTypes fTypes <> " -> " <> prettyPrintRetType' retType
prettyPrintFunType' Nothing = ""

prettyPrintFunType :: Maybe HiddenFunType -> String
prettyPrintFunType Nothing = ""
prettyPrintFunType (Just (FunType fTypes retType)) = prettyPrintFTypes fTypes <> " -> " <> prettyPrintRetType' retType

prettyPrintRetType' :: RetType -> String
prettyPrintRetType' (Tokened t _) = prettyPrintRetType t

prettyPrintRetType :: HiddenRetType -> String
prettyPrintRetType (RetType typ) = prettyPrintType' typ
prettyPrintRetType Void = "void"

prettyPrintFTypes :: FTypes -> String
prettyPrintFTypes Nothing = ""
prettyPrintFTypes (Just []) = ""
prettyPrintFTypes (Just [x]) = prettyPrintFType x
prettyPrintFTypes (Just (x:xs)) = prettyPrintFType x <> " " <> prettyPrintFTypes (Just xs)

prettyPrintFType :: FType -> String
prettyPrintFType (FType typ) = prettyPrintType' typ

printFArg :: FArg -> String
printFArg (Tokened x _) = x

prettyPrintFArgs :: FArgs -> String
prettyPrintFArgs Nothing = ""
prettyPrintFArgs (Just []) = ""
prettyPrintFArgs (Just [x]) = printFArg x
prettyPrintFArgs (Just (x:xs)) = printFArg x <> "," <> prettyPrintFArgs (Just xs)

prettyPrintVarDecls :: [VarDeclaration] -> String
prettyPrintVarDecls [] = ""
prettyPrintVarDecls [x] = prettyPrintVarDecl' x
prettyPrintVarDecls (x:xs) = prettyPrintVarDecl' x <> prettyPrintVarDecls xs

-- TODO Improve pretty printing
prettyPrintStmts :: [HiddenStatement] -> String
prettyPrintStmts xs = helper xs 1
  where
    helper [] _ = ""
    helper (x:xs) n = replicate (n * 2) ' ' <> prettyPrintStmt x <> "\n" <> helper xs n

prettyPrintStmts' :: [Statement] -> String
prettyPrintStmts' = prettyPrintStmts . map (\(Tokened st _) -> st)

prettyPrintStmt :: HiddenStatement -> String
prettyPrintStmt (If expr stmts Nothing) = "if " <> prettyPrintExpr' expr <> " then " <> prettyPrintStmts' stmts
prettyPrintStmt (If expr stmts (Just elseStmts)) = "if " <> prettyPrintExpr' expr <> " then " <> prettyPrintStmts' stmts <> " else " <> prettyPrintStmts' elseStmts
prettyPrintStmt (While expr stmts) = "while " <> prettyPrintExpr' expr <> " do " <> prettyPrintStmts' stmts
prettyPrintStmt (VarAssign ident Nothing expr) = ident <> " = " <> prettyPrintExpr' expr
prettyPrintStmt (VarAssign ident (Just field) expr) = ident <> "." <> prettyPrintField field <> " = " <> prettyPrintExpr' expr
prettyPrintStmt (StatementFunCall funCall) = prettyPrintFunCall' funCall
prettyPrintStmt (Return Nothing) = "return"
prettyPrintStmt (Return (Just expr)) = "return " <> prettyPrintExpr' expr

prettyPrintExpr' :: Expression -> String
prettyPrintExpr' (Tokened expr _) = prettyPrintExpr expr

prettyPrintExpr :: HiddenExpression -> String
prettyPrintExpr (ExprId ident Nothing) = ident
prettyPrintExpr (ExprId ident (Just field)) = ident <> "." <> prettyPrintField field
prettyPrintExpr (BinaryExpr op expr1 expr2) = prettyPrintExpr' expr1 <> " " <> prettyPrintOp2 op <> " " <> prettyPrintExpr' expr2
prettyPrintExpr (UnaryExpr op expr) = prettyPrintOp1 op <> " " <> prettyPrintExpr' expr
prettyPrintExpr (IntValue val) = show val
prettyPrintExpr (CharValue val) = show val
prettyPrintExpr (BoolValue val) = show val
prettyPrintExpr (BracedExpression expr) = "(" <> prettyPrintExpr' expr <> ")"
prettyPrintExpr (ExprFunCall funCall) = prettyPrintFunCall' funCall
prettyPrintExpr EmptyList = "[]"
prettyPrintExpr (PairExpression (expr1, expr2)) = "(" <> prettyPrintExpr' expr1 <> ", " <> prettyPrintExpr' expr2 <> ")"
prettyPrintExpr (ListExpr exprs final) = "[" <> prettyPrintExprs' exprs <> "]" <> " : " <> prettyPrintExpr' final
prettyPrintExpr BadList = undefined

prettyPrintExprs' :: [Expression] -> String
prettyPrintExprs' = prettyPrintExprs . map (\(Tokened st _) -> st)

prettyPrintExprs :: [HiddenExpression] -> String
prettyPrintExprs [] = ""
prettyPrintExprs [x] = prettyPrintExpr x
prettyPrintExprs (x:xs) = prettyPrintExpr x <> ", " <> prettyPrintExprs xs

prettyPrintFunCall' :: FunctionCall -> String
prettyPrintFunCall' (Tokened f _) = prettyPrintFunCall f

prettyPrintFunCall :: HiddenFunctionCall -> String
prettyPrintFunCall (FunCall ident []) = ident <> "()"
prettyPrintFunCall (FunCall ident args) = ident <> "(" <> prettyPrintArgs args <> ")"
prettyPrintFunCall (PrintFunCall expr) = "print(" <> prettyPrintExpr' expr <> ")"
prettyPrintFunCall (IsEmptyFunCall expr) = "isEmpty(" <> prettyPrintExpr' expr <> ")"

prettyPrintArgs :: [ActArg] -> String
prettyPrintArgs [] = ""
prettyPrintArgs [x] = prettyPrintExpr' x
prettyPrintArgs (x:xs) = prettyPrintExpr' x <> " " <> prettyPrintArgs xs

prettyPrintOp1 :: Op1 -> String
prettyPrintOp1 (Tokened op _) = prettyPrintOp1' op

prettyPrintOp1' :: HiddenOp1 -> String
prettyPrintOp1' Not = "!"
prettyPrintOp1' Negative = "-"

prettyPrintOp2 :: Op2 -> String
prettyPrintOp2 (Tokened op _) = prettyPrintOp2' op

prettyPrintOp2' :: HiddenOp2 -> String
prettyPrintOp2' Plus = "+"
prettyPrintOp2' Minus = "-"
prettyPrintOp2' Multiply = "*"
prettyPrintOp2' Divide = "/"
prettyPrintOp2' Modulo = "%"
prettyPrintOp2' Equal = "=="
prettyPrintOp2' SmallerThan = "<"
prettyPrintOp2' BiggerThan = ">"
prettyPrintOp2' SmallerEqualThan = "<="
prettyPrintOp2' BiggerEqualThan = ">="
prettyPrintOp2' NotEqual = "!="
prettyPrintOp2' And = "&&"
prettyPrintOp2' Or = "||"
prettyPrintOp2' Constructor = ":"

prettyPrintType' :: Type -> String
prettyPrintType' (Tokened typ _) = prettyPrintType typ

prettyPrintType :: HiddenType -> String
prettyPrintType (Basic INT) = "Int"
prettyPrintType (Basic CHAR) = "Char"
prettyPrintType (Basic BOOL) = "Bool"
prettyPrintType (List typ) = "[" <> prettyPrintType' typ <> "]"
prettyPrintType (Pair typ1 typ2) = "(" <> prettyPrintType' typ1 <> ", " <> prettyPrintType' typ2 <> ")"
prettyPrintType (Var v) = "var" <> "(" <> v <> ")"
prettyPrintType (TypeId ident) = ident

prettyPrintField :: Field -> String
prettyPrintField (Tokened fld _) = prettyPrintField' fld

prettyPrintField' :: HiddenField -> String
prettyPrintField' (HD (Just fld)) = "hd" <> "." <> prettyPrintField fld
prettyPrintField' (HD Nothing) = "hd"
prettyPrintField' (TL (Just fld)) = "tl" <> "." <> prettyPrintField fld
prettyPrintField' (TL Nothing) = "tl"
prettyPrintField' (FST (Just fld)) = "fst" <> "." <> prettyPrintField fld
prettyPrintField' (FST Nothing) = "fst"
prettyPrintField' (SND (Just fld)) = "snd" <> "." <> prettyPrintField fld
prettyPrintField' (SND Nothing) = "snd"