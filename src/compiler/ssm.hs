-- {-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
-- {-# HLINT ignore "Use <$>" #-}
module Compiler.SSM where

import Data.Map (Map, insert, lookup, size, toList)
import qualified Data.Map as Map
import Compiler.TypedAST
    ( TypedAST(..),
      Function(..),
      Variable(..),
      GenericType(..),
      TypedExpression(..),
      FunctionCall(..),
      Statement(..),
      VariableMap,
      getVariables,
      getFunctions,
      HiddenStatement(..),
      FunctionCall'(..),
      Expression'(..),
      Variable'(..),
      Function'(..),
      Typed(Typed),
      getTyped,
      getType,
      FuncMap,
      functionMapToFunctions,
      typeToString,
      getFuncName )
import qualified Compiler.AST as AST
import Compiler.AST (Op2(..), Op1(..), HiddenOp2 (..), HiddenOp1 (..))
import Data.Maybe ( fromJust, fromMaybe )
import Data.Char (ord)
import Control.Monad.Trans.State (StateT (runStateT, StateT), get, put)
import System.Directory (createDirectoryIfMissing)
import Compiler.Token (Tokened(..), getTokened)
import Control.Monad (unless, when)
import qualified Compiler.TypedAST as TypedAST

type CodeVariableMap = Map String (DataLocation, GenericType)
data Reg = PC | SP | MP | HP | RR | R5 | R6 | R7 | RInt Int
  deriving (Eq, Ord)
data DataLocation = Stack Int | Register Reg | Heap Int | Mark Int | StackTop Int
  deriving (Eq, Show)

emptyListValue = -2147483648

instance Show Reg where
  show PC = "PC"
  show SP = "SP"
  show MP = "MP"
  show HP = "HP"
  show RR = "RR"
  show R5 = "R5"
  show R6 = "R6"
  show R7 = "R7"
  show (RInt i) = show i

type State = (VariableState, FunctionState, HelperFunctionsState, FuncMap)
type FunctionState = (Int, String, CodeVariableMap)

-- (GlobalVariableCounter, LocalCounter, FunctionCounter, GlobalMap, LocalMap)
type VariableState = (Int, Int, Int, CodeVariableMap, CodeVariableMap)
type CodeMap = Map String Code
type HelperFunctionsState = (CodeMap, CodeMap)

type CodeParser a = StateT State (Either Error) a

getFuncMaps :: CodeParser FuncMap
getFuncMaps = do
  (_, _, _, funcMaps) <- get
  return funcMaps

putVarState :: VariableState -> CodeParser ()
putVarState varState = do
  (_, state, printListMap, funcs) <- get
  put (varState, state, printListMap, funcs)

getVarState :: CodeParser VariableState
getVarState = do
  (varState, _, _, _) <- get
  return varState

putFuncState :: FunctionState -> CodeParser ()
putFuncState funcState = do
  (varState, _, printListMap, funcs) <- get
  put (varState, funcState, printListMap, funcs)

getFuncState :: CodeParser FunctionState
getFuncState = do
  (_, funcState, _, _) <- get
  return funcState

getHelperFunctionsState :: CodeParser HelperFunctionsState
getHelperFunctionsState = do
  (_, _, helperFunctionsState, funcs) <- get
  return helperFunctionsState

putHelperFunctionsState :: HelperFunctionsState -> CodeParser ()
putHelperFunctionsState helperFunctionsState = do
  (varState, funcState, _, funcs) <- get
  put (varState, funcState, helperFunctionsState, funcs)

putPrintMap :: CodeMap -> CodeParser ()
putPrintMap printListMap = do
  (_, copyMap) <- getHelperFunctionsState
  putHelperFunctionsState (printListMap, copyMap)

getPrintMap :: CodeParser CodeMap
getPrintMap = do
  (printListMap, _) <- getHelperFunctionsState
  return printListMap

addPrintMap :: GenericType -> Code -> CodeParser ()
addPrintMap genericType code = do
  printListMap <- getPrintMap
  let newPrintListMap = insertFuncMap genericType code printListMap
  putPrintMap newPrintListMap

printHasType :: GenericType -> CodeParser Bool
printHasType genericType = do
  printListMap <- getPrintMap
  let stringType = typeToString genericType
  return $ Map.member stringType printListMap

getCopyMap :: CodeParser CodeMap
getCopyMap = do
  (_, copyMap) <- getHelperFunctionsState
  return copyMap

addCopyMap :: GenericType -> Code -> CodeParser ()
addCopyMap genericType code = do
  (_, copyMap) <- getHelperFunctionsState
  let newCopyMap = insertFuncMap genericType code copyMap
  putCopyMap newCopyMap

putCopyMap :: CodeMap -> CodeParser ()
putCopyMap copyMap = do
  (printMap, _) <- getHelperFunctionsState
  putHelperFunctionsState (printMap, copyMap)

copyHasType :: GenericType -> CodeParser Bool
copyHasType genericType = do
  (_, copyMap) <- getHelperFunctionsState
  let stringType = typeToString genericType
  return $ Map.member stringType copyMap

insertFuncMap :: GenericType -> Code -> CodeMap -> CodeMap
insertFuncMap genericType = Map.insert (typeToString genericType)

getInternalStateCounter :: FunctionState -> Int
getInternalStateCounter (counter, _, _) = counter

getInternalStateLabel :: FunctionState -> String
getInternalStateLabel (_, func, _) = func

getFunction :: CodeParser String
getFunction = do
  (_, state, _, _) <- get
  return $ getInternalStateLabel state

setFunction :: String -> CodeParser ()
setFunction func = do
  (counter, _, map) <- getFuncState
  resetFunctionCounter
  putFuncState (counter, func, map)

getFunctionStateMap :: CodeParser CodeVariableMap
getFunctionStateMap = do
  (_, state, _, _) <- get
  let (_, _, map) = state
  return map

incrementCounter :: FunctionState -> FunctionState
incrementCounter (counter, label, varMap) = (counter + 1, label, varMap)

incrementFunctionStateCounter :: CodeParser ()
incrementFunctionStateCounter = do
  state <- getFuncState
  let newState = incrementCounter state
  putFuncState newState

changeGlobalVariableCounter :: Int -> CodeParser ()
changeGlobalVariableCounter change = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  putVarState (heapCounter + change, stackCounter, markCounter, globalMap, localMap)

incrementGlobalVariableCounter :: CodeParser ()
incrementGlobalVariableCounter = changeGlobalVariableCounter 1

decrementGlobalVariableCounter :: CodeParser ()
decrementGlobalVariableCounter = changeGlobalVariableCounter (-1)

getGlobalVariableCounter :: CodeParser Int
getGlobalVariableCounter = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  return heapCounter

changeLocalCounter :: Int -> CodeParser ()
changeLocalCounter change = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  putVarState (heapCounter, stackCounter + change, markCounter, globalMap, localMap)

incrementLocalCounter :: CodeParser ()
incrementLocalCounter = changeLocalCounter 1

decrementLocalCounter :: CodeParser ()
decrementLocalCounter = changeLocalCounter (-1)

getLocalCounter :: CodeParser Int
getLocalCounter = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  return stackCounter

changeFunctionCounter :: Int -> CodeParser ()
changeFunctionCounter change = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  putVarState (heapCounter, stackCounter, markCounter + change, globalMap, localMap)

incrementFunctionCounter :: CodeParser ()
incrementFunctionCounter = changeFunctionCounter 1

decrementFunctionCounter :: CodeParser ()
decrementFunctionCounter = changeFunctionCounter (-1)

resetFunctionCounter :: CodeParser ()
resetFunctionCounter = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  putVarState (heapCounter, stackCounter, -1, globalMap, localMap)

getFunctionCounter :: CodeParser Int
getFunctionCounter = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  return markCounter

getFunctionName :: CodeParser String
getFunctionName = do
  state <- getFuncState
  return $ getInternalStateLabel state

getStateCounter :: CodeParser Int
getStateCounter = do
  state <- getFuncState
  return $ getInternalStateCounter state

insertGlobalVar :: String -> GenericType -> DataLocation -> CodeParser ()
insertGlobalVar name t location = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  let newGlobalMap = Map.insert name (location, t) globalMap
  putVarState (heapCounter, stackCounter, markCounter, newGlobalMap, localMap)

getGlobalVarMap :: CodeParser CodeVariableMap
getGlobalVarMap = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  return globalMap

insertLocalVar :: String -> GenericType -> DataLocation -> CodeParser ()
insertLocalVar name t location = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  newName <- getLocalVarName name
  let newLocalMap = Map.insert newName (location, t) localMap
  putVarState (heapCounter, stackCounter, markCounter, globalMap, newLocalMap)

getLocalVarName :: String -> CodeParser String
getLocalVarName name = do
  label <- getFunctionName
  return $ "##" ++ label ++ "_" ++ name

getLocalVarMap :: CodeParser CodeVariableMap
getLocalVarMap = do
  varState <- getVarState
  let (heapCounter, stackCounter, markCounter, globalMap, localMap) = varState
  return localMap

insertFunctionVar :: String -> GenericType -> DataLocation -> CodeParser ()
insertFunctionVar name t location = do
  label <- getFunction
  varMap <- getFunctionStateMap
  newName <- getFunctionVarName name
  let newVarMap = Map.insert newName (location, t) varMap
  counter <- getStateCounter
  putFuncState (counter, label, newVarMap)

getFunctionVarName :: String -> CodeParser String
getFunctionVarName name = do
  label <- getFunctionName
  return $ "#" ++ label ++ "_" ++ name

data Error
  = TypeMismatch GenericType GenericType
  | UnknownVariable String
  deriving (Show)

prettyPrintCode :: Code -> String
prettyPrintCode code = unlines $ map show code

emptyState :: FuncMap -> State
emptyState fs = ((0, 1, -1, Map.empty, Map.empty), (1, "", Map.empty), (Map.empty, Map.empty), fs)

-- codeWriter :: IO ()
-- codeWriter = do
--   let x = runStateT (functionToInstructions testFunc1) emptyState
--   case x of
--     Left err -> print err
--     Right (result, state) -> do
--       printToFile (BRA "main" : result)

instance Show Instruction where
  show (LDC i) = "\tLDC " ++ show i
  show (LDChar c) = "\tLDC " ++ show (ord c)
  show (LDL i) = "\tLDL " ++ show i
  show (LDS i) = "\tLDS " ++ show i
  show (LDA i) = "\tLDA " ++ show i
  show (LDAA i) = "\tLDAA " ++ show i
  show (LDLA i) = "\tLDLA " ++ show i
  show (LDSA i) = "\tLDSA " ++ show i
  show (STR r) = "\tSTR " ++ show r
  show (STL i) = "\tSTL " ++ show i
  show (STS i) = "\tSTS " ++ show i
  show (STA i) = "\tSTA " ++ show i
  show (LDR r) = "\tLDR " ++ show r
  show (BRA s) = "\tBRA " ++ s
  show (BRT s) = "\tBRT " ++ s
  show (BRF s) = "\tBRF " ++ s
  show (BSR s) = "\tBSR " ++ s
  show (BEQ s) = "\tBEQ " ++ s
  show (BNE s) = "\tBNE " ++ s
  show (BLT s) = "\tBLT " ++ s
  show (BGT s) = "\tBGT " ++ s
  show (BLE s) = "\tBLE " ++ s
  show (BGE s) = "\tBGE " ++ s
  show ADD = "\tADD"
  show SUB = "\tSUB"
  show MUL = "\tMUL"
  show DIV = "\tDIV"
  show MOD = "\tMOD"
  show (LABEL s) = s ++ ":"
  show (LINK i) = "\tLINK " ++ show i
  show UNLINK = "\tUNLINK"
  show (AJS i) = "\tAJS " ++ show i
  show SWP = "\tSWP"
  show (SWPR r) = "\tSWPR " ++ show r
  show (SWPRR r1 r2) = "\tSWPRR " ++ show r1 ++ " " ++ show r2
  show (LDRR r1 r2) = "\tLDRR " ++ show r1 ++ " " ++ show r2
  show JSR = "\tJSR"
  show (TRAP i) = "\tTRAP " ++ show i
  show NOP = "\tNOP"
  show HALT = "\tHALT"
  show RET = "\tRET"
  show NEG = "\tNEG"
  show NOT = "\tNOT"
  show Compiler.SSM.LT = "\tLT"
  show Compiler.SSM.GT = "\tGT"
  show Compiler.SSM.LE = "\tLE"
  show Compiler.SSM.GE = "\tGE"
  show Compiler.SSM.EQ = "\tEQ"
  show Compiler.SSM.NEQ = "\tNE"
  show Compiler.SSM.AND = "\tAND"
  show Compiler.SSM.OR = "\tOR"
  show (LDH i) = "\tLDH " ++ show i
  show STH = "\tSTH"
  show (STMH i) = "\tSTMH " ++ show i
  show (LDMA i j) = "\tLDMA " ++ show i ++ " " ++ show j

data Instruction =
    STR Reg | STH | STL Int | STS Int | STA Int | STMH Int                                                      --store
  | LDR Reg | LDH Int | LDL Int | LDS Int | LDA Int | LDMA Int Int | LDC Int | LDChar Char | LDLA Int | LDSA Int | LDAA Reg               --load
  | BRA String | BRT String | BRF String | BSR String                                              --branch
  | BEQ String | BNE String | BLT String | BGT String | BLE String | BGE String                    -- branch equality stuff
  | ADD | SUB | MUL | DIV | MOD                                                                    -- ops ints                                                         
  | LT | GT | LE | GE | EQ | NEQ | AND | OR                                                        --ops bools
  | NEG | NOT                                                                                      --unary ops
  | RET                                                                                            -- return
  | LINK Int | UNLINK
  | AJS Int                                                                                        --Adjust stack
  | SWP | SWPR Reg | SWPRR Reg Reg                                                                 --swapping
  | LDRR Reg Reg
  | JSR                                                                                            -- jump to subroutine
  | TRAP Int | NOP | HALT                                                                          --stopping
  | LABEL String
  deriving (Eq)

type Code = [Instruction]

intOperation :: Instruction -> Code -> Code -> Code
intOperation ADD as bs = as ++ bs ++ [ADD]
intOperation SUB as bs = as ++ bs ++ [SUB]
intOperation MUL as bs = as ++ bs ++ [MUL]
intOperation DIV as bs = as ++ bs ++ [DIV]
intOperation MOD as bs = as ++ bs ++ [MOD]
intOperation _ _ _= []

--LT | GT | LE | GE | EQ | NEQ | AND | OR 
boolOperation :: Instruction -> Code -> Code -> Code
boolOperation Compiler.SSM.LT as bs = as ++ bs ++ [Compiler.SSM.LT] --[LDC a, LDC b, Compiler.SSM.LT]
boolOperation Compiler.SSM.GT as bs = as ++ bs ++ [Compiler.SSM.GT]
boolOperation LE as bs = as ++ bs ++ [Compiler.SSM.LE]
boolOperation GE as bs = as ++ bs ++ [Compiler.SSM.GE]
boolOperation Compiler.SSM.EQ as bs = as ++ bs ++ [Compiler.SSM.EQ]
boolOperation NEQ as bs = as ++ bs ++ [Compiler.SSM.NEQ]
boolOperation AND as bs = as ++ bs ++ [Compiler.SSM.AND]
boolOperation OR as bs = as ++ bs ++ [Compiler.SSM.OR]
boolOperation _ _ _= []

--NEG | NOT
unaryOperation :: Instruction -> Code -> Code
unaryOperation NEG as = as ++ [NEG]
unaryOperation NOT as = as ++ [NOT]
unaryOperation _ _ = []
-- notOperation :: Instruction -> Bool -> Code
-- notOperation NOT a = [boolToInt a, NOT]
-- notOperation _ _ = []

boolToInt :: Bool -> Instruction
boolToInt True  = LDC 1
boolToInt False = LDC 0

intOps :: [HiddenOp2]
intOps = [Plus, Minus, Multiply, Divide, Modulo]
boolOps :: [HiddenOp2]
boolOps = [SmallerEqualThan, BiggerEqualThan, SmallerThan, BiggerThan, Equal, NotEqual, And, Or]
unaryOps :: [HiddenOp1]
unaryOps = [Negative, Not]

op1Elem :: Op1 -> [HiddenOp1] -> Bool
op1Elem x lst = getTokened x `elem` lst

op2Elem :: Op2 -> [HiddenOp2] -> Bool
op2Elem x lst = getTokened x `elem` lst

stmtsToInstructions :: [Statement] -> CodeParser Code
stmtsToInstructions [] = return []
stmtsToInstructions (s:ss) = do
  firstResult <- stmtToInstructions (getTokened s)
  result <- stmtsToInstructions ss
  return (firstResult <> result)

branchIfName :: CodeParser String
branchIfName = do
  currentFunction <- getFunctionName
  counter <- getStateCounter
  return $ currentFunction ++ "BranchTrue" ++ show counter

branchElseName :: CodeParser String
branchElseName = do
  currentFunction <- getFunctionName
  counter <- getStateCounter
  return $ currentFunction ++ "BranchFalse" ++ show counter

branchEndName :: CodeParser String
branchEndName = do
  currentFunction <- getFunctionName
  counter <- getStateCounter
  return $ currentFunction ++ "BranchEnd" ++ show counter

stmtToInstructions :: HiddenStatement -> CodeParser Code
stmtToInstructions (If tExpr stmts elseStmts) = case elseStmts of
  Just stmts' -> do
    (expr, values) <- performIf
    elseValues <- performElse stmts'
    ifName <- branchIfName
    elseName <- branchElseName
    label <- branchEndName
    incrementFunctionStateCounter
    return $ expr ++ [BRF elseName, LABEL ifName] ++ values ++ [BRA label] ++ [LABEL elseName] ++ elseValues ++ [LABEL label]
  Nothing -> do
    (expr, values) <- performIf
    ifName <- branchIfName
    label <- branchEndName
    incrementFunctionStateCounter
    return $ expr ++ [BRF label] ++ values ++ [LABEL label]
  where
    performIf = do
      performIfInstr <- stmtsToInstructions stmts -- Perform the if statements
      currentFunction <- getFunctionName -- Get the current function name
      counter <- getStateCounter -- Get the current state counter
      funName <- branchIfName -- Create a new function name
      exprResult <- exprToInstructions Nothing tExpr -- Get the if expression result
      return $ (exprResult, performIfInstr) -- Return the expression result and the new function
    performElse statements = do
      stmtsToInstructions statements
stmtToInstructions (While tExpr stmts) = do
  performWhileInstr <- stmtsToInstructions stmts
  currentFunction <- getFunctionName
  counter <- getStateCounter
  exprResult <- exprToInstructions Nothing tExpr
  let funName = currentFunction ++ "WhileStart" ++ show counter
  let conditionName = currentFunction ++ "WhileCondition" ++ show counter
  let endName = currentFunction ++ "WhileEnd" ++ show counter
  return $ [LABEL conditionName] ++ exprResult ++ [BRF endName, LABEL funName] ++ performWhileInstr ++ [BRA conditionName, LABEL endName]
stmtToInstructions (VarAssign var fld tExpr) = case fld of
  Just field -> do
    exprResult <- exprToInstructions (Just var) tExpr
    (instr, finalFld) <- fieldToInstructions fld True
    varRes <- loadVariable var

    case fromJust finalFld of
      AST.HD _ -> do
        em <- segmentEmptyList
        let isEmpty = [STR R7, LDR R7, LDA 0] ++ em
        return $ exprResult ++ varRes ++ instr ++ isEmpty ++ [LDR R7, STA 0]
      AST.TL _ -> do 
        let isEmpty = [LDA 0, LDC 1, ADD, STR R7]
        return $ exprResult ++ varRes ++ instr ++ isEmpty ++ [LDR R7, STA 0]
      _ -> error "Not a list"
  Nothing -> do
    exprResult <- exprToInstructions (Just var) tExpr
    let t = getType tExpr
    case t of
      List gt -> loadVariable var >>= \r -> return $ exprResult ++ r ++ [STA 0]
      Pair gt gt' -> loadVariable var >>= \r -> return $ exprResult ++ r ++ [STA 0]
      _ -> loadVariable var >>= \r -> return $ exprResult ++ r ++ [STA 0]
stmtToInstructions (StatementFunCall funcall) = funCallToInstructions funcall
stmtToInstructions (Return texpr) = case texpr of
  Just expr -> do
    expression <- exprToInstructions Nothing expr
    end <- stmtToInstructions (Return Nothing)
    return (expression ++ [STR RR] ++ end)
  Nothing -> return [UNLINK, RET]

segmentEmptyList :: CodeParser Code
segmentEmptyList = do
  return [LDC emptyListValue, Compiler.SSM.EQ, BRT "____ListEmpty"]

fieldToInstructions :: Maybe AST.Field -> Bool -> CodeParser (Code, Maybe AST.HiddenField)
fieldToInstructions (Just (Tokened (AST.HD fld) _)) load = fieldToInstructions fld False >>= \(res, final) -> return (LDA 0 : res, Just $ fromMaybe (AST.HD fld) final)
fieldToInstructions (Just (Tokened (AST.TL fld) _)) load = do
  (res, final) <- fieldToInstructions fld False
  return (([LDA 0 | load]) ++ [LDMA 0 2, SWP, LDC emptyListValue, Compiler.SSM.EQ, BRT "____ListEmpty"] ++ res, Just $ fromMaybe (AST.TL fld) final)
fieldToInstructions (Just (Tokened (AST.FST fld) _)) _ = return ([LDA 0], Just (AST.FST fld))
fieldToInstructions (Just (Tokened (AST.SND fld) _)) _ = return ([LDA 1], Just (AST.SND fld))
fieldToInstructions Nothing _ = return ([], Nothing)

funCallToInstructions :: FunctionCall -> CodeParser Code
funCallToInstructions (Typed funCall _ _) = funCallToInstructions' funCall

funCallToInstructions' :: FunctionCall' -> CodeParser Code
funCallToInstructions' (FunCall name args) = do
  argResult <- helper args 0
  let newName = getFuncName name (map getType args)
  return $ argResult ++ [BSR newName, AJS (length args), LDR RR]
  where
    helper :: [TypedExpression] -> Int -> CodeParser Code
    helper (x:xs) i = do
      res <- exprToInstructions Nothing x
      recRes <- helper xs i
      return $ res ++ recRes
    helper _ _ = return []
funCallToInstructions' (PrintFunCall arg) = do
  printRes <- printExpression arg
  return $ printRes ++ printNewLine
funCallToInstructions' (IsEmptyFunCall arg) = do
  exprResult <- exprToInstructions Nothing arg
  let isEmptyCall = [BSR "IsEmpty", LDR RR]
  return $ exprResult ++ isEmptyCall

getListType :: GenericType -> GenericType
getListType (List gType) = gType
getListType _ = undefined

exprToInstructions :: Maybe String -> TypedExpression -> CodeParser Code
exprToInstructions inVar tExpr@(Typed expr t _) = exprToInstructions' inVar expr t
  where
    exprToInstructions' :: Maybe String -> Expression' -> GenericType -> CodeParser Code
    exprToInstructions' inVar expr@(ExprId name fld) gType = do
      copy <- case inVar of
        Nothing -> return []
        Just s -> if s == name then return [] else createCopy gType
      case fld of
        Just field -> do
          (instr, _) <- fieldToInstructions fld False
          var <- loadVariable name
          return $ var ++ [LDA 0] ++ instr ++ copy
        Nothing -> do
          loadVariable name >>= \r -> return $ r ++ [LDA 0] ++ copy
    exprToInstructions' inVar (BinaryExpr op2 tExpr1 tExpr2) _
      | op2 `op2Elem` intOps =  do
        e1 <- exprToInstructions inVar tExpr1
        e2 <- exprToInstructions inVar tExpr2
        return $ intOperation op e1 e2
      | op2 `op2Elem` boolOps = do
        e1 <- exprToInstructions inVar tExpr1
        e2 <- exprToInstructions inVar tExpr2
        return $ boolOperation op e1 e2
      | otherwise = undefined
      where
        op = fromJust $ Map.lookup (getTokened op2) op2Codes
    exprToInstructions' inVar (UnaryExpr op1 tExpr) _
      | op1 `op1Elem` unaryOps = exprToInstructions inVar tExpr >>= \expr1 -> return $ unaryOperation op expr1
      | otherwise = undefined
      where
        op = fromJust $ Map.lookup (getTokened op1) op1Codes
    exprToInstructions' inVar (IntValue i) _ = return [LDC (fromInteger i)]
    exprToInstructions' inVar (CharValue c) _ = return [LDChar c]
    exprToInstructions' inVar (BoolValue b) _ = return [boolToInt b]
    exprToInstructions' inVar (BracedExpression tExpr) _ = exprToInstructions inVar tExpr
    exprToInstructions' inVar (ExprFunCall (Typed (PrintFunCall _) _ _)) _ = error "Cannot have print function call as an expression"
    exprToInstructions' inVar (ExprFunCall funCall) _ = funCallToInstructions funCall
    exprToInstructions' inVar EmptyList t = exprToInstructions' inVar (ListExpr [] tExpr) t
    exprToInstructions' inVar (PairExpression (tExpr1, tExpr2)) _ = do
      e1 <- exprToInstructions inVar tExpr1
      e2 <- exprToInstructions inVar tExpr2

      let res = e1 ++ e2

      return $ res ++ [STMH 2, LDC 1, SUB]
    exprToInstructions' inVar (ListExpr exprs final) gType = do
      let innerType = case gType of
            List gt -> gt
            _ -> error "Not a list"

      -- If final is an ExprId, copy the entire list that is already in memory
      -- If final is an ExprFunCall, copy the entire list that is already in memory

      let isFinalEmpty = exprIsEmptyList final
      x <- if isFinalEmpty then return [LDC emptyListValue, LDC (-1), STMH 2, LDC 1, SUB] else exprToInstructions inVar final
      _exprInstructions <- mapM (exprToInstructions inVar) exprs
      let exprInstructions = _exprInstructions

      result <- helper (reverse exprInstructions) True

      return (x ++ result)
      where
        helper :: [Code] -> Bool -> CodeParser Code
        helper [] hasThing = if not hasThing then return [LDC (-1), STMH 2, LDC 1, SUB] else return []
        helper (x:xs) hasThing = do
          if not hasThing then do
            let first = x ++ [LDC (-1), STMH 2, LDC 1, SUB]
            res <- helper' xs
            return $ first  ++ res
          else do
            helper' (x:xs)
        helper' :: [Code] -> CodeParser Code
        helper' [] = return []
        helper' (x:xs) = do
          let current = x ++ [SWP, STMH 2, LDC 1, SUB]
          res <- helper' xs
          return $ current ++ res

exprIsEmptyList :: TypedExpression -> Bool
exprIsEmptyList (Typed e _ _) = exprIsEmptyList' e

exprIsEmptyList' :: Expression' -> Bool
exprIsEmptyList' EmptyList = True
exprIsEmptyList' _ = False

createCopy :: GenericType -> CodeParser Code
createCopy t = do
  case t of
    Basic bt -> return []
    Pair gt gt' -> createPairCopy (gt, gt')
    List gt -> do
      (call, res) <- createListCopy gt
      return (call ++ [AJS (-1)] ++ res)
    _ -> undefined

createListCopy :: GenericType -> CodeParser (Code, Code)
createListCopy t = do
  let listType = List t

  let name = typeToString listType
  let funcName = "__copy_" ++ name
  let innerName = "__inner_copy_" ++ name
  let createName = "__create_copy_" ++ name
  let createInnerName = "__create_inner_copy_" ++ name
  let isEmptyLabel = "__is_empty_" ++ name

  let returnCode = ([BSR funcName], [LDR RR])

  alreadyExists <- copyHasType listType
  if alreadyExists then return returnCode else do

    let createFunc =  [LABEL funcName, LINK 0, LDC (-1)]
    let load = [LDR MP, LDC 2, SUB, LDA 0, BSR "IsEmpty", LDR RR, LDC 1, Compiler.SSM.EQ, BRF innerName, LABEL isEmptyLabel, LDC emptyListValue, LDC (-1), STMH 2, LDC 1, SUB, STR RR, UNLINK, RET]

    case t of
      Basic bt -> do
        let final = [LABEL createName, LDC (-1), STMH 2, LDC 1, SUB, SWP, BRA createInnerName, LABEL createInnerName, SWP, STMH 2, LDC 1, SUB, SWP, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT createInnerName, AJS (-1), STR RR, UNLINK, RET]
        let doStuff = [STS 0, AJS 1]
        let inner = [LABEL innerName, LDMA 0 2, AJS (-1)] ++ doStuff ++ [AJS 1, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT innerName, BRF createName]

        addCopyMap listType (createFunc ++ load ++ inner ++ final)

        return returnCode
      Pair gt gt' -> do
        pair <- createPairCopy (gt, gt')

        let final = [LABEL createName, LDC (-1), STMH 2, LDC 1, SUB, SWP, BRA createInnerName, LABEL createInnerName, SWP, STMH 2, LDC 1, SUB, SWP, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT createInnerName, AJS (-1), STR RR, UNLINK, RET]
        let doStuff = pair
        let inner = [LABEL innerName, LDMA 0 2, SWP] ++ doStuff ++ [SWP, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT innerName, BRF createName]

        addCopyMap listType (createFunc ++ load ++ inner ++ final)

        return returnCode
      List gt -> do

        (call, res) <- createListCopy gt
        let final = [LABEL createName, LDC (-1), STMH 2, LDC 1, SUB, SWP, BRA createInnerName, LABEL createInnerName, SWP, STMH 2, LDC 1, SUB, SWP, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT createInnerName, AJS (-1), STR RR, UNLINK, RET]
        let doStuff = call ++ [AJS (-1)] ++ res
        let inner = [LABEL innerName, LDMA 0 2, SWP] ++ doStuff ++ [SWP, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT innerName, BRF createName]

        addCopyMap listType (createFunc ++ load ++ inner ++ final)

        return returnCode
      _ -> undefined

createPairCopy :: (GenericType, GenericType) -> CodeParser Code
createPairCopy (t1, t2) = do
  let t = Pair t1 t2
  let name = typeToString t
  let funcName = "__copy_" ++ name

  let returnCode = [BSR funcName, AJS (-1), LDR RR]

  alreadyExists <- copyHasType t
  if alreadyExists then return returnCode else do

    let createFunc =  [LABEL funcName, LINK 0]
    let load = [LDR MP, LDC 2, SUB, LDA 0]

    left <- helper t1 True
    right <- helper t2 False

    let final = [STMH 2, LDC 1, SUB, STR RR, UNLINK, RET]
    let doStuff = getInbetween t1
    let inner = [LDMA 0 2] ++ left ++ doStuff ++ right

    addCopyMap t (createFunc ++ load ++ inner ++ final)

    return returnCode
    where
      helper :: GenericType -> Bool -> CodeParser Code
      helper gType isLeft = do
        case gType of
          Basic bt -> return $ ([AJS (-1) | isLeft]) ++ [STS 0, AJS 1]
          Pair gt gt' -> do
            copy <- createPairCopy (gt, gt')
            return $ ([SWP | isLeft]) ++ copy ++ [SWP]
          List gt -> do
            (call, ret) <- createListCopy gt
            return $ ([SWP | isLeft]) ++ call ++ [AJS (-1)] ++ ret ++ ([SWP | isLeft])
          _ -> undefined
      getInbetween :: GenericType -> Code
      getInbetween gType = do
        case gType of
          Basic bt -> [STS 0, AJS 2]
          Pair gt gt' -> []
          List gt -> []
          _ -> undefined


op2Codes :: Map.Map HiddenOp2 Instruction
op2Codes = Map.fromList [ (AST.Plus, ADD), (AST.Minus, SUB),  (AST.Multiply, MUL), (AST.Divide, DIV), (AST.Modulo, MOD)
                   , (AST.SmallerEqualThan, LE), (AST.BiggerEqualThan, GE),  (AST.SmallerThan, Compiler.SSM.LT),  (AST.BiggerThan, Compiler.SSM.GT),
                      (AST.Equal, Compiler.SSM.EQ), (AST.NotEqual, NEQ), (AST.And, AND), (AST.Or, OR) ]

op1Codes :: Map.Map HiddenOp1 Instruction
op1Codes = Map.fromList [ (AST.Not, NOT), (AST.Negative, NEG)]

variableToInstructions :: Variable -> CodeParser [Instruction]
variableToInstructions var@(Typed (GlobalVariable string tExpr) gType _) = case gType of
  List gt -> listVariableToInstructions var
  Pair gt gt'-> pairVariableToInstructions var
  _ -> do
    counter <- getGlobalVariableCounter
    insertGlobalVar string gType (Heap counter)
    incrementGlobalVariableCounter

    expr <- exprToInstructions (Just string) tExpr
    return $ expr ++ storeVariable
variableToInstructions var@(Typed (LocalVariable string tExpr) gType _) = case gType of
  List gt -> listVariableToInstructions var
  Pair gt gt'-> pairVariableToInstructions var
  _ -> do
    counter <- getLocalCounter
    insertLocalVar string gType (Mark counter)
    incrementLocalCounter
    exprToInstructions (Just string) tExpr >>= \r -> return $ r ++ [STL counter, AJS 1]
variableToInstructions var@(Typed (FunctionVariable name) gType _) = case gType of
  List gt -> listVariableToInstructions var
  Pair gt gt'-> pairVariableToInstructions var
  _ -> do
    decrementFunctionCounter
    counter <- getFunctionCounter
    insertFunctionVar name gType (Mark counter)
    return []

listVariableToInstructions :: Variable -> CodeParser [Instruction]
listVariableToInstructions (Typed (GlobalVariable name tExpr) gType _) = do
  counter <- getGlobalVariableCounter
  insertGlobalVar name gType (Heap counter)
  incrementGlobalVariableCounter

  load <- loadVariable name
  expr <- exprToInstructions (Just name) tExpr

  -- First reserve space for the list variable
  -- Then load the expression
  -- Load the variable location
  -- Store the variable location in the pointer
  return $ reserveVariable ++ expr ++ load ++ [STA 0]
listVariableToInstructions (Typed (LocalVariable name tExpr) gType _) = do
  counter <- getLocalCounter
  insertLocalVar name gType (Mark counter)
  incrementLocalCounter

  load <- loadVariable name
  expr <- exprToInstructions (Just name) tExpr

  -- TODO: Implement local list variables
  return $ expr ++ load ++ [STA 0]
listVariableToInstructions (Typed (FunctionVariable name) gType _) = do
  decrementFunctionCounter
  counter <- getFunctionCounter
  insertFunctionVar name gType (Mark counter)
  return []

reserveVariable :: Code
reserveVariable = LDC 0 : storeVariable

storeVariable :: Code
storeVariable = [STS 0, AJS 1]

pairVariableToInstructions :: Variable -> CodeParser [Instruction]
pairVariableToInstructions (Typed (GlobalVariable name tExpr) gType _) = do
  counter <- getGlobalVariableCounter
  insertGlobalVar name gType (Heap counter)
  incrementGlobalVariableCounter

  load <- loadVariable name
  expr <- exprToInstructions (Just name) tExpr

  return $ reserveVariable ++ expr ++ load ++ [STA 0]
pairVariableToInstructions (Typed (LocalVariable name tExpr) gType _) = do
  counter <- getLocalCounter
  insertLocalVar name gType (Mark counter)
  incrementLocalCounter

  load <- loadVariable name
  expr <- exprToInstructions (Just name) tExpr

  return $ reserveVariable ++ expr ++ [LDC 1, SUB] ++ load ++ [STA 0]
pairVariableToInstructions (Typed (FunctionVariable name) gType _) = do
  decrementFunctionCounter
  counter <- getFunctionCounter
  insertFunctionVar name gType (Mark counter)
  return []

loadVariable :: String -> CodeParser Code
loadVariable name = do
  localVarmap <- getLocalVarMap
  case Map.lookup name localVarmap of
    Just dl -> helper dl
    Nothing -> do
      functionVarMap <- getFunctionStateMap
      case Map.lookup name functionVarMap of
        Just dl -> helper dl
        Nothing -> do
          globalVarMap <- getGlobalVarMap
          case Map.lookup name globalVarMap of
            Just dl -> helper dl
            Nothing -> error $ "Variable " ++ name ++ " not found" ++ show functionVarMap
  where
    helper :: (DataLocation, GenericType) -> CodeParser Code
    helper (m, t) = do
      case m of
        Mark i -> return [LDR MP, LDC i, ADD]
        Heap i -> return [LDR R6, LDC (i + 1), ADD]
        _ -> error "Unreachable code"

functionToInstructions :: Function' -> String -> CodeParser [Instruction]
functionToInstructions func@(Function string funcVars vars stmts) name = do
  setFunction name
  args <- concat <$> mapM variableToInstructions funcVars
  variables <- concat <$> mapM variableToInstructions vars

  let totalVars = length funcVars
  parsedStatements <- stmtsToInstructions stmts

  let newparsedStatements = if not (null stmts) && statementIsReturn (last stmts) then parsedStatements else parsedStatements ++ [UNLINK, RET]

  let statementsCode = case string of
        "main" -> map (\x -> if x == RET then HALT else x) parsedStatements
        _ -> newparsedStatements
  return $ [LABEL string, LINK totalVars] ++ args ++ variables ++ statementsCode

statementIsReturn :: Statement -> Bool
statementIsReturn (Tokened stmt _) = statementIsReturn' stmt
  where
    statementIsReturn' :: HiddenStatement -> Bool
    statementIsReturn' (Return _) = True
    statementIsReturn' _ = False

createIsEmptyList :: CodeParser Code
createIsEmptyList = return [
  LABEL "IsEmpty", LINK 0, LDR MP, LDC 2, SUB, LDA 0, LDA 0, LDC emptyListValue, Compiler.SSM.EQ, BRT "IsEmptyTrue",
  LABEL "IsEmptyFalse", LDC 0, STR RR, UNLINK, RET,
  LABEL "IsEmptyTrue", LDC 1, STR RR, UNLINK, RET
  ]

printExpression :: TypedExpression -> CodeParser Code
printExpression tExpr@(Typed expr t _) = printExpression' expr t
  where
    printExpression' :: Expression' -> GenericType -> CodeParser Code
    printExpression' expr@(IntValue i) _ = do
      expr <- exprToInstructions Nothing tExpr
      return $ printBasic AST.INT expr True
    printExpression' expr@(CharValue c) _ = do
      expr <- exprToInstructions Nothing tExpr
      return $ printBasic AST.CHAR expr True
    printExpression' expr@(BoolValue b) _ = do
      expr <- exprToInstructions Nothing tExpr
      return $ printBasic AST.BOOL expr True
    printExpression' (BinaryExpr op e1 e2) t = do
      e1' <- exprToInstructions Nothing e1
      e2' <- exprToInstructions Nothing e2
      case t of
        Basic bt -> return $ printBasic bt (e1' <> e2') True
        Void -> printString "Void"
        _ -> error "Cannot print"
    printExpression' expr@(UnaryExpr op e) t = do
      e' <- exprToInstructions Nothing tExpr
      case t of
        Basic bt -> return $ printBasic bt e' True
        _ -> error "Cannot print"
    printExpression' (BracedExpression e) _ = printExpression e
    printExpression' EmptyList _ = printString "[]"
    printExpression' (PairExpression _) (Pair t1 t2) = printPairExpression (t1, t2) tExpr
    printExpression' (PairExpression _) _ = error "Cannot print pair"
    printExpression' expr@(ExprId name fld) gType = case gType of
      Basic bt -> exprToInstructions Nothing tExpr >>= \e -> return $ printBasic bt e True
      Pair gt gt' -> printPairExpression (gt, gt') tExpr
      List gt -> do
        variable <- exprToInstructions Nothing tExpr

        print <- printList gt
        return $ variable ++ print
      _ -> do
        error "Cannot print"
    printExpression' expr@(ExprFunCall funcall) gType = case gType of
      Basic bt -> do
        e' <- exprToInstructions Nothing tExpr
        return $ printBasic bt e' True
      Pair gt gt' -> printPairExpression (gt, gt') tExpr
      List gt -> printList gt
      _ -> error ("Cannot print: " ++ show expr)
    printExpression' (ListExpr exprs final) (List gType) = printListExpression tExpr gType
    printExpression' (ListExpr exprs final) _ = error "Cannot print list"

printChar :: Char -> Bool -> Code
printChar c = printBasic AST.CHAR [LDChar c]

printNewLine :: Code
printNewLine = printChar '\n' False

printBasic :: AST.BasicType -> Code -> Bool -> Code
printBasic AST.INT code keep = code ++ printBasicRaw AST.INT keep
printBasic AST.CHAR code keep = code ++ printBasicRaw AST.CHAR keep
printBasic AST.BOOL code keep = code ++ printBasicRaw AST.BOOL keep

printBasicRaw :: AST.BasicType -> Bool -> Code
printBasicRaw t True = printBasicRaw t False ++ [AJS 1]
printBasicRaw t _ = case t of
  AST.INT -> [TRAP 0]
  AST.CHAR -> [TRAP 1]
  AST.BOOL -> [TRAP 0]

printPairExpression :: (GenericType, GenericType) -> TypedExpression -> CodeParser Code
printPairExpression (t1, t2) expr = do
  code <- exprToInstructions Nothing expr
  pairCode <- printPair (t1, t2)
  return $ code ++ pairCode

printPair :: (GenericType, GenericType) -> CodeParser Code
printPair (t1, t2) = printPair' (t1, t2)
  where
    printPair' :: (GenericType, GenericType) -> CodeParser Code
    printPair' (t1, t2) = do
      let funcType = Pair t1 t2
      let funcName = getPrintName funcType
      let returnCode = [BSR funcName]

      alreadyExists <- printHasType funcType

      let start = printChar '(' False
      let _middle = printChar ',' False
      let middle = if not $ isBasicType t1 then _middle ++ [SWP] else _middle
      let end = printChar ')' False

      if alreadyExists then do
        return returnCode
        else do

        left <- handlePair t1
        right <- handlePair t2

        let funcCode = [LABEL funcName, LINK 0, LDR MP, LDC 2, SUB, LDA 0, LDMA 0 2, SWP] ++ start ++ left ++ middle ++ right ++ end ++ [UNLINK, RET]
        addPrintMap funcType funcCode

        return returnCode
    handlePair :: GenericType -> CodeParser Code
    handlePair (Basic bt) = return $ printBasicRaw bt False
    handlePair (Pair gt gt') = printPair' (gt, gt')
    handlePair (List gt) = printList gt >>= \t -> return $ t ++ [AJS (-2)]
    handlePair _ = undefined

getPrintName :: GenericType -> String
getPrintName gType = "_Print" ++ typeToString gType

isBasicType :: GenericType -> Bool
isBasicType (Basic _) = True
isBasicType _ = False

printListExpression :: TypedExpression -> GenericType -> CodeParser Code
printListExpression expr gType = do
  code <- exprToInstructions Nothing expr
  printCode <- printList gType
  return $ code ++ printCode

printList :: GenericType -> CodeParser Code
printList gType = printList' gType False
  where
    printList' gType inner = do
      alreadyExists <- printHasType (List gType)

      let funcName = getPrintName (List gType)
      let innerName = funcName ++ "True"
      let innerName2 = funcName ++ "2"
      let endName = funcName ++ "False"
      let returnCode = if inner then [LDC 0, BSR funcName] else [LDC 0, LDC 0, BSR funcName]

      if alreadyExists then do
        return returnCode
      else do

        let start = if gType == Basic AST.CHAR then [] else printChar '[' False
        let middle = if gType == Basic AST.CHAR then [] else printChar ',' False
        let end = if gType == Basic AST.CHAR then [] else printChar ']' False

        let createFunc =  [LABEL funcName, LINK 0]
        let load = [LDR MP, LDC 4, SUB, LDA 0, BRA innerName]
        let final = [LABEL endName] ++ end ++ [UNLINK, RET]

        let isStartElement = [LDC emptyListValue, SWP, Compiler.SSM.EQ, AJS 1, SWP, BRT endName]

        case gType of
          Basic bt -> do
            basicPrint <- case bt of
              AST.INT -> return $ printBasicRaw AST.INT True
              AST.CHAR -> return $ printBasicRaw AST.CHAR True
              AST.BOOL -> return $ printBasicRaw AST.BOOL True

            let inner = [LABEL innerName2] ++ middle ++ [LABEL innerName, LDMA 0 2, SWP] ++ isStartElement ++ basicPrint ++ [SWP, LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT innerName2, BRF endName]

            let newFuncCode = createFunc ++ start ++ load ++ inner ++ final

            addPrintMap (List gType) newFuncCode
            return returnCode
          Pair gt gt' -> do
            printPairCode <- printPair (gt, gt')
            let inner = [LABEL innerName2] ++ middle ++ [LABEL innerName, LDMA 0 2, SWP] ++ isStartElement ++ printPairCode ++ [AJS (-1), LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT innerName2, BRF endName]
            let newFuncCode = createFunc ++ start ++ load ++ inner ++ final

            addPrintMap (List gType) newFuncCode
            return returnCode
          List gt -> do
            printListCode <- printList' gt True

            let isStartElement' = [SWP] ++ isStartElement ++ [SWP]
            let inner = [LABEL innerName2] ++ middle ++ [LABEL innerName, LDMA 0 2] ++ isStartElement' ++ printListCode ++ [AJS (-1), LDC (-1), SWP, Compiler.SSM.NEQ, AJS 1, SWP, BRT innerName2, BRF endName]
            let newFuncCode = createFunc ++ start ++ load ++ inner ++ final

            addPrintMap (List gType) newFuncCode
            return returnCode
          _ -> error "Cannot print"

printString :: String -> CodeParser Code
printString s = return $ concatMap (\c -> [LDChar c, TRAP 1]) s

codeToString :: Code -> String
codeToString = foldr ((\x1 x2 -> x1 ++ "\n" ++ x2) . show) ""

printToFile :: Code -> String -> IO ()
printToFile code name = do
  let outPutDir = "out/"
  createDirectoryIfMissing True outPutDir
  writeFile (outPutDir ++ name ++ ".ssm") (codeToString code)

compileAST ::  String -> TypedAST -> IO ()
compileAST fileName ast = do
  let code = runStateT (performAST ast) (emptyState (getFunctions ast))
  case code of
    Left err -> print err
    Right (result, state) -> do
      printToFile result fileName
      -- print state
  where
    performAST :: TypedAST -> CodeParser Code
    performAST ast = do
      let stackStart = [LDR SP, STR R6]
      funcs <- (`functionMapToFunctions` True) <$> getFuncMaps

      globalVariables <- concat <$> mapM variableToInstructions (getVariables ast)
      functions <- concat <$> mapM (\(name, x) -> functionToInstructions (getTyped x) name) funcs

      prints <- concat . Map.elems <$> getPrintMap
      copies <- concat . Map.elems <$> getCopyMap

      isEmptyCode <- createIsEmptyList
      segmantation <- printString "SEGMENTATION FAULT"

      return $ stackStart ++ [BRA "__start"] ++ prints ++ copies ++ isEmptyCode ++ (LABEL "____ListEmpty" : segmantation ++ [HALT]) ++ [LABEL "__start"] ++ globalVariables ++ [BRA "main"] ++ functions
