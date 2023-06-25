{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Compiler.Unification where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans.State( evalState, runState, StateT (runStateT) )
import qualified Control.Monad.Identity as MIdentity ( Identity, runIdentity )
import Control.Monad.State.Class ( MonadState(put, get) )
import Control.Monad.Error.Class (MonadError, throwError, catchError)
import qualified Compiler.AST as AST
import Compiler.TypedAST
 (
    Expression'
    (
      ListExpr,
      UnaryExpr,
      BinaryExpr,
      IntValue,
      CharValue,
      BoolValue,
      BracedExpression,
      PairExpression,
      ExprFunCall,
      ExprId,
      EmptyList
    ),
    Function,
    Function'(..),
    FunctionCall,
    FunctionCall'(IsEmptyFunCall, FunCall, PrintFunCall),
    GenericType(..),
    Statement(..),
    Typed(..),
    TypedAST(..),
    TypedExpression,
    TypedRoot(..),
    Variable,
    Variable'(..),
    HiddenStatement (..), getTyped, setTyped, FuncMap, getType, FuncTypeMap
  )
import Data.Maybe ( fromJust, mapMaybe, fromMaybe )
import Data.Functor.Identity (Identity(Identity, runIdentity))
import Control.Monad (when, foldM, unless, ap, liftM, zipWithM, forM_)
import Control.Monad.Trans.Except ( ExceptT, runExceptT )
import Data.Foldable (foldrM)
import Compiler.AST (HiddenExpression(BadList))
import Data.Type.Equality (apply)
import Compiler.Token (getTokened, Tokened (..), getTokenedTokens, PositionedToken, getTokenedRange, getTokenRange)
import Control.Monad.Trans.Class (lift)
import Data.List (isPrefixOf, nub, find)
import Compiler.Position (PositionRange (..), Position (Position), getPosition, setNewRange)
import Data.Default (Default(def))
import Control.Arrow (Arrow(first))
import GHC.Stack (HasCallStack)

type FuncState = String
type State = (Int, String, TypeEnv, FuncMap, PositionRange)

data Error = Error Error' PositionRange
  deriving (Eq, Show)
data Error' =
    TypeMismatch GenericType GenericType
  | ReturnTypeMismatch GenericType GenericType
  | FunctionNotFound String
  | FunctionArgumentLengthMismatch String Int Int
  | VariableNotFound String
  | TypeVariableNotFound String
  | CircularTypeVariable String
  | UnifyError GenericType GenericType
  | TypeNotFound String
  | FieldAccess AST.Field GenericType
  | VariableWrongType AST.VarDeclaration GenericType
  deriving (Eq, Show)

type Result a = (a, [Error])
newtype UnifyM a = UnifyM { runUnifyM :: StateT State (ExceptT [Error] MIdentity.Identity) (Result a) }
type TypeEnv = (Map String GenericType, Map String GenericType)

instance Functor UnifyM where
  fmap = liftM

instance Applicative UnifyM where
  pure = return
  (<*>) = ap

instance Monad UnifyM where
  return x = UnifyM $ return (x, [])
  m >>= f = UnifyM $ do
    (x, errs) <- runUnifyM m
    (y, errs') <- runUnifyM (f x)
    return (y, errs ++ errs')

instance MonadState State UnifyM where
  get = UnifyM $ get >>= \s -> return (s, [])
  put s = UnifyM $ put s >> return ((), [])

instance MonadError [Error] UnifyM where
  throwError err = UnifyM $ lift $ throwError err
  catchError (UnifyM x) f = UnifyM $ catchError x (runUnifyM . f)

emptyFuncMap :: FuncMap
emptyFuncMap = Map.empty

emptyState :: State
emptyState = (0, "", emptyTypeEnv, emptyFuncMap, PositionRange (Position 0 0) (Position 0 0))

getCurrentTokens :: UnifyM PositionRange
getCurrentTokens = do
  (_, _, _, _, currentTokens) <- get
  return currentTokens

putCurrentTokens :: PositionRange -> UnifyM ()
putCurrentTokens currentTokens = do
  (n, funcState, typeEnv, funcMap, _) <- get
  put (n, funcState, typeEnv, funcMap, currentTokens)

setCurrentTokens :: Tokened a -> UnifyM ()
setCurrentTokens tokened = putCurrentTokens (getTokenedRange tokened)

setCurrentTokensTyped :: Typed a -> UnifyM ()
setCurrentTokensTyped typed = do
  let x = getTypedTokens typed
  let y = foldr (setNewRange . getPosition) (getPosition (head x)) x
  putCurrentTokens y

getTypedTokens :: Typed a -> [PositionedToken]
getTypedTokens (Typed _ _ tokens) = tokens

getStateCounter :: UnifyM Int
getStateCounter = do
  (n, _, _, _, _) <- get
  return n

putStateCounter :: Int -> UnifyM ()
putStateCounter n = do
  (_, funcState, typeEnv, funcMap, currentTokens) <- get
  put (n, funcState, typeEnv, funcMap, currentTokens)

getTypeEnv :: UnifyM TypeEnv
getTypeEnv = do
  (_, _, typeEnv, _, _) <- get
  return typeEnv

getTypeVarMap :: UnifyM (Map String GenericType)
getTypeVarMap = do
  fst <$> getTypeEnv

getVarTypeMap :: UnifyM (Map String GenericType)
getVarTypeMap = do
  snd <$> getTypeEnv

putTypeEnv :: TypeEnv -> UnifyM ()
putTypeEnv typeEnv = do
  (n, funcState, _, funcMap, currentTokens) <- get
  put (n, funcState, typeEnv, funcMap, currentTokens)

getFunctionMap :: UnifyM FuncMap
getFunctionMap = do
  (_, _, _, funcMap, _) <- get
  return funcMap

putFunctionMap :: FuncMap -> UnifyM ()
putFunctionMap funcMap = do
  (n, funcState, typeEnv, _, currentTokens) <- get
  put (n, funcState, typeEnv, funcMap, currentTokens)

removePolyFunctions :: FuncTypeMap -> FuncTypeMap
removePolyFunctions funcMap = Map.fromList (filter (\(types, _) -> not $ any isFreshTypeVar types) $ Map.toList funcMap)

getPolyFunction :: String -> UnifyM Function
getPolyFunction name = do
  funcMap <- getFunctionMap
  case Map.lookup name funcMap of
    Just funcMap -> do
      let x = Map.toList funcMap
      case find (\(types, _) -> any isFreshTypeVar types) x of
        Just (_, func) -> return func
        Nothing -> return $ snd $ head x
    Nothing -> throwErrorFunc [FunctionNotFound name]

getFunction :: HasCallStack => String -> [GenericType] -> UnifyM Function
getFunction name types = do
  funcMap <- getFunctionMap
  case Map.lookup name funcMap of
    Just func -> case Map.lookup types func of
      Just func' -> return func'
      Nothing -> throwErrorFunc [FunctionNotFound name]
    Nothing -> throwErrorFunc [FunctionNotFound name]

getFunctionReturnType :: String -> [GenericType] -> UnifyM GenericType
getFunctionReturnType name types = do
  func <- getFunction name types
  return $ getFunctionType func

addEmptyFunction :: String -> UnifyM ()
addEmptyFunction name = do
  funcMap <- getFunctionMap
  putFunctionMap (Map.insert name Map.empty funcMap)

putFunction :: Function -> UnifyM ()
putFunction func = do
  funcMap <- getFunctionMap
  let name = getFunctionName func
  let types = getFunctionTypes func
  let funcMap' = Map.insert name (Map.insert types func (Map.findWithDefault Map.empty name funcMap)) funcMap
  putFunctionMap funcMap'

typeIdToString :: GenericType -> String
typeIdToString (TypeId name _) = name
typeIdToString _ = error "Not a fresh type variable"

setVariableType :: Variable -> GenericType -> Variable
setVariableType (Typed v t pos) newT = Typed v newT pos

addCallToFunctionInStmts :: [Statement] -> UnifyM ()
addCallToFunctionInStmts [] = return ()
addCallToFunctionInStmts (x:xs) = case getTokened x of
  If _ ifs elses -> do
    addCallToFunctionInStmts ifs
    addCallToFunctionInStmts (fromMaybe [] elses)
    addCallToFunctionInStmts xs
  While _ stmts -> do
    addCallToFunctionInStmts stmts
    addCallToFunctionInStmts xs
  StatementFunCall (Typed (FunCall name args) _ _) -> do
    func <- getPolyFunction name
    let funcTypes = getFunctionArgTypes func
    let callTypes = map getType args
    let types = zip funcTypes callTypes
    subs <- mapM (uncurry unify) types
    let substitution = if null subs then emptyTypeEnv else foldl1 (<>) subs
    addCallToFunction name substitution
    addCallToFunctionInStmts xs
  _ -> addCallToFunctionInStmts xs

applySubstitutionFunCall :: TypeEnv -> FunctionCall -> UnifyM FunctionCall
applySubstitutionFunCall env (Typed call t pos) = case call of
  FunCall s tys -> do
    tys' <- mapM (applySubstitutionExpr env) tys
    t' <- applySubstitution env t
    return $ Typed (FunCall s tys') t' pos
  PrintFunCall ty -> do
    ty' <- applySubstitutionExpr env ty
    t' <- applySubstitution env t
    return $ Typed (PrintFunCall ty') t' pos
  IsEmptyFunCall ty -> do
    ty' <- applySubstitutionExpr env ty
    t' <- applySubstitution env t
    return $ Typed (IsEmptyFunCall ty') t' pos

applySubstitutionExpr :: TypeEnv -> TypedExpression -> UnifyM TypedExpression
applySubstitutionExpr env tExpr@(Typed expr t pos) = case expr of
  ListExpr exprs finalExpr -> do
    newTys <- mapM (applySubstitutionExpr env) exprs
    newTy <- applySubstitutionExpr env finalExpr
    newType <- applySubstitution env t
    return $ Typed (ListExpr newTys finalExpr) newType pos
  BinaryExpr to ty ty' -> do
    newTy <- applySubstitutionExpr env ty
    newTy' <- applySubstitutionExpr env ty'
    newType <- applySubstitution env t
    return $ Typed (BinaryExpr to newTy newTy') newType pos
  UnaryExpr to ty -> do
    newTy <- applySubstitutionExpr env ty
    newType <- applySubstitution env t
    return $ Typed (UnaryExpr to newTy) newType pos
  BracedExpression ty -> do
    newTy <- applySubstitutionExpr env ty
    newType <- applySubstitution env t
    return $ Typed (BracedExpression newTy) newType pos
  ExprFunCall funcCall -> do
    newTy <- applySubstitutionFunCall env funcCall
    newType <- applySubstitution env t
    return $ Typed (ExprFunCall newTy) newType pos
  PairExpression (left, right) -> do
    newLeft <- applySubstitutionExpr env left
    newRight <- applySubstitutionExpr env right
    newType <- applySubstitution env t
    return $ Typed (PairExpression (newLeft, newRight)) newType pos
  _ -> do
    newType <- applySubstitution env t
    return $ Typed expr newType pos

applySubstitutionStmt :: TypeEnv -> Statement -> UnifyM Statement
applySubstitutionStmt env (Tokened stmt pos) = case stmt of
  If ty tos m_tos -> do
    newTy <- applySubstitutionExpr env ty
    newTos <- mapM (applySubstitutionStmt env) tos
    newMTos <- mapM (applySubstitutionStmt env) (fromMaybe [] m_tos)
    return $ Tokened (If ty newTos (Just newMTos)) pos
  While ty tos -> do
    newTy <- applySubstitutionExpr env ty
    newTos <- mapM (applySubstitutionStmt env) tos
    return $ Tokened (While ty newTos) pos
  VarAssign s m_to ty -> do
    newTy <- applySubstitutionExpr env ty
    return $ Tokened (VarAssign s m_to ty) pos
  StatementFunCall ty -> do
    newTy <- applySubstitutionFunCall env ty
    return $ Tokened (StatementFunCall newTy) pos
  Return m_ty -> do
    newTy <- mapM (applySubstitutionExpr env) m_ty
    return $ Tokened (Return newTy) pos

addCallToFunction :: String -> TypeEnv -> UnifyM ()
addCallToFunction name call = do
  func <- getPolyFunction name
  let (Function name args vars statmenets) = getTyped func
  newArgs <- mapM (\v -> applySubstitution call (getType v) >>= \newType -> return $ setVariableType v newType) args
  newStatements <- mapM (applySubstitutionStmt call) statmenets

  let newFunc = setTyped (Function name newArgs vars newStatements) func

  addCallToFunctionInStmts newStatements
  putFunction newFunc

-- addCallToFunction :: String -> [GenericType] -> UnifyM ()
-- addCallToFunction name call = do
--   func <- getPolyFunction name
--   let (Function name args vars statmenets) = getTyped func
--   let zipped = zip args call
--   let newArgs = map (uncurry setVariableType) zipped
--   let newFunc = setTyped (Function name newArgs vars statmenets) func

--   -- Do addCallToFunction for every function call in the statements
--   -- addCallToFunctionInStmts statmenets

--   putFunction newFunc

-- addCallToFunction :: String -> [GenericType] -> UnifyM ()
-- addCallToFunction name call = do
--   func <- getFunction name
--   let (Function name args vars statmenets funcCalls) = getTyped func

--   let zipped = zip args call
--   let res = Map.fromList (map ((\(x, y) -> (typeIdToString $ getVariableType x, y))) $ filter (\(x, y) -> isFreshTypeVar (getVariableType x)) zipped)

--   let newFunc = setTyped (Function name args vars statmenets (nub $ res : funcCalls)) func
--   putFunction newFunc

getFuncState :: UnifyM FuncState
getFuncState = do
  (_, funcState, _, _, _) <- get
  return funcState

putFuncState :: FuncState -> UnifyM ()
putFuncState funcState = do
  (n, _, typeEnv, funcMap, currentTokens) <- get
  put (n, funcState, typeEnv, funcMap, currentTokens)

setFuncName :: String -> UnifyM ()
setFuncName name = do
  putFuncState name

getFuncName :: UnifyM String
getFuncName = getFuncState

addFuncArg :: Variable -> UnifyM ()
addFuncArg var = do
  typeEnv <- getTypeEnv
  name <- getFuncArgName (getVariableName var)
  putTypeEnv (insertVarType name (getVariableType var) typeEnv)

addFuncVar :: Variable -> UnifyM ()
addFuncVar var = do
  typeEnv <- getTypeEnv
  name <- getFuncVarName (getVariableName var)
  putTypeEnv (insertVarType name (getVariableType var) typeEnv)

getInnerTyped :: Typed a -> (a, GenericType)
getInnerTyped (Typed a gType _) = (a, gType)

getFunctionName :: Function -> String
getFunctionName f = getInnerFunctionName . fst $ getInnerTyped f

getFunctionTypes :: Function -> [GenericType]
getFunctionTypes f = getInnerFunctionArgTypes . fst $ getInnerTyped f
  where
    getInnerFunctionArgTypes (Function _ args _ _) = map getVariableType args

getInnerFunctionName :: Function' -> String
getInnerFunctionName (Function id _ _ _) = id

getFunctionType :: Function -> GenericType
getFunctionType f = snd $ getInnerTyped f

getFunctionArgTypes :: Function -> [GenericType]
getFunctionArgTypes f = getInnerFunctionArgTypes . fst $ getInnerTyped f
    where
        getInnerFunctionArgTypes (Function _ args _ _) = map getVariableType args

addFunc :: Function -> UnifyM ()
addFunc func = do
  typeEnv <- getTypeEnv
  putTypeEnv (insertVarType (getFunctionName func) (getFunctionType func) typeEnv)

addTypeId :: String -> GenericType -> UnifyM ()
addTypeId id t = do
  typeEnv <- getTypeEnv
  putTypeEnv (insertTypeVar id t typeEnv)

getVariableType :: Variable -> GenericType
getVariableType v = snd $ getInnerTyped v

getVariableName :: Variable -> String
getVariableName v = getInnerVariableName . fst $ getInnerTyped v
  where
    getInnerVariableName (GlobalVariable id _) = id
    getInnerVariableName (LocalVariable id _) = id
    getInnerVariableName (FunctionVariable id) = id

getFuncArgName :: String -> UnifyM String
getFuncArgName arg = do
  id <- getFuncName
  if null id then return arg
  else return ("#" ++ id ++ "_" ++ arg)

getFuncVarName :: String -> UnifyM String
getFuncVarName arg = do
  id <- getFuncName
  if null id then return arg
  else return ("##" ++ id ++ "_" ++ arg)

isInFuncArgs :: String -> UnifyM Bool
isInFuncArgs arg = do
  funcArgName <- getFuncArgName arg
  isInVarTypeMap funcArgName

isInFuncVars :: String -> UnifyM Bool
isInFuncVars var = do
  funcVarName <- getFuncVarName var
  isInVarTypeMap funcVarName

isInVarTypeMap :: String -> UnifyM Bool
isInVarTypeMap ident = do
  varTypeMap <- getVarTypeMap
  return (ident `Map.member` varTypeMap)

freshTypeVar :: UnifyM (GenericType, String)
freshTypeVar = do
  n <- getStateCounter
  putStateCounter (n + 1)
  let name = "_t" ++ show n
  return (TypeId name True, name)

isFreshTypeVar :: GenericType -> Bool
isFreshTypeVar (TypeId name True) = True
isFreshTypeVar GenericType = True
isFreshTypeVar _ = False

createTyped :: a  -> GenericType -> [PositionedToken] -> UnifyM (Typed a)
createTyped a gType tokens = case gType of
  GenericType -> freshTypeVar >>= \(t, _) -> return $ Typed a t tokens
  _ -> return $ Typed a gType tokens

emptyTypeEnv :: TypeEnv
emptyTypeEnv = (Map.empty, Map.empty)

unionTypeEnv :: TypeEnv -> TypeEnv -> TypeEnv
unionTypeEnv (env1, env2) (env3, env4) = (Map.union env1 env3, Map.union env2 env4)

insertTypeVar :: String -> GenericType -> TypeEnv -> TypeEnv
insertTypeVar ident t (env, env2) = (Map.insert ident t env, env2)

singletonTypeVar :: String -> GenericType -> TypeEnv
singletonTypeVar ident t = (Map.singleton ident t, Map.empty)

getTypeVar :: String -> TypeEnv -> UnifyM GenericType
getTypeVar ident (env, _) = case Map.lookup ident env of
  Just t -> return t
  Nothing -> throwError' [TypeVariableNotFound ident]

lookupTypeVar :: String -> TypeEnv -> Maybe GenericType
lookupTypeVar ident (env, _) = Map.lookup ident env

insertVarType :: String -> GenericType -> TypeEnv -> TypeEnv
insertVarType ident t (env, env2) = (env, Map.insert ident t env2)

singletonVarType :: String -> GenericType -> TypeEnv
singletonVarType ident t = (Map.empty, Map.singleton ident t)

getVarType :: String -> TypeEnv -> UnifyM GenericType
getVarType ident (_, env) = case Map.lookup ident env of
  Just t -> return t
  Nothing -> throwErrorType [VariableNotFound ident]

lookupVarType :: String -> TypeEnv -> Maybe GenericType
lookupVarType ident (_, env) = Map.lookup ident env

applySubstitution :: TypeEnv -> GenericType -> UnifyM GenericType
applySubstitution subst (Var ident) = getTypeVar ident subst `catchError` (\err -> UnifyM $ return (Var ident, []))
applySubstitution subst (Pair t1 t2) = do
  left <- applySubstitution subst t1
  right <- applySubstitution subst t2
  return $ Pair left right
applySubstitution subst (List t) = applySubstitution subst t >>= \res -> return $ List res
applySubstitution _ (Basic bt) = return $ Basic bt
applySubstitution subst (TypeId ident isGenerated) = getTypeVar ident subst `catchError` (\err -> UnifyM $ return (TypeId ident isGenerated, []))
applySubstitution _ GenericType = return GenericType
applySubstitution _ Void = return Void

causesCircularReference :: String -> GenericType -> Bool
causesCircularReference ident (Var ident2) = ident == ident2
causesCircularReference ident (Pair t1 t2) = causesCircularReference ident t1 || causesCircularReference ident t2
causesCircularReference ident (List t) = causesCircularReference ident t
causesCircularReference _ _ = False

unify ::  GenericType -> GenericType -> UnifyM TypeEnv
unify GenericType t = do
  (tVar, name) <- freshTypeVar
  return $ singletonTypeVar name t
unify t GenericType = do
  (tVar, name) <- freshTypeVar
  return $ singletonTypeVar name t
unify (Var ident) t = if causesCircularReference ident t
  then throwErrorTypeEnv [CircularTypeVariable ident]
  else return $ singletonTypeVar ident t
unify t1@(TypeId ident1 True) t2@(TypeId ident2 True)
  | ident1 == ident2 = return emptyTypeEnv
  | otherwise = return $ singletonTypeVar ident1 t2 <> singletonTypeVar ident2 t1
unify t1@(TypeId ident1 False) t2@(TypeId ident2 False) = if ident1 == ident2
  then return emptyTypeEnv
  else throwErrorTypeEnv [UnifyError t1 t2]
unify (TypeId ident _) t = return $ singletonTypeVar ident t
unify t (TypeId ident _) = return $ singletonTypeVar ident t
unify (Basic bt1) (Basic bt2)
  | bt1 == bt2 = return emptyTypeEnv
unify (Pair t1 t2) (Pair t3 t4) = do
  s1 <- unify t1 t3

  left <- applySubstitution s1 t2
  right <- applySubstitution s1 t4

  s2 <- unify left right
  return (s1 `unionTypeEnv` s2)
unify (List t1) (List t2) = unify t1 t2
unify t1 t2
  | (isList t1 && not (isList t2)) || (isList t2 && not (isList t1)) = throwErrorTypeEnv [UnifyError t1 t2]
  | (isPair t1 && not (isPair t2)) || (isPair t2 && not (isPair t1)) = throwErrorTypeEnv [UnifyError t1 t2]
  | otherwise = throwErrorTypeEnv [UnifyError t1 t2]

throwError' :: [Error'] -> UnifyM a
throwError' err = getCurrentTokens >>= \r -> throwError (map (`Error` r) err)

throwErrorGeneric :: a -> [Error'] -> UnifyM a
throwErrorGeneric def err = throwError' err `catchError` (\err -> UnifyM $ return (def, err))

throwErrorTypeEnv :: [Error'] -> UnifyM TypeEnv
throwErrorTypeEnv = throwErrorGeneric emptyTypeEnv

throwErrorType :: [Error'] -> UnifyM GenericType
throwErrorType = throwErrorGeneric GenericType

throwErrorVoid :: [Error'] -> UnifyM ()
throwErrorVoid = throwErrorGeneric ()

throwErrorFunc :: [Error'] -> UnifyM Function
throwErrorFunc = throwErrorGeneric (Typed (Function [] [] [] []) GenericType [])

isList :: GenericType -> Bool
isList (List _) = True
isList _ = False

isPair :: GenericType -> Bool
isPair (Pair _ _) = True
isPair _ = False

inferExpression :: AST.Expression -> UnifyM (TypedExpression, GenericType)
inferExpression _expr@(Tokened a tokens) = do
  oldTokens <- getCurrentTokens
  setCurrentTokens _expr
  res <- case a of
    AST.UnaryExpr op expr -> do
      (typedExpr, exprType) <- inferExpression expr
      case getTokened op of
        AST.Not -> do
          substitution <- unify (Basic AST.BOOL) exprType
          finalExprType <- applySubstitution substitution exprType
          return (Typed (UnaryExpr op typedExpr) finalExprType tokens, finalExprType)
        AST.Negative -> do
          substitution <- unify (Basic AST.INT) exprType
          finalExprType <- applySubstitution substitution exprType
          return (Typed (UnaryExpr op typedExpr) finalExprType tokens, finalExprType)
    (AST.BinaryExpr tOp@(Tokened op _) expr1 expr2)
      | op == AST.Plus || op == AST.Minus || op == AST.Multiply || op == AST.Divide || op == AST.Modulo -> processIntegerExpression -- INT -> Int
      | op == AST.Or || op == AST.And -> processBoolExpression -- Bool to Bool
      | op == AST.Equal || op == AST.NotEqual -> processComparableExpression -- Anything to Bool
      | op == AST.BiggerThan || op == AST.SmallerThan || op == AST.BiggerEqualThan || op == AST.SmallerEqualThan -> processDifferenceComparable -- Char and Int to Bool
      | otherwise -> undefined
      where
        processIntegerExpression = processBinaryExpression (Basic AST.INT) (Basic AST.INT) (Basic AST.INT)
        processBoolExpression = processBinaryExpression (Basic AST.BOOL) (Basic AST.BOOL) (Basic AST.BOOL)
        processComparableExpression = freshTypeVar >>= \(t, _) -> processBinaryExpression t t (Basic AST.BOOL)
        processDifferenceComparable = processBinaryExpression (Basic AST.INT) (Basic AST.INT) (Basic AST.BOOL)
        processBinaryExpression :: GenericType -> GenericType -> GenericType -> UnifyM (TypedExpression, GenericType)
        processBinaryExpression expectedType1 expectedType2 resultType = do
          -- Infer the type and constraints for the expressions
          (typedExpr1, exprType1) <- inferExpression expr1
          (typedExpr2, exprType2) <- inferExpression expr2

          -- Unify the expression types with the expected types
          substitution1 <- unify expectedType1 exprType1
          substitution2 <- unify expectedType2 exprType2

          -- Apply the substitutions to the expression types and create the typed binary expression
          finalExprType1 <- applySubstitution substitution1 exprType1
          finalExprType2 <- applySubstitution substitution2 exprType2

          let insertTypeId (TypeId ident _) t = addTypeId ident t
              insertTypeId _ _ = return ()

          insertTypeId exprType1 finalExprType1
          insertTypeId exprType2 finalExprType2

          return (Typed (BinaryExpr tOp typedExpr1 typedExpr2) resultType tokens, resultType)
    (AST.IntValue value) -> let t = Basic AST.INT in return (Typed (IntValue value) t tokens, t)
    (AST.CharValue value) -> let t = Basic AST.CHAR in return (Typed (CharValue value) t tokens, t)
    (AST.BoolValue value) -> let t = Basic AST.BOOL in return (Typed (BoolValue value) t tokens, t)
    (AST.BracedExpression exp) -> inferExpression exp >>= \(typedExp, t) -> return (Typed (BracedExpression typedExp) t tokens, t)
    (AST.PairExpression (first, second)) -> do
      (typedFirst, firstType) <- inferExpression first
      (typedSecond, secondType) <- inferExpression second
      let t = Pair firstType secondType
      return (Typed (PairExpression (typedFirst, typedSecond)) t tokens, t)
    AST.EmptyList -> freshTypeVar >>= \(t, _) -> let finalT = List t in return (Typed EmptyList finalT tokens, finalT)
    (AST.ExprFunCall funCall) -> do
      (typedFunCall, funCallType) <- inferFunctionCall funCall
      return (Typed (ExprFunCall typedFunCall) funCallType tokens, funCallType)
    (AST.ExprId ident field) -> do
      (name, varType) <- getVariable ident
      finalType <- getVariableFieldType _expr varType field
      return (Typed (ExprId name field) finalType tokens, finalType)
    (AST.ListExpr exprs final) -> do
      -- Infer the type and constraints for the expressions
      typedExpressions <- mapM inferExpression exprs
      substitutions <- mapM (\(typedExpr, exprType) -> unify GenericType exprType) typedExpressions

      let (expressions, types) = splitPair typedExpressions
      let subsZipped = zip typedExpressions substitutions

      -- Apply the substitutions to the expression types and create the typed binary expression
      (finalType, finalExprTypes) <- helper subsZipped
      let finalZipped = zip types finalExprTypes

      let insertTypeId (TypeId ident _) t = addTypeId ident t
          insertTypeId _ _ = return ()

      (finalTyped, trulyFinalType) <- case getTokened final of
        (AST.ExprId s m_fi) -> do
          (typedExpr, exprType) <- inferExpression final
          sub <- unify finalType exprType
          t <- applySubstitution sub exprType
          return (typedExpr, t)
        (AST.ExprFunCall _) -> do
          (typedFunCall, funCallType) <- inferExpression final
          sub <- unify finalType funCallType
          t <- applySubstitution sub funCallType
          insertTypeId finalType t
          return (setType typedFunCall t, t)
        AST.EmptyList -> return (Typed EmptyList finalType tokens, finalType)
        _ -> undefined

      mapM_ (uncurry insertTypeId) finalZipped

      return (Typed (ListExpr expressions finalTyped) trulyFinalType tokens, trulyFinalType)
    BadList -> undefined
  putCurrentTokens oldTokens
  return res
  where
    helper :: [((TypedExpression, GenericType), TypeEnv)] -> UnifyM (GenericType, [GenericType])
    helper xs = do
      (res, _) <- helper' xs
      return res
      where
        helper' :: [((TypedExpression, GenericType), TypeEnv)] -> UnifyM ((GenericType, [GenericType]), PositionRange)
        helper' [] = return ((List GenericType, []), def)
        helper' [((e, t), s)] = do
          old <- getCurrentTokens
          setCurrentTokensTyped e
          current <- getCurrentTokens
          t' <- applySubstitution s t
          putCurrentTokens old
          return ((List t', [t']), current)
        helper' (x@((e, t), s) : xs) = do
          old <- getCurrentTokens
          ((t', _), hdRange) <- helper' [x]
          ((gt, res), tlRange) <- helper' xs

          putCurrentTokens (hdRange `setNewRange` tlRange)

          substitution <- unify (List t) gt
          finalT <- applySubstitution substitution gt

          putCurrentTokens old

          return ((finalT, t' : res), old)

    setType :: TypedExpression -> GenericType -> TypedExpression
    setType (Typed expr _ tokens) t = Typed expr t tokens

getVariable :: String -> UnifyM (String, GenericType)
getVariable ident = do
  isInFuncArgs <- isInFuncArgs ident
  isInFuncVars <- isInFuncVars ident
  name <- case (isInFuncArgs, isInFuncVars) of
    (_, True) -> getFuncVarName ident
    (True, _) -> getFuncArgName ident
    _ -> return ident
  typeEnv <- getTypeEnv
  varType <- getVarType name typeEnv
  return (name, varType)

splitPair :: [(a,b)] -> ([a], [b])
splitPair [] = ([], [])
splitPair ((a,b):xs) = (a:as, b:bs)
  where
    (as, bs) = splitPair xs

getReturnType :: [GenericType] -> UnifyM (Maybe GenericType)
getReturnType [] = return Nothing
getReturnType (GenericType:xs) = getReturnType xs
getReturnType (x:xs) = do
  y <- getReturnType xs
  case y of
    Nothing -> return $ Just x
    Just y -> do
      substitution <- unify x y
      Just <$> applySubstitution substitution x

inferStatement :: AST.Statement -> GenericType -> UnifyM (Statement, [GenericType])
inferStatement (Tokened stmt tokens) retType = do
  oldTokens <- getCurrentTokens
  res <- case stmt of
    AST.If expr stmts elseStmts -> do
      -- Infer the type and constraints for the expression
      (typedExpr, exprType) <- inferExpression expr

      -- Unify the expression type with the boolean type
      substitution <- unify (Basic AST.BOOL) exprType

      -- Apply the substitution to the expression type and create the typed if statement
      finalExprType <- applySubstitution substitution exprType
      (typedStmts, retTypesIf) <- splitPair <$> mapM (`inferStatement` retType) stmts
      (typedElseStmts, retTypesElse) <- case elseStmts of
        Nothing -> return (Nothing, [])
        Just stmts' -> do
          (typedStmts, ts) <- splitPair <$> mapM (`inferStatement` retType) stmts'
          return (Just typedStmts, ts)

      return (Tokened (If typedExpr typedStmts typedElseStmts) tokens, concat $ retTypesIf <> retTypesElse)
    (AST.While expr stmts) -> do
      -- Infer the type and constraints for the expression
      (typedExpr, exprType) <- inferExpression expr

      -- Unify the expression type with the boolean type
      substitution <- unify (Basic AST.BOOL) exprType

      -- Apply the substitution to the expression type and create the typed while statement
      finalExprType <- applySubstitution substitution exprType
      (typedStmts, retTypes) <- splitPair <$> mapM (`inferStatement` retType) stmts
      return (Tokened (While typedExpr typedStmts) tokens, concat retTypes)
    (AST.Return Nothing) -> return (Tokened (Return Nothing) tokens, [Void])
    (AST.Return (Just expr)) -> do
      -- Infer the type and constraints for the expression
      (typedExpr, exprType) <- inferExpression expr

      -- Create the typed return statement
      return (Tokened (Return (Just typedExpr)) tokens, [exprType])
    (AST.VarAssign ident field expr) -> do
      -- Infer the type and constraints for the expression
      (typedExpr, exprType) <- inferExpression expr

      -- Check if the expression type is the same as the type of the variable
      (name, varType) <- getVariable ident

      -- Get the actual type of the variable by using the field
      varType <- getVariableFieldType expr varType field
      substitution <- unify varType exprType

      -- Throw an error if the var and expr types are not the same
      _finalExprType <- applySubstitution substitution exprType
      finalExprType <- if _finalExprType /= exprType then throwErrorType [TypeMismatch exprType _finalExprType] else return _finalExprType

      case varType of
        TypeId s _ -> do
          typeEnv <- getTypeEnv
          let newTypeEnv = insertTypeVar s finalExprType (typeEnv `unionTypeEnv` substitution)
          putTypeEnv newTypeEnv
        _ -> return ()

      -- Create the typed variable assignment statement
      return (Tokened (VarAssign name field typedExpr) tokens, [])
    (AST.StatementFunCall funCall) -> do
      -- Infer the type and constraints for the function call
      (typedFunCall, t) <- inferFunctionCall funCall

      -- Create the typed function call statement
      return (Tokened (StatementFunCall typedFunCall) tokens, [])
  putCurrentTokens oldTokens
  return res


inferFunctionCall :: AST.FunctionCall -> UnifyM (FunctionCall, GenericType)
inferFunctionCall (Tokened funCall tokens) = do
  oldTokens <- getCurrentTokens
  res <- case funCall of
    AST.FunCall ident exprs -> do
      -- Infer the type and constraints for the expressions
      (typedFuncArgs, funcArgTypes) <- splitPair <$> mapM inferExpression exprs

      -- Get the type of the function
      func <- getPolyFunction ident
      let funcType = getFunctionType func
      let funcArgsType = getFunctionArgTypes func

      -- Unify the types of the function call with the types of the function arguments
      let zipped = zip funcArgsType funcArgTypes
      substitutions <- mapM (uncurry unify) zipped
      let substitution = if null substitutions then emptyTypeEnv else foldl1 (<>) substitutions
      subs <- mapM (applySubstitution substitution) funcArgTypes

      resolvedFuncType <- applySubstitution substitution funcType

      -- Create the typed function call
      let call = (Typed (FunCall ident typedFuncArgs) resolvedFuncType tokens, resolvedFuncType)

      if any isFreshTypeVar subs then
        return ()
      else do
        addCallToFunction ident substitution

      return call
    AST.PrintFunCall arg -> do
      -- Infer the type and constraints for the expression
      (typedExpr, exprType) <- inferExpression arg

      -- Create the typed print function call
      return (Typed (PrintFunCall typedExpr) Void tokens, Void)
    AST.IsEmptyFunCall arg -> do
      -- Infer the type and constraints for the expression
      (typedExpr, exprType) <- inferExpression arg

      -- Check if exprType is a list
      substitution <- unify (List GenericType) exprType

      -- Apply the substitution to the expression type and create the typed print function call
      finalExprType <- applySubstitution substitution exprType
      unless (isList finalExprType) $ throwErrorVoid [TypeMismatch (List GenericType) finalExprType]

      -- Create the typed print function call
      return (Typed (IsEmptyFunCall typedExpr) Void tokens, Basic AST.BOOL)
  putCurrentTokens oldTokens
  return res

getVariableFieldType :: AST.Expression -> GenericType -> Maybe AST.Field -> UnifyM GenericType
getVariableFieldType expr t@(TypeId _ _) Nothing = return t
getVariableFieldType expr (TypeId ident _) field = do
  oldTokens <- getCurrentTokens
  env <- getTypeEnv
  res <- case lookupTypeVar ident env of
    Just t -> case t of
      TypeId s _ -> case field of
        Nothing -> return t
        Just field -> case getTokened field of
          AST.HD m_fi -> do
            (newType, _) <- freshTypeVar
            substitution <- unify t (List newType)
            _finalType <- applySubstitution substitution t
            finalType <- if isList _finalType then return _finalType else throwErrorType [TypeMismatch (List GenericType) _finalType]
            let newTypeEnv = insertTypeVar ident finalType (env `unionTypeEnv` substitution)
            putTypeEnv newTypeEnv
            getVariableFieldType expr newType m_fi
          AST.TL m_fi -> do
            (newType, _) <- freshTypeVar
            substitution <- unify t (List newType)
            _finalType <- applySubstitution substitution t
            finalType <- if isList _finalType then return _finalType else throwErrorType [TypeMismatch (List GenericType) _finalType]
            let newTypeEnv = insertTypeVar ident finalType (env `unionTypeEnv` substitution)
            putTypeEnv newTypeEnv
            getVariableFieldType expr finalType m_fi
          AST.FST m_fi -> handlePair True t m_fi
          AST.SND m_fi -> handlePair False t m_fi
      _ -> getVariableFieldType expr t field
    Nothing -> throwErrorType [TypeNotFound ident]
  putCurrentTokens oldTokens
  return res
    where
      handlePair bool t field = do
        env <- getTypeEnv
        (newType, _) <- freshTypeVar
        (newType2, _) <- freshTypeVar
        substitution <- unify t (Pair newType newType2)
        _finalType <- applySubstitution substitution t
        finalType <- if isPair _finalType then return _finalType else throwErrorType [TypeMismatch (Pair newType newType2) t]
        let newTypeEnv = insertTypeVar ident finalType (env `unionTypeEnv` substitution)
        putTypeEnv newTypeEnv
        getVariableFieldType expr (if bool then newType else newType2) field
getVariableFieldType expr t field = do
  oldTokens <- getCurrentTokens
  res <- case field of
    Nothing -> return t
    Just field -> case t of
      Pair t1 t2 -> case getTokened field of
        AST.FST newField -> getVariableFieldType expr t1 newField
        AST.SND newField -> getVariableFieldType expr t2 newField
        _ -> throwErrorGeneric (List t1) [FieldAccess field t]
      List t -> case getTokened field of
        AST.HD newField -> getVariableFieldType expr t newField
        AST.TL newField -> getVariableFieldType expr (List t) newField
        _ -> throwErrorGeneric (Pair t t) [FieldAccess field t]
      _ -> throwErrorType [FieldAccess field t]
  putCurrentTokens oldTokens
  return res

inferFunctionDeclaration :: AST.FuncDeclaration -> UnifyM Function
inferFunctionDeclaration func@(Tokened (AST.FuncDeclaration id args funType vardecs stmts) tokens) = do -- Implement the function to infer the type of a function declaration
  {-
    var One = ...
    b Two = ...
    c Three = ...
    d Four = ...

    Main() :: #a #b #c {
      #a LocalOne = ...
      #b LocalTwo = ...
      #c LocalThree = ...
      d LocalFour = ...

      [Statement]...
    }
  -}

  -- Set the function name in the state 
  oldTokens <- getCurrentTokens
  setCurrentTokens func
  addEmptyFunction id
  setFuncName id

  -- Parse the function arguments
  (fArgs, retType) <- case funType of
    -- If it doesn't, make fresh typevariables for them 
    Nothing -> case args of
      Nothing -> return ([], Nothing)
      Just ss -> do
        mapM (\(Tokened arg argTokens) -> do
            (t, name) <- freshTypeVar
            addTypeId name t
            return $ Typed (FunctionVariable arg) t argTokens
          ) ss >>= \res -> return (res, Nothing)
    -- If it does, parse the arguments
    Just (Tokened (AST.FunType ftypes retType) funTypeTokens) -> case ftypes of
      Nothing -> return ([], Just retType)
      Just fts -> do
        -- Check if the number of arguments matches the number of types
        fts <- mapM convertFType fts
        fts <- if length fts < length (fromJust args)
          then throwErrorGeneric (fts ++ replicate (length (fromJust args) - length fts) (GenericType, [])) [FunctionArgumentLengthMismatch id (length fts) (length (fromJust args))]
          else if length fts > length (fromJust args)
            then do
              let res = concatMap snd $ drop (length (fromJust args)) fts
              let range = getTokenRange res
              forM_ range putCurrentTokens
              throwErrorGeneric (take (length (fromJust args)) fts) [FunctionArgumentLengthMismatch id (length fts) (length (fromJust args))]
            else return fts

        -- If argument contains typeId types, rename to (#typeIdName)
        variables <- zipWithM (curry (\((t, tokens), Tokened id idTokens) -> return $ Typed (FunctionVariable id) t (idTokens ++ tokens))) fts (fromJust args)

        (res, mp) <- foldrM (\(var@(Typed (FunctionVariable id) gType varTokens), _) (accVar, accMap) -> case gType of
            TypeId s _ ->
              case Map.lookup s accMap of
                Nothing -> do
                  (newType, name) <- freshTypeVar
                  addTypeId name newType
                  let newVar = Typed (FunctionVariable id) newType varTokens
                  return (newVar : accVar, Map.insert s newType accMap)
                Just str -> return (Typed (FunctionVariable id) str varTokens : accVar, accMap)
            _ -> return (var : accVar, accMap)
          ) ([], Map.empty) (zip variables (repeat Map.empty))
        return (res, Just retType)

  mapM_ addFuncArg fArgs
  typedLocalVarDecls <- mapM inferAndUpdateLocalVarDeclaration vardecs

  -- Get the return type from the function type
  ret <- case getTokened <$> retType of
    Just (AST.RetType t) ->  convertType t >>= \(t, _) -> return t
    _ -> freshTypeVar >>= \(t, _) -> return t

  -- Statements
  (typedStmts, retTypes) <- splitPair <$> mapM (`inferStatement` ret) stmts

  -- Update the func args and variables after the statements have been processed.
  let updateFuncArg var@(Typed (FunctionVariable id) t argTokens) = do
        typeEnv <- getTypeEnv
        case t of
          TypeId s _ -> do
            let res = lookupTypeVar s typeEnv
            case res of
              Just t -> do
                let arg = Typed (FunctionVariable id) t argTokens
                addFuncArg arg
                return arg
              Nothing -> return var
          _ -> return var
      updateFuncArg var = return var

  fArgs <- mapM updateFuncArg fArgs
  finalReturnType <- getReturnType (concat retTypes)

  case finalReturnType of
    Just t -> do
      env <- getTypeEnv
      substitution <- unify t ret
      finalType <- applySubstitution (env `unionTypeEnv` substitution) t
      let newTypeEnv = insertTypeVar id finalType (env `unionTypeEnv` substitution)
      putTypeEnv newTypeEnv
    Nothing -> do
      env <- getTypeEnv
      let newTypeEnv = insertTypeVar id ret env
      putTypeEnv newTypeEnv

  when (id == "main") $ do
    case finalReturnType of
      Just t -> do
        unless (isVoid t) $ throwErrorVoid [TypeMismatch Void t]
      Nothing -> return ()

  -- Unify the return type with the inferred return type
  let emptyFunc = Function id fArgs typedLocalVarDecls typedStmts
  func <- case finalReturnType of
    Just t -> do
      createTyped emptyFunc t tokens
    Nothing -> do
      unify ret Void
      createTyped emptyFunc Void tokens

  addFunc func
  putCurrentTokens oldTokens
  return func

isVoid :: GenericType -> Bool
isVoid Void = True
isVoid _ = False

compareTypes :: GenericType -> GenericType -> Bool
compareTypes t1 t2 = case (t1, t2) of
  (TypeId s1 _, TypeId s2 _) -> s1 == s2
  (Var s1, Var s2) -> s1 == s2
  (Pair t1 t2, Pair t3 t4) -> compareTypes t1 t3 && compareTypes t2 t4
  (List t1, List t2) -> compareTypes t1 t2
  _ -> t1 == t2

inferAndUpdateLocalVarDeclaration :: AST.VarDeclaration -> UnifyM Variable
inferAndUpdateLocalVarDeclaration var = do
  var <- inferAndUpdateVarDeclaration (inferVarDeclFunction var LocalVariable) var
  addFuncVar var
  return var

inferAndUpdateGlobalVarDeclaration :: AST.VarDeclaration -> UnifyM Variable
inferAndUpdateGlobalVarDeclaration var = inferAndUpdateVarDeclaration (inferVarDeclFunction var GlobalVariable) var

inferVarDeclFunction :: AST.VarDeclaration -> (String -> TypedExpression -> Variable') -> String -> GenericType -> TypedExpression -> UnifyM Variable
inferVarDeclFunction var varType name t expr = createTyped (varType name expr) t (getTokenedTokens var)

inferAndUpdateVarDeclaration :: (String -> GenericType -> TypedExpression -> UnifyM Variable) -> AST.VarDeclaration -> UnifyM Variable
inferAndUpdateVarDeclaration f varDecl@(Tokened (AST.VarDeclaration typ ident expr) tokens) = do
  oldTokens <- getCurrentTokens
  -- Infer the type and constraints for the expression
  (typedExpr, exprType) <- inferExpression expr

  -- Unify the declared type with the inferred type of the expression
  (declType, _) <- convertType typ
  substitution <- unify declType exprType

  typeEnv <- getTypeEnv
  (isCorrect, name) <- case declType of
    TypeId s _ -> do
      actualType <- getTypeVar s (typeEnv `unionTypeEnv` substitution) `catchError` (\err -> UnifyM $ return (GenericType, err))
      return (actualType == exprType, s)
    _ -> return (True, "")

  unless isCorrect $ throwErrorVoid [TypeMismatch declType exprType]

  -- Apply the substitution to the declared type and create the typed variable
  finalType <- applySubstitution substitution declType

  let newTypeEnv = insertVarType ident finalType (typeEnv `unionTypeEnv` substitution)
  putTypeEnv newTypeEnv

  t <- case finalType of
    TypeId s _ -> do
      getTypeVar s newTypeEnv `catchError` (\err -> UnifyM $ return (GenericType, err))
    List (TypeId s _) -> do
      throwErrorType [VariableWrongType varDecl finalType]
    _ -> do
      return finalType

  when (t == Void) $ throwErrorVoid [VariableWrongType varDecl t]

  putCurrentTokens oldTokens
  f ident t typedExpr

convertFType :: AST.FType -> UnifyM (GenericType, [PositionedToken])
convertFType (AST.FType t) = convertType t

convertType :: AST.Type -> UnifyM (GenericType, [PositionedToken])
convertType (Tokened t tokens) = convertType' t >>= \t -> return (t, tokens)
  where
    convertType' :: AST.HiddenType -> UnifyM GenericType
    convertType' (AST.Basic bt) = return $ Basic bt
    convertType' (AST.Pair t1 t2) = do
      (t1, _) <- convertType t1
      (t2, _) <- convertType t2
      return $ Pair t1 t2
    convertType' (AST.List t) = do
      (t, _) <- convertType t
      return $ List t
    convertType' (AST.Var s) = freshTypeVar >>= \(t, _) -> return t
    convertType' (AST.TypeId s) = return $ TypeId s False

splitRoots :: [AST.Root] -> ([AST.VarDeclaration], [AST.FuncDeclaration])
splitRoots [] = ([], [])
splitRoots (root : roots) = case root of
  AST.VarDecl v -> (v : varDecls, funcDecls)
  AST.FunDecl f -> (varDecls, f : funcDecls)
  AST.EmptyRoot _ -> undefined
  where
    (varDecls, funcDecls) = splitRoots roots

inferAST :: TypeEnv -> AST.AST -> UnifyM TypedAST
inferAST env (AST.AST roots) = do
  typedRoots <- foldM (\typedRootsAcc root -> do
    case root of
      AST.VarDecl vd -> do
        x <- inferAndUpdateGlobalVarDeclaration vd
        return (typedRootsAcc ++ [x])
      AST.FunDecl fd -> do
        x <- inferFunctionDeclaration fd
        putFunction x
        setFuncName ""
        return typedRootsAcc
      AST.EmptyRoot _ -> undefined
    ) [] roots
  funcs <- getFunctionMap
  -- Remove all polymorhpic funcs
  let funcs' = Map.map removePolyFunctions funcs
  return $ TypedAST typedRoots funcs'
  where
    (varDecls, funcDecls) = splitRoots roots

getTypedVar :: TypedRoot -> Maybe Variable
getTypedVar (RootVar var) = Just var
getTypedVar _ = Nothing

getTypedFunc :: TypedRoot -> Maybe Function
getTypedFunc (RootFunc func) = Just func
getTypedFunc _ = Nothing

unifyEntireAST :: AST.AST -> UnifyM TypedAST
unifyEntireAST = inferAST emptyTypeEnv

runUnifyEntireAST :: AST.AST -> Result (Maybe TypedAST)
runUnifyEntireAST ast = case runIdentity . runExceptT . flip runStateT emptyState . runUnifyM $ unifyEntireAST ast of
  Left s -> (Nothing, s)
  Right ((x0, x1), _) -> (Just x0, x1)