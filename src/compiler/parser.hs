{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Compiler.Parser where

import Control.Applicative
import Compiler.Token
import Compiler.AST
import Data.Bifunctor
import Data.Functor
import Data.List
import Control.Monad.Trans.State (StateT, runStateT)
import Control.Monad.Trans.Class
import Control.Monad
import Control.Monad.Error.Class (MonadError(throwError, catchError))
import Control.Monad.Except (ExceptT, runExceptT)
import qualified Data.Functor.Identity as MIdentity
import qualified Control.Monad.Trans.Identity as Identity
import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.State.Class ( MonadState(put, get) )
import Data.Maybe (catMaybes, fromMaybe, maybeToList)


parse :: [PositionedToken] -> (Maybe AST, [Error])
parse tokens = parse' tokens 0
  where
    parse' :: [PositionedToken] -> Integer -> (Maybe AST, [Error])
    parse' tokens cnt = case runIdentity . runExceptT $ runStateT (runParser ast tokens) cnt of
      Left (errs, errTokens) -> let (result, errs') = parse' errTokens (cnt + 1) in (result, errs <> errs')
      Right (((res, errs), rest), _) ->  (Just res, errs)

unexpected :: PositionedToken -> Error
unexpected t
  | rawToken t == EOF = UnexpectedEndOfFile t
  | otherwise = Unexpected t

data Error
  = EndOfInput
  | Unexpected PositionedToken
  | UnexpectedEndOfFile PositionedToken
  | ExpectedEndOfFile PositionedToken
  | EmptyFunction [PositionedToken]
  | VarInStatementBody String [PositionedToken]
  | Empty
  | MissingMainFunction
  | MultipleMain Root
  | MissingSemiColon [PositionedToken]
  deriving (Eq, Show)

type Result a = (a, [Error])
newtype Parser a = Parser {runParser :: [PositionedToken] -> StateT Integer (ExceptT ([Error], [PositionedToken]) MIdentity.Identity) (Result a, [PositionedToken])}

instance MonadError ([Error], [PositionedToken]) Parser where
  throwError err = Parser $ \_ -> lift $ throwError err
  catchError (Parser x) f = Parser $ \input -> do
    cnt <- get
    case runIdentity . runExceptT $ runStateT (x input) cnt of
      Left (err, errTokens) -> do
        cnt' <- get
        case runIdentity . runExceptT $ runStateT (runParser (f (err, errTokens)) input) cnt' of
          Left (err', errTokens') -> lift $ throwError (nub $ err', errTokens')
          Right (output, cnt'') -> do
            put cnt''
            return output
      Right (output, cnt') -> do
        put cnt'
        return output

instance Functor Parser where
  fmap f (Parser g) = Parser $ \input -> do
    ((y, errs), rest) <- g input
    let res = f y
    return ((res, errs), rest)

instance Applicative Parser where
  pure x = Parser $ \input -> return ((x, []), input)
  Parser f <*> Parser x = Parser $ \input -> do
    ((y, errs), rest) <- f input
    ((y', errs'), rest') <- x rest
    return ((y y', errs <> errs'), rest')

instance Monad Parser where
  return = pure
  Parser x >>= f = Parser $ \input -> do
    ((y, errs), rest) <- x input
    ((y', errs'), rest') <- runParser (f y) rest
    return ((y', errs <> errs'), rest')

instance Alternative Parser where
  empty = Parser $ \input -> lift $ throwError ([Empty], input)
  Parser x <|> Parser y = Parser $ \input -> do
    cnt <- get
    case runIdentity . runExceptT $ runStateT (x input) cnt of
      Left (err, errTokens) -> do
        cnt' <- get
        case runIdentity . runExceptT $ runStateT (y input) cnt' of
          Left (err', errTokens') -> lift $ throwError $ if length errTokens < length errTokens' then (err, errTokens) else (err', errTokens') -- TODO Choose between least tokens (parser that went the furthest) or left recursion
          Right (output, cnt'') -> do
            put cnt''
            return output
      Right (output, cnt') -> do
        put cnt'
        return output

createResult :: a -> Result a
createResult x = (x, [])

satisifies :: (Token -> Bool) -> Parser PositionedToken
satisifies predicate = Parser $ \input -> case input of
  [] -> lift $ throwError ([EndOfInput], input)
  hd : rest
    | predicate $ rawToken hd -> lift $ return (createResult hd, rest)
    | otherwise -> lift $ throwError ([unexpected hd], input)

pluck :: (Token -> Maybe a) -> Parser (Tokened a)
pluck f = Parser $ \input -> case input of
  [] -> lift $ throwError ([EndOfInput], input)
  hd : rest -> case f (rawToken hd) of
    Just res -> lift $ return (createResult (Tokened res [hd]), rest)
    _  -> lift $ throwError ([unexpected hd], input)

token :: Token -> Parser PositionedToken
token = satisifies . (==)

sepBy1 :: Parser a -> Parser sep -> Parser [a]
sepBy1 p sep = liftA2 (:) p (many (sep *> p))

opsL :: Parser (a -> a -> a) -> Parser a -> Parser a
opsL sep p = liftA2 squash p (many (liftA2 (,) sep p))
  where
    squash = foldl' (\acc (combine, a) -> combine acc a)

opsR :: Parser (a -> a -> a) -> Parser a -> Parser a
opsR sep p = liftA2 squash p (many (liftA2 (,) sep p))
  where
    squash start annotated =
      let (start', annotated') = foldl' shift (start, []) annotated
          shift (oldStart, stack) (combine, a) = (a, (combine, oldStart) : stack)
       in foldl' (\acc (combine, a) -> combine a acc) start' annotated'

literal :: Parser Expression
literal = minusIntLit <|> intLit <|> boolLit <|> charLit
  where
    minusIntLit = do
      minusses <- some $ token MinusToken
      (Tokened value tokens) <- intLit

      res <- case value of
        IntValue i -> return $ IntValue $
          if even (length minusses) then i else -i

      return (Tokened value (minusses <> tokens))

    intLit = pluck $ \case
        IntLit i -> Just (IntValue i)
        _ -> Nothing
    charLit = do
      pluck $ \case
        CharLit c -> Just (CharValue c)
        _ -> Nothing
    boolLit =
      pluck $ \case
        BoolLit b -> Just (BoolValue b)
        _ -> Nothing

skipToken :: Parser ()
skipToken = Parser $ \input -> case input of
  [] -> throwError ([EndOfInput], input) `catchError` (\(e, t) -> return (((), e), t))
  hd : rest -> return (createResult (), rest)

setNewTokens :: [PositionedToken] -> Parser ()
setNewTokens newTokens = Parser $ \_ -> return (((), []), newTokens)

skipTokensTillNewResult :: [PositionedToken] -> (Bool, Bool) -> [PositionedToken]
skipTokensTillNewResult tokens (scInclusive, cbInclusive) = skipTokensTillNewResult' 0 tokens
  where
    skipTokensTillNewResult' :: Int -> [PositionedToken] -> [PositionedToken]
    skipTokensTillNewResult' 0 (x : xs) = case rawToken x of
      CBraceOpen -> skipTokensTillNewResult' 1 xs
      SemiColonToken -> if scInclusive then x : xs else xs
      EOF -> [x]
      CBraceClose -> if cbInclusive then x : xs else xs
      _ -> skipTokensTillNewResult' 0 xs
    skipTokensTillNewResult' counter (x : xs) = case rawToken x of
      CBraceOpen -> skipTokensTillNewResult' (counter + 1) xs
      CBraceClose -> case counter of
        1 -> if cbInclusive then x : xs else xs
        _ -> skipTokensTillNewResult' (counter - 1) xs
      EOF -> [x]
      _ -> skipTokensTillNewResult' counter xs
    skipTokensTillNewResult' _ [] = []

handleVarDecl :: Parser (Either ([Error], [PositionedToken]) VarDeclaration)
handleVarDecl = (Right <$> varDeclaration) `catchError` (\(e, t) -> Parser $ \_ -> return ((Left (e, t), e), t))

root :: Parser Root
root = func <|> var
  where
    func = ((Right <$> funcDeclaration) `catchError` (\(e, t) -> Parser $ \_ -> return ((Left (e, t), e), t))) >>= \v -> case v of
      Left e -> do
        inp <- getInput
        setNewTokens inp
        throwError e
      Right res -> return $ FunDecl res
    var = handleVarDecl >>= \v -> case v of
      Left (e, tokens) -> do
        skipToken
        inp <- getInput
        setNewTokens inp
        throwError (e, inp)
      Right res -> return $ VarDecl res

identifier :: Parser (String, PositionedToken)
identifier = Parser $ \input -> case input of
  [] -> lift $ throwError ([EndOfInput], input)
  hd : rest -> case rawToken hd of
    IdentToken n -> lift $ return (createResult (n, hd), rest)
    _  -> lift $ throwError ([unexpected hd], input)
  where
    isIdToken = \case
      IdentToken n -> Just n
      _ -> Nothing


identity :: Parser (Tokened String)
identity = do
  (id, t) <- identifier
  return $ Tokened id [t]

simpleTypeParser :: Parser Type
simpleTypeParser = do
      typeToken <- token IntToken <|> token BoolToken <|> token CharToken
      res <- case rawToken typeToken of
        IntToken -> return $ Basic INT
        BoolToken -> return $ Basic BOOL
        CharToken -> return $ Basic CHAR
      return $ Tokened res [typeToken]

pairTypeParser :: Parser Type -> Parser Type
pairTypeParser parser = do
  _bOpen <- token BraceOpen
  t1 <- parser
  _comma <- token CommaToken
  t2 <- parser
  _bClose <- token BraceClose

  return $ Tokened (Pair t1 t2) ([_bOpen] ++ getTokenedTokens t1 ++ [_comma] ++ getTokenedTokens t2 ++ [_bClose])

listTypeParser :: Parser Type -> Parser Type
listTypeParser parser = do
  _bOpen <- token SBraceOpen
  t <- parser
  _bCLose <- token SBraceClose

  return $ Tokened (List t) ([_bOpen] ++ getTokenedTokens t ++ [_bCLose])

identityTypeParser :: Parser Type
identityTypeParser = do
  (Tokened id t) <- identity
  return $ Tokened (TypeId id) t

typeParser :: Parser Type
typeParser = simpleTypeParser <|> pairTypeParser typeParser <|> listTypeParser typeParser <|> identityTypeParser

varParser :: Parser Type
varParser = do
  _v <- token VarToken
  res <- Parser (\input -> do
    counter <- get
    put (counter + 1)
    return (createResult $ Var ("v" ++ show counter), input))
  return $ Tokened res [_v]

getInput :: Parser [PositionedToken]
getInput = Parser $ \input -> return (createResult input, input)

emptyVariable :: VarDeclaration
emptyVariable = Tokened (VarDeclaration (Tokened (Basic INT) []) "" (Tokened EmptyList [])) []

varDeclaration :: Parser VarDeclaration
varDeclaration = do
  varType <- varParser <|> typeParser
  id <- identity
  _is <- token IsToken
  expr <- expression
  currentTokens <- getInput

  let tokens = getTokenedTokens varType ++ getTokenedTokens id ++ [_is] ++ getTokenedTokens expr
  _semi <- optional $ token SemiColonToken

  case _semi of
    Nothing -> Parser $ \input -> return ((emptyVariable, [MissingSemiColon tokens]), currentTokens)
    Just po -> return $ Tokened (VarDeclaration varType (getTokened id) expr) (tokens ++ [po])

funcDeclaration :: Parser FuncDeclaration
funcDeclaration = do
  id <- identity
  _bOpen <- token BraceOpen
  args <- fArgs
  _bClose <- token BraceClose
  funtype <- optional funType
  _FuncBraceOpen <- token CBraceOpen

  (vardecls, stmts, endToken, errs) <- handleBody False

  argTokens <- case args of
    Nothing -> return []
    Just t -> return $ concatMap getTokenedTokens t

  let tokens = getTokenedTokens id ++ [_bOpen] ++ argTokens ++ [_bClose] ++ maybe [] getTokenedTokens funtype ++ [_FuncBraceOpen] ++ concatMap getTokenedTokens vardecls ++ concatMap getTokenedTokens stmts

  let func = Tokened (FuncDeclaration (getTokened id) args funtype vardecls stmts) tokens

  x <- getInput
  when (null stmts) $ throwError (EmptyFunction (getTokenedTokens func) : errs, x)

  return func
  where
    handleBodyVarDecl :: Parser FuncBody
    handleBodyVarDecl = handleVarDecl >>= (\v -> case v of
      Left (e, t) -> throwError (e, t)
      Right res -> return $ FuncVar res)

    handleBody :: Bool -> Parser ([VarDeclaration], [Statement], Maybe PositionedToken, [Error])
    handleBody stmtFound = do
      parsed <- ((FuncClose <$> token CBraceClose) <|> (FuncStmt <$> statement) <|> handleBodyVarDecl) `catchError` (
          \(err, tokens) -> Parser $ \_ -> return ((FuncError err tokens, err), tokens)
        )

      case parsed of
        FuncVar to -> do
          (vardecls, stmts, endToken, ers) <- handleBody stmtFound
          if stmtFound then do
            let err = VarInStatementBody (getVarDeclName to) (getTokenedTokens to) 
            return (vardecls, stmts, endToken, err : ers)
          else do
            return (to : vardecls, stmts, endToken, ers)
        FuncStmt to -> do
          (vardecls, stmts, endToken, ers) <- handleBody True
          return (vardecls, to : stmts, endToken, ers)
        FuncClose po -> return ([], [], Just po, [])
        FuncError e tokens -> do
          if not (null tokens) && rawToken (head tokens) == SemiColonToken then setNewTokens (tail tokens) else setNewTokens tokens

          mapM_ addError e 

          if null tokens
            then throwError (e, tokens)
            else do
              (vars, stms, x, errs) <- handleBody stmtFound
              return (vars, stms, x, nub $ errs ++ e)

data FuncBody = FuncVar VarDeclaration | FuncStmt Statement | FuncClose PositionedToken | FuncError [Error] [PositionedToken]
  deriving (Show)

getFtypesTokens :: [FType] -> [PositionedToken]
getFtypesTokens [] = []
getFtypesTokens (FType t:xs) = getTokenedTokens t ++ getFtypesTokens xs

funType :: Parser FunType
funType = do
  _one <- token FunctionToken
  ftypes <- fTypes
  _two <- token ArrowToken
  let v = token VoidToken >>= \t -> return $ Tokened Void [t]
  let t = typeParser >>= \t -> return $ Tokened (RetType t) (getTokenedTokens t)
  retType <- v <|> t
  return $ Tokened (FunType ftypes retType) ([_one] ++ maybe [] getFtypesTokens ftypes ++ [_two] ++ getTokenedTokens retType)

fTypes :: Parser (Maybe [FType])
fTypes = optional $ many fType

fType :: Parser FType
fType = FType <$> typeParser

fArgs :: Parser (Maybe [FArg])
fArgs = optional $ do
  arg <- optional fArg
  case arg of
    Nothing -> return []
    Just a -> do
      args <- many $ token CommaToken *> fArg
      return $ a : args

fArg :: Parser FArg
fArg = identity


-- {-precedence: (low to high)
-- ||                        assoc: right
-- &&                        assoc: right
-- <, >, <=, >=, ==, !=      assoc: -
-- :                         assoc: right
-- +, -                      assoc: left
-- *, /, mod                 assoc: left
-- -}

expression :: Parser Expression
expression = binaryExpression
  where
    binaryExpression = orExpr
      where
        binaryOp :: Token -> HiddenOp2 -> Parser (Expression -> Expression -> Expression)
        binaryOp token' op = token token' >>= \t -> return (\l r -> Tokened (BinaryExpr (Tokened op [t]) l r) (getTokenedTokens l ++ [t] ++ getTokenedTokens r))

        orExpr = opsR (binaryOp OrToken Or) andExpr
        andExpr = opsR (binaryOp AndToken And) comparisonExpr
        comparisonExpr = opsL comparisonOperator constructorExpr
          where
            comparisonOperator =
              binaryOp SmallerToken SmallerThan
                <|> binaryOp SmallerEqualToken SmallerEqualThan
                <|> binaryOp LargerToken BiggerThan
                <|> binaryOp LargerEqualToken BiggerEqualThan
                <|> binaryOp EqualToken Equal
                <|> binaryOp UnequalToken NotEqual
        constructorExpr = opsR constructorOperator addSubExpr
          where
            constructorOperator = token ConstructorToken >>= \t -> return $ func [t]
              where
                func :: [PositionedToken] -> Expression -> Expression -> Expression
                func ts x y = case y of
                 Tokened (ListExpr expressions final) ts' -> Tokened (ListExpr (x : expressions) final) (ts ++ ts' ++ getTokenedTokens x)
                 Tokened EmptyList ts' -> Tokened (ListExpr [x] y) (ts ++ ts' ++ getTokenedTokens x)
                 Tokened (ExprId name fld) ts' -> Tokened (ListExpr [x] y) (ts ++ ts' ++ getTokenedTokens x)
                 Tokened (ExprFunCall funCall) ts' -> Tokened (ListExpr [x] y) (ts ++ ts' ++ getTokenedTokens x)
                 Tokened (BracedExpression expr) ts' -> func (ts ++ ts') x expr
                 _ -> Tokened BadList ts
        addSubExpr = opsL addSubOperator mulDivExpr
          where
            addSubOperator = binaryOp PlusToken Plus <|> binaryOp MinusToken Minus
        mulDivExpr = opsL mulDivOperator (unaryExpression <|> expressions)
          where
            mulDivOperator =
                  binaryOp MultToken Multiply
              <|> binaryOp DivToken Divide
              <|> binaryOp ModToken Modulo

    unaryExpression = negateExpr <|> notExpr
    notExpr = do
      _not <- token NotToken
      expr <- expressions
      return $ Tokened (UnaryExpr (Tokened Not [_not]) expr) (_not : getTokenedTokens expr)
    negateExpr = do
      _not <- token MinusToken
      expr <- expressions
      return $ Tokened (UnaryExpr (Tokened Negative [_not]) expr) (_not : getTokenedTokens expr)
    expressions = pairExpression <|> literal <|> bracedExpression <|> emptyListExpression <|> funCallExpression <|> fieldExpression <|> unaryExpression
    emptyListExpression = token EmptyListToken >>= \t -> return $ Tokened EmptyList [t]

    pairExpression = do
      _bO <- token BraceOpen
      expr1 <- expression
      _comma <- token CommaToken
      expr2 <- expression
      _bC <- token BraceClose
      return $ Tokened (PairExpression (expr1, expr2)) (_bO : getTokenedTokens expr1 ++ [_comma] ++ getTokenedTokens expr2 ++ [_bC])

    bracedExpression = do
      _bO <- token BraceOpen
      expr <- expression
      _bC <- token BraceClose
      return $ Tokened (BracedExpression expr) (_bO : getTokenedTokens expr ++ [_bC])

    fieldExpression = do
      id <- identity
      fld <- fieldParser

      fldTokens <- case fld of
        Nothing -> return []
        Just f -> return $ getTokenedTokens f

      return $ Tokened (ExprId (getTokened id) fld) (getTokenedTokens id ++ fldTokens)
    funCallExpression = do
      funCall <- funCallParser
      return $ Tokened (ExprFunCall funCall) (getTokenedTokens funCall)

funCallParser :: Parser FunctionCall
funCallParser = printFunCall <|> isEmptyFunCall <|> emptyArgs <|> args
  where
    emptyArgs = do
      id <- identity
      _one <- token BraceOpen
      _two <- token BraceClose
      return $ Tokened (FunCall (getTokened id) []) (getTokenedTokens id ++ [_one, _two])
    args = do
      id <- identity
      _one <- token BraceOpen
      arguments <- sepBy1 expression (token CommaToken)
      _two <- token BraceClose
      return $ Tokened (FunCall (getTokened id) arguments) (getTokenedTokens id ++ [_one] ++ concatMap getTokenedTokens arguments ++ [_two])
    isEmptyFunCall = do
      _empty <- token EmptyToken
      _one <- token BraceOpen
      argument <- expression
      _two <- token BraceClose
      return $ Tokened (IsEmptyFunCall argument) ([_empty, _one] ++ getTokenedTokens argument ++ [_two])
    printFunCall = do
      _empty <- token PrintToken
      _one <- token BraceOpen
      argument <- expression
      _two <- token BraceClose
      return $ Tokened (PrintFunCall argument) ([_empty, _one] ++ getTokenedTokens argument ++ [_two])

statement :: Parser Statement
statement = ifStatement <|> whileStatement <|> assignStatement <|> funcallStatement <|> returnStatement
  where
    handleBody :: Parser ([Statement], Maybe PositionedToken)
    handleBody = do
      parsed <- ((FuncClose <$> token CBraceClose) <|> (FuncStmt <$> statement)) `catchError` (
          \(err, tokens) -> Parser $ \_ -> return ((FuncError err tokens, err), tokens)
        )

      case parsed of
        FuncStmt to -> do
          (stmts, endToken) <- handleBody
          return (to : stmts, endToken)
        FuncClose po -> return ([], Just po)
        FuncError e tokens -> do
          if not (null tokens) && rawToken (head tokens) == SemiColonToken then setNewTokens (tail tokens) else setNewTokens tokens

          if null tokens
            then throwError (e, tokens)
            else handleBody
        _ -> undefined

    --if
    ifStatement :: Parser Statement
    ifStatement = do
      _if <- token IfToken
      _bO <- token BraceOpen
      cond <- expression
      _bC <- token BraceClose
      _cbO <- token CBraceOpen

      (ifStmts, closingToken) <- handleBody
      (elseStmts, elseTokens) <- elseParser
      return $ Tokened (If cond ifStmts elseStmts) ([_if, _bO] ++ getTokenedTokens cond ++ [_bC, _cbO] ++ concatMap getTokenedTokens ifStmts ++ maybeToList closingToken ++ elseTokens)


    --while
    whileStatement = do
      _while <- token WhileToken
      _bO <- token BraceOpen
      cond <- expression
      _bC <- token BraceClose
      _cbO <- token CBraceOpen
      stmts <- many statement
      _cbC <- token CBraceClose
      return $ Tokened (While cond stmts) ([_while, _bO] ++ getTokenedTokens cond ++ [_bC, _cbO] ++ concatMap getTokenedTokens stmts ++ [_cbC])
    --varInit
    assignStatement :: Parser Statement
    assignStatement = do
      id <- identity
      field <- fieldParser
      _is <- token IsToken
      expr <- expression
      _semi <- token SemiColonToken
      return $ Tokened (VarAssign (getTokened id) field expr) ([_is] ++ getTokenedTokens id ++ getTokenedTokens expr ++ [_semi])
    -- funcall
    funcallStatement :: Parser Statement
    funcallStatement = do
      call <- funCallParser
      let tokens = getTokenedTokens call
      currentTokens <- getInput
      _semi <- token SemiColonToken `catchError` (\err -> Parser $ \input -> throwError ([MissingSemiColon tokens], currentTokens))
      return $ Tokened (StatementFunCall call) (getTokenedTokens call ++ [_semi])
    -- return
    returnStatement :: Parser Statement
    returnStatement = do
      _ret <- token ReturnToken
      expr <- optional expression
      _semi <- token SemiColonToken
      return $ Tokened (Return expr) ([_ret] ++ maybe [] getTokenedTokens expr ++ [_semi])

    elseParser :: Parser (Maybe [Statement], [PositionedToken])
    elseParser = do
      elTok <- optional (token ElseToken)
      case elTok of
        Nothing -> return (Nothing, [])
        Just po -> do
          _cbO <- token CBraceOpen
          (stmts, closing) <- handleBody
          return (Just stmts, po : _cbO : maybeToList closing)

fieldParser :: Parser (Maybe Field)
fieldParser = optional _fieldParser
  where
    _fieldParser = do
      _dot <- token DotToken
      field <- token FstToken <|> token SndToken <|> token HeadToken <|> token TailToken

      case rawToken field of
        FstToken -> func FST _dot field
        SndToken -> func SND _dot field
        HeadToken -> func HD _dot field
        TailToken -> func TL _dot field
    func fld _dot field = fieldParser >>= \f -> return $ Tokened (fld f) ([_dot, field] ++ maybe [] getTokenedTokens f)

eof :: Parser ()
eof = Parser $ \input -> case input of
  [] -> throwError ([EndOfInput], [])
  to : tos -> if rawToken to == EOF && length input == 1
    then return (((), []), [])
    else throwError ([ExpectedEndOfFile to], [])

isMain :: Root -> Bool
isMain (VarDecl _) = False
isMain (FunDecl (Tokened (FuncDeclaration id _ _ _ _) _)) = id == "main"
isMain (EmptyRoot _) = False

isEmptyRoot :: Root -> Bool
isEmptyRoot (EmptyRoot _) = True
isEmptyRoot _ = False

getEmptyRootValue :: Root -> Bool
getEmptyRootValue (EmptyRoot val) = val
getEmptyRootValue _ = False

addError :: Error -> Parser ()
addError err = Parser $ \input -> return (((), [err]), input)

ast :: Parser AST
ast = AST <$> rootParsing [] False
  where
    rootParsing :: [Root] -> Bool -> Parser [Root]
    rootParsing current mainFound = do
      e <- (Just <$> eof) `catchError` (\(e, t) -> Parser $ \input -> return ((Nothing, []), input))

      case e of
        Nothing -> do
          ro <- (Right <$> root) `catchError` (\(e, t) -> return (Left (e, t))) -- TODO improve error handling

          case ro of
            Left (e, pos) -> do
              setNewTokens pos
              mapM_ addError e
              rootParsing current mainFound
            Right ro' -> do
              let isM = isMain ro'

              if isM && mainFound then addError (MultipleMain ro') >> rootParsing current mainFound else rootParsing (ro' : current) (mainFound || isM)
        _ -> finishRootParsing current mainFound
    finishRootParsing current mainFound = do
      input <- getInput
      if mainFound
        then return current
        else throwError ([MissingMainFunction], input) `catchError` (\(err, input) -> Parser $ \_ -> return ((current, err), input))
