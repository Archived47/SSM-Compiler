{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Compiler.Scanner where

import Control.Applicative (Alternative (..), liftA2, (<|>), optional)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT, catchError)
import Control.Monad.State (State, gets, modify', runState, StateT (runStateT), lift)
import Data.Char (isAlphaNum, isDigit, isLower, isSpace, isUpper, isAlpha)
import Data.List (foldl', foldl1', intercalate)
import Data.Maybe (listToMaybe, maybeToList, fromMaybe)
import Control.Monad.Trans.State (StateT, get, put)
import qualified Control.Monad.Identity as MIdentity
import Control.Monad.Trans.Except (throwE)
import Control.Monad.Identity (Identity(..))
import Control.Monad ( when, unless )
import Compiler.Position
import Compiler.Token

type InnerPositionedToken = Positioned RawToken

data RawToken = WhiteSpaces String | Comment String | RawToken Token | ErrToken [LexerError]
  deriving (Show, Eq)

startState :: LexerState
startState = Position 1 1

innerToResult :: [InnerPositionedToken] -> ([PositionedToken], [LexerError])
innerToResult [] = ([], [])
innerToResult (x:xs) = case x of
  Positioned (RawToken t) pr -> let (res, errs) = innerToResult xs in (Positioned t pr : res, errs)
  Positioned (ErrToken e) pr -> let (res, errs) = innerToResult xs in (res, e ++ errs)
  Positioned _ pr -> innerToResult xs

outerToInnerSingle :: PositionedToken -> InnerPositionedToken
outerToInnerSingle (Positioned t pr) = Positioned (RawToken t) pr

outerToInner :: [PositionedToken] -> [InnerPositionedToken]
outerToInner [] = []
outerToInner (x:xs) = case x of
  Positioned t pr -> Positioned (RawToken t) pr : outerToInner xs

scan :: String -> ([PositionedToken], [LexerError])
scan input = case runIdentity . runExceptT . flip runStateT startState $ runLexer runTokens input of
  Left any -> error $ show any
  Right ((x0 ,_ ), _) -> innerToResult x0

-- Represents the kind of error that can occur
data LexerErrorInner
  = Unexpected Char
  | UnexpectedEOF
  | InvalidChar Char
  | UnterminatedComment
  deriving (Eq, Show)

type LexerErrros = [LexerError]
data LexerError = Error LexerErrorInner PositionRange
  deriving (Eq, Show)

-- Create the right lex error when we encounter an unexpected string
unexpected :: String -> Position -> LexerError
unexpected [] pos = Error UnexpectedEOF (createRange pos)
unexpected (c : _) pos = Error (Unexpected c) (createRange pos)

type LexerState = Position
newtype Lexer a = Lexer {runLexer :: String -> StateT LexerState (ExceptT ([LexerError], String, Bool) MIdentity.Identity) (a, String)}

instance Functor Lexer where
  fmap f (Lexer l) = Lexer $ \input -> do
    (a, rest) <- l input
    return (f a, rest)

instance Applicative Lexer where
  pure a = Lexer (\input -> return (a, input))
  Lexer lF <*> Lexer lA =
    Lexer $ \input -> do
      (f, rest) <- lF input
      (a, rest) <- lA rest
      return (f a, rest)

instance Alternative Lexer where
  empty = Lexer $ \input -> get >>= \st -> lift $ throwE ([unexpected input st], input, False)
  Lexer lA <|> Lexer lB = Lexer $ \input -> do
    st <- get
    let left = runIdentity . runExceptT . flip runStateT st $ lA input
    let right = runIdentity . runExceptT . flip runStateT st $ lB input

    case (left, right) of
      (Right ((a, restA), stA), Right ((b, restB), stB)) ->
        if length restA <= length restB
          then put stA >> return (a, restA)
          else put stB >> return (b, restB)
      (Left e, Left _) -> get >>= \st -> lift $ throwE e
      (Right ((a, rest), st'), _) -> put st' >> return (a, rest)
      (Left _, Right ((b, rest), st')) -> put st' >> return (b, rest)

infixl 9 |>
(|>) :: (Show a) => Lexer a -> Lexer a -> Lexer a
Lexer lA |> Lexer lB = Lexer $ \input -> do
  st <- get
  case runIdentity . runExceptT . flip runStateT st $ lA input of
    Left err@(_, _, pre) -> if pre then lift $ throwE err else case runIdentity . runExceptT . flip runStateT st $ lB input of
      Left _ -> lift $ throwE err
      Right (x0, st') -> put st' >> return x0
    Right (x0, st') -> put st' >> return x0

instance Monad Lexer where
  return = pure
  Lexer l >>= f =
    Lexer $ \input -> do
      (a, rest) <- l input
      let Lexer l' = f a
      (b, rest') <- l' rest
      return (b, rest')

instance MonadError LexerErrros Lexer where
  throwError err = Lexer $ \input -> lift $ throwE (err, input, False)
  catchError (Lexer l) f =
    Lexer $ \input -> do
      st <- get
      let res = runIdentity . runExceptT . flip runStateT st $ l input
      case res of
        Left (errs, rest, _) -> do
          put st
          let Lexer l' = f errs
          (a, rest') <- l' rest
          return (a, rest')
        Right (res, newSt) -> put newSt >> return res

satisfies :: (Char -> Bool) -> Lexer (Positioned Char)
satisfies p =
  Lexer $ \case
    c : cs | p c -> do
      st <- get
      if c == '\n'
        then put (nextLine st)
        else put (nextColumn st)
      return (Positioned c (createRange st), cs)
    rest -> get >>= \st -> lift $ throwE ([unexpected rest st], rest, False)

char :: Char -> Lexer (Positioned Char)
char target = satisfies (== target)

foldPositions :: [Positioned Char] -> Positioned String
foldPositions input = foldr (\(Positioned c r) (Positioned cs r') -> Positioned (c : cs) (setNewRange r r')) (Positioned "" (getPosition $ head input)) input

foldPositionsString :: [Positioned String] -> Positioned String
foldPositionsString input = foldr (\(Positioned c r) (Positioned cs r') -> Positioned (c ++ cs) (setNewRange r r')) (Positioned "" (getPosition $ head input)) input

string :: String -> Lexer (Positioned String)
string input = do
  x <- traverse char input
  let res = foldr (\(Positioned c r) (Positioned cs r') -> Positioned (c : cs) (setNewRange r r')) (Positioned "" (getPosition $ head x)) x
  return res

oneOf :: Alternative f => [f a] -> f a
oneOf = foldl1' (<|>)

eof :: Lexer (Maybe PositionedToken)
eof = Lexer $ \case
  [] -> get >>= \st -> return (Just $ Positioned EOF (createRange st), [])
  rest -> return (Nothing, rest)

skipToken :: Lexer ()
skipToken = Lexer $ \case
  [] -> get >>= \st -> lift $ throwE ([Error UnexpectedEOF (createRange st)], [], False)
  c : cs -> do
    st <- get
    if c == '\n'
      then put (nextLine st)
      else put (nextColumn st)
    return ((), cs)

runTokens :: Lexer [InnerPositionedToken]
runTokens = runTokens' []
  where
    runTokens' :: [InnerPositionedToken] -> Lexer [InnerPositionedToken]
    runTokens' acc = do
      x <- eof `catchError` \err -> do
        return Nothing

      case x of
        Nothing -> do
          (newToken, _) <- token `catchError` \err -> do
            skipToken `catchError` \err -> return ()
            return (lexerErrorsToError err, "")
          runTokens' (newToken : acc)
        Just to -> return (reverse (outerToInnerSingle to : acc))

lexerErrorsToError :: [LexerError] -> InnerPositionedToken
lexerErrorsToError errs = let res = lexerErrorsToError' errs in case snd res of
  Nothing -> Positioned (ErrToken $ fst res) startRange
  Just range -> Positioned (ErrToken $ fst res) range
  where
    lexerErrorsToError' :: [LexerError] -> ([LexerError], Maybe PositionRange)
    lexerErrorsToError' [] = ([], Nothing)
    lexerErrorsToError' (current@(Error err st) : xs) = let (err', range) = lexerErrorsToError' xs in (current : err', Just $ setNewRange st (fromMaybe st range))

token :: Lexer (InnerPositionedToken, String)
token = comments |> whitespace |> (keyword <|> operator <|> symbols <|> functions <|> litteral <|> name)
  where
    with :: Token -> Lexer (Positioned String) -> Lexer (InnerPositionedToken, String)
    with b f = do
      res <- f
      return (Positioned (RawToken b) (getRange res), getPosItem res)

    whitespace :: Lexer (InnerPositionedToken, String)
    whitespace = Lexer $ \input -> do
      st <- get
      unless (isSpace $ head input) $ lift $ throwE ([unexpected input st], input, False)

      let (whitespaces, rest) = span isSpace input
      let x = foldr (\c st -> if c == '\n' then nextLine st else nextColumn st) st whitespaces
      put x

      return ((Positioned (WhiteSpaces whitespaces) (createRange st), whitespaces), rest)

    comments :: Lexer (InnerPositionedToken, String)
    comments = multi |> single
      where
        single :: Lexer (InnerPositionedToken, String)
        single = do
          commentLoc <- string "//"
          Lexer $ \input -> do
            st <- get
            let (characters, rest) = break (== '\n') input
            return ((Positioned (Comment characters) (setNewRange (getRange commentLoc) (createRange (addCols (length characters) st))), characters), rest)


        multi :: Lexer (InnerPositionedToken, String)
        multi = do
          start <- string "/*"
          Lexer $ \input -> do
            st <- get
            let range = createRange st
            let res = gulp range 1 input []
            case res of
              Left le -> lift $ throwE ([le], [], True)
              Right (resulting, comment, end) -> do
                let st' = getRangeEnd end
                put st'
                let newComment = getPosItem start ++ comment
                return ((Positioned (Comment newComment) (setNewRange range (createRange st')), newComment), resulting)
          where
            gulp :: PositionRange -> Int -> String -> String -> Either LexerError (String, String, PositionRange)
            gulp pos depth ('/':'*':xs) acc = gulp (addColsRange 2 pos) (depth + 1) xs (acc ++ "/*")
            gulp pos depth ('*':'/':xs) acc
              | depth == 1 = Right (xs, acc ++ "*/", pos)
              | otherwise = gulp (addColsRange 2 pos) (depth - 1) xs (acc ++ "*/")
            gulp pos depth ('\n':xs) acc = gulp (addRowsRange 1 pos) depth xs (acc ++ "\n")
            gulp pos depth (x:xs) acc = gulp (nextColumnRange pos) depth xs (acc ++ [x])
            gulp st depth [] _ = Left $ Error UnterminatedComment st

    keyword :: Lexer (InnerPositionedToken, String)
    keyword = oneOf
        [ VarToken `with` string "var"
        , IntToken `with` string "Int"
        , BoolToken `with` string "Bool"
        , CharToken `with` string "Char"
        , VoidToken `with` string "Void"
        , FunctionToken `with` string "::"
        , IsToken `with` string "="
        , ArrowToken `with` string "->"
        , IfToken `with` string "if"
        , ElseToken `with` string "else"
        , WhileToken `with` string "while"
        , ReturnToken `with` string "return"
        ]

    operator :: Lexer (InnerPositionedToken, String)
    operator = boolOp <|> basicOp
      where
        basicOp :: Lexer (InnerPositionedToken, String)
        basicOp =
          oneOf
            [ MinusToken `with` string "-"
            , PlusToken `with` string "+"
            , MultToken `with` string "*"
            , DivToken `with` string "/"
            , ModToken `with` string "%"
            ]
        boolOp :: Lexer (InnerPositionedToken, String)
        boolOp =
          oneOf
            [ EqualToken `with` string "=="
            , UnequalToken `with` string "!="
            , SmallerEqualToken `with` string "<="
            , LargerEqualToken `with` string ">="
            , SmallerToken `with` string "<"
            , LargerToken `with` string ">"
            , AndToken `with` string "&&"
            , OrToken `with` string "||"
            , NotToken `with` string "!"
            ]

    symbols = brackets <|> rest
      where
        rest :: Lexer (InnerPositionedToken, String)
        rest =
          oneOf
            [ CommaToken `with` string ","
            , DotToken `with` string "."
            , UnderscoreToken `with` string "_"
            , SemiColonToken `with` string ";"
            , IsToken `with` string "="
            , ConstructorToken `with` string ":"
            ]

        brackets :: Lexer (InnerPositionedToken, String)
        brackets =
          oneOf
            [ BraceOpen `with` string "("
            , BraceClose `with` string ")"
            , SBraceOpen `with` string "["
            , SBraceClose `with` string "]"
            , CBraceOpen `with` string "{"
            , CBraceClose `with` string "}"
            ]

    functions :: Lexer (InnerPositionedToken, String)
    functions = oneOf
      [ HeadToken `with` string "hd"
      , TailToken `with` string "tl"
      , FstToken `with` string "fst"
      , SndToken `with` string "snd"
      , ConstructorToken `with` string ":"
      , EmptyToken `with` string "isEmpty"
      , PrintToken `with` string "print"
      , EmptyListToken `with` string "[]"
      ]

    litteral :: Lexer (InnerPositionedToken, String)
    litteral = intLit <|> charLit <|> boolLit
      where
        intLit :: Lexer (InnerPositionedToken, String)
        intLit = do
          res <- some (satisfies isDigit)
          let strRes = foldPositions res
          return (Positioned (RawToken $ IntLit (read (getPosItem strRes))) (getRange strRes), getPosItem strRes)

        charLit :: Lexer (InnerPositionedToken, String)
        charLit = do
          start <- char '\''
          c <- satisfies (/= '\'')
          end <- char '\''
          return (Positioned (RawToken $ CharLit (getPosItem c)) (setNewRange (getRange start) (getRange end)), ['\'', getPosItem c, '\''])

        boolLit :: Lexer (InnerPositionedToken, String)
        boolLit = (BoolLit True `with` string "True") <|> (BoolLit False `with` string "False")

    name :: Lexer (InnerPositionedToken, String)
    name = identity
      where
        continuesName :: Lexer (Positioned Char)
        continuesName = satisfies isAlphaNum <|> char '_'

        followedBy :: Lexer (Positioned Char) -> Lexer (Positioned Char) -> Lexer (Positioned String)
        followedBy l1 l2 = foldPositions <$> liftA2 (:) l1 (many l2)

        identity :: Lexer (InnerPositionedToken, String)
        identity = do
          result <- satisfies isAlpha `followedBy` continuesName
          return (Positioned (RawToken $ IdentToken (getPosItem result)) (getRange result), getPosItem result)