module Compiler.Token where
import Compiler.Position

data Tokened a = Tokened a [PositionedToken]
  deriving (Show, Eq)
type PositionedToken = Positioned Token

rawToken :: PositionedToken -> Token
rawToken (Positioned t _) = t

data Token =
  VarToken |
  IntToken | BoolToken | CharToken | VoidToken | -- Types
  FunctionToken | IsToken | SemiColonToken | CommaToken | ArrowToken | DotToken | UnderscoreToken | -- Symbols
  IfToken | ElseToken | WhileToken | ReturnToken | -- Statement tokens
  BraceOpen | BraceClose | SBraceOpen | SBraceClose | CBraceOpen | CBraceClose | -- Brackets
  MinusToken | PlusToken | MultToken | DivToken | ModToken | -- Operators
  EqualToken | UnequalToken | SmallerToken | LargerToken | SmallerEqualToken | LargerEqualToken | AndToken | OrToken | NotToken | -- Booleans
  HeadToken | TailToken | FstToken | SndToken | PrintToken | ConstructorToken | EmptyToken | EmptyListToken | -- Lists
  IntLit Integer | CharLit Char | BoolLit Bool | IdentToken String | EOF
  deriving (Show, Eq)

makeTokened :: a -> [PositionedToken] -> Tokened a
makeTokened = Tokened

getTokenRange :: [PositionedToken] -> Maybe PositionRange
getTokenRange [] = Nothing
getTokenRange ((Positioned _ x):xs) = Just (getTokenRange' x xs)
  where
    getTokenRange' x [] = x
    getTokenRange' x ((Positioned _ y):ys) = setNewRange x (getTokenRange' y ys)

getTokenedRange :: Tokened a -> PositionRange
getTokenedRange (Tokened _ []) = error "Empty tokened"
getTokenedRange (Tokened _ ((Positioned _ x):xs)) = setNewRange x (getTokenedRange' xs)
  where
    getTokenedRange' [] = x
    getTokenedRange' ((Positioned _ x):xs) = setNewRange x (getTokenedRange' xs)

getTokened :: Tokened a -> a
getTokened (Tokened x _) = x

getTokenedTokens :: Tokened a -> [PositionedToken]
getTokenedTokens (Tokened _ x) = x

addTokenedToken :: Tokened a -> PositionedToken -> Tokened a
addTokenedToken (Tokened x xs) t = Tokened x (t:xs)

addTokenedTokens :: Tokened a -> [PositionedToken] -> Tokened a
addTokenedTokens (Tokened x xs) ts = Tokened x (ts ++ xs)
