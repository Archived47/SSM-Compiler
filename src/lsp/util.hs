module LSP.Util where


import Language.LSP.Server
import Language.LSP.Types
import Control.Monad.IO.Class
import qualified Data.Text as T
import qualified Compiler.Unification as U
import qualified Compiler.Position as P
import qualified Compiler.AST as P
import Data.Text (Text)
import Compiler.Position (getRange, getRanges)
import qualified Compiler.Scanner as S
import qualified Compiler.Parser as P
import Compiler.Token (getTokenedTokens)




convertPosition' :: P.Position -> Language.LSP.Types.Position
convertPosition' (P.Position l c) = Language.LSP.Types.Position (fromIntegral l -1) (fromIntegral c -1)

lexErrToText :: S.LexerError -> String
lexErrToText (S.Error lexErInner _) = show lexErInner


lexErrToRanges :: S.LexerError -> P.PositionRange
lexErrToRanges (S.Error _ posRange) = posRange

--data PositionRange = PositionRange Position Position

lexErrDataDiag :: S.LexerError -> (Range, Text)
lexErrDataDiag (S.Error lexErInner (P.PositionRange p1 p2)) = (Range (convertPosition' p1) (convertPosition' p2), T.pack (show lexErInner))

parseErrDataDiag :: P.Error -> (Range, Text)
parseErrDataDiag err = case err of
  P.EndOfInput -> (Range (Position 0 0) (Position 0 0), T.pack (show err))
  P.Unexpected po -> (posRangeToRange (getRange po), T.pack (show err))
  P.UnexpectedEndOfFile po -> (posRangeToRange (getRange po), T.pack (show err))
  P.ExpectedEndOfFile po -> (posRangeToRange (getRange po), T.pack (show err))
  P.EmptyFunction pos -> (posRangeToRange (getRanges pos), T.pack (show err))
  P.VarInStatementBody s pos -> (posRangeToRange (getRanges pos), T.pack (show err))
  P.Empty -> (Range (Position 0 0) (Position 0 0), T.pack (show err))
  P.MissingMainFunction -> (Range (Position 0 0) (Position 0 0), T.pack (show err))
  P.MultipleMain ro -> (posRangeToRange (rootToRange ro), T.pack (show err))
  P.MissingSemiColon pos -> (posRangeToRange (getRanges pos), T.pack (show err))

typeErrDataDiag :: U.Error -> (Range, Text)
typeErrDataDiag (U.Error e (P.PositionRange p1 p2)) = (Range (convertPosition' p1) (convertPosition' p2), T.pack (show e))

rootToRange :: P.Root -> P.PositionRange
rootToRange (P.FunDecl func) = getRanges (getTokenedTokens func)
rootToRange (P.VarDecl var) = getRanges (getTokenedTokens var)
rootToRange (P.EmptyRoot _) = P.PositionRange (P.Position 0 0) (P.Position 0 0)

posRangeToRange :: P.PositionRange -> Range
posRangeToRange (P.PositionRange p1 p2) = Range (convertPosition' p1) (convertPosition' p2)

gettErrorsInPosition :: Position -> [(Range, Text)] -> Text
gettErrorsInPosition pos items = let 
    res = filter (\(Range (Position l1 c1) (Position l2 c2), _) -> (l1 <= line && line <= l2) && (c1 <= col && col <= c2)) items
    lst = map snd res
  in concatText lst
  where
    line = _line pos
    col = _character pos

concatText :: [Text] -> Text
concatText [] = T.empty
concatText [x] = x
concatText (x:xs) = T.append (T.append x (T.pack "\n")) (concatText xs)