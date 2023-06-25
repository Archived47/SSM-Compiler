{-# LANGUAGE ExistentialQuantification #-}
module Compiler.Position where
import Data.Default (Default (def))

data Position = Position {line :: Int, column :: Int}
  deriving (Show, Eq)
data PositionRange = PositionRange Position Position
  deriving (Show, Eq)
data Positioned a = Positioned a PositionRange
  deriving (Show, Eq)

instance Ord Position where
  compare (Position lineA columnA) (Position lineB columnB)
    | lineA < lineB = LT
    | lineA == lineB && columnA < columnB = LT
    | lineA == lineB && columnA == columnB = EQ
    | otherwise = GT

getPosItem :: Positioned a -> a
getPosItem (Positioned a _) = a

getPosition :: Positioned a -> PositionRange
getPosition (Positioned _ pos) = pos

getRange :: Positioned a -> PositionRange
getRange (Positioned _ (PositionRange start end)) = PositionRange start end

getRanges :: [Positioned a] -> PositionRange
getRanges = foldr (setNewRange . getRange) (PositionRange def def)

isInRange :: Position -> PositionRange -> Bool
isInRange pos range = pos >= getRangeStart range && pos <= getRangeEnd range

hasRangeOverlap :: PositionRange -> PositionRange -> Bool
hasRangeOverlap (PositionRange startA endA) (PositionRange startB endB) = startA <= endB && endA >= startB

getRangeStart :: PositionRange -> Position
getRangeStart (PositionRange start _) = start

getRangeEnd :: PositionRange -> Position
getRangeEnd (PositionRange _ end) = end

addRanges :: Positioned a -> Positioned a -> Positioned a
addRanges (Positioned a rangeA) (Positioned b rangeB) = Positioned a (setNewRange rangeA rangeB)

setNewRange :: PositionRange -> PositionRange -> PositionRange
setNewRange (PositionRange startA endA) (PositionRange startB endB) = PositionRange (getEarliestPosition startA startB) (getLatestPosition endA endB)

addCols :: Int -> Position -> Position
addCols n (Position line col) = Position line (col + n)

addRows :: Int -> Position -> Position
addRows n (Position line col) = Position (line + n) defaultCol

addColsRange :: Int -> PositionRange -> PositionRange
addColsRange n (PositionRange start end) = PositionRange start (addCols n end)

addRowsRange :: Int -> PositionRange -> PositionRange
addRowsRange n (PositionRange start end) = PositionRange start (addRows n end)

createPosition :: Int -> Int -> Position
createPosition = Position

getEarliestPosition :: Position -> Position -> Position
getEarliestPosition (Position lineA columnA) (Position lineB columnB)
  | lineA < lineB = Position lineA columnA
  | lineA == lineB && columnA < columnB = Position lineA columnA
  | otherwise = Position lineB columnB

getLatestPosition :: Position -> Position -> Position
getLatestPosition (Position lineA columnA) (Position lineB columnB)
  | lineA > lineB = Position lineA columnA
  | lineA == lineB && columnA > columnB = Position lineA columnA
  | otherwise = Position lineB columnB

createRange :: Position -> PositionRange
createRange pos = PositionRange pos (addCols 1 pos)

start :: Position
start = Position 0 0

defaultRow :: Int
defaultRow = 1

defaultCol :: Int
defaultCol = 1

nextLine :: Position -> Position
nextLine (Position line col) = Position (line + 1) defaultCol

nextColumn :: Position -> Position
nextColumn (Position line column) = Position line (column + 1)

nextColumnRange :: PositionRange -> PositionRange
nextColumnRange (PositionRange start end) = PositionRange start (nextColumn end)

startRange :: PositionRange
startRange = PositionRange start start

instance Default Position where
  def = Position 1 1

instance Default PositionRange where
  def = createRange def