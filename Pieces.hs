{-|
Describes the puzzle pieces in the original cube game.
-}
module Pieces where

type FlipSide = Bool
data Color = Red | Yellow | Orange | Green | Blue | Purple
  deriving (Eq, Show, Enum, Bounded)
type Label = String
type Voxel = Bool
newtype Piece = Piece ((Color, FlipSide, Label), [Voxel])

type Edge = [Voxel]
type Edges = [Edge]

allColors :: [Color]
allColors = [minBound..maxBound]

pieces :: [Piece]
pieces = zipWith (\idx (vs, c)-> Piece ((c, True, show (mod idx 6)), map (=='1') vs)) [0..] [
  ("1101011011011100", Red),
  ("1010011000101101", Red),
  ("1101001101010010", Red),
  ("0101010100100001", Red),
  ("0010000110101101", Red),
  ("0101001000100010", Red),
  ("0101001000101101", Yellow),
  ("1101101001011010", Yellow),
  ("0010001001010101", Yellow),
  ("0101001011000101", Yellow),
  ("0010010100101101", Yellow),
  ("1110001011010010", Yellow),
  ("0100001000100101", Orange),
  ("1010110101001101", Orange),
  ("0110001000110010", Orange),
  ("0101010110100011", Orange),
  ("0001101011010101", Orange),
  ("1101001001011010", Orange),
  ("0101110110101101", Green),
  ("0101110110100010", Green),
  ("0101001001010010", Green),
  ("0101010101010010", Green),
  ("0010110100100010", Green),
  ("0010110110100010", Green),
  ("0101001000100010", Blue),
  ("0101110100100101", Blue),
  ("0101101001010101", Blue),
  ("1101101011011010", Blue),
  ("0010110111010101", Blue),
  ("0010001000100010", Blue),
  ("0010001001010100", Purple),
  ("1010010111000101", Purple),
  ("1010010100110001", Purple),
  ("1110011011100010", Purple),
  ("1100010100101101", Purple),
  ("0001001000111101", Purple) ]
