module Pieces where

import Data.List (intercalate)

type FlipSide = Bool
type Color = Int
type Label = String
type Voxel = Bool
newtype Piece = Piece ((Color, FlipSide, Label), [Voxel])

type Edge = [Voxel]
type Edges = [Edge]

instance Show Piece where
  show (Piece ((colorIdx, flipside, label), vs))
    = color colorIdx ++ intercalate ('\n' : color colorIdx) lines ++ reset
      where
        lines = map (concatMap showBit) [
          [ 0, 1, 2, 3, 4],
          [15, x, x, x, 5],
          [14, x,ll, x, 6],
          [13, x, x, x, 7],
          [12,11,10, 9, 8] ]

        x = (-1)
        ll = (-2)
        showBit (-1) = filled
        showBit (-2) = label
        showBit n = if (vs !! n) then filled else " "
        filled = if flipside then "█" else "▓"

        color 0 = "\ESC[1;31m"     -- red
        color 1 = "\ESC[1;33m"     -- yellow
        color 2 = "\ESC[38;5;208m" -- orrnj
        color 3 = "\ESC[1;32m"     -- green
        color 4 = "\ESC[1;36m"     -- blue
        color 5 = "\ESC[1;35m"     -- purple

        reset = "\ESC[0m"

pieces :: [Piece]
pieces = zipWith (\idx (c,vs)-> Piece ((c, True, show (mod idx 6)), map (=='1') vs)) [0..] [
  -- red
  (0, "1101011011011100"),
  (0, "1010011000101101"),
  (0, "1101001101010010"),
  (0, "0101010100100001"),
  (0, "0010000110101101"),
  (0, "0101001000100010"),
  -- yellow
  (1, "0101001000101101"),
  (1, "1101101001011010"),
  (1, "0010001001010101"),
  (1, "0101001011000101"),
  (1, "0010010100101101"),
  (1, "1110001011010010"),
  -- orrnj
  (2, "0100001000100101"),
  (2, "1010110101001101"),
  (2, "0110001000110010"),
  (2, "0101010110100011"),
  (2, "0001101011010101"),
  (2, "1101001001011010"),
  -- green
  (3, "0101110110101101"),
  (3, "0101110110100010"),
  (3, "0101001001010010"),
  (3, "0101010101010010"),
  (3, "0010110100100010"),
  (3, "0010110110100010"),
  -- blue
  (4, "0101001000100010"),
  (4, "0101110100100101"),
  (4, "0101101001010101"),
  (4, "1101101011011010"),
  (4, "0010110111010101"),
  (4, "0010001000100010"),
  -- purple
  (5, "0010001001010100"),
  (5, "1010010111000101"),
  (5, "1010010100110001"),
  (5, "1110011011100010"),
  (5, "1100010100101101"),
  (5, "0001001000111101") ]
