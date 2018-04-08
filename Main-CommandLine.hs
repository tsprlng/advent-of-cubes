module Main where

import Pieces
import Solver
import Data.List (intercalate)

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

instance Show Net where
  show (Net [a,b,c,d,e,f]) = intercalate "\n" $ map (foldl1 append) [
    [  x   , show f,   x   ],
    [show c, show a, show d],
    [  x   , show b,   x   ],
    [  x   , show e,   x   ] ]
    where
      x = intercalate "\n" $ replicate 5 "     "
      append a b = unlines $ zipWith (\a b -> a ++ "  " ++ b) (lines a) (lines b)

main = do
  mapM_ (\n -> putStrLn $ (("Color " ++ show n ++ ": ") ++) $ show $ length $ possibilities n) [0..5]
  putStrLn ""
  putStrLn $ ("One of each: " ++) $ show $ length allColorPossibilities
  putStrLn ""
  putStrLn $ intercalate "\n--\n" $ map show $ allColorPossibilities
