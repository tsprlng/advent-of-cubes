{-|
A simple version of the program that draws every solution for any given colour / for the mix of all colours, using terminal escape characters at the command line.
-}
module Main where

import Pieces
import Solver
import Data.List (intercalate)
import Control.Monad (forM_)

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

        color Red    = "\ESC[1;31m"
        color Yellow = "\ESC[1;33m"
        color Orange = "\ESC[38;5;208m"
        color Green  = "\ESC[1;32m"
        color Blue   = "\ESC[1;36m"
        color Purple = "\ESC[1;35m"

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
  forM_ allColors $ \color ->
    putStrLn $ ((show color ++ ": ") ++) $ show $ length $ possibilities color
  putStrLn $ ("One of each: " ++) $ show $ length allColorPossibilities
  putStrLn ""
  putStrLn $ intercalate "\n--\n" $ map show $
    concatMap possibilities allColors ++ allColorPossibilities
