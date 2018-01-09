module Main where

import Solver
import Data.List (intercalate)

main = do
  putStrLn . show $ length allColorPossibilities
  putStrLn $ intercalate "\n--\n" $ map show $ allColorPossibilities
