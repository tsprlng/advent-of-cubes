module Main where

import Solver
import Data.List (intercalate)

main = do
  mapM_ (\n -> putStrLn $ (("Color " ++ show n ++ ": ") ++) $ show $ length $ possibilities n) [0..5]
  putStrLn ""
  putStrLn $ ("One of each: " ++) $ show $ length allColorPossibilities
  putStrLn ""
  putStrLn $ intercalate "\n--\n" $ map show $ allColorPossibilities
