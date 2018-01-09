import Pieces
import Data.List (intercalate, groupBy)
import Debug.Trace (trace)

newtype Net = Net [Piece]
type PieceVariations = [Piece]

instance Show Net where
  show (Net [a,b,c,d,e,f]) = intercalate "\n" $ map (foldl1 append) [
    [empty, show f, empty],
    [show c, show a, show d],
    [empty, show b, empty],
    [empty, show e, empty] ]
    where
      empty = intercalate "\n" $ replicate 5 "     "

append :: String -> String -> String
append a b = unlines $ zipWith (\a b -> a ++ "  " ++ b) (lines a) (lines b)

choices :: [a] -> [(a, [a])]
choices [] = []
choices (x:xs) = (x, xs) : map (\(c,xs) -> (c, x:xs)) (choices xs)

rotate :: Int -> [a] -> [a]
rotate n xs = drop n xs ++ take n xs

nand True True = False
nand _ _ = True

xor False True = True
xor True False = True
xor _ _ = False

edges :: Piece -> Edges
edges (Piece (_,p)) = map (map (p!!)) [[0,1,2,3,4],[4,5,6,7,8],[8,9,10,11,12],[12,13,14,15,0]]
  -- this isn't very general or succinct is it?

interfaces2 :: Edge -> Edge -> Bool
interfaces2 edge edge1 = all id $ zipWith (\f (x,y) -> f x y) [nand, xor, xor, xor, nand] $ zip edge edge1

interfaces3 e1a e1b e2a e2b = corner && line1 && line2
  where
    line1 = all id $ zipWith (\f (x,y) -> f x y) [ignore, xor, xor, xor, ignore] $ zip e1a e1b
    line2 = all id $ zipWith (\f (x,y) -> f x y) [ignore, xor, xor, xor, ignore] $ zip e2a e2b
    corner = (==1).length $ filter id $ map (!!0) [e1a, e1b, e2a] 
    ignore = \a b-> True

interface2 edge edge1 = zipWith (||) edge edge1

variations :: Piece -> [Piece]
variations (Piece ((c,s,l), vxs)) = (map (\vxs -> Piece ((c,s,l), vxs)) $ rots vxs) ++ (map (\vxs -> Piece ((c,not s,l), vxs)) $ map flip $ rots vxs)
  where
    rots vxs = take 4 $ iterate (rotate 4) vxs
    flip vxs = head vxs : reverse (tail vxs)

groupsOfColorPieces = groupBy (\(Piece ((c1,_,_),_)) (Piece ((c2,_,_),_)) -> c1==c2) pieces

allColorPossibilities :: [Net]
allColorPossibilities = concatMap tryPiece (head groupsOfColorPieces)
  where
    tryPiece p = map (Net . (p:)) $ possibilities2 p $ map (concatMap variations) (tail groupsOfColorPieces)


possibilities :: Color -> [Net]
possibilities color = map (Net . (head thisColor :)) $ possibilities2 (head thisColor) (map variations $ tail thisColor)
  where
    thisColor = filter (\(Piece ((c,s,l),_))->c==color) pieces

possibilities2 :: Piece -> [PieceVariations] -> [[Piece]]
possibilities2 a nexts = concatMap tryVariations $ choices nexts
  where
    tryVariations :: (PieceVariations, [PieceVariations]) -> [[Piece]]
    tryVariations (variations, others) = concatMap tryVariation variations
      where
        tryVariation b
          | interfaces2 (reverse $ edges a !! 2) (edges b !! 0) = map (b:) $ possibilities3a a b others
          | otherwise = []

possibilities3a :: Piece -> Piece -> [PieceVariations] -> [[Piece]]
possibilities3a a b nexts = concatMap tryVariations $ choices nexts
  where
    tryVariations (variations, others) = concatMap tryVariation variations
      where
        tryVariation c = if valid c then map (c:) $ possibilities3b a b c others else []
        valid c = interfaces3 (edges a !! 3) (reverse $ edges c !! 1) (reverse $ edges b !! 3) (edges c !! 2)

possibilities3b a b c nexts = concatMap tryVariations $ choices nexts
  where
    tryVariations (variations, others) = concatMap tryVariation variations
      where
        tryVariation d = if valid d then map (d:) $ possibilities4 a b c d others else []
        valid d = interfaces3 (reverse $ edges a !! 1) (edges d !! 3) (edges b !! 1) (reverse $ edges d !! 2)

--possibilities4 _ _ _ _ nexts = [map (const xpiece) nexts]
  --where
    --xpiece = Piece (0, replicate 16 False)

possibilities4 a b c d nexts = concatMap tryVariations $ choices nexts
  where
    tryVariations (variations, others) = concatMap tryVariation variations
      where
        tryVariation e = if valid1 e && valid2 e then map (e:) $ possibilities5 a b c d e others else []
        valid1 e = interfaces3 (reverse $ edges b !! 2) (edges e !! 0) (edges c !! 3) (reverse $ edges e !! 3)
        valid2 e = interfaces3 (edges b !! 2) (reverse $ edges e !! 0) (reverse $ edges d !! 1) (edges e !! 1)

possibilities5 a b c d e [lastVariations] = concatMap tryVariation lastVariations
  where
    tryVariation f = if valid1 f && valid2 f && valid3 f && valid4 f then [[f]] else []
    valid1 f = interfaces3 (reverse $ edges e !! 2) (edges f !! 0) (edges c !! 0) (reverse $ edges f !! 3)
    valid2 f = interfaces3 (reverse $ edges d !! 0) (edges f !! 1) (edges e !! 2) (reverse $ edges f !! 0)
    valid3 f = interfaces3 (reverse $ edges a !! 0) (edges f !! 2) (edges d !! 0) (reverse $ edges f !! 1)
    valid4 f = interfaces3 (reverse $ edges c !! 0) (edges f !! 3) (edges a !! 0) (reverse $ edges f !! 2)
-- -}

-- pick first
-- match first[0] second[0]

-- match third1[0] first[3], third1[3] second[1]
-- match third2[0] first[1], third2[3] second[3]

-- match fourth[0] first[2], fourth[1] third1[1], fourth[3] third2[1]

-- match fifth[0]

--possibilities1 otherPieces edge
