{-|
Converts a cube-solution from Solver into 3D vertexes and colours for rendering.
-}
module Cube (
  pieceToLines,
  pieceToQuads,
  transforms,
  sideColor,
  lineColor,
  faceColor,
  GLfloat,
  Vertex,
  Color4
) where

import qualified Data.Map as M

import Pieces

type GLfloat = Double
type Vertex = (GLfloat, GLfloat, GLfloat)

type Color4 = (GLfloat, GLfloat, GLfloat, GLfloat)

vertex3 :: GLfloat -> GLfloat -> GLfloat -> Vertex
vertex3 x y z = (x,y,z)

type PieceMap = M.Map (Int, Int) Bool

pieceAsMap :: Piece -> PieceMap
pieceAsMap (Piece (_, vs)) = M.fromList $ concat $ zipWith row [0..] [[0,1,2,3,4], [15,f,f,f,5], [14,f,f,f,6], [13,f,f,f,7], [12,11,10,9,8]]
  where
    row = \y cs -> zipWith (\x c -> ((x,y), isFilled c)) [0..] cs
    f = (-1)
    isFilled (-1) = True
    isFilled v = vs !! v

whichFaces :: PieceMap -> M.Map (Int, Int) (Bool, (Bool, Bool, Bool, Bool), (Bool, Bool, Bool, Bool))
whichFaces pieceMap = M.fromList $ map answer $ M.toList pieceMap
  where
    answer ((x,y), self)
      = ((x,y), (
          self,
          (should (x, y-1), should (x, y+1), should (x-1, y), should (x+1, y)),
          (should (x-1, y-1), should (x+1, y-1), should (x+1, y+1), should (x-1, y+1))
        ))
      where
        should (x,y) = self && not (M.findWithDefault False (x,y) pieceMap)

type NumShrinker = GLfloat -> GLfloat -> GLfloat

pieceToLines :: Piece -> [Vertex]
pieceToLines piece = concatMap toQuads $ M.toList $ whichFaces $ pieceAsMap piece
  where
    sz = 200.0
    back :: Vertex -> Vertex
    back (x,y,z) = (x, y, z + 160)

    aa  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (t && not l,(-),l && not t,(-)) $ shrink (tl||l,(+),tl||t,(+)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz)      10
    bb  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (t && not r,(+),r && not t,(-)) $ shrink (tr||r,(-),tr||t,(+)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz)      10
    cc  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (b && not r,(+),r && not b,(+)) $ shrink (br||r,(-),br||b,(-)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz + sz) 10
    dd  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (b && not l,(-),l && not b,(+)) $ shrink (bl||l,(+),bl||b,(-)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz + sz) 10
    aa' = back . aa
    bb' = back . bb
    cc' = back . cc
    dd' = back . dd

    toQuads :: ((Int, Int), (Bool, (Bool, Bool, Bool, Bool), (Bool, Bool, Bool, Bool))) -> [Vertex]
    toQuads info@(_, (s, (t, b, l, r), _)) = map (\f -> f info) $ concat [
        if t then [aa,bb,bb,bb',bb',aa',aa',aa] else [],
        if b then [cc,dd,dd,dd',dd',cc',cc',cc] else [],
        if l then [aa,dd,dd,dd',dd',aa',aa',aa] else [],
        if r then [bb,cc,cc,cc',cc',bb',bb',bb] else []
      ]

    shrink :: (Bool, NumShrinker, Bool, NumShrinker) -> Vertex -> Vertex
    shrink (xc, xt, yc, yt) (x, y, z) = vertex3 (if xc then xt x sz else x) (if yc then yt y sz else y) z
      where
        sz = 18

threeConcat :: [([a],[b],[c])] -> ([a],[b],[c])
threeConcat [] = ([],[],[])
threeConcat ((a,b,c):xs) = (\(as,bs,cs) -> (a++as, b++bs, c++cs)) $ threeConcat xs

pieceToQuads :: Piece -> ([Vertex], [Vertex], [Vertex])
pieceToQuads piece = threeConcat $ map toQuads $ M.toList $ whichFaces $ pieceAsMap piece
  where
    sz = 200
    back :: Vertex -> Vertex
    back (x,y,z) = (x, y, z + 160)

    aa  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (t && not l,(-),l && not t,(-)) $ shrink (tl||l,(+),tl||t,(+)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz)      10
    bb  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (t && not r,(+),r && not t,(-)) $ shrink (tr||r,(-),tr||t,(+)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz)      10
    cc  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (b && not r,(+),r && not b,(+)) $ shrink (br||r,(-),br||b,(-)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz + sz) 10
    dd  ((x,y),(s,(t,b,l,r),(tl,tr,br,bl))) = shrink (b && not l,(-),l && not b,(+)) $ shrink (bl||l,(+),bl||b,(-)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz + sz) 10
    aa' = back . aa
    bb' = back . bb
    cc' = back . cc
    dd' = back . dd

    toQuads :: ((Int, Int), (Bool, (Bool, Bool, Bool, Bool), (Bool, Bool, Bool, Bool))) -> ([Vertex], [Vertex], [Vertex])
    toQuads info@(_, (s, (t, b, l, r), _)) = (map (\f -> f info) frontFace, map (\f -> f info) backFace, map (\f -> f info) sides)
      where
        backFace = if s then [aa,dd,cc,bb] else []
        frontFace = if s then [aa',bb',cc',dd'] else []
        sides = concat [
            if t then [aa,bb,bb',aa'] else [],
            if b then [cc,dd,dd',cc'] else [],
            if l then [aa,aa',dd',dd] else [],
            if r then [bb,cc,cc',bb'] else []
          ]

    shrink :: (Bool, NumShrinker, Bool, NumShrinker) -> Vertex -> Vertex
    shrink (xc, xt, yc, yt) (x, y, z) = vertex3 (if xc then xt x sz else x) (if yc then yt y sz else y) z
      where
        sz = 18

lineColor, faceColor :: Piece -> Color4
lineColor (Piece ((Red,_,_),_))     = (0.8, 0.2, 0.22, 1)  -- red
lineColor (Piece ((Yellow,_,_),_))  = (1.0, 1.0, 0.4, 1)   -- yello
lineColor (Piece ((Orange,_,_),_))  = (0.8, 0.5, 0.2, 1)   -- orng
lineColor (Piece ((Green,_,_),_))   = (0.2, 0.8, 0.2, 1)   -- green
lineColor (Piece ((Blue,_,_),_))    = (0.2, 0.2, 0.6, 1)   -- blue
lineColor (Piece ((Purple,_,_),_))  = (0.6, 0.1, 0.44, 1)  -- purple
faceColor piece@(Piece ((c,_,_),_)) = (\(r, g, b, a) -> (r, g, b, 0.84)) $ lineColor piece
sideColor piece@(Piece ((c,_,_),_)) = (\(r, g, b, a) -> ((r+(g+b)*0.3), (g+(r+b)*0.3), (b+(r+g)*0.3), 0.82)) $ lineColor piece

rotate5 :: GLfloat -> Vertex -> Vertex
rotate5 p' v = r' p v
  where
    p = 3.14 * (1 - p')
    r' :: GLfloat -> Vertex -> Vertex
    r' p (x, y, z) = (x, cos p * y + sin p * z, sin p * y + cos p * z)

transforms :: GLfloat -> [ (Vertex -> Vertex) ]
transforms p = [
    mix p $ \(x, y, z) -> (vertex3 (500-x) (500-y) (300+z),  vertex3 (-x+spacing) (-y) (z)),
    mix p $ \(x, y, z) -> (vertex3 (500-x) (-300-z) (500-y), vertex3 (-x+spacing) (-y-2*spacing) (z)),
    mix p $ \(x, y, z) -> (vertex3 (300+z) (500-y) (x-500),  vertex3 (-x+3*spacing) (-y) (z)),
    mix p $ \(x, y, z) -> (vertex3 (-300-z) (500-y) (500-x), vertex3 (-x-spacing) (-y) (z)),
    mix p $ \(x', y', z') -> let (x,y,z) = rotate5 p (x',y',z') in (vertex3 (500-x) (y-500) (-300-z), vertex3 (-x+spacing) (y-4*spacing) (0-z)),
    mix p $ \(x, y, z) -> (vertex3 (500-x) (300+z) (y-500),  vertex3 (-x+spacing) (-y+2*spacing) (z))
  ]
  where
    spacing = 500
    mix p flappy = \(x,y,z)-> let ((xx,yy,zz),(xxx,yyy,zzz)) = flappy (x,y,z) in vertex3 (mixx p xxx xx) (mixx p yyy yy) (mixx p zzz zz)
    mixx p x xx = p*xx + (1 - abs p)*x

--rotato :: Vertex -> [Vertex] -> [Vertex]
--rotato (r,p,y) = map (\(x,y,z) -> )
