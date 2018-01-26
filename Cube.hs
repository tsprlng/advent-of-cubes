module Cube where

import Graphics.Rendering.OpenGL as GL
import qualified Data.Map as M

import Pieces

vertex3 :: GLfloat -> GLfloat -> GLfloat -> GL.Vertex3 GLfloat
vertex3 = GL.Vertex3

color3 :: GLfloat -> GLfloat -> GLfloat -> GL.Color3 GLfloat
color3 = GL.Color3

type PieceMap = M.Map (Int, Int) Bool

pieceAsMap :: Piece -> PieceMap
pieceAsMap (Piece (_, vs)) = M.fromList $ concat $ zipWith row [0..] [[0,1,2,3,4], [15,f,f,f,5], [14,f,f,f,6], [13,f,f,f,7], [12,11,10,9,8]]
  where
    row = \y cs -> zipWith (\x c -> ((x,y), isFilled c)) [0..] cs
    f = (-1)
    isFilled (-1) = True
    isFilled v = vs !! v

whichFaces :: PieceMap -> M.Map (Int, Int) (Bool, Bool, Bool, Bool, Bool)
whichFaces pieceMap = M.fromList $ map answer $ M.toList pieceMap
  where
    answer ((x,y), self) = ((x,y), (self, should (x, y-1), should (x, y+1), should (x-1, y), should (x+1, y)))
      where
        should (x,y) = self && not (M.findWithDefault False (x,y) pieceMap)

type NumShrinker = GLfloat -> GLfloat -> GLfloat

pieceToLines :: Piece -> [Vertex3 GLfloat]
pieceToLines piece = concatMap toQuads $ M.toList $ whichFaces $ pieceAsMap piece
  where
    sz = 200

    aa  ((x,y),(s,t,b,l,r)) = shrink (l,(+),t,(+)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz)      0
    bb  ((x,y),(s,t,b,l,r)) = shrink (r,(-),t,(+)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz)      0
    cc  ((x,y),(s,t,b,l,r)) = shrink (r,(-),b,(-)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz + sz) 0
    dd  ((x,y),(s,t,b,l,r)) = shrink (l,(+),b,(-)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz + sz) 0
    aa' ((x,y),(s,t,b,l,r)) = shrink (l,(+),t,(+)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz)      sz
    bb' ((x,y),(s,t,b,l,r)) = shrink (r,(-),t,(+)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz)      sz
    cc' ((x,y),(s,t,b,l,r)) = shrink (r,(-),b,(-)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz + sz) sz
    dd' ((x,y),(s,t,b,l,r)) = shrink (l,(+),b,(-)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz + sz) sz

    toQuads :: ((Int, Int), (Bool, Bool, Bool, Bool, Bool)) -> [Vertex3 GLfloat]
    toQuads info@((x,y), (s, t, b, l, r)) = map (\f -> f info) $ concat [
        if t then [aa,bb,bb,bb',bb',aa',aa',aa] else [],
        if b then [cc,dd,dd,dd',dd',cc',cc',cc] else [],
        if l then [aa,dd,dd,dd',dd',aa',aa',aa] else [],
        if r then [bb,cc,cc,cc',cc',bb',bb',bb] else []
      ]

    shrink :: (Bool, NumShrinker, Bool, NumShrinker) -> Vertex3 GLfloat -> Vertex3 GLfloat
    shrink (xc, xt, yc, yt) (Vertex3 x y z) = Vertex3 (if xc then xt x sz else x) (if yc then yt y sz else y) z
      where
        sz = 18

pairConcat :: [([a],[b])] -> ([a],[b])
pairConcat [] = ([],[])
pairConcat ((a,b):xs) = (\(as,bs) -> (a++as, b++bs)) $ pairConcat xs

pieceToQuads :: Piece -> ([Vertex3 GLfloat], [Vertex3 GLfloat])
pieceToQuads piece = pairConcat $ map toQuads $ M.toList $ whichFaces $ pieceAsMap piece
  where
    sz = 200

    aa  ((x,y),(s,t,b,l,r)) = shrink (l,(+),t,(+)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz)      0
    bb  ((x,y),(s,t,b,l,r)) = shrink (r,(-),t,(+)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz)      0
    cc  ((x,y),(s,t,b,l,r)) = shrink (r,(-),b,(-)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz + sz) 0
    dd  ((x,y),(s,t,b,l,r)) = shrink (l,(+),b,(-)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz + sz) 0
    aa' ((x,y),(s,t,b,l,r)) = shrink (l,(+),t,(+)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz)      sz
    bb' ((x,y),(s,t,b,l,r)) = shrink (r,(-),t,(+)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz)      sz
    cc' ((x,y),(s,t,b,l,r)) = shrink (r,(-),b,(-)) $ vertex3 (fromIntegral x * sz + sz) (fromIntegral y * sz + sz) sz
    dd' ((x,y),(s,t,b,l,r)) = shrink (l,(+),b,(-)) $ vertex3 (fromIntegral x * sz)      (fromIntegral y * sz + sz) sz

    toQuads :: ((Int, Int), (Bool, Bool, Bool, Bool, Bool)) -> ([Vertex3 GLfloat], [Vertex3 GLfloat])
    toQuads info@((x,y), (s, t, b, l, r)) = (map (\f -> f info) faces, map (\f -> f info) sides)
      where
        --faces = if s then [aa,bb,cc,dd] else []
        --faces = if s then [aa',bb',cc',dd'] else []  -- TODO why not symmetrical?
        faces = if s then [aa,bb,cc,dd,aa',bb',cc',dd'] else []
        sides = concat [
            if t then [aa,bb,bb',aa'] else [],
            if b then [cc,dd,dd',cc'] else [],
            if l then [aa,dd,dd',aa'] else [],
            if r then [bb,cc,cc',bb'] else []
          ]

    shrink :: (Bool, NumShrinker, Bool, NumShrinker) -> Vertex3 GLfloat -> Vertex3 GLfloat
    shrink (xc, xt, yc, yt) (Vertex3 x y z) = Vertex3 (if xc then xt x sz else x) (if yc then yt y sz else y) z
      where
        sz = 18.0

lineColor, faceColor :: Piece -> Color4 GLfloat
lineColor (Piece ((0,_,_),_)) = Color4 0.8 0.2 0.22 1
lineColor (Piece ((1,_,_),_)) = Color4 1 1 0.4 1
lineColor (Piece ((2,_,_),_)) = Color4 0.8 0.5 0.2 1
lineColor (Piece ((3,_,_),_)) = Color4 0.2 0.8 0.2 1
lineColor (Piece ((4,_,_),_)) = Color4 0.2 0.2 0.6 1
lineColor (Piece ((5,_,_),_)) = Color4 0.6 0.1 0.44 1
faceColor piece@(Piece ((c,_,_),_)) = (\(Color4 r g b a) -> Color4 r g b 0.78) $ lineColor piece
sideColor piece@(Piece ((c,_,_),_)) = (\(Color4 r g b a) -> Color4 (r+(g+b)*0.3) (g+(r+b)*0.3) (b+(r+g)*0.3) 0.82) $ lineColor piece

transforms :: [ (Vertex3 GLfloat -> Vertex3 GLfloat) ]
transforms = [
    \(Vertex3 x y z) -> Vertex3 (1000-x) (1000-y) z,
    \(Vertex3 x y z) -> Vertex3 (1000-x) z (200-y),
    \(Vertex3 x y z) -> Vertex3 (1000-z) (1000-y) (x-800),
    \(Vertex3 x y z) -> Vertex3 z (1000-y) (200-x),
    \(Vertex3 x y z) -> Vertex3 (1000-x) (y) (-600-z),
    \(Vertex3 x y z) -> Vertex3 (1000-x) (1000-z) (y-800)
  ]
