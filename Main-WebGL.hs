{-# LANGUAGE OverloadedStrings #-}

import Haste
import Haste.DOM
import Haste.Foreign
import Data.IORef
import Control.Monad (forM_)

import Numeric (showHex)

import Solver (allColorPossibilities, netPieces)
import Cube (Color4, transforms, pieceToQuads, Vertex, faceColor, sideColor)

type CssColor = String

cssColor :: Color4 -> CssColor
cssColor (r,g,b,_) = "#" ++ concatMap floatToCssHex [r,g,b]
  where
    floatToCssHex n = showHex (min 255 $ round (255.0 * realToFrac n)) ""

main :: IO ()
main = do
  render

render :: IO ()
render = do
  let (frontFace, backFace, sides) = (\(fF,_,_)->fF, \(_,bF,_)->bF, \(_,_,s)->s)

  let pcs = netPieces $ head allColorPossibilities
  forM_ [(backFace, faceColor), (sides, sideColor), (frontFace, faceColor)] $ \(quadFilter, colorer) -> do
    (flip mapM_) (zip pcs $ Cube.transforms 1) $ \(piece,transform) -> do
      (flip addMeshFromQuads (cssColor $ colorer piece)) $ map transform $ quadFilter $ pieceToQuads piece

  forM_ (map netPieces $ allColorPossibilities) $ \pcs -> do
    let stuff = flip concatMap [(backFace, faceColor), (sides, sideColor), (frontFace, faceColor)] $ \(quadFilter, colorer) ->
      flip map (zip pcs $ Cube.transforms 1) $ \(piece, transform) ->
        (cssColor $ colorer piece, map transform $ quadFilter $ pieceToQuads piece)
    offerCube stuff

addMeshFromQuads :: [(Double, Double, Double)] -> CssColor -> IO ()
addMeshFromQuads = ffi "(quads, color)=>{ postMessage({quads: quads, color: color}); };"

offerCube :: [(CssColor, [(Double, Double, Double)])] -> IO ()
offerCube :: ffi "function(quadSets){ postMessage({newCube: quadSets}) }"
