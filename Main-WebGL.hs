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
  let pcs = netPieces $ head allColorPossibilities
  let (frontFace, backFace, sides) = (\(fF,_,_)->fF, \(_,bF,_)->bF, \(_,_,s)->s)
  forM_ [(backFace, faceColor), (sides, sideColor), (frontFace, faceColor)] $ \(quadFilter, colorer) -> do
    (flip mapM_) (zip pcs $ Cube.transforms 1) $ \(piece,transform) -> do
      (flip addMeshFromQuads (cssColor $ colorer piece)) $ map transform $ quadFilter $ pieceToQuads piece

-- TODO this choice of interface is very useful as a proof of concept but is pretty shit as an actual design
addMeshFromQuads :: [(Double, Double, Double)] -> CssColor -> IO ()
addMeshFromQuads = ffi "(quads, color)=>{ postMessage({quads: quads, color: color}); };"

--offerCube :: [(CssColor, [(Double, Double, Double)])] -> IO ()
--offerCube :: ffi "function(quadSets){ postMessage({newCube: quadSets}) }"
