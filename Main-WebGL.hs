{-# LANGUAGE OverloadedStrings #-}

import Haste
import Haste.DOM
import Haste.Foreign
import Data.IORef

import Numeric (showHex)

import Solver (allColorPossibilities, netPieces)
import Cube (Color4, transforms, pieceToQuads, Vertex, faceColor, sideColor)

cssColor :: Color4 -> String
cssColor (r,g,b,_) = "#" ++ concatMap floatToCssHex [r,g,b]
  where
    floatToCssHex n = showHex (min 255 $ round (255.0 * realToFrac n)) ""

main :: IO ()
main = do
  render

render = do
  let pcs = netPieces $ head allColorPossibilities
  (flip mapM_) (zip pcs $ Cube.transforms 1) $ \(piece,transform) -> do
    let (frontFace, backFace, sides) = pieceToQuads piece
    (flip addMeshFromQuads (cssColor $ faceColor piece)) $ map transform $ backFace
  (flip mapM_) (zip pcs $ Cube.transforms 1) $ \(piece,transform) -> do
    let (frontFace, backFace, sides) = pieceToQuads piece
    (flip addMeshFromQuads (cssColor $ sideColor piece)) $ map transform $ sides
  (flip mapM_) (zip pcs $ Cube.transforms 1) $ \(piece,transform) -> do
    let (frontFace, backFace, sides) = pieceToQuads piece
    (flip addMeshFromQuads (cssColor $ faceColor piece)) $ map transform $ frontFace

addMeshFromQuads :: [(Double, Double, Double)] -> String -> IO ()
addMeshFromQuads = ffi "addMeshFromQuads"
