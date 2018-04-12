{-# LANGUAGE OverloadedStrings #-}
import Haste hiding (alert)
import Haste.DOM
import Haste.Foreign
import Data.IORef

import Foreign.C.Types (CDouble)
import Numeric (showHex)

import Solver (allColorPossibilities, netPieces)
import Cube (transforms, pieceToQuads, Vertex, faceColor, sideColor)

import Haste.DOM
mkTitle :: String -> IO Elem
mkTitle text = do
  textElem <- newTextElem text
  title <- newElem "h1" `with` [ children [textElem] ]
  return title

v3c :: (CDouble, CDouble, CDouble) -> (Double, Double, Double)
v3c (x,y,z) = (realToFrac x, realToFrac y, realToFrac z)

-- color to css color
c4c :: (CDouble, CDouble, CDouble, a) -> String
c4c (r,g,b,_) = "#" ++ concatMap floatToCssHex [r,g,b]
  where
    floatToCssHex n = showHex (min 255 $ round (255.0 * realToFrac n)) ""

main :: IO ()
main = do
  render

render = do
  let pcs = netPieces $ head allColorPossibilities
  (flip mapM_) (zip pcs Cube.transforms) $ \(piece,transform) -> do
    let (frontFace, backFace, sides) = pieceToQuads piece
    (flip addMeshFromQuads (c4c $ faceColor piece)) $ map v3c $ map transform $ backFace
  (flip mapM_) (zip pcs Cube.transforms) $ \(piece,transform) -> do
    let (frontFace, backFace, sides) = pieceToQuads piece
    (flip addMeshFromQuads (c4c $ sideColor piece)) $ map v3c $ map transform $ sides
  (flip mapM_) (zip pcs Cube.transforms) $ \(piece,transform) -> do
    let (frontFace, backFace, sides) = pieceToQuads piece
    (flip addMeshFromQuads (c4c $ faceColor piece)) $ map v3c $ map transform $ frontFace

alert :: String -> IO ()
alert = ffi "((s)=>{window.alert(s)})"

addMeshFromQuads :: [(Double, Double, Double)] -> String -> IO ()
addMeshFromQuads = ffi "addMeshFromQuads"
