{-# LANGUAGE OverloadedStrings #-}
import Haste hiding (alert)
import Haste.DOM
import Haste.Foreign
import Data.IORef

import Foreign.C.Types (CDouble)

import Solver (allColorPossibilities, netPieces)
import Cube (transforms, pieceToQuads, Vertex)

import Haste.DOM
mkTitle :: String -> IO Elem
mkTitle text = do
  textElem <- newTextElem text
  title <- newElem "h1" `with` [ children [textElem] ]
  return title

v3c :: (CDouble, CDouble, CDouble) -> (Double, Double, Double)
v3c (x,y,z) = (realToFrac x, realToFrac y, realToFrac z)

main :: IO ()
main = do
  titleElem <- mkTitle "Hello World"
  appendChild documentBody titleElem
  render

render = do
  let pcs = netPieces $ head allColorPossibilities
  (flip mapM_) (zip pcs Cube.transforms) $ \(piece,transform) -> do
    let (faces, sides) = pieceToQuads piece
    (flip addMeshFromQuads "#cc8844") $ map v3c $ map transform $ faces
    (flip addMeshFromQuads "#eecc88") $ map v3c $ map transform $ sides

alert :: String -> IO ()
alert = ffi "((s)=>{window.alert(s)})"

addMeshFromQuads :: [(Double, Double, Double)] -> String -> IO ()
addMeshFromQuads = ffi "addMeshFromQuads"
