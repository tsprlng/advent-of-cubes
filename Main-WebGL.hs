{-# LANGUAGE OverloadedStrings #-}
import Haste hiding (alert)
import Haste.DOM
import Haste.Foreign
import Data.IORef

import Solver (allColorPossibilities, netPieces)
import Cube (transforms, pieceToQuads)

import Haste.DOM
mkTitle :: String -> IO Elem
mkTitle text = do
  textElem <- newTextElem text
  title <- newElem "h1" `with` [ children [textElem] ]
  return title

main :: IO ()
main = do
  titleElem <- mkTitle "Hello World"
  appendChild documentBody titleElem

render = do
  let pcs = netPieces $ head allColorPossibilities
  mapM_ (zip pcs Cube.transforms) $ \(piece,transform) -> do
    let (faces, sides) = pieceToQuads piece
    addMeshFromQuads $ map transform $ faces

alert :: String -> IO ()
alert = ffi "((s)=>{window.alert(s)})"
