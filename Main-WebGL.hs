import Haste
import Haste.DOM
import Data.IORef

mkTitle :: String -> IO Elem
mkTitle text = do
  textElem <- newTextElem text
  title <- newElem "h1" `with` [ children [textElem] ]
  return title

main :: IO ()
main = do
  titleElem <- mkTitle "Hello World"
  appendChild documentBody titleElem
