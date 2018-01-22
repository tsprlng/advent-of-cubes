import Graphics.Rendering.OpenGL as GL
import Graphics.UI.GLFW as GLFW
import Graphics.Rendering.OpenGL (($=))
import Data.IORef
import Control.Monad
import System.Environment (getArgs, getProgName)

import qualified Data.Map as M
import Data.Map ((!))
import Pieces
import Solver (allColorPossibilities, netPieces)

data Action = Action (IO Action)

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

pieceToLines :: Piece -> [Vertex3 GLfloat]
pieceToLines piece = concatMap toQuads $ M.toList $ whichFaces $ pieceAsMap piece
  where
    between = 200
    one = 200
    d = (-5)

    aa x y = vertex3 (fromIntegral x *between) (fromIntegral y *between) d
    bb x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between) d
    cc x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between+one) d
    dd x y = vertex3 (fromIntegral x *between) (fromIntegral y *between+one) d
    aa' x y = vertex3 (fromIntegral x *between) (fromIntegral y *between) (d+one)
    bb' x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between) (d+one)
    cc' x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between+one) (d+one)
    dd' x y = vertex3 (fromIntegral x *between) (fromIntegral y *between+one) (d+one)

    toQuads :: ((Int, Int), (Bool, Bool, Bool, Bool, Bool)) -> [Vertex3 GLfloat]
    toQuads ((x,y), (s, t, b, l, r)) = map (\f -> f x y) $ concat [
        if t then [aa,bb,bb,bb',bb',aa',aa',aa] else [],
        if b then [cc,dd,dd,dd',dd',cc',cc',cc] else [],
        if l then [aa,dd,dd,dd',dd',aa',aa',aa] else [],
        if r then [bb,cc,cc,cc',cc',bb',bb',bb] else []
      ]

pieceToQuads :: Piece -> [Vertex3 GLfloat]
pieceToQuads piece = concatMap toQuads $ M.toList $ whichFaces $ pieceAsMap piece
  where
    between = 200
    one = 200
    d = (-5)

    aa x y = vertex3 (fromIntegral x *between) (fromIntegral y *between) d
    bb x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between) d
    cc x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between+one) d
    dd x y = vertex3 (fromIntegral x *between) (fromIntegral y *between+one) d
    aa' x y = vertex3 (fromIntegral x *between) (fromIntegral y *between) (d+one)
    bb' x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between) (d+one)
    cc' x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between+one) (d+one)
    dd' x y = vertex3 (fromIntegral x *between) (fromIntegral y *between+one) (d+one)

    toQuads :: ((Int, Int), (Bool, Bool, Bool, Bool, Bool)) -> [Vertex3 GLfloat]
    toQuads ((x,y), (s, t, b, l, r)) = map (\f -> f x y) $ concat [
        if s then [aa,bb,cc,dd,aa',bb',cc',dd'] else [],
        if t then [aa,bb,bb',aa'] else [],
        if b then [cc,dd,dd',cc'] else [],
        if l then [aa,dd,dd',aa'] else [],
        if r then [bb,cc,cc',bb'] else []
      ]

main = do
  -- invoke either active or passive drawing loop depending on command line argument
  args <- getArgs
  prog <- getProgName
  main' passive
--  case args of
--    ["active"]  -> putStrLn "Running in active mode" >> main' active
--    ["passive"] -> putStrLn "Running in passive mode" >> main' passive
--    _ -> putStrLn $ "USAGE: " ++ prog ++ " [active|passive]"

main' run = do
  GLFW.initialize
  -- open window
  GLFW.openWindow (GL.Size 800 600) [GLFW.DisplayAlphaBits 8, GLFW.DisplayDepthBits 16] GLFW.Window
  GLFW.windowTitle $= "Cube 0 - World of Foam Cubes"
  GL.shadeModel    $= GL.Smooth
  GL.depthFunc $= Just Less
  -- enable antialiasing
  GL.lineSmooth $= GL.Enabled
  GL.blend      $= GL.Enabled
  GL.blendFunc  $= (GL.SrcAlpha, GL.OneMinusSrcAlpha)
  GL.lineWidth  $= 1.5
  -- set the color to clear background
  GL.clearColor $= Color4 0 0 0 0

  -- set 2D orthogonal view inside windowSizeCallback because
  -- any change to the Window size should result in different
  -- OpenGL Viewport.
  aspect <- newIORef 1.0
  GLFW.windowSizeCallback $= \ size@(GL.Size w h) ->
    do
      GL.viewport   $= (GL.Position 0 0, size)
      GL.matrixMode $= GL.Projection
      GL.loadIdentity
      --GL.ortho 0 (realToFrac w) (realToFrac h) 0 (-1) 5
      GL.frustum (-20) (600) (480) (-20) 4 4000
      --GL.frustum (-20) (realToFrac w) (realToFrac h) (-20) 4 4000
      GL.rotate 0.2 (GL.Vector3 0 1 0 :: GL.Vector3 GL.GLfloat)
      GL.translate $ GL.Vector3 0 0 (-14::GLfloat)

      writeIORef aspect (fromIntegral w / fromIntegral h)
  -- keep all line strokes as a list of points in an IORef
  chosenOne <- newIORef 0
  -- run the main loop
  run chosenOne aspect
  -- finish up
  GLFW.closeWindow
  GLFW.terminate

passive chosenOne aspect = do
  -- disable auto polling in swapBuffers
  GLFW.disableSpecial GLFW.AutoPollEvent

  -- keep track of whether ESC has been pressed
  quit <- newIORef False

  -- keep track of whether screen needs to be redrawn
  dirty <- newIORef True

  -- mark screen dirty in refresh callback which is often called
  -- when screen or part of screen comes into visibility.
  GLFW.windowRefreshCallback $= writeIORef dirty True

  -- use key callback to track whether ESC is pressed
  GLFW.keyCallback $= \k s -> do
     when (k == (GLFW.CharKey 'C') && s == GLFW.Press) $ do
        which <- readIORef chosenOne
        let next = if which + 1 == length allColorPossibilities then 0 else which + 1
        writeIORef chosenOne next
        GLFW.windowTitle $= "Cube " ++ show next ++ " - World of Foam Cubes"
        writeIORef dirty True
     when (k == (GLFW.CharKey 'Q') && s == GLFW.Press) $
        writeIORef quit True
     when (fromEnum k == fromEnum GLFW.ESC && s == GLFW.Press) $
        writeIORef quit True

  -- Terminate the program if the window is closed
  GLFW.windowCloseCallback $= (writeIORef quit True >> return True)

  -- by default start with waitForPress
  waitForPress dirty
  loop dirty quit
  where

    loop dirty quit = do
        GLFW.waitEvents
        -- redraw screen if dirty
        d <- readIORef dirty

        when d $
          render chosenOne >> GLFW.swapBuffers

        writeIORef dirty False
        -- check if we need to quit the loop
        q <- readIORef quit
        unless q $
          loop dirty quit

    waitForPress dirty =
      do
        GLFW.mousePosCallback    $= \_ -> return ()

        GLFW.mouseButtonCallback $= \b s ->
            when (b == GLFW.ButtonLeft && s == GLFW.Press) $
              do
                -- when left mouse button is pressed, switch to waitForRelease action.
                (GL.Position x y) <- GL.get GLFW.mousePos
                waitForRelease dirty

    waitForRelease dirty =
      do
        GLFW.mousePosCallback $= \(Position x y) ->
          do

            GL.loadIdentity
            --GL.ortho 0 (realToFrac w) (realToFrac h) 0 (-1) 5
            --GL.frustum (-20) (600) (480) (-20) 4 4000
            --GL.rotate (0.02*fromIntegral x - 12) (GL.Vector3 0 1 0 :: GL.Vector3 GL.GLfloat)
            --GL.rotate (0.02*fromIntegral y - 12) (GL.Vector3 1 0 0 :: GL.Vector3 GL.GLfloat)
            --GL.translate $ GL.Vector3 0 0 (-14::GLfloat)

            a <- readIORef aspect
            perspective 45.0 a 4 20000
            lookAt (Vertex3 (6000 - 100 * fromIntegral x) (6000 - 100 * fromIntegral y) (-3000) :: Vertex3 GLdouble) (Vertex3 100 100 0 :: Vertex3 GLdouble) (Vector3 0 1 0 :: Vector3 GLdouble)
            -- mark screen dirty
            writeIORef dirty True

        GLFW.mouseButtonCallback $= \b s ->
            -- when left mouse button is released, switch back to
            -- waitForPress action.
            when (b == GLFW.ButtonLeft && s == GLFW.Release) $
              waitForPress dirty

lineColor, faceColor :: Piece -> Color4 GLfloat
lineColor (Piece ((0,_,_),_)) = Color4 0.8 0.2 0.22 1
lineColor (Piece ((1,_,_),_)) = Color4 1 1 0.4 1
lineColor (Piece ((2,_,_),_)) = Color4 0.8 0.5 0.2 1
lineColor (Piece ((3,_,_),_)) = Color4 0.2 0.8 0.2 1
lineColor (Piece ((4,_,_),_)) = Color4 0.2 0.2 0.6 1
lineColor (Piece ((5,_,_),_)) = Color4 0.6 0.1 0.44 1
faceColor piece@(Piece ((c,_,_),_)) = (\(Color4 r g b a) -> Color4 r g b 0.68) $ lineColor piece

--transforms :: [ (Vertex3 GLfloat -> Vertex3 GLfloat) ]
transforms = [
    \(Vertex3 x y z) -> Vertex3 (1000-x) (1000-y) z,
    \(Vertex3 x y z) -> Vertex3 (1000-x) z (200-y),
    \(Vertex3 x y z) -> Vertex3 (1000-z) (1000-y) (x-800),
    \(Vertex3 x y z) -> Vertex3 z (1000-y) (200-x),
    \(Vertex3 x y z) -> Vertex3 (1000-x) (y) (-600-z),
    \(Vertex3 x y z) -> Vertex3 (1000-x) (1000-z) (y-800)
  ]

render chosenOne = do
  l <- readIORef chosenOne
  GL.clear [GL.ColorBuffer, GL.DepthBuffer]

  let soln = allColorPossibilities !! l
  let pcs = netPieces soln

  flip mapM_ (zip pcs transforms) $ \(piece,transform) -> do

    GL.color $ lineColor piece
    GL.renderPrimitive GL.Lines $ mapM_ GL.vertex $ map transform $ pieceToLines piece
    GL.color $ faceColor piece
    GL.renderPrimitive GL.Quads $ mapM_ GL.vertex $ map transform $ pieceToQuads piece


vertex3 :: GLfloat -> GLfloat -> GLfloat -> GL.Vertex3 GLfloat
vertex3 = GL.Vertex3


color3 :: GLfloat -> GLfloat -> GLfloat -> GL.Color3 GLfloat
color3 = GL.Color3
