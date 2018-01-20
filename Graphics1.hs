import Graphics.Rendering.OpenGL as GL
import Graphics.UI.GLFW as GLFW
import Graphics.Rendering.OpenGL (($=))
import Data.IORef
import Control.Monad
import System.Environment (getArgs, getProgName)

import qualified Data.Map as M
import Data.Map ((!))
import Pieces

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
    aa' x y = vertex3 (fromIntegral x *between) (fromIntegral y *between) (d+200)
    bb' x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between) (d+200)
    cc' x y = vertex3 (fromIntegral x *between+one) (fromIntegral y *between+one) (d+200)
    dd' x y = vertex3 (fromIntegral x *between) (fromIntegral y *between+one) (d+200)

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
  GLFW.openWindow (GL.Size 800 600) [GLFW.DisplayAlphaBits 8] GLFW.Window
  GLFW.windowTitle $= "World of Foam Cubes"
  GL.shadeModel    $= GL.Smooth
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
  -- keep all line strokes as a list of points in an IORef
  lines <- newIORef []
  -- run the main loop
  run lines
  -- finish up
  GLFW.closeWindow
  GLFW.terminate

passive lines = do
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
          render lines >> GLFW.swapBuffers

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
                -- when left mouse button is pressed, add the point
                -- to lines and switch to waitForRelease action.
                (GL.Position x y) <- GL.get GLFW.mousePos
                modifyIORef lines (((x,y):) . ((x,y):))
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

            perspective 45.0 1.0 4 8000
            lookAt (Vertex3 (3000 - 100 * fromIntegral x) 0 (-3000) :: Vertex3 GLdouble) (Vertex3 100 100 0 :: Vertex3 GLdouble) (Vector3 0 1 0 :: Vector3 GLdouble)
            -- update the line with new ending position
            modifyIORef lines (((x,y):) . tail)
            -- mark screen dirty
            writeIORef dirty True

        GLFW.mouseButtonCallback $= \b s ->
            -- when left mouse button is released, switch back to
            -- waitForPress action.
            when (b == GLFW.ButtonLeft && s == GLFW.Release) $
              waitForPress dirty


render lines = do
  l <- readIORef lines
  GL.clear [GL.ColorBuffer]
  GL.color $ (Color4 1 0 0.4 0.4 :: Color4 GLfloat)
 -- GL.renderPrimitive GL.Lines $ return [
 --     GL.vertex (vertex3 (-3000) (-3000) (-3000)), GL.vertex (vertex3 3000 3000 3000),
 --     GL.vertex (vertex3 (-3005) (-3005) (-3005)), GL.vertex (vertex3 3005 3005 3005)
 --   ]
  GL.renderPrimitive GL.Lines $ mapM_
    (\ (x, y) -> GL.vertex (vertex3 (fromIntegral x) (fromIntegral y) 1)) l
  GL.renderPrimitive GL.Quads $ mapM_ GL.vertex $ pieceToQuads $ head pieces


vertex3 :: GLfloat -> GLfloat -> GLfloat -> GL.Vertex3 GLfloat
vertex3 = GL.Vertex3


color3 :: GLfloat -> GLfloat -> GLfloat -> GL.Color3 GLfloat
color3 = GL.Color3
