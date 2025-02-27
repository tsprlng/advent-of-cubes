{-|
A version of the program that renders a 3D cube solution to a GL window, and lets you cycle through the solutions and rotate the cubes.
-}
import Control.Exception (assert)
import Graphics.Rendering.OpenGL as GL
import Graphics.UI.GLFW as GLFW
import Graphics.Rendering.OpenGL (($=))
import Data.IORef
import Control.Monad
import System.Environment (getArgs, getProgName)
--import System.Posix.Signals (installHandler, Handler (Catch), sigTERM)

import Data.Maybe (fromJust)
import qualified Data.Map as M
import Data.Map ((!))

import Pieces
import Solver (possibilities, allColorPossibilities, netPieces)
import qualified Cube

data DrawState = DrawState {
  aspect      :: IORef GLdouble  -- window aspect ratio (for squaring up viewport)
, chosenOne   :: IORef Int  -- index of solution being drawn
, drawLines   :: IORef Bool -- whether to draw lines!
, flappiness  :: IORef Cube.GLfloat  -- how flappy the cube is
, flappingIn  :: IORef Bool  -- is it getting less flappy?
, flappingOut :: IORef Bool  -- is it getting flappier?
}

v3c = \(x,y,z)-> Vertex3 (realToFrac x ::GLfloat) (realToFrac y) (realToFrac z)
c4c = \(r,g,b,a)-> Color4 (realToFrac r ::GLfloat) (realToFrac g) (realToFrac b) (realToFrac a)

lineColor = c4c . Cube.lineColor
faceColor = c4c . Cube.faceColor
sideColor = c4c . Cube.sideColor

main = do
  -- invoke either active or passive drawing loop depending on command line argument
  args <- getArgs
  prog <- getProgName
  case args of
    [] -> main' passive allColorPossibilities
    [n] -> main' passive (possibilities (allColors !! read n))
  --main' passive
--  case args of
--    ["active"]  -> putStrLn "Running in active mode" >> main' active
--    ["passive"] -> putStrLn "Running in passive mode" >> main' passive
--    _ -> putStrLn $ "USAGE: " ++ prog ++ " [active|passive]"

initTitle = "Cube 0 - World of Foam Cubes"

main' run possibilities = do
  assert <$> GLFW.init
  -- open window
  GLFW.windowHint $ GLFW.WindowHint'Samples (Just 4)
  GLFW.windowHint $ GLFW.WindowHint'AlphaBits (Just 8)
  GLFW.windowHint $ GLFW.WindowHint'DepthBits (Just 16)
  window <- fromJust <$> GLFW.createWindow 800 600 initTitle Nothing Nothing
  GLFW.makeContextCurrent $ Just window
  GL.shadeModel    $= GL.Smooth
  GL.depthFunc $= Just Less
  -- enable antialiasing
  GL.multisample $= GL.Enabled
  GL.lineSmooth $= GL.Enabled
  GL.blend      $= GL.Enabled
  GL.blendFunc  $= (GL.SrcAlpha, GL.OneMinusSrcAlpha)
  GL.lineWidth  $= 1.4
  GL.cullFace   $= Just GL.Back
  -- set the color to clear background
  GL.clearColor $= Color4 0 0 0 0

  drawState <- return DrawState
    `ap` (newIORef 1.0)
    `ap` (newIORef 0)
    `ap` (newIORef True)
    `ap` (newIORef 1.0)
    `ap` (newIORef False)
    `ap` (newIORef False)

  let resizeCallback = \ _ w h -> do
      GL.viewport   $= (GL.Position 0 0, GL.Size (fromIntegral w) (fromIntegral h))
      GL.matrixMode $= GL.Projection

      let a = (fromIntegral w / fromIntegral h)
      writeIORef (aspect drawState) a

      GL.loadIdentity
      perspective 45.0 a 4 20000
      let ang = fromIntegral 37 / 100.0
      lookAt (Vertex3 (3000 * sin ang) (14000 - 100 * fromIntegral 130) (3000 * cos ang) :: Vertex3 GLdouble) (Vertex3 0 0 0 :: Vertex3 GLdouble) (Vector3 0 1 0 :: Vector3 GLdouble)

  GLFW.setFramebufferSizeCallback window $ Just resizeCallback
  (w,h) <- getFramebufferSize window
  resizeCallback window w h  -- not automatically called on startup on MacOS

  -- run the main loop
  run window possibilities drawState
  -- finish up
  GLFW.setWindowShouldClose window True
  GLFW.terminate

passive window possibilities drawState = do 
  -- disable auto polling in swapBuffers
  --GLFW.disableSpecial GLFW.AutoPollEvent  -- TODO this was removed apparently?

  -- keep track of whether ESC has been pressed
  quit <- newIORef False
--  installHandler sigTERM (Catch $ writeIORef quit True) Nothing  -- TODO apparently not needed, pressing ^C twice works anyway?

  -- keep track of whether screen needs to be redrawn
  dirty <- newIORef True

  -- mark screen dirty in refresh callback which is often called
  -- when screen or part of screen comes into visibility.
  GLFW.setWindowRefreshCallback window $ Just $ \_ -> writeIORef dirty True

  -- use key callback to track whether ESC is pressed
  GLFW.setKeyCallback window $ Just $ \_ k scan s _ -> do
     keyname <- GLFW.getKeyName k scan

     when (keyname == (Just "h")) $ do
        writeIORef (flappingIn drawState) (s /= GLFW.KeyState'Released)
        writeIORef dirty True
     when (keyname == (Just "s")) $ do
        writeIORef (flappingOut drawState) (s /= GLFW.KeyState'Released)
        writeIORef dirty True
     when (keyname == (Just "l") && s == GLFW.KeyState'Pressed) $ do
        (drawLines drawState) $~! not
        writeIORef dirty True
     when (keyname == (Just "c") && s == GLFW.KeyState'Pressed) $ do
        which <- readIORef (chosenOne drawState)
        let next = if which + 1 == length possibilities then 0 else which + 1
        writeIORef (chosenOne drawState) next
        GLFW.setWindowTitle window $ "Cube " ++ show next ++ " - World of Foam Cubes"
        writeIORef dirty True
     when (keyname == (Just "q") && s == GLFW.KeyState'Pressed) $
        writeIORef quit True
     when (fromEnum k == fromEnum GLFW.Key'Escape && s == GLFW.KeyState'Pressed) $
        writeIORef quit True

  -- Terminate the program if the window is closed
  GLFW.setWindowCloseCallback window $ Just (\_ -> writeIORef quit True)

  -- by default start with waitForPress
  waitForPress dirty
  loop dirty quit
  where

    loop dirty quit = do
        GLFW.pollEvents
        d <- readIORef dirty
        unless d GLFW.waitEvents
        -- redraw screen if dirty
        d <- readIORef dirty

        when d $
          render possibilities drawState >> GLFW.swapBuffers window

        flappingIn <- readIORef (flappingIn drawState)
        flappingOut <- readIORef (flappingOut drawState)
        let shouldRepeat = (flappingIn || flappingOut)
        unless shouldRepeat $
          writeIORef dirty False
        -- check if we need to quit the loop
        q <- readIORef quit
        unless q $
          loop dirty quit

    waitForPress dirty =
      do
        GLFW.setCursorPosCallback window Nothing

        GLFW.setMouseButtonCallback window $ Just $ \_ b s _ ->
            when (b == GLFW.MouseButton'1 && s == GLFW.MouseButtonState'Pressed) $
              do
                -- when left mouse button is pressed, switch to waitForRelease action.
                (x, y) <- GLFW.getCursorPos window
                waitForRelease dirty

    waitForRelease dirty =
      do
        GLFW.setCursorPosCallback window $ Just $ \_ x y ->
          do

            GL.loadIdentity
            --GL.ortho 0 (realToFrac w) (realToFrac h) 0 (-1) 5
            --GL.frustum (-20) (600) (480) (-20) 4 4000
            --GL.rotate (0.02*fromIntegral x - 12) (GL.Vector3 0 1 0 :: GL.Vector3 GL.GLfloat)
            --GL.rotate (0.02*fromIntegral y - 12) (GL.Vector3 1 0 0 :: GL.Vector3 GL.GLfloat)
            --GL.translate $ GL.Vector3 0 0 (-14::GLfloat)

            a <- readIORef (aspect drawState)
            perspective 45.0 a 4 20000

            let ang = x / 100.0
            lookAt (Vertex3 (3000 * sin ang) (14000 - 100 * y) (3000 * cos ang) :: Vertex3 GLdouble) (Vertex3 0 0 0 :: Vertex3 GLdouble) (Vector3 0 1 0 :: Vector3 GLdouble)
            -- mark screen dirty
            writeIORef dirty True

        GLFW.setMouseButtonCallback window $ Just $ \_ b s _ ->
            -- when left mouse button is released, switch back to
            -- waitForPress action.
            when (b == GLFW.MouseButton'1 && s == GLFW.MouseButtonState'Released) $
              waitForPress dirty

render possibilities drawState = do
  l <- readIORef (chosenOne drawState)
  GL.clear [GL.ColorBuffer, GL.DepthBuffer]

  let soln = possibilities !! l
  let pcs = netPieces soln
  flappingIn <- readIORef $ flappingIn drawState
  flappingOut <- readIORef $ flappingOut drawState

  when flappingIn $
    modifyIORef (flappiness drawState) $ \f -> min 1 (f+0.008)
  when flappingOut $
    modifyIORef (flappiness drawState) $ \f -> max (-1) (f-0.008)

  flappiness <- (/2.0) . (+1.0) . sin . (/2.0) . (*3.14159) <$> readIORef (flappiness drawState)
  lines <- readIORef (drawLines drawState)

  when (flappingIn || flappingOut) $ GL.rotate (1.2::GLfloat) $ Vector3 0 1 0

  let (frontFace, backFace, sides) = (\(fF,_,_)->fF, \(_,bF,_)->bF, \(_,_,s)->s)
  forM_ [(backFace, faceColor), (sides, sideColor), (frontFace, faceColor)] $ \(quadFilter, colorer) -> do
    forM_ (zip pcs $ Cube.transforms flappiness) $ \(piece,transform) -> do
      when lines $ do
        GL.lineWidth $= 3.8
        GL.color $ lineColor piece
        GL.renderPrimitive GL.Lines $ mapM_ (GL.vertex . v3c) $ map transform $ Cube.pieceToLines piece
      GL.color $ colorer piece
      GL.renderPrimitive GL.Quads $ mapM_ (GL.vertex . v3c) $ map transform $ quadFilter $ Cube.pieceToQuads piece

  --GL.scale 0.1 0.1 (0.1 :: GLfloat)
  --GL.currentRasterPosition $= GL.Vertex4 100 100 0 1
  --GL.lighting $= GL.Disabled
  --GLFW.renderString GLFW.Fixed8x16 "Hello"
  --GL.lighting $= GL.Enabled
