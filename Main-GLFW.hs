import Graphics.Rendering.OpenGL as GL
import Graphics.UI.GLFW as GLFW
import Graphics.Rendering.OpenGL (($=))
import Data.IORef
import Control.Monad
import System.Environment (getArgs, getProgName)
--import System.Posix.Signals (installHandler, Handler (Catch), sigTERM)

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
    [n] -> main' passive (possibilities (read n))
  --main' passive
--  case args of
--    ["active"]  -> putStrLn "Running in active mode" >> main' active
--    ["passive"] -> putStrLn "Running in passive mode" >> main' passive
--    _ -> putStrLn $ "USAGE: " ++ prog ++ " [active|passive]"

main' run possibilities = do
  GLFW.initialize
  -- open window
  GLFW.openWindowHint FSAASamples 4
  GLFW.openWindow (GL.Size 800 600) [GLFW.DisplayAlphaBits 8, GLFW.DisplayDepthBits 16] GLFW.Window
  GLFW.windowTitle $= "Cube 0 - World of Foam Cubes"
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

  thing <- newIORef False
  drawState <- return DrawState
    `ap` (newIORef 1.0)
    `ap` (newIORef 0)
    `ap` (newIORef True)
    `ap` (newIORef 1.0)
    `ap` (newIORef False)
    `ap` (newIORef False)

  GLFW.windowSizeCallback $= \ size@(GL.Size w h) ->
    do
      GL.viewport   $= (GL.Position 0 0, size)
      GL.matrixMode $= GL.Projection

      let a = (fromIntegral w / fromIntegral h)
      writeIORef (aspect drawState) a

      GL.loadIdentity
      perspective 45.0 a 4 20000
      let ang = fromIntegral 37 / 100.0
      lookAt (Vertex3 (3000 * sin ang) (14000 - 100 * fromIntegral 130) (3000 * cos ang) :: Vertex3 GLdouble) (Vertex3 0 0 0 :: Vertex3 GLdouble) (Vector3 0 1 0 :: Vector3 GLdouble)

  -- run the main loop
  run possibilities drawState
  -- finish up
  GLFW.closeWindow
  GLFW.terminate

passive possibilities drawState = do 
  -- disable auto polling in swapBuffers
  GLFW.disableSpecial GLFW.AutoPollEvent

  -- keep track of whether ESC has been pressed
  quit <- newIORef False
--  installHandler sigTERM (Catch $ writeIORef quit True) Nothing  -- TODO apparently not needed, pressing ^C twice works anyway?

  -- keep track of whether screen needs to be redrawn
  dirty <- newIORef True

  -- mark screen dirty in refresh callback which is often called
  -- when screen or part of screen comes into visibility.
  GLFW.windowRefreshCallback $= writeIORef dirty True

  -- use key callback to track whether ESC is pressed
  GLFW.keyCallback $= \k s -> do
     when (k == (GLFW.CharKey 'H')) $ do
        writeIORef (flappingIn drawState) (s == GLFW.Press)
        writeIORef dirty True
     when (k == (GLFW.CharKey 'S')) $ do
        writeIORef (flappingOut drawState) (s == GLFW.Press)
        writeIORef dirty True
     when (k == (GLFW.CharKey 'L') && s == GLFW.Press) $ do
        (drawLines drawState) $~! not
        writeIORef dirty True
     when (k == (GLFW.CharKey 'C') && s == GLFW.Press) $ do
        which <- readIORef (chosenOne drawState)
        let next = if which + 1 == length possibilities then 0 else which + 1
        writeIORef (chosenOne drawState) next
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
        GLFW.pollEvents
        d <- readIORef dirty
        unless d GLFW.waitEvents
        -- redraw screen if dirty
        d <- readIORef dirty

        when d $
          render possibilities drawState >> GLFW.swapBuffers

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

            a <- readIORef (aspect drawState)
            perspective 45.0 a 4 20000

            let ang = fromIntegral x / 100.0
            lookAt (Vertex3 (3000 * sin ang) (14000 - 100 * fromIntegral y) (3000 * cos ang) :: Vertex3 GLdouble) (Vertex3 0 0 0 :: Vertex3 GLdouble) (Vector3 0 1 0 :: Vector3 GLdouble)
            -- mark screen dirty
            writeIORef dirty True

        GLFW.mouseButtonCallback $= \b s ->
            -- when left mouse button is released, switch back to
            -- waitForPress action.
            when (b == GLFW.ButtonLeft && s == GLFW.Release) $
              waitForPress dirty

render possibilities drawState = do
  l <- readIORef (chosenOne drawState)
  GL.clear [GL.ColorBuffer, GL.DepthBuffer]

  let soln = possibilities !! l
  let pcs = netPieces soln
  flappingIn <- readIORef $ flappingIn drawState
  flappingOut <- readIORef $ flappingOut drawState

  when flappingIn $
    modifyIORef (flappiness drawState) $ \f -> min 1 (f+0.02)
  when flappingOut $
    modifyIORef (flappiness drawState) $ \f -> max (-1) (f-0.02)

  flappiness <- (/2.0) . (+1.0) . sin . (/2.0) . (*3.14159) <$> readIORef (flappiness drawState)
  lines <- readIORef (drawLines drawState)

  when (flappingIn || flappingOut) $ GL.rotate (3.0::GLfloat) $ Vector3 0 1 0
  flip mapM_ (zip pcs $ Cube.transforms flappiness) $ \(piece,transform) -> do

    when lines $ do
      GL.color $ lineColor piece
      GL.renderPrimitive GL.Lines $ mapM_ (GL.vertex . v3c) $ map transform $ Cube.pieceToLines piece
    let (frontFace, backFace, sides) = Cube.pieceToQuads piece
    GL.color $ faceColor piece
    GL.renderPrimitive GL.Quads $ mapM_ (GL.vertex . v3c) $ map transform $ backFace

  flip mapM_ (zip pcs $ Cube.transforms flappiness) $ \(piece,transform) -> do

    when lines $ do
      GL.color $ lineColor piece
      GL.renderPrimitive GL.Lines $ mapM_ (GL.vertex . v3c) $ map transform $ Cube.pieceToLines piece
    let (frontFace, backFace, sides) = Cube.pieceToQuads piece
    GL.color $ sideColor piece
    GL.renderPrimitive GL.Quads $ mapM_ (GL.vertex . v3c) $ map transform $ sides

  flip mapM_ (zip pcs $ Cube.transforms flappiness) $ \(piece,transform) -> do

    when lines $ do
      GL.color $ lineColor piece
      GL.renderPrimitive GL.Lines $ mapM_ (GL.vertex . v3c) $ map transform $ Cube.pieceToLines piece
    let (frontFace, backFace, sides) = Cube.pieceToQuads piece
    GL.color $ faceColor piece
    GL.renderPrimitive GL.Quads $ mapM_ (GL.vertex . v3c) $ map transform $ frontFace

  --GL.scale 0.1 0.1 (0.1 :: GLfloat)
  --GL.currentRasterPosition $= GL.Vertex4 100 100 0 1
  --GL.lighting $= GL.Disabled
  --GLFW.renderString GLFW.Fixed8x16 "Hello"
  --GL.lighting $= GL.Enabled
