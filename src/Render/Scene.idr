module Render.Scene

import Data.DPair
import Data.Vect
import Data.IORef
import Data.Buffer
import System.File
import Data.NumIdr
import Render.Color
import Render.Camera
import Render.Object

%default total


public export
record Scene where
  constructor MkScene
  objects : List Object
  bgcolor : Color


export
render : (cam : Camera) -> Scene -> PictureType cam
render cam sc = joinAxes $ foldl drawObject (repeat _ sc.bgcolor) sc.objects
  where
    drawPixel : (Integer, Integer, ColorAlpha) -> Array [cam.pixh, cam.pixw] Color -> Array [cam.pixh, cam.pixw] Color
    drawPixel (x, y, col) arr = fromMaybe arr $ do
      x' <- integerToFin x _
      y' <- integerToFin y _
      pure $ indexUpdate [x',y'] (over col) arr

    drawObject : Array [cam.pixh, cam.pixw] Color -> Object -> Array [cam.pixh, cam.pixw] Color
    drawObject pic (MkObject obj) =
      let pixs = draw obj cam
      in  foldr drawPixel pic pixs


export
renderToPPM : HasIO io => (dest : String) -> Camera -> Scene -> io (Either FileError ())
renderToPPM dest cam sc = do
  let bufsize = cast cam.pixw * cast cam.pixh * 3
  Just buf <- newBuffer bufsize
    | Nothing => pure $ Right ()

  let pic = render cam sc
  ind <- newIORef 0
  for_ pic $ \x => do
        i <- readIORef ind
        setByte buf i (cast $ x * 255)
        modifyIORef ind (+1)


  _ <- if !(exists dest) then removeFile {io} dest else pure $ Right ()
  Right h <- openFile dest Append
    | Left err => pure $ Left err
  Right () <- fPutStrLn h "P6\n\{show cam.pixw} \{show cam.pixh}\n255"
    | Left err => pure $ Left err
  Right () <- writeBufferData h buf 0 bufsize
    | Left (err,_) => pure $ Left err
  pure $ Right ()
