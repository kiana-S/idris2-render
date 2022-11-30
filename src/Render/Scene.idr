module Render.Scene

import Data.DPair
import Data.Vect
import Data.IORef
import Data.Buffer
import System.File
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
render cam sc =
  let blank : PictureType cam = replicate _ (replicate _ sc.bgcolor)
  in  foldl drawObject blank sc.objects
  where
    drawPixel : (Integer, Integer, ColorAlpha) -> PictureType cam -> PictureType cam
    drawPixel (x, y, col) pic = fromMaybe pic $ do
      x' <- integerToFin x cam.pixw
      y' <- integerToFin y cam.pixh
      pure $ updateAt y' (updateAt x' (over col)) pic

    drawObject : PictureType cam -> Object -> PictureType cam
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
  for_ pic $ traverse_ $ \[r,g,b] => do
        i <- readIORef ind
        setByte buf (i)     (cast $ r * 255)
        setByte buf (i + 1) (cast $ g * 255)
        setByte buf (i + 2) (cast $ b * 255)
        modifyIORef ind (+3)


  _ <- if !(exists dest) then removeFile {io} dest else pure $ Right ()
  Right h <- openFile dest Append
    | Left err => pure $ Left err
  Right () <- fPutStrLn h "P6\n\{show cam.pixw} \{show cam.pixh}\n255"
    | Left err => pure $ Left err
  Right () <- writeBufferData h buf 0 bufsize
    | Left (err,_) => pure $ Left err
  pure $ Right ()
