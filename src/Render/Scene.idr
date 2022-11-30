module Render.Scene

import Data.Vect
import Render.Color
import Render.Camera
import Render.Object

%default total


public export
record Scene where
  constructor MkScene
  objects : List Object
  bgcolor : Color


public export
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
