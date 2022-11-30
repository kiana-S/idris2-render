module Render.Object.Point

import Data.Vect
import Render.Color
import Render.Camera
import Render.Picture
import Render.Object

%default total



public export
record Point where
  constructor MkPoint
  pos : (Double, Double)
  color : Color


Object' Point where
  draw (MkPoint pos col) cam =
    let (px,py) = pointToPix cam pos
    in  [(px,py,col)]
