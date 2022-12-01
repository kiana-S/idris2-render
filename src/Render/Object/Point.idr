module Render.Object.Point

import Data.Vect
import Data.NumIdr
import Render.Color
import Render.Camera
import Render.Object.Interface

%default total


public export
record Point where
  constructor MkPoint
  pos : Point 2 Double
  color : ColorAlpha


export
IsObject Point where
  draw (MkPoint pos col) cam =
    let p = pointToPix cam pos
    in  [(p.x,p.y,col)]
