module Render.Object.Rectangle

import Data.Vect
import Render.Color
import Render.Camera
import Render.Object.Interface

%default total


public export
record Rectangle where
  constructor MkRect
  pos : (Double, Double)
  width, height : Double
  color : ColorAlpha


export
IsObject Rectangle where
  draw (MkRect pos w h col) cam =
    let (px,py) = pointToPix cam pos
        pw = cast (w / cam.scenew * cast cam.pixw)
        ph = cast (h / cam.sceneh * cast cam.pixh)
    in  (,,col) <$> [px..px+pw-1] <*> [py..py+ph-1]
