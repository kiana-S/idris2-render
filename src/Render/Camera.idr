module Render.Camera

import Data.Nat
import Render.Color

%default total

public export
record Camera where
  constructor MkCamera
  center : (Double, Double)
  scenew, sceneh : Double
  pixw, pixh : Nat


export
pointToPix : Camera -> (Double, Double) -> (Integer, Integer)
pointToPix (MkCamera (cx,cy) sw sh pw ph) (x,y) =
  let pw' = cast pw
      ph' = cast ph
  in (cast ((x - cx) / sw * pw' + pw' / 2),
      cast ((y - cy) / sh * ph' + ph' / 2))
