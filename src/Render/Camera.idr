module Render.Camera

import Data.Vect
import Data.NumIdr
import Render.Color

%default total

public export
record Camera where
  constructor MkCamera
  matrix : Rigid 2 Double

  scenew, sceneh : Double
  pixw, pixh : Nat



public export
PictureType : Camera -> Type
PictureType cam = Array [cam.pixh, cam.pixw, 3] Double


export
pointToPix : Camera -> Point 2 Double -> Point 2 Integer
pointToPix (MkCamera mat sw sh pw ph) p =
  let p' = applyInv mat p
  in  point [cast (p'.x / sw * cast pw), cast (p'.y / sh * cast ph)]
