module Render.Scene

import Data.Vect
import Render.Color
import Render.Camera
import Render.Object

%default total


public export
record Scene where
  constructor MkScene

  camera : Camera
  objects : List Object
  bgcolor : Vect 3 Bits8


public export
PictureType : Scene -> Type
PictureType sc = Vect sc.camera.pixh (Vect sc.camera.pixw (Vect 3 Bits8))



