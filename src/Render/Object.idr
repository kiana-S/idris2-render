module Render.Object

import Data.Vect
import Render.Camera
import Render.Color
import public Render.Object.Interface
import public Render.Object.Point

%default total

public export
data Object : Type where
  MkObject : IsObject obj => obj -> Object
