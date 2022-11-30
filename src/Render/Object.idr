module Render.Object

import Data.Vect
import Render.Camera
import Render.Color

%default total


public export
interface Object' obj where
  draw : obj -> Camera -> List (Integer, Integer, Color)


export
data Object : Type where
  MkObject : Object' obj => obj -> Object
