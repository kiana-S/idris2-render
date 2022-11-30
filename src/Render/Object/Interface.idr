module Render.Object.Interface

import Data.Vect
import Render.Color
import Render.Camera

%default total

public export
interface IsObject obj where
  draw : obj -> Camera -> List (Integer, Integer, ColorAlpha)
