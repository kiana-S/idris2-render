module Render.Color

import Data.Vect
import Data.NumIdr

%default total


public export
Color : Type
Color = Vector 3 Double

public export
ColorAlpha : Type
ColorAlpha = (Vector 3 Double, Double)

export
toAlpha : Color -> ColorAlpha
toAlpha = (,1)


export
over : ColorAlpha -> Color -> Color
over (ca,a) cb = lerp a cb ca
