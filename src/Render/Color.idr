module Render.Color

import Data.Vect

%default total


public export
Color : Type
Color = Vect 3 Double

public export
ColorAlpha : Type
ColorAlpha = Vect 4 Double

export
withAlpha : Double -> Color -> ColorAlpha
withAlpha a [r,g,b] = [r,g,b,a]

export
toAlpha : Color -> ColorAlpha
toAlpha = withAlpha 1

