-- Decimal notation and arithmetic use the ordinary checked source-to-VM path.
def affine (x slope : Float) : Float := x * slope + 0.5
#eval affine 2.5 4.0
#eval (1.25e2 : Float32)
#eval Float.toString (2.1 : Float)
-- The typed boxes preserve the negative-zero sign bit across conversions.
#eval UInt64.toNat (Float.toBits (-0.0 : Float))
