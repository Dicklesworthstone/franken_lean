structure P where
  x : Nat
  deriving Repr
#eval ({ x := 3 } : P)
