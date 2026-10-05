structure Point where
  x : Nat
  y : Nat
def p : Point := ⟨1, 2⟩
#eval p.x + p.y
