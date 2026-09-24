structure Point where
  x : Nat
  y : Nat

instance : Add Point where
  add p q := ⟨p.x + q.x, p.y + q.y⟩

#eval ((⟨1, 2⟩ : Point) + ⟨3, 4⟩).x
