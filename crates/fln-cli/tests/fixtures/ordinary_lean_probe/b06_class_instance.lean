class Shape (α : Type) where
  area : α → Nat
structure Sq where
  s : Nat
instance : Shape Sq where
  area q := q.s * q.s
#eval Shape.area (Sq.mk 3)
