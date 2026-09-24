class Shape (α : Type) where
  area : α → Nat
structure Sq where side : Nat
instance : Shape Sq where area s := s.side * s.side
def totalArea {α : Type} [Shape α] (xs : List α) : Nat := xs.foldl (fun acc s => acc + Shape.area s) 0
#eval totalArea [Sq.mk 2, Sq.mk 3]
