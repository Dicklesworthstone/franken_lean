def wrapped (n : Nat) : Nat := n + 1
theorem t1 : wrapped 3 = 3 + 1 := rfl
inductive Tree where
  | leaf : Tree
  | node : Tree -> Tree -> Tree
structure P where
  x : Nat
  y : Nat
def area (p : P) : Nat := p.x * p.y
