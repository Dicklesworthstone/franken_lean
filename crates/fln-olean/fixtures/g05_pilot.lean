def wrapped (n : Nat) : Nat := n + 1
theorem t1 : wrapped 3 = 3 + 1 := rfl
inductive Tree where
  | leaf : Tree
  | node : Tree -> Tree -> Tree
structure P where
  x : Nat
  y : Nat
def area (p : P) : Nat := p.x * p.y
def big : Nat := 123456789012345678901234567890123456789
def uni : String := "héllo — ∀ε>0 ∃δ"
