def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)

theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by
  exact h

theorem nested (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f (f x)) = x := by
  simp only [contract f, h]

theorem unfolded (f : Nat -> Nat) (x : Nat) (h : f x = x) : twice f (twice f x) = x := by
  simp only [twice, h]

theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by
  simp only [h]
  exact hy

theorem computed : 2 + 3 = 5 := by
  simp only []
