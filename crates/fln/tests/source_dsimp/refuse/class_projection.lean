theorem bad (x y : Nat) (h : x + y = 13) : x + y = 13 := by
  dsimp only
  exact h
