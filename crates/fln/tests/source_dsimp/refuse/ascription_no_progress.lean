theorem bad (x : Nat) (h : (x : Nat) + 2 = 7) : (x : Nat) + 2 = 7 := by
  dsimp only
  exact h
