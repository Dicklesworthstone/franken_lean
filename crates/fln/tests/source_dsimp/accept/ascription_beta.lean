theorem kept (x : Nat) (h : x + 2 = 7) : ((fun y => y) x : Nat) + 2 = 7 := by
  dsimp only
  guard_target =ₛ x + 2 = 7
  exact h
