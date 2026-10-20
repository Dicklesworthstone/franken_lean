structure Pair where
  first : Nat
  second : Nat

theorem kept (x y : Nat) (h : x + y = 13) : (Pair.mk (x + y) 2).first = 13 := by
  dsimp only
  guard_target =ₛ x + y = 13
  exact h
