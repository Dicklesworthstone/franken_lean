def wrapped (n : Nat) : Nat := n + 1
set_option maxHeartbeats 400 in
theorem scoped_wins_over_cli : wrapped 400 + 0 = 401 := by simp [wrapped]
theorem unscoped_uses_cli : wrapped 400 + 1 = 402 := by simp [wrapped]
