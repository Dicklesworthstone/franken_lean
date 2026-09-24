example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp
