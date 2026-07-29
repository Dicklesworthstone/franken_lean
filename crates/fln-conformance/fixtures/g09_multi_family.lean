-- G0-9 multi-family pilot: one small file firing all five stock trace families.
macro "twice! " t:term : term => `($t + $t)
def wrapped (n : Nat) : Nat := n + 1
theorem byDelta : wrapped 3 = 3 + 1 := rfl
theorem bySimp (n : Nat) : n + 0 = n := by simp
example : (twice! 2) = 4 := rfl
example (a : Nat) : id a = a := congrArg _ rfl
