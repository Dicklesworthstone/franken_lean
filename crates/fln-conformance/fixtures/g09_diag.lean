set_option diagnostics true
set_option diagnostics.threshold 1
def wrapped (n : Nat) : Nat := n + 1
theorem byDelta : wrapped 3 = 3 + 1 := rfl
example (a : Nat) : id a = a := congrArg _ rfl
