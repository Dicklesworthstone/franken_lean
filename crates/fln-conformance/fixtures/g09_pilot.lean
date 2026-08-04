-- G0-9 replay-rig pilot: small, deterministic, defeq-rich.
def wrapped (n : Nat) : Nat := n + 1
theorem byDelta : wrapped 3 = 3 + 1 := rfl
theorem byRefl (n : Nat) : n = n := rfl
example (a : Nat) : id a = a := congrArg _ rfl
