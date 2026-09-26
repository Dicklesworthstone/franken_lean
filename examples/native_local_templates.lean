def applyBoth (f : Nat -> Nat -> Nat) (a b : Nat) : Nat := f a b

def run (delta : Nat) : Nat :=
  let keep (A : Type) (x : A) : A := x
  let stage (n : Nat) : Nat -> Nat :=
    let base : Nat := keep Nat (n + delta)
    fun (m : Nat) => base + m
  let alias : Nat -> Nat -> Nat := stage
  applyBoth alias 20 16

#eval run 6
