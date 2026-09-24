def safeDiv (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)
def f : Option Nat := do
  let x ← safeDiv 10 2
  let y ← safeDiv x 0
  return x + y
#eval f
