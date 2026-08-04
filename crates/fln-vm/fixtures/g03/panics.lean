def risky (n : Nat) : Nat :=
  if n = 0 then panic! "zero not allowed" else n * 2
#eval risky 21
#eval risky 0
