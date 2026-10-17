partial def gcd' (a b : Nat) : Nat :=
  if b == 0 then a else gcd' b (a % b)
