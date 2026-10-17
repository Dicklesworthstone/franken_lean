partial def count (n : Nat) : Nat :=
  if n == 0 then 7 else count (n - 1)
