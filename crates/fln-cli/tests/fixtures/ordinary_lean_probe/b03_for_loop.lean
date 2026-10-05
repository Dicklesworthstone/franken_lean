def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s
#eval sumTo 10
