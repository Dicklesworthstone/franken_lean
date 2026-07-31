-- With `partial` the same shape is ACCEPTED (and deliberately never evaluated).
partial def loops : Nat -> Nat
  | n => loops n
#eval "accepted without evaluating loops"
