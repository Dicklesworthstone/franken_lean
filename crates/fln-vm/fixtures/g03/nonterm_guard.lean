-- The guard IS the observable: without `partial`, a nonterminating def REFUSES.
def loops : Nat -> Nat
  | n => loops n
