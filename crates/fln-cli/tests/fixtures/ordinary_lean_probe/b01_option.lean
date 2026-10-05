def safeDiv (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)
#eval safeDiv 10 2
