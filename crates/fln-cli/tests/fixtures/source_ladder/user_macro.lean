def double (n : Nat) : Nat := 2 * n
macro "dbl " x:term:max : term => `(double $x)
syntax "trip " term:max : term
macro_rules | `(trip $x) => `(double $x + $x)
#eval dbl 21
#eval trip 2
