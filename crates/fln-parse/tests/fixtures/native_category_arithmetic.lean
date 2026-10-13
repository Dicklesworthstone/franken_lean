
declare_syntax_cat arithmetic
syntax num : arithmetic
syntax "(" arithmetic ")" : arithmetic
syntax:60 arithmetic:60 "+" arithmetic:61 : arithmetic
syntax:70 arithmetic:70 "*" arithmetic:71 : arithmetic
syntax "arithEval " "[" arithmetic "]" : term
macro_rules
  | `(arithEval [$n:num]) => `($n)
  | `(arithEval [($x:arithmetic)]) => `(arithEval [$x])
  | `(arithEval [$a:arithmetic + $b:arithmetic]) => `(Nat.add (arithEval [$a]) (arithEval [$b]))
  | `(arithEval [$a:arithmetic * $b:arithmetic]) => `(Nat.mul (arithEval [$a]) (arithEval [$b]))
