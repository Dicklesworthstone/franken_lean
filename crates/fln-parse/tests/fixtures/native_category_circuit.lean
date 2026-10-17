
declare_syntax_cat circuit
syntax "on" : circuit
syntax "off" : circuit
syntax "box " "[" circuit "]" : circuit
macro_rules
  | `(circuit| on) => `((42 : Nat))
  | `(circuit| off) => `((0 : Nat))
  | `(circuit| box [$x:circuit]) => `(circuit| $x)
syntax "answerCircuit" : term
macro_rules | `(answerCircuit) => `(circuit| box [on])
