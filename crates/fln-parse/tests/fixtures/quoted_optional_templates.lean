-- Bracketed optional bodies emit all their syntax only when every capture exists.
syntax "optionalOutput!" "[" ("value" term)? "]" : term
macro_rules
  | `(optionalOutput![]) => `((0 : Nat))
  | `(optionalOutput![value $x]) => `($x)

syntax "optionalInput!" "[" (term)? "]" : term
macro_rules
  | `(optionalInput![$(x)?]) => `(optionalOutput![$[value (Nat.succ $x)]?])

syntax "optionalPair!" "[" (term)? "]" "[" (term)? "]" : term
macro_rules
  | `(optionalPair![$(x)?][$(y)?]) => `(optionalOutput![$[value (Nat.add $x $y)]?])

macro "optionalDirect!" "[" x:(term)? "]" : term =>
  `(optionalOutput![$[value (Nat.succ $x)]?])

syntax "optionalShadow!" "[" (term)? "]" : term
macro_rules
  | `(optionalShadow![$(x)?]) => `(optionalOutput![$[value (let x := 99; $x)]?])

theorem absent : optionalInput![] = (0 : Nat) := rfl
theorem present : optionalInput![41] = (42 : Nat) := rfl
theorem bothPresent : optionalPair![19][23] = (42 : Nat) := rfl
theorem leftAbsent : optionalPair![][23] = (0 : Nat) := rfl
theorem rightAbsent : optionalPair![19][] = (0 : Nat) := rfl
theorem bothAbsent : optionalPair![][] = (0 : Nat) := rfl
theorem hygienic (x : Nat) : optionalPair![x][x] = Nat.add x x := rfl
theorem directPresent : optionalDirect![41] = (42 : Nat) := rfl
theorem directAbsent : optionalDirect![] = (0 : Nat) := rfl
theorem shadowed (x : Nat) : optionalShadow![x] = x := rfl
