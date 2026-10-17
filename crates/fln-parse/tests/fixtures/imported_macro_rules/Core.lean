syntax (name := importedSyntax) "imported! " term:max : term
macro_rules | `(imported! $x) => `(Nat.add $x 1)
