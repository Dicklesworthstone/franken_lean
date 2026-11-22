syntax "bindfun " bracketedBinder " => " term : term
macro_rules
  | `(bindfun ($n:ident : $ty:term) => $body) => `(fun ($n : $ty) => $body)
def composed : Nat := (bindfun (n : Nat) => n) 42
theorem composed_ok : composed = 42 := rfl
#eval composed

syntax (name := sigProbe) "sigProbe " ident optDeclSig " complete" : command
macro_rules | `(sigProbe $id $sig complete) => `(def $id $sig := 17)
sigProbe fromSignature : Nat complete
theorem signature_ok : fromSignature = 17 := rfl
#eval fromSignature

syntax (name := sequenceProbe) "sequenceProbe " doSeq " finish" : term
macro_rules | `(sequenceProbe $seq finish) => `(Id.run do $seq)
def fromSequence : Nat := sequenceProbe
  pure 23
finish
theorem sequence_ok : fromSequence = 23 := rfl
#eval fromSequence
