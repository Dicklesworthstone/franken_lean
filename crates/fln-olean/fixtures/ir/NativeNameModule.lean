module

prelude
public import Init

public section

@[noinline] def nativeNamePart (n : Nat) : String :=
  if n == 0 then "A.B\x00🙂" else if n == 1 then "" else "λ"

@[noinline] def nativeNameDirect (n : Nat) : Lean.Name :=
  .str (.str .anonymous "Root") (nativeNamePart n)

@[noinline] def nativeNameTwo (n : Nat) : Lean.Name :=
  Lean.Name.mkStr2 "Parent" (nativeNamePart n)

@[noinline] def nativeNameFour (n : Nat) : Lean.Name :=
  Lean.Name.mkStr4 "Lean" "Parser" "Tactic" (nativeNamePart n)
