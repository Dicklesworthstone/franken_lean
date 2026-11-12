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

@[noinline] def nativeNameEqual (left right : String) : Nat :=
  if Lean.Name.beq (.str .anonymous left) (.str .anonymous right) then 11 else 29

-- Keep a real captured Name and reuse the boxed native predicate twice.
@[noinline, nospecialize] def nativeNameUsePredicate (f : Lean.Name → Bool)
    (right : String) : Nat :=
  (if f (.str .anonymous right) then 1 else 0) +
    (if f (.str .anonymous "fixed") then 2 else 0)

@[noinline] def nativeNamePartial (left right : String) : Nat :=
  nativeNameUsePredicate (Lean.Name.beq (.str .anonymous left)) right

@[noinline] def nativeNameShape (n : Nat) : Nat :=
  let left := if n == 0 then Lean.Name.str .anonymous "A.B"
    else .str (.str .anonymous "A") "B"
  if Lean.Name.beq left (.str .anonymous "A.B") then 11 else 29

@[noinline] def nativeNameNumeric (parent component : Nat) : Lean.Name :=
  .num (.num .anonymous parent) component

@[noinline] def nativeNameNumericFields (parent component : Nat) : Nat :=
  let value := nativeNameNumeric parent component
  if Lean.Name.beq value (nativeNameNumeric parent component) then
    match value with
    | .num (.num .anonymous previous) last => 17 * previous + last
    | _ => 9999999
  else 9999999

@[noinline] def nativeNameNumericEqual (parent left right : Nat) : Nat :=
  if Lean.Name.beq (nativeNameNumeric parent left) (nativeNameNumeric parent right)
  then 11 else 29
