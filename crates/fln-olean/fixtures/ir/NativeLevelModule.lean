module

prelude
public import Lean.Level

public section

-- Keep both direct native calls and captured boxed calls in the generated IR.
@[noinline, nospecialize] def useLevelData
    (f : Nat → Bool → Bool → Lean.Level.Data) (depth : Nat) : Nat :=
  (f depth false false).toNat + (f depth true false).toNat +
    (f depth false true).toNat + (f depth true true).toNat

@[noinline] def levelDataDirect (hash depth : Nat) : Nat :=
  (Lean.Level.mkData hash.toUInt64 depth true false).toNat

@[noinline] def levelDataCaptured (hash depth : Nat) : Nat :=
  useLevelData (@Lean.Level.mkData hash.toUInt64) depth

@[noinline] def levelValue (tag : Nat) : Lean.Level :=
  let u := Lean.Level.param .anonymous
  let v := Lean.Level.mvar ⟨.anonymous⟩
  match tag with
  | 0 => .zero
  | 1 => .succ .zero
  | 2 => u
  | 3 => v
  | 4 => .max u v
  | 5 => .max v u
  | 6 => .imax u v
  | 7 => .max .zero (.succ .zero)
  | _ => .succ u

@[noinline, nospecialize] def useLevelPredicate
    (f : Lean.Level → Bool) (first second : Lean.Level) : Nat :=
  (if f first then 1 else 0) + (if f second then 2 else 0)

@[noinline] def levelCompareDirect (a b : Nat) : Nat :=
  if Lean.Level.beq (levelValue a) (levelValue b) then 1 else 0

@[noinline] def levelCompareCaptured (a b : Nat) : Nat :=
  useLevelPredicate (Lean.Level.beq (levelValue a)) (levelValue b) (levelValue a)
