module

prelude
public import Init

public section

-- Encode both signs in a natural so the harness can compare unbounded results.
-- Every entry receives magnitudes rather than relying on a host Int carrier.
@[inline] def integerFromMagnitude (negative magnitude : Nat) : Int :=
  if negative == 0 then Int.ofNat magnitude else Int.neg (Int.ofNat magnitude)

@[inline] def integerEncoding (value : Int) : Nat :=
  let magnitude := Int.natAbs value
  if value < 0 then magnitude * 2 + 1 else magnitude * 2

-- Reuse each closure after its first call to exercise the captured object.
@[noinline, nospecialize] def useIntTransform (f : Int → Int) (n : Int) : Nat :=
  integerEncoding (f n) + 1024 * integerEncoding (f (n + 1))

@[noinline, nospecialize] def useIntMeasure (f : Int → Nat) (n : Int) : Nat :=
  f n + 1024 * f (n + 1)

@[noinline, nospecialize] def useNatIntTransform (f : Nat → Int) (n : Nat) : Nat :=
  integerEncoding (f n) + 1024 * integerEncoding (f (n + 1))

@[noinline, nospecialize] def useIntDecision {p : Int → Prop}
    (f : (n : Int) → Decidable (p n)) (n : Int) : Nat :=
  let first := match f n with | .isTrue _ => 1 | .isFalse _ => 0
  let second := match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0
  first + second

@[noinline] def intBoxedAdd (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.add (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedSub (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.sub (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedMul (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.mul (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedEDiv (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.ediv (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedEMod (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.emod (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedTDiv (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.tdiv (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedTMod (sa a sb b : Nat) : Nat :=
  useIntTransform (Int.tmod (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedNeg (sign magnitude : Nat) : Nat :=
  useIntTransform Int.neg (integerFromMagnitude sign magnitude)

@[noinline] def intBoxedNatAbs (sign magnitude : Nat) : Nat :=
  useIntMeasure Int.natAbs (integerFromMagnitude sign magnitude)

@[noinline] def intBoxedOfNat (magnitude : Nat) : Nat :=
  useNatIntTransform Int.ofNat magnitude

@[noinline] def intBoxedNegSucc (magnitude : Nat) : Nat :=
  useNatIntTransform Int.negSucc magnitude

@[noinline] def intBoxedDecEq (sa a sb b : Nat) : Nat :=
  useIntDecision (Int.decEq (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedDecLe (sa a sb b : Nat) : Nat :=
  useIntDecision (Int.decLe (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedDecLt (sa a sb b : Nat) : Nat :=
  useIntDecision (Int.decLt (integerFromMagnitude sa a)) (integerFromMagnitude sb b)

@[noinline] def intBoxedDecNonneg (sign magnitude : Nat) : Nat :=
  useIntDecision Int.decNonneg (integerFromMagnitude sign magnitude)
