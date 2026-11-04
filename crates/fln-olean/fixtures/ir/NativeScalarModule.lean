module

prelude
public import Init

public section

-- These consumers retain native PAP/AP pairs instead of specializing them.
-- Each captured function is reused so its borrowed/consuming ABI matters.
@[noinline, nospecialize] def useNatTransform (f : Nat → Nat) (n : Nat) : Nat :=
  f n + f (n + 1)

@[noinline, nospecialize] def useNatPredicate (f : Nat → Bool) (n : Nat) : Nat :=
  (if f n then 1 else 0) + (if f (n + 1) then 2 else 0)

@[noinline, nospecialize] def useNatDecision {p : Nat → Prop}
    (f : (n : Nat) → Decidable (p n)) (n : Nat) : Nat :=
  let first := match f n with | .isTrue _ => 1 | .isFalse _ => 0
  let second := match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0
  first + second

@[noinline] def natBoxedAdd (a b : Nat) : Nat := useNatTransform (Nat.add a) b
@[noinline] def natBoxedSub (a b : Nat) : Nat := useNatTransform (Nat.sub a) b
@[noinline] def natBoxedMul (a b : Nat) : Nat := useNatTransform (Nat.mul a) b
@[noinline] def natBoxedDiv (a b : Nat) : Nat := useNatTransform (Nat.div a) b
@[noinline] def natBoxedMod (a b : Nat) : Nat := useNatTransform (Nat.mod a) b
@[noinline] def natBoxedPow (a b : Nat) : Nat := useNatTransform (Nat.pow a) b
@[noinline] def natBoxedPred (n : Nat) : Nat := useNatTransform Nat.pred n
@[noinline] def natBoxedBeq (a b : Nat) : Nat := useNatPredicate (Nat.beq a) b
@[noinline] def natBoxedBle (a b : Nat) : Nat := useNatPredicate (Nat.ble a) b
@[noinline] def natBoxedDecEq (a b : Nat) : Nat := useNatDecision (Nat.decEq a) b
@[noinline] def natBoxedDecLe (a b : Nat) : Nat := useNatDecision (Nat.decLe a) b
@[noinline] def natBoxedDecLt (a b : Nat) : Nat := useNatDecision (Nat.decLt a) b

@[noinline, nospecialize] def useStringTransform (f : String → String) (s : String) : Nat :=
  let first := f s
  let second := f (s ++ "!")
  first.length + second.utf8ByteSize + s.length

@[noinline, nospecialize] def useCharTransform (f : Char → String) (c : Char) : Nat :=
  let first := f c
  let second := f 'λ'
  first.length + second.utf8ByteSize

@[noinline, nospecialize] def useStringMeasure (f : String → Nat) (s : String) : Nat :=
  f s + f (s ++ "λ")

@[noinline, nospecialize] def useStringHash (f : String → UInt64) (s : String) : Nat :=
  (f s).toNat

@[noinline, nospecialize] def useStringDecision {p : String → Prop}
    (f : (s : String) → Decidable (p s)) (s : String) : Nat :=
  let first := match f s with | .isTrue _ => 1 | .isFalse _ => 0
  let second := match f (s ++ "!") with | .isTrue _ => 2 | .isFalse _ => 0
  first + second

@[noinline] def stringBoxedAppend (a b : String) : Nat :=
  useStringTransform (String.append a) b + a.utf8ByteSize

@[noinline] def stringBoxedPush (s : String) : Nat :=
  useCharTransform (String.push s) '🦀' + s.length

@[noinline] def stringBoxedLength (s : String) : Nat := useStringMeasure String.length s
@[noinline] def stringBoxedBytes (s : String) : Nat := useStringMeasure String.utf8ByteSize s
@[noinline] def stringBoxedHash (s : String) : Nat := useStringHash String.hash s
@[noinline] def stringBoxedEq (a b : String) : Nat := useStringDecision (String.decEq a) b
