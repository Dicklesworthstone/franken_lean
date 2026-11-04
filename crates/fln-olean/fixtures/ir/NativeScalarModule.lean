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

@[noinline, nospecialize] def useUInt8Transform (f : UInt8 → UInt8) (n : UInt8) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt8Decision {p : UInt8 → Prop}
    (f : (n : UInt8) → Decidable (p n)) (n : UInt8) : Nat :=
  (match f n with | .isTrue _ => 1 | .isFalse _ => 0) +
  (match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0)
@[noinline, nospecialize] def useUInt8FromNat (f : Nat → UInt8) (n : Nat) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt8ToNat (f : UInt8 → Nat) (n : UInt8) : Nat :=
  f n + f (n + 1)
@[noinline] def uint8Boxed (operation a b : Nat) : Nat :=
  let x := UInt8.ofNat a
  let y := UInt8.ofNat b
  match operation with
  | 0 => useUInt8Transform (UInt8.add x) y
  | 1 => useUInt8Transform (UInt8.sub x) y
  | 2 => useUInt8Transform (UInt8.mul x) y
  | 3 => useUInt8Transform (UInt8.div x) y
  | 4 => useUInt8Transform (UInt8.mod x) y
  | 5 => useUInt8Transform (UInt8.land x) y
  | 6 => useUInt8Transform (UInt8.lor x) y
  | 7 => useUInt8Transform (UInt8.xor x) y
  | 8 => useUInt8Transform (UInt8.shiftLeft x) y
  | 9 => useUInt8Transform (UInt8.shiftRight x) y
  | 10 => useUInt8Transform UInt8.complement x
  | 11 => useUInt8Transform UInt8.neg x
  | 12 => useUInt8Transform UInt8.log2 x
  | 13 => useUInt8Decision (UInt8.decEq x) y
  | 14 => useUInt8Decision (UInt8.decLe x) y
  | 15 => useUInt8Decision (UInt8.decLt x) y
  | 16 => useUInt8FromNat UInt8.ofNat a
  | _ => useUInt8ToNat UInt8.toNat x

@[noinline, nospecialize] def useUInt16Transform (f : UInt16 → UInt16) (n : UInt16) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt16Decision {p : UInt16 → Prop}
    (f : (n : UInt16) → Decidable (p n)) (n : UInt16) : Nat :=
  (match f n with | .isTrue _ => 1 | .isFalse _ => 0) +
  (match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0)
@[noinline, nospecialize] def useUInt16FromNat (f : Nat → UInt16) (n : Nat) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt16ToNat (f : UInt16 → Nat) (n : UInt16) : Nat :=
  f n + f (n + 1)
@[noinline] def uint16Boxed (operation a b : Nat) : Nat :=
  let x := UInt16.ofNat a
  let y := UInt16.ofNat b
  match operation with
  | 0 => useUInt16Transform (UInt16.add x) y
  | 1 => useUInt16Transform (UInt16.sub x) y
  | 2 => useUInt16Transform (UInt16.mul x) y
  | 3 => useUInt16Transform (UInt16.div x) y
  | 4 => useUInt16Transform (UInt16.mod x) y
  | 5 => useUInt16Transform (UInt16.land x) y
  | 6 => useUInt16Transform (UInt16.lor x) y
  | 7 => useUInt16Transform (UInt16.xor x) y
  | 8 => useUInt16Transform (UInt16.shiftLeft x) y
  | 9 => useUInt16Transform (UInt16.shiftRight x) y
  | 10 => useUInt16Transform UInt16.complement x
  | 11 => useUInt16Transform UInt16.neg x
  | 12 => useUInt16Transform UInt16.log2 x
  | 13 => useUInt16Decision (UInt16.decEq x) y
  | 14 => useUInt16Decision (UInt16.decLe x) y
  | 15 => useUInt16Decision (UInt16.decLt x) y
  | 16 => useUInt16FromNat UInt16.ofNat a
  | _ => useUInt16ToNat UInt16.toNat x

@[noinline, nospecialize] def useUInt32Transform (f : UInt32 → UInt32) (n : UInt32) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt32Decision {p : UInt32 → Prop}
    (f : (n : UInt32) → Decidable (p n)) (n : UInt32) : Nat :=
  (match f n with | .isTrue _ => 1 | .isFalse _ => 0) +
  (match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0)
@[noinline, nospecialize] def useUInt32FromNat (f : Nat → UInt32) (n : Nat) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt32ToNat (f : UInt32 → Nat) (n : UInt32) : Nat :=
  f n + f (n + 1)
@[noinline] def uint32Boxed (operation a b : Nat) : Nat :=
  let x := UInt32.ofNat a
  let y := UInt32.ofNat b
  match operation with
  | 0 => useUInt32Transform (UInt32.add x) y
  | 1 => useUInt32Transform (UInt32.sub x) y
  | 2 => useUInt32Transform (UInt32.mul x) y
  | 3 => useUInt32Transform (UInt32.div x) y
  | 4 => useUInt32Transform (UInt32.mod x) y
  | 5 => useUInt32Transform (UInt32.land x) y
  | 6 => useUInt32Transform (UInt32.lor x) y
  | 7 => useUInt32Transform (UInt32.xor x) y
  | 8 => useUInt32Transform (UInt32.shiftLeft x) y
  | 9 => useUInt32Transform (UInt32.shiftRight x) y
  | 10 => useUInt32Transform UInt32.complement x
  | 11 => useUInt32Transform UInt32.neg x
  | 12 => useUInt32Transform UInt32.log2 x
  | 13 => useUInt32Decision (UInt32.decEq x) y
  | 14 => useUInt32Decision (UInt32.decLe x) y
  | 15 => useUInt32Decision (UInt32.decLt x) y
  | 16 => useUInt32FromNat UInt32.ofNat a
  | _ => useUInt32ToNat UInt32.toNat x

@[noinline, nospecialize] def useUInt64Transform (f : UInt64 → UInt64) (n : UInt64) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt64Decision {p : UInt64 → Prop}
    (f : (n : UInt64) → Decidable (p n)) (n : UInt64) : Nat :=
  (match f n with | .isTrue _ => 1 | .isFalse _ => 0) +
  (match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0)
@[noinline, nospecialize] def useUInt64FromNat (f : Nat → UInt64) (n : Nat) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUInt64ToNat (f : UInt64 → Nat) (n : UInt64) : Nat :=
  f n + f (n + 1)
@[noinline] def uint64Boxed (operation a b : Nat) : Nat :=
  let x := UInt64.ofNat a
  let y := UInt64.ofNat b
  match operation with
  | 0 => useUInt64Transform (UInt64.add x) y
  | 1 => useUInt64Transform (UInt64.sub x) y
  | 2 => useUInt64Transform (UInt64.mul x) y
  | 3 => useUInt64Transform (UInt64.div x) y
  | 4 => useUInt64Transform (UInt64.mod x) y
  | 5 => useUInt64Transform (UInt64.land x) y
  | 6 => useUInt64Transform (UInt64.lor x) y
  | 7 => useUInt64Transform (UInt64.xor x) y
  | 8 => useUInt64Transform (UInt64.shiftLeft x) y
  | 9 => useUInt64Transform (UInt64.shiftRight x) y
  | 10 => useUInt64Transform UInt64.complement x
  | 11 => useUInt64Transform UInt64.neg x
  | 12 => useUInt64Transform UInt64.log2 x
  | 13 => useUInt64Decision (UInt64.decEq x) y
  | 14 => useUInt64Decision (UInt64.decLe x) y
  | 15 => useUInt64Decision (UInt64.decLt x) y
  | 16 => useUInt64FromNat UInt64.ofNat a
  | _ => useUInt64ToNat UInt64.toNat x

@[noinline, nospecialize] def useUSizeTransform (f : USize → USize) (n : USize) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUSizeDecision {p : USize → Prop}
    (f : (n : USize) → Decidable (p n)) (n : USize) : Nat :=
  (match f n with | .isTrue _ => 1 | .isFalse _ => 0) +
  (match f (n + 1) with | .isTrue _ => 2 | .isFalse _ => 0)
@[noinline, nospecialize] def useUSizeFromNat (f : Nat → USize) (n : Nat) : Nat :=
  (f n).toNat + (f (n + 1)).toNat
@[noinline, nospecialize] def useUSizeToNat (f : USize → Nat) (n : USize) : Nat :=
  f n + f (n + 1)
@[noinline] def usizeBoxed (operation a b : Nat) : Nat :=
  let x := USize.ofNat a
  let y := USize.ofNat b
  match operation with
  | 0 => useUSizeTransform (USize.add x) y
  | 1 => useUSizeTransform (USize.sub x) y
  | 2 => useUSizeTransform (USize.mul x) y
  | 3 => useUSizeTransform (USize.div x) y
  | 4 => useUSizeTransform (USize.mod x) y
  | 5 => useUSizeTransform (USize.land x) y
  | 6 => useUSizeTransform (USize.lor x) y
  | 7 => useUSizeTransform (USize.xor x) y
  | 8 => useUSizeTransform (USize.shiftLeft x) y
  | 9 => useUSizeTransform (USize.shiftRight x) y
  | 10 => useUSizeTransform USize.complement x
  | 11 => useUSizeTransform USize.neg x
  | 12 => useUSizeTransform USize.log2 x
  | 13 => useUSizeDecision (USize.decEq x) y
  | 14 => useUSizeDecision (USize.decLe x) y
  | 15 => useUSizeDecision (USize.decLt x) y
  | 16 => useUSizeFromNat USize.ofNat a
  | _ => useUSizeToNat USize.toNat x
