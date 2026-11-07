module

prelude
public import Init

public section

-- User-class code only. The Reference supplies executable IR as an oracle;
-- Golem must execute every selected function using its own runtime.
inductive ResetChain where
  | nil
  | cons (head : Nat) (tail : ResetChain)

@[noinline] def resetMap (delta : Nat) : ResetChain → ResetChain
  | .nil => .nil
  | .cons x xs => .cons (x + delta) (resetMap delta xs)

@[noinline] def resetSum : ResetChain → Nat
  | .nil => 0
  | .cons x xs => x + resetSum xs

@[noinline] def resetHead (replacement : Nat) : ResetChain → ResetChain
  | .nil => .nil
  | .cons _ xs => .cons replacement xs

@[noinline] def resetApply (f : ResetChain → ResetChain) (xs : ResetChain) : ResetChain :=
  f xs

@[noinline] def resetAnswer (delta : Nat) : Nat :=
  resetSum (resetMap delta (.cons 19 (.cons 23 (.cons 7 .nil))))

@[noinline] def resetSharedAnswer (delta : Nat) : Nat :=
  let xs := ResetChain.cons 19 (.cons 23 (.cons 7 .nil))
  let ys := resetMap delta xs
  let zs := resetHead 42 xs
  resetSum ys + resetSum xs + resetSum zs

@[noinline] def resetClosureAnswer (delta : Nat) : Nat :=
  resetSum (resetApply (resetMap delta) (.cons 19 (.cons 23 .nil)))

@[noinline] def resetEmptyAnswer (delta : Nat) : Nat :=
  resetSum (resetMap delta .nil)

-- Multiple constructors retain a checked incoming layout at the case split.
-- The mixed payload forces the pin to initialize scalar fields in the reuse
-- continuation, instead of testing only object stores in allocation branches.
inductive PackedResetChain where
  | nil
  | cons (head : Nat) (wide : UInt64) (word : USize) (byte : UInt8) (tail : PackedResetChain)

@[noinline] def resetPackedMap (delta : Nat) : PackedResetChain → PackedResetChain
  | .nil => .nil
  | .cons head wide word byte tail =>
      .cons (head + delta) (wide + UInt64.ofNat delta)
        (word + USize.ofNat delta) (byte + UInt8.ofNat delta) (resetPackedMap delta tail)

@[noinline] def resetPackedSum : PackedResetChain → Nat
  | .nil => 0
  | .cons head wide word byte tail =>
      head + wide.toNat + word.toNat + byte.toNat + resetPackedSum tail

@[noinline] def resetPackedInput : PackedResetChain :=
  .cons 19 9223372036854775825 13 251 (.cons 23 18446744073709551615 7 255 .nil)

@[noinline] def resetPackedAnswer (delta : Nat) : Nat :=
  resetPackedSum (resetPackedMap delta resetPackedInput)

@[noinline] def resetPackedSharedAnswer (delta : Nat) : Nat :=
  let xs := resetPackedInput
  let ys := resetPackedMap delta xs
  resetPackedSum ys + resetPackedSum xs

-- A single-constructor structure has no case establishing its incoming
-- layout. These payloads fill whole words, so a checked allocation extent can
-- witness the reset/reuse layout without treating trailing padding as data.
structure ResetPackedRecord where
  count : Nat
  wide : UInt64
  word : USize
  floating : Float

@[noinline] def resetPackedRecordUpdate (delta : Nat) (input : ResetPackedRecord) :
    ResetPackedRecord :=
  { input with
    count := input.count + delta
    wide := input.wide + UInt64.ofNat delta
    word := input.word + USize.ofNat delta }

@[noinline] def resetPackedRecordRead (input : ResetPackedRecord) : Nat :=
  input.count + input.wide.toNat + input.word.toNat + input.floating.toBits.toNat

@[noinline] def resetPackedRecordInput : ResetPackedRecord :=
  { count := 19, wide := 9223372036854775825, word := 18446744073709551615,
    floating := Float.ofBits 0x7ff8123456789abc }

@[noinline] def resetPackedRecordApply
    (f : ResetPackedRecord → ResetPackedRecord) (input : ResetPackedRecord) : ResetPackedRecord :=
  f input

@[noinline] def resetPackedRecordAnswer (delta : Nat) : Nat :=
  resetPackedRecordRead (resetPackedRecordUpdate delta resetPackedRecordInput)

@[noinline] def resetPackedRecordSharedAnswer (delta : Nat) : Nat :=
  let input := resetPackedRecordInput
  let updated := resetPackedRecordApply (resetPackedRecordUpdate delta) input
  resetPackedRecordRead updated + resetPackedRecordRead input

-- Also retain heap constructors with no object fields and negative zero's
-- exact representation. A zero object-field count does not make this scalar.
structure ResetScalarRecord where
  wide : UInt64
  word : USize
  floating : Float

@[noinline] def resetScalarRecordUpdate (delta : Nat) (input : ResetScalarRecord) :
    ResetScalarRecord :=
  { input with
    wide := input.wide + UInt64.ofNat delta
    word := input.word + USize.ofNat delta }

@[noinline] def resetScalarRecordRead (input : ResetScalarRecord) : Nat :=
  input.wide.toNat + input.word.toNat + input.floating.toBits.toNat

@[noinline] def resetScalarRecordAnswer (delta : Nat) : Nat :=
  let input : ResetScalarRecord :=
    { wide := 18446744073709551615, word := 9223372036854775825,
      floating := Float.ofBits 0x8000000000000000 }
  let updated := resetScalarRecordUpdate delta input
  resetScalarRecordRead updated + resetScalarRecordRead input
