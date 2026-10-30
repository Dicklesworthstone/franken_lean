module

prelude
public import Init.Data.Float
public import Init.Data.Float32
public import Init.Data.UInt.BasicAux

public section

-- Generated with the Reference pinned in SUITE.lock (Lean v4.32.0).
set_option trace.compiler.ir.result true

@[noinline] def float64Add (x y : Float) : Float := Float.add x y
@[noinline] def float32Add (x y : Float32) : Float32 := Float32.add x y
@[noinline] def float64Apply (f : Float → Float) (x : Float) : Float := f x
@[noinline] def float32Apply (f : Float32 → Float32) (x : Float32) : Float32 := f x

@[noinline] def float64Answer : Nat :=
  let x := Float.ofBits (UInt64.ofNat 4609434218613702656)
  let y := Float.ofBits (UInt64.ofNat 4612811918334230528)
  Float.toUInt64 (float64Apply (float64Add x) y) |>.toNat

@[noinline] def float32Answer : Nat :=
  let x := Float32.ofBits (UInt32.ofNat 1069547520)
  let y := Float32.ofBits (UInt32.ofNat 1075838976)
  Float32.toUInt32 (float32Apply (float32Add x) y) |>.toNat

structure FloatingRecord where
  narrow : Float32
  byte : UInt8
  wide : Float

@[noinline] def floatingMake (x : Float) (y : Float32) : FloatingRecord :=
  { narrow := y, byte := 7, wide := x }

@[noinline] def floatingRead (p : FloatingRecord) : Nat :=
  p.wide.toBits.toNat + p.narrow.toBits.toNat + p.byte.toNat

@[noinline] def floatingRecordAnswer : Nat :=
  floatingRead (floatingMake
    (Float.ofBits (UInt64.ofNat 9223372036854775808))
    (Float32.ofBits (UInt32.ofNat 2139095040)))

@[noinline] def floatingChoose (b : Bool) (x y : Float) : Float :=
  let z := if b then x else y
  float64Add z z

@[noinline] def floatingJoinAnswer : Nat :=
  Float.toUInt64 (floatingChoose true
    (Float.ofBits (UInt64.ofNat 4612811918334230528))
    (Float.ofBits (UInt64.ofNat 4615063718147915776))) |>.toNat
