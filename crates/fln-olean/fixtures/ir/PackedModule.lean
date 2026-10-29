module

prelude
public import Init.Data.UInt.BasicAux
public import Init.Data.String.Bootstrap

public section

-- Generated with the Reference pinned in SUITE.lock (Lean v4.32.0).
-- Integer fields appear in source order, which differs from their physical
-- packing order. The String field exercises the object/scalar boundary.
set_option trace.compiler.ir.result true

structure PackedRecord where
  label : String
  narrow : UInt8
  count : USize
  middle : UInt32
  wide : UInt64
  small : UInt16

@[noinline] def packedMake (n : Nat) : PackedRecord :=
  { label := "λ🦀"
    narrow := UInt8.ofNat (n + 171)
    count := USize.ofNat (n + 9223372036854775831)
    middle := UInt32.ofNat (n + 3735928559)
    wide := UInt64.ofNat (n + 9223372036854775825)
    small := UInt16.ofNat (n + 48879) }

@[noinline] def packedRead (p : PackedRecord) : Nat :=
  String.Internal.length p.label + p.narrow.toNat + p.count.toNat + p.middle.toNat +
    p.wide.toNat + p.small.toNat

@[noinline] def packedApply (f : PackedRecord → Nat) (p : PackedRecord) : Nat := f p

@[noinline] def packedResult (n : Nat) : Nat := packedRead (packedMake n)

def packedAnswer : Nat := packedResult 0

def packedClosureAnswer : Nat := packedApply packedRead (packedMake 1)
