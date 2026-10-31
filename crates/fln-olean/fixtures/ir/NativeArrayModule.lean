module

prelude
public import Init

public section

-- These are compiler-produced user functions, run by Golem from their .ir.
@[noinline] def arrayNativeRoundTrip (n : Nat) : Nat :=
  let original := Array.replicate 3 n
  let changed := original.set! 1 (n + 7)
  original[1]! + changed[1]!

@[noinline] def arrayNativeSize (n : Nat) : Nat :=
  (Array.replicate n 7).usize.toNat

@[noinline] def arrayNativeHeap (n : Nat) : Nat :=
  -- Supply the heap default in user code so this fixture's only callees are
  -- its own functions and the reviewed native operations.
  letI : Inhabited (Array Nat) := ⟨#[]⟩
  let original := Array.replicate 2 (#[n] : Array Nat)
  let changed := original.set! 0 #[n + 1]
  original[0]![0]! + changed[0]![0]!

@[noinline] def byteArrayNativeRoundTrip (n : Nat) : Nat :=
  let original := (ByteArray.emptyWithCapacity 1).push n.toUInt8
  let changed := original.set! 0 (n + 1).toUInt8
  (original.get! 0).toNat + (changed.get! 0).toNat + changed.usize.toNat

@[noinline] def byteArrayNativeBounds (n : Nat) : Nat :=
  let original := (ByteArray.emptyWithCapacity 1).push 42
  let changed := original.set! n 7
  (changed.get! n).toNat

@[noinline] def byteArrayNativeHash (n : Nat) : Nat :=
  ((ByteArray.emptyWithCapacity 1).push n.toUInt8).hash.toNat

@[noinline] def arrayProofRoundTrip (n : Nat) : Nat :=
  let original := Array.replicate 2 n
  if h : 0 < original.size then
    let changed := original.set 0 (n + 7) h
    if h' : 0 < changed.size then
      original[0] + changed[0]
    else 0
  else 0

@[noinline] def arrayProofUSize (n : Nat) : Nat :=
  let original := Array.replicate 2 n
  let index : USize := 0
  if h : index.toNat < original.size then
    let changed := original.uset index (n + 7) h
    if h' : index.toNat < changed.size then
      original.uget index h + changed.uget index h'
    else 0
  else 0

@[noinline] def byteArrayProofRoundTrip (n : Nat) : Nat :=
  let original := (ByteArray.emptyWithCapacity 1).push n.toUInt8
  if h : 0 < original.size then
    let changed := original.set 0 (n + 1).toUInt8 h
    if h' : 0 < changed.size then
      (original.get 0 h).toNat + (changed.get 0 h').toNat
    else 0
  else 0

@[noinline] def byteArrayProofUSize (n : Nat) : Nat :=
  let original := (ByteArray.emptyWithCapacity 1).push n.toUInt8
  let index : USize := 0
  if h : index.toNat < original.size then
    let changed := original.uset index (n + 1).toUInt8 h
    if h' : index.toNat < changed.size then
      (original.uget index h).toNat + (changed.uget index h').toNat
    else 0
  else 0
