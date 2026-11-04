module

prelude
public import Init

public section

-- These are compiler-produced user functions, run by Golem from their .ir.
@[noinline] def arrayNativeEmpty (n : Nat) : Nat :=
  let original : Array Nat := Array.emptyWithCapacity n
  let changed := original.push 42
  original.size + changed.size + changed[0]!

@[noinline, nospecialize] def useArrayEmpty (empty : Nat → Array Nat) (n : Nat) : Nat :=
  let original := empty n
  let second := empty (n + 1)
  let changed := original.push n
  original.size + second.size + changed.size + changed[0]!

@[noinline] def arrayPartialEmpty (n : Nat) : Nat :=
  useArrayEmpty (@Array.emptyWithCapacity Nat) n

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

-- Higher-order native array calls keep type/proof slots in the pin's generated
-- `_boxed` closures. The noinline consumers force real PAP/AP instructions.
@[noinline] def useArrayPush (push : Nat → Array Nat) (n : Nat) : Nat :=
  let first := push n
  let second := push (n + 1)
  first.size + second.size + first[2]! + second[2]!

@[noinline] def arrayPartialPush (n : Nat) : Nat :=
  useArrayPush (Array.push (Array.replicate 2 n)) n

@[noinline] def useArrayRead (a : Array Nat) (read : (i : Nat) → i < a.size → Nat)
    (h : 0 < a.size) : Nat :=
  read 0 h + read 0 h

@[noinline] def arrayPartialRead (n : Nat) : Nat :=
  let a := Array.replicate 2 n
  if h : 0 < a.size then useArrayRead a a.getInternal h else 0

@[noinline] def useArrayWrite (a : Array Nat)
    (write : (i : Nat) → Nat → i < a.size → Array Nat) (h : 0 < a.size) (n : Nat) : Nat :=
  let first := write 0 n h
  let second := write 0 (n + 1) h
  first[0]! + second[0]! + a[0]!

@[noinline] def arrayPartialWrite (n : Nat) : Nat :=
  let a := Array.replicate 2 n
  if h : 0 < a.size then useArrayWrite a (@Array.set Nat a) h (n + 1) else 0

@[noinline] def useByteArrayRead (a : ByteArray)
    (read : (i : Nat) → i < a.size → UInt8) (h : 0 < a.size) : Nat :=
  (read 0 h).toNat

@[noinline] def byteArrayPartialRead (n : Nat) : Nat :=
  let a := (ByteArray.emptyWithCapacity 1).push n.toUInt8
  if h : 0 < a.size then useByteArrayRead a (@ByteArray.get a) h else 0
