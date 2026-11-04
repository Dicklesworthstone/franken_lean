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

-- Keep the list/native-array representation boundary visible in compiler IR.
-- The positional fingerprint observes every payload and the order of swaps.
@[noinline] def arrayListFingerprint : List Nat → Nat
  | [] => 0
  | n :: ns => n + 37 * arrayListFingerprint ns

@[noinline] def arrayFromList (xs : List Nat) : Array Nat := Array.mk xs
@[noinline] def arrayAsList (xs : Array Nat) : List Nat := xs.toList

@[noinline] def arrayNativeListRoundTrip (n : Nat) : Nat :=
  let source := [n, n + 1, n + 2]
  let original := arrayFromList source
  let changed := original.pop
  arrayListFingerprint source + 2 * arrayListFingerprint (arrayAsList original) +
    3 * arrayListFingerprint (arrayAsList changed)

@[noinline] def arrayNativePopEmpty (n : Nat) : Nat :=
  let original := Array.replicate n 7
  let changed := original.pop
  original.size + 10 * changed.size

@[noinline] def arrayNativeSwap (n : Nat) : Nat :=
  let original := arrayFromList [n, n + 1, n + 2]
  if hi : 0 < original.size then
    if hj : 2 < original.size then
      let changed := original.swap 0 2 hi hj
      arrayListFingerprint (arrayAsList original) +
        2 * arrayListFingerprint (arrayAsList changed)
    else 0
  else 0

@[noinline] def arrayNativeSwapIfInBounds (n : Nat) : Nat :=
  let original := arrayFromList [11, 23, 47]
  let changed := original.swapIfInBounds (n * n) 0
  arrayListFingerprint (arrayAsList original) +
    2 * arrayListFingerprint (arrayAsList changed)

@[noinline, nospecialize] def useArrayFromList (build : List Nat → Array Nat) (n : Nat) : Nat :=
  let first := build [n, n + 1]
  let second := build []
  arrayListFingerprint (arrayAsList first) + second.size

@[noinline] def arrayPartialFromList (n : Nat) : Nat :=
  useArrayFromList (@Array.mk Nat) n

@[noinline, nospecialize] def useArrayToList (convert : Array Nat → List Nat) (n : Nat) : Nat :=
  let original := arrayFromList [n, n + 1]
  let first := convert original
  let second := convert original
  arrayListFingerprint first + 2 * arrayListFingerprint second + original.size

@[noinline] def arrayPartialToList (n : Nat) : Nat :=
  useArrayToList (@Array.toList Nat) n

@[noinline, nospecialize] def useArrayPop (pop : Array Nat → Array Nat) (n : Nat) : Nat :=
  let original := arrayFromList [n, n + 1, n + 2]
  let first := pop original
  let second := pop original
  arrayListFingerprint (arrayAsList original) +
    2 * arrayListFingerprint (arrayAsList first) +
    3 * arrayListFingerprint (arrayAsList second)

@[noinline] def arrayPartialPop (n : Nat) : Nat :=
  useArrayPop (@Array.pop Nat) n

@[noinline, nospecialize] def useArraySwap (a : Array Nat)
    (swap : (i j : Nat) → i < a.size → j < a.size → Array Nat)
    (hi : 0 < a.size) (hj : 2 < a.size) : Nat :=
  let first := swap 0 2 hi hj
  let second := swap 2 0 hj hi
  arrayListFingerprint (arrayAsList a) +
    2 * arrayListFingerprint (arrayAsList first) +
    3 * arrayListFingerprint (arrayAsList second)

@[noinline] def arrayPartialSwap (n : Nat) : Nat :=
  let a := arrayFromList [n, n + 1, n + 2]
  if hi : 0 < a.size then
    if hj : 2 < a.size then useArraySwap a (@Array.swap Nat a) hi hj else 0
  else 0

-- This closure has captured every runtime operand while BOTH erased proofs
-- remain pending. They must be consumed before the native swap is invoked.
@[noinline, nospecialize] def useArraySwapProofs (a : Array Nat)
    (finish : 0 < a.size → 2 < a.size → Array Nat)
    (hi : 0 < a.size) (hj : 2 < a.size) : Nat :=
  let first := finish hi hj
  let second := finish hi hj
  arrayListFingerprint (arrayAsList a) +
    2 * arrayListFingerprint (arrayAsList first) +
    3 * arrayListFingerprint (arrayAsList second)

@[noinline] def arrayPartialSwapProofs (n : Nat) : Nat :=
  let a := arrayFromList [n, n + 1, n + 2]
  if hi : 0 < a.size then
    if hj : 2 < a.size then useArraySwapProofs a (@Array.swap Nat a 0 2) hi hj else 0
  else 0

@[noinline, nospecialize] def useArraySwapIfInBounds
    (swap : Nat → Nat → Array Nat) (n : Nat) : Nat :=
  let first := swap 0 2
  let second := swap (n * n) 0
  arrayListFingerprint (arrayAsList first) +
    2 * arrayListFingerprint (arrayAsList second)

@[noinline] def arrayPartialSwapIfInBounds (n : Nat) : Nat :=
  let a := arrayFromList [11, 23, 47]
  useArraySwapIfInBounds (a.swapIfInBounds) n + arrayListFingerprint (arrayAsList a)

@[noinline] def arrayNativeHeapSwap (n : Nat) : Nat :=
  letI : Inhabited (Array Nat) := ⟨#[]⟩
  let original : Array (Array Nat) := Array.mk [#[n], #[n + 1]]
  if hi : 0 < original.size then
    if hj : 1 < original.size then
      let changed := original.swap 0 1 hi hj
      let shorter := changed.pop
      original[0]![0]! + 2 * changed[0]![0]! + 3 * shorter[0]![0]!
    else 0
  else 0

-- Array.reverse and its loop come from the actual pinned library IR, with
-- their library-code classification authenticated by the complete partition.
@[noinline] def arrayLibraryReverse (n : Nat) : Nat :=
  let original := arrayFromList [n, n + 1, n + 2, n + 3]
  let changed := original.reverse
  arrayListFingerprint (arrayAsList original) +
    2 * arrayListFingerprint (arrayAsList changed)

@[noinline] def arrayLibraryReverseSmall (n : Nat) : Nat :=
  let original := Array.replicate n 7
  original.reverse.size
