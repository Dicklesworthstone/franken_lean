module

prelude
public import Init

public section

-- Compile user code with the SUITE.lock Reference, then execute its binary
-- IR on Golem. No Reference runtime is used by the imported-IR executor.
@[noinline] def localStateAnswer (n : Nat) : Nat := runST fun _ => do
  let r ← ST.mkRef n
  r.set (n + 1)
  let old ← r.swap (n + 2)
  let current ← r.get
  return old + current

@[noinline] def localStateSharedAnswer (n : Nat) : Nat := runST fun _ => do
  let r ← ST.mkRef n
  let alias := r
  alias.set (n + 1)
  let current ← r.get
  return n + current

@[noinline] def localStateApply {σ : Type} (f : Nat → ST σ Nat) (n : Nat) : ST σ Nat :=
  f n

@[noinline] def localStateExchange {σ : Type} (r : ST.Ref σ Nat) (n : Nat) : ST σ Nat :=
  r.swap n

@[noinline] def localStateClosureAnswer (n : Nat) : Nat := runST fun _ => do
  let r ← ST.mkRef n
  let old ← localStateApply (localStateExchange r) (n + 1)
  let current ← r.get
  return old + current

@[noinline] def localStateArrayAnswer (n : Nat) : Nat := runST fun _ => do
  let r ← ST.mkRef (#[n] : Array Nat)
  let old ← r.swap #[n, n + 1]
  let current ← r.get
  return n + old.size + current.size

-- These public operations compile through the pin's take-based unsafe
-- implementation, not the logical get/set bodies. Both updates must run.
@[noinline] def localStateModifyAnswer (n : Nat) : Nat := runST fun _ => do
  let r ← ST.mkRef n
  r.modify fun value => value + 1
  let old ← r.modifyGet fun value => (value, value + 2)
  let current ← r.get
  return old + current

@[noinline] def localStateArrayModifyAnswer (n : Nat) : Nat := runST fun _ => do
  let original : Array Nat := #[n]
  let r ← ST.mkRef original
  r.modify fun values => values.push (n + 1)
  let previous ← r.modifyGet fun values => (values.size, values.push (n + 2))
  let current ← r.get
  return n + original.size + previous + current.size

@[noinline] def localStateUpdateThrough {σ : Type}
    (r : ST.Ref σ Nat) (f : Nat → Nat) : ST σ Unit :=
  r.modify f

@[noinline] def localStateModifyClosureAnswer (n : Nat) : Nat := runST fun _ => do
  let r ← ST.mkRef n
  let update := localStateUpdateThrough r
  update fun value => value + n
  update fun value => value + 1
  r.get
