module

prelude
public import Init

public section

-- Compile user code with the SUITE.lock Reference, then execute its binary
-- IR on Golem. No Reference runtime is used by the imported-IR executor.
@[noinline] def localStateAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← ST.mkRef (σ := σ) n
  r.set (n + 1)
  let old ← r.swap (n + 2)
  let current ← r.get
  return old + current

@[noinline] def localStateSharedAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← ST.mkRef (σ := σ) n
  let alias := r
  alias.set (n + 1)
  let current ← r.get
  return n + current

@[noinline] def localStateApply {σ : Type} (f : Nat → ST σ Nat) (n : Nat) : ST σ Nat :=
  f n

@[noinline] def localStateExchange {σ : Type} (r : ST.Ref σ Nat) (n : Nat) : ST σ Nat :=
  r.swap n

@[noinline] def localStateClosureAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← ST.mkRef (σ := σ) n
  let old ← localStateApply (localStateExchange r) (n + 1)
  let current ← r.get
  return old + current

@[noinline] def localStateArrayAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← ST.mkRef (σ := σ) (#[n] : Array Nat)
  let old ← r.swap #[n, n + 1]
  let current ← r.get
  return n + old.size + current.size

-- These public operations compile through the pin's take-based unsafe
-- implementation, not the logical get/set bodies. Both updates must run.
@[noinline] def localStateModifyAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← ST.mkRef (σ := σ) n
  r.modify fun value => value + 1
  let old ← r.modifyGet fun value => (value, value + 2)
  let current ← r.get
  return old + current

@[noinline] def localStateArrayModifyAnswer (n : Nat) : Nat := runST fun σ => do
  let original : Array Nat := #[n]
  let r ← ST.mkRef (σ := σ) original
  r.modify fun values => values.push (n + 1)
  let previous ← r.modifyGet fun values => (values.size, values.push (n + 2))
  let current ← r.get
  return n + original.size + previous + current.size

@[noinline] def localStateUpdateThrough {σ : Type}
    (r : ST.Ref σ Nat) (f : Nat → Nat) : ST σ Unit :=
  r.modify f

@[noinline] def localStateModifyClosureAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← ST.mkRef (σ := σ) n
  let update := localStateUpdateThrough r
  update fun value => value + n
  update fun value => value + 1
  r.get

-- Keep the primitive itself first class. These helpers deliberately prevent
-- specialization from replacing a primitive closure with a direct extern call.
@[noinline, nospecialize] def localStateRunAction {σ α : Type}
    (action : ST σ α) : ST σ α := action

@[noinline, nospecialize] def localStateUseAllocator {σ : Type}
    (allocate : Nat → ST σ (ST.Ref σ Nat)) (n : Nat) : ST σ (ST.Ref σ Nat) :=
  allocate n

@[noinline, nospecialize] def localStateUseSetter {σ : Type}
    (write : Nat → ST σ Unit) (first second : Nat) : ST σ Unit := do
  write first
  write second

@[noinline, nospecialize] def localStateUseSwap {σ : Type}
    (exchange : Nat → ST σ Nat) (first second : Nat) : ST σ Nat := do
  let old ← exchange first
  let next ← exchange second
  return old + next

@[noinline] def localStateBoxedAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← localStateUseAllocator (σ := σ) ST.Prim.mkRef n
  let read := ST.Prim.Ref.get r
  let before ← localStateRunAction read
  localStateUseSetter (ST.Prim.Ref.set r) (n + 1) (n + 2)
  let previous ← localStateUseSwap (ST.Prim.Ref.swap r) (n + 3) (n + 4)
  let current ← localStateRunAction read
  return before + previous + current

@[noinline] unsafe def localStateBoxedTakeAnswer (n : Nat) : Nat := runST fun σ => do
  let r ← localStateUseAllocator (σ := σ) ST.Prim.mkRef n
  let take := ST.Prim.Ref.take r
  let first ← localStateRunAction take
  localStateUseSetter (ST.Prim.Ref.set r) (n + 1) (n + 2)
  let second ← localStateRunAction take
  ST.Prim.Ref.set r (n + 3)
  let current ← localStateRunAction (ST.Prim.Ref.get r)
  return first + second + current
