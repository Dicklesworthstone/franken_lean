module

-- User code only: the imported task and cell primitives remain native.
prelude
public import Init.System.IO

public section

@[noinline] def useBaseIOAsTask
    (make : BaseIO Nat → Task.Priority → BaseIO (Task Nat)) (n : Nat) : BaseIO Nat := do
  let task ← make (pure (n + 1)) 0
  IO.wait task

@[noinline] def useBaseIOMapTask
    (map : (Nat → BaseIO Nat) → Task Nat → Task.Priority → Bool → BaseIO (Task Nat))
    (n : Nat) : BaseIO Nat := do
  let task ← map (fun x => pure (x + 2)) (Task.pure n) 0 true
  IO.wait task

@[noinline] def useBaseIOBindTask
    (bind : Task Nat → (Nat → BaseIO (Task Nat)) → Task.Priority → Bool → BaseIO (Task Nat))
    (n : Nat) : BaseIO Nat := do
  let task ← bind (Task.pure n) (fun x => pure (Task.pure (x + 3))) 0 false
  IO.wait task

@[noinline] def useBaseIOMapTail
    (map : Task Nat → Task.Priority → Bool → BaseIO (Task Nat)) (n : Nat) : BaseIO Nat := do
  let first ← map (Task.pure n) 0 true
  let second ← map (Task.pure (n + 1)) 0 false
  return (← IO.wait first) + (← IO.wait second)

def baseIOAsTask (n : Nat) : BaseIO Nat := useBaseIOAsTask (@BaseIO.asTask Nat) n
def baseIOMapTask (n : Nat) : BaseIO Nat := useBaseIOMapTask (@BaseIO.mapTask Nat Nat) n
def baseIOBindTask (n : Nat) : BaseIO Nat := useBaseIOBindTask (@BaseIO.bindTask Nat Nat) n
def baseIOShared (n : Nat) : BaseIO Nat :=
  useBaseIOMapTail (@BaseIO.mapTask Nat Nat (fun x => pure (x + 4))) n

def baseIOPipeline (n : Nat) : BaseIO Nat := do
  let ref ← IO.mkRef n
  let first ← BaseIO.asTask (do
    ref.set ((← ref.get) + 1)
    ref.get) 0
  let a ← IO.wait first
  let second ← BaseIO.mapTask (fun x => do
    ref.set ((← ref.get) + 10)
    pure (x + 2)) first 0 true
  let b ← IO.wait second
  let third ← BaseIO.bindTask second (fun x => do
    ref.set ((← ref.get) + 100)
    pure (Task.pure (x + 3))) 0 true
  let c ← IO.wait third
  return a + b + c + (← ref.get)

def baseIOObserve (n : Nat) : BaseIO Nat := do
  let first := Task.pure n
  let second := Task.pure (n + 10)
  let state ← IO.getTaskState first
  let ready ← IO.waitAny [first, second]
  match state with
  | .finished => return ready + (← IO.wait first)
  | _ => return 999

@[noinline] def baseIOAdd (a b : Nat) : Nat := a + b

def baseIOCallable (n : Nat) : BaseIO Nat := do
  let task ← BaseIO.asTask (pure (baseIOAdd n)) 0
  let f ← IO.wait task
  return f 1 + f 2

def baseIOBoundCallable (n : Nat) : BaseIO Nat := do
  let task ← BaseIO.bindTask (Task.pure n)
    (fun x => pure (Task.pure (baseIOAdd x))) 0 true
  let f ← IO.wait task
  return f 3 + f 4

structure BaseIOTaskHigh : Type 1 where
  value : Nat

def baseIOUniverses (n : Nat) : BaseIO Nat := do
  let high := Task.pure (BaseIOTaskHigh.mk n)
  let mapped ← BaseIO.mapTask (fun x => pure (x.value + 1)) high 0 true
  let bound ← BaseIO.bindTask high (fun x => pure (Task.pure (x.value + 2))) 0 true
  return (← IO.wait mapped) + (← IO.wait bound)

def baseIOExceptSuccess (n : Nat) : BaseIO Nat := do
  let task ← EIO.asTask (pure (n + 5) : EIO Nat Nat) 0
  match ← IO.wait task with
  | .ok value => pure value
  | .error value => pure (value + 100)

def baseIOExceptError (n : Nat) : BaseIO Nat := do
  let task ← EIO.asTask (throw n : EIO Nat Nat) 0
  match ← IO.wait task with
  | .ok value => pure (value + 100)
  | .error value => pure (value + 6)

def baseIOExceptMap (n : Nat) : BaseIO Nat := do
  let task ← EIO.mapTask (fun x => (throw (x + 7) : EIO Nat Nat)) (Task.pure n) 0 true
  match ← IO.wait task with
  | .ok value => pure (value + 100)
  | .error value => pure value

def baseIOExceptBind (n : Nat) : BaseIO Nat := do
  let task ← EIO.bindTask (Task.pure n)
    (fun x => (pure (Task.pure (.ok (x + 8))) : EIO Nat (Task (Except Nat Nat)))) 0 true
  match ← IO.wait task with
  | .ok value => pure value
  | .error value => pure (value + 100)

def baseIOIOSuccess (n : Nat) : BaseIO Nat := do
  let task ← IO.asTask (pure (n + 9)) 0
  match ← IO.wait task with
  | .ok value => pure value
  | .error _ => pure 999
