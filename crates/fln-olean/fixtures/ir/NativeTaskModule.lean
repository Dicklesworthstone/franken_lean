module

-- User callbacks compiled by the pinned Reference for imported-IR differentials.
-- Task primitives use native implementations; their Reference bodies are not run.
prelude
public import Init.Core

public section

@[noinline] def useTaskPure (make : Nat → Task Nat) (n : Nat) : Nat :=
  (make n).get

@[noinline] def useTaskGet (get : Task Nat → Nat) (n : Nat) : Nat :=
  let task := Task.pure n
  get task + get task

@[noinline] def useTaskSpawn
    (spawn : (Unit → Nat) → Task.Priority → Task Nat) (n : Nat) : Nat :=
  (spawn (fun _ => n + 1) 0).get

@[noinline] def useTaskMap
    (map : (Nat → Nat) → Task Nat → Task.Priority → Bool → Task Nat) (n : Nat) : Nat :=
  (map (fun x => x + 1) (Task.pure n) 0 true).get

@[noinline] def useTaskBind
    (bind : Task Nat → (Nat → Task Nat) → Task.Priority → Bool → Task Nat) (n : Nat) : Nat :=
  (bind (Task.pure n) (fun x => Task.pure (x + 2)) 0 false).get

@[noinline] def useTaskMapTail
    (map : Task Nat → Task.Priority → Bool → Task Nat) (n : Nat) : Nat :=
  let source := Task.pure n
  (map source 0 true).get + (map source 0 false).get

def taskPure (n : Nat) : Nat := useTaskPure Task.pure n
def taskGet (n : Nat) : Nat := useTaskGet Task.get n
def taskSpawn (n : Nat) : Nat := useTaskSpawn (@Task.spawn Nat) n
def taskMap (n : Nat) : Nat := useTaskMap (@Task.map Nat Nat) n
def taskBind (n : Nat) : Nat := useTaskBind (@Task.bind Nat Nat) n
def taskShared (n : Nat) : Nat := useTaskMapTail (@Task.map Nat Nat (fun x => x + 1)) n

def taskPipeline (n : Nat) : Nat :=
  let start := Task.spawn (fun _ => n) 0
  let mapped := Task.map (fun x => x + 1) start 0 false
  let bound := Task.bind mapped (fun x => Task.pure (x + 2)) 0 true
  bound.get + bound.get

@[noinline] def taskAdd (a b : Nat) : Nat := a + b

def taskCallable (n : Nat) : Nat :=
  let task := Task.map taskAdd (Task.pure n) 0 true
  let fn := task.get
  fn 1 + fn 2

def taskBoundCallable (n : Nat) : Nat :=
  let task := Task.bind (Task.pure n) (fun x => Task.pure (taskAdd x)) 0 true
  let fn := task.get
  fn 3 + fn 4

structure TaskHigh : Type 1 where
  value : Nat

def taskUniverses (n : Nat) : Nat :=
  let high := Task.pure (TaskHigh.mk n)
  let low := Task.map (fun x => x.value + 1) high 0 true
  let raised := Task.bind low (fun x => Task.pure (TaskHigh.mk (x + 2))) 0 true
  raised.get.value
