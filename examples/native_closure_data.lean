-- First-class functions stored in ground data use owned, typed runtime closures.
structure Handler (A : Type) where
  run : A -> A

def jobs : List (Handler Nat) :=
  [Handler.mk (Nat.add 10), Handler.mk (Nat.sub 52)]

def runJobs (initial : Nat) (handlers : List (Handler Nat)) : Nat :=
  List.foldl (fun (n : Nat) (h : Handler Nat) => h.run n) initial handlers

def prefixer (prefix : String) : Handler String :=
  { run := fun text => prefix ++ text }

def choose (b : Bool) : Nat -> Nat :=
  if b then (fun n => n + 2) else (fun n => n + 3)

theorem checked : List.length jobs = 2 := by rfl

#eval runJobs 0 jobs
#eval String.length ((prefixer "hello").run "abc") + 34
#eval choose false 39
