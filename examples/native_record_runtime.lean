-- Native object fields survive helpers, updates, matching and recursion.
structure State where
  count : Nat
  label : String

def choose (flag : Bool) (left right : State) : State :=
  if flag then left else right

def walk (n : Nat) (p : State) : State := match n with
  | .zero => p
  | .succ k =>
    let bump (x : Nat) : Nat := x + n;
    walk k { p with count := bump p.count, label := p.label ++ "x" }

def score (p : State) : Nat := match p with
  | .mk count label => count + String.length label

theorem initialCount : (State.mk 7 "").count = 7 := by rfl

def answer : Nat := score (walk 7 (choose true { count := 7, label := "" } { count := 0, label := "" }))
-- Append `#eval answer` to execute: 42.
