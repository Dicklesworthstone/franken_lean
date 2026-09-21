-- Named equations are checked premises of recursor minors, not assumed facts.
def zeroBranch (n : Nat) (h : n = Nat.zero) : Nat := n

def succBranch (n k : Nat) (h : n = Nat.succ k) : Nat := k

def predecessor (n : Nat) : Nat :=
  match h : n with
  | Nat.zero => zeroBranch n h
  | Nat.succ k => succBranch n k h

theorem computes : predecessor 5 = 4 := by rfl

def classify (b : Bool) : Nat :=
  match h : b with
  | false => 0
  | true => 1

theorem classified : classify true = 1 := by rfl

theorem dependent (n : Nat) : n = n :=
  match h : n with
  | Nat.zero => rfl
  | Nat.succ k => rfl
