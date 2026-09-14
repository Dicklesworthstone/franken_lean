-- Constructive conditions with checked branch evidence.
def inspect (p : Prop) [Decidable p] (yes : p -> Nat) (no : Not p -> Nat) : Nat :=
  if h : p then yes h else no h

theorem inspect_true : inspect True (fun h => 7) (fun h => 9) = 7 := by rfl
theorem inspect_false : inspect False (fun h => 7) (fun h => 9) = 9 := by rfl

theorem recover (p : Prop) [Decidable p] (hp : p) : p := by
  refine if evidence : p then ?_ else ?_
  · exact evidence
  · exact hp

def Carrier : Type := if Not True then String else Nat
def inhabitant : Carrier := 23
theorem inhabitant_ok : inhabitant = 23 := by rfl

def callback : Nat -> Nat := if True then fun n => n + 1 else fun n => n + 2
theorem callback_ok : callback 7 = 8 := by rfl

def count (n : Nat) (p : Prop) [Decidable p] : Nat := match n with
  | .zero => 0
  | .succ k => if h : p then count k p + 1 else count k p + 2

theorem count_true : count 3 True = 3 := by rfl
theorem count_false : count 3 False = 6 := by rfl