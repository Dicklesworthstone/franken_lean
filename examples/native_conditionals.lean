-- All branches remain checked; checking does not run the execution backend.
def choose {A : Type} (b : Bool) (yes no : A) : A := if b then yes else no

theorem choose_same (A : Type) (b : Bool) (x : A) : choose b x x = x := by
  cases b with
  | false => rfl
  | true => rfl

def classify (n : Nat) : Nat := if n == 3 then 17 else 19
theorem equal_input : classify 3 = 17 := by rfl
theorem other_input : classify 4 = 19 := by rfl

def count (n : Nat) (b : Bool) : Nat := match n with
  | .zero => 0
  | .succ k => if b then count k b + 1 else count k b + 2

theorem count_true : count 4 true = 4 := by rfl
theorem count_false : count 4 false = 8 := by rfl

def nested (a b : Bool) : Nat := if a then if b then 1 else 2 else 3
theorem nested_else : nested true false = 2 := by rfl

def localValue : Nat := by
  let n := if true then let x := 5; x + 2 else 9
  exact n
theorem local_ok : localValue = 7 := by rfl
