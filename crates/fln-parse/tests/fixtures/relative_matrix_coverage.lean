inductive Tag where | left | right

def code (t : Tag) (n : Nat) : Nat :=
  match t, n with
  | _, 0 => 10
  | .left, .succ k => k + 20
  | .right, .succ k => k + 30

theorem zero : code Tag.right 0 = 10 := by rfl
 theorem_placeholder