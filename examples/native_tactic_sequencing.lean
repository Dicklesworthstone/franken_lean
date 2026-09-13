-- Every mapped tactic sees only the goals created by its left operand.
inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)

theorem duplicate (P : Prop) (p : P) : Both P P := by
  constructor <;> exact p

theorem four (P : Prop) (p : P) : Both (Both P P) (Both P P) := by
  constructor <;> constructor <;> exact p

theorem sibling (P Q : Prop) (p : P) (q : Q) : Both (Both P P) Q := by
  constructor
  constructor <;> exact p
  exact q

theorem quantified : Both (forall n : Nat, n = n) (forall b : Bool, b = b) := by
  constructor <;> (intro x; rfl)

theorem scoped_local (P : Prop) (p : P) : Both P P := by
  constructor <;> (have saved := p; exact saved)

structure Pair where
  first : Nat
  second : Nat

def shared : Pair := by
  refine Pair.mk ?same ?same <;> exact 17

theorem shared_ok : shared.first = 17 := by rfl

def copy (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copy k)

theorem copy_ok (n : Nat) : copy n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [copy, ih]

theorem copies (n : Nat) : Both (copy n = n) (copy n = n) := by
  constructor <;> exact copy_ok n
