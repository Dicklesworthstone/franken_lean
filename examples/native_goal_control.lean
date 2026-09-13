-- Scoped goal control retains the actual proof of every subgoal.
inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)

theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  constructor
  · exact p
  · exact q

theorem nested (P Q : Prop) (p : P) (q : Q) : Both (Both P Q) (Both Q P) := by
  constructor
  all_goals constructor
  · exact p
  · exact q
  · exact q
  · exact p

theorem quantified : Both (forall n : Nat, n = n) (forall b : Bool, b = b) := by
  constructor
  all_goals
    intro x
    rfl

theorem implication (P Q : Prop) (q : Q) : Both (P -> P) Q := by
  constructor
  focus intro p
  exact p
  exact q

structure Package where
  carrier : Type
  value : carrier

def packed : Package := by
  refine Package.mk ?_ ?_
  · exact Nat
  · exact 23

theorem packed_ok : packed.value = 23 := by rfl

theorem transported (n m : Nat) (h : n = m) (P : Nat -> Prop) (p : P n) : Both (P m) (P n) := by
  constructor
  · subst h
    exact p
  · exact p

def copy (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copy k)

theorem copy_ok (n : Nat) : copy n = n := by
  induction n with
  | zero => focus rfl
  | succ k ih =>
    · simp only [copy, ih]

theorem copied_twice (n : Nat) : Both (copy n = n) (copy n = n) := by
  have same : copy n = n := by exact copy_ok n
  constructor
  all_goals exact same
