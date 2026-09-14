-- Each successful iteration commits; the final failing iteration does not.
inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)

theorem four (P : Prop) (p : P) : Both (Both P P) (Both P P) := by
  repeat (first | constructor | exact p)

theorem introduced (P : Prop) : P -> P -> P -> P := by
  repeat (intro first; intro second)
  intro last
  exact last

structure Package where
  carrier : Type
  value : carrier

def packed : Package := by
  refine Package.mk ?type ?value
  repeat (exact Nat; fail)
  exact String
  exact "preserved"

theorem packed_ok : packed.value = "preserved" := by rfl

def chosen : Nat := by
  repeat (exact 7; fail)
  exact 9

theorem chosen_ok : chosen = 9 := by rfl

theorem grouped (P Q : Prop) (p : P) (q : Q) : Both (Both P P) Q := by
  constructor
  repeat (constructor <;> exact p)
  exact q

theorem outer (P : Prop) : P -> P := by
  first
  | repeat intro discarded
    fail
  | intro kept
    exact kept

theorem shared (P : Prop) (p : P) : Both P P := by
  refine Both.intro ?same ?same
  repeat exact p

theorem local (n : Nat) : n = n := by
  have same : n = n := by
    repeat (first | fail | rfl)
  exact same
