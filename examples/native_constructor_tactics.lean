inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)
inductive Either (P Q : Prop) : Prop where
  | left (proof : P)
  | right (proof : Q)

theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  constructor
  exact p
  exact q

theorem chooseRight (P Q : Prop) (q : Q) : Either P Q := by
  right
  exact q

inductive Witness (P : Nat -> Prop) : Prop where
  | intro (n : Nat) (proof : P n)

theorem seven : Witness (fun n => n = 7) := by
  constructor
  exact 7
  rfl

structure Package where
  carrier : Type
  value : carrier

def package : Package := by
  constructor
  exact Nat
  exact 7

theorem package_ok : package.value = 7 := by rfl

inductive At : Nat -> Type where
  | zero : At 0
  | one : At 1

def selected : At 1 := by constructor

theorem selected_ok : selected = At.one := by rfl
