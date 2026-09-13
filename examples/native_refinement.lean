-- Explicit proof holes become scoped obligations, never assumptions.
inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)

inductive Witness (P : Nat -> Prop) : Prop where
  | intro (n : Nat) (proof : P n)

theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  refine Both.intro p ?_
  exact q

theorem witness : Witness (fun n => n = 7) := by
  refine Witness.intro ?value ?proof
  exact 7
  rfl

structure Package where
  carrier : Type
  value : carrier

def package : Package := by
  refine Package.mk ?type ?value
  exact Nat
  exact 7

theorem package_ok : package.value = 7 := by rfl

def identity : forall A : Type, A -> A := by
  refine fun A x => ?_
  exact x

theorem identity_ok : identity Nat 12 = 12 := by rfl

structure Functions where
  first : Nat -> Nat
  second : Nat -> Nat

def functions : Functions := by
  refine Functions.mk (fun x => ?_) (fun x => ?_)
  exact x + 1
  exact x + 2

theorem functions_ok : functions.first 7 + functions.second 7 = 17 := by rfl

theorem transported (A B : Type) (a : A) (b : B) (h : HEq a b)
    (P : forall T : Type, T -> Prop) (pa : P A a) : P B b := by
  refine ?_
  subst h
  exact pa

def copy (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copy k)

theorem induction_with_hole (n : Nat) : copy n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    refine ?_
    simp only [copy, ih]

def ignore (n : Nat) : 0 = 0 := rfl

theorem unused_is_still_provided : 0 = 0 := by
  refine ignore ?_
  exact 7
