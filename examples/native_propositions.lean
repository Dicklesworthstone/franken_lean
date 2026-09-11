inductive Absurd : Prop where
inductive Truth : Prop where
  | intro

theorem truth : Truth := Truth.intro
def absurdElim (A : Type) (h : Absurd) : A := by cases h

inductive Both (P Q : Prop) : Prop where
  | intro (hp : P) (hq : Q)

theorem first (P Q : Prop) (h : Both P Q) : P := by
  cases h with
  | intro hp hq => exact hp

def proofConstant (P Q : Prop) (h : Both P Q) : Nat := match h with
  | .intro hp hq => 7

theorem constant_ok (P Q : Prop) (hp : P) (hq : Q) : proofConstant P Q (Both.intro hp hq) = 7 := by rfl

inductive EitherProof (P Q : Prop) : Prop where
  | left (h : P)
  | right (h : Q)

theorem swap (P Q : Prop) (h : EitherProof P Q) : EitherProof Q P := by
  cases h with
  | left hp => exact EitherProof.right hp
  | right hq => exact EitherProof.left hq

inductive HasWitness (A : Type) (P : A -> Prop) : Prop where
  | intro (a : A) (h : P a)

theorem transport (A : Type) (P Q : A -> Prop)
    (f : forall a : A, P a -> Q a) (h : HasWitness A P) : HasWitness A Q := by
  cases h with
  | intro a hp => exact HasWitness.intro a (f a hp)

inductive Below (a : Nat) : Nat -> Prop where
  | refl : Below a a
  | step (n : Nat) (h : Below a n) : Below a (Nat.succ n)

theorem sample : Below 2 4 := Below.step 3 (Below.step 2 Below.refl)
theorem transitive (a b : Nat) (hab : Below a b) (c : Nat) (hbc : Below b c) : Below a c := by
  induction hbc with
  | refl => exact hab
  | step n h ih => exact Below.step n ih
