inductive Branching where
  | leaf (value : Nat)
  | node (children : Nat -> Branching)

def first (t : Branching) : Nat := match t with
  | .leaf value => value
  | .node children => match children 0 with
    | .leaf value => value
    | .node other => 99

theorem selected : first (Branching.node (fun n => Branching.leaf (n + 7))) = 7 := by rfl

theorem branching_induction (P : Branching -> Prop)
    (atLeaf : forall n : Nat, P (Branching.leaf n))
    (atNode : forall f : Nat -> Branching, (forall n : Nat, P (f n)) -> P (Branching.node f))
    (t : Branching) : P t := by
  induction t with
  | leaf n => exact atLeaf n
  | node f ih => exact atNode f ih

inductive Accessible (A : Type) (R : A -> A -> Prop) : A -> Prop where
  | intro (x : A) (next : forall y : A, R y x -> Accessible A R y) : Accessible A R x

def foldAccessible (A : Type) (R : A -> A -> Prop) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
    (a : A) (h : Accessible A R a) : P a := by
  induction h with
  | intro x next ih => exact step x ih

inductive NoEdge (x y : Nat) : Prop where

def accessible (a : Nat) : Accessible Nat NoEdge a :=
  Accessible.intro a (fun y h => by cases h)

theorem folded : foldAccessible Nat NoEdge (fun x => Nat)
    (fun x ih => x + 1) 7 (accessible 7) = 8 := by rfl
