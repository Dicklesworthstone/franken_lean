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

-- The same recursion can now be written as source self-calls on next y hy.
def foldRecursive (A : Type) (R : A -> A -> Prop) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
    (a : A) (h : Accessible A R a) : P a := match h with
  | .intro x next => step x (fun y hy => foldRecursive A R P step y (next y hy))

inductive Before : Bool -> Bool -> Prop where
  | edge : Before false true

def falseAcc : Accessible Bool Before false :=
  Accessible.intro false (fun y h => by cases h)

def smaller (y : Bool) (h : Before y true) : Accessible Bool Before y := by
  cases h with
  | edge => exact falseAcc

def trueAcc : Accessible Bool Before true := Accessible.intro true smaller

def stepBefore (x : Bool) (rec : forall y : Bool, Before y x -> Nat) : Nat := by
  cases x with
  | false => exact 5
  | true => exact rec false Before.edge + 1

theorem recursive_folded : foldRecursive Bool Before (fun x => Nat)
    stepBefore true trueAcc = 6 := by rfl

def follow (t : Branching) (route : Nat) : Nat := match t with
  | .leaf n => n
  | .node children => follow (children route) (route + 1)

theorem followed : follow (Branching.node (fun n =>
    Branching.node (fun k => Branching.leaf (n + k)))) 3 = 7 := by rfl

def erase (t : Branching) : Nat := match t with
  | .leaf n => 0
  | .node children => erase (children 3)

theorem erased (t : Branching) : erase t = 0 := by
  induction t with
  | leaf n => rfl
  | node children ih => simp only [erase, ih 3]
