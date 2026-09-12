inductive Walk : Nat -> Type where
  | done (n : Nat) : Walk n
  | step (n : Nat) (child : Walk n) : Walk n

def copyWalk (n : Nat) (w : Walk n) : Walk n := match w with
  | .done k => Walk.done k
  | .step k child => Walk.step k (copyWalk k child)

theorem copy_at_three (w : Walk 3) : copyWalk 3 w = w := by
  induction w with
  | done k => rfl
  | step k child ih => simp only [copyWalk, ih]

def zeroAcc (n : Nat) (w : Walk n) (acc : Nat) : Nat := match w with
  | .done k => 0
  | .step k child => zeroAcc k child (acc + 1)

theorem arbitrary_accumulator (w : Walk 3) (acc : Nat) : zeroAcc 3 w acc = 0 := by
  induction w generalizing acc with
  | done k => rfl
  | step k child ih => simp only [zeroAcc, ih]

inductive TreeAt (A : Type) : Nat -> Nat -> Type where
  | leaf (n : Nat) (value : A) : TreeAt A n n
  | fork (n : Nat) (left right : TreeAt A n n) : TreeAt A n n

def copyTree {A : Type} (n m : Nat) (t : TreeAt A n m) : TreeAt A n m := match t with
  | .leaf k value => TreeAt.leaf k value
  | .fork k left right => TreeAt.fork k (copyTree k k left) (copyTree k k right)

theorem two_children {A : Type} (n : Nat) (t : TreeAt A n n) : copyTree n n t = t := by
  induction t with
  | leaf k value => rfl
  | fork k left right ihl ihr => simp only [copyTree, ihl, ihr]

inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def copyVec {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := match xs with
  | .nil => Vec.nil
  | .cons k x rest => Vec.cons k x (copyVec k rest)

def nonemptyHead {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by
  induction xs with
  | cons k x rest ih => exact x

theorem head_value : nonemptyHead 0 (Vec.cons 0 7 Vec.nil) = 7 := by rfl

theorem nonempty_copy {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : copyVec (Nat.succ n) xs = xs := by
  induction xs generalizing n with
  | cons k x rest ih =>
    cases k with
    | zero =>
      cases rest with
      | nil => rfl
    | succ j => simp only [copyVec, ih j rest (HEq.refl (Nat.succ j)) (HEq.refl rest)]

theorem dependent_scope (w : Walk 3) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by
  induction w with
  | done k => exact hp
  | step k child ih => exact hp

inductive Diagonal : Nat -> Nat -> Type where
  | mk (n : Nat) : Diagonal n n

def impossible (d : Diagonal 0 1) : Nat := by induction d