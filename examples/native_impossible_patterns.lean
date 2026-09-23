-- Constructor indices prove that the omitted branches are impossible.
-- Neither a dummy head nor a representation-changing runtime cast is used.
inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def first {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A :=
  match xs with
  | .cons k x tail => x

inductive Choice : Bool -> Type where
  | yes (n : Nat) : Choice true
  | no (text : String) : Choice false

def selected (x : Choice true) : Nat :=
  match x with
  | .yes n => n

#eval first 0 (Vec.cons 0 40 Vec.nil) + selected (Choice.yes 2)
