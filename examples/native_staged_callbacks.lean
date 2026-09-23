-- The prefix computes once, then the selected callback owns its captures.
inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def first {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A :=
  match xs with
  | .cons k x tail => x

def use (offset : Nat) : Nat :=
  let build : Nat -> Nat -> Nat := (by
    intro n
    let subtotal := n + offset
    exact fun k => subtotal + k)
  let callback := first 0 (Vec.cons 0 (build 1) Vec.nil)
  callback 1

#eval use 40
