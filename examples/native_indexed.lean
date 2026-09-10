inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def empty : Vec Nat 0 := Vec.nil
def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)
theorem two_ok : two = Vec.cons 1 7 (Vec.cons 0 9 Vec.nil) := by rfl

inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | intro (a : A) (value : P a) : Witness A P a value

def witness : Witness Nat (fun n => Bool) 7 true := Witness.intro 7 true
theorem witness_ok : witness = Witness.intro 7 true := by rfl

theorem reflexivity : forall x : Nat, x = x := by
  intro x
  rfl
