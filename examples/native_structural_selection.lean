-- Source-ordered candidate selection keeps function arguments in their original order.
def addRight : Nat -> Nat -> Nat
  | x, .zero => x
  | x, .succ k => Nat.succ (addRight x k)

theorem addRight_ok : addRight 4 7 = 11 := by rfl

def copyWithTag : Bool -> Nat -> Nat
  | tag, .zero => 0
  | tag, .succ k => Nat.succ (copyWithTag tag k)

theorem copyWithTag_identity (tag : Bool) (n : Nat) : copyWithTag tag n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [copyWithTag, ih]

def accumulate : Nat -> Nat -> Nat
  | acc, .zero => acc
  | acc, .succ k => accumulate (acc + 1) k

theorem accumulate_ok : accumulate 7 4 = 11 := by rfl

inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def copyTagged {A : Type} (tag : Bool) (n : Nat) (xs : Vec A n) : Vec A n := match tag, xs with
  | _, .nil => Vec.nil
  | b, .cons k x tail => Vec.cons k x (copyTagged b k tail)

theorem copyTagged_ok : copyTagged false 1 (Vec.cons 0 9 Vec.nil) = Vec.cons 0 9 Vec.nil := by rfl
