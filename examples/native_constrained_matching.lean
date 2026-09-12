inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def head {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A := match xs with
  | .cons k x rest => x

def tail {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := match xs with
  | .cons k x rest => rest

def second (xs : Vec Nat 2) : Nat := match xs with
  | .cons k x rest => match rest with
    | .cons j y remaining => y

theorem head_ok : head 0 (Vec.cons 0 9 Vec.nil) = 9 := by rfl
theorem tail_ok : tail 0 (Vec.cons 0 9 Vec.nil) = Vec.nil := by rfl
theorem second_ok : second (Vec.cons 1 5 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl

inductive PairAt : Nat -> Nat -> Type where
  | mk (a b : Nat) : PairAt a b

def total (n : Nat) (x : PairAt n n) : Nat := match x with
  | .mk a b => a + b

theorem total_ok : total 7 (PairAt.mk 7 7) = 14 := by rfl

inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | intro (a : A) (v : P a) : Witness A P a v

def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := match w with
  | .intro a v => v

theorem extract_ok : extract (Witness.intro 7 true) = true := by rfl

inductive Choice : Nat -> Type where
  | absent : Choice 0
  | first (x : Nat) : Choice 1
  | second (x : Nat) : Choice 1

def keep (x : Choice 1) : Choice 1 := match x with
  | .first n => Choice.first n
  | rest => rest

theorem keep_ok : keep (Choice.second 9) = Choice.second 9 := by rfl

inductive Cell : Nat -> Type where
  | make (x : Nat) : Cell x

def readIndex (n : Nat) (cell : Cell n) : Nat := match cell with
  | .make x => let retained := n; retained

theorem cell_reconstructed (n : Nat) (cell : Cell n) : cell = Cell.make n := match cell with
  | .make x => (rfl : cell = Cell.make x)

theorem index_ok : readIndex 9 (Cell.make 9) = 9 := by rfl
