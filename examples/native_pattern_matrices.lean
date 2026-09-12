-- The first matching row wins; every reachable row is checked.
def priority (a b : Bool) : Nat := match a, b with
  | true, _ => 1
  | _, true => 2
  | _, _ => 3

theorem first_row : priority true true = 1 := by rfl
theorem second_row : priority false true = 2 := by rfl
theorem fallback : priority false false = 3 := by rfl

inductive Maybe (A : Type) where
  | none
  | some (value : A)

def flatten (m : Maybe (Maybe Nat)) : Nat := match m with
  | .none => 0
  | .some .none => 1
  | .some (.some n) => n

theorem nested_value : flatten (Maybe.some (Maybe.some 23)) = 23 := by rfl
theorem nested_empty : flatten (Maybe.some Maybe.none) = 1 := by rfl

inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def second (xs : Vec Nat 2) : Nat := match xs with
  | .cons k x (.cons j y rest) => y

def sumHeads (n : Nat) (xs ys : Vec Nat n) : Nat := match xs, ys with
  | .nil, .nil => 0
  | .cons k x xt, .cons j y yt => x + y

theorem second_value : second (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl
theorem heads_value : sumHeads 1 (Vec.cons 0 3 Vec.nil) (Vec.cons 0 7 Vec.nil) = 10 := by rfl

def swapped (x y : Nat) : Nat := match x, y with | y, x => x
theorem hygienic : swapped 3 7 = 7 := by rfl
