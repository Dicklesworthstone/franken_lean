-- Pattern lambdas are checked function values, including dependent signatures.
inductive Maybe (A : Type) where
  | none
  | some (value : A)

def map {A B : Type} (f : A -> B) : Maybe A -> Maybe B := fun
  | .none => Maybe.none
  | .some x => Maybe.some (f x)

def increment (n : Nat) : Nat := n + 1

theorem mapped : map increment (Maybe.some 8) = Maybe.some 9 := by rfl

def choose : Bool -> Bool -> Nat := fun
  | true, _ => 1
  | _, true => 2
  | _, _ => 3

theorem chosen : choose false true = 2 := by rfl

def identity : forall A : Type, A -> A := fun | A, value => value

theorem kept : identity Nat 11 = 11 := by rfl

structure Reader where
  run : Bool -> Nat

def reader : Reader := { run := fun | true => 7 | false => 9 }

theorem read_value : reader.run false = 9 := by rfl

theorem reflected : forall b : Bool, b = b := fun
  | true => by
    have h : true = true := rfl
    exact h
  | false => by rfl

def apply (f : Bool -> Nat) (b : Bool) : Nat := f b

theorem supplied : apply (fun | true => 17 | false => 19) true = 17 := by rfl
