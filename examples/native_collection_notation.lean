-- Native list notation, structural recursion and polymorphic checked operations.
def sum (xs : List Nat) : Nat := match xs with
  | [] => 0
  | x :: rest => x + sum rest

def copy.{u} {A : Type u} (xs : List A) : List A := match xs with
  | [] => []
  | x :: rest => x :: copy rest

def samples : List Nat := [2, 3, 5,]

theorem total : sum samples = 10 := by rfl
theorem copied : copy samples = samples := by rfl
theorem mapped : List.map Nat.succ samples = [3, 4, 6] := by rfl
theorem reversed : List.reverse samples = [5, 3, 2] := by rfl
theorem folded : List.foldl (fun acc x => acc * 10 + x) 0 samples = 235 := by rfl
theorem first : Option.getD (List.head? samples) 99 = 2 := by rfl
theorem absent : Option.getD (List.head? ([] : List Nat)) 99 = 99 := by rfl

theorem polymorphic_map.{u,v} {A : Type u} {B : Type v}
    (f : A -> B) (x : A) (xs : List A) :
    List.map f (x :: xs) = f x :: List.map f xs := by rfl
