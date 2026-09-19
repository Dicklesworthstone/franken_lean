-- Native collection data, computation, and universally quantified proofs.
-- Check with: fln check-source --json examples/native_collections.lean

def samples : List Nat := List.cons 5 (List.cons 2 List.nil)

theorem sample_length : List.length samples = 2 := by rfl
theorem sample_head : List.head? samples = Option.some 5 := by rfl
theorem reverse_head : Option.getD (List.head? (List.reverse samples)) 0 = 2 := by rfl
theorem left_fold : List.foldl Nat.sub 10 samples = 3 := by rfl
theorem right_fold : List.foldr Nat.sub 10 samples = 5 := by rfl

theorem mapped.{u,v} {A : Type u} {B : Type v} (f : A -> B) (a : A) (xs : List A) :
    List.map f (List.cons a xs) = List.cons (f a) (List.map f xs) := by rfl

theorem append_nil.{u} {A : Type u} (xs : List A) : List.append xs List.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [List.append]; rw [ih]

theorem map_identity.{u} {A : Type u} (xs : List A) : List.map (fun x => x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [List.map]; rw [ih]
