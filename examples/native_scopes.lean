namespace Collections
universe u

inductive Sequence (A : Type u) where
  | nil
  | cons (head : A) (tail : Sequence A)

def size {A : Type u} (xs : Sequence A) : Nat :=
  match xs with
  | Sequence.nil => 0
  | Sequence.cons x rest => size rest + 1

def sample : Sequence Nat := Sequence.cons 7 Sequence.nil
theorem length : size sample = 1 := by rfl
end Collections

section
open Collections
theorem outside : size sample = 1 := by rfl
end
