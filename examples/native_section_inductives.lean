section
variable (A : Type u) (unused : String)
inductive Chain where
  | nil
  | cons (value : A) (tail : Chain)
end

def copy {A : Type u} (xs : Chain A) : Chain A := match xs with
  | .nil => Chain.nil
  | .cons x tail => Chain.cons x (copy tail)

theorem copy_ok {A : Type u} (xs : Chain A) : copy xs = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [copy, ih]
