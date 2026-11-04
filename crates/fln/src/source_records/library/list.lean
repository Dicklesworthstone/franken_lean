-- The Bool coercions are ordinary checked instances, as in Init.Coe.
-- Spell out the common equality so constructing CoeSort needs no instance
-- that is still being defined.
instance boolToProp : Coe Bool Prop where
  coe b := b = true
instance boolToSort : CoeSort Bool Prop where
  coe b := b = true

universe u
namespace List
@[simp] theorem nil_append {α : Type u} (as : List α) : [] ++ as = as := rfl
@[simp] theorem cons_append {α : Type u} {a : α} {as bs : List α} : (a :: as) ++ bs = a :: (as ++ bs) := rfl
@[simp] theorem append_nil {α : Type u} (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [cons_append, ih]
@[simp] theorem append_assoc {α : Type u} (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [cons_append, ih]
end List
