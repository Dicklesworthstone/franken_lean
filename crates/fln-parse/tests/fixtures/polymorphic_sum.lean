-- Separate carrier universes must survive source inference and both checkers.
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α)
  | inr (val : β)

def mapSum (f : α -> γ) (g : β -> δ) (value : Sum α β) : Sum γ δ :=
  match value with
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr (g b)

def observe (value : Sum Nat Bool) : Nat := match value with
  | Sum.inl n => n + 1
  | Sum.inr b => if b then 2 else 3

theorem leftValue : observe (Sum.inl 4) = 5 := by rfl
theorem rightValue : observe (Sum.inr true) = 2 := by rfl

def higherLeft (A : Type) : Sum (Type) Nat := Sum.inl A
def higherRight (B : Type) : Sum Nat (Type) := Sum.inr B
