structure NamedPair where
  first : Nat
  second : Nat

def namedTotal : NamedPair -> Nat := fun whole@⟨x, y⟩ =>
  let other@(NamedPair.mk a b) : NamedPair := whole
  other.first + b

def namedFirst : {A : Type} -> A -> A -> A :=
  fun {A} whole@_ (other : A) => whole

def namedInBranch (p : NamedPair) (n : Nat) : Nat :=
  match n with
  | .zero => let whole@⟨x, y⟩ := p; whole.first + y
  | .succ _ => 0

theorem totalValue : namedTotal ⟨7, 8⟩ = 15 := by rfl
theorem firstValue : namedFirst 7 8 = 7 := by rfl
theorem branchValue : namedInBranch ⟨40, 2⟩ 0 = 42 := by rfl
