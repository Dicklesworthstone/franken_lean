@[simp] def wrap (A : Type) (x : A) : A := x
theorem erased (A : Type) (x : A) (P : A → Prop) (ready : P x) : P (wrap A x) := by
  fail_if_success dsimp [-wrap]
  guard_target =ₛ P (wrap A x)
  dsimp only [wrap]
  guard_target =ₛ P x
  exact ready
