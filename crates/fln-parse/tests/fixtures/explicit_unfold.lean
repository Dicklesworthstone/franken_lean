namespace ExplicitUnfold

def selected (n : Nat) : Nat := n
def untouched (n : Nat) : Nat := n
def outer (n : Nat) : Nat := selected n
def Alias : Type := Nat

theorem selective (n : Nat) : selected (untouched n) = untouched n := by
  unfold selected
  guard_target =ₛ untouched n = untouched n
  rfl

theorem ordered (n : Nat) : outer n = n := by
  fail_if_success unfold selected outer
  unfold outer selected
  guard_target =ₛ n = n
  rfl

theorem locations (n m : Nat) (h : selected n = m) : selected n = m := by
  unfold selected at h ⊢
  guard_target =ₛ n = m
  exact h

theorem allLocations (n m : Nat) (unused : True) (h : selected n = m) : selected n = m := by
  unfold selected at *
  exact h

theorem localValue : True := by
  let x : Alias := Nat.zero
  unfold Alias at x
  have value : x = Nat.zero := by unfold x; rfl
  exact True.intro

theorem recover (n : Nat) : selected n = n := by
  fail_if_success unfold selected untouched
  guard_target =ₛ selected n = n
  unfold selected
  rfl

end ExplicitUnfold
