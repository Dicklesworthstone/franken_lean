-- Shared source bytes for native admission and the pinned Reference. Each CASE follows this preamble.
def chooseValue (b : Bool) (x y : Nat) : Nat :=
  match b with
  | true => x
  | false => y
def copyNat : Nat → Nat
  | 0 => 0
  | n + 1 => copyNat n + 1
def plainValue (n : Nat) : Nat := n + 1
@[irreducible] def lockedChoice (b : Bool) (x y : Nat) : Nat :=
  match b with
  | true => x
  | false => y
def pairChoice (a b : Bool) (x y : Nat) : Nat :=
  match a, b with
  | true, true => x
  | true, false => y
  | false, _ => y
def nestedChoice (a b : Bool) (x y : Nat) : Nat :=
  match a with
  | true => match b with | true => x | false => y
  | false => y
def chooseType (b : Bool) (A B : Type) : Type :=
  match b with
  | true => A
  | false => B
def anyChoice (b : Bool) (x : Nat) : Nat := match b with | _ => x

-- CASE simp_bang accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  simp! only []
  guard_target =ₛ P x
  exact h
-- CASE dsimp_bang accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P y) : P (chooseValue false x y) := by
  dsimp! only []
  guard_target =ₛ P y
  exact h
-- CASE simpa_bang accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  simpa! only [] using h
-- CASE simp_all_bang accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) : P x := by
  simp_all! only []
-- CASE simp_explicit_config accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  simp +autoUnfold only []
  guard_target =ₛ P x
  exact h
-- CASE dsimp_explicit_config accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  dsimp (autoUnfold := true) only []
  guard_target =ₛ P x
  exact h
-- CASE simpa_explicit_config accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  simpa (config := { autoUnfold := true }) only [] using h
-- CASE config_disable_restores_default accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp +autoUnfold -autoUnfold only []
  exact h
-- CASE config_reset_restores_default accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp +autoUnfold (config := {}) only []
  exact h
-- CASE bang_overrides_negative_config accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  dsimp! -autoUnfold only []
  guard_target =ₛ P x
  exact h
-- CASE simpa_bang_overrides_reset accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  simpa! (config := { autoUnfold := false }) only [] using h
-- CASE stuck_discriminant accept
theorem t (P : Nat → Prop) (b : Bool) (x y : Nat) (h : P (chooseValue b x y)) :
    P (chooseValue b x y) := by
  fail_if_success dsimp! only []
  guard_target =ₛ P (chooseValue b x y)
  exact h
-- CASE ordinary_definition_stays_folded accept
theorem t (P : Nat → Prop) (x : Nat) (h : P (plainValue x)) : P (plainValue x) := by
  fail_if_success dsimp! only []
  exact h
-- CASE dsimp_explicit_ordinary_definition_stays_folded accept
theorem t (P : Nat → Prop) (x : Nat) (h : P (plainValue x)) : P (plainValue x) := by
  fail_if_success dsimp! only [plainValue]
  exact h
-- CASE simp_explicit_equation_still_rewrites accept
theorem t (P : Nat → Prop) (x : Nat) (h : P (x + 1)) : P (plainValue x) := by
  simp! only [plainValue]
  guard_target =ₛ P (x + 1)
  exact h
-- CASE erased_definition_stays_folded accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp! only [-chooseValue]
  exact h
-- CASE erasure_survives_later_definition_selection accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp! only [-chooseValue, chooseValue]
  exact h
-- CASE irreducible_definition_stays_folded accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (lockedChoice true x y)) :
    P (lockedChoice true x y) := by
  fail_if_success dsimp! only []
  exact h
-- CASE partial_application_stays_folded accept
theorem t (P : (Nat → Nat) → Prop) (x : Nat) (h : P (chooseValue true x)) :
    P (chooseValue true x) := by
  fail_if_success dsimp! only []
  exact h
-- CASE recursive_smart_unfolding accept
theorem t (P : Nat → Prop) (n : Nat) (h : P (copyNat n + 1)) : P (copyNat (n + 1)) := by
  dsimp! only []
  guard_target =ₛ P (copyNat n + 1)
  exact h
-- CASE recursive_stuck_major accept
theorem t (P : Nat → Prop) (n : Nat) (h : P (copyNat n)) : P (copyNat n) := by
  fail_if_success dsimp! only []
  exact h
-- CASE data_hypothesis accept
def t (A B : Type) (x : chooseType true A B) : A := by
  dsimp! only [] at x
  guard_hyp x :ₛ A
  exact x
-- CASE proof_hypothesis accept
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) : P x := by
  simp! only [] at h
  guard_hyp h :ₛ P x
  exact h
-- CASE several_discriminants_choose_branch accept
theorem t (P : Nat → Prop) (b : Bool) (x y : Nat) (h : P y) : P (pairChoice false b x y) := by
  dsimp! only []
  guard_target =ₛ P y
  exact h
-- CASE several_discriminants_stay_stuck accept
theorem t (P : Nat → Prop) (b : Bool) (x y : Nat) (h : P (pairChoice true b x y)) :
    P (pairChoice true b x y) := by
  fail_if_success dsimp! only []
  exact h
-- CASE nested_rhs_match_does_not_block_outer_branch accept
theorem t (P : Nat → Prop) (b : Bool) (x y : Nat) (h : P (chooseValue b x y)) :
    P (nestedChoice true b x y) := by
  dsimp! only []
  fail_if_success dsimp! only []
  exact h
-- CASE wildcard_only_match accept
theorem t (P : Nat → Prop) (b : Bool) (x : Nat) (h : P x) : P (anyChoice b x) := by
  dsimp! only []
  guard_target =ₛ P x
  exact h
-- CASE beneath_lambda accept
theorem t (P : (Nat → Nat) → Prop) (h : P (fun n => n)) :
    P (fun n => chooseValue true n 0) := by
  dsimp! only []
  guard_target =ₛ P (fun n => n)
  exact h
-- CASE false_equation_is_rejected reject
theorem t : chooseValue true 0 1 = 1 := by simp! only []
-- CASE wrong_using_evidence_is_rejected reject
theorem t (P : Nat → Prop) (x y : Nat) (h : P y) : P (chooseValue true x y) := by
  simpa! only [] using h
-- CASE successful_branch_cannot_be_reported_as_failure reject
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp! only []
  exact h
-- CASE erased_default_dsimp_definition accept
attribute [simp] chooseValue
attribute [-simp] chooseValue
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp!
  exact h
-- CASE erased_default_simp_definition accept
attribute [simp] chooseValue
attribute [-simp] chooseValue
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success simp!
  exact h
-- CASE only_ignores_default_erasure accept
attribute [simp] chooseValue
attribute [-simp] chooseValue
theorem t (P : Nat → Prop) (x y : Nat) (h : P x) : P (chooseValue true x y) := by
  dsimp! only []
  guard_target =ₛ P x
  exact h
-- CASE default_erasure_survives_readded_definition accept
attribute [simp] chooseValue
attribute [-simp] chooseValue
attribute [simp] chooseValue
theorem t (P : Nat → Prop) (x y : Nat) (h : P (chooseValue true x y)) :
    P (chooseValue true x y) := by
  fail_if_success dsimp!
  fail_if_success simp!
  exact h
