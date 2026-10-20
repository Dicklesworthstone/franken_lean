-- Shared verbatim inputs for native admission, installed CLI, and pinned Lean.
-- CASE nested_definitions accept
 def wrap (n : Nat) : Nat := n
 def twice (n : Nat) : Nat := wrap (wrap n)
 theorem t (P : Nat -> Prop) (h : P 7) : P (twice 7) := by
   dsimp only [twice, wrap]
   guard_target =ₛ P 7
   exact h
-- CASE beta accept
 theorem t (A : Type) (P : A -> Prop) (x : A) (h : P x) : P ((fun y : A => y) x) := by
   dsimp only []
   guard_target =ₛ P x
   exact h
-- CASE zeta accept
 theorem t (A : Type) (P : A -> Prop) (x : A) (h : P x) : P (let y := x; y) := by
   dsimp only []
   guard_target =ₛ P x
   exact h
-- CASE dependent_binders accept
 def wrap (A : Type) (x : A) : A := x
 theorem t (A : Type) (P : A -> Prop) (h : (x : A) -> P x) : (x : A) -> P (wrap A x) := by
   dsimp only [wrap]
   guard_target =ₛ ((x : A) -> P x)
   exact h
-- CASE data_hypothesis accept
 def Carrier (A : Type) : Type := A
 def t (A : Type) (x : Carrier A) : A := by
   dsimp only [Carrier] at x
   guard_hyp x :ₛ A
   exact x
-- CASE goal_domain accept
 def Carrier (A : Type) : Type := A
 def t (A : Type) : Carrier A -> A := by
   dsimp only [Carrier]
   guard_target =ₛ (A -> A)
   exact fun x => x
-- CASE local_shadow accept
 def value : Nat := 99
 theorem t (P : Nat -> Prop) (h : P 5) : P 5 := by
   let value : Nat := 5
   have found : P value := by
     dsimp only [value]
     guard_target =ₛ P 5
     exact h
   exact found
-- CASE wildcard_hypothesis accept
 def hide (P : Prop) : Prop := P
 theorem t (P : Prop) (h : hide P) : P := by
   dsimp only [hide] at *
   guard_hyp h :ₛ P
   exact h
-- CASE wildcard_dependent_exclusion accept
 def hide (P : Prop) : Prop := P
 theorem t (P : Prop) (h : hide P) (D : hide P -> Prop) (hd : D h) : D h := by
   fail_if_success dsimp only [hide] at *
   exact hd
-- CASE false_hypothesis_data_goal accept
 def impossible : Prop := False
 def t (A : Type) (h : impossible) : A := by
   dsimp only [impossible] at h
-- CASE close_true accept
 theorem t : True := by dsimp only []
-- CASE close_reflexive_equality accept
 theorem t (A : Type) (x : A) : x = x := by dsimp only []
-- CASE preserve_unselected_definition accept
 def wrap (n : Nat) : Nat := n
 theorem t (P : Nat -> Prop) (h : P (wrap 3)) : P (wrap 3) := by
   fail_if_success dsimp only []
   exact h
-- CASE preserve_irreducible_definition accept
 @[irreducible] def wrap (n : Nat) : Nat := n
 theorem t (P : Nat -> Prop) (h : P (wrap 3)) : P (wrap 3) := by
   fail_if_success dsimp only [wrap]
   exact h
-- CASE default_reflexive_rule accept
 @[implicit_reducible] def wrap (n : Nat) : Nat := n
 @[simp] theorem unwrapped (n : Nat) : wrap n = n := rfl
 theorem t (P : Nat -> Prop) (h : P 3) : P (wrap 3) := by
   dsimp
   guard_target =ₛ P 3
   exact h
-- CASE nonreflexive_rule_is_not_used accept
 theorem t (A : Type) (P : A -> Prop) (a b : A) (h : a = b) (hp : P a) : P a := by
   fail_if_success dsimp only [h]
   exact hp
-- CASE reflexive_rule_under_lambda accept
 @[implicit_reducible] def wrap (n : Nat) : Nat := n
 theorem unwrapped (n : Nat) : wrap n = n := rfl
 theorem t (P : (Nat -> Nat) -> Prop) (h : P (fun n => n)) : P (fun n => wrap n) := by
   dsimp only [unwrapped]
   guard_target =ₛ P (fun n => n)
   exact h
-- CASE default_transparency_is_not_defeq_eligibility accept
 def wrap (n : Nat) : Nat := n
 @[simp] theorem unwrapped (n : Nat) : wrap n = n := by rfl
 theorem t (P : Nat -> Prop) (h : P (wrap 3)) : P (wrap 3) := by
   fail_if_success dsimp only [unwrapped]
   exact h
-- CASE preserve_partial_application accept
 def wrap (n : Nat) : Nat := n
 theorem t (P : (Nat -> Nat) -> Prop) (h : P wrap) : P wrap := by
   fail_if_success dsimp only [wrap]
   exact h
-- CASE dependent_hypothesis_replacement accept
 def Carrier (A : Type) : Type := A
 theorem t (A : Type) (x : Carrier A) (P : Carrier A -> Prop) (h : P x) : P x := by
   dsimp only [Carrier] at x
   guard_hyp x :ₛ A
   exact h
-- CASE preserve_proof_terms accept
 theorem t (P : Prop) (h : P) (D : P -> Prop) (hd : D ((fun p : P => p) h)) : D ((fun p : P => p) h) := by
   fail_if_success dsimp only []
   exact hd
-- CASE projection accept
 structure Pair where
   first : Nat
   second : Nat
 theorem t (P : Nat -> Prop) (h : P 2) : P (Pair.first (Pair.mk 2 3)) := by
   dsimp only []
   guard_target =ₛ P 2
   exact h
-- CASE false_proof reject
 theorem bad : False := by dsimp only []
-- CASE arbitrary_equality_is_not_reflexivity reject
 theorem bad (A : Type) (a b : A) (h : a = b) : a = b := by dsimp only [h]
-- CASE unknown_selection reject
 theorem bad : True := by dsimp only [missingDefinition]
-- CASE unknown_location reject
 theorem bad : True := by dsimp only [] at missingHypothesis
