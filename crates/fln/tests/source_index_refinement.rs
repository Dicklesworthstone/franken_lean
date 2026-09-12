//! Fixed index elimination builds actual equality transports and contradictions.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";

#[test]
fn constrained_induction_quantifies_the_child_not_the_original_major() {
    check(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n\
        def copy (n : Nat) (w : Walk n) : Walk n := match w with | .done k => Walk.done k | .step k child => Walk.step k (copy k child)\n\
        theorem copied (w : Walk 3) : copy 3 w = w := by induction w with | done k => rfl | step k child ih => simp only [copy, ih]",
    );
}

#[test]
fn constrained_induction_prunes_only_proved_impossible_constructors() {
    check(&format!(
        "{VEC}\
        def head {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by induction xs with | cons k value tail ih => exact value\n\
        theorem checked : head 0 (Vec.cons 0 7 Vec.nil) = 7 := by rfl"
    ));
}

#[test]
fn repeated_index_induction_exposes_both_real_recursive_hypotheses() {
    check(
        "inductive TreeAt (A : Type) : Nat -> Nat -> Type where | leaf (n : Nat) (a : A) : TreeAt A n n | fork (n : Nat) (left right : TreeAt A n n) : TreeAt A n n\n\
        def copy {A : Type} (n m : Nat) (t : TreeAt A n m) : TreeAt A n m := match t with | .leaf k a => TreeAt.leaf k a | .fork k l r => TreeAt.fork k (copy k k l) (copy k k r)\n\
        theorem copied {A : Type} (n : Nat) (t : TreeAt A n n) : copy n n t = t := by induction t with | leaf k a => rfl | fork k l r ihl ihr => simp only [copy, ihl, ihr]",
    );
}

#[test]
fn constrained_induction_can_change_a_generalized_accumulator() {
    check(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n\
        def zero (n : Nat) (w : Walk n) (acc : Nat) : Nat := match w with | .done k => 0 | .step k child => zero k child (acc + 1)\n\
        theorem zeroed (w : Walk 3) (acc : Nat) : zero 3 w acc = 0 := by induction w generalizing acc with | done k => rfl | step k child ih => simp only [zero, ih]",
    );
}

#[test]
fn constrained_induction_generalizes_proof_dependent_hypotheses() {
    check(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n\
        theorem preserve (w : Walk 3) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by induction w with | done k => exact hp | step k child ih => exact hp\n\
        theorem introduced : forall w : Walk 3, w = w := by intro w; induction w with | done k => rfl | step k child ih => rfl",
    );
}

#[test]
fn constrained_induction_allows_indices_shared_with_family_parameters() {
    check(
        "inductive Anchored (base : Nat) : Nat -> Type where | stop : Anchored base base | step (child : Anchored base base) : Anchored base base\n\
        def copy (base index : Nat) (w : Anchored base index) : Anchored base index := match w with | .stop => Anchored.stop | .step child => Anchored.step (copy base base child)\n\
        theorem copied (base : Nat) (w : Anchored base base) : copy base base w = w := by induction w with | stop => rfl | step child ih => simp only [copy, ih]",
    );
}

#[test]
fn dependent_index_induction_keeps_each_index_in_its_own_domain() {
    check(
        "inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | stop (a : A) (v : P a) : Trace A P a v | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v\n\
        def copy {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with | .stop x vx => Trace.stop x vx | .step x vx child => Trace.step x vx (copy x vx child)\n\
        theorem copied (t : Trace Nat (fun x => Bool) 3 true) : copy 3 true t = t := by induction t with | stop a v => rfl | step a v child ih => simp only [copy, ih]",
    );
}

#[test]
fn induction_on_an_entirely_impossible_input_needs_no_alternatives() {
    check(
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
        def impossible (d : Diagonal 0 1) : Nat := by induction d",
    );
}

#[test]
fn constrained_induction_keeps_recursive_evidence_out_of_cases() {
    let prefix = "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n\
        def zero (n : Nat) (w : Walk n) : Nat := match w with | .done k => 0 | .step k child => zero k child\n";
    check(&format!(
        "{prefix}theorem good (w : Walk 3) : zero 3 w = 0 := by induction w with | done k => rfl | step k child ih => simp only [zero, ih]"
    ));
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    for statement in [
        "theorem bad (w : Walk 3) : zero 3 w = 0 := by cases w with | done k => rfl | step k child => assumption",
        "theorem bad (w : Walk 3) : 0 = 1 := by induction w with | done k => rfl | step k child ih => exact ih",
        "theorem bad (w : Walk 3) : zero 3 w = 0 := by induction w generalizing w with | done k => rfl | step k child ih => simp only [zero, ih]",
        "theorem bad (w : Walk 3) : w = w := by induction w with | done k => rfl | step k child ih => let unused := (child : Nat); rfl",
    ] {
        let source = format!("{prefix}{statement}");
        assert!(
            engine
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits)
                )
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn conditional_child_hypotheses_require_their_actual_index_evidence() {
    check(&format!("{VEC}\
        def copy {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := match xs with
          | .nil => Vec.nil
          | .cons k x tail => Vec.cons k x (copy k tail)
        theorem copied {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : copy (Nat.succ n) xs = xs := by
          induction xs generalizing n with
          | cons k x tail ih =>
            cases k with
            | zero =>
              cases tail with
              | nil => rfl
            | succ j => simp only [copy, ih j tail (HEq.refl (Nat.succ j)) (HEq.refl tail)]"));
    // The child of a length-one vector has length zero. A conditional IH at
    // length one cannot prove a false proposition just by naming that child.
    reject(&format!(
        "{VEC}\
        theorem bad (xs : Vec Nat 1) : 0 = 1 := by induction xs with
          | cons k x tail ih => exact ih tail (HEq.refl 0) (HEq.refl tail)"
    ));
}

#[test]
fn constrained_induction_keeps_local_aliases_and_pattern_name_shadowing() {
    check("inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n
        def copy (n : Nat) (w : Walk n) : Walk n := match w with | .done k => Walk.done k | .step k child => Walk.step k (copy k child)
        theorem let_major (w : Walk 3) : copy 3 w = w := let saved := w; let second := saved; by
          induction second with | done k => rfl | step k child ih => simp only [copy, ih]
        theorem let_context (w : Walk 3) : copy 3 w = w := let saved := copy 3 w; by
          induction w with | done k => rfl | step k child ih => simp only [copy, ih]
        theorem shadows (w : Walk 3) : copy 3 w = w := by
          induction w with | done w => rfl | step w child ih => simp only [copy, ih]");
    reject("inductive Walk : Nat -> Type where | done (n : Nat) : Walk n
        theorem bad (w : Walk 3) : w = w := let saved := (w : String); by induction w with | done k => rfl");
}

#[test]
fn selected_induction_companions_follow_scope_transport_but_not_shadowing() {
    let prefix = "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n\
        def copy (n : Nat) (w : Walk n) : Walk n := match w with | .done k => Walk.done k | .step k child => Walk.step k (copy k child)\n";
    check(&format!(
        "{prefix}\
        theorem nested (w : Walk 3) : copy 3 w = w := by induction w with
          | done k => rfl
          | step k child ih =>
            cases child with
            | done j => rfl
            | step j grandchild => simp only [copy, ih]"
    ));
    reject(&format!(
        "{prefix}theorem bad (w : Walk 3) : copy 3 w = w := by induction w with | done k => rfl | step k child ih => simp only [copy]"
    ));
    reject(&format!(
        "{prefix}theorem bad (w : Walk 3) : forall ignored : Nat, copy 3 w = w := by induction w with | done k => intro ih; rfl | step k child ih => intro ih; simp only [copy, ih]"
    ));
}

#[test]
fn checked_proof_lets_are_rules_only_when_explicitly_selected() {
    check("theorem forward (x y : Nat) (h : x = y) : x = y := let selected : x = y := h; by simp only [selected]
        theorem reverse (x y : Nat) (h : x = y) : y = x := let selected : x = y := h; by simp only [selected]
        theorem function_rule (f : Nat -> Nat) (h : forall n : Nat, f n = n) (n : Nat) : f n = n := let selected := h; by simp only [selected]");
    reject("theorem bad (x y : Nat) (h : x = y) : x = y := let unselected := h; by simp only []");
    reject(
        "theorem bad (x y : Nat) (h : x = y) : x = y := let selected : x = y := (1 : String); by simp only [selected]",
    );
}

#[test]
fn automatic_heterogeneous_reflexivity_checks_types_and_respects_selection() {
    check(
        "theorem same {A : Type} (x : A) : HEq x x := by simp only []
        def ident (x : Nat) : Nat := x
        theorem selected (x : Nat) : HEq (ident x) x := by simp only [ident]",
    );
    for source in [
        "theorem bad : HEq 1 2 := by simp only []",
        "theorem bad : HEq 1 true := by simp only []",
        "def ident (x : Nat) : Nat := x\ntheorem bad (x : Nat) : HEq (ident x) x := by simp only []",
    ] {
        reject(source);
    }
}

#[test]
fn constrained_induction_does_not_bypass_coverage_or_small_elimination() {
    for source in [
        "inductive Tag : Nat -> Type where | zero : Tag 0 | one : Tag 1\ndef bad (f : Nat -> Nat) (x : Tag (f 7)) : Nat := by induction x with | zero => exact 0",
        "inductive ExistsAt (A : Type) : Nat -> Prop where | intro (n : Nat) (x : A) : ExistsAt A n\ndef bad {A : Type} (h : ExistsAt A 3) : A := by induction h with | intro n x => exact x",
        "inductive Tagged (base : Nat) : Nat -> Type where | mk : Tagged base base\ntheorem bad (base : Nat) (x : Tagged base base) : x = x := by induction x generalizing base with | mk => rfl",
    ] {
        reject(source);
    }
    reject(&format!(
        "{VEC}\
        def bad (xs : Vec Nat 1) : Nat := by induction xs with
          | nil => exact (1 : String)
          | cons k x tail ih => exact x"
    ));
}

#[test]
fn constrained_induction_resource_stops_preserve_the_original_engine() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = engine
        .check_source_files(
            &[VEC.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&KVMap::new());
    let source =
        b"def head (xs : Vec Nat 1) : Nat := by induction xs with | cons k x tail ih => exact x";
    let mut small = limits;
    small.kernel.steps = 1;
    match engine.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(small)) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        result => panic!("expected a resource nonanswer, got {result:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    assert!(matches!(
        engine.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits)),
        Ok(fln::Outcome::Complete(_))
    ));
}

#[test]
fn induction_specialization_keeps_ignored_argument_annotations_kernel_checked() {
    let prefix = "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n\
        def ignore (x : Nat) : 0 = 0 := rfl\n";
    check(&format!(
        "{prefix}theorem control (w : Walk 3) : 0 = 0 := by induction w with | done k => rfl | step k child ih => exact ignore 0"
    ));
    let source = format!(
        "{prefix}theorem bad (w : Walk 3) : 0 = 0 := by induction w with | done k => rfl | step k child ih => exact ignore (child : Nat)"
    );
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err("the ignored value must remain in the checked branch");
    assert_eq!(
        error.disposition(),
        ("kernel-rejection", true, 1),
        "{error:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
#[test]
fn nonempty_vector_head_omits_only_the_impossible_branch() {
    check(&format!(
        "{VEC}\
    def head {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by\n  cases xs with\n  | cons k x tail => exact x\n\
    theorem head_ok : head 0 (Vec.cons 0 9 Vec.nil) = 9 := by rfl"
    ));
}
#[test]
fn nonempty_vector_tail_refines_its_dependent_result() {
    check(&format!(
        "{VEC}\
    def tail {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := by\n  cases xs with\n  | cons k x rest => exact rest\n\
    theorem tail_ok : tail 0 (Vec.cons 0 9 Vec.nil) = Vec.nil := by rfl"
    ));
}
#[test]
fn repeated_indices_remain_connected() {
    check(
        "inductive Same : Nat -> Nat -> Type where | mk (k : Nat) : Same k k\n\
    def selected (n : Nat) (x : Same n n) : Nat := by\n  cases x with\n  | mk k => exact k\n\
    theorem selected_ok : selected 7 (Same.mk 7) = 7 := by rfl",
    );
}

#[test]
fn repeated_constructor_fields_keep_their_source_names_after_refinement() {
    check(
        "inductive PairAt : Nat -> Nat -> Type where | mk (a b : Nat) : PairAt a b\n\
    theorem equal_fields (n : Nat) (x : PairAt n n) : n = n := by\n  cases x with\n  | mk a b => exact (rfl : a = b)\n\
    def field_sum (n : Nat) (x : PairAt n n) : Nat := by\n  cases x with\n  | mk a b => exact a + b\n\
    theorem sum_ok : field_sum 7 (PairAt.mk 7 7) = 14 := by rfl",
    );
}

#[test]
fn shared_parameter_index_is_not_generalized_out_of_the_parameter() {
    check(
        "inductive Tagged (tag : Nat) : Nat -> Type where | mk : Tagged tag tag\n\
    def selected (n : Nat) (x : Tagged n n) : Nat := by\n  cases x with\n  | mk => exact n\n\
    theorem selected_ok : selected 7 Tagged.mk = 7 := by rfl",
    );
}

#[test]
fn fixed_dependent_indices_transport_values_and_proof_dependent_hypotheses() {
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) : Witness A P a v\n\
    def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := by\n  cases w with\n  | intro a v => exact v\n\
    theorem extract_ok : extract (Witness.intro 7 true) = true := by rfl\n\
    theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by\n  cases w with\n  | intro a v => exact hp",
    );
}

#[test]
fn nested_fixed_cases_refine_the_correct_original_discriminant() {
    check(&format!(
        "{VEC}\
    def second (xs : Vec Nat 2) : Nat := by\n  cases xs with\n  | cons k x rest =>\n    cases rest with\n    | cons j y tail => exact y\n\
    theorem second_ok : second (Vec.cons 1 5 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl"
    ));
}

#[test]
fn dependent_original_values_remain_usable_through_aliases() {
    check(&format!(
        "{VEC}\
    theorem reconstruct {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : xs = xs := by\n  cases xs with\n  | cons k x tail => exact (rfl : xs = Vec.cons k x tail)\n\
    def from_let (xs : Vec Nat 1) : Nat := let saved := xs; by\n  cases xs with\n  | cons k x rest => exact x\n\
    theorem from_let_ok : from_let (Vec.cons 0 5 Vec.nil) = 5 := by rfl"
    ));
}

#[test]
fn contradictory_repeated_indices_and_bool_tags_need_no_source_branch() {
    check(
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
    def impossible (x : Diagonal 0 1) : Nat := by cases x\n\
    inductive TruthTag : Bool -> Type where | tagged : TruthTag true\n\
    def impossible_bool (x : TruthTag false) : Nat := by cases x\n\
    inductive Open : Nat -> Type where\n\
    def impossible_empty (x : Open 7) : Nat := by cases x",
    );
}

#[test]
fn let_indices_and_huge_literals_are_not_unrolled_into_unary_data() {
    check(&format!(
        "{VEC}\
    def let_input : Nat := let n := 1; let xs : Vec Nat n := Vec.cons 0 7 Vec.nil; by\n  cases xs with\n  | cons k x tail => exact x\n\
    theorem let_ok : let_input = 7 := by rfl\n\
    inductive Tag : Nat -> Type where | point : Tag 340282366920938463463374607431768211456\n\
    def huge (x : Tag 340282366920938463463374607431768211457) : Nat := by cases x"
    ));
}

#[test]
fn proof_families_keep_small_elimination_policy() {
    check(
        "inductive Even : Nat -> Prop where | zero : Even 0 | step (n : Nat) (h : Even n) : Even (Nat.succ (Nat.succ n))\n\
    theorem impossible (h : Even 1) : 0 = 1 := by cases h",
    );
}

fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "unexpected acceptance:\n{source}"
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
}

#[test]
fn incomplete_or_unreachable_supplied_branches_are_not_silently_erased() {
    for suffix in [
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | nil => exact 0",
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | nil => exact (true : Nat) | cons k a tail => exact a",
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | cons k a tail => exact (true : Nat)",
        "def wrong (x : Vec Nat 1) : Nat := by cases x with | cons k a tail => exact missing",
        "theorem wrong (x : Vec Nat 1) : 0 = 1 := by cases x with | cons k a tail => rfl",
    ] {
        reject(&format!("{VEC}{suffix}"));
    }
}

#[test]
fn unknown_equations_do_not_justify_pruning_a_branch() {
    reject(
        "inductive Tag : Nat -> Type where | zero : Tag 0 | one : Tag 1\n\
    def wrong (f : Nat -> Nat) (x : Tag (f 7)) : Nat := by cases x with | zero => exact 0",
    );
    reject(
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
    theorem wrong (n : Nat) (x : Diagonal n n) : n = 0 := by cases x with | mk k => rfl",
    );
}

#[test]
fn dependent_fixed_cases_do_not_expose_hidden_induction_hypotheses_or_prop_data() {
    reject(&format!(
        "{VEC}\
    theorem wrong (x : Vec Nat 1) : x = Vec.cons 0 0 Vec.nil := by cases x with | cons k a tail => assumption"
    ));
    reject(
        "inductive EitherAt (A : Type) : Nat -> Prop where | left (a : A) : EitherAt A 0 | right (a : A) : EitherAt A 1\n\
    def extract {A : Type} (h : EitherAt A 0) : A := by cases h with | left a => exact a",
    );
}

#[test]
fn constructor_binders_shadow_reintroduced_original_hypotheses() {
    check(&format!(
        "{VEC}\
    def shadow (xs : Vec Nat 1) (x : xs = xs) : Nat := by\n  cases xs with\n  | cons k x tail => exact x\n\
    theorem shadow_ok : shadow (Vec.cons 0 7 Vec.nil) rfl = 7 := by rfl\n\
    def major_shadow (xs : Vec Nat 1) : Nat := by\n  cases xs with\n  | cons k xs tail => exact xs\n\
    theorem major_ok : major_shadow (Vec.cons 0 9 Vec.nil) = 9 := by rfl"
    ));
}

#[test]
fn failed_refinement_never_publishes_a_file_prefix() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let prefix = format!(
        "{VEC}\
    def head (xs : Vec Nat 1) : Nat := by cases xs with | cons k x tail => exact x"
    );
    let bad =
        "theorem impossible (xs : Vec Nat 1) : 0 = 1 := by cases xs with | cons k x tail => rfl";
    let good = "theorem correct : head (Vec.cons 0 9 Vec.nil) = 9 := by rfl";
    for source in [bad, good, bad, good] {
        let result = engine.check_source_files(
            &[prefix.as_bytes(), source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            source == good,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn unused_invalid_discriminants_remain_checked_obligations() {
    reject(&format!(
        "{VEC}\
    def wrong : Nat := let xs : Vec Nat 1 := (Vec.nil : Vec Nat 1); by\n  cases xs with\n  | cons k x tail => exact 0"
    ));
}

#[test]
fn source_matches_refine_fixed_vector_payloads_and_results() {
    check(&format!(
        "{VEC}\
        def head {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : A := match xs with | .cons k x rest => x\n\
        def tail {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := match xs with | Vec.cons k x rest => rest\n\
        theorem head_ok : head 0 (Vec.cons 0 9 Vec.nil) = 9 := by rfl\n\
        theorem tail_ok : tail 0 (Vec.cons 0 9 Vec.nil) = Vec.nil := by rfl"
    ));
}

#[test]
fn source_matches_connect_repeated_indices_and_field_names() {
    check(
        "inductive PairAt : Nat -> Nat -> Type where | mk (a b : Nat) : PairAt a b\n\
        def total (n : Nat) (x : PairAt n n) : Nat := match x with | .mk a b => a + b\n\
        theorem same (n : Nat) (x : PairAt n n) : n = n := match x with | .mk a b => (rfl : a = b)\n\
        theorem total_ok : total 7 (PairAt.mk 7 7) = 14 := by rfl",
    );
}

#[test]
fn source_matches_refine_nonlocal_discriminants_and_nested_terms() {
    check(&format!(
        "{VEC}\
        def second (xs : Vec Nat 2) : Nat := match xs with\n\
          | .cons k x rest => match rest with\n\
            | .cons j y tail => y\n\
        def keep (xs : Vec Nat 1) : Vec Nat 1 := xs\n\
        def head (xs : Vec Nat 1) : Nat := match keep xs with | .cons k x rest => x\n\
        theorem second_ok : second (Vec.cons 1 5 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl\n\
        theorem head_ok : head (Vec.cons 0 12 Vec.nil) = 12 := by rfl"
    ));
}

#[test]
fn source_matches_check_every_retained_expression_and_scope() {
    for body in [
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .nil => 0",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .nil => (true : Nat) | .cons k x rest => x",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest => (true : Nat)",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest => missing",
        "def bad (xs : Vec Nat 1) : Nat := match (Vec.nil : Vec Nat 1) with | .cons k x rest => 0",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest => let ignored := (1 : String); x",
        "theorem bad (xs : Vec Nat 1) : 0 = 1 := match xs with | .cons k x rest => by assumption",
    ] {
        reject(&format!("{VEC}{body}"));
    }
}

#[test]
fn source_refinement_preserves_dependent_indices_and_original_hypotheses() {
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) : Witness A P a v\n\
        def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := match w with | .intro a v => v\n\
        theorem extract_ok : extract (Witness.intro 7 true) = true := by rfl\n\
        theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := match w with | .intro a v => hp",
    );
}

#[test]
fn source_refinement_preserves_parameters_shared_with_indices() {
    check(
        "inductive Tagged (tag : Nat) : Nat -> Type where | mk : Tagged tag tag\n\
        def selected (n : Nat) (x : Tagged n n) : Nat := match x with | .mk => n\n\
        theorem selected_ok : selected 7 Tagged.mk = 7 := by rfl",
    );
}

#[test]
fn source_refinement_infers_results_and_accepts_function_valued_branches() {
    check(&format!(
        "{VEC}\
        def head (xs : Vec Nat 1) := match xs with | .cons k x rest => x\n\
        def shifted (xs : Vec Nat 1) : Nat -> Nat := match xs with | .cons k x rest => fun delta => x + delta\n\
        theorem head_ok : head (Vec.cons 0 3 Vec.nil) = 3 := by rfl\n\
        theorem shift_ok : shifted (Vec.cons 0 3 Vec.nil) 8 = 11 := by rfl"
    ));
}

#[test]
fn source_refinement_skips_implicit_fields_without_skipping_checked_arguments() {
    check(
        "inductive Hidden : Nat -> Type where | mk {n : Nat} (value : Nat) : Hidden n\n\
        def extract (x : Hidden 7) : Nat := match x with | .mk value => value\n\
        theorem value_ok : extract (Hidden.mk 23) = 23 := by rfl",
    );
}

#[test]
fn source_refinement_catch_all_binds_the_actual_reachable_constructor() {
    check(
        "inductive Choice : Nat -> Type where | absent : Choice 0 | first (x : Nat) : Choice 1 | second (x : Nat) : Choice 1\n\
        def keep (x : Choice 1) : Choice 1 := match x with | .first n => Choice.first n | rest => rest\n\
        theorem first_ok : keep (Choice.first 7) = Choice.first 7 := by rfl\n\
        theorem second_ok : keep (Choice.second 9) = Choice.second 9 := by rfl",
    );
}

#[test]
fn source_refinement_rejects_redundant_fallbacks_and_malformed_patterns() {
    for body in [
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest => x | _ => (true : Nat)",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x => x",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest extra => x",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x x => x",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest => x | .cons k y tail => y",
        "def bad (xs : Vec Nat 1) : Nat := match xs with | .missing x => x",
    ] {
        reject(&format!("{VEC}{body}"));
    }
}

#[test]
fn source_refinement_preserves_proposition_elimination_restrictions() {
    reject(
        "inductive EitherAt (A : Type) : Nat -> Prop where | left (a : A) : EitherAt A 0 | right (a : A) : EitherAt A 1\n\
        def extract {A : Type} (h : EitherAt A 0) : A := match h with | .left a => a",
    );
    check(
        "inductive Even : Nat -> Prop where | zero : Even 0 | step (n : Nat) (h : Even n) : Even (Nat.succ (Nat.succ n))\n\
        theorem zero (h : Even 0) : 0 = 0 := match h with | .zero => rfl",
    );
}

#[test]
fn source_refinement_does_not_invent_function_injectivity_or_branch_coverage() {
    reject(
        "inductive Tag : Nat -> Type where | zero : Tag 0 | one : Tag 1\n\
        def bad (f : Nat -> Nat) (x : Tag (f 7)) : Nat := match x with | .zero => 0",
    );
    check(
        "inductive Tag : Nat -> Type where | zero : Tag 0 | one : Tag 1\n\
        def choose (f : Nat -> Nat) (x : Tag (f 7)) : Nat := match x with | .zero => 3 | .one => 5",
    );
}

#[test]
fn a_discriminant_with_an_ignored_invalid_argument_still_reaches_kernel_checking() {
    let source = format!(
        "{VEC}\
        def ignore (x : String) : Vec Nat 1 := Vec.cons 0 7 Vec.nil\n\
        def bad : Nat := match ignore (1 : String) with | .cons k x rest => 0"
    );
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err("discarding the discriminant must not discard its typing obligations");
    assert_eq!(
        error.disposition(),
        ("kernel-rejection", true, 1),
        "{error:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn constrained_match_resource_exhaustion_is_not_a_language_rejection() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = engine
        .check_source_files(
            &[VEC.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&KVMap::new());
    let source = b"def head (xs : Vec Nat 1) : Nat := match xs with | .cons k x rest => x";
    let mut small = limits;
    small.kernel.steps = 1;
    match engine.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(small)) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        result => panic!("expected a resource nonanswer, got {result:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    assert!(matches!(
        engine.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits)),
        Ok(fln::Outcome::Complete(_))
    ));
}
