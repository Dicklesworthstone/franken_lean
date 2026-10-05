//! Fixed index elimination builds actual equality transports and contradictions.
//! A written index that every constructor binds as its own field and returns
//! unchanged is promoted to a parameter, as the pinned Reference does
//! (`fixedIndicesToParams`), so its constructor position is inaccessible in
//! patterns and binds no field in alternatives. `induction` refuses a major whose
//! remaining indices are not distinct local variables (`checkInductionTargets`);
//! `cases` and `match` still refine them. Every program in a test whose comment
//! cites the pin was run through pinned `lean` v4.32.0.
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
/// Every `Walk` constructor binds the index as its own field and returns it
/// unchanged, so it is a parameter: `Walk.done` has no field and `Walk.step`
/// has one, `child`.
const WALK: &str = "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n";
/// The pin's `copy`: only `_` may stand in the inaccessible parameter position.
const WALK_COPY: &str = "def copy (n : Nat) : Walk n -> Walk n | .done _ => Walk.done n | .step _ child => Walk.step n (copy n child)\n";

#[test]
fn promoted_index_induction_quantifies_the_child_not_the_original_major() {
    // `w : Walk 3` eliminates with `3` fixed and `ih` is about `child`. Pin, for
    // the twin: type mismatch, `ih : copy 3 child = child` is not the major's
    // `copy 3 (Walk.step 3 child) = Walk.step 3 child`.
    check(&format!(
        r#"{WALK}{WALK_COPY}
theorem copied (w : Walk 3) : copy 3 w = w := by
  induction w with
  | done => rfl
  | step child ih =>
    have child_eq : copy 3 child = child := ih
    simp only [copy, child_eq]"#
    ));
    reject(&format!(
        r#"{WALK}{WALK_COPY}
theorem bad (w : Walk 3) : copy 3 w = w := by
  induction w with
  | done => rfl
  | step child ih => exact (ih : copy 3 (Walk.step 3 child) = Walk.step 3 child)"#
    ));
}

#[test]
fn induction_refuses_a_computed_index_and_cases_prunes_only_the_impossible_constructor() {
    // Pin: "Invalid target: Index in target's type is not a variable". `cases`
    // refines `Nat.succ n` and drops the impossible `nil`. With a variable index
    // nothing is impossible, so `induction` needs `nil` (pin: "Alternative `nil`
    // has not been provided").
    reject_because(
        &format!(
            "{VEC}\
            def head {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by induction xs with | cons k value tail ih => exact value\n\
            theorem checked : head 0 (Vec.cons 0 7 Vec.nil) = 7 := by rfl"
        ),
        "InductionIndexNotVariable",
    );
    check(&format!(
        "{VEC}\
        def head {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by cases xs with | cons k value tail => exact value\n\
        theorem checked : head 0 (Vec.cons 0 7 Vec.nil) = 7 := by rfl"
    ));
    reject_because(
        &format!(
            "{VEC}\
            theorem every {{A : Type}} (n : Nat) (xs : Vec A n) : True := by induction xs with | cons k value tail ih => exact True.intro"
        ),
        "EliminationCoverage",
    );
}

#[test]
fn promoted_tree_induction_exposes_both_real_recursive_hypotheses() {
    // The first `TreeAt` index is promoted and the second stays an index, which
    // `induction` needs as its own variable `m`; the repeated statement is an
    // instance. Pin, for induction directly on `t : TreeAt A n n`: "Type mismatch
    // when assigning motive"; with only `ihl` the right child stays unsolved.
    let tree = "inductive TreeAt (A : Type) : Nat -> Nat -> Type where | leaf (n : Nat) (a : A) : TreeAt A n n | fork (n : Nat) (left right : TreeAt A n n) : TreeAt A n n\n\
        def copyTree {A : Type} (n m : Nat) (t : TreeAt A n m) : TreeAt A n m := match t with | .leaf _ a => TreeAt.leaf n a | .fork _ l r => TreeAt.fork n (copyTree n n l) (copyTree n n r)\n";
    check(&format!(
        r#"{tree}theorem copied_all {{A : Type}} (n m : Nat) (t : TreeAt A n m) : copyTree n m t = t := by
  induction t with
  | leaf a => rfl
  | fork l r ihl ihr => simp only [copyTree, ihl, ihr]
theorem copied {{A : Type}} (n : Nat) (t : TreeAt A n n) : copyTree n n t = t := copied_all n n t"#
    ));
    reject_because(
        &format!(
            r#"{tree}theorem copied {{A : Type}} (n : Nat) (t : TreeAt A n n) : copyTree n n t = t := by
  induction t with
  | leaf a => rfl
  | fork l r ihl ihr => simp only [copyTree, ihl, ihr]"#
        ),
        "InductionMotiveMismatch",
    );
    reject(&format!(
        r#"{tree}theorem copied_all {{A : Type}} (n m : Nat) (t : TreeAt A n m) : copyTree n m t = t := by
  induction t with
  | leaf a => rfl
  | fork l r ihl ihr => simp only [copyTree, ihl]"#
    ));
}

#[test]
fn promoted_index_induction_can_change_a_generalized_accumulator() {
    // Pin, without `generalizing acc`: "Function expected at ih", which is only
    // `zero 3 child acc = 0`.
    let prefix = format!(
        "{WALK}def zero (n : Nat) (w : Walk n) (acc : Nat) : Nat := match w with | .done _ => 0 | .step _ child => zero n child (acc + 1)\n"
    );
    check(&format!(
        r#"{prefix}theorem zeroed (w : Walk 3) (acc : Nat) : zero 3 w acc = 0 := by
  induction w generalizing acc with
  | done => rfl
  | step child ih => simp only [zero]; exact ih (acc + 1)"#
    ));
    reject(&format!(
        r#"{prefix}theorem zeroed (w : Walk 3) (acc : Nat) : zero 3 w acc = 0 := by
  induction w with
  | done => rfl
  | step child ih => simp only [zero]; exact ih (acc + 1)"#
    ));
}

#[test]
fn promoted_index_induction_generalizes_proof_dependent_hypotheses() {
    check(&format!(
        "{WALK}\
        theorem preserve (w : Walk 3) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by induction w with | done => exact hp | step child ih => exact hp\n\
        theorem introduced : forall w : Walk 3, w = w := by intro w; induction w with | done => rfl | step child ih => rfl"
    ));
}

#[test]
fn indices_shared_with_family_parameters_need_a_general_index_for_induction() {
    // `stop` binds no field, so `Anchored`'s index stays an index. Pin, for
    // induction directly on `w : Anchored base base`: "Type mismatch when
    // assigning motive". Induction on a distinct index proves the general
    // statement, and the shared one is its instance.
    let prefix = "inductive Anchored (base : Nat) : Nat -> Type where | stop : Anchored base base | step (child : Anchored base base) : Anchored base base\n\
        def copy (base index : Nat) (w : Anchored base index) : Anchored base index := match w with | .stop => Anchored.stop | .step child => Anchored.step (copy base base child)\n";
    check(&format!(
        r#"{prefix}theorem copied_all (base index : Nat) (w : Anchored base index) : copy base index w = w := by
  induction w with
  | stop => rfl
  | step child ih => simp only [copy, ih]
theorem copied (base : Nat) (w : Anchored base base) : copy base base w = w := copied_all base base w"#
    ));
    reject_because(
        &format!(
            "{prefix}theorem copied (base : Nat) (w : Anchored base base) : copy base base w = w := by induction w with | stop => rfl | step child ih => simp only [copy, ih]"
        ),
        "InductionMotiveMismatch",
    );
}

#[test]
fn promoted_dependent_index_induction_keeps_each_index_in_its_own_domain() {
    // Both `Trace` indices are promoted together. `P` is given with `@` because
    // the pin does not infer it from `3` and `true`.
    check(
        "inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | stop (a : A) (v : P a) : Trace A P a v | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v\n\
        def copy {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with | .stop _ _ => Trace.stop a v | .step _ _ child => Trace.step a v (copy a v child)\n\
        theorem copied (t : Trace Nat (fun x => Bool) 3 true) : @copy Nat (fun x => Bool) 3 true t = t := by induction t with | stop => rfl | step child ih => simp only [copy, ih]",
    );
}

#[test]
fn induction_refuses_an_impossible_fixed_index_and_cases_needs_no_alternatives() {
    // Pin: "Invalid target: Index in target's type is not a variable".
    let diagonal = "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n";
    reject_because(
        &format!("{diagonal}def impossible (d : Diagonal 0 1) : Nat := by induction d"),
        "InductionIndexNotVariable",
    );
    check(&format!(
        "{diagonal}def impossible (d : Diagonal 0 1) : Nat := by cases d"
    ));
}

#[test]
fn promoted_index_induction_keeps_recursive_evidence_out_of_cases() {
    // Pin: `assumption` finds no hypothesis in `cases`; `rfl` cannot prove
    // `0 = 1`; "Variable `w` cannot be generalized because the induction target
    // depends on it"; `child` is not a `Nat`.
    let prefix = format!(
        "{WALK}def zero (n : Nat) (w : Walk n) : Nat := match w with | .done _ => 0 | .step _ child => zero n child\n"
    );
    check(&format!(
        "{prefix}theorem good (w : Walk 3) : zero 3 w = 0 := by induction w with | done => rfl | step child ih => simp only [zero, ih]"
    ));
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    for statement in [
        "theorem bad (w : Walk 3) : zero 3 w = 0 := by cases w with | done => rfl | step child => assumption",
        "theorem bad (w : Walk 3) : 0 = 1 := by induction w with | done => rfl | step child ih => exact ih",
        "theorem bad (w : Walk 3) : zero 3 w = 0 := by induction w generalizing w with | done => rfl | step child ih => simp only [zero, ih]",
        "theorem bad (w : Walk 3) : w = w := by induction w with | done => rfl | step child ih => let unused := (child : Nat); rfl",
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
fn conditional_child_hypotheses_are_refused_and_a_variable_index_gives_real_ones() {
    // Pin, for both conditional-hypothesis programs: "Invalid target: Index in
    // target's type is not a variable". With the length a variable, `ih` is the
    // child's own hypothesis at its actual index `k`, and the `Nat.succ n`
    // statement is an instance of the general one.
    let vec_copy = "def copy {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := match xs with\n  | .nil => Vec.nil\n  | .cons k x tail => Vec.cons k x (copy k tail)\n";
    check(&format!(
        r#"{VEC}{vec_copy}theorem copied_all {{A : Type}} (n : Nat) (xs : Vec A n) : copy n xs = xs := by
  induction xs with
  | nil => rfl
  | cons k x tail ih =>
    have child : copy k tail = tail := ih
    simp only [copy, child]
theorem copied {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : copy (Nat.succ n) xs = xs := copied_all (Nat.succ n) xs"#
    ));
    reject_because(
        &format!(
            r#"{VEC}{vec_copy}theorem copied {{A : Type}} (n : Nat) (xs : Vec A (Nat.succ n)) : copy (Nat.succ n) xs = xs := by
  induction xs generalizing n with
  | cons k x tail ih =>
    cases k with
    | zero =>
      cases tail with
      | nil => rfl
    | succ j => simp only [copy, ih j tail (HEq.refl (Nat.succ j)) (HEq.refl tail)]"#
        ),
        "InductionIndexNotVariable",
    );
    reject_because(
        &format!(
            r#"{VEC}theorem bad (xs : Vec Nat 1) : 0 = 1 := by induction xs with
  | cons k x tail ih => exact ih tail (HEq.refl 0) (HEq.refl tail)"#
        ),
        "InductionIndexNotVariable",
    );
}

#[test]
fn promoted_index_induction_keeps_local_aliases_and_pattern_name_shadowing() {
    // Aliases of the major are generalized with it: in `step` the alias is the
    // constructor value, not the child (pin: `rfl` is a type mismatch against
    // `saved = child`). A branch may name the child after the major.
    check(&format!(
        r#"{WALK}{WALK_COPY}
theorem let_major (w : Walk 3) : copy 3 w = w := let saved := w; let second := saved; by
  induction w with | done => rfl | step child ih => simp only [copy, ih]
theorem let_context (w : Walk 3) : copy 3 w = w := let saved := copy 3 w; by
  induction w with | done => rfl | step child ih => simp only [copy, ih]
theorem alias_tracks (w : Walk 3) : True := let saved := w; by
  induction w with
  | done => exact True.intro
  | step child ih =>
    have h : saved = Walk.step 3 child := rfl
    exact True.intro
theorem shadows (w : Walk 3) : copy 3 w = w := by
  induction w with | done => rfl | step w ih => simp only [copy, ih]"#
    ));
    reject(&format!(
        r#"{WALK}
theorem alias_wrong (w : Walk 3) : True := let saved := w; by
  induction w with
  | done => exact True.intro
  | step child ih =>
    have h : saved = child := rfl
    exact True.intro"#
    ));
    reject(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n\n\
        theorem bad (w : Walk 3) : w = w := let saved := (w : String); by induction w with | done => rfl",
    );
}

#[test]
fn selected_induction_companions_follow_scope_transport_but_not_shadowing() {
    // `cases child` transports `ih` to `copy 3 (Walk.step 3 grandchild) = ...`.
    // Pin: without `ih` the `step` goal stays unsolved; a shadowing `ih : Nat` "is
    // not a proposition or let-declaration".
    let prefix = format!("{WALK}{WALK_COPY}");
    check(&format!(
        r#"{prefix}theorem nested (w : Walk 3) : copy 3 w = w := by induction w with
  | done => rfl
  | step child ih =>
    cases child with
    | done => rfl
    | step grandchild =>
      simp only [copy] at ih ⊢
      simp only [ih]"#
    ));
    reject(&format!(
        "{prefix}theorem bad (w : Walk 3) : copy 3 w = w := by induction w with | done => rfl | step child ih => simp only [copy]"
    ));
    reject(&format!(
        "{prefix}theorem bad (w : Walk 3) : forall ignored : Nat, copy 3 w = w := by induction w with | done => intro ih; rfl | step child ih => intro ih; simp only [copy, ih]"
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
fn induction_resource_stops_preserve_the_original_engine() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let preloaded = format!(
        "{VEC}def copy {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := match xs with | .nil => Vec.nil | .cons k x tail => Vec.cons k x (copy k tail)\n"
    );
    let engine = engine
        .check_source_files(
            &[preloaded.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&KVMap::new());
    let source = b"theorem copied (n : Nat) (xs : Vec Nat n) : copy n xs = xs := by induction xs with | nil => rfl | cons k x tail ih => simp only [copy, ih]";
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
    // Pin: "Invalid target: Index in target's type is not a variable". The full
    // budget refuses the fixed-length form, and still publishes nothing.
    let fixed =
        b"def head (xs : Vec Nat 1) : Nat := by induction xs with | cons k x tail ih => exact x";
    let error = engine
        .check_source_files(&[fixed], &KVMap::new(), SourceCheckLimits::new(limits))
        .expect_err("a fixed index is not an induction target");
    assert!(
        format!("{error:?}").contains("InductionIndexNotVariable"),
        "{error:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn promoted_index_induction_keeps_ignored_argument_annotations_kernel_checked() {
    // The pin refuses the annotation while elaborating ("Type mismatch: `child`
    // has type `Walk 3` but is expected to have type `Nat`"); here the kernel
    // still refuses it. `control` is a pin prelude name, so the twin is `kept`.
    let prefix = format!("{WALK}def ignore (x : Nat) : 0 = 0 := rfl\n");
    check(&format!(
        "{prefix}theorem kept (w : Walk 3) : 0 = 0 := by induction w with | done => rfl | step child ih => exact ignore 0"
    ));
    let source = format!(
        "{prefix}theorem bad (w : Walk 3) : 0 = 0 := by induction w with | done => rfl | step child ih => exact ignore (child : Nat)"
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
    // `mk` binds the first index as its field, so it is promoted and `mk` has no
    // field (pin: "Too many variable names provided at alternative `mk`: 1
    // provided, but 0 expected"). `cases` connects the remaining index to it.
    let same = "inductive Same : Nat -> Nat -> Type where | mk (k : Nat) : Same k k\n";
    reject_because(
        &format!(
            "{same}\
    def selected (n : Nat) (x : Same n n) : Nat := by\n  cases x with\n  | mk k => exact k\n\
    theorem selected_ok : selected 7 (Same.mk 7) = 7 := by rfl"
        ),
        "EliminationArity",
    );
    check(&format!(
        "{same}\
    def selected (n : Nat) (x : Same n n) : Nat := by\n  cases x with\n  | mk => exact n\n\
    theorem selected_ok : selected 7 (Same.mk 7) = 7 := by rfl\n\
    theorem connected (n m : Nat) (x : Same n m) : n = m := by\n  cases x with\n  | mk => rfl"
    ));
}

#[test]
fn cases_on_repeated_indices_binds_unrefined_fields_by_their_source_names() {
    // `PairAt` as written is wholly promoted, so `mk` has no fields (pin: "Too
    // many variable names provided at alternative `mk`: 2 provided, but 0
    // expected"). After a leading `tag` field both stay indices: `cases` on
    // `PairAt n n` replaces `a b` by `n`, and `tag` keeps its source name.
    let promoted = "inductive PairAt : Nat -> Nat -> Type where | mk (a b : Nat) : PairAt a b\n";
    reject_because(
        &format!(
            "{promoted}\
    theorem equal_fields (n : Nat) (x : PairAt n n) : n = n := by\n  cases x with\n  | mk a b => exact (rfl : a = b)\n\
    def field_sum (n : Nat) (x : PairAt n n) : Nat := by\n  cases x with\n  | mk a b => exact a + b\n\
    theorem sum_ok : field_sum 7 (PairAt.mk 7 7) = 14 := by rfl"
        ),
        "EliminationArity",
    );
    check(&format!(
        "{promoted}\
    def field_sum (n : Nat) (x : PairAt n n) : Nat := by\n  cases x with\n  | mk => exact n + n\n\
    theorem sum_ok : field_sum 7 (PairAt.mk 7 7) = 14 := by rfl"
    ));
    check(
        "inductive PairAt : Nat -> Nat -> Type where | mk (tag : Nat) (a b : Nat) : PairAt a b\n\
    def field_sum (n : Nat) (x : PairAt n n) : Nat := by\n  cases x with\n  | mk tag a b => exact tag + n + n\n\
    theorem sum_ok : field_sum 7 (PairAt.mk 1 7 7) = 15 := by rfl",
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
fn cases_on_promoted_dependent_indices_transports_payloads_and_proof_dependent_hypotheses() {
    // `Witness` as written is wholly promoted, so `intro` has no fields (pin: "Too
    // many variable names provided at alternative `intro`: 2 provided, but 0
    // expected"). A payload of type `P a` reaches the branch as a `Bool`. `P` is
    // given with `@` because the pin does not infer it from `7` and `true`.
    reject_because(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) : Witness A P a v\n\
    def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := by\n  cases w with\n  | intro a v => exact v\n\
    theorem extract_ok : extract (Witness.intro 7 true) = true := by rfl\n\
    theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by\n  cases w with\n  | intro a v => exact hp",
        "EliminationArity",
    );
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) (payload : P a) : Witness A P a v\n\
    def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := by\n  cases w with\n  | intro payload => exact payload\n\
    theorem extract_ok : extract (@Witness.intro Nat (fun x => Bool) 7 true false) = false := by rfl\n\
    theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := by\n  cases w with\n  | intro payload => exact hp",
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

/// Refused for the pin's reason: the refusal names `reason`, the FrankenLean
/// variant that corresponds to it, and the environment is unchanged.
fn reject_because(source: &str, reason: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    let Err(error) = result else {
        panic!("unexpected acceptance:\n{source}\n{result:?}");
    };
    let rendered = format!("{error:?}");
    assert!(
        rendered.contains(reason),
        "expected {reason} for:\n{source}\ngot {rendered}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
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
    // `PairAt` as written is wholly promoted, so its named patterns stand in
    // parameter positions (pin: "Type mismatch"). After a leading `tag` field
    // both stay indices: one field name stands for both repeated positions and
    // the other is `_`, and the branch's goal names the field.
    reject_because(
        "inductive PairAt : Nat -> Nat -> Type where | mk (a b : Nat) : PairAt a b\n\
        def total (n : Nat) (x : PairAt n n) : Nat := match x with | .mk a b => a + b\n\
        theorem same (n : Nat) (x : PairAt n n) : n = n := match x with | .mk a b => (rfl : a = b)\n\
        theorem total_ok : total 7 (PairAt.mk 7 7) = 14 := by rfl",
        "InaccessibleParameter",
    );
    check(
        "inductive PairAt : Nat -> Nat -> Type where | mk (tag : Nat) (a b : Nat) : PairAt a b\n\
        def total (n : Nat) (x : PairAt n n) : Nat := match n, x with | _, .mk tag a _ => tag + a + a\n\
        theorem same (n : Nat) (x : PairAt n n) : n = n := match n, x with | _, .mk tag a _ => (rfl : a = a)\n\
        theorem total_ok : total 7 (PairAt.mk 1 7 7) = 15 := by rfl",
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
fn source_matches_on_promoted_dependent_indices_preserve_payloads_and_original_hypotheses() {
    // `Witness` as written is wholly promoted, so `.intro a v` names parameter
    // positions (pin: "Type mismatch"). Only `_` stands there; a payload of type
    // `P a` is matched as a `Bool`. `P` is given with `@` because the pin does
    // not infer it from `7` and `true`.
    reject_because(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) : Witness A P a v\n\
        def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := match w with | .intro a v => v\n\
        theorem extract_ok : extract (Witness.intro 7 true) = true := by rfl\n\
        theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := match w with | .intro a v => hp",
        "InaccessibleParameter",
    );
    check(
        "inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where | intro (a : A) (v : P a) (payload : P a) : Witness A P a v\n\
        def extract (w : Witness Nat (fun x => Bool) 7 true) : Bool := match w with | .intro _ _ payload => payload\n\
        theorem extract_ok : extract (@Witness.intro Nat (fun x => Bool) 7 true false) = false := by rfl\n\
        theorem retain (w : Witness Nat (fun x => Bool) 7 true) (h : w = w) (P : w = w -> Prop) (hp : P h) : P h := match w with | .intro _ _ payload => hp",
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

/// The pin refuses `(1 : String)` while elaborating (no `OfNat String 1`). The
/// index is a wildcard because the pin also refuses `.cons k ..` against `Vec Nat 1`
/// (`k.succ` is not `1`), and the twin must be a program the pin accepts.
#[test]
fn a_discriminant_with_an_ignored_invalid_argument_is_still_checked() {
    let source = |argument: &str| {
        format!(
            "{VEC}\
            def ignore (x : String) : Vec Nat 1 := Vec.cons 0 7 Vec.nil\n\
            def bad : Nat := match ignore {argument} with | .cons _ x rest => 0"
        )
    };
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let run = |argument: &str| {
        engine.check_source_files(
            &[source(argument).as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
    };
    let root = engine.logical_root(&KVMap::new());
    let error = run("(1 : String)")
        .expect_err("discarding the discriminant must not discard its typing obligations");
    assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    assert!(matches!(run("\"one\""), Ok(fln::Outcome::Complete(_))));
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
