//! Induction over indexed families, held to the pinned Reference. A written
//! index that every constructor binds as its own field and returns unchanged is
//! promoted to a parameter (`fixedIndicesToParams`), so `x : Loop 7` eliminates
//! with `7` fixed and constructors bind no field for it. `induction` refuses a
//! major whose remaining indices are not distinct local variables
//! (`checkInductionTargets`); only `cases` and `match` refine such indices.
//! Every program here was run through pinned `lean` v4.32.0: each `check` is
//! accepted there, and each `reject` is refused there for the reason it names.
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
const LOOP: &str = "inductive Loop : Nat -> Type where | seed (n : Nat) : Loop n | step (n : Nat) (rest : Loop n) : Loop n\n\
    def copy (n : Nat) : Loop n -> Loop n | .seed _ => Loop.seed n | .step _ rest => Loop.step n (copy n rest)\n";
#[test]
fn promoted_index_induction_has_a_genuine_child_hypothesis() {
    check(&format!(
        r#"{LOOP}
theorem copied (x : Loop 7) : copy 7 x = x := by
  induction x with
  | seed => rfl
  | step rest ih => simp only [copy, ih]"#
    ));
}

#[test]
fn every_written_uniform_index_is_promoted() {
    check(
        r#"
inductive PairAt : Nat -> Nat -> Type where
  | leaf (a b : Nat) : PairAt a b
  | step (a b : Nat) (child : PairAt a b) : PairAt a b
def copyPair (a b : Nat) : PairAt a b -> PairAt a b
  | .leaf _ _ => PairAt.leaf a b
  | .step _ _ child => PairAt.step a b (copyPair a b child)
theorem repeat_copy (n : Nat) (value : PairAt n n) : copyPair n n value = value := by
  induction value with
  | leaf => rfl
  | step child ih => simp only [copyPair, ih]
"#,
    );
}

#[test]
fn dependent_index_telescopes_are_promoted_together() {
    check(
        r#"
inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | base (a : A) (v : P a) : Trace A P a v
  | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v
def traceCopy {A : Type} {P : A -> Type} (a : A) (v : P a) : Trace A P a v -> Trace A P a v
  | .base _ _ => Trace.base a v
  | .step _ _ child => Trace.step a v (traceCopy a v child)
theorem trace_copy (A : Type) (P : A -> Type) (f : A -> A) (a : A) (v : P (f a))
    (value : Trace A P (f a) v) : traceCopy (f a) v value = value := by
  induction value with
  | base => rfl
  | step child ih => simp only [traceCopy, ih]
"#,
    );
}

#[test]
fn explicit_generalization_allows_changing_accumulators() {
    check(&format!(
        r#"{LOOP}
theorem generalized (x : Loop 7) (acc : Nat) : copy 7 x = x := by
  induction x generalizing acc with
  | seed => rfl
  | step rest ih => simp only [copy, ih (acc + 1)]
"#
    ));
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
#[test]
fn a_variable_index_is_generalized_by_the_motive() {
    check(&format!(
        r#"{VEC}
def length : (n : Nat) -> Vec Nat n -> Nat
  | _, .nil => 0
  | _, .cons k _ tail => Nat.succ (length k tail)
theorem length_eq (n : Nat) (xs : Vec Nat n) : length n xs = n := by
  induction xs with
  | nil => rfl
  | cons k x tail ih => simp only [length, ih]
theorem length_two : length 2 (Vec.cons 1 3 (Vec.cons 0 9 Vec.nil)) = 2 := by rfl
"#
    ));
}

#[test]
fn proof_dependent_hypotheses_and_let_values_survive_generalization() {
    check(&format!(
        r#"{LOOP}
theorem retained (x : Loop 7) (h : x = x) (P : x = x -> Prop) (hp : P h) : P h := by
  induction x with
  | seed => exact hp
  | step rest ih => exact hp
theorem remembered (x : Loop 7) : True := let original := x; by
  induction x with
  | seed => exact True.intro
  | step rest ih => exact ih
"#
    ));
}

#[test]
fn multiple_recursive_children_have_separate_hypotheses() {
    check(
        r#"
inductive TreeAt : Bool -> Type where
  | leaf (tag : Bool) : TreeAt tag
  | node (tag : Bool) (left right : TreeAt tag) : TreeAt tag
def mirror (tag : Bool) : TreeAt tag -> TreeAt tag
  | .leaf _ => TreeAt.leaf tag
  | .node _ left right => TreeAt.node tag (mirror tag right) (mirror tag left)
theorem twice (tree : TreeAt true) : mirror true (mirror true tree) = tree := by
  induction tree with
  | leaf => rfl
  | node left right ihl ihr => simp only [mirror, ihl, ihr]
"#,
    );
}

#[test]
fn branch_names_shadow_original_locals_without_changing_core_identity() {
    check(&format!(
        r#"{LOOP}
theorem shadow (x : Loop 7) (rest : Nat) (ih : Nat) : copy 7 x = x := by
  induction x with
  | seed => rfl
  | step rest ih => simp only [copy, ih]
"#
    ));
}

const WALK: &str = "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\n";
#[test]
fn equation_definitions_over_a_promoted_family_skip_its_parameters() {
    // Several discriminants compile through elimination, not the single-match
    // path; both read a promoted parameter's position as `_`.
    check(&format!(
        r#"{WALK}def drain (n : Nat) : Walk n -> Nat -> Nat
  | .done _, acc => acc
  | .step _ child, acc => drain n child (acc + 1)
theorem drained : drain 3 (Walk.step 3 (Walk.step 3 (Walk.done 3))) 0 = 2 := by rfl
def both (n : Nat) (x : Walk n) (k : Nat) : Nat := match x, k with
  | .done _, k => k
  | .step _ child, k => both n child k + 1
theorem both_two : both 3 (Walk.step 3 (Walk.done 3)) 5 = 6 := by rfl
"#
    ));
    // Pin: type mismatch, the pattern `Walk.done m : Walk m` against `Walk n`,
    // with one discriminant and with several.
    reject(
        &format!(
            "{WALK}def first (n : Nat) (x : Walk n) : Nat := match x with\n  | .done m => m\n  | .step _ _ => 0"
        ),
        Some("InaccessibleParameter"),
    );
    reject(
        &format!(
            "{WALK}def drain (n : Nat) : Walk n -> Nat -> Nat\n  | .done m, acc => acc\n  | .step _ child, acc => drain n child (acc + 1)"
        ),
        Some("InaccessibleParameter"),
    );
    // The pattern matrix aliases a written name to its generated column, which
    // the match leaves unbound at a parameter position: the same refusal, not a
    // scope error (examples/native_matrix_recursion.lean, pin 44:4).
    reject(
        &format!(
            "{WALK}def constrained (w : Walk 7) (flag : Bool) : Nat := match w, flag with\n  | .done k, _ => k\n  | .step _ child, _ => constrained child flag"
        ),
        Some("InaccessibleParameter"),
    );
}

fn name(text: &str) -> fln::Name {
    fln::Name::from_components(text.split('.'))
}

#[test]
fn promotion_produces_the_declaration_the_pin_prints() {
    // Pin `#print Loop`: "number of parameters: 1"; `#check @Loop.seed`:
    // `(n : Nat) → Loop n`; `#check @Imp.c`: `{n : Nat} → Imp n`; `#check
    // @Loop.rec`: `{a : Nat} → {motive : Loop a → Sort u_1} → motive (Loop.seed a)
    // → ((rest : Loop a) → motive rest → motive (Loop.step a rest)) → (t : Loop a)
    // → motive t`. `Vec`'s index is not uniform, so it stays an index.
    use fln_core::expr::{BinderInfo, ExprNode};
    use fln_env::constants::ConstantInfo;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!("{LOOP}inductive Imp : Nat -> Type where | c {{n : Nat}} : Imp n\n{VEC}");
    let checked = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let environment = checked.environment();
    for (family, params, indices) in [("Loop", 1, 0), ("Imp", 1, 0), ("Vec", 1, 1)] {
        let Some(ConstantInfo::Induct(info)) = environment.find(&name(family)) else {
            panic!("{family} is not an admitted family");
        };
        assert_eq!(
            (info.num_params, info.num_indices),
            (params, indices),
            "{family}"
        );
    }
    for (ctor, fields, written) in [
        ("Loop.seed", 0, BinderInfo::Default),
        ("Loop.step", 1, BinderInfo::Default),
        ("Imp.c", 0, BinderInfo::Implicit),
    ] {
        let Some(ConstantInfo::Ctor(info)) = environment.find(&name(ctor)) else {
            panic!("{ctor} is not an admitted constructor");
        };
        assert_eq!((info.num_params, info.num_fields), (1, fields), "{ctor}");
        let ExprNode::ForallE {
            binder_name,
            binder_info,
            ..
        } = info.base.type_.node()
        else {
            panic!("{ctor} has no parameter binder");
        };
        assert_eq!(
            binder_name,
            &name("n"),
            "{ctor} keeps its written binder name"
        );
        assert_eq!(
            *binder_info, written,
            "{ctor} keeps its written binder style"
        );
    }
    let Some(ConstantInfo::Rec(rec)) = environment.find(&name("Loop.rec")) else {
        panic!("Loop.rec is not admitted");
    };
    assert_eq!((rec.num_params, rec.num_indices, rec.num_minors), (1, 0, 2));
    let ExprNode::ForallE { binder_info, .. } = rec.base.type_.node() else {
        panic!("Loop.rec has no parameter binder");
    };
    assert_eq!(*binder_info, BinderInfo::Implicit);
}

/// Refused, leaving the engine's environment unchanged. `reason`, when given,
/// names the refusal the pin's own reason corresponds to.
fn reject(source: &str, reason: Option<&str>) {
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
        panic!("unexpected acceptance: {source}\n{result:?}");
    };
    if let Some(reason) = reason {
        let rendered = format!("{error:?}");
        assert!(
            rendered.contains(reason),
            "expected {reason} for:\n{source}\ngot {rendered}"
        );
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn a_fixed_or_computed_index_is_refused_as_the_pin_refuses_it() {
    // Pin: "Invalid target: Index in target's type is not a variable".
    for source in [
        format!(
            "{VEC}theorem false_length (xs : Vec Nat 1) : 0 = 1 := by\n  induction xs with\n  | cons k x tail ih => exact ih"
        ),
        format!(
            "{VEC}theorem bad (n : Nat) (xs : Vec Nat (Nat.succ n)) : True := by\n  induction xs with\n  | nil => exact True.intro\n  | cons k x tail ih => exact True.intro"
        ),
        "inductive Holds : Nat -> Prop where\n  | base : Holds 0\n  | step (previous : Holds 0) : Holds 0\n\
         theorem duplicate (h : Holds 0) : Holds 0 := by\n  induction h with\n  | base => exact Holds.base\n  | step previous ih => exact Holds.step ih"
            .to_owned(),
        "inductive Diagonal : Nat -> Nat -> Type where | mk (n : Nat) : Diagonal n n\n\
         def empty (x : Diagonal 0 1) : Nat := by induction x"
            .to_owned(),
        "inductive Tags : Nat -> Type where | zero : Tags 0 | one : Tags 1\n\
         def bad (f : Nat -> Nat) (x : Tags (f 7)) : Nat := by induction x with | zero => exact 0 | one => exact 1"
            .to_owned(),
        "inductive HasData (A : Type) : Nat -> Prop where\n  | base (a : A) : HasData A 0\n  | step (previous : HasData A 0) : HasData A 0\n\
         def extract (A : Type) (h : HasData A 0) : A := by\n  induction h with\n  | base a => exact a\n  | step previous ih => exact ih"
            .to_owned(),
    ] {
        reject(&source, Some("InductionIndexNotVariable"));
    }
}

#[test]
fn a_repeated_index_is_refused_as_the_pin_refuses_it() {
    // Pin: "Invalid target: Target (or one of its indices) occurs more than once".
    reject(
        "inductive Twice : Nat -> Nat -> Type where | mk : Twice 0 0 | swap (a b : Nat) (t : Twice b a) : Twice a b\n\
         theorem bad (n : Nat) (x : Twice n n) : True := by induction x with | mk => exact True.intro | swap a b t ih => exact True.intro",
        Some("InductionIndexRepeated"),
    );
}

#[test]
fn an_index_read_by_the_parameters_is_refused_as_the_pin_refuses_it() {
    // Pin: "Type mismatch when assigning motive", for both families.
    reject(
        "inductive Marked (tag : Nat) : Nat -> Type where\n  | base : Marked tag tag\n  | step (child : Marked tag tag) : Marked tag tag\n\
         theorem marked (tag : Nat) (value : Marked tag tag) : True := by\n  induction value with\n  | base => exact True.intro\n  | step child ih => exact True.intro",
        Some("InductionMotiveMismatch"),
    );
    reject(
        "inductive Same : Nat -> Nat -> Type where | mk (a : Nat) : Same a 0 | other (a b : Nat) : Same a b\n\
         theorem bad (n : Nat) (x : Same n n) : True := by induction x with | mk => exact True.intro | other b => exact True.intro",
        Some("InductionMotiveMismatch"),
    );
}

#[test]
fn a_promoted_index_binds_no_field_in_the_alternatives() {
    // Pin: "Too many variable names provided at alternative `seed`: 1 provided, but 0 expected".
    reject(
        &format!(
            "{LOOP}theorem old (x : Loop 7) : copy 7 x = x := by\n  induction x with\n  | seed n => rfl\n  | step n rest ih => simp only [copy, ih]"
        ),
        Some("EliminationArity"),
    );
}

#[test]
fn induction_does_not_assume_the_whole_equals_its_child() {
    // Pin: type mismatch, `ih : rest = Loop.seed 7` against `Loop.step 7 rest = Loop.seed 7`.
    reject(
        &format!(
            r#"{LOOP}
theorem false_statement (x : Loop 7) : x = Loop.seed 7 := by
  induction x with
  | seed => rfl
  | step rest ih => exact ih
"#
        ),
        None,
    );
}

#[test]
fn cases_has_no_induction_hypothesis() {
    // Pin: unknown identifier `ih`.
    reject(
        &format!(
            r#"{LOOP}
theorem copied (x : Loop 7) : copy 7 x = x := by
  cases x with
  | seed => rfl
  | step rest => simp only [copy, ih]
"#
        ),
        None,
    );
}

#[test]
fn bad_branches_are_not_discarded() {
    // Pin: `rfl` fails; `step` not provided; unknown identifier `x` (the target
    // is cleared); `x` cannot be generalized; `n` is generalized twice; a
    // `Bool` is not a `Nat`.
    for (body, reason) in [
        (
            "theorem bad (x : Loop 7) : 0 = 1 := by induction x with | seed => rfl | step rest ih => assumption",
            None,
        ),
        (
            "theorem bad (x : Loop 7) : x = x := by induction x with | seed => rfl",
            Some("EliminationCoverage"),
        ),
        (
            "theorem bad (x : Loop 7) : x = x := by induction x with | seed => rfl | step rest ih => exact (true : x = x)",
            None,
        ),
        (
            "theorem bad (x : Loop 7) : x = x := by induction x generalizing x with | seed => rfl | step rest ih => rfl",
            None,
        ),
        (
            "theorem bad (x : Loop 7) (n : Nat) : x = x := by induction x generalizing n n with | seed => rfl | step rest ih => rfl",
            None,
        ),
        (
            "theorem bad (x : Loop 7) : copy 7 x = x := by\n  induction x with\n  | seed => rfl\n  | step rest ih => exact (let unused := (true : Nat); ih)",
            None,
        ),
    ] {
        reject(&format!("{LOOP}{body}"), reason);
    }
}

#[test]
fn low_budgets_and_bad_file_suffixes_preserve_the_original_environment() {
    use fln::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = engine
        .check_source_files(
            &[LOOP.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&KVMap::new());
    let good = "theorem good (x : Loop 7) : copy 7 x = x := by\n  induction x with\n  | seed => rfl\n  | step rest ih => simp only [copy, ih]";
    let bad = "theorem bad (x : Loop 7) : 0 = 1 := by\n  induction x with\n  | seed => rfl\n  | step rest ih => assumption";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[good.as_bytes()], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a resource nonanswer, got {other:?}"),
    }
    for valid in [false, true, false, true] {
        let sources = if valid {
            vec![good.as_bytes()]
        } else {
            vec![good.as_bytes(), bad.as_bytes()]
        };
        let result =
            engine.check_source_files(&sources, &KVMap::new(), SourceCheckLimits::new(limits));
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            valid,
            "{result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}
