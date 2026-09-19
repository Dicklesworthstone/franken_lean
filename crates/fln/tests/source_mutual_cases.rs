//! Tactic and indexed case analysis over native admitted mutual data families.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_elab::{
    records::RecordBudget,
    source::scope::{SourceScope, elaborate_mutual_inductives},
};
fn engine(families: &[&str]) -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let syntax: Vec<_> = families
        .iter()
        .map(|s| {
            fln_parse::parse_definition(s.as_bytes())
                .unwrap()
                .syntax()
                .clone()
        })
        .collect();
    let candidate = elaborate_mutual_inductives(
        &syntax,
        engine.environment(),
        limits.kernel,
        RecordBudget::default(),
        &SourceScope::default(),
    )
    .unwrap();
    (
        engine
            .admit_declaration(candidate, &KVMap::new(), limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .engine,
        limits,
    )
}
const FAMILIES: &[&str] = &[
    "inductive Tree (A : Type) where | node (value : A) (children : Forest A)",
    "inductive Forest (B : Type) where | nil | cons (head : Tree B) (tail : Forest B)",
];
fn check(families: &[&str], source: &str) {
    let (engine, limits) = engine(families);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn tactic_cases_return_real_constructor_fields_and_compute() {
    check(
        FAMILIES,
        "def head (t : Tree Nat) : Nat := by cases t with | node n xs => exact n\ndef empty (xs : Forest Nat) : Bool := by cases xs with | nil => exact true | cons t rest => exact false\ntheorem computes : head (Tree.node 7 (@Forest.nil Nat)) = 7 := by rfl\ntheorem emptyComputes : empty (@Forest.nil Nat) = true := by rfl",
    );
}
#[test]
fn dependent_hypotheses_are_specialized_and_original_inputs_are_not_exposed() {
    check(
        FAMILIES,
        "theorem keep (t : Tree Nat) (P : Tree Nat -> Prop) (h : P t) : P t := by cases t with | node n xs => exact h\ndef payload (t : Tree Nat) : Type := match t with | .node n xs => Nat\ndef unpack (t : Tree Nat) : payload t := by cases t with | node n xs => exact n\ntheorem unpackComputes : unpack (Tree.node 8 (@Forest.nil Nat)) = 8 := by rfl",
    );
}
#[test]
fn empty_selected_family_eliminates_without_any_fabricated_branch() {
    check(
        &[
            "inductive VoidA where",
            "inductive Holder where | hold (x : VoidA)",
        ],
        "def impossible (v : VoidA) : Nat := by cases v\ntheorem impossibleProof (v : VoidA) : 0 = 1 := by cases v",
    );
}
#[test]
fn computed_scrutinees_and_named_equations_preserve_case_identity() {
    check(
        FAMILIES,
        "theorem computed (n : Nat) : n = n := by cases h : Tree.node n (@Forest.nil Nat) with | node x xs => rfl",
    );
}
#[test]
fn indexed_mutual_matches_keep_destination_indices_in_the_motive() {
    check(
        &[
            "inductive T (A : Type) : A -> Type where | node (x : A) (children : F A x) : T A x",
            "inductive F (B : Type) : B -> Type where | nil (x : B) : F B x | cons (x : B) (t : T B x) : F B x",
        ],
        "theorem keep (A : Type) (x : A) (t : T A x) (P : (y : A) -> T A y -> Prop) (h : P x t) : P x t := by cases t with | node y children => exact h\ndef read (A : Type) (x : A) (t : T A x) : A := match t with | .node y children => y\ntheorem readComputes : read Nat 7 (T.node 7 (F.nil 7)) = 7 := by rfl",
    );
}
#[test]
fn hidden_induction_hypotheses_cannot_prove_false_or_replace_missing_cases() {
    for source in [
        "theorem bad (t : Tree Nat) : 0 = 1 := by cases t with | node n xs ih => exact ih",
        "theorem bad (xs : Forest Nat) : 0 = 1 := by cases xs with | nil => rfl | cons t rest => rfl",
        "def bad (xs : Forest Nat) : Nat := by cases xs with | nil => exact 0",
        "def bad (t : Tree Nat) : Tree Nat := by cases t with | node n xs => exact t",
        "theorem bad (t : Tree Nat) : 0 = 1 := by induction t with | node n xs ih => exact ih",
    ] {
        let (engine, limits) = engine(FAMILIES);
        let root = engine.logical_root(&KVMap::new());
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
        engine
            .check_source_files(
                &[b"theorem recovery : 1 = 1 := by rfl"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap();
    }
}

#[test]
fn stopped_kernel_checks_are_nonanswers_and_leave_the_base_reusable() {
    let (engine, limits) = engine(FAMILIES);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let source = b"def head (t : Tree Nat) : Nat := by cases t with | node n xs => exact n";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source], &options, low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("kernel exhaustion must remain a nonanswer: {other:?}"),
    }
    assert_eq!(engine.logical_root(&options), root);
    engine
        .check_source_files(&[source], &options, SourceCheckLimits::new(limits))
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&options), root);
}
