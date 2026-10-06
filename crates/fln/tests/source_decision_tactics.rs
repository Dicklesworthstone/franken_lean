//! Decision-driven proof control must retain evidence and every branch.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, Outcome, SourceCheckLimits,
};
use std::path::{Path, PathBuf};

fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let before = engine.logical_root(&KVMap::new());
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
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
#[test]
fn decidable_case_split_supplies_positive_then_negative_evidence() {
    check(
        r#"
        inductive Either (P Q : Prop) : Prop where
          | left (p : P)
          | right (q : Q)
        theorem excluded (p : Prop) [Decidable p] : Either p (Not p) := by
          by_cases evidence : p
          · exact Either.left evidence
          · exact Either.right evidence
    "#,
    );
}
#[test]
fn case_splits_compute_data_without_skipping_either_source_branch() {
    check(
        r#"
        def flag (p : Prop) [Decidable p] : Nat := by
          by_cases h : p
          · exact 7
          · exact 9
        theorem positive : flag True = 7 := by rfl
        theorem negative : flag False = 9 := by rfl
        theorem twice : flag (Not (Not True)) = 7 := by rfl
    "#,
    );
    reject("def invalid : Nat := by by_cases h : True; exact 7; exact (1 : String)");
}
/// An unnamed `by_cases p` binds a hygienic hypothesis, as at the pin (lean v4.32.0, each
/// program run 2026-10-06): `assumption` finds it, a source `h` does not. The refusal is the
/// pin's first error, verbatim. This test used to accept `f h` and `exact h` there.
#[test]
fn default_names_shadow_hygienically_and_dependent_contexts_survive() {
    check(
        r#"
        theorem default_name (p : Prop) [Decidable p] (f : p -> False) : Not p := by
          by_cases p
          · exact fun unused => f unused
          · assumption
        theorem dependent (p : Prop) [Decidable p] (h : Nat)
            (P : Nat -> Prop) (saved : P h) : P h := by
          by_cases h : p
          · exact saved
          · exact saved
    "#,
    );
    let source = "theorem default_name (p : Prop) [Decidable p] (f : p -> False) : Not p := by\n  by_cases p\n  · exact fun unused => f h\n  · exact h\n";
    reject(source);
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let error = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err(source)
        .to_string();
    assert!(
        error.contains("Unknown identifier `h`"),
        "the pin refuses the default name with `Unknown identifier `h``: {error}"
    );
}
#[test]
fn case_proofs_work_inside_local_lemmas_and_scoped_controllers() {
    check(
        r#"
        theorem nested (p q : Prop) [Decidable p] [Decidable q] (proof : p) : p := by
          have saved : p := by
            by_cases hp : p
            · exact hp
            · by_cases hq : q <;> exact proof
          exact saved
    "#,
    );
}
#[test]
fn missing_decisions_invalid_propositions_and_branch_leaks_refuse() {
    for source in [
        "theorem bad (p : Prop) : True := by by_cases h : p <;> exact True.intro",
        "theorem bad : True := by by_cases h : Nat <;> exact True.intro",
        "theorem bad : True := by by_cases h : (fun ignored => True) (1 : String) <;> exact True.intro",
        "theorem bad (p : Prop) [Decidable p] : p := by by_cases h : p; exact h; exact h",
        "theorem bad : False := by by_cases h : True <;> exact h",
    ] {
        reject(source);
    }
}

/// The pin refuses `(1 : String)` while elaborating (no `OfNat String 1`), in an
/// unselected branch as in an ignored argument; each twin must check.
#[test]
fn unselected_branches_and_ignored_proposition_arguments_are_checked() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let run = |source: &str| {
        engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
    };
    for (source, twin) in [
        (
            "def bad : Nat := by by_cases h : True; exact 7; exact (1 : String)",
            "def bad : Nat := by by_cases h : True; exact 7; exact (1 : Nat)",
        ),
        (
            "def bad : Nat := by by_cases h : (fun ignored => True) (1 : String); exact 7; exact 9",
            "def bad : Nat := by by_cases h : (fun ignored => True) \"one\"; exact 7; exact 9",
        ),
    ] {
        let result = run(source).unwrap_err();
        assert_eq!(
            result.disposition(),
            ("elaboration", false, 1),
            "{source}: {result:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        assert!(matches!(run(twin), Ok(fln::Outcome::Complete(_))), "{twin}");
    }
}

#[test]
fn failed_case_attempts_restore_the_goal_and_unavailable_dictionaries() {
    check(
        r#"
        theorem fallback (p : Prop) : True := by
          first | (by_cases h : p <;> exact True.intro) | exact True.intro
        theorem restored (p : Prop) [Decidable p] (saved : p) : p := by
          first | (by_cases h : p; exact h; fail) | exact saved
        theorem negative_evidence (p : Prop) [Decidable p] (h : p) : p := by
          by_cases evidence : p
          · exact evidence
          · contradiction
    "#,
    );
}

#[test]
fn decision_case_resource_stops_are_nonanswers_and_recovery_is_clean() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source = "theorem t : True := by try (by_cases h : True <;> exact True.intro)";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(e) => assert!(
            matches!(e.disposition(), ("resource" | "inconclusive", false, 3)),
            "{e:?}"
        ),
        result => panic!("exhaustion was swallowed: {result:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn computed_decision_tactic_returns_a_checked_proof() {
    check(
        r#"
        theorem yes : True := by decide
        theorem negative : Not False := by decide
        theorem nested : Not (Not True) := by decide
        inductive Holds : Prop where | yes
        instance holdsDecision : Decidable Holds := Decidable.isTrue Holds.yes
        theorem custom : Holds := by decide
    "#,
    );
}

#[test]
fn decisions_must_be_available_true_and_reducible() {
    for source in [
        "theorem bad : False := by decide",
        "theorem bad : Not True := by decide",
        "theorem bad (p : Prop) [Decidable p] : p := by decide",
        "theorem bad (p : Prop) (h : p) : p := by decide",
        "def bad : Nat := by decide",
    ] {
        reject(source);
    }
    check("theorem fallback (p : Prop) [Decidable p] (h : p) : p := by first | decide | exact h");
}

#[test]
fn explicitly_supplied_decision_proofs_still_check_the_boolean_equation() {
    check("theorem direct : True := of_decide_eq_true (Eq.refl true)");
    check("theorem target_inferred : True := by apply of_decide_eq_true; rfl");
    check(
        "theorem supplied (p : Prop) [Decidable p] (h : decide p = true) : p := of_decide_eq_true h",
    );
    reject("theorem forged : False := of_decide_eq_true (Eq.refl true)");
    reject("def forged : Nat := of_decide_eq_true (Eq.refl true)");
}

#[test]
fn local_decision_values_and_nested_proof_scopes_are_preserved() {
    check(
        r#"
        theorem available (p : Prop) (hp : p) : p := by
          let witness : Decidable p := Decidable.isTrue hp
          decide
        theorem nested : Not False := by
          have loc : Not False := by decide
          first | (have hidden : False := by decide; exact hidden) | exact loc
        inductive Both (P Q : Prop) : Prop where | intro (left : P) (right : Q)
        theorem parallel : Both True (Not False) := by constructor <;> decide
        theorem independent : Both True True := by
          constructor
          · let witness : Decidable True := Decidable.isTrue True.intro
            decide
          · decide
        "#,
    );
}

#[test]
fn dictionary_dependencies_close_hygienically_without_capturing_sibling_holes() {
    check(
        r#"
        theorem dependent (A : Type) (a : A) (P : A -> Prop) (proof : P a) : P a := by
          let witness : Decidable (P a) := Decidable.isTrue proof
          have saved : P a := by
            let proof := 23
            decide
          exact saved
        structure Later where
          proof : True
          carrier : Type
          value : carrier
        def build : Later := by
          refine Later.mk ?_ ?_ ?_
          · decide
          · exact Nat
          · exact 23
        theorem built : build.value = 23 := by rfl
        "#,
    );
}

#[test]
fn decision_computation_uses_admitted_matches_and_arithmetic() {
    check(
        r#"
        inductive Holds : Prop where | proof
        instance computed : Decidable Holds := match (3 + 4 == 7) with
          | true => Decidable.isTrue Holds.proof
          | false => Decidable.isTrue Holds.proof
        theorem evaluated : Holds := by decide
        def atZero (n : Nat) : Prop := match n with
          | .zero => True
          | .succ k => False
        instance zeroDecision : Decidable (atZero 0) := Decidable.isTrue True.intro
        theorem indexed : atZero 0 := by decide
        "#,
    );
}

#[test]
fn decision_tactics_compose_with_proposition_conditionals_and_scoped_holes() {
    check(
        r#"
        theorem conditional (p : Prop) [Decidable p] (hp : p) : p := by
          refine if branch : p then ?_ else ?_
          · let witness : Decidable p := Decidable.isTrue branch
            decide
          · exact hp
        inductive Holds : Prop where | proof
        instance conditionalDictionary : Decidable Holds :=
          if 3 + 4 == 7 then Decidable.isTrue Holds.proof else Decidable.isTrue Holds.proof
        theorem computed : Holds := by decide
        theorem composed (p : Prop) [Decidable p] (hp : p) : p := by
          by_cases evidence : p
          · exact if True then evidence else hp
          · exact hp
        "#,
    );
}

#[test]
fn a_reduced_dictionary_does_not_erase_ill_typed_arguments_or_lets() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let run = |source: &str| {
        engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
    };
    // The pin refuses each `1 : String` while elaborating (no `OfNat String 1`);
    // the false decision still reaches K1. Each twin must check.
    for (source, refusal, twin) in [
        (
            "theorem bad : True := by let witness : Decidable True := (fun ignored => Decidable.isTrue True.intro) (1 : String); decide",
            ("elaboration", false, 1),
            "theorem bad : True := by let witness : Decidable True := (fun ignored => Decidable.isTrue True.intro) \"one\"; decide",
        ),
        (
            "theorem bad : True := by have unused : String := 1; decide",
            ("elaboration", false, 1),
            "theorem bad : True := by have unused : String := \"one\"; decide",
        ),
        (
            "theorem bad : False := of_decide_eq_true (Eq.refl true)",
            ("kernel-rejection", true, 1),
            "theorem bad : True := of_decide_eq_true (Eq.refl true)",
        ),
    ] {
        let problem = run(source).unwrap_err();
        assert_eq!(problem.disposition(), refusal, "{source}\n{problem:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        assert!(matches!(run(twin), Ok(fln::Outcome::Complete(_))), "{twin}");
    }
}

#[test]
fn decide_resource_exhaustion_is_not_optional_tactic_failure() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = "theorem t : True := by first | decide | exact True.intro";
    let before = engine.logical_root(&KVMap::new());
    let mut limited = SourceCheckLimits::new(limits);
    limited.admission.kernel = limited.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limited) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(problem) => assert!(
            matches!(
                problem.disposition(),
                ("resource" | "inconclusive", false, 3)
            ),
            "{problem:?}"
        ),
        outcome => panic!("resource exhaustion was caught: {outcome:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

const STACK: usize = 256 * 1024 * 1024;

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

/// `Init.Tactics` and its import closure, dependency first.
const INIT_TACTICS: &[&str] = &["Init.Prelude", "Init.Coe", "Init.Notation", "Init.Tactics"];
/// `Init.Core` and its import closure, dependency first.
const INIT_CORE: &[&str] = &[
    "Init.Prelude",
    "Init.Coe",
    "Init.Notation",
    "Init.Tactics",
    "Init.SizeOf",
    "Init.Core",
];

/// A pinned import closure (its last module the root), admitted through the
/// council with its instance journals activated.
fn import_pinned(lib: &Path, closure: &[&str]) -> Engine {
    let names: Vec<Name> = closure
        .iter()
        .map(|module| Name::from_components(module.split('.')))
        .collect();
    let parts: Vec<[Vec<u8>; 3]> = closure
        .iter()
        .map(|module| {
            let base = module
                .split('.')
                .fold(lib.to_path_buf(), |path, part| path.join(part))
                .with_extension("olean");
            let read = |path: PathBuf| std::fs::read(&path).expect("pinned olean part");
            [
                read(base.clone()),
                read(base.with_extension("olean.server")),
                read(base.with_extension("olean.private")),
            ]
        })
        .collect();
    let inputs: Vec<OleanModuleInput<'_>> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        256 * 1024 * 1024,
        Budget::for_stack_bytes(STACK),
    ));
    match Engine::from_environment(Environment::new()).import_olean_modules_for_source(
        &inputs,
        &[names.last().expect("a nonempty closure").clone()],
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(imported)) => imported.engine,
        other => panic!("the pinned closure passes the council: {other:?}"),
    }
}

/// Against the pinned `Init.Tactics`, `decide` evaluates the pin's
/// `Decidable.decide` (vendored `Lean/Meta/AppBuilder.lean` `mkDecide`). There
/// `decide` alone is an `export` alias, not a constant, and evaluating it
/// refused every true proposition as "did not reduce". The pin, with `prelude`
/// and `import Init.Tactics`: `POSITIVE` exits 0; `NEGATIVE` exits 1,
/// "Tactic `decide` proved that the proposition 2 + 2 = 5 is false".
#[test]
fn decide_evaluates_the_pins_decidable_decide_against_the_real_prelude() {
    const POSITIVE: &str = "theorem one : 2 + 2 = 4 := by decide";
    const NEGATIVE: &str = "theorem one : 2 + 2 = 5 := by decide";
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let engine = import_pinned(&lib, INIT_TACTICS);
            let limits =
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
            let positive = engine.check_source_files(&[POSITIVE.as_bytes()], &KVMap::new(), limits);
            assert!(
                matches!(positive, Ok(Outcome::Complete(_))),
                "{POSITIVE} must be admitted: {positive:?}"
            );
            let before = engine.logical_root(&KVMap::new());
            let negative = engine.check_source_files(&[NEGATIVE.as_bytes()], &KVMap::new(), limits);
            let rendered = format!("{negative:?}");
            assert!(
                negative.is_err() && rendered.contains("DecisionNotTrue"),
                "{NEGATIVE} must be refused as a false decision: {rendered}"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}

/// Against the pinned `Init.Core`, instance selection for `Decidable (2 + 2 =
/// 4)` reaches `instDecidableEqNat` within the default budget. Its 39 newer
/// `Decidable` instances each fail one strict match; each used to cost a
/// second, delta-retried inference equation, 14k-45k heartbeats apiece, and
/// the search ran out of heartbeats first. The pin, with `prelude` and
/// `import Init.Core`, exits 0 on both declarations.
#[test]
fn decidable_selection_against_the_real_init_core_fits_the_default_budget() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let engine = import_pinned(&lib, INIT_CORE);
            let limits =
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
            for source in [
                "theorem one : 2 + 2 = 4 := by decide",
                "def inst : Decidable (2 + 2 = 4) := inferInstance",
            ] {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                assert!(
                    matches!(checked, Ok(Outcome::Complete(_))),
                    "{source} must be admitted within the default budget: {checked:?}"
                );
            }
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
