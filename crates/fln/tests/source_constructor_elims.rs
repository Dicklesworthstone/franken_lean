//! Late constructor generation is a checked source operation, with real
//! eliminator inference, scoped options, atomic failure and exported metadata.
#![forbid(unsafe_code)]

use fln::source_check::SourceFileCheck;
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    OleanWriteBudget, Outcome, SourceCheckError, SourceCheckLimits, SourceModuleInput,
};
use fln_elab::eliminator_tags::{TagKind, read};
use fln_env::constants::ConstantInfo;
use std::sync::OnceLock;

const PAYLOAD: &str = "set_option genCtorIdx false in\n\
inductive Payload where | left (value : Nat) | right (text : String)\n";
const GENERATE: &str = "attribute [gen_constructor_elims] Payload\n";
const USE: &str = "def takeLeft (value : Payload) (selected : Payload.ctorIdx value = 0) : Nat :=\n\
  Payload.left.elim value selected (fun n => n)\n\
theorem left_computes : takeLeft (Payload.left 7) rfl = 7 := by rfl\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn base() -> Engine {
    // The real imported Prelude supplies Eq, PULift, cond and Nat.ble. Its
    // declarations and metadata pass the ordinary independent import seats.
    static PRELUDE: OnceLock<Engine> = OnceLock::new();
    PRELUDE
        .get_or_init(|| {
            const STACK: usize = 128 * 1024 * 1024;
            std::thread::Builder::new()
                .stack_size(STACK)
                .spawn(|| {
                    let prelude = name("Init.Prelude");
                    Engine::builder()
                        .build_empty()
                        .import_olean_modules_for_source(
                            &[OleanModuleInput {
                                name: &prelude,
                                artifact: include_bytes!(
                                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                                ),
                                server_artifact: Some(include_bytes!(
                                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                                )),
                                private_artifact: Some(include_bytes!(
                                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                                )),
                            }],
                            std::slice::from_ref(&prelude),
                            &KVMap::new(),
                            SourceOleanImportLimits::new(OleanCheckLimits::new(
                                16 << 20,
                                Budget::for_stack_bytes(STACK),
                            )),
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap()
                        .engine
                })
                .unwrap()
                .join()
                .unwrap()
        })
        .clone()
}

fn checked(engine: &Engine, source: &str) -> SourceFileCheck {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn rejected(engine: &Engine, source: &str) -> SourceCheckError {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &options,
        SourceCheckLimits::new(limits()),
    );
    assert_eq!(before, engine.logical_root(&options));
    match result {
        Err(error) => error,
        Ok(outcome) => panic!("{source}\n{:?}", outcome.map_complete(|_| ())),
    }
}

fn generated(engine: &Engine, family: &str, constructors: &[&str]) {
    let env = engine.environment();
    for suffix in ["ctorIdx", "ctorElimType", "ctorElim"] {
        assert!(matches!(
            env.find(&name(&format!("{family}.{suffix}"))),
            Some(ConstantInfo::Defn(_))
        ));
    }
    for kind in [TagKind::ElabAsElim, TagKind::SparseCasesOn] {
        let tags = read(env, kind).unwrap();
        for constructor in constructors {
            assert!(tags.contains(&name(&format!("{family}.{constructor}.elim"))));
        }
        assert!(!tags.contains(&name(&format!("{family}.ctorElim"))));
        assert!(!tags.contains(&name(&format!("{family}.ctorElimType"))));
    }
}

#[test]
fn late_generation_has_real_inferred_motive_and_kernel_computation() {
    let producer = checked(&base(), PAYLOAD);
    assert!(
        !producer
            .engine
            .environment()
            .contains(&name("Payload.ctorIdx"))
    );
    let result = checked(&producer.engine, &format!("{GENERATE}{USE}"));
    generated(&result.engine, "Payload", &["left", "right"]);
    assert!(
        !producer
            .engine
            .environment()
            .contains(&name("Payload.ctorIdx"))
    );
    rejected(
        &result.engine,
        "def wrongMotive (value : Payload) (h : Payload.ctorIdx value = 0) : String :=\n\
         Payload.left.elim value h (fun n => n)",
    );
    rejected(
        &result.engine,
        "def wrongIndex : Nat := Payload.left.elim (Payload.right \"x\") (Eq.refl 0) (fun n => n)",
    );
}

#[test]
fn generic_indexed_constructor_eliminates_with_its_original_indices() {
    let result = checked(
        &base(),
        "set_option genCtorIdx false in\n\
         inductive LateVector (A : Type) : Nat → Type where\n\
           | nil : LateVector A 0\n\
           | cons (n : Nat) (head : A) (tail : LateVector A n) : LateVector A (n + 1)\n\
         attribute [gen_constructor_elims] LateVector\n\
         def headOf {n : Nat} (value : LateVector Nat (n + 1))\n\
             (selected : LateVector.ctorIdx value = 1) : Nat :=\n\
           LateVector.cons.elim value selected (fun _ value _ => value)\n\
         theorem head_computes : headOf (LateVector.cons 0 7 LateVector.nil) rfl = 7 := by rfl",
    );
    generated(&result.engine, "LateVector", &["nil", "cons"]);
}

#[test]
fn an_existing_index_still_generates_eliminators_with_generation_disabled() {
    let producer = checked(
        &base(),
        &format!(
            "{PAYLOAD}def Payload.ctorIdx (value : Payload) : Nat :=\n\
             match value with | Payload.left _ => 0 | Payload.right _ => 1\n"
        ),
    );
    let index = producer
        .engine
        .environment()
        .find(&name("Payload.ctorIdx"))
        .unwrap()
        .clone();
    let result = checked(
        &producer.engine,
        &format!("set_option genCtorIdx false in\n{GENERATE}{USE}"),
    );
    generated(&result.engine, "Payload", &["left", "right"]);
    assert_eq!(
        result.engine.environment().find(&name("Payload.ctorIdx")),
        Some(&index)
    );
}

#[test]
fn option_scope_restores_and_an_explicit_disabled_request_does_nothing() {
    let producer = checked(&base(), PAYLOAD);
    let root = producer.engine.logical_root(&KVMap::new());
    let skipped = checked(
        &producer.engine,
        &format!("set_option genCtorIdx false in\n{GENERATE}"),
    );
    assert_eq!(root, skipped.engine.logical_root(&KVMap::new()));
    let result = checked(
        &base(),
        "section\nset_option genCtorIdx false\n\
         inductive Disabled where | left (n : Nat) | right (n : Nat)\nend\n\
         inductive Automatic where | left (n : Nat) | right (n : Nat)",
    );
    assert!(
        !result
            .engine
            .environment()
            .contains(&name("Disabled.ctorIdx"))
    );
    generated(&result.engine, "Automatic", &["left", "right"]);
}

#[test]
fn single_constructor_indices_are_macro_inline_and_repeated_requests_are_empty() {
    let producer = checked(
        &base(),
        "set_option genCtorIdx false in\n\
         inductive LateSingleton (A : Type) where | mk (value : A)\n\
         attribute [gen_constructor_elims] LateSingleton\n\
         theorem singleton_index : LateSingleton.ctorIdx (LateSingleton.mk 7) = 0 := by rfl",
    );
    let env = producer.engine.environment();
    assert!(
        fln_elab::macro_inline::read(env)
            .unwrap()
            .contains(&name("LateSingleton.ctorIdx"))
    );
    assert!(!env.contains(&name("LateSingleton.ctorElim")));
    assert!(!env.contains(&name("LateSingleton.mk.elim")));
    let result = checked(
        &producer.engine,
        "attribute [gen_constructor_elims, gen_constructor_elims] LateSingleton",
    );
    assert_eq!(
        producer.engine.logical_root(&KVMap::new()),
        result.engine.logical_root(&KVMap::new())
    );
}

#[test]
fn namespace_aliases_resolve_the_admitted_owner() {
    let producer = checked(
        &base(),
        &format!(
            "namespace Original\n{PAYLOAD}end Original\n\
                  namespace Alias\nexport Original (Payload)\nend Alias\n"
        ),
    );
    let result = checked(
        &producer.engine,
        "attribute [gen_constructor_elims] Alias.Payload",
    );
    generated(&result.engine, "Original.Payload", &["left", "right"]);
    assert!(
        !result
            .engine
            .environment()
            .contains(&name("Alias.Payload.ctorIdx"))
    );
}

#[test]
fn wrong_targets_modifiers_erasure_and_unimplemented_inline_requests_are_refused() {
    let producer = checked(&base(), PAYLOAD);
    for source in [
        "attribute [local gen_constructor_elims] Payload",
        "attribute [scoped gen_constructor_elims] Payload",
        "attribute [-gen_constructor_elims] Payload",
        "attribute [gen_constructor_elims 100] Payload",
        "attribute [gen_constructor_elims, simp] Payload",
        "attribute [gen_constructor_elims] Payload.left",
        "attribute [gen_constructor_elims] Nat.zero",
        "attribute [gen_constructor_elims] Missing",
        "@[gen_constructor_elims] inductive Inline where | left (n : Nat) | right (n : Nat)",
    ] {
        rejected(&producer.engine, source);
        assert!(
            !producer
                .engine
                .environment()
                .contains(&name("Payload.ctorIdx"))
        );
    }
}

#[test]
fn late_collisions_and_failed_later_targets_publish_no_generated_prefix() {
    let producer = checked(&base(), PAYLOAD);
    rejected(
        &producer.engine,
        "attribute [gen_constructor_elims] Payload Nat.zero",
    );
    rejected(
        &producer.engine,
        "attribute [gen_constructor_elims] Payload Missing",
    );
    rejected(
        &producer.engine,
        "attribute [gen_constructor_elims] Payload Payload",
    );
    let collision = checked(&producer.engine, "def Payload.right.elim : Nat := 9");
    rejected(&collision.engine, GENERATE);
    for engine in [&producer.engine, &collision.engine] {
        assert!(!engine.environment().contains(&name("Payload.ctorIdx")));
        assert!(!engine.environment().contains(&name("Payload.ctorElimType")));
        assert!(
            !read(engine.environment(), TagKind::ElabAsElim)
                .unwrap()
                .contains(&name("Payload.left.elim"))
        );
    }
}

#[test]
fn generation_budget_exhaustion_is_an_inconclusive_result() {
    let producer = checked(&base(), PAYLOAD);
    let options = KVMap::new();
    let root = producer.engine.logical_root(&options);
    let mut starved = limits();
    starved.kernel.steps = 0;
    let result = producer
        .engine
        .check_source_files(
            &[GENERATE.as_bytes()],
            &options,
            SourceCheckLimits::new(starved),
        )
        .map(|outcome| outcome.map_complete(|_| ()));
    assert!(matches!(result, Ok(Outcome::Inconclusive(_))), "{result:?}");
    assert_eq!(root, producer.engine.logical_root(&options));
    assert!(
        !producer
            .engine
            .environment()
            .contains(&name("Payload.ctorIdx"))
    );
}

#[test]
fn an_explicit_request_reports_missing_bootstrap_support() {
    let seed = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let producer = checked(
        &seed,
        "inductive Early where | left (n : Nat) | right (n : Nat)",
    );
    let error = rejected(&producer.engine, "attribute [gen_constructor_elims] Early");
    assert_eq!(error.disposition(), ("capability", false, 5));
    assert!(
        !producer
            .engine
            .environment()
            .contains(&name("Early.ctorElim"))
    );
}

#[test]
fn the_real_prelude_bool_target_and_late_command_generate_the_enum_auxiliaries() {
    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let end_marker = "export Bool (false true)";
    let end = prelude.find(end_marker).unwrap() + end_marker.len();
    let command = "attribute [gen_constructor_elims] Bool";
    assert!(prelude.contains(command));
    // Keep the actual early Prelude target unchanged. Supply ordinary checked
    // support definitions before replaying its real late attribute; unrelated
    // intervening Prelude commands are outside this focused source test.
    let support = "\n\
        structure PULift.{r, s} (α : Sort s) : Sort (max s r 1) where\n\
          up ::\n\
          down : α\n\
        @[match_pattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a\n\
        @[symm] theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a := h ▸ rfl\n\
        set_option genCtorIdx false in\n\
        inductive Nat where | zero : Nat | succ (n : Nat) : Nat\n\
        @[macro_inline] def cond {α : Sort u} (c : Bool) (x y : α) : α :=\n\
          match c with | true => x | false => y\n\
        def Nat.ble : Nat → Nat → Bool\n\
          | zero, _ => true\n\
          | succ _, zero => false\n\
          | succ n, succ m => ble n m\n";
    let source = format!(
        "{}{support}{command}\n\
         theorem falseIndex : Eq (Bool.ctorIdx false) Nat.zero := Eq.refl Nat.zero\n\
         theorem trueIndex : Eq (Bool.ctorIdx true) (Nat.succ Nat.zero) := Eq.refl (Nat.succ Nat.zero)\n\
         def falseValue : Nat := Bool.false.elim false (Eq.refl Nat.zero) Nat.zero\n\
         theorem falseValueComputes : Eq falseValue Nat.zero := Eq.refl Nat.zero\n",
        &prelude[..end],
    );
    let module = name("Init.Prelude");
    let result = Engine::builder()
        .build_empty()
        .compile_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    let engine = &result.checked.checked.engine;
    generated(engine, "Bool", &["false", "true"]);
    let deprecations = fln_elab::deprecations::Deprecations::read(engine.environment()).unwrap();
    let alias = deprecations.get(&name("Bool.toCtorIdx")).unwrap();
    assert_eq!(alias.new_name, Some(name("Bool.ctorIdx")));
    assert_eq!(alias.since.as_deref(), Some("2025-08-25"));
}
