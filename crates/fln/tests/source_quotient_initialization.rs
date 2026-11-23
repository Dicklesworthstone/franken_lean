//! `init_quot` creates the native checked primitives from source, without a seed.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImport;
use fln::source_check::modules::{SourceModuleCheckLimits, execution::SourceProgramLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits,
    EvaluationPresentation, KVMap, Name, OleanCheckLimits, OleanModuleInput, OleanWriteBudget,
    Outcome, SourceCheckLimits, SourceModuleInput, VmExit,
};
use fln_env::constants::{ConstantInfo, QuotKind};
use fln_kernel::Declaration;

const EQ: &str =
    "universe u\ninductive Eq {α : Sort u} : α → α → Prop where\n  | refl (a : α) : Eq a a\n";
const BETA: &str = "theorem quotientBeta.{quotU,quotV} {A : Sort quotU} {r : A → A → Prop} {B : Sort quotV} (f : A → B) (h : (a b : A) → r a b → Eq (f a) (f b)) (a : A) : Eq (Quot.lift f h (Quot.mk r a)) (f a) := Eq.refl (f a)\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn checked(base: &Engine, source: &str) -> fln::source_check::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
}

fn equality() -> Engine {
    checked(&Engine::builder().build_empty(), EQ).engine
}

fn quartet(engine: &Engine) {
    for (text, kind) in [
        ("Quot", QuotKind::Type),
        ("Quot.mk", QuotKind::Ctor),
        ("Quot.lift", QuotKind::Lift),
        ("Quot.ind", QuotKind::Ind),
    ] {
        assert!(
            matches!(engine.environment().find(&name(text)),
            Some(ConstantInfo::Quot(value)) if value.kind == kind),
            "{text}"
        );
    }
    assert!(!engine.environment().contains(&name("Quot.sound")));
}

#[test]
fn direct_command_retains_one_atomic_quartet_admission_and_no_sound_axiom() {
    let base = equality();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let result = base
        .admit_source_command(
            b"/- primitive initialization -/ init_quot",
            &options,
            admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(result.admissions.as_slice(), [admitted]
        if matches!(&admitted.declaration, Declaration::Quotient(rows) if rows.len() == 4)));
    quartet(&result.engine);
    checked(&result.engine, BETA);
    assert_eq!(base.logical_root(&options), root);
    assert!(!base.environment().contains(&name("Quot")));
    for bad in [
        "init_quot extra",
        "private init_quot",
        "init_quot init_quot",
    ] {
        assert!(
            base.admit_source_command(bad.as_bytes(), &options, admission())
                .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn namespace_and_section_variables_do_not_change_the_primitive_types_or_names() {
    let base = equality();
    let canonical = checked(&base, "init_quot");
    let nested = checked(
        &base,
        "namespace Nested\nsection\nvariable (P : Prop) (h : P)\ninclude h\ninit_quot\ntheorem saved : P := h\nend\nend Nested",
    );
    quartet(&nested.engine);
    for text in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] {
        assert_eq!(
            canonical.engine.environment().find(&name(text)),
            nested.engine.environment().find(&name(text))
        );
        assert!(
            !nested
                .engine
                .environment()
                .contains(&name(&format!("Nested.{text}")))
        );
    }
    assert!(nested.engine.environment().contains(&name("Nested.saved")));
    checked(&nested.engine, BETA);
}

#[test]
fn missing_or_noninductive_equality_and_name_collisions_cannot_publish_a_prefix() {
    let empty = Engine::builder().build_empty();
    let axiom = checked(&empty, "axiom Eq.{u} {A : Sort u} : A → A → Prop").engine;
    let base = equality();
    let initialized = checked(&base, "init_quot").engine;
    let type_collision = checked(&base, "axiom Quot : Prop").engine;
    let lift_collision = checked(&base, "axiom Quot.lift : Prop").engine;
    for engine in [
        &empty,
        &axiom,
        &initialized,
        &type_collision,
        &lift_collision,
    ] {
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let length = engine.environment().len();
        assert!(
            engine
                .admit_source_command(b"init_quot", &options, admission())
                .is_err()
        );
        assert!(
            engine
                .check_source_files(
                    &[b"init_quot"],
                    &options,
                    SourceCheckLimits::new(admission())
                )
                .is_err()
        );
        assert_eq!(engine.logical_root(&options), root);
        assert_eq!(engine.environment().len(), length);
    }
    // The pin panics (despite exit 0) on duplicate primitive names. These are
    // native atomic refusal controls, not claims of a clean oracle rejection.
    assert!(!lift_collision.environment().contains(&name("Quot")));
    assert!(!lift_collision.environment().contains(&name("Quot.mk")));
}

#[test]
fn checker_exhaustion_stays_a_nonanswer_and_leaves_no_primitives() {
    let base = equality();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut starved = admission();
    starved.checker.admission.conversion.quick.max_comparisons = 0;
    let error = base
        .admit_source_command(b"init_quot", &options, starved)
        .unwrap_err();
    assert!(
        matches!(&error, EngineExecutionError::BatchCommand { index: 0, error, .. }
        if matches!(error.as_ref(), EngineExecutionError::CouncilNoAnswer { .. })),
        "{error:?}"
    );
    let error = base
        .check_source_files(&[b"init_quot"], &options, SourceCheckLimits::new(starved))
        .unwrap_err();
    assert_eq!(error.disposition(), ("inconclusive", false, 3));
    assert_eq!(base.logical_root(&options), root);
    assert!(!base.environment().contains(&name("Quot")));
}

#[test]
fn module_private_sections_still_export_the_quartet_and_reimport_checked_primitives() {
    let initial = Engine::builder().build_empty();
    let library = name("Quotients");
    let main = name("Main");
    let source = format!(
        "module\nprelude\n{}section\nvariable (P : Prop) (h : P)\ninclude h\ninit_quot\ntheorem saved : P := h\nend\n",
        EQ.replace("inductive Eq", "public inductive Eq")
    );
    let consumer = format!("module\nprelude\npublic import Quotients\npublic {BETA}");
    let limits = SourceModuleCheckLimits::new(SourceCheckLimits::new(admission()));
    let build = initial
        .compile_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &main,
                    source: consumer.as_bytes(),
                },
            ],
            &main,
            &KVMap::new(),
            limits,
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    quartet(&build.checked.checked.engine);
    let inputs: Vec<_> = build
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.server.as_slice()),
            private_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.private.as_slice()),
        })
        .collect();
    let readmitted = initial
        .check_olean_modules(
            &inputs,
            &KVMap::new(),
            OleanCheckLimits::new(4 * 1024 * 1024, admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    quartet(&readmitted.engine);
    assert!(
        readmitted
            .engine
            .environment()
            .contains(&name("quotientBeta"))
    );
    assert!(initial.environment().is_empty());
    let hidden_eq = format!("module\nprelude\n{EQ}init_quot\n");
    assert!(
        initial
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &main,
                    source: hidden_eq.as_bytes()
                }],
                &main,
                &KVMap::new(),
                limits,
                OleanWriteBudget::default(),
            )
            .is_err()
    );
    assert!(initial.environment().is_empty());
}

#[test]
fn source_initialized_quotient_lift_executes_on_the_native_vm_without_a_seed() {
    let options = KVMap::new();
    let initial = SourceOleanImport::empty(&options);
    let main = name("Main");
    let source = format!(
        "prelude\nunsafe axiom lcAny : Type\nunsafe axiom lcErased : Type\nunsafe axiom lcVoid : Type\n{EQ}inductive Color where | red | blue\ninit_quot\n#eval Quot.lift (fun (c : Color) => c) (fun (a b : Color) (h : Eq a b) => h) (Quot.mk (fun (a b : Color) => Eq a b) Color.blue)\n"
    );
    // The raw presentation exposes the returned value directly, without asking
    // a minimal source library to supply the standard Repr printing instances.
    let run = initial
        .execute_lean_source_modules_with_presentation(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
            &options,
            SourceProgramLimits::new(EngineExecutionLimits::new(admission().kernel)),
            None,
            EvaluationPresentation::Raw,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let batch = &run.modules[0].commands.batch;
    quartet(&batch.engine);
    assert_eq!(batch.executions.len(), 1);
    let VmExit::Returned(value) = &batch.executions[0].exit else {
        panic!("native quotient lift did not return")
    };
    // The checked result is the second constructor of Color, a heap value
    // outside the scalar/String projection exposed by closed_vm_value.
    assert!(!value.value.is_scalar());
    assert_eq!(value.value.header().tag, 1);
    assert!(initial.engine.environment().is_empty());
}

#[test]
fn untouched_prelude_bootstraps_through_quotient_initialization_from_empty() {
    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let end = prelude
        .find("\ninit_quot\n")
        .expect("pinned initialization command")
        + "\ninit_quot\n".len();
    let source = format!("{}\n{BETA}", &prelude[..end]);
    let initial = Engine::builder().build_empty();
    let main = name("Init.Prelude");
    let result = initial.compile_source_modules(
        &[SourceModuleInput {
            name: &main,
            source: source.as_bytes(),
        }],
        &main,
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        OleanWriteBudget::default(),
    );
    assert!(matches!(result, Ok(Outcome::Complete(_))), "{result:?}");
    quartet(
        &result
            .unwrap()
            .into_complete()
            .unwrap()
            .checked
            .checked
            .engine,
    );
    assert!(initial.environment().is_empty());
}
