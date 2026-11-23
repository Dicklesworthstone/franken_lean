//! Declaration admission and source-module compiler eligibility are distinct.
//! The signature controls target the pinned Reference compiler at
//! 8c9756b28d64dab099da31a4c09229a9e6a2ef35; import and budget tests also
//! verify native authority isolation and resource-error classification.

#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckError;
use fln::source_check::modules::execution::{SourceProgramExecution, SourceProgramLimits};
use fln::source_check::modules::imported::SourceOleanImport;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, EvaluationPresentation, KVMap,
    Name, Outcome, SourceCheckLimits, SourceModuleInput,
};

const POLY: &str = "universe u\ndef ident (A : Type u) (x : A) : A := x\n";
const ENUM: &str = "inductive E where\n | a\n | b\n";
const MARKERS: &str = "axiom lcAny : Type\naxiom lcErased : Type\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn run(
    source: &str,
    limits: EngineExecutionLimits,
) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
    let entry = name("Main");
    SourceOleanImport::empty(&KVMap::new()).execute_lean_source_modules_with_presentation(
        &[SourceModuleInput {
            name: &entry,
            source: source.as_bytes(),
        }],
        &entry,
        &KVMap::new(),
        SourceProgramLimits::new(limits),
        None,
        EvaluationPresentation::Lean,
    )
}

fn accepted(source: &str) {
    let result = run(source, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("{source}\n{reason:?}"));
    assert_eq!(result.modules.len(), 1);
    assert!(result.modules[0].commands.batch.executions.is_empty());
}

fn missing(source: &str, marker: &str) {
    let error = run(source, limits()).expect_err("missing compiler prerequisite must fail");
    assert_eq!(error.disposition(), ("compilation", false, 1), "{error:?}");
    assert!(
        error.to_string().contains(&format!("Unknown constant `{marker}`")),
        "{source}\n{error:?}",
    );
}

#[test]
fn executable_polymorphism_requires_each_actual_marker() {
    missing(&format!("prelude\n{POLY}"), "lcAny");
    missing(&format!("prelude\naxiom lcAny : Type\n{POLY}"), "lcErased");
    missing(&format!("prelude\naxiom lcErased : Type\n{POLY}"), "lcAny");
    accepted(&format!("prelude\n{MARKERS}{POLY}"));
    missing(
        &format!("prelude\n{ENUM}def f (A : Type) : E := E.a\n"),
        "lcErased",
    );
    missing(
        &format!("prelude\n{ENUM}axiom A : Type\ndef f (a : A) : E := E.a\n"),
        "lcAny",
    );
}

#[test]
fn noncomputable_sections_record_only_actual_compiler_failures() {
    for (header, declaration) in [
        ("prelude\n", "def ident"),
        ("module\nprelude\n", "public def ident"),
    ] {
        let source = format!(
            "{header}universe u\nnoncomputable section\n{declaration} (A : Type u) (x : A) : A := x\nend\n",
        );
        let completed = run(&source, limits()).unwrap().into_complete().unwrap();
        let engine = &completed.modules[0].commands.batch.engine;
        assert!(
            fln_elab::noncomputable::read(engine.environment())
                .unwrap()
                .contains(&name("ident")),
            "{source}",
        );
    }
    for source in [
        format!("prelude\n{MARKERS}noncomputable section\n{POLY}end\n"),
        format!("prelude\n{ENUM}noncomputable section\ndef ident (e : E) : E := e\nend\n"),
    ] {
        let completed = run(&source, limits()).unwrap().into_complete().unwrap();
        assert!(
            !fln_elab::noncomputable::read(
                completed.modules[0].commands.batch.engine.environment()
            )
            .unwrap()
            .contains(&name("ident")),
            "{source}",
        );
    }
    let use_outside = format!(
        "prelude\n{ENUM}noncomputable section\n{POLY}end\ndef value : E := ident E E.a\n",
    );
    let error = run(&use_outside, limits()).expect_err("the retained tag blocks later codegen");
    assert_eq!(error.disposition().2, 1, "{error:?}");
    assert!(error.to_string().contains("noncomputable"), "{error:?}");

    let mut constrained = limits();
    constrained.ingress.max_nodes = 0;
    let source = format!("prelude\nnoncomputable section\n{POLY}end\n");
    let error = run(&source, constrained).expect_err("section cannot suppress resource exhaustion");
    assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
}

#[test]
fn public_section_compiler_effects_replay_into_importing_modules() {
    let receipt = SourceOleanImport::empty(&KVMap::new());
    let library = name("Library");
    let main = name("Main");
    let library_source = b"module\nprelude\nuniverse u\nnoncomputable section\npublic def ident (A : Type u) (x : A) : A := x\nend\n";
    let outcome = receipt
        .execute_lean_source_modules_with_presentation(
            &[
                SourceModuleInput {
                    name: &library,
                    source: library_source,
                },
                SourceModuleInput {
                    name: &main,
                    source: b"prelude\nimport Library\n",
                },
            ],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(limits()),
            None,
            EvaluationPresentation::Lean,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for module in &outcome.modules {
        let environment = module.commands.batch.engine.environment();
        assert!(environment.contains(&name("ident")), "{module:?}");
        assert!(
            fln_elab::noncomputable::read(environment)
                .unwrap()
                .contains(&name("ident")),
            "{module:?}",
        );
    }
}

#[test]
fn only_extern_axioms_request_compilation_of_their_signature() {
    let external = "universe u\n@[extern \"poly_ext\"] axiom ext (A : Type u) (x : A) : A\n";
    missing(&format!("prelude\n{external}"), "lcErased");
    accepted(&format!("prelude\n{MARKERS}{external}"));
    accepted("prelude\nuniverse u\naxiom ext (A : Type u) (x : A) : A\n");
}

#[test]
fn proof_typeformer_and_ignored_polymorphic_parameters_require_erasure() {
    for declaration in [
        "axiom P : Prop\ndef f (p : P) : E := E.a\n",
        "def f (g : E → Type) : E := E.a\n",
        "universe u\ndef f (A : Type u) (x : A) : E := E.a\n",
    ] {
        missing(&format!("prelude\n{ENUM}{declaration}"), "lcErased");
    }
}

#[test]
fn only_generated_recursor_metadata_exempts_auxiliary_wrappers() {
    accepted(&format!("prelude\n{ENUM}#check E.recOn\n"));
    missing(
        "prelude\nuniverse u\nnamespace User\ndef recOn (A : Type u) (x : A) : A := x\nend User\n",
        "lcAny",
    );
}

#[test]
fn proofs_noncomputable_and_concrete_entries_remain_admissible() {
    for source in [
        "prelude\nuniverse u\nnoncomputable def ident (A : Type u) (x : A) : A := x\n".to_owned(),
        "prelude\ntheorem ident (P : Prop) (x : P) : P := x\n".to_owned(),
        "prelude\ndef ident (A : Type) : Type := A\n".to_owned(),
        format!("prelude\n{ENUM}def ident (e : E) : E := e\n"),
        format!("prelude\n{ENUM}def value : E := E.a\n"),
    ] {
        accepted(&source);
    }
}

#[test]
fn closure_parameters_and_eliminated_body_binders_do_not_require_markers() {
    accepted(&format!(
        "prelude\n{ENUM}axiom A : Type\ndef f (g : E → A) (e : E) : E := e\n"
    ));
    accepted(&format!(
        "prelude\n{ENUM}def f : E := (fun (A : Type) (x : A) => E.a) E E.a\n"
    ));
}

#[test]
fn public_module_declarations_observe_the_same_compiler_boundary() {
    missing(
        "module\nprelude\nuniverse u\npublic def ident (A : Type u) (x : A) : A := x\n",
        "lcAny",
    );
}

#[test]
fn logical_checking_and_raw_command_apis_do_not_gain_a_codegen_requirement() {
    let base = Engine::builder().build_empty();
    let checked = base
        .check_source_files(
            &[POLY.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(checked.engine.environment().contains(&name("ident")));
    assert!(!base.environment().contains(&name("ident")));
    let executed = base
        .execute_source_commands_with_presentation(
            POLY.as_bytes(),
            &KVMap::new(),
            limits(),
            EvaluationPresentation::Lean,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(executed.batch.engine.environment().contains(&name("ident")));
    assert!(executed.batch.executions.is_empty());
}

#[test]
fn admitted_marker_imports_are_isolated_from_sibling_modules_and_failed_retries() {
    let receipt = SourceOleanImport::empty(&KVMap::new());
    let markers = name("Markers");
    let consumer = name("Consumer");
    let main = name("Main");
    let marker_source = format!("prelude\n{MARKERS}");
    let entry = b"prelude\nimport Markers\nimport Consumer\n";
    for imports_markers in [false, true, false] {
        let consumer_source = format!(
            "prelude\n{}{POLY}",
            if imports_markers { "import Markers\n" } else { "" },
        );
        let outcome = receipt.execute_lean_source_modules_with_presentation(
            &[
                SourceModuleInput {
                    name: &markers,
                    source: marker_source.as_bytes(),
                },
                SourceModuleInput {
                    name: &consumer,
                    source: consumer_source.as_bytes(),
                },
                SourceModuleInput {
                    name: &main,
                    source: entry,
                },
            ],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(limits()),
            None,
            EvaluationPresentation::Lean,
        );
        if imports_markers {
            let completed = outcome.unwrap().into_complete().unwrap();
            let environment = completed.modules.last().unwrap().commands.batch.engine.environment();
            assert!(environment.contains(&name("ident")));
            assert!(environment.contains(&name("lcAny")));
            assert!(environment.contains(&name("lcErased")));
        } else {
            let error = outcome.expect_err("a sibling's markers are not imported");
            assert_eq!(error.disposition(), ("compilation", false, 1), "{error:?}");
            assert!(error.to_string().contains("lcAny"), "{error:?}");
            assert!(error.to_string().contains("Consumer"), "{error:?}");
        }
        assert!(!receipt.engine.environment().contains(&name("ident")));
        assert!(!receipt.engine.environment().contains(&name("lcAny")));
    }
}

#[test]
fn resource_exhaustion_during_signature_analysis_is_a_nonanswer() {
    let mut constrained = limits();
    constrained.ingress.max_nodes = 0;
    let source = format!("prelude\n{POLY}");
    let error = run(&source, constrained).expect_err("analysis has no work budget");
    assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
    assert!(!error.to_string().contains("Unknown constant"), "{error:?}");
    missing(&source, "lcAny");
    accepted(&format!("prelude\n{MARKERS}{POLY}"));
}
