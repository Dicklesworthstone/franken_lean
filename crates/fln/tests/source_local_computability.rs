//! Public executable wrappers may call earlier hidden local implementations.
//! Logical checking retains the public headers; dependency analysis alone sees
//! the checked private predecessor and its exact executable import closure.
#![forbid(unsafe_code)]

use fln::source_check::SourceCheckError;
use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput, OleanWriteBudget,
    Outcome, SourceCheckLimits, SourceModuleInput, VmExit,
};
use fln_elab::source::SourceInferenceError;
use fln_elab::{NatDefinitionElabError, NatDefinitionFrontendError};

const TOKEN: &str = "public inductive Token where\n| left\n| right\n";
const BASE: &str = "module\nprelude\npublic inductive Token where\n| left\n| right\npublic def importedBody : Token := Token.right\n";
const WRAPPER: &str =
    "public def hiddenBody : Token := secret\n@[expose] public def wrapper : Token := hiddenBody\n";

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 << 20),
    )))
}

fn api(imported: bool) -> String {
    let prefix = if imported {
        "module\nprelude\npublic import Base\nprivate def secret : Token := importedBody\n"
            .to_owned()
    } else {
        format!("module\nprelude\n{TOKEN}private def secret : Token := Token.right\n")
    };
    format!("{prefix}{WRAPPER}")
}

fn check_api(
    base: &Engine,
    source: &str,
    imported: bool,
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let name = n("Api");
    let base_name = n("Base");
    let mut files = vec![SourceModuleInput {
        name: &name,
        source: source.as_bytes(),
    }];
    if imported {
        files.push(SourceModuleInput {
            name: &base_name,
            source: BASE.as_bytes(),
        });
    }
    base.check_source_modules(&files, &name, &KVMap::new(), limits())
}

fn inference(error: SourceModuleCheckError) -> SourceInferenceError {
    let SourceModuleCheckError::Source {
        module,
        error: SourceCheckError::Command { error, .. },
    } = error
    else {
        panic!("expected a checked source command refusal, got {error:?}")
    };
    assert_eq!(module, n("Api"));
    let mut error = *error;
    loop {
        match error {
            EngineExecutionError::BatchCommand { error: inner, .. } => error = *inner,
            EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
                NatDefinitionElabError::Inference(error),
            )) => return error,
            other => panic!("expected a source inference refusal, got {other:?}"),
        }
    }
}

fn assert_right(exit: &VmExit) {
    let VmExit::Returned(returned) = exit else {
        panic!("expected a constructor result, got {exit:?}")
    };
    assert!(!returned.value.is_scalar());
    assert_eq!(returned.value.header().tag, 1);
}

fn execute_wrapper(imported: bool) {
    let initial = Engine::builder().build_empty();
    let source = api(imported);
    let name = n("Api");
    let base = n("Base");
    let mut inputs = vec![SourceModuleInput {
        name: &name,
        source: source.as_bytes(),
    }];
    if imported {
        inputs.push(SourceModuleInput {
            name: &base,
            source: BASE.as_bytes(),
        });
    }
    let built = initial
        .compile_source_modules(
            &inputs,
            &name,
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    let artifacts: Vec<_> = built
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
    let receipt = initial
        .import_olean_modules_for_source(
            &artifacts,
            &[name],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                4 << 20,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let main = n("Main");
    let program = receipt
        .execute_source_modules(
            &[SourceModuleInput {
                name: &main,
                source: b"module\nprelude\npublic import Api\n#eval wrapper\n#eval (fun x : Token => x) wrapper\n",
            }],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(EngineExecutionLimits::new(limits().source.admission.kernel)),
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let batch = &program.modules.last().unwrap().commands.batch;
    assert_eq!(batch.source_evaluation_indices.len(), 2);
    for &index in &batch.source_evaluation_indices {
        let execution = &batch.executions[index];
        assert_right(&execution.exit);
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        assert_right(&replay);
    }
    let environment = batch.engine.environment();
    assert!(matches!(
        environment.find(&n("hiddenBody")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(matches!(
        environment.find(&n("wrapper")),
        Some(ConstantInfo::Defn(_))
    ));
    let secret = Name::num(n("_private.Api"), 0).append_core(&n("secret"));
    assert!(!environment.contains(&secret));
    if imported {
        assert!(matches!(
            environment.find(&n("importedBody")),
            Some(ConstantInfo::Axiom(_))
        ));
    }
    assert!(initial.environment().is_empty());
}

#[test]
fn exposed_definition_uses_earlier_hidden_local_body_and_replays() {
    execute_wrapper(false);
}

#[test]
fn exposed_definition_combines_hidden_local_and_imported_bodies() {
    execute_wrapper(true);
}

#[test]
fn compiler_view_does_not_make_hidden_local_bodies_logically_reducible() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    for imported in [false, true] {
        let prefix = api(imported);
        check_api(&initial, &prefix, imported)
            .unwrap()
            .into_complete()
            .unwrap();
        let source = format!(
            "{prefix}@[expose] public def leak (P : Token -> Type) (x : P Token.right) : P wrapper := x\n"
        );
        let error = inference(check_api(&initial, &source, imported).unwrap_err());
        let SourceInferenceError::ConversionRefused(verdict) = error else {
            panic!("public conversion must remain opaque: {error:?}");
        };
        assert!(
            matches!(
                verdict.as_ref(),
                fln_kernel::verdict::Verdict::Rejected {
                    class: fln::RejectClass::NotDefEq,
                    ..
                }
            ),
            "the negative control must be a completed conversion refusal: {verdict:?}"
        );
        assert_eq!(initial.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn local_noncomputable_and_bodyless_dependencies_remain_refused() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    for unavailable in [
        "public noncomputable def hiddenBody : Token := Token.right\n",
        "public axiom hiddenBody : Token\n",
    ] {
        let prefix = format!("module\nprelude\n{TOKEN}{unavailable}");
        check_api(&initial, &prefix, false)
            .unwrap()
            .into_complete()
            .unwrap();
        let source = format!("{prefix}@[expose] public def wrapper : Token := hiddenBody\n");
        assert!(matches!(
            inference(check_api(&initial, &source, false).unwrap_err()),
            SourceInferenceError::NoncomputableDependency(name) if name == n("hiddenBody")
        ));
        assert_eq!(initial.logical_root(&KVMap::new()), root);
    }
}
