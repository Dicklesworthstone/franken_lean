//! Partial source definitions survive native module export, import and cache reuse.
//! The complete fixture is checked from an empty engine; no ambient seed or pin
//! artifact is substituted for the module graph.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{
    SourceModuleBuild, SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, OleanWriteBudget, SourceCheckLimits, SourceModuleInput, VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}
fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}
fn session() -> SourceModuleSession {
    SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    )
}
const CORE: &str = r#"prelude
universe u
class Inhabited (A : Sort u) where
  default : A
def default {A : Sort u} [i : Inhabited A] : A := i.default
inductive Token where
  | off
  | on
"#;
const LIB: &str = r#"prelude
import Core
partial def turn (x : Token) : Token := match x with
  | .off => turn Token.on
  | .on => Token.on
"#;
const MAIN: &str = "prelude\nimport Lib\ndef client (x : Token) : Token := turn x\n";

fn build(session: &mut SourceModuleSession, lib: &str) -> SourceModuleBuild {
    let names = [name("Main"), name("Lib"), name("Core")];
    let sources = [MAIN, lib, CORE];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    session
        .compile_with_cancel(&inputs, &names[0], OleanWriteBudget::default(), None)
        .unwrap_or_else(|error| panic!("{lib}: {error:?}"))
        .into_complete()
        .unwrap()
}
fn imported(built: &SourceModuleBuild) -> Engine {
    let inputs: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &[name("Main")],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                4 << 20,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn assert_actual_body(engine: &Engine, tag: u8) {
    let batch = engine
        .execute_source_definitions(
            &[b"#eval client Token.off\n"],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().source.admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(batch.executions.len(), 1);
    let execution = &batch.executions[0];
    let VmExit::Returned(returned) = &execution.exit else {
        panic!("must return");
    };
    assert!(!returned.value.is_scalar());
    assert_eq!(returned.value.header().tag, tag);
    let VmExit::Returned(replayed) =
        fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
            .unwrap()
            .into_complete()
            .unwrap()
    else {
        panic!("must replay");
    };
    assert!(!replayed.value.is_scalar());
    assert_eq!(replayed.value.header().tag, tag);
    assert_eq!(returned.usage.steps, replayed.usage.steps);
}

#[test]
fn compiled_partial_pair_is_rechecked_imported_and_replayed_without_the_seed() {
    let built = build(&mut session(), LIB);
    let loaded = imported(&built);
    assert!(
        matches!(loaded.environment().find(&name("turn")), Some(ConstantInfo::Opaque(value)) if !value.is_unsafe)
    );
    assert!(
        matches!(loaded.environment().find(&name("turn._unsafe_rec")), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial)
    );
    assert_actual_body(&loaded, 1);
    assert!(
        loaded
            .check_source_files(
                &[b"def leak (x : Token) : Token := turn._unsafe_rec x\n"],
                &KVMap::new(),
                limits().source,
            )
            .is_err()
    );
}

#[test]
fn warm_cache_retains_the_pair_and_body_edits_invalidate_importers() {
    let mut session = session();
    let cold = build(&mut session, LIB);
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 3));
    let warm = build(&mut session, LIB);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (3, 0));
    for (before, after) in cold.artifacts.iter().zip(&warm.artifacts) {
        assert_eq!(before.name, after.name);
        assert_eq!(before.bytes, after.bytes);
    }
    assert_actual_body(&imported(&warm), 1);
    let edited = "prelude\nimport Core\npartial def turn (x : Token) : Token := match x with\n  | .off => Token.off\n  | .on => turn Token.off\n";
    let changed = build(&mut session, edited);
    assert_eq!((changed.reused_modules, changed.elaborated_modules), (1, 2));
    assert_actual_body(&imported(&changed), 0);
    let restored = build(&mut session, LIB);
    assert_actual_body(&imported(&restored), 1);
}
