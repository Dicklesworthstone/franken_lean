//! Mutual partial groups preserve every checked interface and companion at module boundaries.
#![forbid(unsafe_code)]
use fln::source_check::modules::{SourceModuleCheckLimits, imported::SourceOleanImportLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, OleanWriteBudget, SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(budget())))
}
const LIB: &str = r#"prelude
universe u
class Inhabited (α : Sort u) where
  default : α
def default {α : Sort u} [inst : Inhabited α] : α := Inhabited.default
inductive Flag where | stop | again
mutual
  partial def left (x : Flag) : Flag := match x with
    | Flag.stop => Flag.again
    | Flag.again => right Flag.stop
  partial def right (x : Flag) : Flag := match x with
    | Flag.stop => Flag.stop
    | Flag.again => left Flag.stop
end
mutual
  partial def keep {α : Type} (x : α) (flag : Flag) : α := match flag with
    | Flag.stop => x
    | Flag.again => relay x Flag.stop
  partial def relay {α : Type} (x : α) (flag : Flag) : α := match flag with
    | Flag.stop => x
    | Flag.again => keep x Flag.stop
end
"#;
const MAIN: &str = "prelude\nimport Lib\ndef after : Flag := left Flag.stop\ndef retained {α : Type} (x : α) : α := keep x Flag.again";
#[test]
fn mutual_companions_survive_export_reimport_and_execute_nonwitness_results() {
    let base = Engine::builder().build_empty();
    let lib = n("Lib");
    let main = n("Main");
    let build = base
        .compile_source_modules(
            &[
                SourceModuleInput {
                    name: &main,
                    source: MAIN.as_bytes(),
                },
                SourceModuleInput {
                    name: &lib,
                    source: LIB.as_bytes(),
                },
            ],
            &main,
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(build.artifacts.len(), 2);
    let inputs: Vec<_> = build
        .artifacts
        .iter()
        .map(|a| OleanModuleInput {
            name: &a.name,
            artifact: &a.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            &[main],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 * 1024 * 1024, budget())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let original = build.checked.checked.engine.environment();
    assert_eq!(imported.environment().len(), original.len());
    for (name, value) in original.constants() {
        assert_eq!(
            imported.environment().find(name),
            Some(value),
            "{}",
            name.to_display_string()
        );
    }
    for text in ["left", "right", "keep", "relay"] {
        assert!(
            matches!(imported.environment().find(&n(text)), Some(ConstantInfo::Opaque(value)) if !value.is_unsafe && value.all.len()==2)
        );
        assert!(
            matches!(imported.environment().find(&n(&format!("{text}._unsafe_rec"))), Some(ConstantInfo::Defn(value)) if value.safety==DefinitionSafety::Partial && value.all.len()==2)
        );
    }
    let execution = imported
        .execute_source_definitions(
            &[b"#eval retained after"],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let [value] = execution.executions.as_slice() else {
        panic!("one execution")
    };
    let fln::VmExit::Returned(returned) = &value.exit else {
        panic!("{value:?}")
    };
    assert_eq!(
        fln::vm_value_kind(&returned.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
    assert!(base.environment().is_empty());
}
#[test]
fn failed_safe_consumer_cannot_export_mutual_implementation_access() {
    let base = Engine::builder().build_empty();
    let lib = n("Lib");
    let main = n("Main");
    let bad = b"prelude\nimport Lib\ndef leak : Flag := left._unsafe_rec Flag.stop";
    assert!(
        base.compile_source_modules(
            &[
                SourceModuleInput {
                    name: &main,
                    source: bad
                },
                SourceModuleInput {
                    name: &lib,
                    source: LIB.as_bytes()
                }
            ],
            &main,
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default()
        )
        .is_err()
    );
    assert!(base.environment().is_empty());
}
#[test]
fn cancellation_at_group_and_module_publication_boundaries_returns_no_prefix() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    struct Stop {
        calls: AtomicUsize,
        at: usize,
    }
    impl fln::CancellationProbe for Stop {
        fn is_cancelled(&self) -> bool {
            self.calls.fetch_add(1, Ordering::Relaxed) + 1 >= self.at
        }
    }
    let base = Engine::builder().build_empty();
    let lib = n("Lib");
    let main = n("Main");
    let inputs = [
        SourceModuleInput {
            name: &main,
            source: MAIN.as_bytes(),
        },
        SourceModuleInput {
            name: &lib,
            source: LIB.as_bytes(),
        },
    ];
    let count = Stop {
        calls: AtomicUsize::new(0),
        at: usize::MAX,
    };
    base.check_source_modules_with_cancel(&inputs, &main, &KVMap::new(), limits(), Some(&count))
        .unwrap()
        .into_complete()
        .unwrap();
    let total = count.calls.load(Ordering::Relaxed);
    assert!(total > 4);
    for at in [1, total / 4, total / 2, 3 * total / 4, total] {
        let stop = Stop {
            calls: AtomicUsize::new(0),
            at,
        };
        assert!(matches!(
            base.check_source_modules_with_cancel(
                &inputs,
                &main,
                &KVMap::new(),
                limits(),
                Some(&stop)
            ),
            Ok(fln::Outcome::Inconclusive(_))
        ));
        assert!(base.environment().is_empty());
    }
    base.check_source_modules(&inputs, &main, &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
}
