//! Partial functions retain both checked halves across source and artifact boundaries.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
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

// Deliberately standalone source. Exporting an ambient source seed is forbidden;
// both the inhabitant class and the data constructors have real module provenance.
const LIB: &str = r#"prelude
universe u
class Inhabited (α : Sort u) where
  default : α
def default {α : Sort u} [inst : Inhabited α] : α := Inhabited.default
inductive Flag where
  | stop
  | again
partial def keep {α : Type} (x : α) (flag : Flag) : α :=
  match flag with
  | Flag.stop => x
  | Flag.again => keep x Flag.stop
partial def rotate (flag : Flag) : Flag :=
  match flag with
  | Flag.stop => Flag.again
  | Flag.again => rotate Flag.stop
"#;
const MAIN: &str = "prelude\nimport Lib\ndef after : Flag := rotate Flag.stop\ndef retained {α : Type} (x : α) : α := keep x Flag.again";

#[test]
fn partial_module_artifacts_reimport_and_execute_the_checked_companion() {
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
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
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
    assert!(matches!(
        imported.environment().find(&n("keep")),
        Some(ConstantInfo::Opaque(_))
    ));
    assert!(
        matches!(imported.environment().find(&n("keep._unsafe_rec")), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial)
    );
    // Source and imported extension journals have different grouping/order and
    // import provenance. Compare actual declarations and effective policy, not
    // their history-dependent whole-environment roots.
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
    assert_eq!(
        fln_elab::reducibility::ReducibilityTable::read(original).unwrap(),
        fln_elab::reducibility::ReducibilityTable::read(imported.environment()).unwrap(),
    );
    assert!(
        fln_elab::instances::InstanceRegistry::read(imported.environment())
            .unwrap()
            .is_class(&n("Inhabited"))
    );
    let execution = imported
        .execute_source_definitions(
            &[b"#eval after"],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let [value] = execution.executions.as_slice() else {
        panic!("one evaluation")
    };
    let fln::VmExit::Returned(returned) = &value.exit else {
        panic!("{value:?}")
    };
    // The logical witness returns its Flag parameter, hence would be stop (0)
    // here. Only the compiled companion returns again (1).
    assert_eq!(
        fln::vm_value_kind(&returned.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
    assert!(base.environment().is_empty());
}

#[test]
fn a_failed_partial_module_build_returns_no_artifacts() {
    let base = Engine::builder().build_empty();
    let lib = n("Lib");
    let main = n("Main");
    // A safe consumer cannot mention the recursive implementation directly.
    let broken =
        "prelude\nimport Lib\ndef leak {α : Type} (x : α) : α := keep._unsafe_rec x Flag.again";
    assert!(
        base.compile_source_modules(
            &[
                SourceModuleInput {
                    name: &main,
                    source: broken.as_bytes()
                },
                SourceModuleInput {
                    name: &lib,
                    source: LIB.as_bytes()
                }
            ],
            &main,
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .is_err()
    );
    assert!(base.environment().is_empty());
}

#[test]
fn single_declaration_doors_cannot_publish_only_one_half() {
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(budget()))
        .unwrap()
        .into_complete()
        .unwrap();
    let source = b"partial def loop (n : Nat) : Nat := loop n";
    assert!(
        base.admit_source_declaration(source, &KVMap::new(), EngineAdmissionLimits::new(budget()))
            .is_err()
    );
    assert!(!base.environment().contains(&n("loop")));
    assert!(!base.environment().contains(&n("loop._unsafe_rec")));
    let checked = base
        .check_source_files(&[source], &KVMap::new(), limits().source)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        checked
            .engine
            .environment()
            .contains(&n("loop._unsafe_rec"))
    );
}

#[test]
fn cancelled_module_replay_publishes_neither_partial_half() {
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
    assert!(total > 2);
    for at in [1, total / 2, total] {
        let stop = Stop {
            calls: AtomicUsize::new(0),
            at,
        };
        let outcome = base.check_source_modules_with_cancel(
            &inputs,
            &main,
            &KVMap::new(),
            limits(),
            Some(&stop),
        );
        assert!(matches!(outcome, Ok(fln::Outcome::Inconclusive(_))));
        assert!(base.environment().is_empty());
    }
    base.check_source_modules(&inputs, &main, &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn named_function_witnesses_reimport_without_replacing_executable_callbacks() {
    let base = Engine::builder().build_empty();
    let library = format!(
        r#"{LIB}
def Callback (A : Type) : Type := Flag -> A
partial def shift {{A : Type}} (f : Callback A) (flag : Flag) : Callback A :=
  match flag with
  | Flag.stop => fun _ => f Flag.again
  | Flag.again => shift f Flag.stop
"#
    );
    let main_source = b"prelude\nimport CallbackLib\ndef result : Flag := shift (fun x => x) Flag.again Flag.stop";
    let library_name = n("CallbackLib");
    let main_name = n("CallbackMain");
    let build = base
        .compile_source_modules(
            &[
                SourceModuleInput {
                    name: &main_name,
                    source: main_source,
                },
                SourceModuleInput {
                    name: &library_name,
                    source: library.as_bytes(),
                },
            ],
            &main_name,
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
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            &[main_name],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 * 1024 * 1024, budget())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    for name in [n("shift"), n("shift._unsafe_rec")] {
        assert_eq!(
            imported.environment().find(&name),
            build.checked.checked.engine.environment().find(&name),
        );
    }
    let execution = imported
        .execute_source_definitions(
            &[b"#eval result"],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let [value] = execution.executions.as_slice() else {
        panic!("one evaluation")
    };
    let fln::VmExit::Returned(returned) = &value.exit else {
        panic!("{value:?}")
    };
    // The checked whole-function inhabitant is f (the identity), which would
    // return stop here. The recursive implementation returns f again instead.
    assert_eq!(
        fln::vm_value_kind(&returned.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
    assert!(base.environment().is_empty());
}
