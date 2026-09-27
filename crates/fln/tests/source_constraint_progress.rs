//! Instance fixed points must leave room for later defaulting and preserve all
//! dependent typing obligations. These are real source/council/VM paths.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
const DEPENDENT: &str = r#"
def shift (offset : Nat) (q : Quot (fun (a b : Nat) => a + offset = b + offset)) : Nat :=
  Quot.lift (fun (n : Nat) => n + offset) (fun (a b : Nat) (h : a + offset = b + offset) => h) q
#eval shift 2 (Quot.mk (fun (a b : Nat) => a + 2 = b + 2) 40)
"#;

#[test]
fn blocked_overloads_reach_defaulting_and_execute_with_the_default_budget() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let run = || {
        base.execute_source_definitions(
            &[DEPENDENT.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap()
    };
    let first = run();
    let second = run();
    for result in [&first, &second] {
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("dependent overloaded application did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn blocked_dictionary_progress_never_skips_a_later_typing_refusal() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    // The preceding valid declaration must not escape a failed file, and the
    // invalid relation witness must not be forgotten after instance progress.
    let bad = r#"
def prior : Nat := 1
def invalid (offset : Nat) (q : Quot (fun (a b : Nat) => True)) : Nat :=
  Quot.lift (fun (n : Nat) => n + offset) (fun (a b : Nat) (h : True) => h) q
"#;
    assert!(
        base.check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["prior"]))
    );
    let recovered = base
        .check_source_files(&[b"def recovery : Nat := 42"], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        recovered
            .engine
            .environment()
            .contains(&Name::from_components(["recovery"]))
    );
}
