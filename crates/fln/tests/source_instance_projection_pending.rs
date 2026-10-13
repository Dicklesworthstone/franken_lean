//! Pending candidate dictionaries preserve the original dependent application.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("source admission must complete")
        .engine
}

fn base() -> Engine {
    with_receiver(true)
}

fn with_receiver(registered: bool) -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = "class PendingCarrier (f : Nat -> Nat) where
           value : Nat
         instance chosen (f : Nat -> Nat) : PendingCarrier f := { value := f 1 }
         class PendingMark (f : Nat -> Nat) (n : Nat) where
           value : Nat
         instance marked (f : Nat -> Nat) [c : PendingCarrier f] :
           PendingMark f (@PendingCarrier.value f c) := { value := 42 }";
    if registered {
        checked(&seed, source)
    } else {
        // Keep the same checked dictionary and instances transparency, without
        // installing its instance registration. Reducibility is set in the
        // defining file, just as it is by the instance command above.
        let source = source.replacen("instance chosen", "def chosen", 1);
        checked(
            &seed,
            &format!("{source}\nattribute [implicit_reducible] chosen"),
        )
    }
}

const INFERRED: &str = "def inferred (f : Nat -> Nat) : PendingMark f (f 1) := inferInstance";

#[test]
fn a_candidate_projection_synthesizes_its_receiver_before_application_congruence() {
    let base = base();
    // Kernel-check the explicit dictionary independently of search, then require
    // synthesis to find that same term while matching the dependent result.
    let base = checked(
        &base,
        "def explicit (f : Nat -> Nat) : PendingMark f (f 1) := @marked f (chosen f)",
    );
    let result = checked(
        &base,
        &format!(
            "{INFERRED}
             theorem same (f : Nat -> Nat) : inferred f = explicit f := by rfl"
        ),
    );
    let source = "def result : Nat :=
      @PendingMark.value (fun n : Nat => n + 1) 2 (inferred (fun n : Nat => n + 1))\n#eval result";
    let executed = result
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("the selected checked dictionary executes");
    assert_eq!(executed.batch.source_evaluation_indices.len(), 1);
    let index = executed.batch.source_evaluation_indices[0];
    let fln::VmExit::Returned(returned) = &executed.batch.executions[index].exit else {
        panic!("the dictionary field must return a Nat");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some("42")
    );
}

#[test]
fn failed_projection_search_keeps_the_environment_atomic_and_preserves_resource_stops() {
    let base = with_receiver(false);
    let root = base.logical_root(&KVMap::new());
    let source = "def provisional (f : Nat -> Nat) : PendingMark f (f 1) := @marked f (chosen f)\ndef rejected (f : Nat -> Nat) : PendingMark f (f 1) := inferInstance";
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err("the missing receiver instance must remain a synthesis failure");
    assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
    assert!(
        matches!(error, fln::SourceCheckError::Command { command: 1, .. }),
        "the valid preceding definition must complete: {error:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    for name in ["provisional", "rejected"] {
        assert!(!base.environment().contains(&Name::from_components([name])));
    }
    // Installing the already admitted receiver dictionary makes this same
    // inference succeed after the failed batch, with no provisional declaration.
    let base = checked(&base, "attribute [instance] chosen");
    checked(&base, INFERRED);
    let root = base.logical_root(&KVMap::new());
    let mut stopped = 0;
    for steps in [100, 1_000] {
        let mut low = limits();
        low.admission.kernel = low.admission.kernel.narrowed(steps, 256);
        match base.check_source_files(&[INFERRED.as_bytes()], &KVMap::new(), low) {
            Ok(fln::Outcome::Inconclusive(_)) => stopped += 1,
            Err(error) => {
                assert!(
                    matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
                    "steps={steps}: {error:?}"
                );
                stopped += 1;
            }
            Ok(fln::Outcome::Complete(_)) => {}
            other => panic!("search must preserve the resource outcome: {other:?}"),
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    assert!(stopped > 0);
}

#[test]
fn a_function_valued_candidate_dictionary_is_synthesized_before_its_projected_field() {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let base = checked(
        &seed,
        "class IndexedCarrier (f : Nat -> Nat) (n : Nat) where
           value : Nat
         instance indexedChosen (f : Nat -> Nat) (n : Nat) : IndexedCarrier f n :=
           { value := f 1 }
         class IndexedMark (f : Nat -> Nat) (n : Nat) where
           value : Nat
         instance indexedMarked (f : Nat -> Nat) [c : (n : Nat) -> IndexedCarrier f n] :
           IndexedMark f (@IndexedCarrier.value f 0 (c 0)) := { value := 42 }",
    );
    let base = checked(
        &base,
        "def explicit (f : Nat -> Nat) : IndexedMark f (f 1) :=
           @indexedMarked f (indexedChosen f)",
    );
    checked(
        &base,
        "def inferred (f : Nat -> Nat) : IndexedMark f (f 1) := inferInstance
         theorem same (f : Nat -> Nat) : inferred f = explicit f := by rfl
         theorem computes :
           @IndexedMark.value (fun n : Nat => n + 1) 2 (inferred (fun n : Nat => n + 1)) = 42 := by rfl",
    );
}
