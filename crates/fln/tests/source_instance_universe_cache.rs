//! Output-only universes reuse checked answers without becoming input filters.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn tree(depth: usize, bottom: &str, empty: bool) -> String {
    let mut source =
        format!("class U0.{{u}} (A : outParam (Sort u)) where\n  value : Nat\n{bottom}\n");
    for level in 1..=depth {
        let previous = level - 1;
        source.push_str(&format!(
            "class U{level}.{{u}} (A : outParam (Sort u)) where\n  value : Nat\n"
        ));
        if empty {
            for prefix in ["a", "b"] {
                source.push_str(&format!("instance {prefix}{level}.{{u}} {{A : Sort u}} [child : U{previous} A] : U{level} Nat := U{level}.mk child.value\n"));
            }
        } else {
            source.push_str(&format!("instance u{level}.{{u,v}} {{A : Sort u}} {{B : Sort v}} [left : U{previous} A] [right : U{previous} B] : U{level} Nat := U{level}.mk left.value\n"));
        }
    }
    source.push_str(&format!("class Answer where\n  value : Nat\ninstance fallback : Answer := Answer.mk 4\ninstance answer.{{u}} {{A : Sort u}} [dict : U{depth} A] : Answer := Answer.mk dict.value\n"));
    source
}
#[test]
fn higher_universe_diamonds_keep_checked_terms_and_execute_their_dictionary_values() {
    let base = checked(
        &seed(),
        &tree(8, "instance bottom : U0 Type := U0.mk 42", false),
    );
    let result = checked(
        &base,
        "def result : Answer := inferInstance\ntheorem correct : result.value = 42 := by rfl",
    );
    let execution = result
        .execute_source_definitions(
            &[b"#eval result.value"],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&execution.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}
#[test]
fn repeated_empty_universe_queries_finish_then_recover_after_registry_extension() {
    let base = checked(&seed(), &tree(9, "", true));
    let original = base.logical_root(&KVMap::new());
    checked(
        &base,
        "def result : Answer := inferInstance\ntheorem fallbackValue : result.value = 4 := by rfl",
    );
    checked(
        &base,
        "instance added : U0 Type := U0.mk 42\ndef result : Answer := inferInstance\ntheorem recovered : result.value = 42 := by rfl",
    );
    assert_eq!(base.logical_root(&KVMap::new()), original);
}
