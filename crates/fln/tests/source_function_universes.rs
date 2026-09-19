//! Function arguments infer their domain and codomain universes independently.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};
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
fn check(engine: &Engine, source: &str) {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both source admission seats must complete");
}
#[test]
fn independent_function_universes_are_not_paired_by_normal_form_sort_order() {
    let engine = engine();
    for universes in ["u,v", "v,u", "small,large", "right,left"] {
        let (u, v) = universes.split_once(',').unwrap();
        check(
            &engine,
            &format!(
                r#"
            def call.{{{u},{v}}} {{A : Type {u}}} {{B : Type {v}}} (f : A -> B) (a : A) : B := f a
            theorem call_ok.{{{u},{v}}} {{A : Type {u}}} {{B : Type {v}}} (f : A -> B) (a : A) :
                call f a = f a := by rfl
        "#
            ),
        );
    }
}
#[test]
fn dependent_function_bodies_keep_their_opened_local_context() {
    check(
        &engine(),
        r#"
        def dependent.{u,v} {A : Type u} {B : A -> Type v} (f : (a : A) -> B a) (a : A) : B a := f a
        theorem dependent_ok.{u,v} {A : Type u} {B : A -> Type v} (f : (a : A) -> B a) (a : A) :
            dependent f a = f a := by rfl
        def twice.{u} {A : Type u} (f : A -> A) (a : A) : A := f (f a)
        theorem concrete : twice Nat.succ 40 = 42 := by rfl
    "#,
    );
}
#[test]
fn nested_function_arguments_and_sort_valued_results_infer_without_ascriptions() {
    check(
        &engine(),
        r#"
        def call.{u,v} {A : Type u} {B : Type v} (f : A -> B) (a : A) : B := f a
        theorem output_type : call (fun (n : Nat) => Nat) 1 = Nat := by rfl
        theorem returned_function : call (fun (n : Nat) => Nat.succ) 1 41 = 42 := by rfl
        theorem nested : call (call (fun (n : Nat) => Nat.succ) 1) 41 = 42 := by rfl
    "#,
    );
}
#[test]
fn function_type_errors_and_resource_stops_do_not_publish_or_poison_recovery() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    for text in [
        "def bad (f : Nat -> Nat) : Bool -> Bool := f",
        "def bad.{u,v} {A : Type u} {B : Type v} (f : A -> A) : B -> B := f",
        "theorem bad : (fun (n : Nat) => Nat.succ n) 1 = 1 := by rfl",
    ] {
        assert!(
            engine
                .check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{text}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let stopped = engine.check_source_files(
        &[b"def stopped (f : Nat -> Nat) : Nat := f 1"],
        &KVMap::new(),
        low,
    );
    match stopped {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("resource stop became a verdict: {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    check(
        &engine,
        "theorem recovered : (fun (n : Nat) => Nat.succ n) 41 = 42 := by rfl",
    );
}
