//! Domain/codomain universe constraints precede their lossy aggregate maximum.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const INTERFACES: &str = r#"
class Pure.{u,v} (f : Type u -> Type v) where
  pure : {A : Type u} -> A -> f A
class Bind.{u,v} (m : Type u -> Type v) where
  bind : {A B : Type u} -> m A -> (A -> m B) -> m B
def Id.{u} (A : Type u) : Type u := A
"#;
const INSTANCES: &str = r#"
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
"#;
const PROGRAM: &str = r#"
def choose (o : Option Nat) : Id Nat :=
  Bind.bind (m := Id) (match o with | Option.some n => Pure.pure n | Option.none => Pure.pure 0) (fun y => Pure.pure y)
theorem chosen : choose (Option.some 42) = (42 : Nat) := by rfl
theorem absent : choose Option.none = (0 : Nat) := by rfl
"#;

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn higher_kinded_instance_levels_are_inferred_without_cyclic_assignments() {
    let source = format!("{INTERFACES}{INSTANCES}{PROGRAM}");
    let engine = checked(&seed(), &source);
    for name in ["idPure", "idBind"] {
        let declaration = engine
            .environment()
            .find(&fln::Name::from_components([name]))
            .unwrap();
        let base = declaration.constant_val();
        assert_eq!(
            base.level_params.len(),
            1,
            "the common universe is generalized, not defaulted"
        );
        assert!(!base.type_.has_expr_mvar());
        assert!(!base.type_.has_level_mvar());
    }
    // Independently checked uses at different universes share no assignments.
    checked(
        &engine,
        "def higher : Id Type := Pure.pure (f := Id) Nat\ntheorem higherValue : higher = Nat := by rfl",
    );
}

#[test]
fn higher_kinded_arguments_keep_independent_input_and_output_universes() {
    checked(
        &seed(),
        r#"
        def consume.{u,v} (F : Type u -> Type v) (A : Type u) : Type v := F A
        def identityType.{u} (A : Type u) : Type u := A
        def raiseType.{u} (A : Type u) : Type (u+1) := Type u -> A
        def same : Type := consume identityType Nat
        def higher : Type 1 := consume raiseType Nat
        theorem sameValue : same = Nat := by rfl
        theorem higherValue : higher = (Type -> Nat) := by rfl
    "#,
    );
}

#[test]
fn changed_universe_order_never_admits_invalid_branches_or_instances() {
    let base = checked(&seed(), &format!("{INTERFACES}{INSTANCES}"));
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (o : Option Nat) : Id Nat := Bind.bind (m := Id) (match o with | Option.some n => Pure.pure n | Option.none => Pure.pure true) (fun y => Pure.pure y)",
        "def bad (o : Option Nat) : Id Nat := Bind.bind (m := Id) (match o with | Option.some n => Pure.pure n | Option.none => let unused := (1 : String); Pure.pure 0) (fun y => Pure.pure y)",
        "def bad (o : Option Nat) : Id Nat := Bind.bind (m := Id) (match o with | Option.some n => Pure.pure n) (fun y => Pure.pure y)",
        "instance invalid : Pure Id := { pure := fun a => true }",
        "def raiseType.{u} (A : Type u) : Type (u+1) := Type u -> A\ndef consume.{u,v} (F : Type u -> Type v) (A : Type u) : Type v := F A\ndef bad : Type := consume raiseType Nat",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let missing = checked(&seed(), INTERFACES);
    assert!(
        missing
            .check_source_files(
                &[PROGRAM.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission())
            )
            .is_err()
    );
    checked(&base, PROGRAM);
}

#[test]
fn named_monad_matches_run_after_checked_source_admission() {
    let base = checked(&seed(), &format!("{INTERFACES}{INSTANCES}{PROGRAM}"));
    let execution = base
        .execute_source_definitions(
            &[b"#eval choose (Option.some 42)\n#eval choose Option.none"],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(execution.executions.len(), 2);
    for (run, expected) in execution.executions.iter().zip(["42", "0"]) {
        let fln::VmExit::Returned(value) = &run.exit else {
            panic!("{run:?}");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn imported_monad_reaches_constructor_match_branches() {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(|| {
            use fln::source_check::modules::imported::SourceOleanImportLimits;
            use fln::{Name, OleanCheckLimits, OleanModuleInput};
            let module = Name::from_components(["Init", "Prelude"]);
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                ),
                server_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                )),
                private_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                )),
            }];
            let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(128 << 20));
            let imported = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, admission.kernel)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let source = include_str!("fixtures/named_monad_match.lean")
                .strip_prefix("prelude\nimport Init.Prelude\n")
                .unwrap();
            let root = imported.engine.logical_root(&KVMap::new());
            let checked = imported
                .engine
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission),
                )
                .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
                .into_complete()
                .unwrap();
            assert_eq!(checked.theorems, 6);
            assert_eq!(imported.engine.logical_root(&KVMap::new()), root);
        })
        .unwrap()
        .join()
        .unwrap();
}
