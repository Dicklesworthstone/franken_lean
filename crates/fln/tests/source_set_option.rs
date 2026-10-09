//! `set_option` through the source path (bead `fln-set-option-t69b`): admitted only through the
//! option table, scoped as the pin scopes it, and refused by name otherwise.
//!
//! The verdicts are the pinned v4.32.0's on the same shapes, with Init's own `Monad` and
//! `MonadLiftT` in place of the seed classes below: inside `section … set_option autoLift false`
//! and under `set_option autoLift false in`, a bind that needs a lift is a `Type mismatch`; after
//! `end`, and for the command after the `in` one, it is accepted. `Unknown option `foo.bar`` and
//! `set_option value type mismatch` are errors there too.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

const CLASSES: &str = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class MonadLiftT (m n : Type -> Type) where
  monadLift : {A : Type} -> m A -> n A
def liftM {m n : Type -> Type} [inst : MonadLiftT m n] {A : Type} (x : m A) : n A := @MonadLiftT.monadLift m n inst A x
"#;

/// A bind of an `M` action in an `N` block: accepted only through an inserted lift.
const LIFTED: &str = "def lifted {M N : Type -> Type} [Pure N] [Bind N] [MonadLiftT M N] {A : Type} (action : M A) : N A := do\n  let x ← action\n  return x\n";

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn run(base: &Engine, source: &str) -> Result<fln::SourceFileCheck, String> {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .map_err(|error| error.to_string())?
        .into_complete()
        .map_err(|outcome| format!("{outcome:?}"))
}

#[test]
fn an_honored_option_changes_elaboration_and_ends_with_its_scope() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    // The control: the lift is inserted by default.
    run(&base, LIFTED).unwrap();
    let off = format!("section\nset_option autoLift false\n{LIFTED}end\n");
    assert!(run(&base, &off).is_err(), "{off}");
    let ended = format!("section\nset_option autoLift false\nend\n{LIFTED}");
    run(&base, &ended).unwrap();
    let only_in = format!("set_option autoLift false in\n{LIFTED}");
    assert!(run(&base, &only_in).is_err(), "{only_in}");
    let next = format!("set_option autoLift false in\ndef other : Nat := 1\n{LIFTED}");
    run(&base, &next).unwrap();
    // Set back to the default inside the scope, the lift returns.
    let restored =
        format!("section\nset_option autoLift false\nset_option autoLift true\n{LIFTED}end\n");
    run(&base, &restored).unwrap();
}

#[test]
fn silenced_and_inert_options_are_admitted_and_change_nothing() {
    let base = seed();
    let plain = "def x : Nat := 1\ntheorem t : x = 1 := rfl\n";
    let with_options = format!(
        "set_option linter.unusedVariables false\nset_option warn.sorry false\n\
         set_option maxHeartbeats 400000\nset_option autoImplicit false\n\
         set_option pp.all false\nset_option maxRecDepth 2048\n{plain}"
    );
    let checked = run(&base, &with_options).unwrap();
    assert_eq!(
        checked.result_logical_root,
        run(&base, plain).unwrap().result_logical_root
    );
    assert_eq!(checked.theorems, 1);
}

#[test]
fn unknown_mistyped_and_unimplemented_options_are_refused_by_name() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    for (source, named) in [
        ("set_option foo.bar true", "`foo.bar`"),
        ("set_option maxHeartbeats true", "`maxHeartbeats`"),
        ("set_option autoLift 1", "`autoLift`"),
        ("set_option pp.all true", "`pp.all`"),
        ("set_option maxHeartbeats 1000", "`maxHeartbeats`"),
        ("set_option linter.missingDocs true", "`linter.missingDocs`"),
        (
            "set_option trace.Meta.synthInstance true",
            "`trace.Meta.synthInstance`",
        ),
        ("set_option pp.all true in\ndef x : Nat := 1", "`pp.all`"),
    ] {
        let error = run(&base, &format!("{source}\ndef y : Nat := 2\n")).unwrap_err();
        assert!(error.contains(named), "{source}: {error}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn options_reach_golem_through_the_execution_path() {
    let run = |source: &str| {
        seed()
            .execute_source_definitions(
                &[source.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap()
    };
    for source in [
        "set_option linter.unusedVariables false\n#eval 6 * 7\n",
        "set_option maxHeartbeats 400000 in\n#eval 6 * 7\n",
        "section\nset_option maxHeartbeats 0\n#eval 6 * 7\nend\n",
    ] {
        let execution = run(source);
        let VmExit::Returned(value) = &execution.executions.last().unwrap().exit else {
            panic!("{source}: Golem did not return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42"),
            "{source}"
        );
    }
    let refused = seed().execute_source_definitions(
        &[b"set_option pp.all true in\n#eval 6 * 7\n"],
        &KVMap::new(),
        EngineExecutionLimits::new(limits().admission.kernel),
    );
    assert!(format!("{refused:?}").contains("pp.all"), "{refused:?}");
}
