//! Generated recOn/casesOn declarations are available at the ordinary source
//! door, with checked metadata, dependent motive inference, and VM execution.
//! The source verdicts were compared with the pinned Lean v4.32.0 binary.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};
use fln_elab::aux_recursors::AuxRecursors;
use fln_elab::protected_names::ProtectedNames;
use fln_elab::reducibility::{Reducibility, ReducibilityTable};
use fln_env::constants::{ConstantInfo, ReducibilityHints};

const CHAIN: &str = "inductive Chain where | nil | cons (head : Nat) (tail : Chain)\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
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

fn evaluates(source: &str, expected: &str) {
    let result = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("generated case analysis did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn source_command_admits_wrappers_and_their_exact_elaborator_tags() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let batch = base
        .admit_source_command(CHAIN.as_bytes(), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        batch.admissions.len(),
        3,
        "family plus two checked definitions"
    );
    assert_eq!(batch.base_logical_root, root);
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&name("Chain")));
    let env = batch.engine.environment();
    let tagged = AuxRecursors::read(env).unwrap();
    let protected = ProtectedNames::read(env).unwrap();
    let reducibility = ReducibilityTable::read(env).unwrap();
    for suffix in ["recOn", "casesOn"] {
        let n = name(&format!("Chain.{suffix}"));
        let Some(ConstantInfo::Defn(definition)) = env.find(&n) else {
            panic!("generated {suffix} must be an admitted definition")
        };
        assert_eq!(definition.hints, ReducibilityHints::Abbrev);
        assert!(tagged.contains(&n));
        assert_eq!(reducibility.get(&n), Some(Reducibility::Reducible));
        assert_eq!(protected.contains(&n), suffix == "recOn");
    }
    assert!(!tagged.contains(&name("Chain.rec")));
}

#[test]
fn generated_eliminators_infer_dependent_motives_and_wait_for_expected_types() {
    checked(
        &engine(),
        &format!(
            "{CHAIN}\
             theorem recursive_self (c : Chain) : c = c := Chain.recOn c rfl (fun _ _ _ => rfl)\n\
             theorem case_self (c : Chain) : c = c := Chain.casesOn c rfl (fun _ _ => rfl)\n\
             theorem count : Chain.recOn (Chain.cons 7 (Chain.cons 9 Chain.nil)) 0 (fun _ _ ih => ih + 1) = 2 := rfl\n\
             theorem explicit : @Chain.recOn (fun _ => Nat) Chain.nil 0 (fun _ _ ih => ih + 1) = 0 := rfl\n\
             theorem named : Chain.casesOn (motive := fun _ => Nat) Chain.nil 0 (fun n _ => n) = 0 := rfl"
        ),
    );
    checked(
        &engine(),
        "structure Point where\n  x : Nat\n  y : Nat\n\
         theorem record_self (p : Point) : p = p := Point.recOn p (fun _ _ => rfl)",
    );
}

#[test]
fn generated_case_analysis_runs_on_recursive_data_and_records() {
    evaluates(
        &format!(
            "{CHAIN}def first (c : Chain) : Nat := Chain.casesOn c 0 (fun n _ => n)\n\
             theorem first_ok : first (Chain.cons 42 Chain.nil) = 42 := rfl\n\
             #eval first (Chain.cons 42 Chain.nil)"
        ),
        "42",
    );
    evaluates(
        "structure Point where\n  x : Nat\n  y : Nat\n\
         def total (p : Point) : Nat := Point.casesOn p (fun x y => x + y)\n\
         #eval total ⟨20, 22⟩",
        "42",
    );
}

#[test]
fn compiled_rec_on_keeps_the_pins_refusal_and_wrong_branches_publish_nothing() {
    let base = checked(&engine(), CHAIN);
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def count (c : Chain) : Nat := Chain.recOn c 0 (fun _ _ ih => ih + 1)",
        "def count : Nat := @Chain.recOn (fun _ => Nat) Chain.nil 0 (fun _ _ ih => ih + 1)",
        "def count (c : Chain) : Nat := Chain.recOn.{1} c 0 (fun _ _ ih => ih + 1)",
        "def count : Nat := @Chain.recOn.{1} (fun _ => Nat) Chain.nil 0 (fun _ _ ih => ih + 1)",
    ] {
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        assert!(
            error
                .to_string()
                .contains("Failed to find LCNF signature for Chain.recOn"),
            "{error}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    for source in [
        "theorem bad : Chain.casesOn Chain.nil 0 (fun n _ => n) = 1 := rfl",
        "def bad (c : Chain) : Nat := Chain.casesOn c true (fun n _ => n)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn auxiliary_collisions_are_atomic_and_ordinary_names_are_not_tagged() {
    for suffix in ["recOn", "casesOn"] {
        let base = checked(&engine(), &format!("def Collision.{suffix} : Nat := 7"));
        let root = base.logical_root(&KVMap::new());
        assert!(
            base.admit_source_command(b"inductive Collision where | mk", &KVMap::new(), limits(),)
                .is_err()
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&name("Collision")));
        assert!(!base.environment().contains(&name("Collision.mk")));
    }
    let ordinary = checked(
        &engine(),
        "def User.casesOn (n : Nat) : Nat := n\ndef User.recOn (n : Nat) : Nat := n",
    );
    let tagged = AuxRecursors::read(ordinary.environment()).unwrap();
    assert!(!tagged.contains(&name("User.casesOn")));
    assert!(!tagged.contains(&name("User.recOn")));
    checked(&ordinary, "theorem identity : User.recOn 42 = 42 := rfl");
}

#[test]
fn prelude_free_bootstrap_generates_rec_on_before_punit_exists() {
    let base = Engine::builder().build_empty();
    let result = base
        .admit_source_command(b"inductive Flag where | off | on", &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.admissions.len(), 2);
    assert!(result.engine.environment().contains(&name("Flag.recOn")));
    assert!(!result.engine.environment().contains(&name("Flag.casesOn")));
}
