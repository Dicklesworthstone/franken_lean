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
// Match the pin's bootstrap guard without adding declarations to the bounded
// seed. PUnit and PProd are already present there; Prod is intentionally not.
const PROD: &str = "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n";

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
    evaluates_on(&engine(), source, expected);
}

fn evaluates_on(base: &Engine, source: &str, expected: &str) {
    let result = base
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

#[test]
fn recursive_source_families_publish_checked_course_of_values_with_exact_tags() {
    let seed = engine();
    let without_prod = checked(&seed, CHAIN);
    assert!(!without_prod.environment().contains(&name("Chain.below")));
    let base = checked(&seed, PROD);
    let root = base.logical_root(&KVMap::new());
    let batch = base
        .admit_source_command(CHAIN.as_bytes(), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(batch.admissions.len(), 6);
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&name("Chain")));
    let env = batch.engine.environment();
    let tagged = AuxRecursors::read(env).unwrap();
    let protected = ProtectedNames::read(env).unwrap();
    let reducibility = ReducibilityTable::read(env).unwrap();
    for suffix in ["below", "brecOn.go", "brecOn"] {
        let n = name(&format!("Chain.{suffix}"));
        let Some(ConstantInfo::Defn(definition)) = env.find(&n) else {
            panic!("generated {suffix} must pass ordinary definition admission")
        };
        assert_eq!(definition.hints, ReducibilityHints::Abbrev);
        assert!(protected.contains(&n));
        assert_eq!(reducibility.get(&n), Some(Reducibility::Reducible));
        assert_eq!(tagged.contains(&n), suffix != "brecOn.go");
    }
    let nonrecursive_and_proof = checked(
        &batch.engine,
        "inductive Flag where | off | on\n\
         inductive ProofChain : Prop where | nil | cons : ProofChain -> ProofChain",
    );
    for n in [
        "Prod.below",
        "Flag.below",
        "ProofChain.below",
        "ProofChain.brecOn",
    ] {
        assert!(
            !nonrecursive_and_proof.environment().contains(&name(n)),
            "{n}"
        );
    }
}

#[test]
fn ordinary_source_course_of_values_proves_results_using_recursive_history() {
    checked(
        &checked(&engine(), PROD),
        &format!(
            "{CHAIN}\
             def sumStep (c : Chain) : @Chain.below (fun _ => Nat) c -> Nat :=\n  \
               Chain.casesOn (motive := fun c => @Chain.below (fun _ => Nat) c -> Nat) c\n    \
                 (fun _ => 0) (fun head tail history => match history with\n      \
                   | PProd.mk previous _ => head + previous)\n\
             theorem total_ok : Chain.brecOn (Chain.cons 20 (Chain.cons 22 Chain.nil)) sumStep = 42 := by rfl"
        ),
    );
    checked(
        &checked(&engine(), PROD),
        "mutual\n\
         inductive Tree where | node (forest : Forest)\n\
         inductive Forest where | nil | cons (tree : Tree) (rest : Forest)\nend\n\
         theorem tree_ok : @Tree.brecOn (fun _ => Nat) (fun _ => Nat)\n  \
           (Tree.node Forest.nil) (fun _ _ => 42) (fun _ _ => 0) = 42 := rfl",
    );
}

#[test]
fn direct_course_of_values_compilation_preserves_the_reference_boundary() {
    let base = checked(&checked(&engine(), PROD), CHAIN);
    for (source, expected) in [
        (
            "def bad : Nat := Chain.brecOn Chain.nil (fun _ _ => 42)",
            "Chain.brecOn",
        ),
        (
            "def bad : Nat := @Chain.brecOn.{1} (fun _ => Nat) Chain.nil (fun _ _ => 42)",
            "Chain.brecOn",
        ),
        (
            "def bad := @Chain.brecOn.go (fun _ => Nat) Chain.nil (fun _ _ => 42)",
            "Chain.brecOn.go",
        ),
        (
            "def bad := @Chain.brecOn.go.{0} (fun _ => True) Chain.nil (fun _ _ => True.intro)",
            "Chain.brecOn.go",
        ),
        (
            "def bad : Nat := Nat.brecOn 42 (fun n _ => n)",
            "Nat.brecOn",
        ),
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
                .contains(&format!("Failed to find LCNF signature for {expected}")),
            "{source}\n{error}"
        );
    }
    checked(
        &base,
        "def proof : True := match @Chain.brecOn.go (fun _ => True) Chain.nil (fun _ _ => True.intro) with\n\
           | PProd.mk proof _ => proof\n\
         def typeFormer : Type := match @Chain.brecOn.go (fun _ => Type) Chain.nil (fun _ _ => Nat) with\n\
           | PProd.mk A _ => A\n\
         def User.brecOn (n : Nat) : Nat := n\n\
         def User.brecOn.go (n : Nat) : Nat := n\n\
         theorem ordinary : User.brecOn.go 42 = 42 := rfl",
    );
}

#[test]
fn course_of_values_collisions_refuse_the_whole_command() {
    let seed = checked(&engine(), PROD);
    for suffix in ["below", "brecOn.go", "brecOn"] {
        let base = checked(&seed, &format!("def Collision.{suffix} : Nat := 7"));
        let root = base.logical_root(&KVMap::new());
        assert!(
            base.admit_source_command(
                b"inductive Collision where | nil | cons : Collision -> Collision",
                &KVMap::new(),
                limits(),
            )
            .is_err(),
            "{suffix}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for generated in ["Collision", "Collision.rec", "Collision.recOn"] {
            assert!(
                !base.environment().contains(&name(generated)),
                "{generated}"
            );
        }
        assert!(
            !AuxRecursors::read(base.environment())
                .unwrap()
                .contains(&name(&format!("Collision.{suffix}")))
        );
    }
}
