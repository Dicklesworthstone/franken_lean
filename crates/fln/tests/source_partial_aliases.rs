//! Inhabitant search for partial definitions follows named return types without
//! exposing opaque or irreducible definitions to the logical witness search.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;
use std::sync::OnceLock;
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    static BASE: OnceLock<Engine> = OnceLock::new();
    BASE.get_or_init(|| {
        Engine::with_source_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}
fn check(base: &Engine, source: &str) -> Engine {
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
fn values(base: &Engine, source: &str) -> Vec<String> {
    let batch = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    batch
        .source_evaluation_indices
        .iter()
        .map(|&i| {
            let fln::VmExit::Returned(value) = &batch.executions[i].exit else {
                panic!("expected a return")
            };
            fln_vm::interpreter::nat_decimal(&value.value).unwrap()
        })
        .collect()
}
fn references(expr: &Expr, target: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(e) = pending.pop() {
        match e.node() {
            ExprNode::Const { name, .. } if name == target => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}
#[test]
fn named_polymorphic_results_use_the_argument_inhabitant() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Alias (A : Type) : Type := A
partial def keep {A : Type} (x : A) (n : Nat) : Alias A := if n == 0 then x else keep x (n - 1)
#eval keep 43 5
"#
        ),
        ["43"]
    );
}
#[test]
fn return_type_alias_chains_unfold_one_step_at_a_time() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Inner (A : Type) : Type := A
def Middle (A : Type) : Type := Inner A
def Outer (A : Type) : Type := Middle A
partial def retain {A : Type} (x : A) (n : Nat) : Outer A := if n == 0 then x else retain x (n - 1)
#eval retain 71 4
"#
        ),
        ["71"]
    );
}
#[test]
fn named_natural_results_use_the_existing_native_instances() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Count : Type := Nat
partial def length' (n : Nat) : Count := if n == 0 then (8 : Nat) else Nat.add (length' (n - 1)) 1
#eval length' 3
"#
        ),
        ["11"]
    );
}
#[test]
fn available_intermediate_alias_instances_are_not_skipped() {
    let base = check(
        &engine(),
        r#"
inductive Token where
  | stop
  | again
def Inner : Type := Token
instance innerWitness : Inhabited Inner := ⟨Token.stop⟩
def Outer : Type := Inner
partial def turn (n : Nat) : Outer := if n == 0 then Token.again else turn (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(value)) =
        base.environment().find(&Name::from_components(["turn"]))
    else {
        panic!("opaque partial interface")
    };
    assert!(references(
        &value.value,
        &Name::from_components(["innerWitness"])
    ));
}
#[test]
fn opacity_irreducibility_and_uninhabited_aliases_remain_refusals() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def Impossible : Prop := False\npartial def bad (n : Nat) : Impossible := bad (n + 1)",
        "opaque Hidden : Type := Nat\naxiom witness : Hidden\npartial def bad (n : Nat) : Hidden := if n == 0 then witness else bad (n - 1)",
        "@[irreducible] def Hidden : Type := Nat\naxiom witness : Hidden\npartial def bad (n : Nat) : Hidden := if n == 0 then witness else bad (n - 1)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    assert_eq!(values(&base, "#eval 7\n"), ["7"]);
}

#[test]
fn mutual_partial_results_share_checked_alias_inhabitants() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Alias (A : Type) : Type := A
mutual
partial def first {A : Type} (x : A) (n : Nat) : Alias A := if n == 0 then x else second x (n - 1)
partial def second {A : Type} (x : A) (n : Nat) : Alias A := if n == 0 then x else first x (n - 1)
end
#eval first 43 5
#eval second 67 4
"#
        ),
        ["43", "67"]
    );
}
