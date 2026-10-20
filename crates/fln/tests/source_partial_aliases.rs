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

#[test]
fn named_function_results_use_whole_argument_inhabitants_before_opening() {
    assert_eq!(
        values(
            &engine(),
            include_str!("../../fln-parse/tests/fixtures/partial_definitions/FunctionResult.lean")
        ),
        ["42"]
    );
}

#[test]
fn intermediate_function_alias_instances_are_tried_before_the_codomain() {
    let base = check(
        &engine(),
        r#"
inductive Token where
  | stop
  | again
def InnerFunction : Type := Nat -> Token
instance innerFunctionWitness : Inhabited InnerFunction := ⟨fun _ => Token.stop⟩
def OuterFunction : Type := InnerFunction
partial def chooseFunction (n : Nat) : OuterFunction :=
  if n == 0 then (fun _ => Token.again) else chooseFunction (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(value)) = base
        .environment()
        .find(&Name::from_components(["chooseFunction"]))
    else {
        panic!("opaque partial interface")
    };
    assert!(references(
        &value.value,
        &Name::from_components(["innerFunctionWitness"])
    ));
}

#[test]
fn hidden_dependent_telescopes_contribute_providers_in_lexical_order() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Callback (A : Type) : Type := A -> A
def Factory (A : Type) : Type := A -> Callback A
partial def makeFactory {A : Type} (n : Nat) : Factory A :=
  if n == 0 then (fun x _ => x) else makeFactory (n - 1)
#eval makeFactory 4 42 91
"#
        ),
        ["42"]
    );
}

#[test]
fn mutual_function_results_share_whole_function_inhabitants() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Callback (A : Type) : Type := Nat -> A
mutual
partial def first {A : Type} (f : Callback A) (n : Nat) : Callback A :=
  if n == 0 then f else second f (n - 1)
partial def second {A : Type} (f : Callback A) (n : Nat) : Callback A :=
  if n == 0 then f else first f (n - 1)
end
#eval first (fun n => n + 5) 4 12
#eval second (fun n => n + 9) 3 12
"#
        ),
        ["17", "21"]
    );
}

#[test]
fn captured_function_providers_close_with_the_partial_section() {
    assert_eq!(
        values(
            &engine(),
            r#"
def Callback (A : Type) : Type := Nat -> A
section
variable {A : Type} (f : Callback A)
partial def capture (n : Nat) : Callback A :=
  if n == 0 then f else capture (n - 1)
end
#eval capture (fun n => n + 30) 3 12
"#
        ),
        ["42"]
    );
}

#[test]
fn function_aliases_cannot_turn_opaque_execution_into_a_proof() {
    let base = check(
        &engine(),
        r#"
def Callback : Type := Nat -> Nat
partial def makeCallback (n : Nat) : Callback :=
  if n == 0 then (fun k => k + 3) else makeCallback (n - 1)
"#,
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem invalid : makeCallback 0 0 = 3 := by rfl",
        "def leak (n : Nat) : Nat := makeCallback._unsafe_rec n n",
        "def ImpossibleFunction : Type := Nat -> False\npartial def bad (n : Nat) : ImpossibleFunction := bad (n + 1)",
        "def CallbackTo (A : Type) : Type := Nat -> A\npartial def confused {A : Type} (f : CallbackTo A) (n : Nat) : CallbackTo A := if n == 0 then true else confused f (n - 1)",
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
    assert_eq!(values(&base, "#eval makeCallback 3 7\n"), ["10"]);
}

// A constructive, local fallback provider exercises strategy ordering without
// an installed Init artifact or introducing a choice axiom into this model.
const NONEMPTY_MODEL: &str = r#"
class Nonempty (A : Type) where
  witness : A
def Classical.ofNonempty {A : Type} [inst : Nonempty A] : A := inst.witness
inductive Token where
  | stop
  | again
def Callback : Type := Nat -> Token
instance nonemptyCallback : Nonempty Callback := ⟨fun _ => Token.stop⟩
"#;

#[test]
fn fallback_restarts_at_the_function_alias_without_leaking_opened_parameters() {
    let base = check(&engine(), NONEMPTY_MODEL);
    let base = check(
        &base,
        r#"
partial def fallback (n : Nat) : Callback :=
  if n == 0 then (fun _ => Token.again) else fallback (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(value)) = base
        .environment()
        .find(&Name::from_components(["fallback"]))
    else {
        panic!("opaque partial interface")
    };
    assert!(references(
        &value.value,
        &Name::from_components(["nonemptyCallback"])
    ));
    assert!(references(
        &value.value,
        &Name::from_components(["Classical", "ofNonempty"])
    ));
    assert_eq!(
        values(
            &base,
            "#eval match fallback 3 8 with | Token.stop => 0 | Token.again => 42\n"
        ),
        ["42"]
    );
}

#[test]
fn all_inhabited_paths_precede_an_available_outer_nonempty_provider() {
    let base = check(&engine(), NONEMPTY_MODEL);
    let base = check(
        &base,
        r#"
instance tokenWitness : Inhabited Token := ⟨Token.again⟩
partial def preferred (n : Nat) : Callback :=
  if n == 0 then (fun _ => Token.stop) else preferred (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(value)) = base
        .environment()
        .find(&Name::from_components(["preferred"]))
    else {
        panic!("opaque partial interface")
    };
    assert!(references(
        &value.value,
        &Name::from_components(["tokenWitness"])
    ));
    assert!(!references(
        &value.value,
        &Name::from_components(["nonemptyCallback"])
    ));
    assert!(!references(
        &value.value,
        &Name::from_components(["Classical", "ofNonempty"])
    ));
}

#[test]
fn polymorphic_function_alias_witnesses_are_closed_checked_terms() {
    // This checks the logical admission boundary, not runtime specialization of
    // a polymorphic callback computed after an effectful prefix.
    let base = check(
        &engine(),
        r#"
def Endo (A : Type) : Type := A -> A
def PolymorphicFactory : Type 1 := (A : Type) -> Endo A
partial def polymorphicFactory (n : Nat) : PolymorphicFactory :=
  if n == 0 then (fun A x => x) else polymorphicFactory (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(value)) = base
        .environment()
        .find(&Name::from_components(["polymorphicFactory"]))
    else {
        panic!("opaque partial interface")
    };
    assert!(!value.value.has_fvar());
    assert!(!value.value.has_loose_bvars());
    assert!(!value.value.has_expr_mvar());
    assert!(!value.value.has_level_mvar());
    assert!(base.environment().contains(&Name::from_components([
        "polymorphicFactory",
        "_unsafe_rec"
    ])));
}
