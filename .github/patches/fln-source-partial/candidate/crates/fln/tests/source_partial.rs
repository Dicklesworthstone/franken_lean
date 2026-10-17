//! Native source partial recursion retains both independently checked halves.
//! These tests do not require an installed Reference or imported .olean files.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::sync::OnceLock;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    static SEED: OnceLock<Engine> = OnceLock::new();
    SEED.get_or_init(|| {
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
    .expect("both checkers answered")
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
        .expect("native execution completed");
    batch
        .source_evaluation_indices
        .iter()
        .map(|index| {
            let execution = &batch.executions[*index];
            let fln::VmExit::Returned(value) = &execution.exit else {
                panic!("unexpected exit: {:?}", execution.exit);
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

fn refuses(base: &Engine, source: &str, label: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "accepted {source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(label.split('.')))
    );
}

fn references(expr: &Expr, target: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.node() {
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

const COUNT: &str =
    "partial def count (n : Nat) : Nat := if n == 0 then 10 else count (n - 1) + 1\n";

#[test]
fn recursive_body_executes_instead_of_the_opaque_inhabitant() {
    assert_eq!(
        values(&engine(), &format!("{COUNT}#eval count 5\n#eval count 0\n")),
        ["15", "10"]
    );
}

#[test]
fn unrestricted_recursion_accepts_growing_arguments_and_euclidean_gcd() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def climb (n : Nat) : Nat := if n < 10 then climb (n + 1) else n
partial def gcd' (a b : Nat) : Nat := if b == 0 then a else gcd' b (a % b)
#eval climb 3
#eval gcd' 48 18
"#
        ),
        ["10", "6"]
    );
}

#[test]
fn checked_source_publishes_the_exact_opaque_and_partial_group() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let batch = base
        .admit_source_command(COUNT.as_bytes(), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(batch.admissions.len(), 2);
    assert_eq!(batch.base_logical_root, root);
    assert_eq!(base.logical_root(&KVMap::new()), root);
    let logical = Name::from_components(["count"]);
    let companion = Name::from_components(["count", "_unsafe_rec"]);
    let Some(ConstantInfo::Opaque(opaque)) = batch.engine.environment().find(&logical) else {
        panic!("missing opaque interface");
    };
    let Some(ConstantInfo::Defn(executable)) = batch.engine.environment().find(&companion) else {
        panic!("missing executable companion");
    };
    assert!(!opaque.is_unsafe);
    assert_eq!(executable.safety, DefinitionSafety::Partial);
    assert_eq!(opaque.base.type_, executable.base.type_);
    assert_eq!(opaque.base.level_params, executable.base.level_params);
    assert_eq!(opaque.all, [logical]);
    assert_eq!(executable.all, [companion]);
    assert_ne!(opaque.value, executable.value);
    assert_eq!(values(&batch.engine, "#eval count 5\n"), ["15"]);
}

#[test]
fn partial_values_remain_opaque_to_proofs_and_companions_remain_nonsafe() {
    let base = check(&engine(), COUNT);
    check(&base, "theorem same (n : Nat) : count n = count n := rfl");
    for source in [
        "theorem leak : count 0 = 10 := rfl",
        "theorem leak : count 5 = 5 := rfl",
        "def leak (n : Nat) : Nat := count._unsafe_rec n",
        "theorem leak : count._unsafe_rec 0 = count._unsafe_rec 0 := rfl",
    ] {
        refuses(&base, source, "leak");
    }
}

#[test]
fn nonrecursive_partial_definitions_keep_their_actual_reducible_value() {
    let base = check(
        &engine(),
        "partial def plain (n : Nat) : Nat := n + 1\ntheorem ok : plain 2 = 3 := rfl\n",
    );
    assert!(
        matches!(base.environment().find(&Name::from_components(["plain"])), Some(ConstantInfo::Defn(v)) if v.safety == DefinitionSafety::Safe)
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["plain", "_unsafe_rec"]))
    );
    assert_eq!(values(&base, "#eval plain 7\n"), ["8"]);
}

#[test]
fn polymorphic_partial_recursion_can_use_an_argument_as_its_inhabitant() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def retain {A : Type} (x : A) (n : Nat) : A := if n == 0 then x else retain x (n - 1)
#eval retain 42 3
"#
        ),
        ["42"]
    );
}

#[test]
fn malformed_bodies_uninhabited_results_and_termination_hints_are_refused() {
    let base = engine();
    for source in [
        "partial def bad (n : Nat) : False := bad (n + 1)",
        "partial def bad (n : Nat) : Nat := bad True",
        "partial def bad : Nat := bad",
        "partial def bad (n : Nat) : Nat := if n == 0 then True else bad n",
        "partial def bad (n : Nat) : Nat := bad n\ntermination_by n",
        "partial def bad (n : Nat) : Nat := bad n\ntermination_by structural n",
        "partial theorem bad (n : Nat) : False := bad n",
    ] {
        refuses(&base, source, "bad");
    }
}

#[test]
fn single_declaration_api_does_not_drop_the_required_companion() {
    let base = engine();
    let error = base
        .admit_source_declaration(COUNT.as_bytes(), &KVMap::new(), limits())
        .unwrap_err();
    assert!(error.to_string().contains("atomic admission"), "{error:?}");
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["count"]))
    );
}

#[test]
fn companion_collision_never_publishes_the_logical_half() {
    let base = check(&engine(), "def count._unsafe_rec (n : Nat) : Nat := n\n");
    refuses(&base, COUNT, "count");
}

#[test]
fn leading_lambdas_and_function_valued_results_keep_their_telescope() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def lambda : Nat -> Nat := fun n => if n == 0 then 7 else lambda (n - 1) + 1
partial def higher (n : Nat) : Nat -> Nat := fun k => if n == 0 then k else higher (n - 1) (k + 1)
partial def pick : (A : Type) -> A -> Nat -> A := fun A x n => if n == 0 then x else pick A x (n - 1)
#eval lambda 3
#eval higher 4 20
#eval pick Nat 42 3
"#
        ),
        ["10", "24", "42"]
    );
}

#[test]
fn captured_section_parameters_used_only_by_the_body_are_retained() {
    assert_eq!(
        values(
            &engine(),
            r#"
section
variable (step : Nat)
partial def walk (n : Nat) : Nat := if n == 0 then step else walk (n - 1) + step
end
section
variable {A : Type} (x : A)
partial def keep (n : Nat) : A := if n == 0 then x else keep (n - 1)
end
#eval walk 3 4
#eval keep 42 3
"#
        ),
        ["15", "42"]
    );
}

#[test]
fn inhabitant_search_makes_arguments_available_to_dependent_instances() {
    assert_eq!(
        values(
            &engine(),
            r#"
structure Box (A : Type) where
  value : A
instance {A : Type} [Inhabited A] : Inhabited (Box A) := ⟨⟨default⟩⟩
partial def boxed {A : Type} (x : A) (n : Nat) : Box A := if n == 0 then ⟨x⟩ else boxed x (n - 1)
#eval (boxed 37 3).value
"#
        ),
        ["37"]
    );
}

#[test]
fn namespace_and_protected_recursive_names_preserve_lookup_rules() {
    assert_eq!(
        values(
            &engine(),
            r#"
namespace Nested
partial def count (n : Nat) : Nat := if n == 0 then 9 else count (n - 1) + 1
protected partial def guarded (n : Nat) : Nat := if n == 0 then 20 else Nested.guarded (n - 1) + 1
end Nested
#eval Nested.count 3
#eval Nested.guarded 2
"#
        ),
        ["12", "22"]
    );
    refuses(
        &engine(),
        "namespace Nested\nprotected partial def bad (n : Nat) : Nat := bad n\nend Nested",
        "Nested.bad",
    );
}

#[test]
fn infinite_partial_execution_stops_with_a_resource_nonanswer() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = "partial def loop (n : Nat) : Nat := loop (n + 1)\n#eval loop 0\n";
    let mut bounded = EngineExecutionLimits::new(limits().kernel);
    bounded.vm.max_steps = 100;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["loop"]))
    );
}

#[test]
fn nonempty_fallback_checks_a_logical_choice_without_executing_it() {
    // The seed intentionally lacks Nonempty and choice. Check the pin's
    // inductive and register its class metadata directly: the source parser
    // does not yet accept `class inductive`. No product axiom is introduced.
    let nonempty = check(
        &engine(),
        r#"
universe u
inductive Nonempty (A : Sort u) : Prop where
  | intro (value : A) : Nonempty A
"#,
    );
    let environment = fln_elab::instances::register_class(
        nonempty.environment(),
        &Name::from_components(["Nonempty"]),
    )
    .unwrap();
    let base = check(
        &Engine::from_environment(environment),
        r#"
universe u
axiom Classical.choice {A : Sort u} : Nonempty A -> A
noncomputable def Classical.ofNonempty {A : Sort u} [h : Nonempty A] : A := Classical.choice h
partial def select {A : Type} [Nonempty A] (n : Nat) : A := select (n + 1)
"#,
    );
    let Some(ConstantInfo::Opaque(logical)) =
        base.environment().find(&Name::from_components(["select"]))
    else {
        panic!("missing logical interface");
    };
    let choice = Name::from_components(["Classical", "ofNonempty"]);
    assert!(references(&logical.value, &choice));
    let Some(ConstantInfo::Defn(executable)) = base
        .environment()
        .find(&Name::from_components(["select", "_unsafe_rec"]))
    else {
        panic!("missing actual executable");
    };
    assert!(!references(&executable.value, &choice));
    assert!(!references(
        &executable.value,
        &Name::from_components(["Classical", "choice"])
    ));
    refuses(
        &base,
        "partial def bad (n : Nat) : False := bad (n + 1)",
        "bad",
    );
    let mut bounded = EngineExecutionLimits::new(limits().kernel);
    bounded.vm.max_steps = 100;
    let program = "instance : Nonempty Nat := ⟨0⟩\n#eval select (A := Nat) 0\n";
    assert!(matches!(
        base.execute_source_definitions(&[program.as_bytes()], &KVMap::new(), bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
}

#[test]
fn universe_polymorphism_and_default_shadowing_do_not_capture_the_witness() {
    let base = check(
        &engine(),
        r#"
universe u
partial def retainSort {A : Sort u} (x : A) (n : Nat) : A := if n == 0 then x else retainSort x (n - 1)
partial def shadow (default : Bool) (n : Nat) : Nat := if n == 0 then 8 else shadow default (n - 1)
"#,
    );
    let Some(ConstantInfo::Opaque(logical)) = base
        .environment()
        .find(&Name::from_components(["retainSort"]))
    else {
        panic!("missing polymorphic partial interface");
    };
    let Some(ConstantInfo::Defn(executable)) = base
        .environment()
        .find(&Name::from_components(["retainSort", "_unsafe_rec"]))
    else {
        panic!("missing polymorphic executable");
    };
    assert_eq!(logical.base.level_params, [Name::from_components(["u"])]);
    assert_eq!(logical.base.level_params, executable.base.level_params);
    assert_eq!(logical.base.type_, executable.base.type_);
    assert_eq!(
        values(&base, "#eval retainSort 23 4\n#eval shadow true 4\n"),
        ["23", "8"]
    );
}

#[test]
fn recursive_names_are_available_before_tactic_alternative_selection() {
    assert_eq!(
        values(
            &engine(),
            "partial def chosen (n : Nat) : Nat := by first | exact (if n == 0 then 7 else chosen (n - 1) + 1) | exact 99\n#eval chosen 4\n",
        ),
        ["11"]
    );
    let base = check(
        &engine(),
        "partial def discarded (n : Nat) : Nat := by first | exact (let unused := discarded n; true) | exact 42\n",
    );
    assert!(
        matches!(base.environment().find(&Name::from_components(["discarded"])), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Safe)
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["discarded", "_unsafe_rec"]))
    );
    assert_eq!(values(&base, "#eval discarded 3\n"), ["42"]);
}

#[test]
fn local_structural_recursion_and_where_helpers_capture_partial_self() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def nested (n : Nat) : Nat :=
  let rec inner (k : Nat) : Nat := match k with
    | .zero => if n == 0 then 2 else nested (n - 1)
    | .succ j => inner j + 1
  inner 3
partial def helper (n : Nat) : Nat := if n == 0 then 5 else go (n - 1)
where go (k : Nat) : Nat := helper k + 1
#eval nested 2
#eval helper 3
"#
        ),
        ["11", "8"]
    );
}

#[test]
fn inferred_results_are_constrained_by_the_selected_body_not_a_fallback() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def inferred (n : Nat) := if n == 0 then 6 else inferred (n - 1) + 1
partial def generic {A : Type} (x : A) (n : Nat) := if n == 0 then x else generic x (n - 1)
partial def function := fun (n : Nat) => if n == 0 then 9 else function (n - 1) + 1
partial def literal := 41
#eval inferred 3
#eval generic 37 4
#eval function 2
#eval literal
"#
        ),
        ["9", "37", "11", "41"]
    );
    for source in [
        "partial def bad (n : Nat) := bad n",
        "partial def bad : False := by assumption",
    ] {
        refuses(&engine(), source, "bad");
    }
}

#[test]
fn higher_order_self_references_keep_the_actual_recursive_function() {
    assert_eq!(
        values(
            &engine(),
            r#"
def call (f : Nat -> Nat) (n : Nat) : Nat := f n
partial def callback (n : Nat) : Nat := if n == 0 then 3 else call callback (n - 1) + 1
section
variable (step : Nat)
partial def captured (n : Nat) : Nat := if n == 0 then step else call captured (n - 1) + step
end
#eval callback 4
#eval captured 2 3
"#
        ),
        ["7", "8"]
    );
}

#[test]
fn explicit_lambda_domains_see_the_registered_partial_self() {
    assert_eq!(
        values(
            &engine(),
            r#"
partial def typed (n : Nat) : Nat -> Nat :=
  fun (x : (let unused := typed n; Nat)) => if n == 0 then x else typed (n - 1) (x + 1)
#eval typed 3 8
"#
        ),
        ["11"]
    );
}
