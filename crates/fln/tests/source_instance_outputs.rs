//! Whole source files exercise annotations, selection and publication through
//! the production engine and both ordinary checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn fixture(mode: &str) -> Engine {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &engine,
        &format!(
            r#"class Transfer (A : Type) (B : {mode} Type) where
  convert : A -> B
instance (priority := 500) boolean : Transfer Nat Bool := Transfer.mk (fun x => true)
instance (priority := 2000) natural : Transfer Nat Nat := Transfer.mk (fun x => x + 1)
def transfer {{A B : Type}} [d : Transfer A B] (x : A) : B := Transfer.convert x
def explicit (B : Type) [d : Transfer Nat B] (x : Nat) : B := Transfer.convert x"#
        ),
    )
}
fn contains(expr: &Expr, name: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name: actual, .. } if actual == name => return true,
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
fn definition(engine: &Engine, name: &str) -> fln_env::constants::DefinitionVal {
    let Some(ConstantInfo::Defn(definition)) = engine.environment().find(&n(name)) else {
        panic!("missing definition {name}");
    };
    for expr in [&definition.base.type_, &definition.value] {
        assert!(!expr.has_expr_mvar());
        assert!(!expr.has_level_mvar());
        assert!(!expr.has_fvar());
        assert!(!expr.has_loose_bvars());
    }
    definition.clone()
}

#[test]
fn source_output_parameters_infer_types_and_execute_selected_dictionary_fields() {
    let engine = checked(
        &fixture("outParam"),
        "def inferred := transfer 4\ntheorem result : inferred = 5 := by rfl",
    );
    let result = definition(&engine, "inferred");
    assert_eq!(result.base.type_, Expr::const_(n("Nat"), vec![]));
    assert!(contains(&result.value, &n("natural")));
    assert!(!contains(&result.value, &n("boolean")));
    let Some(ConstantInfo::Induct(class)) = engine.environment().find(&n("Transfer")) else {
        panic!("source class must be a checked inductive");
    };
    assert!(contains(&class.base.type_, &n("outParam")));
    let Some(ConstantInfo::Rec(recursor)) = engine.environment().find(&n("Transfer.rec")) else {
        panic!("source class must have a checked eliminator");
    };
    assert!(!contains(&recursor.base.type_, &n("outParam")));
}

#[test]
fn completed_instance_outputs_convert_regular_aliases_without_changing_inputs() {
    let engine = checked(
        &fixture("outParam"),
        concat!(
            "def Id (A : Type) : Type := A\n",
            "def wrapped : Id (Id Nat) := transfer 4\n",
            "theorem wrapped_ok : wrapped = (5 : Nat) := by rfl\n",
            "def NatAlias : Type := Nat\n",
            "instance distinct : Transfer NatAlias Bool := { convert := fun x => true }\n",
            "def aliasInput (x : NatAlias) : Bool := Transfer.convert x\n",
        ),
    );
    assert!(contains(
        &definition(&engine, "wrapped").value,
        &n("natural")
    ));
    assert!(contains(
        &definition(&engine, "aliasInput").value,
        &n("distinct")
    ));
    assert!(!contains(
        &definition(&engine, "aliasInput").value,
        &n("natural")
    ));
}

#[test]
fn source_semi_outputs_use_known_types_but_can_also_infer_unknown_types() {
    let engine = checked(
        &fixture("semiOutParam"),
        "def inferred := transfer 4\ntheorem inferred_ok : inferred = 5 := by rfl\ndef chosen := explicit Bool 4\ntheorem chosen_ok : chosen = true := by rfl",
    );
    assert!(contains(
        &definition(&engine, "inferred").value,
        &n("natural")
    ));
    assert!(contains(
        &definition(&engine, "chosen").value,
        &n("boolean")
    ));
}

#[test]
fn incompatible_outputs_do_not_select_lower_priority_or_publish_partial_files() {
    let base = fixture("outParam");
    let before = base.logical_root(&KVMap::new());
    for text in [
        "def shouldNotPublish := transfer 4\ndef incompatible := explicit Bool 4",
        "instance (priority := 3000) temporary : Transfer Nat Nat := Transfer.mk (fun x => x + 2)\ndef incompatible := explicit Bool 4",
    ] {
        assert!(
            base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{text}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(base.environment().find(&n("shouldNotPublish")).is_none());
        assert!(base.environment().find(&n("temporary")).is_none());
    }
    checked(&base, "theorem recovery : explicit Nat 4 = 5 := by rfl");
}

#[test]
fn local_output_instances_preserve_precedence_and_compute() {
    checked(
        &fixture("outParam"),
        "def localResult : Bool := let d : Transfer Nat Bool := Transfer.mk (fun x => true); explicit Bool 4\ntheorem local_ok : localResult = true := by rfl",
    );
}

#[test]
fn recursive_source_search_solves_ready_outputs_before_blocked_prerequisites() {
    let engine = checked(
        &fixture("outParam"),
        "class Needs (A : Type) where\n  value : A\ninstance needNat : Needs Nat := Needs.mk 23\nclass Root where\n  result : Nat\ninstance buildRoot {B : Type} [need : Needs B] [give : Transfer Nat B] : Root := Root.mk 37\ndef resolved : Nat := Root.result\ntheorem result : resolved = 37 := by rfl",
    );
    let resolved = definition(&engine, "resolved");
    for name in ["buildRoot", "needNat", "natural"] {
        assert!(contains(&resolved.value, &n(name)), "missing {name}");
    }
}

const DEPENDENT_DICTIONARIES: &str = r#"
class Dict (A : Type) where
  value : Nat
class Family (A : outParam Type) [d : Dict A] where
  value : Nat
class Further (A : outParam Type) [d : Dict A] [f : @Family A d] where
  value : Nat
def dictZero : Dict Nat := @Dict.mk Nat 0
def dictOne : Dict Nat := @Dict.mk Nat 1
instance (priority := 2000) familyHigh : @Family Nat dictZero := @Family.mk Nat dictZero 17
instance (priority := 500) familyLow : @Family Nat dictOne := @Family.mk Nat dictOne 99
instance further : @Further Nat dictZero familyHigh := @Further.mk Nat dictZero familyHigh 25
def useFurther {A : Type} [d : Dict A] [f : @Family A d] [g : @Further A d f] (n : Nat) : Nat :=
  @Family.value A d f + @Further.value A d f g + n
"#;

#[test]
fn transitive_opaque_dictionary_outputs_reach_both_checkers_and_native_execution() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!(
        "{DEPENDENT_DICTIONARIES}\ndef result := useFurther 0\ntheorem correct : result = 42 := by rfl"
    );
    let result = checked(&base, &source);
    for selected in ["dictZero", "familyHigh", "further"] {
        assert!(contains(&definition(&result, "result").value, &n(selected)));
    }
    assert!(!contains(
        &definition(&result, "result").value,
        &n("familyLow")
    ));
    let source = format!("{DEPENDENT_DICTIONARIES}\n#eval useFurther 0");
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("native dictionary program did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn dependent_output_conflicts_refuse_without_falling_back_or_publishing_prefixes() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let base = checked(&base, DEPENDENT_DICTIONARIES);
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "def unpublished : Nat := useFurther 0\ndef wrong : @Family Nat dictOne := inferInstance",
        "def unpublished : Nat := useFurther 0\ndef wrong : @Further Nat dictOne familyLow := inferInstance",
        "def unpublished : Nat := useFurther 0\ntheorem wrong : useFurther 0 = 99 := by rfl",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &options, limits())
                .is_err()
        );
        assert!(!base.environment().contains(&n("unpublished")));
        assert_eq!(base.logical_root(&options), root);
    }
    checked(
        &base,
        "def recovered : Nat := useFurther 0\ntheorem recovery : recovered = 42 := by rfl",
    );
}

#[test]
fn a_local_dependent_output_dictionary_still_precedes_global_candidates() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let base = checked(&base, DEPENDENT_DICTIONARIES);
    checked(
        &base,
        r#"
def localChoice [f : @Family Nat dictOne] : @Family Nat dictOne := inferInstance
theorem localCorrect (f : @Family Nat dictOne) : @localChoice f = f := by rfl
"#,
    );
}
