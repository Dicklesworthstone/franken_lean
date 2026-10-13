//! Native deriving is a checked command expansion, including module replay.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput, VmExit,
};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;

fn n(text: &str) -> Name {
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

#[test]
fn records_derive_real_defaults_and_execute_generated_helpers() {
    let base = engine();
    let source = "structure Settings where\n  count : Nat := 37\n  label : String := \"hello\"\n  flag : Bool\nderiving Inhabited\nstructure Marker : Type where\nderiving Inhabited\ndef settings : Settings := default\ntheorem count_ok : settings.count = 37 := by rfl\ntheorem flag_ok : settings.flag = false := by rfl\ndef marker : Marker := default";
    let first = checked(&base, source);
    let second = checked(&base, source);
    assert_eq!(
        first.logical_root(&KVMap::new()),
        second.logical_root(&KVMap::new())
    );
    for name in [
        "instInhabitedSettings",
        "instInhabitedSettings.default",
        "instInhabitedMarker",
        "instInhabitedMarker.default",
    ] {
        assert!(
            matches!(
                first.environment().find(&n(name)),
                Some(ConstantInfo::Defn(_))
            ),
            "{name}"
        );
        assert!(!base.environment().contains(&n(name)));
    }
    let program = b"#eval settings.count + String.length settings.label";
    let run = || {
        first
            .execute_source_definitions(
                &[program],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let result = run();
    let VmExit::Returned(value) = &result.executions[0].exit else {
        panic!("returned value")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(
        result.executions[0].flbc_artifact,
        run().executions[0].flbc_artifact
    );
}

#[test]
fn constructor_search_tries_every_constructor_before_adding_hypotheses() {
    checked(
        &engine(),
        "inductive Choice (A B : Type) where\n | left (value : A)\n | empty\nderiving Inhabited\ninductive PairChoice (A B : Type) where\n | left (value : A)\n | right (value : B)\nderiving Inhabited\ndef choose {A B : Type} : Choice A B := default\ndef paired {A B : Type} [Inhabited A] : PairChoice A B := default\ntheorem empty_ok : (default : Choice Nat String) = Choice.empty := by rfl\ntheorem left_ok : (default : PairChoice Nat String) = PairChoice.left 0 := by rfl",
    );
}

fn alpha_type(expr: &Expr) -> Expr {
    match expr.node() {
        ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } => Expr::forall_e(
            Name::anonymous(),
            alpha_type(binder_type),
            alpha_type(body),
            *binder_info,
        ),
        ExprNode::App { f, a } => Expr::app(alpha_type(f), alpha_type(a)),
        _ => expr.clone(),
    }
}

#[test]
fn generated_instance_statements_match_the_pinned_reference_binder_order() {
    // Reference v4.32.0: Inhabited.lean's mkInstanceCmdWith interleaves each
    // used hypothesis after its type parameter. mkDefaultValue's helper instead
    // places all family parameters first. Names of bound variables are alpha.
    let result = checked(
        &engine(),
        "structure Box (A : Type) where\n  value : A\nderiving Inhabited\ninductive PairChoice (A B : Type) where\n | left (value : A)\n | right (value : B)\nderiving Inhabited\ndef boxStatement {A : Type} [Inhabited A] : Inhabited (Box A) := inferInstance\ndef boxDefaultStatement {A : Type} [Inhabited A] : Box A := default\ndef pairStatement {A : Type} [Inhabited A] {B : Type} : Inhabited (PairChoice A B) := inferInstance\ndef pairDefaultStatement {A B : Type} [Inhabited A] : PairChoice A B := default\ndef natBox : Box Nat := default\ntheorem value_ok : natBox.value = 0 := by rfl",
    );
    for (generated, expected) in [
        ("instInhabitedBox", "boxStatement"),
        ("instInhabitedBox.default", "boxDefaultStatement"),
        ("instInhabitedPairChoice", "pairStatement"),
        ("instInhabitedPairChoice.default", "pairDefaultStatement"),
    ] {
        let generated = result
            .environment()
            .find(&n(generated))
            .unwrap()
            .constant_val();
        let expected = result
            .environment()
            .find(&n(expected))
            .unwrap()
            .constant_val();
        assert_eq!(generated.level_params, expected.level_params);
        assert_eq!(alpha_type(&generated.type_), alpha_type(&expected.type_));
    }
}

#[test]
fn namespaces_and_existing_dictionary_parameters_remain_in_the_generated_telescope() {
    checked(
        &engine(),
        "namespace Library\nstructure Box (A : Type) [Inhabited A] where\n  value : A := default\nderiving Inhabited\ndef expected {A : Type} {i : Inhabited A} : Inhabited (@Box A i) := @instInhabitedBox A i\nend Library\ndef boxed : Library.Box Nat := default\ntheorem value_ok : boxed.value = 0 := by rfl",
    );
}

#[test]
fn derived_instances_survive_source_module_export_and_import_replay() {
    let names = [n("Main"), n("Library")];
    let modules = [
        SourceModuleInput { name: &names[0], source: b"import Library\ndef p : Box Nat := default\ntheorem value_ok : p.value = 0 := by rfl" },
        SourceModuleInput { name: &names[1], source: b"structure Box (A : Type) where\n  value : A\nderiving Inhabited" },
    ];
    let result = engine()
        .check_source_modules(
            &modules,
            &names[0],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.module_order, [n("Library"), n("Main")]);
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&n("instInhabitedBox.default"))
    );
    assert!(result.checked.engine.environment().contains(&n("value_ok")));
}

#[test]
fn missing_handlers_and_uninhabited_fields_do_not_publish_a_successful_prefix() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "inductive NoValues where\nderiving Inhabited",
        "structure Package where\n  carrier : Type\n  value : carrier\nderiving Inhabited",
        "structure Package where\n  carrier : Type := Nat\n  value : carrier\nderiving Inhabited",
        "structure Point where\n  x : Nat\nderiving Inhabited, Repr",
        "structure Point where\n  x : Nat := \"wrong\"\nderiving Inhabited",
        "structure Point where\n  x : Nat\ndef absent : Point := default",
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
        assert!(!base.environment().contains(&n("Point")));
        assert!(!base.environment().contains(&n("instInhabitedPoint")));
    }
    checked(
        &base,
        "structure Point where\n  x : Nat\nderiving Inhabited\ntheorem recovery : (default : Point).x = 0 := by rfl",
    );
}

#[test]
fn low_level_single_family_elaboration_cannot_ignore_deriving() {
    let base = engine();
    for source in [
        "structure Point where\n  x : Nat\nderiving Inhabited",
        "inductive Flag where\n | off\n | on\nderiving Inhabited",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        let result = if fln_elab::source::is_record(parsed.syntax()) {
            fln_elab::source::elaborate_record(
                parsed.syntax(),
                base.environment(),
                limits().kernel,
                fln_elab::records::RecordBudget::default(),
            )
            .map(|_| ())
        } else {
            fln_elab::source::elaborate_inductive(
                parsed.syntax(),
                base.environment(),
                limits().kernel,
                fln_elab::records::RecordBudget::default(),
            )
            .map(|_| ())
        };
        assert!(result.is_err(), "{source}");
    }
}
