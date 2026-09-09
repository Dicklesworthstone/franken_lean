//! Source-defined records/classes exercise the production checking pipeline.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::ExprNode;
use fln_elab::instances::InstanceRegistry;
use fln_kernel::Declaration;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn check(engine: &Engine, text: &str) -> fln::SourceFileCheck {
    engine
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
}

#[test]
fn source_records_generate_constructors_projections_and_real_proofs() {
    let text = "structure Point where\n  x : Nat\n  y : Nat\ndef point : Point := Point.mk 7 9\ntheorem x_ok : Point.x point = 7 := by rfl\ntheorem y_ok : Point.y point = 9 := by rfl";
    let result = check(&engine(), text);
    assert_eq!((result.commands, result.theorems), (4, 2));
    for name in ["Point", "Point.mk", "Point.rec", "Point.x", "Point.y"] {
        assert!(result.engine.environment().contains(&n(name)));
    }
    let info = result.engine.environment().find(&n("Point.x")).unwrap();
    assert!(matches!(
        info.constant_val().type_.node(),
        ExprNode::ForallE { .. }
    ));
}

#[test]
fn dependent_fields_infer_a_large_enough_record_universe() {
    check(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier\ndef wrapped : Package := Package.mk Nat 23\ntheorem value_ok : Package.value wrapped = 23 := by rfl",
    );
}

#[test]
fn type_parameters_and_method_arguments_use_the_same_scoped_elaborator() {
    check(
        &engine(),
        "structure Box (A : Type) where\n  value : A\n  transform (x : A) : A\ndef box : Box Nat := Box.mk 3 (fun x => x + 1)\ntheorem box_ok : Box.transform box (Box.value box) = 4 := by rfl",
    );
}

#[test]
fn source_classes_feed_registered_global_and_local_instance_search() {
    let text = "class Choice (A : Type) where\n  value : A\ninstance natChoice : Choice Nat := Choice.mk 17\ndef chosen {A : Type} [Choice A] : A := Choice.value\ndef answer : Nat := chosen\ntheorem answer_ok : answer = 17 := by rfl";
    let result = check(&engine(), text);
    assert!(
        InstanceRegistry::read(result.engine.environment())
            .unwrap()
            .is_class(&n("Choice"))
    );
    assert_eq!(result.theorems, 1);
    assert_eq!(
        result.result_logical_root,
        result.engine.logical_root(&KVMap::new())
    );
}

#[test]
fn recursive_instances_can_target_user_defined_classes() {
    check(
        &engine(),
        "class Choice (A : Type) where\n  value : A\ninstance natChoice : Choice Nat := Choice.mk 11\ninstance functionChoice {A : Type} [Choice A] : Choice (Nat -> A) := Choice.mk (fun x => Choice.value)\ndef chosen : Nat -> Nat -> Nat := Choice.value\ntheorem chosen_ok : chosen 4 5 = 11 := by rfl",
    );
}

#[test]
fn regular_structures_are_not_silently_registered_as_classes() {
    let result = check(&engine(), "structure Value where\n  val : Nat");
    assert!(
        !InstanceRegistry::read(result.engine.environment())
            .unwrap()
            .is_class(&n("Value"))
    );
    assert!(
        result
            .engine
            .admit_source_declaration(
                b"instance bad : Value := Value.mk 1",
                &KVMap::new(),
                limits()
            )
            .is_err()
    );
}

#[test]
fn source_command_report_retains_every_checked_declaration_transition() {
    let base = engine();
    let result = base
        .admit_source_command(
            b"structure Point where\n  x : Nat\n  y : Nat",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.admissions.len(), 3);
    assert!(matches!(
        result.admissions[0].declaration,
        Declaration::Inductive(_)
    ));
    assert_eq!(result.base_logical_root, base.logical_root(&KVMap::new()));
    assert_eq!(
        result.result_logical_root,
        result.engine.logical_root(&KVMap::new())
    );
    for pair in result.admissions.windows(2) {
        assert_eq!(pair[0].result_logical_root, pair[1].base_logical_root);
    }
}

#[test]
fn a_late_projection_collision_exposes_no_record_or_class_registration() {
    let base = check(&engine(), "def Choice.value : Nat := 0").engine;
    let root = base.logical_root(&KVMap::new());
    let outcome = base.admit_source_command(
        b"class Choice where\n  value : Nat",
        &KVMap::new(),
        limits(),
    );
    assert!(!matches!(outcome, Ok(Outcome::Complete(_))));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&n("Choice")));
    assert!(
        !InstanceRegistry::read(base.environment())
            .unwrap()
            .is_class(&n("Choice"))
    );
}

#[test]
fn invalid_domains_universes_and_duplicates_cannot_become_records() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for text in [
        "structure Bad where\n  x : missing",
        "structure Bad where\n  x : y\n  y : Nat",
        "structure Bad where\n  x : Nat\n  x : Nat",
        "structure Bad where\n  mk : Nat",
        "structure Bad : Type where\n  A : Type",
        "structure Bad : Prop where\n  x : Nat",
        "structure Bad where\n  x : _",
        "class Bad where\n  x : 4",
    ] {
        assert!(
            !matches!(
                base.admit_source_command(text.as_bytes(), &KVMap::new(), limits()),
                Ok(Outcome::Complete(_))
            ),
            "accepted {text}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn multiline_batch_rejection_never_exposes_the_valid_record_prefix() {
    let base = engine();
    let files: &[&[u8]] = &[
        b"class Choice where\n  value : Nat",
        b"theorem false_equality : 1 = 2 := by rfl",
    ];
    assert!(!matches!(
        base.check_source_files(files, &KVMap::new(), SourceCheckLimits::new(limits())),
        Ok(Outcome::Complete(_))
    ));
    assert!(!base.environment().contains(&n("Choice")));
    check(&base, "structure Recovered where\n  value : Nat");
}

#[test]
fn empty_records_and_checker_resource_stops_remain_distinct() {
    let base = engine();
    check(
        &base,
        "structure EmptyRecord\ntheorem empty : EmptyRecord.mk = EmptyRecord.mk := by rfl",
    );
    let mut small = limits();
    small.kernel = small.kernel.narrowed(0, small.kernel.depth);
    assert!(matches!(
        base.admit_source_command(b"class Choice where\n  value : Nat", &KVMap::new(), small),
        Ok(Outcome::Inconclusive(_))
    ));
    assert!(!base.environment().contains(&n("Choice")));
}
