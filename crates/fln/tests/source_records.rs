//! Source-defined records/classes exercise the production checking pipeline.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};
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
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    // The pin requires an explicit numeral type through this named projection.
    let original = "structure Package where\n  carrier : Type\n  value : carrier\ndef wrapped : Package := Package.mk Nat 23\ntheorem value_ok : Package.value wrapped = 23 := by rfl";
    let Err(error) = base.check_source_files(
        &[original.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) else {
        panic!("accepted an unannotated dependent-field numeral");
    };
    assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&n("wrapped")));
    check(
        &base,
        "structure Package where\n  carrier : Type\n  value : carrier\ndef wrapped : Package := Package.mk Nat 23\ntheorem value_ok : Package.value wrapped = (23 : Nat) := by rfl",
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
fn record_method_binders_and_result_types_use_checked_lambda_scopes() {
    let source = r#"
structure Methods where
  apply : Nat → Nat → Nat
  ignore : Nat → Nat
  identity : {A : Type} → A → A
def methods : Methods := {
  apply (x y : Nat) : Nat := x + y,
  ignore _ := 7,
  identity {A : Type} (x : A) : A := x
}
theorem apply_ok : methods.apply 20 22 = 42 := by rfl
theorem ignore_ok : methods.ignore 100 = 7 := by rfl
theorem identity_ok : methods.identity 19 = 19 := by rfl
structure Box where
  value : Nat
structure Factory where
  make : Nat → Box
def factory : Factory := { make (x : Nat) : Box := { value := x } }
theorem nested_ok : (factory.make 23).value = 23 := by rfl
def changed : Methods := { methods with apply x _ := x + 1 }
theorem update_ok : changed.apply 41 99 = 42 := by rfl
theorem copied_ok : changed.ignore 99 = 7 := by rfl
class Printer (A : Type) where
  render : A → Nat → String
instance printer : Printer Nat where
  render (_ : Nat) _ : String := "printed"
theorem printer_ok : Printer.render 42 0 = "printed" := by rfl
class Chosen (A : Type) where
  value : A
structure Selector where
  select : {A : Type} → [Chosen A] → A
def selector : Selector := {
  select {A : Type} [d : Chosen A] : A := @Chosen.value A d
}
instance chosenNat : Chosen Nat := { value := 17 }
theorem selected_ok : (selector.select : Nat) = 17 := by rfl
"#;
    let result = check(&engine(), source);
    assert_eq!(result.theorems, 8);
    assert!(result.engine.environment().contains(&n("printer_ok")));
    assert!(result.engine.environment().contains(&n("selected_ok")));
}

#[test]
fn field_method_annotations_are_checked_under_the_binders_without_leaking_names() {
    let base = check(
        &engine(),
        "structure Method where\n apply : Nat → Nat\nclass Print where\n render : Nat → String",
    )
    .engine;
    let root = base.logical_root(&KVMap::new());
    for invalid in [
        "def bad : Method := { apply (x : String) := 0 }",
        "def bad : Method := { apply x : String := x }",
        "def bad : Method := { apply x y := x }",
        "instance bad : Print where\n render x : Nat := x",
        "def good : Method := { apply x := x }\ndef escaped : Nat := x",
    ] {
        assert!(
            base.check_source_files(
                &[invalid.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "field binders must obey ordinary typing and scope: {invalid}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
    }
    check(
        &base,
        "def retry : Method := { apply (x : Nat) : Nat := x + 1 }\ntheorem retry_ok : retry.apply 41 = 42 := by rfl",
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

// Signatures observed with lean v4.32.0, `prelude; import Init.Prelude`,
// `#check @<projection>`. See Lean/Meta/Structure.lean mkProjections and
// Lean/Expr.lean inferImplicit: an instance receiver does not by itself make
// the class parameters inferable; an explicit structure receiver does.
#[test]
fn projection_parameter_binders_follow_the_pinned_signatures() {
    use BinderInfo::{Default as E, Implicit as I, InstImplicit as C};
    let result = check(
        &engine(),
        "class C (n : Nat) where\n  val : Nat\n\
         class Dep (A : Type) where\n  val : A\n\
         class Out (A : outParam Type) where\n  val : Nat\n\
         class Inst (A : Type) [d : Dep A] where\n  val : Nat\n\
         structure S (n : Nat) where\n  val : Nat\n\
         structure SI (A : Type) [d : Dep A] where\n  val : Nat\n\
         class Chain (n : Nat) where\n  ty : Type\n  val : ty\n\
         class Methods (A : Type) where\n  hidden : {x : A} -> Nat\n  visible : (x : A) -> Nat\n\
         class Semi (A : semiOutParam Type) where\n  val : Nat",
    );
    for (name, expected) in [
        ("C.val", vec![E, C]),
        ("Dep.val", vec![I, C]),
        ("Out.val", vec![I, C]),
        ("Inst.val", vec![E, I, C]),
        ("S.val", vec![I, E]),
        ("SI.val", vec![I, C, E]),
        ("Chain.ty", vec![E, C]),
        ("Chain.val", vec![I, C]),
        ("Methods.hidden", vec![E, C, I]),
        ("Methods.visible", vec![I, C, E]),
        ("Semi.val", vec![E, C]),
    ] {
        let info = result.engine.environment().find(&n(name)).unwrap();
        let mut ty = &info.constant_val().type_;
        let mut actual = Vec::new();
        while let ExprNode::ForallE {
            binder_info, body, ..
        } = ty.node()
        {
            actual.push(*binder_info);
            ty = body;
        }
        assert_eq!(actual, expected, "{name}: {:?}", info.constant_val().type_);
    }
    let fln_env::constants::ConstantInfo::Defn(projection) =
        result.engine.environment().find(&n("Dep.val")).unwrap()
    else {
        panic!("projection must be a definition");
    };
    // `#print Dep.val` at the pin: type {A}, value `fun A [self] => self.1`.
    assert!(matches!(
        projection.value.node(),
        ExprNode::Lam {
            binder_info: BinderInfo::Default,
            ..
        }
    ));
}

#[test]
fn explicit_class_index_selects_the_right_dictionary_and_checks_its_value() {
    let result = check(
        &engine(),
        "class C (n : Nat) where\n  val : Nat\n\
         instance instC1 : C 1 := C.mk 5\n\
         instance instC2 : C 2 := C.mk 9\n\
         def t : Nat := C.val 1\n\
         theorem first : t = 5 := by rfl\n\
         theorem second : C.val 2 = 9 := by rfl",
    );
    assert_eq!(result.theorems, 2);
    for text in [
        "def missing : Nat := C.val 3",
        "theorem wrong : C.val 2 = 5 := by rfl",
    ] {
        let error = result
            .engine
            .check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert_eq!(error.disposition().2, 1, "{text}: {error}");
    }
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
