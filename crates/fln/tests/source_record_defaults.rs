//! Defaults instantiate checked bodies before dependent fields.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};
use fln_core::name::Name;
use fln_elab::records::defaults::{RecordDefault, RecordDefaults, helper_name, register_defaults};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(e: &Engine, text: &str) -> fln::SourceFileCheck {
    let result = e.check_source_files(
        &[text.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{text}\n{result:?}"
    );
    result.unwrap().into_complete().unwrap()
}

#[test]
fn omitted_defaults_use_actual_preceding_values_and_updates_preserve_copies() {
    check(
        &engine(),
        "structure Config where\n  base : Nat := 3\n  twice : Nat := base + base\n  transform (x : Nat) : Nat := x + twice\ndef standard : Config := {}\ndef custom : Config := { base := 7 }\ndef copied := { custom with base := 20 }\ntheorem a : standard.twice = 6 := by rfl\ntheorem b : custom.twice = 14 := by rfl\ntheorem c : copied.twice = 14 := by rfl\ntheorem d : custom.transform 2 = 16 := by rfl\ntheorem e : copied.transform 2 = 16 := by rfl",
    );
}
#[test]
fn dependent_types_proofs_and_method_parameters_are_closed_in_order() {
    check(
        &engine(),
        "structure Package where\n  carrier : Type := Nat\n  value : carrier\n  copy : carrier := value\n  proof : value = value := rfl\n  ident (x : carrier) : carrier := x\ndef p : Package := { value := 9 }\ndef q : Package := { carrier := String, value := \"hi\" }\ntheorem p_ok : p.copy = (9 : Nat) := by rfl\ntheorem q_ok : q.ident q.copy = \"hi\" := by rfl",
    );
}
#[test]
fn defaults_instantiate_actual_universes_parameters_and_method_binders() {
    check(
        &engine(),
        r#"
universe u
structure Envelope (A : Type u) where
  carrier : Type u := A
  value : carrier
  copy : carrier := value
  ident (value : carrier) : carrier := value
def natural : Envelope Nat := { value := 9 }
def text : Envelope String := { value := "hi" }
def changed : Envelope Nat := { carrier := String, value := "override" }
def types : Envelope Type := { value := Nat }
theorem natural_copy : natural.copy = (9 : Nat) := by rfl
theorem natural_method : natural.ident (12 : Nat) = (12 : Nat) := by rfl
theorem text_copy : text.copy = "hi" := by rfl
theorem changed_copy : changed.copy = "override" := by rfl
theorem type_copy : types.copy = Nat := by rfl

structure Scoped (A : Type) (fallback : A) where
  value : A := fallback
  get (fallback : A) : A := value
  copy : A := value
def withFallback : Scoped Nat 42 := {}
theorem scopes : withFallback.get 7 = 42 := by rfl
theorem copied : withFallback.copy = 42 := by rfl
"#,
    );
}
#[test]
fn default_instantiation_keeps_ordinary_projection_transparency_and_failure_atomicity() {
    let base = check(
        &engine(),
        "structure Package where\n  carrier : Type := Nat\n  value : carrier\n  copy : carrier := value\ndef p : Package := { value := 9 }",
    )
    .engine;
    let root = base.logical_root(&KVMap::new());
    // Instantiating a registered default does not make a later definition's
    // carrier visible to typeclass search. The pin requires the ascription.
    for source in [
        "theorem unannotated : p.copy = 9 := by rfl",
        "def q : Package := { value := 10 }\ntheorem wrong : q.copy = (9 : Nat) := by rfl",
    ] {
        let Err(error) = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        ) else {
            panic!("default instantiation erased a typing or proof obligation: {source}");
        };
        assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["q"])));
    }
    check(&base, "theorem annotated : p.copy = (9 : Nat) := by rfl");
}
#[test]
fn defaults_use_explicit_record_instance_parameters() {
    check(
        &engine(),
        "structure Box (A : Type) [Inhabited A] where\n  value : A := default\ndef make {A : Type} [Inhabited A] : Box A := {}\ninstance chosen : Inhabited Nat := Inhabited.mk 17\ndef b : Box Nat := {}\ntheorem ok : b.value = 17 := by rfl",
    );
}

#[test]
fn copied_parent_defaults_fill_shared_fields_and_keep_explicit_values() {
    let checked = check(
        &engine(),
        r#"
structure B where
  x : Nat
structure C where
  x : Nat := 2
  y : Nat
structure D extends B, C
def omitted : D := { y := 0 }
def supplied : D := { x := 3, y := 0 }
example : omitted.x = 2 := by rfl
example : supplied.x = 3 := by rfl
"#,
    );
    let environment = checked.engine.environment();
    let mut printer = fln::pretty::Printer::new(environment);
    for (name, expected) in [
        ("omitted", "{ y := 0 }"),
        ("supplied", "{ x := 3, y := 0 }"),
    ] {
        let Some(fln::ConstantInfo::Defn(definition)) =
            environment.find(&Name::from_components([name]))
        else {
            panic!("missing checked record value {name}");
        };
        // The frozen helper's marker must neither hide an override nor prevent
        // printing an ordinary record whose inherited value equals its default.
        assert_eq!(printer.expr(&definition.value, 0).unwrap(), expected);
    }
}

#[test]
fn inherited_defaults_use_declared_relaxed_c3_precedence() {
    check(
        &engine(),
        r#"
structure A where
  x : Nat := 1
structure B extends A
structure C where
  x : Nat := 2
structure D extends B, C
def inherited : D := {}
example : inherited.x = 2 := by rfl

structure First where
  x : Nat := 3
structure Earlier extends First, C
def earlier : Earlier := {}
example : earlier.x = 3 := by rfl

structure Required where
  x : Nat
structure WithCopied where
  x : Nat
  y : Nat := 4
structure Middle extends Required, WithCopied
structure Override where
  y : Nat := 5
structure Bottom extends Middle, Override
def copied : Bottom := { x := 0 }
example : copied.y = 5 := by rfl
"#,
    );
}

#[test]
fn inherited_defaults_follow_real_dependencies_even_later_flat_fields() {
    check(
        &engine(),
        r#"
structure B where
  x : Nat
structure C where
  z : Nat
  x : Nat := z
structure D extends B, C
def d : D := { z := 5 }
example : d.x = 5 := by rfl

structure NeedsMethod where
  f : Nat → Nat
  n : Nat
structure ProvidesMethod where
  n : Nat
  f (n : Nat) : Nat := n + 1
structure Method extends NeedsMethod, ProvidesMethod
def method : Method := { n := 8 }
example : method.f 4 = 5 := by rfl
"#,
    );
}

#[test]
fn inherited_defaults_instantiate_owner_parameters_and_universes() {
    check(
        &engine(),
        r#"
universe u
structure Needed (A : Type u) where
  value : A
structure Fallback (n : Nat) (A : Type u) (a : A) where
  value : A := a
  count : Nat := n
  copy : A := value
structure Combined (A : Type u) (a : A) (n : Nat) extends Needed A, Fallback n A a
def natural : Combined Nat 17 4 := {}
def higher : Combined Type Nat 6 := {}
example : natural.value = 17 := by rfl
example : natural.count = 4 := by rfl
example : natural.copy = 17 := by rfl
example : higher.value = Nat := by rfl
example : higher.copy = Nat := by rfl
"#,
    );
}

#[test]
fn inherited_defaults_capture_section_parameters_of_fully_copied_parents() {
    check(
        &engine(),
        r#"
section
variable (n : Nat)
structure Needs where
  x : Nat
structure Provides where
  x : Nat := n
structure Both extends Needs, Provides n
end
def result : Both 7 := {}
example : result.x = 7 := by rfl
"#,
    );
}

#[test]
fn native_defaults_keep_physical_parent_literals_and_flat_own_defaults() {
    check(
        &engine(),
        r#"
structure B where
  x : Nat := 2
structure C where
  x : Nat
  z : Nat := 5
structure D extends B, C where
  total : Nat := x + z
def flat : D := {}
def parent : B := { x := 11 }
def physical : D := { toB := parent }
example : flat.x = 2 := by rfl
example : flat.z = 5 := by rfl
example : flat.total = 7 := by rfl
example : physical.x = 11 := by rfl
example : physical.z = 5 := by rfl
example : physical.total = 16 := by rfl

structure Native extends Inhabited Nat
structure DerivedNative extends Native
def native : DerivedNative := { default := 8 }
example : native.default = 8 := by rfl
"#,
    );
}

#[test]
fn inherited_defaults_are_frozen_before_later_parent_helpers() {
    let e = check(
        &engine(),
        r#"
structure B where
  x : Nat
structure C where
  x : Nat
structure D extends B, C
def C.x._default : Nat := 9
"#,
    )
    .engine;
    check(&e, "def own : C := {}\nexample : own.x = 9 := by rfl");
    let before = e.logical_root(&KVMap::new());
    let refusal = e
        .check_source_files(
            &[b"def absent : D := {}"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("a later ancestor helper must not retroactively alter D");
    assert!(
        format!("{refusal:?}").contains("MissingField"),
        "{refusal:?}"
    );
    assert_eq!(e.logical_root(&KVMap::new()), before);
    check(
        &e,
        "def supplied : D := { x := 4 }\nexample : supplied.x = 4 := by rfl",
    );
}

#[test]
fn class_dictionaries_can_be_constructed_entirely_from_defaults() {
    check(
        &engine(),
        "class Config where\n  value : Nat := 7\n  twice : Nat := value + value\ninstance automatic : Config := {}\ndef result : Nat := Config.twice\ntheorem ok : result = 14 := by rfl\ndef explicit : Config := { value := 11 }\ntheorem other : explicit.twice = 22 := by rfl",
    );
}
#[test]
fn nested_record_literals_and_let_defaults_are_elaborated_natively() {
    check(
        &engine(),
        "structure Inner where\n  value : Nat := 8\nstructure Outer where\n  inner : Inner := {}\n  num : Nat := let n := inner.value; n + 1\ndef result : Outer := {}\ntheorem ok : result.num = 9 := by rfl",
    );
}
#[test]
fn invalid_defaults_are_rejected_even_when_never_used() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let run = |source: &str| {
        e.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
    };
    // Each is refused while elaborating, as the pin refuses it: a numeral with no
    // `OfNat` instance at its type, and a string default where a `Nat` is expected
    // (the pin's "Type mismatch", a rigid mismatch: fln-azxg). Each twin must check.
    for (text, disposition, twin) in [
        (
            "structure Bad where\n  value : Nat := \"wrong\"",
            ("elaboration", false, 1),
            "structure Bad where\n  value : Nat := 7",
        ),
        (
            "structure Bad where\n  carrier : Type\n  value : carrier := 7",
            ("elaboration", false, 1),
            "structure Bad where\n  carrier : Type\n  value : Nat := 7",
        ),
        (
            "structure Bad where\n  value : Nat := (1 : String)",
            ("elaboration", false, 1),
            "structure Bad where\n  value : Nat := (1 : Nat)",
        ),
        (
            "structure Bad where\n  value : Nat := let unused := (1 : String); 0",
            ("elaboration", false, 1),
            "structure Bad where\n  value : Nat := let unused := \"one\"; 0",
        ),
    ] {
        let refusal = run(text).expect_err("invalid default is not optional evidence");
        assert_eq!(refusal.disposition(), disposition, "{text}: {refusal:?}");
        assert_eq!(e.logical_root(&KVMap::new()), root);
        assert!(matches!(run(twin), Ok(Outcome::Complete(_))), "{twin}");
    }
}
#[test]
fn forward_defaults_missing_required_fields_and_unresolved_values_refuse() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for text in [
        "structure Bad where\n  x : Nat := later\n  later : Nat := 3",
        "structure Bad where\n  x : Nat := _",
        "structure Bad where\n  x : Nat := x",
        "structure Needs where\n  first : Nat\n  second : Nat := first\ndef incomplete : Needs := {}",
    ] {
        assert!(
            e.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn checked_helpers_follow_the_pin_only_for_registered_structure_interfaces() {
    let e = check(
        &engine(),
        "structure Plain where\n  value : Nat\ndef Plain.value._default : Nat := 91",
    )
    .engine;
    // The pin's Lean/Structure.lean getFnForFieldUsing? looks up this checked
    // helper once the structure identity exists, without a native default row.
    assert!(
        RecordDefaults::read(e.environment())
            .unwrap()
            .helper(&Name::from_components(["Plain"]), 0)
            .is_none()
    );
    check(
        &e,
        "def inferred : Plain := {}\ntheorem default_value : inferred.value = 91 := by rfl",
    );
    check(&e, "def explicit : Plain := { value := 4 }");

    let bare = check(
        &engine(),
        "inductive Bare where | mk (value : Nat)\ndef Bare.value._default : Nat := 91",
    )
    .engine;
    assert!(
        bare.check_source_files(
            &[b"def absent : Bare := {}"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    check(&bare, "def explicit : Bare := { value := 4 }");

    let wrong = check(
        &engine(),
        "structure Wrong where\n  value : Nat\ndef Wrong.value._default : Bool := Bool.true",
    )
    .engine;
    assert!(
        wrong
            .check_source_files(
                &[b"def absent : Wrong := {}"],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}
#[test]
fn helper_collision_leaves_no_record_projection_or_registration_prefix() {
    let e = check(&engine(), "def Clash.value._default : Nat := 5").engine;
    let root = e.logical_root(&KVMap::new());
    assert!(
        e.check_source_files(
            &[b"structure Clash where\n  value : Nat := 7"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    assert_eq!(e.logical_root(&KVMap::new()), root);
    assert!(!e.environment().contains(&Name::from_components(["Clash"])));
    assert!(
        RecordDefaults::read(e.environment())
            .unwrap()
            .helper(&Name::from_components(["Clash"]), 0)
            .is_none()
    );
}
#[test]
fn registration_checks_helper_signatures_and_rejects_duplicates_atomically() {
    let e = check(&engine(), "structure Good where\n  value : Nat := 8\nstructure Wrong where\n  value : Nat\ndef Wrong.value._default : String := \"not Nat\"").engine;
    let root = e.logical_root(&KVMap::new());
    let row = |name: &str| {
        let record = Name::from_components([name]);
        RecordDefault {
            helper: helper_name(&record, &Name::from_components(["value"])),
            record,
            field: 0,
        }
    };
    let registered = register_defaults(e.environment(), &[row("Good")]).unwrap();
    assert!(register_defaults(&registered, &[row("Good")]).is_err());
    assert!(register_defaults(e.environment(), &[row("Wrong")]).is_err());
    assert_eq!(e.logical_root(&KVMap::new()), root);
}
#[test]
fn ordered_files_share_only_successful_default_registrations() {
    let e = engine();
    let prefix = b"structure Count where\n  value : Nat := 23";
    let good = b"def n : Count := {}\ntheorem ok : n.value = 23 := by rfl";
    let bad = b"def n : Count := {}\ntheorem wrong : n.value = 24 := by rfl";
    for (suffix, success) in [
        (good.as_slice(), true),
        (bad.as_slice(), false),
        (good.as_slice(), true),
    ] {
        let result = e.check_source_files(
            &[prefix, suffix],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            success,
            "{result:?}"
        );
    }
}

#[test]
fn admission_root_includes_the_structure_interface_and_default_helpers() {
    let e = engine();
    let result = e
        .admit_source_command(
            b"structure Count where\n  value : Nat := 23",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.base_logical_root, e.logical_root(&KVMap::new()));
    assert_eq!(
        result.result_logical_root,
        result.engine.logical_root(&KVMap::new())
    );
    assert_ne!(
        result.result_logical_root,
        result.admissions.last().unwrap().result_logical_root
    );
    let record = Name::from_components(["Count"]);
    let helper = helper_name(&record, &Name::from_components(["value"]));
    assert!(
        RecordDefaults::read(result.engine.environment())
            .unwrap()
            .helper(&record, 0)
            .is_none()
    );
    assert!(result.engine.environment().contains(&helper));
    // The block, projection, flat constructor, default helper, recOn, and casesOn.
    assert_eq!(result.admissions.len(), 6);
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["Count", "mk", "_flat_ctor"]))
    );
}

#[test]
fn child_defaults_override_inherited_fields_without_changing_the_parent_layout() {
    let checked = check(
        &engine(),
        r#"
structure Parent where
  value : Nat := 3
  method (n : Nat) : Nat := n + value
structure Child extends Parent where
  value := offset + 1
  method n := n + offset
  offset : Nat := 41
def original : Parent := {}
def inherited : Child := {}
def explicit : Child := { value := 9, offset := 5 }
def parentValue : Child := { toParent := { value := 8 }, offset := 2 }
def updated : Child := { inherited with offset := 100 }
example : original.value = 3 := by rfl
example : original.method 2 = 5 := by rfl
example : inherited.value = 42 := by rfl
example : inherited.method 2 = 43 := by rfl
example : explicit.value = 9 := by rfl
example : explicit.method 2 = 7 := by rfl
example : parentValue.value = 8 := by rfl
example : parentValue.method 2 = 10 := by rfl
example : updated.offset = 100 := by rfl
example : updated.value = 42 := by rfl
example : updated.method 2 = 43 := by rfl
"#,
    );
    let environment = checked.engine.environment();
    let Some(fln::ConstantInfo::Ctor(constructor)) =
        environment.find(&Name::from_components(["Child", "mk"]))
    else {
        panic!("missing checked Child constructor");
    };
    // Overrides change defaults; the constructor still takes toParent and offset.
    assert_eq!(constructor.num_fields, 2);
    for field in ["value", "method"] {
        let helper = helper_name(
            &Name::from_components(["Child"]),
            &Name::from_components([field]),
        );
        let Some(fln::ConstantInfo::Defn(definition)) = environment.find(&helper) else {
            panic!("missing checked override helper {helper:?}");
        };
        for expression in [&definition.base.type_, &definition.value] {
            assert!(!expression.has_expr_mvar());
            assert!(!expression.has_level_mvar());
            assert!(!expression.has_fvar());
            assert!(!expression.has_loose_bvars());
        }
    }
}

#[test]
fn inherited_overrides_capture_default_only_sections_parameters_and_universes() {
    check(
        &engine(),
        r#"
structure Parent where
  value : Nat
section
variable (fallback : Nat)
structure WithFallback extends Parent where
  value := fallback
end
def sectionValue : WithFallback 23 := {}
example : sectionValue.value = 23 := by rfl

universe u
structure Holder (A : Type u) where
  value : A
structure Filled (A : Type u) (fallback : A) extends Holder A where
  value := fallback
def natural : Filled Nat 17 := {}
def text : Filled String "chosen" := {}
def higher : Filled Type Nat := {}
example : natural.value = (17 : Nat) := by rfl
example : text.value = "chosen" := by rfl
example : higher.value = Nat := by rfl
"#,
    );
}

#[test]
fn copied_and_transitive_fields_keep_the_child_declared_default() {
    check(
        &engine(),
        r#"
structure First where
  x : Nat := 1
structure Second where
  x : Nat := 2
  y : Nat := 3
structure Diamond extends First, Second where
  x := 9
  y := 7
structure Bottom extends Diamond
def first : First := {}
def second : Second := {}
def diamond : Diamond := {}
def bottom : Bottom := {}
def explicit : Bottom := { x := 11, y := 13 }
example : first.x = 1 := by rfl
example : second.x = 2 := by rfl
example : second.y = 3 := by rfl
example : diamond.x = 9 := by rfl
example : diamond.y = 7 := by rfl
example : bottom.x = 9 := by rfl
example : bottom.y = 7 := by rfl
example : explicit.x = 11 := by rfl
example : explicit.y = 13 := by rfl
"#,
    );
}

#[test]
fn override_elaboration_keeps_independent_fields_and_hides_recursive_dependencies() {
    let base = check(
        &engine(),
        r#"
structure Parent where
  value : Nat
structure Grandchild extends Parent
structure Carrier where
  carrier : Type
structure FunctionParent where
  method : Nat → Nat
"#,
    )
    .engine;
    check(
        &base,
        r#"
structure Later extends Parent where
  value := (by guard_expr offset = offset; exact offset)
  offset : Nat := 8
def later : Later := {}
example : later.value = 8 := by rfl
structure TypedShadow (n : Nat) extends FunctionParent where
  method (n : Nat) := n
structure BareShadow (n : Nat) extends FunctionParent where
  method n := n
def typed : TypedShadow 2 := {}
def bare : BareShadow 3 := {}
example : typed.method 4 = 4 := by rfl
example : bare.method 4 = 4 := by rfl
"#,
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "structure Invalid extends Parent where\n  value := value",
        // guard_expr discards its compared expressions, so inspecting only the
        // resulting default term would miss this forbidden read of the field.
        "structure Invalid extends Parent where\n  value := (by guard_expr value = value; exact Nat.zero)",
        "structure Invalid extends Parent where\n  value := toParent.value",
        // witness's type depends on carrier; it must be hidden with carrier.
        "structure Invalid extends Carrier where\n  carrier := (by guard_expr witness = witness; exact Nat)\n  witness : carrier",
        "structure Invalid extends Parent where\n  value : Bool := Bool.false",
        "structure Invalid extends Parent where\n  value : Nat",
        "structure Invalid extends Parent where\n  value := 1\n  value := 2",
        "structure Invalid extends Parent where\n  toParent := { value := 0 }",
        "structure Invalid extends Grandchild where\n  toParent := { value := 0 }",
        // Leading typeless bracketed binders request a header binder update at
        // the pin. Overrides cannot change header parameters' binder kinds.
        "structure Invalid (n : Nat) extends FunctionParent where\n  method (n) := n",
        "section\nvariable (n : Nat)\nstructure Invalid extends FunctionParent where\n  method (n) := n\nend",
    ] {
        let result = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(result.is_err(), "{source}\n{result:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["Invalid"]))
        );
    }
    check(
        &base,
        "structure Valid extends Parent where\n  value := 17\ndef valid : Valid := {}\nexample : valid.value = 17 := by rfl",
    );
}

#[test]
fn parent_syntax_cannot_replace_a_child_override_with_an_ancestor_default() {
    let base = check(
        &engine(),
        r#"
structure A where
  x : Nat := 1
structure B where
  y : Nat := 2
structure Combined extends A, B where
  x := 9
structure Child extends A where
  x := 9
structure Transitive extends Child, B
"#,
    )
    .engine;
    check(
        &base,
        r#"
def supplied : Combined := { toA := { x := 7 }, toB := { y := 8 } }
def flat : Combined := { y := 8 }
example : supplied.x = 7 := by rfl
example : supplied.y = 8 := by rfl
example : flat.x = 9 := by rfl
example : flat.y = 8 := by rfl
def inherited : Transitive := {}
def suppliedTransitive : Transitive := { toChild := { x := 7 }, toB := { y := 8 } }
def flatTransitive : Transitive := { y := 8 }
example : inherited.x = 9 := by rfl
example : inherited.y = 2 := by rfl
example : suppliedTransitive.x = 7 := by rfl
example : suppliedTransitive.y = 8 := by rfl
example : flatTransitive.x = 9 := by rfl
example : flatTransitive.y = 8 := by rfl
"#,
    );
    let root = base.logical_root(&KVMap::new());
    // Mixed parent syntax does not yet rebuild an omitted overridden leaf.
    // Refuse this boundary instead of silently taking A's default x = 1.
    for source in [
        "def omitted : Combined := { toB := { y := 8 } }",
        "def omitted : Transitive := { toB := { y := 8 } }",
    ] {
        let result = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(result.is_err(), "{source}\n{result:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["omitted"]))
        );
    }
}

#[test]
fn proof_override_and_frozen_helpers_remain_checked_semireducible_definitions() {
    let checked = check(
        &engine(),
        r#"
structure ProofBase where
  value : Nat := 7
  proof : value = value
structure ProofChild extends ProofBase where
  proof := rfl
structure ProofGrandchild extends ProofChild
def child : ProofChild := {}
def grandchild : ProofGrandchild := {}
example : child.value = 7 := by rfl
example : grandchild.value = 7 := by rfl
example : child.value = child.value := child.proof
example : grandchild.value = grandchild.value := grandchild.proof
"#,
    );
    let environment = checked.engine.environment();
    for (record, suffix) in [
        ("ProofChild", "_default"),
        ("ProofGrandchild", "_inherited_default"),
    ] {
        let name = Name::from_components([record, "proof", suffix]);
        let Some(fln::ConstantInfo::Defn(definition)) = environment.find(&name) else {
            panic!("a checked proof default must remain a definition: {name:?}");
        };
        assert_eq!(definition.safety, fln::DefinitionSafety::Safe);
        assert_eq!(definition.hints, fln::ReducibilityHints::Abbrev);
        assert_eq!(
            fln_elab::reducibility::known_status(environment, &name).unwrap(),
            Some(fln_elab::reducibility::Reducibility::Semireducible),
        );
        for expression in [&definition.base.type_, &definition.value] {
            assert!(!expression.has_expr_mvar());
            assert!(!expression.has_level_mvar());
            assert!(!expression.has_fvar());
            assert!(!expression.has_loose_bvars());
        }
    }
}
