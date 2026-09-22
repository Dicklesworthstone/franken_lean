//! Section record declarations use the real source elaborator and both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};
use fln_env::constants::ConstantInfo;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn params(e: &Engine, name: &str) -> Vec<(Name, BinderInfo)> {
    let ConstantInfo::Induct(family) = e.environment().find(&n(name)).unwrap() else {
        panic!("not inductive")
    };
    let mut ty = family.base.type_.clone();
    let mut out = Vec::new();
    for _ in 0..family.num_params {
        let ExprNode::ForallE {
            binder_name,
            binder_info,
            body,
            ..
        } = ty.node()
        else {
            panic!("parameter missing")
        };
        out.push((binder_name.clone(), *binder_info));
        ty = body.clone();
    }
    assert!(!ty.has_loose_bvars());
    out
}

#[test]
fn fields_select_only_their_transitive_section_dependencies() {
    let e = checked(
        &engine(),
        r#"section
variable {A : Type u} (unused : Nat) (family : A -> Type v) (x : A)
structure Package where
  value : family x
structure Independent where
  value : Nat
end
def packed : Package (fun n : Nat => Nat) 7 := { value := 42 }
theorem works : packed.value = 42 := by rfl"#,
    );
    assert_eq!(
        params(&e, "Package"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("family"), BinderInfo::Default),
            (n("x"), BinderInfo::Default)
        ]
    );
    assert!(params(&e, "Independent").is_empty());
    for name in ["A", "family", "x", "unused"] {
        assert!(!e.environment().contains(&n(name)));
    }
}

#[test]
fn defaults_share_the_final_record_telescope_including_later_dependencies() {
    let e = checked(
        &engine(),
        r#"section
variable (unused : Nat) (seed : Nat) (offset : Nat)
structure Config where
  first : Nat := 1
  value : Nat := seed
  transform (n : Nat) : Nat := n + value + offset
end
def configured : Config 20 2 := {}
theorem firstWorks : configured.first = 1 := by rfl
theorem defaultWorks : configured.value = 20 := by rfl
theorem methodWorks : configured.transform 20 = 42 := by rfl
def changed : Config 20 2 := { configured with value := 40 }
theorem updateKeepsMethod : changed.transform 20 = 42 := by rfl"#,
    );
    assert_eq!(
        params(&e, "Config"),
        vec![
            (n("seed"), BinderInfo::Default),
            (n("offset"), BinderInfo::Default)
        ]
    );
}

#[test]
fn unused_section_variables_do_not_break_unrelated_defaults() {
    let e = checked(
        &engine(),
        r#"section
variable (unused : Nat) {A : Type u} (value : A)
structure Counter where
  value : Nat := 42
end
def counter : Counter := {}
theorem works : counter.value = 42 := by rfl"#,
    );
    assert!(params(&e, "Counter").is_empty());
}

#[test]
fn section_classes_inheritance_and_default_dictionaries_remain_usable() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type)
class Parent where
  value : A
class Child extends Parent A where
  map (x : A) : A := x
end
instance childNat : Child Nat := { value := 42 }
def answer : Nat := Parent.value
theorem works : answer = 42 := by rfl
section
variable {A : Type} [inh : Inhabited A]
structure Defaulted where
  value : A := default
end
def defaulted : Defaulted (A := Nat) := {}
theorem dictionaryWorks : defaulted.value = 0 := by rfl"#,
    );
    assert_eq!(params(&e, "Child"), vec![(n("A"), BinderInfo::Default)]);
    assert_eq!(
        params(&e, "Defaulted"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("inh"), BinderInfo::InstImplicit)
        ]
    );
}

#[test]
fn field_and_written_parameter_shadowing_do_not_capture_section_names() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type) (x : Nat) (unused : Nat)
structure Shadow (A : Type) where
  x : A
  keep (x : A) : A := x
structure Dependent where
  A : Type
  x : A
  copy : A := x
end
def s : Shadow Nat := { x := 7 }
theorem works : s.keep 42 = 42 := by rfl
def d : Dependent := { A := Nat, x := 42 }
theorem dependentWorks : d.copy = 42 := by rfl"#,
    );
    assert_eq!(params(&e, "Shadow"), vec![(n("A"), BinderInfo::Default)]);
    assert!(params(&e, "Dependent").is_empty());
}

#[test]
fn selected_theorem_assumptions_do_not_become_record_parameters() {
    let e = checked(
        &engine(),
        r#"section
variable (unused : Nat) (x : Nat)
include unused
omit x
structure Config where
  value : Nat := x
end
def config : Config 42 := {}
theorem works : config.value = 42 := by rfl"#,
    );
    assert_eq!(params(&e, "Config"), vec![(n("x"), BinderInfo::Default)]);
}

#[test]
fn failed_record_batches_and_scope_exits_do_not_publish_parameters_or_helpers() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "variable (x : Nat)\nstructure Bad where\n  value : Nat := true",
        "variable (x : Nat)\nstructure Bad where\n  value : Nat := x\n  later : Nat := true",
        "section\nvariable (x : Nat)\nend\nstructure Bad where\n  value : Nat := x",
        "variable (x : Nat)\nstructure Bad where\n  value : Nat := x\ntheorem wrong : 0 = 1 := by rfl",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for name in ["Bad", "Bad.mk", "Bad.value._default", "x"] {
            assert!(!base.environment().contains(&n(name)));
        }
    }
    let e = checked(
        &base,
        "variable (x : Nat)\nstructure Good where\n  value : Nat := x\ndef good : Good 42 := {}\ntheorem works : good.value = 42 := by rfl",
    );
    assert_eq!(params(&e, "Good"), vec![(n("x"), BinderInfo::Default)]);
}

#[test]
fn generalized_record_parameter_budget_is_a_resource_stop_not_rejection() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let names = (0..256).map(|i| format!("x{i}")).collect::<Vec<_>>();
    let source = format!(
        "variable ({} : Nat)\nstructure TooWide where\n  value : Nat := {}",
        names.join(" "),
        names.join(" + ")
    );
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&n("TooWide")));
    checked(
        &base,
        "variable (x : Nat)\nstructure Good where\n  value : Nat := x",
    );
}
