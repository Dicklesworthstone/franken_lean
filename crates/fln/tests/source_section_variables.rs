//! Section commands -> elaboration -> both declaration checkers. No admission
//! fixture is substituted for the real source/module entry points.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};

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
fn binders(engine: &Engine, name: &str) -> Vec<(Name, BinderInfo)> {
    let mut ty = engine
        .environment()
        .find(&n(name))
        .unwrap()
        .constant_val()
        .type_
        .clone();
    let mut result = Vec::new();
    while let ExprNode::ForallE {
        binder_name,
        binder_info,
        body,
        ..
    } = ty.node()
    {
        result.push((binder_name.clone(), *binder_info));
        ty = body.clone();
    }
    result
}

#[test]
fn definitions_generalize_only_used_dependencies_in_declaration_order() {
    let e = checked(
        &engine(),
        r#"section
variable {A : Type u} (unused : Nat) (x : A)
def identity := x
def consume (f : A -> Nat) : Nat := f x
def independent : Nat := 7
end
theorem identityWorks : identity 7 = 7 := by rfl
theorem consumeWorks : consume 3 (fun x => x + 1) = 4 := by rfl
theorem independentWorks : independent = 7 := by rfl"#,
    );
    assert_eq!(
        binders(&e, "identity"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("x"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "consume")
            .iter()
            .map(|(n, _)| n.to_display_string())
            .collect::<Vec<_>>(),
        ["A", "x", "f"]
    );
    assert!(binders(&e, "independent").is_empty());
    assert!(!e.environment().contains(&n("A")));
    assert!(!e.environment().contains(&n("x")));
}

#[test]
fn theorem_headers_select_parameters_and_dependent_local_instances() {
    let e = checked(
        &engine(),
        r#"section
variable {A : Type} [inh : Inhabited A] (x : A)
variable {B : Type} [other : Inhabited B]
theorem self : x = x := by rfl
def chosen : A := default
end
theorem chosenWorks : chosen (A := Nat) = 0 := by rfl"#,
    );
    assert_eq!(
        binders(&e, "self"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("inh"), BinderInfo::InstImplicit),
            (n("x"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "chosen"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("inh"), BinderInfo::InstImplicit)
        ]
    );
}

#[test]
fn proof_bodies_cannot_silently_add_assumptions() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "variable (h : False)\ntheorem invalid : False := by exact h",
        "variable (p : Prop) (h : p)\ntheorem invalid : p := by exact h",
        "section\nvariable (x : Nat)\nend\ndef invalid := x",
        "namespace Hidden\nvariable (x : Nat)\nend Hidden\ndef invalid := x",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
    checked(&base, "theorem recovery : 7 = 7 := by rfl");
}

#[test]
fn variable_types_are_checked_even_without_subsequent_declarations() {
    let base = engine();
    for source in [
        "variable (x : 7)",
        "variable (A : Type) (x : A) (bad : x)",
        "variable (x : Missing)",
        "variable [bad : Nat]",
        "variable (x : _)",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
    let after = checked(&base, "variable {A : Type u} (x : A)");
    assert_eq!(
        base.logical_root(&KVMap::new()),
        after.logical_root(&KVMap::new())
    );
}

#[test]
fn section_lifetimes_shadowing_and_escaped_binders_preserve_identity() {
    let e = checked(
        &engine(),
        r#"namespace Outer
variable (x : Nat)
section Inner
variable (y : Nat)
def both : Nat := x + y
end Inner
def shadow (x : Bool) : Bool := x
def one : Nat := x
variable («a.b» : Nat)
def escaped := «a.b»
end Outer
theorem works : Outer.both 3 4 = 7 := by rfl
theorem shadowWorks : Outer.shadow true = true := by rfl
theorem escapedWorks : Outer.escaped 8 = 8 := by rfl"#,
    );
    assert_eq!(
        binders(&e, "Outer.one"),
        vec![(n("x"), BinderInfo::Default)]
    );
    assert_eq!(binders(&e, "Outer.shadow").len(), 1);
}

/// `replaceBinderAnnotation` changes the earlier declaration, not the local's
/// identity or the declarations already closed over it. This covers all three
/// ordinary binder styles, a partial group update, and restoration at `end`.
#[test]
fn section_binder_updates_preserve_dependencies_and_lexical_lifetimes() {
    let e = checked(
        &engine(),
        r#"section
variable (A B : Type) (a : A) (b : B)
def beforeUpdate := a
variable {A}
def afterUpdate := a
def untouched := b
section
variable ⦃A⦄
def strictUpdate := a
end
def restoredImplicit := a
variable (A) {B}
def restoredExplicit := a
def otherUpdate := b
end
theorem firstWorks : beforeUpdate Nat 7 = 7 := rfl
theorem secondWorks : afterUpdate 8 = 8 := rfl
theorem strictWorks : strictUpdate 9 = 9 := rfl
theorem restoredWorks : restoredExplicit Nat 10 = 10 := rfl"#,
    );
    for (name, parameter, value, style) in [
        ("beforeUpdate", "A", "a", BinderInfo::Default),
        ("afterUpdate", "A", "a", BinderInfo::Implicit),
        ("untouched", "B", "b", BinderInfo::Default),
        ("strictUpdate", "A", "a", BinderInfo::StrictImplicit),
        ("restoredImplicit", "A", "a", BinderInfo::Implicit),
        ("restoredExplicit", "A", "a", BinderInfo::Default),
        ("otherUpdate", "B", "b", BinderInfo::Implicit),
    ] {
        assert_eq!(
            binders(&e, name),
            [(n(parameter), style), (n(value), BinderInfo::Default)],
            "{name}"
        );
    }
}

#[test]
fn section_instance_binder_updates_change_generalized_calling_conventions() {
    let e = checked(
        &engine(),
        r#"class SectionPick (A : Type) where
  value : A
section
variable (A : Type) (inst : SectionPick A)
variable [inst]
def selected : A := SectionPick.value
variable {inst}
def explicitSelection : A := @SectionPick.value A inst
end
theorem explicitSelectionWorks : @explicitSelection Nat (SectionPick.mk 17) = 17 := rfl"#,
    );
    assert_eq!(
        binders(&e, "selected"),
        [
            (n("A"), BinderInfo::Default),
            (n("inst"), BinderInfo::InstImplicit)
        ]
    );
    assert_eq!(
        binders(&e, "explicitSelection"),
        [
            (n("A"), BinderInfo::Default),
            (n("inst"), BinderInfo::Implicit)
        ]
    );
}

#[test]
fn new_variables_after_annotation_updates_keep_replay_identities() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type)
variable {A}
variable (a : A)
def afterNewVariable := a
variable (A)
variable ⦃A⦄
variable (b : A)
def afterTwoUpdates := b
end
section
variable (A : Type) (a : A)
variable {A B} (b : B)
def residueOld := a
def residueNew := b
end
theorem firstIdentity : afterNewVariable 23 = 23 := rfl
theorem secondIdentity : afterTwoUpdates 29 = 29 := rfl"#,
    );
    assert_eq!(
        binders(&e, "afterNewVariable"),
        [
            (n("A"), BinderInfo::Implicit),
            (n("a"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "afterTwoUpdates"),
        [
            (n("A"), BinderInfo::StrictImplicit),
            (n("b"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "residueOld"),
        [
            (n("A"), BinderInfo::Implicit),
            (n("a"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "residueNew"),
        [
            (n("B"), BinderInfo::Implicit),
            (n("b"), BinderInfo::Default)
        ]
    );
}

#[test]
fn section_shadowing_keeps_old_dependencies_and_updates_only_the_latest_name() {
    let e = checked(
        &engine(),
        r#"section
variable (A : Type) (a : A)
variable (A : Type) (b : A)
variable {A}
def older := a
def newer := b
end
section
variable (x : Nat) (h : x = x)
variable (x : Bool)
def latest := x
theorem oldProof : h = h := rfl
end
section
variable (x : Nat) (x : Bool)
def sameCommand := x
end
section
variable (p q : Prop) (h : p)
variable (h : q)
include h
theorem includedHypothesis : p := h
end
theorem oldWorks : older Nat 17 = 17 := rfl
theorem newWorks : newer 19 = 19 := rfl
theorem latestWorks : latest true = true := rfl
theorem sameCommandWorks : sameCommand false = false := rfl"#,
    );
    assert_eq!(
        binders(&e, "older"),
        [(n("A"), BinderInfo::Default), (n("a"), BinderInfo::Default)]
    );
    assert_eq!(
        binders(&e, "newer"),
        [
            (n("A"), BinderInfo::Implicit),
            (n("b"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "oldProof"),
        [(n("x"), BinderInfo::Default), (n("h"), BinderInfo::Default)]
    );
    assert_eq!(
        binders(&e, "includedHypothesis"),
        [(n("p"), BinderInfo::Default), (n("h"), BinderInfo::Default)]
    );
    for name in ["latest", "sameCommand"] {
        let type_ = &e.environment().find(&n(name)).unwrap().constant_val().type_;
        assert!(
            matches!(type_.node(), ExprNode::ForallE { binder_type, .. }
                if matches!(binder_type.node(), ExprNode::Const { name, .. } if name == &n("Bool"))),
            "{name} must use the latest Bool binder"
        );
    }
}

#[test]
fn invalid_section_binder_updates_are_atomic() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for (source, expected) in [
        (
            "variable (A : Type)\nvariable (A)",
            "redundant binder annotation update",
        ),
        (
            "variable {A : Type}\nvariable {A}",
            "redundant binder annotation update",
        ),
        (
            "variable (x : Nat)\nvariable [x]",
            "instance binder must end in a registered class",
        ),
        (
            "class SectionPick where\n  value : Nat\nvariable (inst) (h : @Eq SectionPick inst inst)\nvariable [inst]",
            "variable was originally declared without an explicit type",
        ),
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err(source);
        assert!(error.to_string().contains(expected), "{source}: {error}");
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
}

/// The pin keeps a `variable` command's syntax and elaborates it again in each declaration. After
/// `open Second`, `x : Carrier` is ambiguous there (the pin's `stable` takes a `sorry`), and inside
/// `namespace Second` it names `Second.Carrier`. A declaration using such a variable is refused
/// here, never checked against the earlier `First.Carrier`; each refused program is refused by the
/// pin too, or accepted by it only with the reinterpreted (or `sorry`) type. Every verdict was
/// taken from the pinned `lean` v4.32.0 first.
#[test]
fn variable_types_are_elaborated_again_in_each_declaration() {
    let base = engine();
    let carriers = "namespace First\ndef Carrier := Nat\nend First\nnamespace Second\ndef Carrier := Bool\nend Second\n";
    let declared = format!("{carriers}open First\nvariable (x : Carrier)\n");
    for source in [
        // The pin: `rfl` fails (`stable` takes a `sorry`); accepted here before.
        format!(
            "{declared}open Second\ndef stable := x\ntheorem correct : stable (7 : Nat) = (7 : Nat) := by rfl"
        ),
        // The pin: `x : Second.Carrier`, so `(7 : Nat)` is a type mismatch; accepted here before.
        "def Carrier := Nat\nvariable (x : Carrier)\nnamespace Second\ndef Carrier := Bool\n\
         def stable := x\ntheorem t : stable (7 : Nat) = (7 : Nat) := rfl\nend Second"
            .to_owned(),
        // The pin accepts only with `x : sorry` ("declaration uses `sorry`").
        format!("{declared}open Second\ndef stable := x\ntheorem correct : stable 7 = 7 := by rfl"),
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
    for source in [
        // `Third` has no `Carrier`: the binder elaborates as before.
        format!(
            "{carriers}namespace Third\ndef Other := Bool\nend Third\nopen First\nvariable (x : Carrier)\n\
             open Third\ndef stable := x\ntheorem correct : stable (7 : Nat) = (7 : Nat) := by rfl"
        ),
        // A declaration that does not use the variable.
        format!("{declared}open Second\ndef other : Nat := 5\ntheorem t : other = 5 := rfl"),
        // Declared before the `open`.
        format!(
            "{declared}def stable := x\nopen Second\ntheorem correct : stable (7 : Nat) = (7 : Nat) := by rfl"
        ),
        // A binder of the same command that still elaborates as before.
        format!(
            "{carriers}open First\nvariable (n : Nat) (x : Carrier)\nopen Second\ndef twice := n + n\n\
             theorem t : twice 3 = 6 := rfl"
        ),
    ] {
        checked(&base, &source);
    }
}

#[test]
fn section_parameters_are_fixed_during_structural_recursion() {
    checked(
        &engine(),
        r#"section
variable (increment : Nat)
def count (n : Nat) : Nat := match n with
  | 0 => 0
  | Nat.succ k => increment + count k
end
theorem counted : count 3 4 = 12 := by rfl"#,
    );
}

#[test]
fn source_file_boundaries_export_closed_definitions_not_section_state() {
    let base = engine();
    let result = base
        .check_source_files(
            &[
                b"variable (x : Nat)\ndef keep := x",
                b"theorem imported : keep 9 = 9 := by rfl",
            ],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.theorems, 1);
    assert!(
        base.check_source_files(
            &[b"variable (x : Nat)\ndef keep := x", b"def leaked := x"],
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
}

#[test]
fn include_closes_dependencies_and_preserves_unused_explicit_assumptions() {
    let e = checked(
        &engine(),
        r#"section
variable (p : Prop) (h : p)
include h
theorem selected : p := by exact h
variable (unrelated : Nat)
theorem retained : 7 = 7 := by rfl
def independent : Nat := 7
omit h
theorem unselected : 7 = 7 := by rfl
end"#,
    );
    let expected = vec![(n("p"), BinderInfo::Default), (n("h"), BinderInfo::Default)];
    assert_eq!(binders(&e, "selected"), expected);
    assert_eq!(binders(&e, "retained"), expected);
    assert!(binders(&e, "independent").is_empty());
    assert!(binders(&e, "unselected").is_empty());
}

#[test]
fn omit_filters_automatic_instances_and_nested_scopes_restore_selection() {
    let e = checked(
        &engine(),
        r#"section
variable {A : Type} [inh : Inhabited A] (x : A)
theorem automatic : x = x := by rfl
section Inner
omit inh
theorem minimal : x = x := by rfl
end Inner
theorem restored : x = x := by rfl
omit inh
include inh
theorem forced : 7 = 7 := by rfl
end"#,
    );
    let automatic = vec![
        (n("A"), BinderInfo::Implicit),
        (n("inh"), BinderInfo::InstImplicit),
        (n("x"), BinderInfo::Default),
    ];
    assert_eq!(binders(&e, "automatic"), automatic);
    assert_eq!(binders(&e, "restored"), automatic);
    assert_eq!(
        binders(&e, "minimal"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("x"), BinderInfo::Default)
        ]
    );
    assert_eq!(
        binders(&e, "forced"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("inh"), BinderInfo::InstImplicit)
        ]
    );
}

#[test]
fn selections_reject_missing_variables_and_omitted_header_dependencies() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "include missing",
        "omit Nat",
        "variable (p : Prop) (h : p)\ninclude h missing",
        "variable (p : Prop) (h : p)\nomit h\ntheorem invalid : p := by exact h",
        "variable (p : Prop) (h : p)\ninclude h\nomit p\ntheorem invalid : 7 = 7 := by rfl",
        "variable (p : Prop)\nomit p\ntheorem invalid (h : p) : p := by exact h",
        "section\nvariable (h : False)\nend\ninclude h",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    checked(&base, "theorem recovery : 7 = 7 := by rfl");
}

#[test]
fn escaped_selection_is_lexical_and_does_not_leak_between_files() {
    let base = engine();
    let result = base.check_source_files(&[
        b"namespace N\nvariable (p : Prop) (\xC2\xABh.p\xC2\xBB : p)\ninclude \xC2\xABh.p\xC2\xBB\ntheorem selected : p := by exact \xC2\xABh.p\xC2\xBB\nend N",
        b"theorem fresh : 7 = 7 := by rfl",
    ], &KVMap::new(), limits()).unwrap().into_complete().unwrap();
    assert_eq!(
        binders(&result.engine, "N.selected"),
        vec![
            (n("p"), BinderInfo::Default),
            (Name::from_components(["h.p"]), BinderInfo::Default)
        ]
    );
    assert!(binders(&result.engine, "fresh").is_empty());
}

#[test]
fn generalized_named_instances_synthesize_after_the_section_ends() {
    let e = checked(
        &engine(),
        r#"class Pick (A : Type) where
  chosen : A
section
variable {A : Type} [inh : Inhabited A]
instance pickDefault : Pick A := { chosen := default }
end
def chosenNat : Nat := Pick.chosen
theorem chosenWorks : chosenNat = 0 := by rfl"#,
    );
    assert_eq!(
        binders(&e, "pickDefault"),
        vec![
            (n("A"), BinderInfo::Implicit),
            (n("inh"), BinderInfo::InstImplicit)
        ]
    );
}

#[test]
fn variable_source_edits_invalidate_module_caches_without_leaking_assumptions() {
    use fln::SourceModuleInput;
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };

    let names = [n("Base"), n("Main")];
    let mut session = SourceModuleSession::new(
        engine(),
        KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
        SourceModuleCacheLimits::default(),
    );
    let check = |session: &mut SourceModuleSession, base: &str, main: &str| {
        session.check_with_cancel(
            &[
                SourceModuleInput {
                    name: &names[0],
                    source: base.as_bytes(),
                },
                SourceModuleInput {
                    name: &names[1],
                    source: main.as_bytes(),
                },
            ],
            &names[1],
            None,
        )
    };
    let base = "variable (p : Prop) (h : p)\ninclude h\ntheorem chosen : p := by exact h";
    let main = "import Base\ntheorem use (p : Prop) (h : p) : p := by exact chosen p h";
    let cold = check(&mut session, base, main)
        .unwrap()
        .into_complete()
        .unwrap();
    let warm = check(&mut session, base, main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 2));
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    assert_eq!(
        warm.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    let omitted = "variable (p : Prop) (h : p)\nomit h\ntheorem chosen : p := by exact h";
    assert!(check(&mut session, omitted, main).is_err());
    let recovery = check(&mut session, base, main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        recovery.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    assert!(
        check(
            &mut session,
            base,
            "import Base\ntheorem leaked : p := by exact h"
        )
        .is_err()
    );
}
