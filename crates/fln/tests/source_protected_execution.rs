//! A `protected` declaration made by an executed command, in the seed world: as the pin's
//! `addProtected` leaves it, a later command's atomic name does not reach it through its
//! namespace, an `open` or an `export` alias (`resolveQualifiedName` and `getAliases …
//! (skipProtected := id.isAtomic)`, vendored `Lean/ResolveName.lean`). The execution path tags it
//! as the check path does. A definition it compiles and a theorem or template it only admits are
//! both tagged, and a protected definition still runs under its full name. These are the shapes
//! of `fln-cli`'s `source_protected_aliases`, which runs each program through the pinned `lean`
//! v4.32.0 first.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};
use fln_core::expr::ExprNode;
use fln_core::name::Name;
use fln_elab::protected_names::ProtectedNames;
use fln_env::constants::ConstantInfo;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn execute(source: &str) -> Result<Option<String>, String> {
    match engine().execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits()) {
        Ok(outcome) => {
            let run = outcome.into_complete().unwrap();
            Ok(match &run.executions.last().unwrap().exit {
                VmExit::Returned(value) => fln_vm::interpreter::nat_decimal(&value.value),
                _ => None,
            })
        }
        Err(error) => Err(format!("{error:?}")),
    }
}

const DOUBLE: &str = "protected def Foo.double (x : Nat) : Nat := x + x\n";

#[test]
fn an_atomic_name_does_not_reach_a_protected_declaration() {
    for program in [
        "open Foo\ndef y : Nat := double 3\n",
        "namespace Foo\ndef y : Nat := double 3\nend Foo\n",
        "namespace Ex\nexport Foo (double)\nend Ex\nopen Ex\ndef y : Nat := double 3\n",
        "export Foo (double)\ndef y : Nat := double 3\n",
    ] {
        let source = format!("{DOUBLE}{program}");
        assert!(execute(&source).is_err(), "accepted {source}");
    }
    // A protected theorem is admitted, not compiled; it is tagged the same way.
    let theorem = "protected theorem Foo.self (n : Nat) : n = n := rfl\nopen Foo\n\
                   theorem t : 3 = 3 := self 3\n";
    assert!(execute(theorem).is_err(), "accepted {theorem}");
}

#[test]
fn a_protected_definition_runs_under_its_full_name() {
    for (program, value) in [
        ("open Foo\ndef y : Nat := Foo.double 3\n#eval y\n", "6"),
        (
            "namespace Ex\nexport Foo (double)\nend Ex\ndef y : Nat := Ex.double 4\n#eval y\n",
            "8",
        ),
    ] {
        let source = format!("{DOUBLE}{program}");
        assert_eq!(
            execute(&source).unwrap_or_else(|error| panic!("{source}: {error}")),
            Some(value.to_owned()),
            "{source}"
        );
    }
}

fn check(source: &str) -> Result<Engine, String> {
    let check_limits = SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel));
    match engine().check_source_files(&[source.as_bytes()], &KVMap::new(), check_limits) {
        Ok(outcome) => Ok(outcome.into_complete().unwrap().engine),
        Err(error) => Err(format!("{error:?}")),
    }
}

#[test]
fn protected_structure_and_class_fields_match_pin_rules() {
    // Pin-verified (`Init/Prelude.lean:1582`): `class NatPow` marks `NatPow.pow` protected.
    let valid = "\
class MyNatPow (α : Type) where
  protected pow : α → Nat → α
def useQualified [MyNatPow Nat] (a n : Nat) : Nat := MyNatPow.pow a n
";
    let checked = check(valid).unwrap_or_else(|e| panic!("expected accept: {e}"));
    let protected = ProtectedNames::read(checked.environment()).unwrap();
    assert!(protected.contains(&Name::from_components(["MyNatPow", "pow"])));
    assert!(!protected.contains(&Name::from_components(["MyNatPow"])));

    // Unqualified `pow` must not resolve even after `open MyNatPow`.
    let unqualified = "\
class MyNatPow (α : Type) where
  protected pow : α → Nat → α
open MyNatPow
def bad [MyNatPow Nat] (a n : Nat) : Nat := pow a n
";
    assert!(
        check(unqualified).is_err(),
        "protected field must not be exposed unqualified by open"
    );

    // Copied parent fields inherit `protected` from the parent projection (`Structure.lean:669`).
    let copied = "\
structure A where
  x : Nat
structure B where
  x : Nat
  protected y : Nat
structure C extends A, B where
  z : Nat
";
    let copied_env = check(copied).unwrap_or_else(|e| panic!("expected copied accept: {e}"));
    let copied_protected = ProtectedNames::read(copied_env.environment()).unwrap();
    assert!(copied_protected.contains(&Name::from_components(["B", "y"])));
    assert!(copied_protected.contains(&Name::from_components(["C", "y"])));
    assert!(!copied_protected.contains(&Name::from_components(["C", "z"])));

    // Pin (`Structure.lean:362`): field cannot be marked `protected` on a `private` structure.
    let priv_struct = "\
private structure Priv where
  protected f : Nat
";
    assert!(
        check(priv_struct).is_err(),
        "protected field on private structure must be refused"
    );
}

#[test]
fn protected_inductive_and_structure_top_level_match_pin_rules() {
    // Pin-verified (`Init/Prelude.lean:1885`): `protected inductive Nat.le` in root namespace.
    let valid = "\
protected inductive Nat.myLe (n : Nat) : Nat → Prop
  | refl : Nat.myLe n n
  | step {m} : Nat.myLe n m → Nat.myLe n (Nat.succ m)
namespace T
protected inductive I where
  | mk : T.I
protected structure S where
  x : Nat
end T
def okI : T.I := T.I.mk
def okS : T.S := T.S.mk 1
";
    let checked = check(valid).unwrap_or_else(|e| panic!("expected accept: {e}"));
    let protected = ProtectedNames::read(checked.environment()).unwrap();
    assert!(protected.contains(&Name::from_components(["Nat", "myLe"])));
    assert!(!protected.contains(&Name::from_components(["Nat", "myLe", "refl"])));
    assert!(protected.contains(&Name::from_components(["T", "I"])));
    assert!(!protected.contains(&Name::from_components(["T", "I", "mk"])));
    assert!(protected.contains(&Name::from_components(["T", "S"])));
    assert!(!protected.contains(&Name::from_components(["T", "S", "x"])));

    // Atomic self-reference inside `protected inductive` constructor is refused by pin v4.32.0.
    let atomic_self = "\
namespace T
protected inductive I where
  | mk : I
end T
";
    assert!(
        check(atomic_self).is_err(),
        "atomic self-reference in protected inductive constructor must be refused"
    );

    // Atomic protected inductive/structure in root namespace is refused.
    for root_atomic in [
        "protected inductive RootI where\n  | mk : RootI\n",
        "protected structure RootS where\n  x : Nat\n",
    ] {
        assert!(
            check(root_atomic).is_err(),
            "root atomic protected data declaration must be refused: {root_atomic}"
        );
    }

    // `open T` must not expose `T.I` or `T.S` by atomic name.
    let opened = "\
namespace T
protected structure S where
  x : Nat
end T
open T
def bad : S := T.S.mk 1
";
    assert!(
        check(opened).is_err(),
        "protected structure must not resolve unqualified via open"
    );
}

#[test]
fn borrowed_annotation_and_bootstrap_gen_matcher_code_match_pin() {
    let source = "\
set_option bootstrap.genMatcherCode false in
protected def Nat.add2 : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero => a
  | a, Nat.succ b => Nat.succ (Nat.add2 a b)
def useBorrowed (m : @& Nat) : Nat := Nat.add2 m 1
";
    let checked = check(source).unwrap_or_else(|e| panic!("expected accept: {e}"));
    let Some(ConstantInfo::Defn(add2)) = checked
        .environment()
        .find(&Name::from_components(["Nat", "add2"]))
    else {
        panic!("Nat.add2 must be admitted as definition");
    };
    let ExprNode::ForallE { binder_type, .. } = add2.base.type_.node() else {
        panic!("Nat.add2 type must be a function");
    };
    let ExprNode::MData { data, .. } = binder_type.node() else {
        panic!("@& Nat parameter type must retain borrowed MData annotation");
    };
    assert!(data.get_bool(&Name::from_components(["borrowed"]), false));

    // Wrong option type for `bootstrap.genMatcherCode` must be refused.
    assert!(
        check("set_option bootstrap.genMatcherCode 1 in def x : Nat := 0\n").is_err(),
        "non-Bool bootstrap.genMatcherCode must be refused"
    );
}

#[test]
fn empty_inductive_and_class_size_of_match_pin_rules() {
    let source = "\
class SizeOf (α : Sort u) where
  sizeOf : α → Nat
class NoSizeOf (α : Type) where
  op : α → α
inductive NeverValue : Type where
def elimNever (x : NeverValue) : Nat := NeverValue.casesOn x
";
    let checked =
        check(source).unwrap_or_else(|e| panic!("empty inductive with SizeOf must succeed: {e}"));
    assert!(
        checked
            .environment()
            .contains(&Name::from_components(["NeverValue", "_sizeOf_1"])),
        "SizeOf generator must actually run for NeverValue"
    );
    assert!(
        checked
            .environment()
            .contains(&Name::from_components(["NeverValue", "_sizeOf_inst"])),
        "SizeOf instance must be admitted for NeverValue"
    );
    assert!(
        !checked
            .environment()
            .contains(&Name::from_components(["NoSizeOf", "_sizeOf_1"])),
        "Pin (`MutualInductive.lean:1574`) does not generate SizeOf for classes"
    );
    assert!(
        !checked
            .environment()
            .contains(&Name::from_components(["NoSizeOf", "_sizeOf_inst"])),
        "Pin (`MutualInductive.lean:1574`) does not generate SizeOf instances for classes"
    );
}
