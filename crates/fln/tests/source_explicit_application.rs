//! Explicit arguments use the same unifier, checking council, and source transaction.
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
fn check(base: &Engine, text: &str) -> fln::SourceFileCheck {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{text}\n{e:?}"))
        .into_complete()
        .unwrap()
}
const ID: &str = "def identity {A : Sort u} (a : A) : A := a\n";

#[test]
fn explicit_heads_supply_implicit_arguments_and_preserve_ordinary_calls() {
    let base = check(&engine(), ID).engine;
    for value in [
        "@identity Nat 7",
        "(@identity) Nat 7",
        "@identity.{1} Nat 7",
        "identity 7",
        "@identity _ 7",
    ] {
        let result = check(
            &base,
            &format!("theorem explicit_ok : ({value}) = 7 := by rfl"),
        );
        assert_eq!(result.theorems, 1);
    }
}

#[test]
fn explicitness_does_not_leak_into_nested_argument_elaboration() {
    let base = check(&engine(), ID).engine;
    check(
        &base,
        "theorem nested_ok : (@identity Nat (identity 7)) = 7 := by rfl",
    );
}

#[test]
fn explicit_bare_heads_keep_unsupplied_implicit_binders() {
    let base = check(&engine(), ID).engine;
    let result = check(&base, "def whole := @identity");
    let Some(ConstantInfo::Defn(decl)) = result
        .engine
        .environment()
        .find(&Name::from_components(["whole"]))
    else {
        panic!("checked definition");
    };
    assert!(matches!(
        decl.base.type_.node(),
        ExprNode::ForallE {
            binder_info: BinderInfo::Implicit,
            ..
        }
    ));
}

#[test]
fn explicit_instance_arguments_are_consumed_not_synthesized() {
    check(
        &engine(),
        "class Boxed where\n  n : Nat\ndef number [b : Boxed] : Nat := b.n\ntheorem explicit_dict (b : Boxed) : @number b = b.n := by rfl",
    );
}

#[test]
fn explicit_local_functions_and_strict_implicits_remain_typed() {
    check(
        &engine(),
        "def strict ⦃A : Type⦄ (a : A) : A := a\ntheorem strict_ok : @strict Nat 7 = 7 := by rfl\ndef localCall (f : {A : Type} -> A -> A) : Nat := @f Nat 7",
    );
}

#[test]
fn malformed_or_missing_explicit_arguments_cannot_publish() {
    let base = check(&engine(), ID).engine;
    let root = base.logical_root(&KVMap::new());
    for text in [
        "def bad : Nat := @identity 7",
        "def bad : Nat := @identity Nat True.intro",
        "def bad : Nat := @identity _ _",
        "def bad := @missing",
        "def bad := @(_)",
    ] {
        assert!(
            base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{text}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    check(&base, "theorem recovery : @identity Nat 7 = 7 := by rfl");
}
