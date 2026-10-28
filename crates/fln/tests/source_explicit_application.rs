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

/// Under `@`, a bare `_` given for an instance parameter is still synthesized (the pin's
/// `processInstImplicitArg`), in the ordinary and the named-argument path alike. The pin
/// accepts each of these (checked 2026-10-28).
#[test]
fn explicit_holes_for_instance_parameters_are_synthesized() {
    let base = check(
        &engine(),
        "class Pick (α : Type) where\n  pick : α\ninstance : Pick Nat := ⟨7⟩\ndef choose (α : Type) [Pick α] (x : α) : α := Pick.pick",
    )
    .engine;
    for value in [
        "@choose Nat _ 0",
        "@choose Nat _ (x := 0)",
        "@HAdd.hAdd Nat Nat Nat _ 3 4",
    ] {
        let result = check(
            &base,
            &format!("theorem synthesized : ({value}) = 7 := by rfl"),
        );
        assert_eq!(result.theorems, 1);
    }
}

/// Such a hole is one of the application's own instance arguments (App.lean's local
/// `mkInstMVar`). Under `@` the pin propagates the expected result before each written argument
/// that is not a hole, once the result depends on none of the arguments left, and never before
/// a hole. So an output an instance would fix and the expected type would fix is fixed by
/// whichever comes first. `Get Nat Bool` and `Coe Bool Box` make the difference observable:
/// - `solved`: the class input is written, so the instance fixes `Bool` and it is coerced;
/// - `stuck`: `Box` is propagated before `(3 : Nat)`, and `Get Nat Box` is refused;
/// - `midway`: as `stuck` with one more argument, which an earlier synthesis would precede;
/// - `dependent`: the result depends on the last argument, so nothing is propagated;
/// - `last`: the last argument is the instance hole, before which nothing is propagated.
///
/// The pin accepts `solved`, `dependent` and `last` and refuses `stuck` and `midway` with
/// "failed to synthesize instance" (checked 2026-10-28).
#[test]
fn an_explicit_instance_hole_meets_the_expected_type_where_the_pin_propagates_it() {
    let coercions = Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let base = check(
        &coercions,
        "class Get (c : Type) (e : outParam Type) where\n  get : c → e\ninstance : Get Nat Bool := ⟨fun _ => true⟩\nclass Get2 (c : Type) (e : outParam Type) where\n  get2 : c → Nat → e\ninstance : Get2 Nat Bool := ⟨fun _ _ => true⟩\nstructure Box where\n  value : Bool\ninstance : Coe Bool Box := ⟨Box.mk⟩\ndef tagged (c e : Type) [Get c e] (x : c) : (k : Nat) → (fun _ => e) k := fun _ => Get.get x\ndef viaLast (c : Type) (x : c) (e : Type) [Get c e] : e := Get.get x",
    )
    .engine;
    for accepted in [
        "def solved : Box := @Get.get Nat _ _ (3 : Nat)\ntheorem solved_value : solved.value = true := rfl",
        "def dependent : Box := @tagged _ _ _ (3 : Nat) 0\ntheorem dependent_value : dependent.value = true := rfl",
        "def last : Box := @viaLast Nat 3 _ _\ntheorem last_value : last.value = true := rfl",
    ] {
        assert_eq!(check(&base, accepted).theorems, 1, "{accepted}");
    }
    let root = base.logical_root(&KVMap::new());
    for refused in [
        "def stuck : Box := @Get.get _ _ _ (3 : Nat)",
        "def midway : Box := @Get2.get2 _ _ _ (3 : Nat) 0",
    ] {
        let error = base
            .check_source_files(&[refused.as_bytes()], &KVMap::new(), limits())
            .err()
            .unwrap_or_else(|| panic!("accepted {refused}"));
        assert!(
            format!("{error:?}").contains("InstanceSynthesisRequired"),
            "{refused}: {error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn explicit_local_functions_and_strict_implicits_remain_typed() {
    check(
        &engine(),
        "def strict ⦃A : Type⦄ (a : A) : A := a\ntheorem strict_ok : @strict Nat 7 = 7 := by rfl\ndef localCall (f : {A : Type} -> A -> A) : Nat := @f Nat 7",
    );
}

#[test]
fn ordinary_applications_synthesize_trailing_instances_without_a_result_hint() {
    let checked = check(
        &engine(),
        concat!(
            "def read (n : Nat) [Inhabited Nat] : Nat := n + default\n",
            "def ordinary := read 7\n",
            "def named := read (n := 7)\n",
            "def decided := decide (7 = 7)\n",
            "def explicit := @read 7\n",
            "def delayed (n : Nat) ⦃A : Type⦄ (x : A) : A := x\n",
            "def pending := delayed 7\n",
            "theorem ordinary_ok : ordinary = 7 := by rfl\n",
            "theorem named_ok : named = 7 := by rfl\n",
            "theorem decided_ok : decided = true := by rfl\n",
        ),
    );
    for (name, expected) in [("ordinary", "Nat"), ("named", "Nat"), ("decided", "Bool")] {
        let Some(ConstantInfo::Defn(definition)) = checked
            .engine
            .environment()
            .find(&Name::from_components([name]))
        else {
            panic!("checked definition {name}");
        };
        assert!(
            matches!(definition.base.type_.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components([expected]))
        );
    }
    for (name, expected) in [
        ("explicit", BinderInfo::InstImplicit),
        ("pending", BinderInfo::StrictImplicit),
    ] {
        let Some(ConstantInfo::Defn(definition)) = checked
            .engine
            .environment()
            .find(&Name::from_components([name]))
        else {
            panic!("checked definition {name}");
        };
        assert!(
            matches!(definition.base.type_.node(), ExprNode::ForallE { binder_info, .. }
            if *binder_info == expected)
        );
    }
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
