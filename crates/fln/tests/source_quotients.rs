//! Quotient proofs and expected-type computation through the production seed.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::{ConstantInfo, QuotKind};

const EXAMPLE: &str = include_str!("../../../examples/native_quotients.lean");
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
fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn checked(base: &Engine, sources: &[&[u8]]) -> fln::SourceFileCheck {
    base.check_source_files(sources, &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("source checking failed: {e:?}"))
        .into_complete()
        .unwrap()
}

#[test]
fn source_seed_admits_the_quartet_and_keeps_sound_visibly_axiomatic() {
    let base = engine();
    for (text, kind) in [
        ("Quot", QuotKind::Type),
        ("Quot.mk", QuotKind::Ctor),
        ("Quot.lift", QuotKind::Lift),
        ("Quot.ind", QuotKind::Ind),
    ] {
        assert!(matches!(base.environment().find(&name(text)),
            Some(ConstantInfo::Quot(value)) if value.kind == kind));
    }
    assert!(matches!(base.environment().find(&name("Quot.sound")),
        Some(ConstantInfo::Axiom(value)) if !value.is_unsafe));
    let narrow = Engine::with_nat_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(!narrow.environment().contains(&name("Quot")));
}

#[test]
fn quotient_elimination_induction_and_expected_function_types_check_end_to_end() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let result = checked(&base, &[EXAMPLE.as_bytes()]);
    assert_eq!((result.commands, result.theorems), (7, 4));
    for text in [
        "readQuot",
        "related_representatives",
        "quotientFunction",
        "quotient_induction",
    ] {
        assert!(result.engine.environment().contains(&name(text)));
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&name("quotientFunction")));
}

#[test]
fn computation_cannot_erase_missing_or_invalid_respectfulness_evidence() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for bad in [
        "def bad : Nat := Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : True) => rfl) (Quot.mk (fun (a b : Nat) => True) 7)",
        "def bad : Nat := Quot.lift (fun (n : Nat) => n) _ (Quot.mk (fun (a b : Nat) => a = b) 7)",
        "theorem bad : 0 = 1 := Quot.sound True.intro",
        "theorem bad (q : Quot (fun (a b : Nat) => True)) : False := @Quot.ind Nat (fun (a b : Nat) => True) (fun (x : Quot (fun (a b : Nat) => True)) => False) (fun (a : Nat) => True.intro) q",
    ] {
        assert!(
            base.check_source_files(&[bad.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&name("bad")));
    }
    checked(&base, &[b"theorem recovered : 7 = 7 := by rfl"]);
}

#[test]
fn polymorphic_quotient_beta_preserves_both_universes() {
    let source = b"theorem lift_beta {A : Sort u} {r : A -> A -> Prop} {B : Sort v} (f : A -> B) (c : (a b : A) -> r a b -> f a = f b) (a : A) : Quot.lift f c (Quot.mk r a) = f a := by rfl";
    let result = checked(&engine(), &[source]);
    assert_eq!(result.theorems, 1);
    let Some(ConstantInfo::Thm(theorem)) = result.engine.environment().find(&name("lift_beta"))
    else {
        panic!("the beta law must retain a checked proof");
    };
    assert_eq!(theorem.base.level_params.len(), 2);
}

#[test]
fn quotient_definitions_remain_available_across_source_files() {
    let base = engine();
    let result = checked(&base, &[
        EXAMPLE.as_bytes(),
        b"theorem imported (n : Nat) : readQuot (Quot.mk (fun (a b : Nat) => a = b) n) = n := by rfl",
    ]);
    assert_eq!((result.commands, result.theorems), (8, 5));
}
