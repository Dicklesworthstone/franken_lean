//! Proof-producing rewriting through the production engine council.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits};
use fln_core::{name::Name, options::KVMap};
use fln_kernel::verdict::Budget;
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn prove(source: &str) {
    let base = engine();
    let admitted = base
        .admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    assert!(admitted.engine.environment().len() > base.environment().len());
}
#[test]
fn equality_symmetry_and_congruence_have_checked_eliminator_proofs() {
    prove("theorem symm (x y : Nat) (h : x = y) : y = x := by rw [h]");
    prove("theorem cong (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [h]");
    prove("theorem cong (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [<- h]");
    prove("theorem cong (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [← h]");
}
#[test]
fn rewriting_transports_proofs_in_both_directions() {
    prove(
        "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by rw [h]; exact hy",
    );
    prove(
        "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rw [← h]; exact hx",
    );
}
#[test]
fn rewriting_preserves_introduced_and_dependent_local_scopes() {
    prove(
        "theorem arrow (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by rw [h]; intro p; exact p",
    );
    prove(
        "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by intro hx; rw [← h]; exact hx",
    );
    prove(
        "theorem transport (P : Nat -> Prop) (x y : Nat) : x = y -> P x -> P y := by intro h hx; rw [← h]; exact hx",
    );
}
#[test]
fn explicit_rewrite_leaves_its_goal_while_rw_tries_reflexivity() {
    prove("theorem symm (x y : Nat) (h : x = y) : y = x := by rewrite [h]; rfl");
    assert!(
        engine()
            .admit_source_declaration(
                b"theorem symm (x y : Nat) (h : x = y) : y = x := by rewrite [h]",
                &KVMap::new(),
                limits()
            )
            .is_err()
    );
}

#[test]
fn rw_reflexivity_reduces_closed_arithmetic_through_the_kernel() {
    prove("theorem arithmetic (x : Nat) (h : x = 5) : 2 + 3 = x := by rw [h]");
    prove("theorem arithmetic (x : Nat) (h : 5 = x) : x = 2 + 3 := by rw [← h]");
    prove("theorem nested (x : Nat) (h : x = 20) : (2 + 3) * 4 = x := by rw [h]");
    prove(
        "theorem large (x : Nat) (h : x = 18446744073709551617) : 18446744073709551616 + 1 = x := by rw [h]",
    );
}

#[test]
fn rw_arithmetic_does_not_widen_definition_transparency_or_prove_false_equalities() {
    let options = KVMap::new();
    let base = engine()
        .admit_source_declaration(b"def identity (x : Nat) : Nat := x", &options, limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    for source in [
        "theorem bad (x : Nat) (h : x = 6) : 2 + 3 = x := by rw [h]",
        "theorem bad (x y : Nat) (h : x = y) : identity x = y := by rw [h]",
        "theorem bad (x : Nat) (h : x = 5) : identity x = 5 := by rw [h]",
    ] {
        let error = base
            .admit_source_declaration(source.as_bytes(), &options, limits())
            .unwrap_err();
        assert!(error.to_string().contains("unsolved goals"), "{error}");
    }
    for source in [
        "theorem explicit (x y : Nat) (h : x = y) : identity x = y := by rewrite [h]; rfl",
        "theorem explicit (x : Nat) (h : x = 5) : identity x = 5 := by rewrite [h]; rfl",
    ] {
        base.admit_source_declaration(source.as_bytes(), &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
    }
    assert_eq!(base.logical_root(&options), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn rw_arithmetic_resource_stop_is_not_an_unsolved_goal_or_rejection() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[b"theorem bounded (x : Nat) (h : x = 0) : (1 <<< 18446744073709551616) = x := by rw [h]"],
            &options,
            fln::SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("inconclusive", false, 3));
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["bounded"]))
    );
}
#[test]
fn rule_lists_apply_in_source_order_with_comments_and_newlines() {
    let source = "theorem trans (x y z : Nat) (h : x = y) (k : y = z) : x = z := by\r\n  rw [\r\n    h, -- first rewrite\r\n    k,\r\n  ]\r\n";
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    prove(source);
}
#[test]
fn rewrite_arguments_use_normal_source_elaboration() {
    prove("theorem use (x y : Nat) (f : Nat -> x = y) : y = x := by rw [f 0]");
}
#[test]
fn rewrite_universes_are_not_hardcoded_to_nat_or_prop() {
    prove("theorem symm {A : Type} (x y : A) (h : x = y) : y = x := by rw [h]");
    let source = b"def transport (A B : Type) (h : A = B) (b : B) : A := by rw [h]; exact b";
    engine()
        .admit_source_declaration(source, &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
}
#[test]
fn missing_matches_invalid_rules_and_unproved_transports_do_not_publish() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by rw [h]",
        "theorem bad (n : Nat) : 0 = 0 := by rw [n]",
        "theorem bad (x y : Nat) (h : x = y) : x = 0 := by rw [h]; rfl",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by rw [h] at h",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by rw []",
        "theorem bad (x y : Nat) (h : x = y) : x = y := by rw [,h]",
    ] {
        assert!(
            base.admit_source_declaration(source.as_bytes(), &options, limits())
                .is_err(),
            "{source}"
        );
    }
    assert_eq!(base.logical_root(&options), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}
