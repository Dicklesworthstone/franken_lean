//! Real source equality proofs, never a mock checker.
#![forbid(unsafe_code)]
use fln_core::{name::Name, outcome::Outcome};
use fln_elab::{check_definition_source, seed::source_seed_declarations};
use fln_env::{
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    Declaration,
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
    verdict::{Budget, Verdict},
};
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn env() -> Environment {
    let mut env = Environment::new();
    for declaration in source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget()) else {
            panic!("seed nonanswer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed rejected");
        };
        env = match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("seed publication {other:?}"),
        };
    }
    env
}
fn accepted(source: &str) -> Declaration {
    let result = check_definition_source(source.as_bytes(), &env(), budget())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        result.outcome
    );
    let Declaration::Thm(proof) = &result.declaration else {
        panic!("actual theorem");
    };
    assert!(
        !proof.value.has_expr_mvar() && !proof.value.has_level_mvar() && !proof.value.has_fvar()
    );
    result.declaration
}
#[test]
fn reflexivity_works_as_a_tactic_and_an_inferred_proof_term() {
    for source in [
        "theorem same (x : Nat) : x = x := by rfl",
        "theorem same (x : Nat) : x = x := rfl",
        "theorem same (x : Nat) : x = x := by exact Eq.refl x",
        "theorem same {A : Type} (x : A) : x = x := by rfl",
        "theorem same (P : Prop) (h : P) : h = h := by rfl",
        "theorem same : 7 = 7 := by rfl",
        "theorem same : \"hello\" = \"hello\" := by rfl",
    ] {
        accepted(source);
    }
}
#[test]
fn rfl_uses_kernel_conversion_not_only_syntax_equality() {
    accepted("theorem reduce (x : Nat) : x = x := let y := x; by exact Eq.refl y");
    accepted("theorem arithmetic : 2 + 3 = 5 := by rfl");
}
#[test]
fn equality_premises_and_intro_are_real_proof_terms() {
    accepted("theorem retain (x y : Nat) : x = y -> x = y := by intro h; assumption");
    accepted("theorem retain (x y : Nat) (h : x = y) : x = y := by exact h");
}
#[test]
fn false_and_wrong_typed_reflexivity_never_publish_a_proof() {
    for source in [
        "theorem false : 1 = 2 := by rfl",
        "theorem bad : 1 = \"x\" := by rfl",
        "theorem bad : Nat := by rfl",
        "theorem bad : 1 == 1 := by rfl",
    ] {
        match check_definition_source(source.as_bytes(), &env(), budget()) {
            Err(_) => {}
            Ok(result) => assert!(
                !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            ),
        }
    }
}
#[test]
fn equality_has_its_own_precedence_and_does_not_widen_nat_only() {
    let source = b"theorem sum (x : Nat) : x + 0 = x := by rfl\r\n";
    let parsed = fln_parse::parse_definition(source).unwrap();
    assert_eq!(parsed.reconstruct_original(), source);
    assert!(fln_parse::parse_definition(b"theorem bad : 1 = 2 = 3 := by rfl").is_err());
    assert!(fln_parse::parse_nat_definition(b"def bad : Nat := 1 = 1").is_err());
    assert!(env().contains(&Name::from_components(["Eq", "rec"])));
}
