//! Sort formation and impredicativity must survive source universe support.
#![forbid(unsafe_code)]
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::outcome::Outcome;
use fln_elab::check_definition_source;
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, Verdict};

fn checked(source: &str) -> Declaration {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    let result = check_definition_source(source.as_bytes(), &env, budget).unwrap();
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}: {:?}",
        result.outcome
    );
    result.declaration
}

#[test]
fn the_sort_of_type_is_not_type_itself() {
    let Declaration::Defn(value) = checked("def higher := Type") else {
        panic!("definition")
    };
    assert_eq!(value.value, Expr::sort(Level::one()));
    assert_eq!(
        value.base.type_,
        Expr::sort(Level::one().succ().unwrap())
    );
}

#[test]
fn quantification_over_data_into_prop_is_impredicative() {
    checked("def logical (A : Type) (P : Prop) : Prop := A -> P");
    checked("def predicate (A : Type) (P : A -> Prop) : Prop := forall x : A, P x");
}

#[test]
fn source_sort_checking_never_uses_cumulativity() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    for source in ["def wrong : Type := Type", "def wrong : Prop := Nat"] {
        if let Ok(result) = check_definition_source(source.as_bytes(), &env, budget) {
            assert!(
                !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            );
        }
    }
    checked("def valid : Type := Nat");
}
