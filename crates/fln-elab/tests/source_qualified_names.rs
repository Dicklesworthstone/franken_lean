//! Baseline contracts for adding command scopes without changing name identity.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::check_definition_source;
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, Verdict};

#[test]
fn qualified_declaration_names_keep_structural_identity() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    for (source, expected) in [
        (
            "def Alpha.value : Nat := 7",
            Name::from_components(["Alpha", "value"]),
        ),
        (
            "def «Alpha.value» : Nat := 9",
            Name::from_components(["Alpha.value"]),
        ),
    ] {
        let checked = check_definition_source(source.as_bytes(), &env, budget).unwrap();
        assert!(matches!(
            checked.outcome,
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        let Declaration::Defn(value) = checked.declaration else {
            panic!("definition")
        };
        assert_eq!(value.base.name, expected);
        assert_eq!(value.all, vec![expected]);
        assert!(!value.value.has_fvar());
        assert!(!value.value.has_expr_mvar());
    }
}

#[test]
fn declaration_parameters_shadow_root_constants_without_rebinding_the_environment() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    let checked = check_definition_source(
        b"def Alpha.local (Nat : Type) (x : Nat) : Nat := x",
        &env,
        budget,
    )
    .unwrap();
    assert!(matches!(
        checked.outcome,
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    assert_eq!(env.len(), 1);
    assert!(env.contains(&Name::from_components(["Nat"])));
}
