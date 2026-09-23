use super::*;
fn b(n: usize) -> Expr {
    variable(n).unwrap()
}
fn ty(s: &str) -> Expr {
    Expr::const_(super::super::name(s), vec![])
}
#[test]
fn indexed_callback_arguments_are_lifted_only_past_the_new_accumulators() {
    let env = Environment::new();
    let mut preparation = Preparation::new(&env, IngressLimits::default());
    let recursive = RecursiveField {
        target: 0,
        binders: vec![
            (
                super::super::name("childIndex"),
                ty("Nat"),
                BinderInfo::Default,
            ),
            (super::super::name("flag"), ty("Bool"), BinderInfo::Default),
        ],
    };
    let result = Expr::forall_e(
        super::super::name("acc"),
        ty("Nat"),
        Expr::forall_e(
            super::super::name("text"),
            ty("String"),
            ty("Nat"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // Relative to two child binders: prior constructor field + child index,
    // then the flag. Both must cross two *additional* accumulator binders.
    let indices = [Expr::app(Expr::app(ty("Nat.add"), b(2)), b(1)), b(0)];
    let (lambda, interface) = preparation
        .recursive_hypothesis(&recursive, b(0), b(1), &result, &indices)
        .unwrap();
    let expected_indices = [Expr::app(Expr::app(ty("Nat.add"), b(4)), b(3)), b(2)];
    let child = Expr::app(Expr::app(b(5), b(3)), b(2));
    let mut expected = b(4);
    for index in expected_indices {
        expected = Expr::app(expected, index);
    }
    expected = Expr::app(Expr::app(Expr::app(expected, child), b(1)), b(0));
    let mut expected_type = ty("Nat");
    for (name, domain) in [
        ("text", "String"),
        ("acc", "Nat"),
        ("flag", "Bool"),
        ("childIndex", "Nat"),
    ] {
        expected = Expr::lam(
            super::super::name(name),
            ty(domain),
            expected,
            BinderInfo::Default,
        );
        expected_type = Expr::forall_e(
            super::super::name(name),
            ty(domain),
            expected_type,
            BinderInfo::Default,
        );
    }
    assert_eq!(lambda, expected);
    assert_eq!(interface, expected_type);
}
