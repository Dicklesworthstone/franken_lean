//! Strict branch-local bindings survive the shared recursor preparation path.
use super::*;

fn b(index: usize) -> Expr {
    variable(index).unwrap()
}
fn nat() -> Expr {
    scalar(ValueType::Nat).unwrap()
}
fn lam(body: Expr) -> Expr {
    Expr::lam(name("argument"), nat(), body, BinderInfo::Default)
}
fn local(label: &str, value: Expr, body: Expr) -> Expr {
    Expr::let_e(name(label), nat(), value, body, false)
}
fn prepare(function: Expr, argument: Expr) -> Expr {
    let environment = Environment::new();
    Preparation::new(&environment, IngressLimits::default())
        .minor_apply(function, argument)
        .unwrap()
}

#[test]
fn an_unused_strict_initializer_is_not_erased_by_branch_application() {
    let action = call("observableInitializer", [literal(9)]);
    let input = local("paid", action.clone(), lam(literal(42)));
    assert_eq!(
        prepare(input, literal(0)),
        local("paid", action, literal(42))
    );
}

#[test]
fn repeated_reads_share_the_initializer_instead_of_copying_it() {
    let action = call("observableInitializer", [literal(9)]);
    let input = local("shared", action.clone(), lam(call("Nat.add", [b(1), b(1)])));
    assert_eq!(
        prepare(input, literal(0)),
        local("shared", action, call("Nat.add", [b(0), b(0)]))
    );
}

#[test]
fn nested_initializers_keep_order_dependencies_and_outer_argument_scope() {
    let first = call("firstInitializer", [b(0)]);
    let second = call("secondInitializer", [b(0)]);
    let input = local(
        "first",
        first.clone(),
        local("second", second.clone(), lam(call("Nat.add", [b(2), b(0)]))),
    );
    assert_eq!(
        prepare(input, b(0)),
        local(
            "first",
            first,
            local("second", second, call("Nat.add", [b(1), b(2)]))
        )
    );
}

#[test]
fn dynamic_branch_callees_stay_inside_their_strict_bindings() {
    let input = local("callee", call("makeCallback", []), b(0));
    assert_eq!(
        prepare(input, b(0)),
        local("callee", call("makeCallback", []), Expr::app(b(0), b(1)))
    );
}

#[test]
fn retaining_an_initializer_does_not_force_an_unused_symbolic_hypothesis() {
    let marker = Expr::fvar(FVarId(name("unusedIH")));
    let result = prepare(local("paid", literal(3), lam(literal(42))), marker);
    assert_eq!(result, local("paid", literal(3), literal(42)));
    assert!(!result.has_fvar());
}

#[test]
fn deep_let_spines_are_heap_backed_and_refuse_exhausted_budgets() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut function = lam(b(0));
            for _ in 0..2000 {
                function = local("retained", literal(0), function);
            }
            let environment = Environment::new();
            let small = IngressLimits {
                max_context_depth: 20,
                ..IngressLimits::default()
            };
            assert!(matches!(
                Preparation::new(&environment, small).minor_apply(function.clone(), literal(42)),
                Err(IngressError::ResourceLimit { .. })
            ));
            let no_work = IngressLimits {
                max_nodes: 0,
                ..IngressLimits::default()
            };
            assert!(matches!(
                Preparation::new(&environment, no_work).minor_apply(function.clone(), literal(42)),
                Err(IngressError::ResourceLimit { .. })
            ));
            let mut result = prepare(function, literal(42));
            let mut count = 0;
            while let ExprNode::LetE { body, .. } = result.node() {
                count += 1;
                result = body.clone();
            }
            assert_eq!(count, 2000);
            assert_eq!(result, literal(42));
        })
        .unwrap()
        .join()
        .unwrap();
}
