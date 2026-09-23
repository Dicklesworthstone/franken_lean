use super::*;
fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn limits(nodes: usize) -> IngressLimits {
    IngressLimits {
        max_nodes: nodes,
        ..IngressLimits::default()
    }
}
#[test]
fn replacement_lifting_is_charged_at_its_actual_binder_depth() {
    let environment = Environment::new();
    let value = Expr::app(b(0), b(1));
    let body = Expr::lam(name("x"), nat(), b(1), BinderInfo::Default);
    // Lam enter/exit + Nat clone + BVar enter/exit + lifted App and two BVars.
    let mut preparation = Preparation::new(&environment, limits(11));
    assert_eq!(
        preparation.substitution(&body, &value).unwrap(),
        Expr::lam(name("x"), nat(), Expr::app(b(1), b(2)), BinderInfo::Default)
    );
    assert_eq!(preparation.visited, 11);
    let mut bounded = Preparation::new(&environment, limits(10));
    assert!(matches!(
        bounded.substitution(&body, &value),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 10,
            observed: 11
        })
    ));
    // The failed attempt cannot mutate the caller's expressions.
    assert_eq!(body, Expr::lam(name("x"), nat(), b(1), BinderInfo::Default));
    assert_eq!(value, Expr::app(b(0), b(1)));
}
#[test]
fn closed_and_unused_replacements_never_expand_a_disconnected_product() {
    let environment = Environment::new();
    let mut huge = b(0);
    for _ in 0..25 {
        huge = Expr::app(huge.clone(), huge);
    }
    let mut preparation = Preparation::new(&environment, limits(6));
    // The replacement is unused. Core subst only decrements the outside index.
    assert_eq!(preparation.substitution(&b(1), &huge).unwrap(), b(0));
    let closed = Expr::lam(name("x"), nat(), b(0), BinderInfo::Default);
    assert_eq!(preparation.substitution(&closed, &huge).unwrap(), closed);
    // At depth zero no traversal of the replacement is needed, even if open.
    assert_eq!(preparation.substitution(&b(0), &huge).unwrap(), huge);
    assert_eq!(preparation.visited, 6);
}
#[test]
fn lets_metadata_and_projections_preserve_capture_avoiding_scopes() {
    let environment = Environment::new();
    let let_body = Expr::let_e(name("x"), b(0), b(0), Expr::app(b(1), b(0)), false);
    let body = Expr::mdata(KVMap::new(), Expr::proj(name("Record"), 0, let_body));
    let expected = Expr::mdata(
        KVMap::new(),
        Expr::proj(
            name("Record"),
            0,
            Expr::let_e(name("x"), b(2), b(2), Expr::app(b(3), b(0)), false),
        ),
    );
    let mut preparation = Preparation::new(&environment, limits(100));
    assert_eq!(preparation.substitution(&body, &b(2)).unwrap(), expected);
    let shifted = Expr::forall_e(name("A"), b(3), Expr::app(b(4), b(0)), BinderInfo::Implicit);
    let original = Expr::forall_e(name("A"), b(0), Expr::app(b(1), b(0)), BinderInfo::Implicit);
    assert_eq!(preparation.lift(&original, 3).unwrap(), shifted);
    let before = preparation.visited;
    assert_eq!(preparation.lift(&original, 0).unwrap(), original);
    assert_eq!(preparation.visited, before + 1);
}
#[test]
fn shared_and_unshared_syntax_have_identical_fuel_and_results() {
    let environment = Environment::new();
    let leaf = Expr::app(b(0), b(1));
    let shared = Expr::app(leaf.clone(), leaf);
    let unshared = Expr::app(Expr::app(b(0), b(1)), Expr::app(b(0), b(1)));
    for budget in 0..=20 {
        let mut left = Preparation::new(&environment, limits(budget));
        let mut right = Preparation::new(&environment, limits(budget));
        assert_eq!(
            left.substitution(&shared, &nat()),
            right.substitution(&unshared, &nat())
        );
        assert_eq!(left.visited, right.visited);
    }
}
#[test]
fn deep_open_syntax_is_bounded_on_a_small_host_stack() {
    let mut body = b(3000);
    for _ in 0..3000 {
        body = Expr::lam(Name::anonymous(), nat(), body, BinderInfo::Default);
    }
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let environment = Environment::new();
            let mut preparation = Preparation::new(&environment, limits(20_000));
            let substituted = preparation.substitution(&body, &b(0)).unwrap();
            // An open replacement lifted through 3000 binders still denotes the
            // same outer variable. Core uses a heap stack for the actual transform.
            assert_eq!(substituted, body);
            let mut bounded = Preparation::new(&environment, limits(50));
            assert!(matches!(
                bounded.substitution(&body, &b(0)),
                Err(IngressError::ResourceLimit { .. })
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}
#[test]
fn variable_overflow_is_still_a_typed_refusal() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, limits(20));
    let greatest = b(fln_core::expr::MAX_LOOSE_BVAR_RANGE - 1);
    assert!(preparation.lift(&greatest, 1).is_err());
    assert!(
        preparation
            .substitution(
                &Expr::lam(name("x"), nat(), b(1), BinderInfo::Default),
                &greatest
            )
            .is_err()
    );
}
