//! The pin's term order on small terms, decided by hand from `src/Lean/Meta/ACLt.lean`, and the
//! permutation test on rule sides.
use super::*;

fn context() -> Context {
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    let mut env = Environment::new();
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    for declaration in crate::seed::source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
            panic!("seed nonanswer")
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed rejected")
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
    Context::new(&env, budget)
}

fn local(context: &mut Context, name: &str, type_: Expr) -> Expr {
    let name = Name::from_components([name]);
    let id = FVarId(name.clone());
    context
        .txn
        .lctx
        .add_param(id.clone(), name, type_, BinderInfo::Default);
    Expr::fvar(id)
}

fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn nat_lit(value: u64) -> Expr {
    Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
}

/// `(A, a, b, f)` with `a` declared before `b` and `f : A → A → A`.
fn locals(context: &mut Context) -> (Expr, Expr, Expr, Expr) {
    let type_ = local(context, "A", Expr::sort(Level::one()));
    // Declared in the order `b`'s name sorts before: declaration order decides, not the name.
    let a = local(context, "z", type_.clone());
    let b = local(context, "y", type_.clone());
    let f = local(
        context,
        "f",
        arrow(type_.clone(), arrow(type_.clone(), type_.clone())),
    );
    (type_, a, b, f)
}

#[test]
fn locals_are_ordered_by_declaration_and_terms_by_their_arguments() {
    let mut ctx = context();
    let (_, a, b, f) = locals(&mut ctx);
    let fab = app(f.clone(), [a.clone(), b.clone()]);
    let fba = app(f.clone(), [b.clone(), a.clone()]);
    for (left, right, expected) in [
        (&a, &b, true),
        (&b, &a, false),
        (&a, &a, false),
        (&fab, &fba, true),
        (&fba, &fab, false),
        (&fab, &fab, false),
        // A subterm precedes the term (`someChildGe`).
        (&a, &fab, true),
        (&fab, &a, false),
    ] {
        assert_eq!(
            ctx.simp_ac_lt(left, right).unwrap(),
            expected,
            "{left:?} < {right:?}"
        );
    }
    // `f a (f a b)` against `f (f a b) a`: the first arguments decide.
    let nested_left = app(f.clone(), [a.clone(), fab.clone()]);
    let nested_right = app(f, [fab, a]);
    assert!(ctx.simp_ac_lt(&nested_left, &nested_right).unwrap());
    assert!(!ctx.simp_ac_lt(&nested_right, &nested_left).unwrap());
}

#[test]
fn leaves_compare_as_the_pin_compares_them() {
    let mut ctx = context();
    let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
    let succ = Expr::const_(Name::from_components(["Nat", "succ"]), vec![]);
    let two = nat_lit(2);
    let ten = nat_lit(10);
    let text = Expr::lit(Literal::Str("a".to_string()));
    for (left, right, expected) in [
        // `Name.lt`, component by component: `succ` before `zero`.
        (&succ, &zero, true),
        (&zero, &succ, false),
        // Literal values, not their spelling; a number before a string.
        (&two, &ten, true),
        (&ten, &two, false),
        (&ten, &text, true),
        (&text, &ten, false),
        // A constant (weight 4) before a literal (weight 5).
        (&zero, &two, true),
        (&two, &zero, false),
    ] {
        assert_eq!(
            ctx.simp_ac_lt(left, right).unwrap(),
            expected,
            "{left:?} < {right:?}"
        );
    }
}

#[test]
fn the_order_is_strict_and_total_on_ground_terms() {
    let mut ctx = context();
    let (_, a, b, f) = locals(&mut ctx);
    let terms = [
        a.clone(),
        b.clone(),
        app(f.clone(), [a.clone(), b.clone()]),
        app(f.clone(), [b.clone(), a.clone()]),
        app(f.clone(), [a.clone(), a.clone()]),
        app(
            f.clone(),
            [app(f.clone(), [a.clone(), b.clone()]), b.clone()],
        ),
        app(f.clone(), [b.clone(), app(f, [a.clone(), b.clone()])]),
        nat_lit(3),
    ];
    for x in &terms {
        assert!(!ctx.simp_ac_lt(x, x).unwrap(), "{x:?} < itself");
        for y in &terms {
            if x == y {
                continue;
            }
            let (forward, backward) =
                (ctx.simp_ac_lt(x, y).unwrap(), ctx.simp_ac_lt(y, x).unwrap());
            assert!(forward != backward, "{x:?} and {y:?}: {forward} {backward}");
        }
    }
}

#[test]
fn a_permutation_is_equality_up_to_pattern_variables() {
    let mut ctx = context();
    let (type_, a, b, f) = locals(&mut ctx);
    let x = ctx.hole(type_.clone()).unwrap();
    let y = ctx.hole(type_.clone()).unwrap();
    let fxy = app(f.clone(), [x.clone(), y.clone()]);
    let fyx = app(f.clone(), [y.clone(), x.clone()]);
    assert!(ctx.simp_is_perm(&fxy, &fyx));
    // `isDefEq` unifies two variables: `f ?x ?y` and `f ?x ?x` are a permutation too.
    assert!(ctx.simp_is_perm(&fxy, &app(f.clone(), [x.clone(), x.clone()])));
    // A variable is not a term, and locals are not variables.
    assert!(!ctx.simp_is_perm(&fxy, &app(f.clone(), [y.clone(), a.clone()])));
    assert!(!ctx.simp_is_perm(
        &app(f.clone(), [a.clone(), b.clone()]),
        &app(f.clone(), [b, a])
    ));
    assert!(!ctx.simp_is_perm(&fxy, &x));
    // Two variables of different types do not unify.
    let other = ctx.hole(Expr::sort(Level::zero())).unwrap();
    assert!(!ctx.simp_is_perm(&app(f.clone(), [x, y]), &app(f, [other, type_])));
}

#[test]
fn a_statement_is_read_under_its_binders() {
    let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
    let f = Expr::const_(Name::from_components(["f"]), vec![]);
    let equation = |left: Expr, right: Expr| {
        app(
            Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
            [nat.clone(), left, right],
        )
    };
    let bound = |index: u32| Expr::bvar(index).unwrap();
    let binders = |body: Expr| arrow(nat.clone(), arrow(nat.clone(), body));
    let comm = binders(equation(
        app(f.clone(), [bound(1), bound(0)]),
        app(f.clone(), [bound(0), bound(1)]),
    ));
    assert!(statement_is_perm(&comm));
    let three = |body: Expr| arrow(nat.clone(), binders(body));
    // `f x (f y z) = f y (f x z)`.
    let left_comm = three(equation(
        app(f.clone(), [bound(2), app(f.clone(), [bound(1), bound(0)])]),
        app(f.clone(), [bound(1), app(f.clone(), [bound(2), bound(0)])]),
    ));
    assert!(statement_is_perm(&left_comm));
    // `f (f x y) z = f x (f y z)`: not one shape.
    let assoc = three(equation(
        app(f.clone(), [app(f.clone(), [bound(2), bound(1)]), bound(0)]),
        app(f.clone(), [bound(2), app(f, [bound(1), bound(0)])]),
    ));
    assert!(!statement_is_perm(&assoc));
    assert!(!statement_is_perm(&nat));
}

#[test]
fn eta_and_beta_follow_the_pin() {
    let f = Expr::const_(Name::from_components(["f"]), vec![]);
    let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
    let lam = |body: Expr| Expr::lam(Name::anonymous(), nat.clone(), body, BinderInfo::Default);
    let bound = |index: u32| Expr::bvar(index).unwrap();
    // `fun x y => f x y` is `f`; `fun x y => f y x` and `fun x => x` are not eta-expansions.
    assert_eq!(
        eta_expanded_strict(&lam(lam(app(f.clone(), [bound(1), bound(0)])))),
        Some(f.clone())
    );
    assert_eq!(
        eta_expanded_strict(&lam(lam(app(f.clone(), [bound(0), bound(1)])))),
        None
    );
    assert_eq!(eta_expanded_strict(&lam(bound(0))), None);
    // `(fun x y => f y x) a` is `fun y => f y a`: one argument for two binders.
    let a = Expr::const_(Name::from_components(["a"]), vec![]);
    let reduced = beta(
        &lam(lam(app(f.clone(), [bound(0), bound(1)]))),
        std::slice::from_ref(&a),
    )
    .unwrap();
    assert_eq!(reduced, lam(app(f, [bound(0), a])));
}
