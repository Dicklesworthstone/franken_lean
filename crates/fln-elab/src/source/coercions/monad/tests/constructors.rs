//! Regression for function-backed monads disappearing during full WHNF.
use super::*;

fn reader_environment() -> Environment {
    let mut env = environment();
    // An ordinary (semireducible) type constructor, just like a function-backed
    // reader/state transformer. Its admitted value really is a function type.
    let a = Expr::bvar(0).unwrap();
    let reader = Expr::forall_e(
        n("state"),
        c("Nat"),
        Expr::bvar(1).unwrap(),
        BinderInfo::Default,
    );
    env = publish(
        &env,
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("ReaderLike"),
                level_params: vec![],
                type_: constructor_type(),
            },
            value: Expr::lam(n("A"), universe(), reader, BinderInfo::Default),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n("ReaderLike")],
        }),
    );
    publish(
        &env,
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("ReaderAlias"),
                level_params: vec![],
                type_: constructor_type(),
            },
            value: Expr::lam(
                n("A"),
                universe(),
                Expr::app(c("ReaderLike"), a),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![n("ReaderAlias")],
        }),
    )
}

#[test]
fn source_lifts_function_backed_monads_and_their_abbreviations() {
    let env = reader_environment();
    for monad in ["ReaderLike", "ReaderAlias"] {
        let source = format!(
            "def lifted (n : Type -> Type) [lift : MonadLiftT {monad} n] (x : {monad} Nat) : n Nat := x"
        );
        let checked = crate::check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}: {:?}",
            checked.outcome
        );
        let Declaration::Defn(declaration) = checked.declaration else {
            panic!("expected definition");
        };
        assert!(has_lift(&declaration.value));
        assert!(!declaration.value.has_expr_mvar());
        assert!(!declaration.value.has_level_mvar());
        assert!(!declaration.value.has_fvar());
        assert!(!declaration.value.has_loose_bvars());
    }
}

#[test]
fn lifting_recovers_the_monad_after_the_type_hint_has_been_normalized() {
    let mut context = Context::new(&reader_environment(), budget());
    let target = parameter(
        &mut context.txn.lctx,
        "n",
        constructor_type(),
        BinderInfo::Default,
    );
    parameter(
        &mut context.txn.lctx,
        "lift",
        app(c("MonadLiftT"), [c("ReaderLike"), fv(&target)]),
        BinderInfo::InstImplicit,
    );
    let original = Expr::app(c("ReaderLike"), c("Nat"));
    let x = parameter(
        &mut context.txn.lctx,
        "x",
        original.clone(),
        BinderInfo::Default,
    );
    let normalized = context.whnf(&original).unwrap();
    assert!(matches!(normalized.node(), ExprNode::ForallE { .. }));
    let action = Typed {
        value: fv(&x),
        type_: normalized,
    };
    let expected = Expr::app(fv(&target), c("Nat"));
    let result = context.try_monad_lift(&action, &expected).unwrap().unwrap();
    assert!(has_lift(&result.value));
    assert!(context.coercion_eq(&result.type_, &expected).unwrap());
}

#[test]
fn a_function_backed_monad_does_not_create_an_unregistered_lift() {
    let env = reader_environment();
    let source = "def bad (n : Type -> Type) (x : ReaderLike Nat) : n Nat := x";
    if let Ok(checked) = crate::check_definition_source(source.as_bytes(), &env, budget()) {
        assert!(!matches!(
            checked.outcome,
            Outcome::Complete(Verdict::Accepted { .. })
        ));
    }
}
