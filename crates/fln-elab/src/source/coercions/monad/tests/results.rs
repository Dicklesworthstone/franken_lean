//! Real source candidates and admitted library bodies exercise result coercion.
//! The small Monad fixture has actual polymorphic pure/bind fields; no class
//! lookup, synthesis, conversion, declaration admission or output is mocked.
use super::*;

fn declaration(name: &str, parameters: &[LocalDecl], type_: Expr, body: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: close(parameters, type_, false),
        },
        value: close(parameters, body, true),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn add_class(
    mut env: Environment,
    name: &str,
    levels: Vec<Name>,
    parameters: Vec<LocalDecl>,
    fields: Vec<LocalDecl>,
    result_level: Level,
) -> Environment {
    for declaration in record_declarations(
        &RecordSpec {
            name: n(name),
            level_params: levels,
            parameters,
            fields,
            result_level,
            is_class: true,
        },
        RecordBudget::default(),
    )
    .unwrap()
    {
        env = publish(&env, declaration);
    }
    register_class(&env, &n(name)).unwrap()
}

fn coe(name: &str) -> Expr {
    Expr::const_(n(name), vec![Level::one(), Level::one()])
}

fn result_environment(lifts: bool) -> Environment {
    let mut env = if lifts {
        environment()
    } else {
        crate::seed::bootstrap_nat_environment(budget()).unwrap()
    };
    // CoeT keeps the actual two-universe signature, including the value index.
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let mut locals = LocalContext::new();
    let a = parameter(&mut locals, "A", Expr::sort(u.clone()), BinderInfo::Default);
    let x = parameter(&mut locals, "x", fv(&a), BinderInfo::Default);
    let b = parameter(&mut locals, "B", Expr::sort(v.clone()), BinderInfo::Default);
    let field = parameter(&mut locals, "coe", fv(&b), BinderInfo::Default);
    env = add_class(
        env,
        "CoeT",
        vec![n("u"), n("v")],
        vec![a, x, b],
        vec![field],
        Level::max(Level::one(), Level::max(u, v).unwrap()).unwrap(),
    );

    let mut locals = LocalContext::new();
    let mut m = parameter(&mut locals, "m", constructor_type(), BinderInfo::Default);
    let a = parameter(&mut locals, "A", universe(), BinderInfo::Implicit);
    let b = parameter(&mut locals, "B", universe(), BinderInfo::Implicit);
    let x = parameter(&mut locals, "a", fv(&a), BinderInfo::Default);
    let ma = Expr::app(fv(&m), fv(&a));
    let mb = Expr::app(fv(&m), fv(&b));
    let pure = parameter(
        &mut locals,
        "pure",
        close(&[a.clone(), x.clone()], ma.clone(), false),
        BinderInfo::Default,
    );
    let action = parameter(&mut locals, "x", ma, BinderInfo::Default);
    let continuation = parameter(
        &mut locals,
        "k",
        close(std::slice::from_ref(&x), mb.clone(), false),
        BinderInfo::Default,
    );
    let bind = parameter(
        &mut locals,
        "bind",
        close(
            &[a.clone(), b.clone(), action.clone(), continuation],
            mb.clone(),
            false,
        ),
        BinderInfo::Default,
    );
    env = add_class(
        env,
        "Monad",
        vec![],
        vec![m.clone()],
        vec![pure, bind],
        Level::one().succ().unwrap(),
    );
    m.binder_info = BinderInfo::Implicit;
    let family = parameter(
        &mut locals,
        "convert",
        close(
            std::slice::from_ref(&x),
            app(coe("CoeT"), [fv(&a), fv(&x), fv(&b)]),
            false,
        ),
        BinderInfo::InstImplicit,
    );
    let monad = parameter(
        &mut locals,
        "monad",
        Expr::app(c("Monad"), fv(&m)),
        BinderInfo::InstImplicit,
    );
    let converted = app(
        coe("CoeT.coe"),
        [fv(&a), fv(&x), fv(&b), Expr::app(fv(&family), fv(&x))],
    );
    let pure_result = app(c("Monad.pure"), [fv(&m), fv(&monad), fv(&b), converted]);
    let continuation = close(std::slice::from_ref(&x), pure_result, true);
    let body = app(
        c("Monad.bind"),
        [fv(&m), fv(&monad), fv(&a), fv(&b), fv(&action), continuation],
    );
    env = publish(
        &env,
        declaration(
            "Lean.Internal.coeM",
            &[m.clone(), a.clone(), b.clone(), family.clone(), monad.clone(), action.clone()],
            mb,
            body,
        ),
    );
    if !lifts {
        return env;
    }
    let target = parameter(&mut locals, "n", constructor_type(), BinderInfo::Implicit);
    let lift = parameter(
        &mut locals,
        "lift",
        app(c("MonadLiftT"), [fv(&m), fv(&target)]),
        BinderInfo::InstImplicit,
    );
    let mut target_monad = monad;
    target_monad.type_ = Expr::app(c("Monad"), fv(&target));
    let lifted = app(
        c("liftM"),
        [fv(&m), fv(&target), fv(&lift), fv(&a), fv(&action)],
    );
    let body = app(
        c("Lean.Internal.coeM"),
        [fv(&target), fv(&a), fv(&b), fv(&family), fv(&target_monad), lifted],
    );
    publish(
        &env,
        declaration(
            "Lean.Internal.liftCoeM",
            &[m, target.clone(), a, b.clone(), lift, family, target_monad, action],
            Expr::app(fv(&target), fv(&b)),
            body,
        ),
    )
}

fn checked_value(env: &Environment, source: &str) -> Expr {
    let checked = crate::check_definition_source(source.as_bytes(), env, budget())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert!(
        matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}: {:?}",
        checked.outcome
    );
    let Declaration::Defn(declaration) = checked.declaration else {
        panic!("expected definition");
    };
    for expression in [&declaration.base.type_, &declaration.value] {
        assert!(!expression.has_expr_mvar());
        assert!(!expression.has_level_mvar());
        assert!(!expression.has_fvar());
        assert!(!expression.has_loose_bvars());
    }
    declaration.value
}

fn contains_constant(value: &Expr, constant: &str) -> bool {
    let mut work = vec![value];
    while let Some(expr) = work.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } if name == &n(constant) => return true,
            ExprNode::App { f, a } => work.extend([f, a]),
            ExprNode::Lam { binder_type, body, .. }
            | ExprNode::ForallE { binder_type, body, .. } => work.extend([binder_type, body]),
            ExprNode::LetE { type_, value, body, .. } => work.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    false
}

fn final_action_occurrences(value: &Expr) -> usize {
    let mut body = value;
    while let ExprNode::Lam { body: next, .. } = body.node() {
        body = next;
    }
    let mut count = 0;
    let mut work = vec![(body, 0)];
    while let Some((expr, depth)) = work.pop() {
        match expr.node() {
            ExprNode::BVar { idx } if *idx == depth => count += 1,
            ExprNode::App { f, a } => work.extend([(f, depth), (a, depth)]),
            ExprNode::Lam { body, .. } | ExprNode::ForallE { body, .. } => {
                work.push((body, depth + 1));
            }
            ExprNode::LetE { value, body, .. } => {
                work.extend([(value, depth), (body, depth + 1)]);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push((expr, depth)),
            _ => {}
        }
    }
    count
}

const SAME: &str = "def mapped (m : Type -> Type) (A B : Type) [monad : Monad m] [convert : (a : A) -> CoeT A a B] (x : m A) : m B := x";
const LIFTED: &str = "def mapped (m n : Type -> Type) (A B : Type) [lift : MonadLiftT m n] [monad : Monad n] [convert : (a : A) -> CoeT A a B] (x : m A) : n B := x";

#[test]
fn source_maps_results_without_a_monad_lift_class() {
    let env = result_environment(false);
    assert!(!env.contains(&n("MonadLiftT")));
    let value = checked_value(&env, SAME);
    assert!(contains_constant(&value, "Monad.bind"));
    assert!(contains_constant(&value, "Monad.pure"));
    assert!(!contains_constant(&value, "Lean.Internal.coeM"));
    assert!(!has_lift(&value));
    assert_eq!(final_action_occurrences(&value), 1);
}

#[test]
fn source_composes_a_lift_with_result_coercion() {
    let value = checked_value(&result_environment(true), LIFTED);
    assert!(has_lift(&value));
    assert!(contains_constant(&value, "Monad.bind"));
    assert!(!contains_constant(&value, "Lean.Internal.coeM"));
    assert!(!contains_constant(&value, "Lean.Internal.liftCoeM"));
    assert_eq!(final_action_occurrences(&value), 1);
}

#[test]
fn result_coercions_work_in_higher_order_arguments() {
    let env = result_environment(true);
    for source in [
        "def mapped (m : Type -> Type) (A B : Type) [monad : Monad m] [convert : (a : A) -> CoeT A a B] (use : m B -> Nat) (x : m A) : Nat := use x",
        "def mapped (m n : Type -> Type) (A B : Type) [lift : MonadLiftT m n] [monad : Monad n] [convert : (a : A) -> CoeT A a B] (use : n B -> Nat) (x : m A) : Nat := use x",
    ] {
        let value = checked_value(&env, source);
        assert!(contains_constant(&value, "Monad.bind"));
        assert_eq!(final_action_occurrences(&value), 1);
    }
}

fn mapping_context(lifts: bool, dictionary: bool) -> (Context, Typed, Expr) {
    let mut context = Context::new(&result_environment(lifts), budget());
    let m = parameter(&mut context.txn.lctx, "m", constructor_type(), BinderInfo::Default);
    let target = if lifts {
        parameter(&mut context.txn.lctx, "n", constructor_type(), BinderInfo::Default)
    } else {
        m.clone()
    };
    let a = parameter(&mut context.txn.lctx, "A", universe(), BinderInfo::Default);
    let b = parameter(&mut context.txn.lctx, "B", universe(), BinderInfo::Default);
    parameter(
        &mut context.txn.lctx,
        "monad",
        Expr::app(c("Monad"), fv(&target)),
        BinderInfo::InstImplicit,
    );
    if lifts {
        parameter(
            &mut context.txn.lctx,
            "lift",
            app(c("MonadLiftT"), [fv(&m), fv(&target)]),
            BinderInfo::InstImplicit,
        );
    }
    if dictionary {
        let mut locals = LocalContext::new();
        let x = parameter(&mut locals, "a", fv(&a), BinderInfo::Default);
        parameter(
            &mut context.txn.lctx,
            "convert",
            close(std::slice::from_ref(&x), app(coe("CoeT"), [fv(&a), fv(&x), fv(&b)]), false),
            BinderInfo::InstImplicit,
        );
    }
    let type_ = Expr::app(fv(&m), fv(&a));
    let x = parameter(&mut context.txn.lctx, "x", type_.clone(), BinderInfo::Default);
    (context, Typed { value: fv(&x), type_ }, Expr::app(fv(&target), fv(&b)))
}

#[test]
fn disabling_auto_lift_does_not_disable_same_monad_result_coercions() {
    let (mut context, action, expected) = mapping_context(false, true);
    context.txn.options.insert(n("autoLift"), DataValue::OfBool(false));
    let result = context.try_monad_lift(&action, &expected).unwrap().unwrap();
    assert!(contains_constant(&result.value, "Monad.bind"));
    assert!(!has_lift(&result.value));
}

#[test]
fn disabling_auto_lift_also_disables_combined_lift_and_map() {
    let (mut context, action, expected) = mapping_context(true, true);
    context.txn.options.insert(n("autoLift"), DataValue::OfBool(false));
    assert!(context.try_monad_lift(&action, &expected).unwrap().is_none());
}

fn unchanged_except_work(context: &Context, before: &Context) {
    assert!(context.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
    let mut actual = context.txn.clone();
    actual.budget = before.txn.budget.clone();
    assert_eq!(actual, before.txn);
    assert_eq!(context.next, before.next);
    assert_eq!(context.instance_goals, before.instance_goals);
    assert_eq!(context.equations.len(), before.equations.len());
    for (actual, expected) in context.equations.iter().zip(&before.equations) {
        assert_eq!(actual.sides, expected.sides);
        assert!(actual.policy == expected.policy);
    }
}

#[test]
fn a_failed_result_dictionary_rolls_back_the_entire_attempt() {
    for lifts in [false, true] {
        let (mut context, action, expected) = mapping_context(lifts, false);
        let before = context.clone();
        assert!(context.try_monad_lift(&action, &expected).unwrap().is_none());
        unchanged_except_work(&context, &before);
    }
}

#[test]
fn a_value_specific_dictionary_is_not_a_universal_result_conversion() {
    let env = result_environment(true);
    for source in [
        "def bad (m : Type -> Type) (A B : Type) [monad : Monad m] (a : A) [one : CoeT A a B] (x : m A) : m B := x",
        "def bad (m n : Type -> Type) (A B : Type) [lift : MonadLiftT m n] [monad : Monad n] (a : A) [one : CoeT A a B] (x : m A) : n B := x",
        "def bad (m : Type -> Type) (A B : Type) [convert : (a : A) -> CoeT A a B] (x : m A) : m B := x",
        "def bad (m n : Type -> Type) (A B : Type) [lift : MonadLiftT m n] [monad : Monad m] [convert : (a : A) -> CoeT A a B] (x : m A) : n B := x",
    ] {
        if let Ok(checked) = crate::check_definition_source(source.as_bytes(), &env, budget()) {
            assert!(!matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })), "{source}");
        }
    }
}

#[test]
fn result_mapping_exhaustion_retains_work_and_rolls_back_state() {
    let (mut context, action, expected) = mapping_context(false, true);
    context.txn.budget.max_heartbeats = 1;
    let before = context.clone();
    assert!(matches!(
        context.try_monad_lift(&action, &expected),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))
    ));
    unchanged_except_work(&context, &before);
}

#[test]
fn failed_mapping_can_be_followed_by_a_successful_mapping() {
    let (mut context, action, expected) = mapping_context(false, false);
    assert!(context.try_monad_lift(&action, &expected).unwrap().is_none());
    let ExprNode::App { a: source, .. } = action.type_.node() else { panic!("action type") };
    let ExprNode::App { a: target, .. } = expected.node() else { panic!("target type") };
    let mut locals = LocalContext::new();
    let value = parameter(&mut locals, "a", source.clone(), BinderInfo::Default);
    parameter(
        &mut context.txn.lctx,
        "later",
        close(std::slice::from_ref(&value), app(coe("CoeT"), [source.clone(), fv(&value), target.clone()]), false),
        BinderInfo::InstImplicit,
    );
    assert!(context.try_monad_lift(&action, &expected).unwrap().is_some());
}

#[test]
fn expansion_respects_an_explicitly_irreducible_helper() {
    let env = crate::reducibility::register(
        &result_environment(false),
        &n("Lean.Internal.coeM"),
        crate::reducibility::Reducibility::Irreducible,
    )
    .unwrap();
    let value = checked_value(&env, SAME);
    assert!(contains_constant(&value, "Lean.Internal.coeM"));
    assert!(!contains_constant(&value, "Monad.bind"));
}

#[test]
fn a_missing_noninstance_argument_is_never_synthesized() {
    let mut context = Context::new(&result_environment(false), budget());
    let before = context.clone();
    assert!(context.monadic_application("Monad", [None]).unwrap().is_none());
    unchanged_except_work(&context, &before);
}

#[test]
fn an_unknown_destination_constructor_is_not_selected_by_search() {
    let (mut context, action, expected) = mapping_context(true, true);
    let ExprNode::App { a: element, .. } = expected.node() else {
        panic!("expected monadic type");
    };
    let unknown = context.hole(constructor_type()).unwrap();
    let expected = Expr::app(unknown, element.clone());
    let before = context.clone();
    assert!(context.try_monad_lift(&action, &expected).unwrap().is_none());
    unchanged_except_work(&context, &before);
}

#[test]
fn exhaustion_after_synthesis_has_started_is_not_a_failed_coercion() {
    for lifts in [false, true] {
        let (baseline, action, expected) = mapping_context(lifts, true);
        let mut complete = baseline.clone();
        assert!(complete.try_monad_lift(&action, &expected).unwrap().is_some());
        let spent = complete.txn.budget.heartbeats_consumed;
        assert!(spent > 4);
        for allowance in [spent / 4, spent / 2, spent - 1] {
            let mut limited = baseline.clone();
            limited.txn.budget.max_heartbeats = allowance;
            let before = limited.clone();
            assert!(limited.try_monad_lift(&action, &expected).is_err());
            unchanged_except_work(&limited, &before);
        }
    }
}
