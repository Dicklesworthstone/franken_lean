use super::*;

fn interface(prep: &mut Preparation<'_>, parameters: Vec<ValueType>, result: ValueType) -> ValueType {
    prep.stage_interface(ClosureSignature {
        parameter_ownership: borrowed_runtime_parameters(parameters.len()).unwrap(),
        parameters,
        result,
        result_ownership: result_ownership(result),
    })
    .unwrap()
}

fn stages(prep: &mut Preparation<'_>) -> (ValueType, ValueType) {
    let tail = interface(prep, vec![ValueType::Nat], ValueType::Nat);
    let staged = interface(prep, vec![ValueType::Nat], tail);
    let flat = interface(prep, vec![ValueType::Nat, ValueType::Nat], ValueType::Nat);
    (staged, flat)
}

fn local(prep: &mut Preparation<'_>, body: Expr, result: ValueType) -> Expr {
    let lambda = Expr::lam(
        Name::num(name("_fln_runtime_local"), prep.lambdas.len() as u64),
        Expr::const_(name("Nat"), vec![]),
        body,
        BinderInfo::Default,
    );
    prep.lambdas.push(LambdaBinding {
        lambda: lambda.clone(),
        parameters: vec![ValueType::Nat],
        parameter_ownership: borrowed_runtime_parameters(1).unwrap(),
        result,
        result_ownership: result_ownership(result),
        recursion: LambdaRecursion::NonRecursive,
    });
    lambda
}

fn arrow() -> Expr {
    let nat = Expr::const_(name("Nat"), vec![]);
    Expr::forall_e(
        Name::anonymous(),
        nat.clone(),
        Expr::forall_e(Name::anonymous(), nat.clone(), nat, BinderInfo::Default),
        BinderInfo::Default,
    )
}

#[test]
fn a_returned_capture_keeps_its_real_stages_without_changing_the_lambda() {
    let environment = Environment::new();
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    let (staged, flat) = stages(&mut prep);
    let lambda = local(&mut prep, Expr::bvar(1).unwrap(), flat);
    let original = lambda.clone();
    let actual = prep.captured_result(&lambda, &[staged]).unwrap().unwrap();
    assert_eq!(prep.lambdas[0].result, staged);
    assert_eq!(prep.stage_apply(actual, 1).unwrap(), Some(staged));
    assert_eq!(prep.stage_apply(actual, 3).unwrap(), Some(ValueType::Nat));
    assert_eq!(prep.lambdas[0].lambda, original);
    assert_eq!(lambda, original);
}

#[test]
fn aliases_in_argument_initializers_are_lexical_not_global_expression_keys() {
    let environment = Environment::new();
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    let (staged, flat) = stages(&mut prep);
    // Equal relative bodies see distinct aliases. Finishing the first argument
    // must restore the original context before visiting the second argument.
    let first = local(&mut prep, Expr::bvar(1).unwrap(), flat);
    let second = local(&mut prep, Expr::bvar(1).unwrap(), flat);
    let argument = |index, lambda| {
        Expr::let_e(
            name("alias"),
            arrow(),
            Expr::bvar(index).unwrap(),
            lambda,
            false,
        )
    };
    let source = Expr::app(
        Expr::app(
            Expr::const_(name("unknownConsumer"), vec![]),
            argument(1, first),
        ),
        argument(0, second),
    );
    let original = source.clone();
    assert_eq!(prep.captured_result(&source, &[staged, flat]).unwrap(), None);
    assert_eq!(prep.lambdas[0].result, staged);
    assert_eq!(prep.lambdas[1].result, flat);
    assert_eq!(source, original);
}

#[test]
fn unknown_captures_and_incompatible_results_never_authorize_a_conversion() {
    let environment = Environment::new();
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    let (_, flat) = stages(&mut prep);
    let unknown = local(&mut prep, Expr::bvar(10).unwrap(), flat);
    prep.captured_result(&unknown, &[]).unwrap();
    assert_eq!(prep.lambdas[0].result, flat);
    let wrong_tail = interface(&mut prep, vec![ValueType::Nat], ValueType::String);
    let wrong = interface(&mut prep, vec![ValueType::Nat], wrong_tail);
    let incompatible = local(&mut prep, Expr::bvar(1).unwrap(), flat);
    prep.captured_result(&incompatible, &[wrong]).unwrap();
    assert_eq!(prep.lambdas[1].result, flat);
    // Fixed branch/catalog lambdas do not acquire a different public ABI.
    let fixed = Expr::lam(
        name("fixed"),
        Expr::const_(name("Nat"), vec![]),
        Expr::bvar(1).unwrap(),
        BinderInfo::Default,
    );
    prep.lambdas[1].lambda = fixed.clone();
    let (staged, _) = stages(&mut prep);
    prep.captured_result(&fixed, &[staged]).unwrap();
    assert_eq!(prep.lambdas[1].result, flat);
}

#[test]
fn capture_analysis_reports_context_and_work_exhaustion_as_typed_nonanswers() {
    let environment = Environment::new();
    let mut prep = Preparation::new(
        &environment,
        IngressLimits {
            max_context_depth: 0,
            ..IngressLimits::default()
        },
    );
    assert_eq!(
        prep.captured_result(&Expr::bvar(0).unwrap(), &[ValueType::Nat]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 0,
            observed: 1,
        })
    );
    let mut prep = Preparation::new(
        &environment,
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        prep.captured_result(&Expr::bvar(0).unwrap(), &[ValueType::Nat]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            ..
        })
    ));
}

#[test]
fn deep_capture_scopes_use_heap_frames_and_do_not_run_strict_initializers() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let environment = Environment::new();
            let mut prep = Preparation::new(&environment, IngressLimits::default());
            let (staged, flat) = stages(&mut prep);
            let mut source = local(&mut prep, Expr::bvar(2001).unwrap(), flat);
            for _ in 0..2000 {
                source = Expr::let_e(
                    Name::anonymous(),
                    Expr::const_(name("Nat"), vec![]),
                    // An unknown initializer is inspected, never evaluated or
                    // removed; this is metadata analysis, not an admission.
                    Expr::const_(name("strictUnknown"), vec![]),
                    source,
                    false,
                );
            }
            let original = source.clone();
            prep.captured_result(&source, &[staged]).unwrap();
            assert_eq!(prep.lambdas[0].result, staged);
            assert_eq!(source, original);
        })
        .unwrap()
        .join()
        .unwrap();
}
