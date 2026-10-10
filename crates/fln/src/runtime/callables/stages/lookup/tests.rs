use super::*;

fn lambda(label: &str) -> Expr {
    Expr::lam(
        name(label),
        Expr::const_(name("Nat"), vec![]),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    )
}

fn add(preparation: &mut Preparation<'_>, source: Expr, result: ValueType) {
    preparation.lambdas.push(LambdaBinding {
        lambda: source,
        parameters: vec![ValueType::Nat],
        parameter_ownership: borrowed_runtime_parameters(1).unwrap(),
        result,
        result_ownership: result_ownership(result),
        recursion: LambdaRecursion::NonRecursive,
    });
}

#[test]
fn lookup_keeps_latest_rows_and_reads_refined_metadata_from_the_live_table() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let source = lambda("same");
    add(&mut preparation, source.clone(), ValueType::Nat);
    add(&mut preparation, lambda("other"), ValueType::Nat);
    add(&mut preparation, source.clone(), ValueType::String);
    let index = LambdaIndex::new(&mut preparation).unwrap();
    let slot = index.get(&mut preparation, &source).unwrap().unwrap();
    assert_eq!(slot, 2);
    assert_eq!(preparation.lambdas[slot].result, ValueType::String);

    preparation.lambdas[slot].result = ValueType::Constructor;
    preparation.lambdas[slot].result_ownership = result_ownership(ValueType::Constructor);
    let slot = index.get(&mut preparation, &source).unwrap().unwrap();
    assert_eq!(preparation.lambdas[slot].result, ValueType::Constructor);
    assert_eq!(
        preparation.lambdas[slot].result_ownership,
        result_ownership(ValueType::Constructor)
    );

    // Rows discovered after this pass starts take precedence over its prefix.
    add(&mut preparation, source.clone(), ValueType::Bool);
    assert_eq!(index.get(&mut preparation, &source).unwrap(), Some(3));
    assert_eq!(
        index.get(&mut preparation, &lambda("absent")).unwrap(),
        None
    );

    // A separate pass starts from the table it is actually given. No syntax
    // identity or missing lookup survives an earlier refinement invocation.
    let replaced = lambda("replacedBetweenPasses");
    preparation.lambdas[0].lambda = replaced.clone();
    let next = LambdaIndex::new(&mut preparation).unwrap();
    assert_eq!(next.get(&mut preparation, &replaced).unwrap(), Some(0));
    assert_eq!(next.get(&mut preparation, &source).unwrap(), Some(3));
}

#[test]
fn bounded_index_failure_leaves_metadata_available_to_a_fresh_retry() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let first = lambda("first");
    let second = lambda("second");
    add(&mut preparation, first.clone(), ValueType::Nat);
    add(&mut preparation, second.clone(), ValueType::String);
    preparation.limits.max_nodes = 1;
    assert!(matches!(
        LambdaIndex::new(&mut preparation),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 1,
            observed: 2,
        })
    ));
    assert_eq!(preparation.lambdas.len(), 2);
    assert_eq!(preparation.lambdas[0].lambda, first);
    assert_eq!(preparation.lambdas[1].result, ValueType::String);

    preparation.limits.max_nodes = IngressLimits::default().max_nodes;
    preparation.limits.max_lambda_bindings = 1;
    assert!(matches!(
        LambdaIndex::new(&mut preparation),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::LambdaBindings,
            limit: 1,
            observed: 2,
        })
    ));
    preparation.limits.max_lambda_bindings = IngressLimits::default().max_lambda_bindings;
    let retry = LambdaIndex::new(&mut preparation).unwrap();
    assert_eq!(retry.get(&mut preparation, &first).unwrap(), Some(0));
    assert_eq!(retry.get(&mut preparation, &second).unwrap(), Some(1));
}
