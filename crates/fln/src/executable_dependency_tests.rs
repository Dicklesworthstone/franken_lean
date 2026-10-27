//! Executable dependency discovery walks an immutable expression DAG, while
//! retaining the existing executable-only projection and per-inspection budget.

use super::{
    BinderInfo, Expr, IngressError, IngressLimits, IngressResource, KVMap, Name,
    collect_executable_constants,
};
use std::collections::BTreeSet;

fn name(label: &str) -> Name {
    Name::from_components([label])
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn expected_names() -> BTreeSet<Name> {
    BTreeSet::from([name("alpha"), name("beta"), name("gamma"), name("delta")])
}

fn shared_source(depth: usize) -> Expr {
    let mut shared = Expr::app(constant("alpha"), constant("beta"));
    for _ in 0..depth {
        shared = Expr::app(shared.clone(), shared);
    }
    // Type annotations and projection labels have never been executable
    // dependencies. Keep checking that boundary while traversing every value
    // position, including the independent branch after the shared DAG.
    Expr::let_e(
        name("ignoredLetName"),
        constant("ignoredLetType"),
        shared,
        Expr::app(
            Expr::lam(
                name("ignoredLambdaName"),
                constant("ignoredLambdaType"),
                Expr::proj(name("ignoredProjectionLabel"), 0, constant("gamma")),
                BinderInfo::Default,
            ),
            Expr::forall_e(
                name("ignoredForallName"),
                constant("ignoredForallType"),
                Expr::mdata(KVMap::new(), constant("delta")),
                BinderInfo::Default,
            ),
        ),
        false,
    )
}

#[test]
fn shared_executable_dag_collects_all_globals_with_bounded_work() {
    // Expanding this DAG as a tree requires more than 2^64 visits. Dependency
    // discovery only needs the four global names, including the later branch.
    let depth = 64;
    let source = shared_source(depth);
    let limits = IngressLimits {
        max_nodes: 256,
        ..IngressLimits::default()
    };
    let mut names = BTreeSet::new();
    let mut visited_nodes = 0;
    collect_executable_constants(&source, &mut names, &mut visited_nodes, limits).unwrap();
    assert_eq!(names, expected_names());
    assert!(
        visited_nodes <= 2 * depth + 16,
        "shared edges are inspected without expanding their descendants again: {visited_nodes}"
    );
}

#[test]
fn shared_dependency_discovery_refuses_at_the_budget_and_retries_cleanly() {
    let source = shared_source(24);
    let limits = IngressLimits {
        max_nodes: 256,
        ..IngressLimits::default()
    };
    let mut expected = BTreeSet::new();
    let mut measured = 0;
    collect_executable_constants(&source, &mut expected, &mut measured, limits).unwrap();
    assert_eq!(expected, expected_names());

    let boundary = measured - 1;
    let mut refused_names = BTreeSet::new();
    let mut refused_nodes = 0;
    let error = collect_executable_constants(
        &source,
        &mut refused_names,
        &mut refused_nodes,
        IngressLimits {
            max_nodes: boundary,
            ..limits
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        } if limit == boundary && observed == boundary + 1
    ));

    let mut retry_names = BTreeSet::new();
    let mut retry_nodes = 0;
    collect_executable_constants(&source, &mut retry_names, &mut retry_nodes, limits).unwrap();
    assert_eq!(retry_names, expected);
    assert_eq!(retry_nodes, measured);
}

#[test]
fn repeated_pending_nodes_still_consume_the_aggregate_work_budget() {
    let leaf = constant("leaf");
    let source = Expr::app(leaf.clone(), leaf);
    let mut names = BTreeSet::new();
    // Catalog discovery accumulates work across multiple expression roots.
    let mut visited_nodes = 7;
    let error = collect_executable_constants(
        &source,
        &mut names,
        &mut visited_nodes,
        IngressLimits {
            max_nodes: 9,
            ..IngressLimits::default()
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 9,
            observed: 10,
        }
    ));

    let mut retry_names = BTreeSet::new();
    let mut retry_nodes = 7;
    collect_executable_constants(
        &source,
        &mut retry_names,
        &mut retry_nodes,
        IngressLimits {
            max_nodes: 10,
            ..IngressLimits::default()
        },
    )
    .unwrap();
    assert_eq!(retry_names, BTreeSet::from([name("leaf")]));
    assert_eq!(retry_nodes, 10);
}
