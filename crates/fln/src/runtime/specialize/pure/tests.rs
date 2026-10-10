use super::*;
use fln_core::options::DataValue;

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn natural() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}

fn limits(nodes: usize) -> IngressLimits {
    IngressLimits {
        max_nodes: nodes,
        ..IngressLimits::default()
    }
}

fn nodes<T>(result: Result<T, IngressError>, limit: usize, observed: usize) {
    assert_eq!(
        result.err(),
        Some(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        })
    );
}

fn capture_body() -> Expr {
    let branch = || Expr::app(b(2), b(1));
    Expr::lam(
        name("x"),
        natural(),
        Expr::app(branch(), branch()),
        BinderInfo::Default,
    )
}

#[test]
fn exact_substitution_reuses_open_syntax_without_capturing_relative_variables() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let replacement = Expr::app(b(0), b(2));
    let result_branch = || Expr::app(b(1), Expr::app(b(1), b(3)));
    let expected = Expr::lam(
        name("x"),
        natural(),
        Expr::app(result_branch(), result_branch()),
        BinderInfo::Default,
    );
    assert_eq!(
        preparation
            .substitution(&capture_body(), &replacement)
            .unwrap(),
        expected
    );
    let cold_work = preparation.visited;
    assert!(cold_work > 1);
    assert_eq!(preparation.specializations.pure.substitutions.len(), 1);

    // Independently allocated, equal syntax has the same key. The external
    // variable above the substituted one is still decremented, while the open
    // replacement is lifted under exactly the one binder in the source.
    assert_eq!(
        preparation
            .substitution(&capture_body(), &Expr::app(b(0), b(2)))
            .unwrap(),
        expected
    );
    assert_eq!(preparation.visited, cold_work + 1);
    assert_eq!(preparation.specializations.pure.substitutions.len(), 1);
    let changed_branch = || Expr::app(b(1), b(1));
    assert_eq!(
        preparation.substitution(&capture_body(), &b(0)).unwrap(),
        Expr::lam(
            name("x"),
            natural(),
            Expr::app(changed_branch(), changed_branch()),
            BinderInfo::Default,
        )
    );
    assert_eq!(preparation.specializations.pure.substitutions.len(), 2);
}

#[test]
fn substitution_keys_preserve_names_binder_information_metadata_and_replacements() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let cases = [
        ("x", BinderInfo::Default, true),
        ("renamed", BinderInfo::Default, true),
        ("x", BinderInfo::Implicit, true),
        ("x", BinderInfo::Default, false),
    ];
    let mut entries = 0;
    for (label, info, borrowed) in cases {
        let metadata = KVMap::from_entries(vec![(name("borrowed"), DataValue::OfBool(borrowed))]);
        let source = Expr::mdata(
            metadata.clone(),
            Expr::lam(name(label), natural(), b(1), info),
        );
        for number in [7, 8] {
            let value = nat::literal(number);
            let expected = Expr::mdata(
                metadata.clone(),
                Expr::lam(name(label), natural(), value.clone(), info),
            );
            assert_eq!(preparation.substitution(&source, &value).unwrap(), expected);
            entries += 1;
            assert_eq!(
                preparation.specializations.pure.substitutions.len(),
                entries
            );
            let before = preparation.visited;
            assert_eq!(preparation.substitution(&source, &value).unwrap(), expected);
            assert_eq!(preparation.visited, before + 1);
        }
    }
}

fn universe_body(first: Level, second: Level, info: BinderInfo) -> Expr {
    Expr::lam(
        name("A"),
        Expr::sort(first.clone()),
        Expr::app(Expr::const_(name("poly"), vec![first, second]), b(1)),
        info,
    )
}

#[test]
fn universe_keys_are_ordered_exact_and_keep_replacement_levels_simultaneous() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let u = name("u");
    let v = name("v");
    let source = universe_body(
        Level::param(u.clone()),
        Level::param(v.clone()),
        BinderInfo::Default,
    );
    let params = [u.clone(), v.clone()];
    let levels = [Level::param(v.clone()), Level::one()];
    let expected = universe_body(Level::param(v.clone()), Level::one(), BinderInfo::Default);
    assert_eq!(
        preparation
            .universe_instance(&source, &params, &levels)
            .unwrap(),
        expected
    );
    // In particular u -> v does not become u -> 1 through the other row.
    let before = preparation.visited;
    let independently_built = universe_body(
        Level::param(u.clone()),
        Level::param(v.clone()),
        BinderInfo::Default,
    );
    assert_eq!(
        preparation
            .universe_instance(&independently_built, &params, &levels)
            .unwrap(),
        expected
    );
    // Lookup plus the two ordered names and two ordered levels are charged.
    assert_eq!(preparation.visited, before + 5);
    assert_eq!(preparation.specializations.pure.universes.len(), 1);
    assert_eq!(
        preparation
            .universe_instance(&source, &[v.clone(), u.clone()], &levels)
            .unwrap(),
        universe_body(Level::one(), Level::param(v.clone()), BinderInfo::Default)
    );
    assert_eq!(
        preparation
            .universe_instance(&source, &params, &[Level::zero(), Level::one()])
            .unwrap(),
        universe_body(Level::zero(), Level::one(), BinderInfo::Default)
    );
    // Reordering both vectors produces the same transform but remains an
    // exact distinct input, rather than trusting a partial map or fingerprint.
    assert_eq!(
        preparation
            .universe_instance(
                &source,
                &[v.clone(), u.clone()],
                &[Level::one(), Level::param(v.clone())],
            )
            .unwrap(),
        expected
    );
    let implicit = universe_body(
        Level::param(u),
        Level::param(v.clone()),
        BinderInfo::Implicit,
    );
    assert_eq!(
        preparation
            .universe_instance(&implicit, &params, &levels)
            .unwrap(),
        universe_body(Level::param(v), Level::one(), BinderInfo::Implicit)
    );
    assert_eq!(preparation.specializations.pure.universes.len(), 5);
}

#[test]
fn existing_no_op_and_malformed_arity_paths_keep_their_original_work() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, limits(0));
    let u = name("u");
    let parameter = Expr::sort(Level::param(u.clone()));
    assert_eq!(
        preparation.universe_instance(&parameter, &[], &[]).unwrap(),
        parameter
    );
    assert_eq!(
        preparation
            .universe_instance(&natural(), &[u.clone()], &[Level::one()])
            .unwrap(),
        natural()
    );
    // The original no-op rule does not inspect unused, equal-length maps.
    assert_eq!(
        preparation
            .universe_instance(
                &natural(),
                &[u.clone(), u.clone()],
                &[Level::zero(), Level::one()],
            )
            .unwrap(),
        natural()
    );
    for source in [natural(), parameter] {
        assert!(matches!(
            preparation.universe_instance(&source, std::slice::from_ref(&u), &[]),
            Err(IngressError::UnsupportedNode { .. })
        ));
    }
    assert_eq!(preparation.visited, 0);
    assert!(preparation.specializations.pure.universes.is_empty());
    preparation.limits.max_nodes = 6;
    let mut large_open_replacement = b(0);
    for _ in 0..20 {
        large_open_replacement = Expr::app(large_open_replacement.clone(), large_open_replacement);
    }
    assert_eq!(
        preparation
            .substitution(&b(1), &large_open_replacement)
            .unwrap(),
        b(0)
    );
    assert_eq!(
        preparation
            .substitution(&natural(), &large_open_replacement)
            .unwrap(),
        natural()
    );
    assert_eq!(
        preparation
            .substitution(&b(0), &large_open_replacement)
            .unwrap(),
        large_open_replacement
    );
    assert_eq!(preparation.visited, 6);
    assert!(preparation.specializations.pure.substitutions.is_empty());
}

#[test]
fn substitution_insertion_and_hits_are_metered_and_failed_work_is_not_published() {
    let environment = Environment::new();
    let body = capture_body();
    let replacement = Expr::app(b(0), b(2));
    let mut complete = Preparation::new(&environment, IngressLimits::default());
    let expected = complete.substitution(&body, &replacement).unwrap();
    let exact = complete.visited;
    let mut bounded = Preparation::new(&environment, limits(exact - 1));
    nodes(bounded.substitution(&body, &replacement), exact - 1, exact);
    assert!(bounded.specializations.pure.substitutions.is_empty());
    bounded.limits.max_nodes = IngressLimits::default().max_nodes;
    let before_retry = bounded.visited;
    assert_eq!(bounded.substitution(&body, &replacement).unwrap(), expected);
    assert_eq!(bounded.visited, before_retry + exact);
    assert_eq!(bounded.specializations.pure.substitutions.len(), 1);
    let before_hit = bounded.visited;
    bounded.limits.max_nodes = before_hit + 1;
    assert_eq!(bounded.substitution(&body, &replacement).unwrap(), expected);
    assert_eq!(bounded.visited, before_hit + 1);
    nodes(
        bounded.substitution(&body, &replacement),
        before_hit + 1,
        before_hit + 2,
    );
    assert_eq!(bounded.specializations.pure.substitutions.len(), 1);

    let overflowing = Expr::lam(name("x"), natural(), b(1), BinderInfo::Default);
    let greatest = b(fln_core::expr::MAX_LOOSE_BVAR_RANGE - 1);
    let mut malformed = Preparation::new(&environment, IngressLimits::default());
    for _ in 0..2 {
        assert!(matches!(
            malformed.substitution(&overflowing, &greatest),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(malformed.specializations.pure.substitutions.is_empty());
    }
    assert_eq!(
        malformed.substitution(&overflowing, &b(0)).unwrap(),
        overflowing
    );
}

#[test]
fn universe_failures_never_publish_and_completed_hits_respect_remaining_fuel() {
    let environment = Environment::new();
    let u = name("u");
    let v = name("v");
    let source = universe_body(
        Level::param(u.clone()),
        Level::param(v.clone()),
        BinderInfo::Default,
    );
    let params = [u.clone(), v];
    let levels = [Level::zero(), Level::one()];
    let mut complete = Preparation::new(&environment, IngressLimits::default());
    let expected = complete
        .universe_instance(&source, &params, &levels)
        .unwrap();
    let exact = complete.visited;
    let mut bounded = Preparation::new(&environment, limits(exact - 1));
    nodes(
        bounded.universe_instance(&source, &params, &levels),
        exact - 1,
        exact,
    );
    assert!(bounded.specializations.pure.universes.is_empty());
    bounded.limits.max_nodes = IngressLimits::default().max_nodes;
    let before_retry = bounded.visited;
    assert_eq!(
        bounded
            .universe_instance(&source, &params, &levels)
            .unwrap(),
        expected
    );
    assert_eq!(bounded.visited, before_retry + exact);
    let before_hit = bounded.visited;
    bounded.limits.max_nodes = before_hit + 5;
    assert_eq!(
        bounded
            .universe_instance(&source, &params, &levels)
            .unwrap(),
        expected
    );
    assert_eq!(bounded.visited, before_hit + 5);
    nodes(
        bounded.universe_instance(&source, &params, &levels),
        before_hit + 5,
        before_hit + 6,
    );
    assert_eq!(bounded.specializations.pure.universes.len(), 1);
    let mut malformed = Preparation::new(&environment, IngressLimits::default());
    for _ in 0..2 {
        assert!(matches!(
            malformed.universe_instance(&source, &[u.clone(), u.clone()], &levels),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(malformed.specializations.pure.universes.is_empty());
    }
    assert_eq!(
        malformed
            .universe_instance(&source, &params, &levels)
            .unwrap(),
        expected
    );
}

#[test]
fn completed_transform_tables_refuse_growth_without_losing_existing_results() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let body = capture_body();
    let first = preparation.substitution(&body, &natural()).unwrap();
    let first_key = (body.clone(), natural());
    let second_key = (body, b(0));
    nodes(
        remember(
            &mut preparation.specializations.pure.substitutions,
            second_key.clone(),
            b(1),
            1,
        ),
        1,
        2,
    );
    assert_eq!(preparation.specializations.pure.substitutions.len(), 1);
    assert_eq!(
        preparation
            .specializations
            .pure
            .substitutions
            .get(&first_key),
        Some(&first)
    );
    assert!(
        !preparation
            .specializations
            .pure
            .substitutions
            .contains_key(&second_key)
    );
    // The ordered key copy is bounded before allocating its backing buffer.
    preparation.limits.max_nodes = 1;
    let before = preparation.visited;
    nodes(
        copy_key_slice(&mut preparation, &[name("u"), name("v")]),
        1,
        2,
    );
    assert_eq!(preparation.visited, before);
}
