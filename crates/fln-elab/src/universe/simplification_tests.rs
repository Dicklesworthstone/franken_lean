//! Regressions for work hidden in the smart constructors used by instantiation.
use super::*;
use fln_core::name::Name;

fn parameter(name: &str) -> Level {
    Level::param(Name::from_components([name]))
}

fn variable(name: &str) -> LMVarId {
    LMVarId(Name::from_components([name]))
}

fn diamond(mut level: Level, depth: usize) -> Level {
    for _ in 0..depth {
        level = Level::max(level.clone(), level).unwrap();
    }
    level
}

#[test]
fn nonzero_inspection_spends_the_callers_budget() {
    let level = Level::max(parameter("left"), parameter("right")).unwrap();
    let mut remaining = 2;
    assert_eq!(
        is_never_zero(&level, &mut remaining, 2),
        Err(UniverseInstantiationError::VisitLimit { limit: 2 }),
    );
    assert_eq!(remaining, 0);
    let mut remaining = 3;
    assert_eq!(is_never_zero(&level, &mut remaining, 3), Ok(false));
    assert_eq!(remaining, 0);
}

#[test]
fn nonzero_inspection_preserves_imax_and_left_short_circuit() {
    // A successor on imax's LEFT does not make it nonzero.
    let right = Level::imax(Level::one(), parameter("v")).unwrap();
    let mut remaining = 2;
    assert_eq!(is_never_zero(&right, &mut remaining, 2), Ok(false));
    assert_eq!(remaining, 0);

    // Once the left side of max is positive, its enormous right side is not read.
    let level = Level::max(Level::one(), diamond(parameter("v"), 64)).unwrap();
    let mut remaining = 2;
    assert_eq!(is_never_zero(&level, &mut remaining, 2), Ok(true));
    assert_eq!(remaining, 0);
}

#[test]
fn changed_imax_finishes_on_a_shared_parameter_diamond() {
    let u = variable("u");
    let replacement = parameter("replacement");
    let tail = diamond(parameter("tail"), 64);
    let input = Level::imax(Level::mvar(u.clone()), tail.clone()).unwrap();
    let expected = Level::imax(replacement.clone(), tail).unwrap();
    let mut store = UniverseStore::new();
    store.assign(u, replacement);
    let before = store.clone();

    // The old recursive predicate takes 2^65 - 1 calls on this 65-node DAG.
    // Neither the input nor the replacement is a positive numeral, so it has
    // to reach the entire relevant frontier before returning false.
    assert_eq!(store.instantiate_with_limit(&input, 1024), Ok(expected));
    assert_eq!(store, before);
}

#[test]
fn changed_imax_stops_without_publication_and_a_larger_retry_recovers() {
    let u = variable("u");
    let replacement = parameter("replacement");
    let tail = diamond(parameter("tail"), 64);
    let input = Level::imax(Level::mvar(u.clone()), tail.clone()).unwrap();
    let expected = Level::imax(replacement.clone(), tail).unwrap();
    let mut store = UniverseStore::new();
    store.assign(u, replacement);
    let before = store.clone();

    assert_eq!(
        store.instantiate_with_limit(&input, 16),
        Err(UniverseInstantiationError::VisitLimit { limit: 16 }),
    );
    assert_eq!(store, before);
    assert_eq!(store.instantiate_with_limit(&input, 1024), Ok(expected));
    assert_eq!(store, before);
}

#[test]
fn imax_simplification_fits_a_small_host_stack() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            let mut tail = parameter("tail");
            let left = parameter("left");
            for _ in 0..20_000 {
                tail = Level::imax(left.clone(), tail).unwrap();
            }
            let u = variable("u");
            let replacement = parameter("replacement");
            let input = Level::imax(Level::mvar(u.clone()), tail.clone()).unwrap();
            let expected = Level::imax(replacement.clone(), tail).unwrap();
            let mut store = UniverseStore::new();
            store.assign(u, replacement);
            assert_eq!(store.instantiate(&input), Ok(expected));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn bounded_nonzero_predicate_agrees_with_the_core_constructor_inventory() {
    let mut levels = vec![
        Level::zero(),
        Level::one(),
        parameter("p"),
        Level::mvar(variable("u")),
    ];
    for _ in 0..2 {
        let inputs = levels.clone();
        for left in &inputs {
            levels.push(left.clone().succ().unwrap());
            for right in &inputs {
                levels.push(Level::max(left.clone(), right.clone()).unwrap());
                levels.push(Level::imax(left.clone(), right.clone()).unwrap());
            }
        }
    }
    for level in levels {
        let mut remaining = 4096;
        assert_eq!(
            is_never_zero(&level, &mut remaining, 4096),
            Ok(level.is_never_zero()),
        );
    }
}

#[test]
fn equal_level_diamonds_are_compared_under_the_callers_budget() {
    let left = diamond(parameter("p"), 64);
    let right = diamond(parameter("p"), 64);
    let mut remaining = 16;
    assert_eq!(
        equal_levels(&left, &right, &mut remaining, 16),
        Err(UniverseInstantiationError::VisitLimit { limit: 16 }),
    );
    assert_eq!(remaining, 0);
    let mut remaining = 1024;
    assert_eq!(equal_levels(&left, &right, &mut remaining, 1024), Ok(true));
}

#[test]
fn cloned_compound_levels_keep_the_constant_time_identity_path() {
    let original = diamond(parameter("p"), 20_000);
    let cloned = original.clone();
    let mut remaining = 1;
    assert_eq!(
        equal_levels(&original, &cloned, &mut remaining, 1),
        Ok(true)
    );
    assert_eq!(remaining, 0);
    let mut remaining = 0;
    assert_eq!(
        equal_levels(&original, &cloned, &mut remaining, 0),
        Err(UniverseInstantiationError::VisitLimit { limit: 0 }),
    );
}

#[test]
fn bounded_comparison_agrees_with_core_structural_equality() {
    let seeds = [
        Level::zero(),
        Level::one(),
        parameter("p"),
        parameter("q"),
        Level::mvar(variable("u")),
        Level::mvar(variable("v")),
    ];
    let mut levels = seeds.to_vec();
    for left in &seeds {
        levels.push(left.clone().succ().unwrap());
        for right in &seeds {
            levels.push(Level::max(left.clone(), right.clone()).unwrap());
            levels.push(Level::imax(left.clone(), right.clone()).unwrap());
        }
    }
    for left in &levels {
        for right in &levels {
            let mut remaining = 1024;
            assert_eq!(
                equal_levels(left, right, &mut remaining, 1024),
                Ok(left == right),
            );
        }
    }
}

#[test]
fn successor_peeling_has_an_exact_exhaustion_boundary() {
    let input = parameter("p").succ().unwrap().succ().unwrap();
    let mut remaining = 2;
    assert_eq!(
        level_offset(&input, &mut remaining, 2),
        Err(UniverseInstantiationError::VisitLimit { limit: 2 }),
    );
    assert_eq!(remaining, 0);
    let mut remaining = 3;
    let (base, offset) = level_offset(&input, &mut remaining, 3).unwrap();
    assert_eq!(base, &parameter("p"));
    assert_eq!(offset, 2);
    assert_eq!(remaining, 0);
}

#[test]
fn max_over_a_skipped_successor_assignment_stops_and_recovers() {
    let u = variable("u");
    let mut replacement = parameter("p");
    for _ in 0..20_000 {
        replacement = replacement.succ().unwrap();
    }
    let input = Level::max(Level::mvar(u.clone()), Level::zero()).unwrap();
    let mut store = UniverseStore::new();
    store.assign(u, replacement.clone());
    let before = store.clone();
    assert_eq!(
        store.instantiate_with_limit(&input, 16),
        Err(UniverseInstantiationError::VisitLimit { limit: 16 }),
    );
    assert_eq!(store, before);
    assert_eq!(store.instantiate(&input), Ok(replacement));
    assert_eq!(store, before);
}

#[test]
fn equal_assignment_and_original_dags_do_not_bypass_instantiation_limits() {
    let u = variable("u");
    let replacement = diamond(parameter("p"), 64);
    let original = diamond(parameter("p"), 64);
    let input = Level::max(Level::mvar(u.clone()), original).unwrap();
    let mut store = UniverseStore::new();
    store.assign(u, replacement.clone());
    let before = store.clone();
    assert_eq!(
        store.instantiate_with_limit(&input, 16),
        Err(UniverseInstantiationError::VisitLimit { limit: 16 }),
    );
    assert_eq!(store, before);
    assert_eq!(store.instantiate_with_limit(&input, 1024), Ok(replacement));
    assert_eq!(store, before);
}

#[test]
fn expressions_and_smart_constructors_share_one_work_limit() {
    let u = variable("u");
    let mut replacement = parameter("p");
    for _ in 0..96 {
        replacement = replacement.succ().unwrap();
    }
    let input = Expr::sort(Level::max(Level::mvar(u.clone()), Level::zero()).unwrap());
    let mut store = UniverseStore::new();
    store.assign(u, replacement.clone());
    let before = store.clone();
    assert_eq!(
        store.instantiate_expr_with_limit(&input, 32),
        Err(UniverseInstantiationError::VisitLimit { limit: 32 }),
    );
    assert_eq!(store, before);
    assert_eq!(
        store.instantiate_expr_with_limit(&input, 512),
        Ok(Expr::sort(replacement)),
    );
    assert_eq!(store, before);
}

#[test]
fn mvar_free_roots_still_need_no_instantiation_work() {
    let u = variable("u");
    let mut store = UniverseStore::new();
    store.assign(u, parameter("p"));
    let input = diamond(parameter("q"), 64);
    assert_eq!(store.instantiate_with_limit(&input, 0), Ok(input.clone()));
    let input = Expr::sort(input);
    assert_eq!(store.instantiate_expr_with_limit(&input, 0), Ok(input));
}

#[test]
fn smart_constructors_preserve_the_existing_pin_simplification_rules() {
    let zero = Level::zero();
    let one = Level::one();
    let two = one.clone().succ().unwrap();
    let u = parameter("u");
    let v = parameter("v");
    let succ_u = u.clone().succ().unwrap();
    let succ_succ_u = succ_u.clone().succ().unwrap();
    let max_uv = Level::max(u.clone(), v.clone()).unwrap();
    let max_vu = Level::max(v.clone(), u.clone()).unwrap();
    let max_cases = [
        (zero.clone(), u.clone(), u.clone()),
        (u.clone(), zero.clone(), u.clone()),
        (u.clone(), u.clone(), u.clone()),
        (one.clone(), two.clone(), two.clone()),
        (two.clone(), one.clone(), two),
        (succ_u.clone(), u.clone(), succ_u.clone()),
        (succ_u.clone(), succ_succ_u.clone(), succ_succ_u),
        (u.clone(), max_uv.clone(), max_uv.clone()),
        (u.clone(), max_vu.clone(), max_vu.clone()),
        (max_uv.clone(), v.clone(), max_uv.clone()),
        (max_vu.clone(), v.clone(), max_vu),
        (u.clone(), v.clone(), max_uv.clone()),
    ];
    for (left, right, expected) in max_cases {
        let mut remaining = 1024;
        assert_eq!(pin_mk_max(left, right, &mut remaining, 1024), Ok(expected));
    }
    let imax_cases = [
        (u.clone(), zero.clone(), zero),
        (Level::zero(), v.clone(), v.clone()),
        (one.clone(), v.clone(), v.clone()),
        (u.clone(), u.clone(), u.clone()),
        (u.clone(), one.clone(), Level::max(u.clone(), one).unwrap()),
        (
            v.clone(),
            succ_u.clone(),
            Level::max(v.clone(), succ_u).unwrap(),
        ),
        (u.clone(), v.clone(), Level::imax(u, v).unwrap()),
    ];
    for (left, right, expected) in imax_cases {
        let mut remaining = 1024;
        assert_eq!(pin_mk_imax(left, right, &mut remaining, 1024), Ok(expected));
    }
}

#[test]
fn shared_root_detection_covers_the_constructor_inventory_without_hash_equality() {
    let p = parameter("p");
    let q = parameter("q");
    for original in [
        Level::zero(),
        p.clone(),
        Level::mvar(variable("u")),
        p.clone().succ().unwrap(),
        Level::max(p.clone(), q.clone()).unwrap(),
        Level::imax(p.clone(), q.clone()).unwrap(),
    ] {
        let cloned = original.clone();
        assert!(shared_level_root(&original, &cloned));
        let mut remaining = 1;
        assert_eq!(
            equal_levels(&original, &cloned, &mut remaining, 1),
            Ok(true)
        );
        assert_eq!(remaining, 0);
    }
    // Separate but structurally equal compounds are not allocation-identical.
    let left = Level::max(p.clone(), q.clone()).unwrap();
    let right = Level::max(p, q).unwrap();
    assert_eq!(left, right);
    assert!(!shared_level_root(&left, &right));
    let mut remaining = 0;
    assert_eq!(
        equal_levels(&parameter("p"), &parameter("q"), &mut remaining, 0),
        Err(UniverseInstantiationError::VisitLimit { limit: 0 }),
    );
}
