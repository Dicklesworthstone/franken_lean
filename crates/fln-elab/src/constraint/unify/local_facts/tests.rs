//! Syntax-only differential tests; these expressions confer no typing authority.
use super::*;
use fln_core::expr::BinderInfo;
use fln_core::options::KVMap;
use std::cell::Cell;

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn local(s: &str) -> Expr {
    Expr::fvar(FVarId(name(s)))
}
fn meter(cancelled: &dyn Fn() -> bool) -> Meter<'_> {
    Meter {
        steps: 0,
        nodes: 0,
        max_steps: u64::MAX,
        max_nodes: usize::MAX,
        heartbeat_bound: false,
        cancelled,
    }
}
fn tower(n: usize, mut value: Expr) -> Expr {
    let head = Expr::const_(name("head"), vec![]);
    for _ in 0..n {
        value = Expr::app(head.clone(), value);
    }
    value
}
fn reference(expr: &Expr) -> HashSet<FVarId> {
    super::super::facts(expr, &mut meter(&|| false))
        .unwrap()
        .fvars
}
fn copy(cache: &Cache) -> Cache {
    Cache {
        entries: cache.entries.clone(),
        identities: cache.identities,
    }
}

#[test]
fn rebuilt_parents_reuse_completed_subtrees_without_rewalking_them() {
    let shared = tower(256, local("x"));
    let mut cache = Cache::default();
    let mut cold = meter(&|| false);
    assert_eq!(
        cache.scan(&shared, &mut cold).unwrap().unwrap(),
        reference(&shared)
    );
    let parent = Expr::app(shared, local("y"));
    let mut warm = meter(&|| false);
    assert_eq!(
        cache.scan(&parent, &mut warm).unwrap().unwrap(),
        reference(&parent)
    );
    assert!(warm.steps < 64, "{}", warm.steps);
    assert!(cold.steps > 500, "{}", cold.steps);
    assert!(cache.entries.len() <= MAX_ENTRIES);
    assert!(cache.identities <= MAX_IDENTITIES);
}

#[test]
fn exact_syntactic_locals_match_the_original_walk_in_all_containers() {
    let mut nodes = vec![
        local("x"),
        local("y"),
        local("z"),
        Expr::bvar(0).unwrap(),
        Expr::const_(name("closed"), vec![]),
        Expr::sort(Level::one()),
    ];
    let mut seed = 0x28ed_49bf_d2b3_1981u64;
    let mut choose = |n: usize| {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        ((seed >> 32) as usize) % n
    };
    let mut cache = Cache::default();
    for i in 0..256 {
        let a = nodes[choose(nodes.len())].clone();
        let b = nodes[choose(nodes.len())].clone();
        let c = nodes[choose(nodes.len())].clone();
        let expression = match i % 7 {
            0 => Expr::app(a.clone(), a),
            1 => Expr::lam(name("binder"), a, b, BinderInfo::Implicit),
            2 => Expr::forall_e(name("binder"), a, b, BinderInfo::Default),
            3 => Expr::let_e(name("binding"), a, b, c, i % 2 == 0),
            4 => Expr::mdata(KVMap::new(), a),
            5 => Expr::proj(name("Record"), (i % 3) as u64, a),
            _ => Expr::app(a, b),
        };
        let root = tower(24, Expr::app(local("anchor"), expression.clone()));
        let expected = reference(&root);
        let actual = cache
            .scan(&root, &mut meter(&|| false))
            .unwrap()
            .expect("this bounded differential population fits the cache");
        assert_eq!(actual, expected);
        nodes.push(expression);
    }
}

#[test]
fn universe_identities_holes_and_shallow_terms_keep_the_original_path() {
    let mut cache = Cache::default();
    for root in [
        local("x"),
        tower(4, local("x")),
        tower(64, Expr::bvar(0).unwrap()),
        tower(
            64,
            Expr::app(local("x"), Expr::sort(Level::param(name("u")))),
        ),
        tower(
            64,
            Expr::app(local("x"), Expr::sort(Level::mvar(LMVarId(name("u"))))),
        ),
        tower(
            64,
            Expr::app(local("x"), Expr::mvar(MVarId(name("unknown")))),
        ),
    ] {
        assert!(cache.scan(&root, &mut meter(&|| false)).unwrap().is_none());
        assert!(cache.entries.is_empty());
    }
}

#[test]
fn cancellation_and_all_work_boundaries_publish_no_partial_metadata() {
    let mut base = Cache::default();
    base.scan(&tower(32, local("existing")), &mut meter(&|| false))
        .unwrap()
        .unwrap();
    let root = tower(32, local("new"));
    let mut success = meter(&|| false);
    copy(&base).scan(&root, &mut success).unwrap().unwrap();
    for stop in 0..success.steps {
        let mut trial = copy(&base);
        let mut bounded = meter(&|| false);
        bounded.max_steps = stop;
        assert!(matches!(
            trial.scan(&root, &mut bounded),
            Err(UnificationError::StepLimit { .. })
        ));
        assert_eq!(trial.entries.len(), base.entries.len());
        assert_eq!(trial.identities, base.identities);
        assert!(!trial.entries.contains_key(&root.allocation_identity()));
    }
    for stop in [0, 1, success.nodes - 1] {
        let mut trial = copy(&base);
        let mut bounded = meter(&|| false);
        bounded.max_nodes = stop;
        assert!(matches!(
            trial.scan(&root, &mut bounded),
            Err(UnificationError::NodeLimit { .. })
        ));
        assert_eq!(trial.entries.len(), base.entries.len());
        assert_eq!(trial.identities, base.identities);
    }
    for stop in [0, success.steps / 2, success.steps - 1] {
        let polls = Cell::new(0);
        let cancel = || {
            let n = polls.get();
            polls.set(n + 1);
            n >= stop
        };
        let mut trial = copy(&base);
        assert!(matches!(
            trial.scan(&root, &mut meter(&cancel)),
            Err(UnificationError::Cancelled)
        ));
        assert_eq!(trial.entries.len(), base.entries.len());
        assert_eq!(trial.identities, base.identities);
    }
    let mut exact = meter(&|| false);
    exact.max_steps = success.steps;
    exact.max_nodes = success.nodes;
    assert_eq!(
        copy(&base).scan(&root, &mut exact).unwrap().unwrap(),
        reference(&root)
    );
    let mut heartbeat = meter(&|| false);
    heartbeat.max_steps = 0;
    heartbeat.heartbeat_bound = true;
    assert!(matches!(
        copy(&base).scan(&root, &mut heartbeat),
        Err(UnificationError::HeartbeatLimit)
    ));
}

#[test]
fn saturation_is_an_optional_cache_miss_not_lost_scope_information() {
    let mut cache = Cache::default();
    let mut root = local("first");
    for i in 0..512 {
        root = Expr::app(root, local(&format!("local{i}")));
    }
    assert!(cache.scan(&root, &mut meter(&|| false)).unwrap().is_none());
    assert!(cache.entries.is_empty());
    assert_eq!(cache.identities, 0);
    assert_eq!(reference(&root).len(), 513);
    let one = tower(32, local("small"));
    assert_eq!(
        cache.scan(&one, &mut meter(&|| false)).unwrap().unwrap(),
        reference(&one)
    );
    let full = tower(MAX_ENTRIES, local("last"));
    assert!(cache.scan(&full, &mut meter(&|| false)).unwrap().is_none());
    assert!(cache.entries.len() < MAX_ENTRIES);
    assert!(cache.identities < MAX_IDENTITIES);
    assert_eq!(reference(&full), HashSet::from([FVarId(name("last"))]));
}

#[test]
fn cache_keys_pin_allocations_and_never_identify_distinct_local_names() {
    let mut cache = Cache::default();
    let first = tower(32, local("first"));
    let key = first.allocation_identity();
    let expected = reference(&first);
    cache.scan(&first, &mut meter(&|| false)).unwrap().unwrap();
    drop(first);
    assert_eq!(cache.entries[&key].0.allocation_identity(), key);
    assert_eq!(reference(&cache.entries[&key].0), expected);
    let other = tower(32, local("other"));
    assert_ne!(other.allocation_identity(), key);
    assert_eq!(
        cache.scan(&other, &mut meter(&|| false)).unwrap().unwrap(),
        reference(&other)
    );
    let mut hit = meter(&|| true);
    assert!(matches!(
        cache.scan(&other, &mut hit),
        Err(UnificationError::Cancelled)
    ));
}
