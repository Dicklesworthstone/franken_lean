//! Compare the shortcut against the original unpruned metadata walk. These are
//! syntax-analysis fixtures, never declarations or evidence of kernel admission.
use super::*;
use fln_core::expr::BinderInfo;
use fln_core::options::KVMap;
use std::cell::Cell;

fn name(label: &str) -> Name {
    Name::from_components([label])
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

// The pre-change algorithm is retained verbatim as a test-only reference. It
// intentionally does not consult the packed syntax flags being tested.
fn legacy_facts(expr: &Expr, meter: &mut Meter<'_>) -> Result<Facts, UnificationError> {
    let mut result = Facts::default();
    let mut seen = HashSet::new();
    let mut seen_levels = HashSet::new();
    let mut params = HashSet::new();
    let mut uvars = HashSet::new();
    let mut pending = vec![expr];
    let mut levels = Vec::new();
    while let Some(current) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(current.node())) {
            continue;
        }
        meter.node()?;
        match current.node() {
            ExprNode::FVar { id } => {
                result.fvars.insert(id.clone());
            }
            ExprNode::Sort { level } => levels.push(level),
            ExprNode::Const {
                levels: arguments, ..
            } => levels.extend(arguments.iter().rev()),
            _ => {}
        }
        pending.extend(children(current).into_iter().rev().flatten());
    }
    while let Some(level) = levels.pop() {
        if !seen_levels.insert(std::ptr::from_ref(level)) {
            continue;
        }
        meter.node()?;
        match level.view() {
            LevelView::Param(name) if params.insert(name.clone()) => {
                result.params.push(name.clone())
            }
            LevelView::MVar(id) if uvars.insert(id.clone()) => result.uvars.push(id.clone()),
            LevelView::Succ(inner) => levels.push(inner),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                levels.push(b);
                levels.push(a);
            }
            _ => {}
        }
    }
    Ok(result)
}

fn assert_same(actual: &Facts, expected: &Facts) {
    assert_eq!(actual.fvars, expected.fvars);
    assert_eq!(actual.params, expected.params);
    assert_eq!(actual.uvars, expected.uvars);
}

fn tower(depth: usize, mut leaf: Expr) -> Expr {
    let head = Expr::const_(name("head"), vec![]);
    for _ in 0..depth {
        leaf = Expr::app(head.clone(), leaf);
    }
    leaf
}

#[test]
fn closed_ground_metadata_needs_one_visit_not_another_expression_walk() {
    let ground = tower(2_000, Expr::sort(Level::one()));
    let mut limited = meter(&|| false);
    limited.max_steps = 4;
    assert_same(&facts(&ground, &mut limited).unwrap(), &Facts::default());
    assert_eq!((limited.steps, limited.nodes), (1, 1));
    assert_same(
        &facts(&ground, &mut meter(&|| false)).unwrap(),
        &legacy_facts(&ground, &mut meter(&|| false)).unwrap(),
    );
    let mut old = meter(&|| false);
    old.max_steps = 4;
    assert!(matches!(
        legacy_facts(&ground, &mut old),
        Err(UnificationError::StepLimit { limit: 4 })
    ));
}

#[test]
fn open_templates_and_expression_holes_still_pay_their_structural_walk() {
    for leaf in [Expr::bvar(0).unwrap(), Expr::mvar(MVarId(name("pending")))] {
        let root = tower(256, leaf);
        let mut limited = meter(&|| false);
        limited.max_steps = 64;
        assert!(matches!(
            facts(&root, &mut limited),
            Err(UnificationError::StepLimit { limit: 64 })
        ));
        let mut complete = meter(&|| false);
        let actual = facts(&root, &mut complete).unwrap();
        assert!(complete.nodes >= 256);
        assert_same(
            &actual,
            &legacy_facts(&root, &mut meter(&|| false)).unwrap(),
        );
    }
}

#[test]
fn binding_closed_lambdas_skip_only_their_metadata_not_open_bodies() {
    let body = tower(64, Expr::bvar(0).unwrap());
    let lambda = Expr::lam(
        name("x"),
        Expr::sort(Level::one()),
        body.clone(),
        BinderInfo::Default,
    );
    assert!(!lambda.has_loose_bvars());
    let mut closed = meter(&|| false);
    assert_same(&facts(&lambda, &mut closed).unwrap(), &Facts::default());
    assert_eq!(closed.nodes, 1);
    let mut open = meter(&|| false);
    facts(&body, &mut open).unwrap();
    assert!(open.nodes > 64);
}

#[test]
fn metadata_in_annotations_and_universes_is_never_hidden_by_ground_values() {
    let x = Expr::fvar(FVarId(name("x")));
    let u = Expr::sort(Level::param(name("u")));
    let v = Expr::sort(Level::mvar(LMVarId(name("v"))));
    let ground = tower(100, Expr::const_(name("closed"), vec![]));
    let expressions = [
        Expr::lam(name("x"), u.clone(), ground.clone(), BinderInfo::Implicit),
        Expr::forall_e(name("x"), v.clone(), ground.clone(), BinderInfo::Default),
        Expr::let_e(name("x"), u.clone(), x.clone(), ground.clone(), false),
        Expr::let_e(name("x"), v.clone(), ground.clone(), x.clone(), true),
        Expr::mdata(KVMap::new(), Expr::app(x, ground.clone())),
        Expr::proj(name("Record"), 0, Expr::app(u, ground)),
    ];
    for expression in expressions {
        assert_same(
            &facts(&expression, &mut meter(&|| false)).unwrap(),
            &legacy_facts(&expression, &mut meter(&|| false)).unwrap(),
        );
    }
}

#[test]
fn universe_order_and_sharing_match_the_legacy_walk_across_all_node_kinds() {
    let u = Level::param(name("u"));
    let v = Level::param(name("v"));
    let hole = Level::mvar(LMVarId(name("universeHole")));
    let mut nodes = vec![
        Expr::fvar(FVarId(name("x"))),
        Expr::fvar(FVarId(name("y"))),
        Expr::sort(u.clone()),
        Expr::sort(Level::max(v.clone(), hole.clone()).unwrap()),
        Expr::sort(Level::imax(u.clone(), hole.clone()).unwrap()),
        Expr::sort(v.clone().succ().unwrap()),
        Expr::const_(name("C"), vec![hole, v, u]),
        Expr::bvar(0).unwrap(),
        Expr::mvar(MVarId(name("expressionHole"))),
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(7))),
        tower(32, Expr::const_(name("ground"), vec![])),
    ];
    let mut seed = 0x3c79_ac49_2ba7_b653_u64;
    let mut choose = |count: usize| {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        ((seed >> 32) as usize) % count
    };
    for index in 0..512 {
        let a = nodes[choose(nodes.len())].clone();
        let b = nodes[choose(nodes.len())].clone();
        let c = nodes[choose(nodes.len())].clone();
        let expression = match index % 7 {
            0 => Expr::app(a.clone(), a),
            1 => Expr::lam(name("bound"), a, b, BinderInfo::Implicit),
            2 => Expr::forall_e(name("bound"), a, b, BinderInfo::Default),
            3 => Expr::let_e(name("bound"), a, b, c, index % 2 == 0),
            4 => Expr::mdata(KVMap::new(), a),
            5 => Expr::proj(name("Record"), (index % 3) as u64, a),
            _ => Expr::app(a, b),
        };
        assert_same(
            &facts(&expression, &mut meter(&|| false)).unwrap(),
            &legacy_facts(&expression, &mut meter(&|| false)).unwrap(),
        );
        nodes.push(expression);
    }
}

#[test]
fn cancellation_step_and_node_limits_are_checked_before_the_ground_shortcut() {
    let ground = tower(64, Expr::sort(Level::one()));
    assert!(matches!(
        facts(&ground, &mut meter(&|| true)),
        Err(UnificationError::Cancelled)
    ));
    let mut steps = meter(&|| false);
    steps.max_steps = 0;
    assert!(matches!(
        facts(&ground, &mut steps),
        Err(UnificationError::StepLimit { limit: 0 })
    ));
    let mut nodes = meter(&|| false);
    nodes.max_nodes = 0;
    assert!(matches!(
        facts(&ground, &mut nodes),
        Err(UnificationError::NodeLimit { limit: 0 })
    ));
    let mut heartbeats = meter(&|| false);
    heartbeats.max_steps = 0;
    heartbeats.heartbeat_bound = true;
    assert!(matches!(
        facts(&ground, &mut heartbeats),
        Err(UnificationError::HeartbeatLimit)
    ));
    let calls = Cell::new(0);
    let cancel = || {
        let old = calls.get();
        calls.set(old + 1);
        old >= 3
    };
    let open = tower(64, Expr::fvar(FVarId(name("open"))));
    assert!(matches!(
        facts(&open, &mut meter(&cancel)),
        Err(UnificationError::Cancelled)
    ));
    assert_same(
        &facts(&open, &mut meter(&|| false)).unwrap(),
        &legacy_facts(&open, &mut meter(&|| false)).unwrap(),
    );
}
