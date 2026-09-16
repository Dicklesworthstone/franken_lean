//! Source text -> native instance search -> real kernel admission.
//! Fixtures are admitted declarations, not mocked class or unification tables.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::instances::{register_class, register_instance};
use fln_elab::records::{RecordBudget, RecordSpec, record_declarations};
use fln_elab::{LocalContext, check_definition_source};
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}
fn c(value: &str) -> Expr {
    Expr::const_(n(value), vec![])
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let description = format!("{declaration:?}");
    let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
        panic!("fixture admission must answer: {description}");
    };
    let checked = match convene(&Council::nobody_was_asked(), admitted) {
        CouncilOutcome::Agreed(checked) => checked,
        _ => panic!("fixture must be kernel accepted: {description}"),
    };
    match checked.publish(DeclarationBudget::default(), CollisionBudget::default(), None) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("fixture must publish atomically: {other:?}"),
    }
}
fn definition(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}
fn marker(name: &str) -> Declaration {
    let u = n("u");
    let sort = Expr::sort(Level::param(u.clone()));
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![u],
            type_: Expr::forall_e(n("a"), sort.clone(), sort.clone(), BinderInfo::Default),
        },
        value: Expr::lam(n("a"), sort, b(0), BinderInfo::Default),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}
fn record(env: &Environment, name: &str, domains: Vec<Expr>, is_class: bool) -> Environment {
    let mut locals = LocalContext::new();
    let mut parameters = Vec::new();
    for (index, domain) in domains.into_iter().enumerate() {
        let id = FVarId(Name::num(n("_output_fixture"), index as u64));
        parameters.push(
            locals
                .add_param(id, n(&format!("p{index}")), domain, BinderInfo::Default)
                .clone(),
        );
    }
    let spec = RecordSpec {
        name: n(name),
        level_params: vec![],
        parameters,
        fields: vec![],
        result_level: Level::one(),
        is_class,
    };
    let mut env = env.clone();
    for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
        env = publish(&env, declaration);
    }
    if is_class {
        register_class(&env, &n(name)).unwrap()
    } else {
        env
    }
}
fn accepted(source: &str, env: &Environment) -> DefinitionVal {
    let checked = check_definition_source(source.as_bytes(), env, budget())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert!(
        matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}: {:?}",
        checked.outcome
    );
    let Declaration::Defn(value) = checked.declaration else {
        panic!("definition expected");
    };
    for expr in [&value.base.type_, &value.value] {
        assert!(!expr.has_expr_mvar());
        assert!(!expr.has_level_mvar());
        assert!(!expr.has_fvar());
        assert!(!expr.has_loose_bvars());
    }
    value
}
fn source(env: &Environment, text: &str) -> Environment {
    publish(env, Declaration::Defn(accepted(text, env)))
}
fn has_constant(expr: &Expr, name: &str) -> bool {
    let mut work = vec![expr];
    while let Some(expr) = work.pop() {
        match expr.node() {
            ExprNode::Const { name: actual, .. } if actual == &n(name) => return true,
            ExprNode::App { f, a } => work.extend([f, a]),
            ExprNode::Lam { binder_type, body, .. }
            | ExprNode::ForallE { binder_type, body, .. } => work.extend([binder_type, body]),
            ExprNode::MData { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    false
}
fn transfer(output: Expr) -> Expr {
    app(c("Transfer"), [c("Nat"), output])
}
fn fixture(mode: Option<&str>) -> Environment {
    let mut env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    env = publish(&env, marker("outParam"));
    env = publish(&env, marker("semiOutParam"));
    env = record(&env, "Other", vec![], false);
    let sort = Expr::sort(Level::one());
    let output = mode.map_or_else(
        || sort.clone(),
        |mode| {
            Expr::app(
                Expr::const_(
                    n(mode),
                    vec![Level::succ(Level::one()).expect("fixed universe two")],
                ),
                sort.clone(),
            )
        },
    );
    env = record(&env, "Transfer", vec![sort, output], true);
    for (name, output, priority) in [("low", "Other", 500), ("high", "Nat", 2000)] {
        env = publish(
            &env,
            definition(
                name,
                transfer(c(output)),
                app(c("Transfer.mk"), [c("Nat"), c(output)]),
            ),
        );
        env = register_instance(&env, &n(name), priority).unwrap();
    }
    env = source(
        &env,
        "def probe {b : Type} [dict : Transfer Nat b] (dummy : Nat) : Transfer Nat b := dict",
    );
    source(
        &env,
        "def explicitProbe (b : Type) [dict : Transfer Nat b] (dummy : Nat) : Transfer Nat b := dict",
    )
}
fn needs_nat(env: &Environment) -> Environment {
    let mut env = record(env, "Needs", vec![Expr::sort(Level::one())], true);
    env = publish(
        &env,
        definition(
            "needNat",
            Expr::app(c("Needs"), c("Nat")),
            Expr::app(c("Needs.mk"), c("Nat")),
        ),
    );
    register_instance(&env, &n("needNat"), 1000).unwrap()
}

#[test]
fn unknown_output_is_inferred_without_an_expected_result_type() {
    let value = accepted("def inferred := probe 0", &fixture(Some("outParam")));
    assert_eq!(value.base.type_, transfer(c("Nat")));
    assert!(has_constant(&value.value, "high"));
    assert!(!has_constant(&value.value, "low"));
}

#[test]
fn unknown_semi_output_is_also_inferred() {
    let value = accepted("def inferred := probe 0", &fixture(Some("semiOutParam")));
    assert_eq!(value.base.type_, transfer(c("Nat")));
    assert!(has_constant(&value.value, "high"));
}

#[test]
fn ordinary_unknown_parameter_stays_blocked() {
    let env = fixture(None);
    assert!(check_definition_source(b"def stuck := probe 0", &env, budget()).is_err());
    let value = accepted("def explicit := explicitProbe Other 0", &env);
    assert_eq!(value.base.type_, transfer(c("Other")));
    assert!(has_constant(&value.value, "low"));
}

#[test]
fn preexisting_output_cannot_select_a_lower_priority_instance() {
    let env = fixture(Some("outParam"));
    assert!(
        check_definition_source(b"def incompatible := explicitProbe Other 0", &env, budget())
            .is_err(),
        "outParam must not be treated as an input or semi-output"
    );
    // The same immutable environment is still usable after the failed attempt.
    let value = accepted("def compatible := explicitProbe Nat 0", &env);
    assert!(has_constant(&value.value, "high"));
}

#[test]
fn preexisting_semi_output_filters_candidates() {
    let value = accepted(
        "def compatible := explicitProbe Other 0",
        &fixture(Some("semiOutParam")),
    );
    assert_eq!(value.base.type_, transfer(c("Other")));
    assert!(has_constant(&value.value, "low"));
    assert!(!has_constant(&value.value, "high"));
}

#[test]
fn local_instances_still_precede_global_output_candidates() {
    let env = fixture(Some("outParam"));
    let value = accepted(
        "def localWins [local : Transfer Nat Other] : Transfer Nat Other := explicitProbe Other 0",
        &env,
    );
    assert!(!has_constant(&value.value, "high"));
    assert!(!has_constant(&value.value, "low"));
}

#[test]
fn failed_recursive_candidate_does_not_leak_output_assignments() {
    let mut env = fixture(Some("outParam"));
    env = record(&env, "Missing", vec![], true);
    env = publish(
        &env,
        definition(
            "doomed",
            Expr::forall_e(
                n("missing"),
                c("Missing"),
                transfer(c("Other")),
                BinderInfo::InstImplicit,
            ),
            Expr::lam(
                n("missing"),
                c("Missing"),
                app(c("Transfer.mk"), [c("Nat"), c("Other")]),
                BinderInfo::InstImplicit,
            ),
        ),
    );
    env = register_instance(&env, &n("doomed"), 3000).unwrap();
    let value = accepted("def recovered := probe 0", &env);
    assert_eq!(value.base.type_, transfer(c("Nat")));
    assert!(has_constant(&value.value, "high"));
    assert!(!has_constant(&value.value, "doomed"));
}

#[test]
fn later_output_goal_unblocks_an_earlier_independent_goal() {
    let mut env = needs_nat(&fixture(Some("outParam")));
    env = source(
        &env,
        "def combined {b : Type} [need : Needs b] [give : Transfer Nat b] (dummy : Nat) : Needs b := need",
    );
    let value = accepted("def resolved := combined 0", &env);
    assert_eq!(value.base.type_, Expr::app(c("Needs"), c("Nat")));
    assert!(has_constant(&value.value, "needNat"));
    assert!(has_constant(&value.value, "high"));
}

#[test]
fn later_recursive_prerequisite_infers_an_earlier_prerequisites_input() {
    let mut env = needs_nat(&fixture(Some("outParam")));
    env = record(&env, "Root", vec![], true);
    env = source(
        &env,
        "def buildRoot {b : Type} [need : Needs b] [give : Transfer Nat b] : Root := Root.mk",
    );
    env = register_instance(&env, &n("buildRoot"), 1000).unwrap();
    env = source(&env, "def rootProbe [root : Root] (dummy : Nat) : Root := root");
    let value = accepted("def recursive := rootProbe 0", &env);
    assert_eq!(value.base.type_, c("Root"));
    for name in ["buildRoot", "needNat", "high"] {
        assert!(has_constant(&value.value, name), "missing {name}");
    }
}

#[test]
fn an_all_blocked_recursive_candidate_cannot_guess_an_input() {
    let mut env = needs_nat(&fixture(Some("outParam")));
    env = record(&env, "Root", vec![], true);
    env = source(
        &env,
        "def blockedRoot {b : Type} [need : Needs b] : Root := Root.mk",
    );
    env = register_instance(&env, &n("blockedRoot"), 1000).unwrap();
    env = source(&env, "def rootProbe [root : Root] (dummy : Nat) : Root := root");
    assert!(check_definition_source(b"def stuck := rootProbe 0", &env, budget()).is_err());
    assert!(has_constant(&accepted("def stillWorks := probe 0", &env).value, "high"));
}

#[test]
fn recursive_output_cycles_do_not_evade_detection_with_fresh_holes() {
    let mut env = fixture(Some("outParam"));
    env = source(
        &env,
        "def looping {b : Type} [dict : Transfer Nat b] : Transfer Nat b := dict",
    );
    env = register_instance(&env, &n("looping"), 3000).unwrap();
    let value = accepted("def recovered := probe 0", &env);
    assert_eq!(value.base.type_, transfer(c("Nat")));
    assert!(has_constant(&value.value, "high"));
    assert!(!has_constant(&value.value, "looping"));
}
