//! Executable macros retain identifier metadata instead of rewriting or reparsing names.
//! Resolution must use that metadata while preserving the pin's local-name priority.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::source::SourceInferenceError;
use fln_elab::source::scope::SourceScope;
use fln_elab::{NatDefinitionElabError, elaborate_definition_in_scope_with_budget};
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use fln_syntax::tree::{Preresolved, Syntax};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
        panic!("admission nonanswer");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("declaration not accepted");
    };
    let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) = checked
        .publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        )
    else {
        panic!("declaration not published");
    };
    result.environment
}

fn definition(name: &str, type_: Expr, value: Expr, levels: Vec<Name>) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: levels,
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn environment() -> Environment {
    let mut env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    for (name, value) in [("available", 13), ("Client.shadow", 99)] {
        env = publish(
            &env,
            definition(
                name,
                Expr::const_(n("Nat"), vec![]),
                Expr::lit(Literal::Nat(NatLit::from_u64(value))),
                vec![],
            ),
        );
    }
    env
}

fn scope() -> SourceScope {
    SourceScope {
        namespace: n("Client"),
        ..SourceScope::default()
    }
}

fn target(name: &str) -> Vec<Preresolved> {
    vec![Preresolved::Decl {
        name: n(name),
        fields: vec![],
    }]
}

/// Change only the final occurrence, leaving declaration and binder identities intact.
fn annotate(syntax: &mut Syntax, spelling: &Name, metadata: &[Preresolved]) -> bool {
    match syntax {
        Syntax::Ident {
            val, preresolved, ..
        } if val == spelling => {
            *preresolved = metadata.to_vec();
            true
        }
        Syntax::Node { args, .. } => args
            .iter_mut()
            .rev()
            .any(|arg| annotate(arg, spelling, metadata)),
        _ => false,
    }
}

fn parsed(source: &str, spelling: &str, metadata: Vec<Preresolved>) -> Syntax {
    let mut syntax = fln_parse::parse_definition(source.as_bytes())
        .unwrap()
        .syntax()
        .clone();
    assert!(annotate(&mut syntax, &n(spelling), &metadata));
    syntax
}

fn checked(syntax: &Syntax, env: &Environment) -> DefinitionVal {
    let candidate =
        elaborate_definition_in_scope_with_budget(syntax, env, budget(), &scope()).unwrap();
    assert!(matches!(
        check(env, &candidate, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Defn(value) = candidate else {
        panic!("expected a definition")
    };
    value
}

#[test]
fn declaration_metadata_overrides_namespace_spelling_without_reparsing() {
    let syntax = parsed("def chosen : Nat := shadow", "shadow", target("available"));
    assert_eq!(
        checked(&syntax, &environment()).value,
        Expr::const_(n("available"), vec![])
    );
}

#[test]
fn local_spelling_wins_but_a_different_local_cannot_capture_the_exact_target() {
    let env = environment();
    let syntax = parsed(
        "def chosen (shadow : Nat) : Nat := shadow",
        "shadow",
        target("available"),
    );
    let chosen = checked(&syntax, &env);
    let ExprNode::Lam { body, .. } = chosen.value.node() else {
        panic!("expected a lambda");
    };
    assert_eq!(body, &Expr::bvar(0).unwrap());

    let syntax = parsed(
        "def chosen (available : Nat) : Nat := shadow",
        "shadow",
        target("available"),
    );
    let chosen = checked(&syntax, &env);
    let ExprNode::Lam { body, .. } = chosen.value.node() else {
        panic!("expected a lambda");
    };
    assert_eq!(body, &Expr::const_(n("available"), vec![]));
}

#[test]
fn namespace_only_metadata_keeps_ordinary_resolution() {
    let syntax = parsed(
        "def chosen : Nat := shadow",
        "shadow",
        vec![Preresolved::Namespace { ns: n("Unused") }],
    );
    assert_eq!(
        checked(&syntax, &environment()).value,
        Expr::const_(n("Client.shadow"), vec![])
    );
}

#[test]
fn explicit_universes_and_check_queries_use_the_exact_declaration() {
    let u = n("u");
    let domain = Expr::sort(Level::param(u.clone()));
    let env = publish(
        &environment(),
        definition(
            "availableType",
            Expr::forall_e(n("a"), domain.clone(), domain.clone(), BinderInfo::Default),
            Expr::lam(n("a"), domain, Expr::bvar(0).unwrap(), BinderInfo::Default),
            vec![u],
        ),
    );
    let syntax = parsed(
        "def chosen : Type := shadow.{1} Nat",
        "shadow",
        target("availableType"),
    );
    assert_eq!(
        checked(&syntax, &env).value,
        Expr::app(
            Expr::const_(n("availableType"), vec![Level::one()]),
            Expr::const_(n("Nat"), vec![])
        )
    );

    let mut query = fln_parse::parse_source_command(b"#check shadow")
        .unwrap()
        .syntax()
        .clone();
    assert!(annotate(&mut query, &n("shadow"), &target("available")));
    let (candidate, variables) = fln_elab::elaborate_check_in_scope_with_budget(
        &query,
        Name::num(Name::anonymous(), 1),
        &env,
        budget(),
        &scope(),
    )
    .unwrap();
    assert!(variables.is_empty());
    assert!(matches!(
        check(&env, &candidate, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Defn(value) = candidate else {
        panic!("expected a query witness")
    };
    assert_eq!(value.value, Expr::const_(n("available"), vec![]));
}

#[test]
fn unsupported_metadata_is_a_capability_stop_and_never_falls_back_to_spelling() {
    let env = environment();
    let cases = [
        (
            vec![Preresolved::Decl {
                name: n("available"),
                fields: vec!["field".into()],
            }],
            "pre-resolved field projections",
        ),
        (
            vec![
                Preresolved::Decl {
                    name: n("available"),
                    fields: vec![],
                },
                Preresolved::Decl {
                    name: n("Client.shadow"),
                    fields: vec![],
                },
            ],
            "overloaded pre-resolved declarations",
        ),
        (
            target("Unavailable"),
            "an available exact declaration target",
        ),
    ];
    for (metadata, expected) in cases {
        let syntax = parsed("def chosen : Nat := shadow", "shadow", metadata);
        assert!(
            matches!(
                elaborate_definition_in_scope_with_budget(&syntax, &env, budget(), &scope()),
                Err(NatDefinitionElabError::Inference(SourceInferenceError::PreresolvedReference {
                    name, feature
                })) if name == n("shadow") && feature == expected
            ),
            "{expected}"
        );
    }
}

#[test]
fn lazy_equation_discovery_reads_the_metadata_target_absent_from_source_text() {
    let env = environment();
    let syntax = parsed("def chosen := shadow", "shadow", target("available.eq_1"));
    assert_eq!(
        fln_elab::source::equation_theorems::requests(&[&syntax], &env, &scope(), budget())
            .unwrap(),
        vec![fln_elab::source::equation_theorems::Request::Name(n(
            "available.eq_1"
        ))]
    );
}

#[test]
fn specialized_name_only_paths_refuse_metadata_before_dropping_it() {
    let env = environment();
    for source in [
        "def chosen (x : Nat) : Nat := match x with | shadow => x",
        "def chosen : Nat := by exact shadow",
        "def chosen : Nat → Nat | shadow => 13",
    ] {
        let syntax = parsed(source, "shadow", target("available"));
        assert!(
            matches!(
                elaborate_definition_in_scope_with_budget(&syntax, &env, budget(), &scope()),
                Err(NatDefinitionElabError::Inference(SourceInferenceError::PreresolvedReference {
                    name, feature: "pre-resolved identifiers in pattern or tactic syntax"
                })) if name == n("shadow")
            ),
            "{source}"
        );
    }
}
