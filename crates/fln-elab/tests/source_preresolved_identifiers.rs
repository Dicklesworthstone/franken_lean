//! Executable macros retain identifier metadata instead of rewriting or reparsing names.
//! Resolution must use that metadata while preserving the pin's local-name priority.
#![forbid(unsafe_code)]
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::source::SourceInferenceError;
use fln_elab::source::scope::SourceScope;
use fln_elab::tactic_macros::{
    TacticMacroError, TacticMacroExpander, TacticMacroExpansion, TacticMacroProvider,
};
use fln_elab::{NatDefinitionElabError, elaborate_definition_in_scope_with_budget};
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use fln_syntax::source::{ByteSpan, SourceInfo};
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
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("declaration not published: {other:?}"),
    }
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
        "def chosen : Nat := by apply shadow",
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

#[test]
fn exact_tactic_terms_preserve_declaration_metadata_and_local_priority() {
    let env = environment();
    let syntax = parsed(
        "def chosen : Nat := by exact shadow",
        "shadow",
        target("available"),
    );
    assert_eq!(
        checked(&syntax, &env).value,
        Expr::const_(n("available"), vec![])
    );

    // The same metadata still cannot capture a use-site local, and an
    // unavailable exact declaration is never replaced with namespace lookup.
    let local = parsed(
        "def chosen (shadow : Nat) : Nat := by exact shadow",
        "shadow",
        target("available"),
    );
    let checked_local = checked(&local, &env);
    assert!(
        matches!(checked_local.value.node(), ExprNode::Lam { body, .. } if body == &Expr::bvar(0).unwrap())
    );
    let missing = parsed(
        "def chosen : Nat := by exact shadow",
        "shadow",
        target("Unavailable"),
    );
    assert!(matches!(
        elaborate_definition_in_scope_with_budget(&missing, &env, budget(), &scope()),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::PreresolvedReference {
                feature: "an available exact declaration target",
                ..
            }
        ))
    ));
}

/// Deferred literal macros can introduce identifiers after the declaration's
/// initial metadata scan. Exercise that real provider boundary rather than
/// annotating the original source tree, which the earlier tests already cover.
struct PatternProvider {
    replacement: Syntax,
    rewrite_list_cons: bool,
    literal_expansions: AtomicU64,
    constructor_expansions: AtomicU64,
}

impl PatternProvider {
    fn new(replacement: Syntax, rewrite_list_cons: bool) -> Arc<Self> {
        Arc::new(Self {
            replacement,
            rewrite_list_cons,
            literal_expansions: AtomicU64::new(0),
            constructor_expansions: AtomicU64::new(0),
        })
    }
}

impl TacticMacroExpander for PatternProvider {
    fn contains(&self, kind: &Name) -> bool {
        *kind == n("num") || (self.rewrite_list_cons && *kind == n("Lean.Parser.Term.app"))
    }

    fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
        Ok(0)
    }

    fn expand_tactic(
        &self,
        _: &Syntax,
        _: usize,
        _: u64,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        Ok(TacticMacroExpansion::Exhausted)
    }

    fn expand_term(
        &self,
        syntax: &Syntax,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        if *kind == n("num") && matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "37")
        {
            self.literal_expansions.fetch_add(1, Ordering::Relaxed);
            return Ok(Some(self.replacement.clone()));
        }
        if self.rewrite_list_cons
            && *kind == n("Lean.Parser.Term.app")
            && matches!(args.first(), Some(Syntax::Ident { val, .. })
                if val.erase_macro_scopes() == n("_root_.List.cons"))
        {
            self.constructor_expansions.fetch_add(1, Ordering::Relaxed);
            return Ok(Some(pattern_identifier("_root_.List.nil", Vec::new())));
        }
        Ok(None)
    }
}

fn pattern_identifier(spelling: &str, metadata: Vec<Preresolved>) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default().into(),
        val: n(spelling),
        preresolved: metadata,
    }
}

fn pattern_environment() -> Environment {
    let mut env = Environment::new();
    for declaration in fln_elab::seed::source_seed_declarations() {
        env = publish(&env, declaration);
    }
    env
}

fn elaborate_pattern(
    source: &str,
    env: &Environment,
    provider: Arc<PatternProvider>,
) -> Result<Declaration, NatDefinitionElabError> {
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider)),
        ..scope()
    };
    elaborate_definition_in_scope_with_budget(parsed.syntax(), env, budget(), &scope)
}

fn check_pattern_result(env: &Environment, source: &str) {
    let syntax = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let declaration =
        elaborate_definition_in_scope_with_budget(syntax.syntax(), env, budget(), &scope())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert!(
        matches!(
            check(env, &declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ),
        "{source}: {declaration:?}"
    );
}

#[test]
fn generated_pattern_metadata_cannot_silently_fall_back_to_constructor_spelling() {
    let env = pattern_environment();
    let source = "def chosen (x : Nat) : Nat := match x with | 37 => 13 | _ => 99";
    for spelling in ["Nat.zero", "_root_.Nat.zero"] {
        let provider =
            PatternProvider::new(pattern_identifier(spelling, target("Nat.succ")), false);
        let result = elaborate_pattern(source, &env, Arc::clone(&provider));
        assert!(
            matches!(&result,
                Err(NatDefinitionElabError::Inference(SourceInferenceError::PreresolvedReference {
                    name, feature: "pre-resolved identifiers in pattern or tactic syntax"
                })) if *name == n(spelling)),
            "{spelling}: {result:?}"
        );
        assert_eq!(provider.literal_expansions.load(Ordering::Relaxed), 1);
    }
}

#[test]
fn generated_pattern_metadata_accepts_a_matching_anchored_constructor_once() {
    let env = pattern_environment();
    let provider = PatternProvider::new(
        pattern_identifier("_root_.Nat.zero", target("Nat.zero")),
        false,
    );
    let declaration = elaborate_pattern(
        "def chosen (x : Nat) : Nat := match x with | 37 => 13 | _ => 99",
        &env,
        Arc::clone(&provider),
    )
    .unwrap();
    let checked_env = publish(&env, declaration);
    assert_eq!(provider.literal_expansions.load(Ordering::Relaxed), 1);
    check_pattern_result(
        &checked_env,
        "theorem hit : Eq (chosen Nat.zero) 13 := Eq.refl 13",
    );
    check_pattern_result(
        &checked_env,
        "theorem miss : Eq (chosen (Nat.succ Nat.zero)) 99 := Eq.refl 99",
    );
}

#[test]
fn generated_collection_patterns_dispatch_the_lowered_constructor_root() {
    let env = pattern_environment();
    let template = fln_parse::parse_definition(b"def replacement := [Nat.zero]").unwrap();
    let mut pending = vec![template.syntax()];
    let list = loop {
        let node = pending.pop().expect("parsed list notation");
        if node.kind() == Some(&n("term[_]")) {
            break node.clone();
        }
        if let Syntax::Node { args, .. } = node {
            pending.extend(args.iter().rev());
        }
    };
    let provider = PatternProvider::new(list, true);
    let declaration = elaborate_pattern(
        "def chosen (xs : List Nat) : Nat := match xs with | 37 => 13 | _ => 99",
        &env,
        Arc::clone(&provider),
    )
    .unwrap();
    let checked_env = publish(&env, declaration);
    // The replacement is a singleton, so its only cons is the lowering's
    // root. Visiting only the root's children cannot satisfy this control.
    assert_eq!(provider.literal_expansions.load(Ordering::Relaxed), 1);
    assert_eq!(provider.constructor_expansions.load(Ordering::Relaxed), 1);
    check_pattern_result(
        &checked_env,
        "theorem emptyHit : Eq (chosen []) 13 := Eq.refl 13",
    );
    check_pattern_result(
        &checked_env,
        "theorem singletonMiss : Eq (chosen [Nat.zero]) 99 := Eq.refl 99",
    );
}
