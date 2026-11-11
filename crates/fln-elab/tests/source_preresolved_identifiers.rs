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
use fln_elab::source::scope::SourceScope;
use fln_elab::source::{SourceInferenceError, trace};
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
    let mut overloaded = target("available");
    overloaded.extend(target("Client.shadow"));
    for metadata in [target("available"), overloaded] {
        let syntax = parsed(
            "def chosen (shadow : Nat) : Nat := shadow",
            "shadow",
            metadata,
        );
        let chosen = checked(&syntax, &env);
        let ExprNode::Lam { body, .. } = chosen.value.node() else {
            panic!("expected a lambda");
        };
        assert_eq!(body, &Expr::bvar(0).unwrap());
    }

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
fn overloaded_metadata_keeps_all_exact_candidates_in_the_pins_order() {
    let env = environment();
    let mut metadata = target("available");
    metadata.extend(target("Client.shadow"));
    metadata.push(Preresolved::Namespace { ns: n("Ignored") });
    let syntax = parsed("def chosen : Nat := shadow", "shadow", metadata);
    let result = elaborate_definition_in_scope_with_budget(&syntax, &env, budget(), &scope());
    assert!(
        matches!(result,
            Err(NatDefinitionElabError::Inference(SourceInferenceError::AmbiguousTerm {
                name, interpretations,
            })) if name == n("shadow")
                && interpretations == vec![n("Client.shadow"), n("available")]),
        "Term.mkConsts reverses the declaration metadata before trying each candidate"
    );
}

#[test]
fn overloaded_metadata_keeps_imported_private_identities_out_of_textual_resolution() {
    let private = Name::num(n("_private.Library"), 0).append_core(&n("choice"));
    let mut declaration = definition(
        "choice",
        Expr::const_(n("Nat"), vec![]),
        Expr::lit(Literal::Nat(NatLit::from_u64(7))),
        vec![],
    );
    let Declaration::Defn(value) = &mut declaration else {
        unreachable!();
    };
    value.base.name = private.clone();
    value.all = vec![private.clone()];
    let env = publish(&environment(), declaration);
    let mut metadata = target("available");
    metadata.push(Preresolved::Decl {
        name: private.clone(),
        fields: Vec::new(),
    });
    let syntax = parsed("def chosen : Nat := shadow", "shadow", metadata);
    let result = elaborate_definition_in_scope_with_budget(&syntax, &env, budget(), &scope());
    assert!(
        matches!(&result,
            Err(NatDefinitionElabError::Inference(SourceInferenceError::AmbiguousTerm {
                interpretations, ..
            })) if interpretations == &vec![private, n("available")]),
        "captured internal names resolve by identity, not by source components: {result:?}"
    );
}

#[test]
fn overloaded_metadata_is_used_for_whole_applications_and_explicit_universes() {
    let u = n("u");
    let domain = Expr::sort(Level::param(u.clone()));
    let mut env = environment();
    for name in ["First.identity", "Second.identity"] {
        env = publish(
            &env,
            definition(
                name,
                Expr::forall_e(n("a"), domain.clone(), domain.clone(), BinderInfo::Default),
                Expr::lam(
                    n("a"),
                    domain.clone(),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                vec![u.clone()],
            ),
        );
    }
    let mut metadata = target("First.identity");
    metadata.extend(target("Second.identity"));
    for source in [
        "def chosen : Type := shadow Nat",
        "def chosen : Type := shadow.{1} Nat",
        "def chosen : Type := @shadow.{1} Nat",
        "def chosen : Type → Type := @shadow.{1}",
    ] {
        let syntax = parsed(source, "shadow", metadata.clone());
        let result = elaborate_definition_in_scope_with_budget(&syntax, &env, budget(), &scope());
        assert!(
            matches!(&result,
                Err(NatDefinitionElabError::Inference(SourceInferenceError::AmbiguousTerm {
                    name, interpretations,
                })) if name == &n("shadow")
                    && interpretations == &vec![n("Second.identity"), n("First.identity")]),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn every_preresolved_candidate_is_validated_before_overload_trials() {
    let env = environment();
    for (invalid, feature) in [
        (
            target("Unavailable"),
            "an available exact declaration target",
        ),
        (
            vec![Preresolved::Decl {
                name: n("Client.shadow"),
                fields: vec!["field".into()],
            }],
            "pre-resolved field projections",
        ),
    ] {
        for invalid_first in [false, true] {
            let mut metadata = target("available");
            if invalid_first {
                metadata.splice(0..0, invalid.clone());
            } else {
                metadata.extend(invalid.clone());
            }
            let syntax = parsed("def chosen : Nat := shadow", "shadow", metadata);
            assert!(
                matches!(
                    elaborate_definition_in_scope_with_budget(&syntax, &env, budget(), &scope()),
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::PreresolvedReference {
                        name, feature: actual,
                    })) if name == n("shadow") && actual == feature
                ),
                "invalid candidate must not disappear: {feature}, first={invalid_first}"
            );
        }
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
fn exact_and_apply_tactic_terms_preserve_declaration_metadata_and_local_priority() {
    let env = environment();
    for tactic in ["exact", "apply"] {
        let syntax = parsed(
            &format!("def chosen : Nat := by {tactic} shadow"),
            "shadow",
            target("available"),
        );
        // `available` is 13, whereas spelling-only resolution in this scope
        // would choose `Client.shadow`, whose value is 99. Both tactics send
        // their complete operand through the ordinary identifier resolver.
        assert_eq!(
            checked(&syntax, &env).value,
            Expr::const_(n("available"), vec![]),
            "{tactic} must use the pre-resolved declaration, not its spelling"
        );

        // The same metadata still cannot capture a use-site local, and an
        // unavailable exact declaration is never replaced with namespace lookup.
        let local = parsed(
            &format!("def chosen (shadow : Nat) : Nat := by {tactic} shadow"),
            "shadow",
            target("available"),
        );
        let checked_local = checked(&local, &env);
        assert!(
            matches!(checked_local.value.node(), ExprNode::Lam { body, .. } if body == &Expr::bvar(0).unwrap())
        );
        let missing = parsed(
            &format!("def chosen : Nat := by {tactic} shadow"),
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
}

/// Deferred literal macros can introduce identifiers after the declaration's
/// initial metadata scan. Exercise that real provider boundary rather than
/// annotating the original source tree, which the earlier tests already cover.
struct PatternProvider {
    replacements: Vec<Syntax>,
    rewrite_list_cons: bool,
    literal_expansions: AtomicU64,
    constructor_expansions: AtomicU64,
}

impl PatternProvider {
    fn new(replacement: Syntax, rewrite_list_cons: bool) -> Arc<Self> {
        Self::with_replacements(vec![replacement], rewrite_list_cons)
    }

    fn with_replacements(replacements: Vec<Syntax>, rewrite_list_cons: bool) -> Arc<Self> {
        assert!(!replacements.is_empty());
        Arc::new(Self {
            replacements,
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
            let index = self.literal_expansions.fetch_add(1, Ordering::Relaxed) as usize;
            let replacement = self
                .replacements
                .get(index)
                .or(self.replacements.last())
                .expect("at least one replacement");
            return Ok(Some(replacement.clone()));
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
fn equation_capture_retains_each_stateful_pattern_occurrence() {
    let env = pattern_environment();
    let provider = PatternProvider::with_replacements(
        vec![
            pattern_identifier("_root_.Nat.zero", target("Nat.zero")),
            Syntax::node(n("num"), vec![Syntax::atom(SourceInfo::None, "1")]),
        ],
        false,
    );
    let source = "def chosen (x y : Nat) : Nat := match x, y with | 37, 37 => 13 | _, _ => 99";
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let actual_scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider.clone())),
        ..scope()
    };
    let actual = trace::elaborate_definition(parsed.syntax(), &env, budget(), &actual_scope)
        .unwrap()
        .candidate;
    assert_eq!(provider.literal_expansions.load(Ordering::Relaxed), 2);
    let written = fln_parse::parse_definition(
        b"def chosen (x y : Nat) : Nat := match x, y with | Nat.zero, 1 => 13 | _, _ => 99",
    )
    .unwrap();
    let expected = trace::elaborate_definition(written.syntax(), &env, budget(), &scope())
        .unwrap()
        .candidate;
    let actual_record = actual
        .equation_info
        .as_ref()
        .expect("prepared equation rows");
    let expected_record = expected
        .equation_info
        .as_ref()
        .expect("written equation rows");
    assert_eq!(actual_record, expected_record);
    let checked_env = publish(&env, actual.declaration);
    check_pattern_result(
        &checked_env,
        "theorem orderedHit : Eq (chosen Nat.zero 1) 13 := Eq.refl 13",
    );
    check_pattern_result(
        &checked_env,
        "theorem distinctMiss : Eq (chosen Nat.zero Nat.zero) 99 := Eq.refl 99",
    );
    check_pattern_result(
        &checked_env,
        "theorem originalMiss : Eq (chosen 37 37) 99 := Eq.refl 99",
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
