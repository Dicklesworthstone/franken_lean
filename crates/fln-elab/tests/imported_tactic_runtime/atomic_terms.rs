//! Actual quoted templates at the production term/pattern provider boundary.
//! Artifact admission and shared VM limits are exercised by fln's batch tests.
use super::*;
use fln_core::{
    expr::{BinderInfo, Expr, FVarId},
    level::Level,
};
use fln_elab::{
    LocalContext,
    records::{RecordBudget, RecordSpec, record_declarations},
};
use fln_parse::extensions::{FileGrammar, NotationRule, with_grammar};
use std::collections::BTreeMap;

struct Templates {
    rules: Arc<BTreeMap<Name, Arc<NotationRule>>>,
    scopes: AtomicU64,
    calls: AtomicU64,
    depths: Mutex<Vec<(String, usize)>>,
}

impl Templates {
    fn new(commands: &[&str]) -> Arc<Self> {
        Self::with_parser(commands).0
    }

    fn with_parser(
        commands: &[&str],
    ) -> (Arc<Self>, std::rc::Rc<fln_parse::extensions::ActiveGrammar>) {
        let mut grammar =
            FileGrammar::new(false, &[], Some(Name::from_components(["Main"]))).unwrap();
        for source in commands {
            let parsed = with_grammar(&grammar.grammar(), || {
                fln_parse::parse_source_command(source.as_bytes())
            })
            .unwrap();
            grammar.declare(parsed.syntax()).unwrap();
            // The source driver gives quoted identifiers their definition-site
            // backing before a later command supplies the invocation source.
            let unbacked: Vec<_> = grammar
                .rules()
                .flat_map(|(kind, rule)| {
                    rule.cases().enumerate().filter_map(move |(index, case)| {
                        case.source
                            .is_none()
                            .then(|| (kind.clone(), index, case.rhs.clone()))
                    })
                })
                .collect();
            for (kind, index, rhs) in unbacked {
                assert!(grammar.set_rule_template(&kind, index, rhs, Arc::from(source.as_bytes())));
            }
        }
        (
            Arc::new(Self {
                rules: grammar.active_template_rules(),
                scopes: AtomicU64::new(100),
                calls: AtomicU64::new(0),
                depths: Mutex::new(Vec::new()),
            }),
            grammar.grammar(),
        )
    }
}

impl TacticMacroExpander for Templates {
    fn contains(&self, kind: &Name) -> bool {
        self.rules.contains_key(kind)
    }

    fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
        Ok(self.scopes.fetch_add(1, Ordering::Relaxed))
    }

    fn expand_tactic(
        &self,
        syntax: &Syntax,
        candidate: usize,
        macro_scope: u64,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        if candidate != 0 {
            return Ok(TacticMacroExpansion::Exhausted);
        }
        let Some(rule) = syntax.kind().and_then(|kind| self.rules.get(kind)) else {
            return Ok(TacticMacroExpansion::Exhausted);
        };
        match rule
            .expand_root(
                syntax,
                &Name::from_components(["Main"]),
                macro_scope,
                syntax.info(),
            )
            .map_err(|error| TacticMacroError::Unsupported(format!("{error:?}")))?
        {
            Some(syntax) => Ok(TacticMacroExpansion::Expanded {
                syntax,
                no_fallback: false,
            }),
            None => Ok(TacticMacroExpansion::Unsupported),
        }
    }

    fn expand_term(
        &self,
        syntax: &Syntax,
        depth: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        let kind = match syntax {
            Syntax::Node { kind, .. } => kind.clone(),
            Syntax::Ident { .. } => Name::from_components(["ident"]),
            _ => return Ok(None),
        };
        let Some(rule) = self.rules.get(&kind) else {
            return Ok(None);
        };
        if let Syntax::Node { args, .. } = syntax
            && let [Syntax::Atom { val, .. }] = args.as_slice()
        {
            self.depths.lock().unwrap().push((val.clone(), depth));
        }
        if self.calls.fetch_add(1, Ordering::Relaxed) >= 256 {
            return Err(TacticMacroError::Inconclusive(Box::new(
                Inconclusive::dependency_unavailable("test template attempt bound"),
            )));
        }
        rule.expand_root(
            syntax,
            &Name::from_components(["Main"]),
            self.scopes.fetch_add(1, Ordering::Relaxed),
            syntax.info(),
        )
        .map_err(|error| TacticMacroError::Unsupported(format!("{error:?}")))
    }
}

fn checked(source: &str, provider: Arc<Templates>) -> Result<Declaration, NatDefinitionElabError> {
    let mut environment = environment();
    let mut locals = LocalContext::new();
    let fields = ["fst", "snd"]
        .into_iter()
        .map(|name| {
            locals
                .add_param(
                    FVarId(Name::from_components(["_atomic_pair", name])),
                    Name::from_components([name]),
                    Expr::const_(Name::from_components(["Nat"]), vec![]),
                    BinderInfo::Default,
                )
                .clone()
        })
        .collect();
    let spec = RecordSpec {
        name: Name::from_components(["AtomicPair"]),
        level_params: vec![],
        parameters: vec![],
        fields,
        result_level: Level::one(),
        is_class: false,
    };
    for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
        environment = publish(&environment, declaration);
    }
    checked_in(source, provider, &environment)
}

fn publish(environment: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
        panic!("fixture admission did not answer")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture was refused")
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        other => panic!("fixture publication: {other:?}"),
    }
}

fn checked_in(
    source: &str,
    provider: Arc<Templates>,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    let parsed = fln_parse::parse_definition(source.as_bytes())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    checked_syntax_in(source, parsed.syntax(), provider, environment)
}

fn checked_syntax_in(
    source: &str,
    syntax: &Syntax,
    provider: Arc<Templates>,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider)),
        ..SourceScope::default()
    };
    let declaration =
        elaborate_definition_in_scope_with_budget(syntax, environment, budget(), &scope)?;
    assert!(
        matches!(
            fln_kernel::check(environment, &declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ),
        "{source}: {declaration:?}"
    );
    Ok(declaration)
}

#[test]
fn atomic_literals_expand_in_terms_types_and_tactics_but_preserve_raw_indices() {
    let rules = [
        "macro_rules | `(1) => `(11)",
        "macro_rules | `(\"source\") => `(23)",
        "macro_rules | `('a') => `(29)",
        "macro_rules | `(1.5) => `(31)",
    ];
    for source in [
        "theorem number : Eq (1 : Nat) 11 := Eq.refl 11",
        "def universeType : Sort 1 := Nat",
        "theorem projection : Eq ((AtomicPair.mk (Nat.succ Nat.zero) Nat.zero).1) (Nat.succ Nat.zero) := Eq.refl (Nat.succ Nat.zero)",
        "theorem tactic : Eq (1 : Nat) 11 := by exact Eq.refl 1",
        "theorem string : Eq (\"source\" : Nat) 23 := Eq.refl 23",
        "theorem character : Eq ('a' : Nat) 29 := Eq.refl 29",
        "theorem scientific : Eq (1.5 : Nat) 31 := Eq.refl 31",
    ] {
        checked(source, Templates::new(&rules))
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
}

#[test]
fn atomic_identifiers_preserve_binders_and_application_head_fast_paths() {
    let rules = [
        "macro_rules | `(magic) => `(7)",
        "macro_rules | `(fst) => `(7)",
        "macro_rules | `(functionMacroTarget) => `(fun (_ : Nat) => 7)",
    ];
    for source in [
        "theorem binder (magic : Nat) : Eq magic 7 := Eq.refl 7",
        "theorem direct : Eq (let functionMacroTarget := fun (x : Nat) => x; functionMacroTarget 3) 3 := Eq.refl 3",
        "theorem parenthesized : Eq (let functionMacroTarget := fun (x : Nat) => x; (functionMacroTarget) 3) 7 := Eq.refl 7",
        "theorem explicit : Eq (let functionMacroTarget := fun (x : Nat) => x; @functionMacroTarget 3) 3 := Eq.refl 3",
        "theorem patternBinder (n : Nat) : Eq (match n with | magic => magic) 7 := Eq.refl 7",
        "theorem punned (fst : Nat) : Eq (({ fst, snd := 3 } : AtomicPair).fst) 7 := Eq.refl 7",
        "theorem fieldLabel : Eq (({ fst := 3, snd := 4 } : AtomicPair).fst) 3 := Eq.refl 3",
    ] {
        checked(source, Templates::new(&rules))
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
}

#[test]
fn atomic_literal_patterns_expand_before_matrix_decisions() {
    let rules = ["macro_rules | `(1) => `(11)"];
    for source in [
        "theorem pattern : Eq (match (11 : Nat) with | 1 => 42 | _ => 0) 42 := Eq.refl 42",
        "theorem nested : Eq (match (Nat.succ 11) with | Nat.succ 1 => 42 | _ => 0) 42 := Eq.refl 42",
        "theorem ifPattern : Eq (if let 1 := (11 : Nat) then 42 else 0) 42 := Eq.refl 42",
    ] {
        checked(source, Templates::new(&rules))
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
    let provider = Templates::new(&["macro_rules | `(0x0) => `(99)"]);
    let environment = environment();
    let declaration = checked_in(
        "def choose (n : Nat) : Nat := match n with | 1 => 7 | Nat.succ _ => 8 | Nat.zero => 9",
        provider.clone(),
        &environment,
    )
    .unwrap();
    assert!(
        provider
            .depths
            .lock()
            .unwrap()
            .iter()
            .all(|(spelling, _)| spelling != "0x0"),
        "the compiler's compact predecessor must not reenter source macros"
    );
    let environment = publish(&environment, declaration);
    checked_in(
        "theorem preservedPredecessor : Eq (choose (Nat.succ Nat.zero)) 7 := Eq.refl 7",
        Templates::new(&[]),
        &environment,
    )
    .unwrap();
}

#[test]
fn atomic_literal_pattern_chains_advance_the_provider_recursion_depth() {
    let provider = Templates::new(&["macro_rules | `(1) => `(2)", "macro_rules | `(2) => `(11)"]);
    checked(
        "def patternDepth (n : Nat) : Nat := match n with | 1 => 7 | _ => 0",
        provider.clone(),
    )
    .unwrap();
    assert!(provider.depths.lock().unwrap().starts_with(&[
        ("1".into(), 0),
        ("2".into(), 1),
        ("11".into(), 2),
    ]));
    {
        let depths = provider.depths.lock().unwrap();
        let count = |literal| {
            depths
                .iter()
                .filter(|(spelling, _)| spelling == literal)
                .count()
        };
        // Equation-info capture can elaborate the original source pattern
        // again. Each source expansion chain has its own terminal lookup; the
        // generated comparison must not add a lookup of that terminal value.
        assert_eq!(count("11"), count("1"));
    }
    let provider = Templates::new(&[
        "macro_rules | `(outerTerm) => `(match (11 : Nat) with | 1 => 7 | _ => 0)",
        "macro_rules | `(1) => `(2)",
        "macro_rules | `(2) => `(11)",
    ]);
    checked(
        "def generatedPatternDepth : Nat := outerTerm",
        provider.clone(),
    )
    .unwrap();
    assert!(provider.depths.lock().unwrap().starts_with(&[
        ("1".into(), 1),
        ("2".into(), 2),
        ("11".into(), 3),
    ]));
    let (provider, grammar) = Templates::with_parser(&[
        "syntax \"atomicSkip\" : tactic",
        "macro_rules | `(tactic| atomicSkip) => `(tactic| exact (match (11 : Nat) with | 1 => 7 | _ => 0))",
        "macro_rules | `(1) => `(2)",
        "macro_rules | `(2) => `(11)",
    ]);
    let source = "def generatedTacticPatternDepth : Nat := by atomicSkip";
    let parsed = with_grammar(&grammar, || fln_parse::parse_definition(source.as_bytes())).unwrap();
    checked_syntax_in(source, parsed.syntax(), provider.clone(), &environment()).unwrap();
    assert!(provider.depths.lock().unwrap().starts_with(&[
        ("1".into(), 1),
        ("2".into(), 2),
        ("11".into(), 3),
    ]));
}

fn indexed_environment() -> Environment {
    use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
    let environment = environment();
    let mut locals = LocalContext::new();
    let mut local = |label| {
        locals
            .add_param(
                FVarId(Name::from_components(["_atomic_indexed", label])),
                Name::from_components([label]),
                Expr::const_(Name::from_components(["Nat"]), vec![]),
                BinderInfo::Default,
            )
            .clone()
    };
    let index = local("index");
    let field = local("value");
    let spec = InductiveSpec {
        name: Name::from_components(["Indexed"]),
        level_params: vec![],
        parameters: vec![],
        indices: vec![index],
        constructors: vec![ConstructorSpec {
            name: Name::from_components(["mk"]),
            result_indices: vec![Expr::fvar(field.id.clone())],
            fields: vec![field],
        }],
        result_level: Level::one(),
    };
    publish(
        &environment,
        inductive_declaration(&spec, RecordBudget::default()).unwrap(),
    )
}

#[test]
fn expanded_literal_patterns_reach_dependent_index_typing_checks() {
    let environment = indexed_environment();
    let declaration = checked_in(
        "def indexedPattern (n : Nat) (x : Indexed n) : Nat := match n, x with | 1, Indexed.mk 11 => 42 | _, Indexed.mk _ => 0",
        Templates::new(&["macro_rules | `(1) => `(11)"]),
        &environment,
    ).unwrap();
    let environment = publish(&environment, declaration);
    for source in [
        "theorem indexedHit : Eq (indexedPattern 11 (Indexed.mk 11)) 42 := Eq.refl 42",
        "theorem indexedMiss : Eq (indexedPattern 3 (Indexed.mk 3)) 0 := Eq.refl 0",
    ] {
        checked_in(source, Templates::new(&[]), &environment)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
}

#[test]
fn atomic_pattern_shape_changes_and_loops_never_use_the_original_literal() {
    let error = checked(
        "def pattern (n : Nat) : Nat := match n with | 1 => 7 | _ => 0",
        Templates::new(&["macro_rules | `(1) => `(Nat.succ Nat.zero)"]),
    )
    .unwrap_err();
    assert!(matches!(error,
        NatDefinitionElabError::Inference(SourceInferenceError::TacticMacro(TacticMacroError::Unsupported(message)))
            if message.contains("nonliteral patterns")));
    for source in [
        "def termLoop : Nat := 1",
        "def patternLoop (n : Nat) : Nat := match n with | 1 => 7 | _ => 0",
    ] {
        let error = checked(source, Templates::new(&["macro_rules | `(1) => `(1)"])).unwrap_err();
        assert!(matches!(
            error,
            NatDefinitionElabError::Inference(SourceInferenceError::TacticMacro(
                TacticMacroError::Inconclusive(_)
            ))
        ));
    }
}
