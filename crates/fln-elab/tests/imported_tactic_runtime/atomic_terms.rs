//! Actual quoted templates at the production term/pattern provider boundary.
//! Artifact admission and shared VM limits are exercised by fln's batch tests.
#![forbid(unsafe_code)]
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
use fln_syntax::{
    source::{BytePos, ByteSpan},
    tree::{Preresolved, RawIdentifier},
};
use std::collections::BTreeMap;

struct Templates {
    rules: Arc<BTreeMap<Name, Arc<NotationRule>>>,
    scopes: AtomicU64,
    calls: AtomicU64,
    depths: Mutex<Vec<(String, usize)>>,
    expansions: Mutex<Vec<String>>,
}

impl Templates {
    fn new(commands: &[&str]) -> Arc<Self> {
        Self::with_parser(commands).0
    }

    fn with_parser(
        commands: &[&str],
    ) -> (Arc<Self>, std::rc::Rc<fln_parse::extensions::ActiveGrammar>) {
        Self::with_runtime_parser(commands, &[])
    }

    fn with_runtime_parser(
        commands: &[&str],
        kinds: &[Name],
    ) -> (Arc<Self>, std::rc::Rc<fln_parse::extensions::ActiveGrammar>) {
        let mut grammar =
            FileGrammar::new(false, &[], Some(Name::from_components(["Main"]))).unwrap();
        grammar.bind_runtime_macros(kinds.iter().cloned(), [], []);
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
                    rule.cases()
                        .enumerate()
                        .filter(|(_, case)| case.source.is_none())
                        .map(move |(index, case)| (kind.clone(), index, case.rhs.clone()))
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
                expansions: Mutex::new(Vec::new()),
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
        let expanded = rule
            .expand_root(
                syntax,
                &Name::from_components(["Main"]),
                self.scopes.fetch_add(1, Ordering::Relaxed),
                syntax.info(),
            )
            .map_err(|error| TacticMacroError::Unsupported(format!("{error:?}")))?;
        if expanded.is_some() {
            let input = match syntax {
                Syntax::Ident { val, .. } => val.erase_macro_scopes().to_display_string(),
                Syntax::Node { kind, args, .. } => match args.as_slice() {
                    [Syntax::Atom { val, .. }] => val.clone(),
                    _ => kind.to_display_string(),
                },
                _ => unreachable!("term provider selects only node or identifier rules"),
            };
            self.expansions.lock().unwrap().push(input);
        }
        Ok(expanded)
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

fn quoted_identifier(spelling: &str, preresolved: Vec<Preresolved>) -> Syntax {
    let constant = Name::from_components(spelling.split('.'));
    let val = fln_core::name::hygiene::add_macro_scope(
        &Name::from_components(["Definition", "Site"]),
        &constant,
        37,
    )
    .unwrap();
    assert!(val.has_macro_scopes());
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: RawIdentifier::owned(
            Arc::from(spelling),
            ByteSpan::new(BytePos(0), BytePos(spelling.len())).unwrap(),
        )
        .unwrap(),
        val,
        preresolved,
    }
}

fn declaration_reference(declaration: &str) -> Preresolved {
    Preresolved::Decl {
        name: Name::from_components(declaration.split('.')),
        fields: Vec::new(),
    }
}

fn quoted_apply(spelling: &str, preresolved: Vec<Preresolved>) -> Syntax {
    Syntax::Node {
        info: SourceInfo::None,
        kind: Name::from_components(["Lean", "Parser", "Tactic", "apply"]),
        args: vec![
            Syntax::Atom {
                info: SourceInfo::None,
                val: "apply".to_owned(),
            },
            quoted_identifier(spelling, preresolved),
        ],
    }
}

#[test]
fn generated_apply_resolves_hygienic_constructor_prereferences_as_terms() {
    for (constructor, source) in [
        ("True.intro", "theorem quotedTrue : True := by skip"),
        (
            "And.intro",
            "theorem quotedAnd (P Q : Prop) (hp : P) (hq : Q) : And P Q := by skip; assumption; assumption",
        ),
    ] {
        let provider = Provider::new(vec![Candidate::Expansion(quoted_apply(
            constructor,
            vec![declaration_reference(constructor)],
        ))]);
        // The parent helper checks every closed declaration with the kernel.
        super::elaborate(source, provider.clone())
            .unwrap_or_else(|error| panic!("{constructor}: {error:?}"));
        assert_eq!(provider.calls.lock().unwrap().len(), 1);
    }
    let provider = Provider::new(vec![Candidate::Expansion(quoted_apply(
        "True.intro",
        vec![declaration_reference("True.intro")],
    ))]);
    assert!(matches!(
        super::elaborate("theorem falseConstructor : False := by skip", provider),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::Tactic(fln_elab::source::TacticError::ApplyMismatch)
        ))
    ));
}

#[test]
fn generated_apply_rejects_unavailable_overloaded_and_field_prereferences() {
    for (references, expected) in [
        (
            vec![declaration_reference("Missing.constructor")],
            "an available exact declaration target",
        ),
        (
            vec![
                declaration_reference("True.intro"),
                declaration_reference("And.intro"),
            ],
            "overloaded pre-resolved declarations",
        ),
        (
            vec![Preresolved::Decl {
                name: Name::from_components(["True", "intro"]),
                fields: vec!["field".to_owned()],
            }],
            "pre-resolved field projections",
        ),
    ] {
        let provider = Provider::new(vec![Candidate::Expansion(quoted_apply(
            "True.intro",
            references,
        ))]);
        let result = super::elaborate("theorem rejectedMetadata : True := by skip", provider);
        assert!(
            matches!(
                &result,
                Err(NatDefinitionElabError::Inference(SourceInferenceError::PreresolvedReference {
                    feature,
                    ..
                })) if *feature == expected
            ),
            "{expected}: {result:?}"
        );
    }
}

#[test]
fn generated_clear_keeps_specialized_prereference_refusal() {
    let clear = Syntax::Node {
        info: SourceInfo::None,
        kind: Name::from_components(["Lean", "Parser", "Tactic", "clear"]),
        args: vec![
            Syntax::Atom {
                info: SourceInfo::None,
                val: "clear".to_owned(),
            },
            Syntax::Node {
                info: SourceInfo::None,
                kind: Name::from_components(["null"]),
                args: vec![quoted_identifier(
                    "h",
                    vec![declaration_reference("True.intro")],
                )],
            },
        ],
    };
    let provider = Provider::new(vec![Candidate::Expansion(clear)]);
    assert!(matches!(
        super::elaborate(
            "theorem retained (h : True) : True := by skip; exact h",
            provider
        ),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::PreresolvedReference {
                feature: "pre-resolved identifiers in pattern or tactic syntax",
                ..
            }
        ))
    ));
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
        // The matrix and equation capture share this occurrence's prepared
        // row. Neither capture nor a generated comparison adds a lookup.
        assert_eq!(count("1"), 1);
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
fn atomic_term_macro_chains_reach_the_bound_without_recursive_evaluators() {
    let provider = Templates::new(&[
        "macro_rules | `(1) => `(2)",
        "macro_rules | `(2) => `(3)",
        "macro_rules | `(3) => `(4)",
        "macro_rules | `(4) => `(5)",
        "macro_rules | `(5) => `(6)",
        "macro_rules | `(6) => `(7)",
        "macro_rules | `(7) => `(8)",
        "macro_rules | `(8) => `(9)",
    ]);
    let environment = environment();
    let declaration = checked_in("def chain : Nat := 1", provider.clone(), &environment).unwrap();
    assert_eq!(
        *provider.depths.lock().unwrap(),
        (1usize..=9)
            .map(|literal| (literal.to_string(), literal - 1))
            .collect::<Vec<_>>(),
        "each root and the terminal lookup runs once at its reader depth"
    );
    let environment = publish(&environment, declaration);
    checked_in(
        "theorem completedChain : Eq chain 9 := Eq.refl 9",
        Templates::new(&[]),
        &environment,
    )
    .unwrap();

    let provider = Templates::new(&["macro_rules | `(1) => `(2)", "macro_rules | `(2) => `(1)"]);
    let error = checked("def cyclic : Nat := 1", provider.clone()).unwrap_err();
    assert!(matches!(
        error,
        NatDefinitionElabError::Inference(SourceInferenceError::TacticMacro(
            TacticMacroError::Inconclusive(_)
        ))
    ));
    assert_eq!(
        provider
            .depths
            .lock()
            .unwrap()
            .last()
            .map(|(_, depth)| *depth),
        Some(8),
        "cycles retain the existing owned-expansion bound"
    );
}

#[test]
fn atomic_pattern_shape_changes_and_loops_never_use_the_original_literal() {
    let environment = environment();
    let declaration = checked_in(
        "def pattern (n : Nat) : Nat := match n with | 1 => 7 | _ => 0",
        Templates::new(&["macro_rules | `(1) => `(Nat.succ (Nat.succ Nat.zero))"]),
        &environment,
    )
    .unwrap();
    let environment = publish(&environment, declaration);
    for source in [
        "theorem replacementMatches : Eq (pattern 2) 7 := Eq.refl 7",
        "theorem originalDoesNotMatch : Eq (pattern 1) 0 := Eq.refl 0",
    ] {
        checked_in(source, Templates::new(&[]), &environment)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
    for rule in [
        "macro_rules | `(1) => `(Bool.true)",
        "macro_rules | `(1) => `(Nat.add)",
    ] {
        assert!(
            checked(
                "def invalidPattern (n : Nat) : Nat := match n with | 1 => 7 | _ => 0",
                Templates::new(&[rule]),
            )
            .is_err(),
            "a generated pattern must still have the subject's constructor type: {rule}"
        );
    }
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

fn dependent_application_environment() -> Environment {
    let environment = environment();
    let parsed = fln_parse::parse_definition(
        b"inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v",
    )
    .unwrap();
    let declaration = fln_elab::source::scope::elaborate_inductive(
        parsed.syntax(),
        &environment,
        budget(),
        RecordBudget::default(),
        &SourceScope::default(),
    )
    .unwrap();
    publish(&environment, declaration)
}

#[test]
fn dependent_application_typing_uses_the_actual_atomic_expansion_once() {
    let environment = dependent_application_environment();
    for source in [
        "def inferred : W (fun _ => Bool) 3 Bool.true := W.mk 3 true",
        "def inferred : W (fun _ => Bool) 3 Bool.true := by exact W.mk 3 true",
        "def inferred (b : Bool) : W (fun _ => Bool) 3 Bool.true := match b with | true => W.mk 3 true | false => W.mk 3 true",
    ] {
        let provider = Templates::new(&["macro_rules | `(true) => `(_)"]);
        checked_in(source, provider.clone(), &environment)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        let expansions = provider.expansions.lock().unwrap();
        let expected = if source.contains("match b") { 2 } else { 1 };
        assert_eq!(
            expansions.iter().filter(|input| *input == "true").count(),
            expected,
            "the guard must not expand arguments speculatively or replay the provider"
        );
    }
}

struct EquationMacros {
    next: AtomicU64,
    scopes: AtomicU64,
    term_expansions: AtomicU64,
    terminal_literals: Mutex<Vec<u64>>,
    tactic_candidates: Mutex<Vec<usize>>,
    fail_first_candidate: bool,
}

impl EquationMacros {
    fn new(fail_first_candidate: bool) -> Arc<Self> {
        Arc::new(Self {
            next: AtomicU64::new(7),
            scopes: AtomicU64::new(100),
            term_expansions: AtomicU64::new(0),
            terminal_literals: Mutex::new(Vec::new()),
            tactic_candidates: Mutex::new(Vec::new()),
            fail_first_candidate,
        })
    }
}

impl TacticMacroExpander for EquationMacros {
    fn contains(&self, kind: &Name) -> bool {
        *kind == key() || *kind == Name::from_components(["ident"])
    }

    fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
        Ok(self.scopes.fetch_add(1, Ordering::Relaxed))
    }

    fn expand_tactic(
        &self,
        _: &Syntax,
        candidate: usize,
        _: u64,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        let successful = usize::from(self.fail_first_candidate);
        if candidate > successful {
            return Ok(TacticMacroExpansion::Exhausted);
        }
        self.tactic_candidates.lock().unwrap().push(candidate);
        let script = if candidate < successful {
            // A real typing failure after expansion, rather than a fabricated
            // provider refusal: the successful candidate must restore the goal.
            "exact True.intro".to_owned()
        } else {
            format!("exact {}", self.next.fetch_add(1, Ordering::Relaxed))
        };
        Ok(TacticMacroExpansion::Expanded {
            syntax: expansion(&script),
            no_fallback: false,
        })
    }

    fn expand_term(
        &self,
        syntax: &Syntax,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        if matches!(syntax, Syntax::Ident { val, .. }
            if *val == Name::from_components(["equationTick"]))
        {
            self.term_expansions.fetch_add(1, Ordering::Relaxed);
            let value = self.next.fetch_add(1, Ordering::Relaxed);
            return Ok(Some(Syntax::node(
                Name::from_components(["num"]),
                vec![Syntax::atom(SourceInfo::None, value.to_string())],
            )));
        }
        if let Syntax::Node { kind, args, .. } = syntax
            && *kind == Name::from_components(["num"])
            && let [Syntax::Atom { val, .. }] = args.as_slice()
            && let Ok(value) = val.parse()
        {
            self.terminal_literals.lock().unwrap().push(value);
        }
        Ok(None)
    }
}

fn equation_fixture(
    source: &str,
    environment: &Environment,
    provider: Arc<EquationMacros>,
    tactics: bool,
) -> fln_elab::source::ElaboratedDeclaration {
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let mut syntax = parsed.syntax().clone();
    if tactics {
        retag(&mut syntax);
    }
    fln_elab::source::scope::elaborate_definition_with_effects(
        &syntax,
        environment,
        budget(),
        &SourceScope {
            tactic_macros: Some(TacticMacroProvider(provider)),
            ..SourceScope::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
}

fn publish_captured_equations(
    environment: &Environment,
    result: fln_elab::source::ElaboratedDeclaration,
    alternatives: usize,
) -> Environment {
    use fln_elab::source::equation_theorems::{self, Request, journal};
    assert!(result.native_axioms.is_empty());
    assert!(result.local_functions.is_empty());
    let record = result
        .equation_info
        .expect("successful macro bodies must retain their equation information");
    assert_eq!(record.alternatives.len(), alternatives);
    let environment = publish(environment, result.declaration);
    let mut environment = journal::push(&environment, &record).unwrap();
    let equations = equation_theorems::realize(
        &environment,
        &Request::Equations(Name::from_components(["stateful"])),
        budget(),
    )
    .expect("the captured right-hand sides must prove the actual definition's equations");
    assert!(!equations.is_empty());
    for equation in equations {
        environment = publish(&environment, equation);
    }
    environment
}

fn check_captured_equations(
    environment: &Environment,
    result: fln_elab::source::ElaboratedDeclaration,
    values: [u64; 2],
) {
    let environment = publish_captured_equations(environment, result, 2);
    for (index, (argument, value)) in ["Bool.true", "Bool.false"]
        .into_iter()
        .zip(values)
        .enumerate()
    {
        let source = format!(
            "theorem observed{index} : Eq (stateful {argument}) {value} := stateful.eq_{}",
            index + 1
        );
        checked_in(&source, Templates::new(&[]), &environment).unwrap();
    }
}

#[test]
fn equation_capture_preserves_stateful_term_expansions_and_terminal_lookups() {
    for source in [
        "def stateful (b : Bool) : Nat := match b with | true => equationTick | false => equationTick",
        "def stateful (b : Bool) : Nat := match b with | true => by exact equationTick | false => by exact equationTick",
    ] {
        let environment = environment();
        let provider = EquationMacros::new(false);
        let result = equation_fixture(source, &environment, provider.clone(), false);
        assert_eq!(
            provider.term_expansions.load(Ordering::Relaxed),
            2,
            "{source}"
        );
        assert_eq!(
            *provider.terminal_literals.lock().unwrap(),
            [7, 8],
            "terminal None lookups belong to the original elaboration, too: {source}"
        );
        check_captured_equations(&environment, result, [7, 8]);
    }
}

#[test]
fn equation_capture_preserves_failed_tactic_attempts_without_reexecuting_them() {
    for (source, failed_candidate, candidates, literals, values) in [
        (
            "def stateful (b : Bool) : Nat := match b with | true => by skip | false => by skip",
            true,
            vec![0, 1, 0, 1],
            vec![7, 8],
            [7, 8],
        ),
        (
            "def stateful (b : Bool) : Nat := match b with\n  | true => by\n      first\n      | (skip; fail)\n      | skip\n  | false => by\n      first\n      | (skip; fail)\n      | skip",
            false,
            vec![0, 0, 0, 0],
            vec![7, 8, 9, 10],
            [8, 10],
        ),
    ] {
        let environment = environment();
        let provider = EquationMacros::new(failed_candidate);
        let result = equation_fixture(source, &environment, provider.clone(), true);
        assert_eq!(
            *provider.tactic_candidates.lock().unwrap(),
            candidates,
            "{source}"
        );
        assert_eq!(
            *provider.terminal_literals.lock().unwrap(),
            literals,
            "{source}"
        );
        // Opaque definitions elaborate the same body but do not capture
        // equations. They independently fix the number of live scope requests.
        let control_provider = EquationMacros::new(failed_candidate);
        let control = equation_fixture(
            &source.replacen("def stateful", "opaque stateful", 1),
            &environment,
            control_provider.clone(),
            true,
        );
        assert!(control.equation_info.is_none());
        assert!(matches!(
            fln_kernel::check(&environment, &control.declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        assert_eq!(
            provider.scopes.load(Ordering::Relaxed),
            control_provider.scopes.load(Ordering::Relaxed),
            "equation capture must not request additional live macro scopes: {source}"
        );
        check_captured_equations(&environment, result, values);
    }
}

#[test]
fn equation_capture_retains_pattern_locals_and_structural_recursive_calls() {
    for (source, successor) in [
        (
            "def stateful (n : Nat) : Nat := match n with | .zero => equationTick | .succ k => equationTick + k",
            "theorem observedSucc (k : Nat) : Eq (stateful (Nat.succ k)) (8 + k) := stateful.eq_2 k",
        ),
        (
            "def stateful (n : Nat) : Nat := match n with | .zero => equationTick | .succ k => stateful k + equationTick",
            "theorem observedSucc (k : Nat) : Eq (stateful (Nat.succ k)) (stateful k + 8) := stateful.eq_2 k",
        ),
    ] {
        let environment = environment();
        let provider = EquationMacros::new(false);
        let result = equation_fixture(source, &environment, provider.clone(), false);
        assert_eq!(
            provider.term_expansions.load(Ordering::Relaxed),
            2,
            "{source}"
        );
        let environment = publish_captured_equations(&environment, result, 2);
        for proof in [
            "theorem observedZero : Eq (stateful Nat.zero) 7 := stateful.eq_1",
            successor,
        ] {
            checked_in(proof, Templates::new(&[]), &environment)
                .unwrap_or_else(|error| panic!("{source}\n{proof}: {error:?}"));
        }
    }
}

#[test]
fn equation_capture_elaborates_constructor_fields_in_written_order() {
    let source = "def stateful (n : Nat) : Nat := match n with | .succ k => equationTick + k | .zero => equationTick";
    let environment = environment();
    let provider = EquationMacros::new(false);
    let result = equation_fixture(source, &environment, provider.clone(), false);
    assert_eq!(provider.term_expansions.load(Ordering::Relaxed), 2);
    assert_eq!(*provider.terminal_literals.lock().unwrap(), [7, 8]);
    let environment = publish_captured_equations(&environment, result, 2);
    for proof in [
        "theorem observedSucc (k : Nat) : Eq (stateful (Nat.succ k)) (7 + k) := stateful.eq_1 k",
        "theorem observedZero : Eq (stateful Nat.zero) 8 := stateful.eq_2",
    ] {
        checked_in(proof, Templates::new(&[]), &environment)
            .unwrap_or_else(|error| panic!("{proof}: {error:?}"));
    }
}

#[test]
fn equation_capture_keeps_pure_matrix_rows_with_fresh_tactic_scopes() {
    let source = "def stateful (x y : Bool) : Nat := match x, y with | true, true => by exact 7 | false, true => by exact 8 | _, false => by exact 9";
    let environment = environment();
    let provider = EquationMacros::new(false);
    let result = equation_fixture(source, &environment, provider.clone(), false);
    let control_provider = EquationMacros::new(false);
    let control = equation_fixture(
        &source.replacen("def stateful", "opaque stateful", 1),
        &environment,
        control_provider.clone(),
        false,
    );
    assert!(control.equation_info.is_none());
    assert!(matches!(
        fln_kernel::check(&environment, &control.declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    assert_eq!(
        provider.scopes.load(Ordering::Relaxed),
        control_provider.scopes.load(Ordering::Relaxed),
        "capturing repeated pure rows must not allocate more live scopes"
    );
    let environment = publish_captured_equations(&environment, result, 3);
    for proof in [
        "theorem observedFirst : Eq (stateful Bool.true Bool.true) 7 := stateful.eq_1",
        "theorem observedSecond : Eq (stateful Bool.false Bool.true) 8 := stateful.eq_2",
        "theorem observedCatchall (x : Bool) : Eq (stateful x Bool.false) 9 := stateful.eq_3 x",
    ] {
        checked_in(proof, Templates::new(&[]), &environment)
            .unwrap_or_else(|error| panic!("{proof}: {error:?}"));
    }
}

#[test]
fn equation_observation_skips_matches_outside_the_metadata_slice() {
    let source = "def stateful (n : Nat) : Nat := match Nat.succ n, n with | .zero, _ => 7 | .succ _, _ => 8";
    let environment = environment();
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let control = fln_elab::source::scope::elaborate_definition_with_effects(
        parsed.syntax(),
        &environment,
        budget(),
        &SourceScope::default(),
    )
    .unwrap();
    let observed = equation_fixture(source, &environment, EquationMacros::new(false), false);
    for result in [control, observed] {
        assert!(result.equation_info.is_none());
        let environment = publish(&environment, result.declaration);
        checked_in(
            "theorem actualValue (n : Nat) : Eq (stateful n) 8 := Eq.refl 8",
            Templates::new(&[]),
            &environment,
        )
        .unwrap();
    }
}

#[test]
fn regular_matches_expand_branch_bodies_in_written_order() {
    for source in [
        "opaque ordered (b : Bool) : Nat := match b with | true => rhsFirst | false => rhsSecond",
        "opaque ordered (n : Nat) : Nat := match n with | .succ k => rhsFirst + k | .zero => rhsSecond",
    ] {
        let provider = Templates::new(&[
            "macro_rules | `(rhsFirst) => `(7)",
            "macro_rules | `(rhsSecond) => `(8)",
        ]);
        checked_in(source, provider.clone(), &environment())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(
            *provider.expansions.lock().unwrap(),
            ["rhsFirst", "rhsSecond"],
            "source branch order must be independent of recursor argument order: {source}"
        );
    }
}

#[test]
fn regular_match_source_order_preserves_unsafe_definition_admission() {
    let environment = environment();
    let seed = checked_in(
        "unsafe def unsafeSeed : Nat := 7",
        Templates::new(&[]),
        &environment,
    )
    .unwrap();
    let environment = publish(&environment, seed);
    checked_in(
        "unsafe def unsafeChoice (b : Bool) : Nat := match b with | true => unsafeSeed | false => 0",
        Templates::new(&[]),
        &environment,
    )
    .unwrap();
}

#[test]
fn dependent_application_typing_keeps_rejections_after_macro_observation() {
    let environment = dependent_application_environment();
    for (rule, body) in [
        ("macro_rules | `(unrelated) => `(_)", "W.mk 3 true"),
        ("macro_rules | `(unrelated) => `(_)", "W.mk 3 Bool.true"),
        (
            "macro_rules | `(unrelated) => `(_)",
            "W.mk 3 _root_.Bool.true",
        ),
        ("macro_rules | `(magic) => `(true)", "W.mk 3 magic"),
        ("macro_rules | `(magic) => `(true)", "by exact W.mk 3 magic"),
        (
            "macro_rules | `(magic) => `(_root_.Bool.true)",
            "W.mk 3 magic",
        ),
        ("macro_rules | `(magic) => `((true : Bool))", "W.mk 3 magic"),
    ] {
        let source = format!("def rejected : W (fun _ => Bool) 3 Bool.true := {body}");
        let error = checked_in(&source, Templates::new(&[rule]), &environment).unwrap_err();
        assert!(
            matches!(
                error,
                NatDefinitionElabError::Inference(SourceInferenceError::TypeMismatch { .. })
            ),
            "{source}: {error:?}"
        );
    }
    let error = checked_in(
        "def rejected : W (fun _ => Bool) 3 Bool.true := W.mk 3 magic",
        Templates::new(&["macro_rules | `(magic) => `(\"wrong type\")"]),
        &environment,
    )
    .unwrap_err();
    assert!(
        matches!(error, NatDefinitionElabError::Inference(_)),
        "an observed expansion never manufactures an expected-type value: {error:?}"
    );
}

#[test]
fn dependent_application_macro_observations_follow_chains_and_tactic_rollback() {
    let environment = dependent_application_environment();
    let provider = Templates::new(&[
        "macro_rules | `(true) => `(intermediate)",
        "macro_rules | `(intermediate) => `(_)",
    ]);
    checked_in(
        "def inferred : W (fun _ => Bool) 3 Bool.true := W.mk 3 true",
        provider.clone(),
        &environment,
    )
    .unwrap();
    assert_eq!(
        *provider.expansions.lock().unwrap(),
        ["true", "intermediate"],
        "nested observations must collapse without rerunning a macro"
    );

    let provider = Templates::new(&[
        "macro_rules | `(1) => `(3)",
        "macro_rules | `(true) => `(_)",
    ]);
    checked_in(
        "def ordered : W (fun _ => Bool) 3 Bool.true := W.mk 1 true",
        provider.clone(),
        &environment,
    )
    .unwrap();
    assert_eq!(
        *provider.expansions.lock().unwrap(),
        ["1", "true"],
        "only the actual left-to-right argument visits may advance macro state"
    );

    let provider = Templates::new(&["macro_rules | `(magic) => `(true)"]);
    checked_in(
        "def recovered : W (fun _ => Bool) 3 Bool.true := by first | exact W.mk 3 magic | exact W.mk (P := fun _ => Bool) 3 Bool.true",
        provider.clone(),
        &environment,
    )
    .unwrap();
    assert_eq!(
        *provider.expansions.lock().unwrap(),
        ["magic"],
        "a failed candidate drops syntax observations without refunding its macro effects"
    );
}

#[test]
fn generated_leading_lambdas_dispatch_macros_before_opening_binders() {
    // The source driver expands compound source syntax before this boundary.
    // A generated lambda reaches the owned-term worklist and must dispatch its
    // registered rule before the predefinition opens any of its binders.
    for source in [
        "def f : Nat → Nat := generatedLambda",
        "def f := generatedLambda",
    ] {
        let (provider, _) = Templates::with_runtime_parser(
            &[
                "macro_rules | `(generatedLambda) => `(fun (x : Nat) => 0)",
                "macro_rules | `(fun $binder => 0) => `(Nat.succ)",
            ],
            &[Name::from_components(["Lean", "Parser", "Term", "fun"])],
        );
        let environment = environment();
        let declaration = checked_in(source, provider.clone(), &environment)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(
            *provider.expansions.lock().unwrap(),
            ["generatedLambda", "Lean.Parser.Term.fun"],
            "the generated leading lambda must expand exactly once: {source}"
        );
        let environment = publish(&environment, declaration);
        checked_in(
            "theorem generatedRootValue : Eq (f 0) 1 := Eq.refl 1",
            Templates::new(&[]),
            &environment,
        )
        .unwrap();
    }
}

#[test]
fn failed_lambda_candidates_keep_their_body_macro_effects() {
    let provider = Templates::new(&["macro_rules | `(magic) => `(7)"]);
    let environment = environment();
    let declaration = checked_in(
        "def f : Nat := by first | exact (fun (_n : Nat) => magic) | exact 42",
        provider.clone(),
        &environment,
    )
    .unwrap();
    assert_eq!(
        *provider.expansions.lock().unwrap(),
        ["magic"],
        "a rigid non-function expectation rejects the lambda after elaborating its body"
    );
    let environment = publish(&environment, declaration);
    checked_in(
        "theorem failedLambdaValue : Eq f 42 := Eq.refl 42",
        Templates::new(&[]),
        &environment,
    )
    .unwrap();
}
