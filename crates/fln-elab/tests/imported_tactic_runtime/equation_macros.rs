//! Generated equations retain the macro outcomes used by the checked definition.
//! Counters alone are insufficient: realize the real equations and admit their
//! proofs, then use them at the original values and refuse changed values.
#![forbid(unsafe_code)]

use super::*;
use fln_elab::source::{equation_theorems, trace};
use fln_syntax::{
    source::{BytePos, ByteSpan},
    tree::RawIdentifier,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn identifier(text: &str) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: RawIdentifier::owned(
            Arc::from(text),
            ByteSpan::new(BytePos(0), BytePos(text.len())).unwrap(),
        )
        .unwrap(),
        val: name(text),
        preresolved: Vec::new(),
    }
}

fn numeral(value: u64) -> Syntax {
    Syntax::node(
        name("num"),
        vec![Syntax::atom(SourceInfo::None, value.to_string())],
    )
}

struct Stateful {
    occurrences: [AtomicU64; 2],
    expansions: Mutex<Vec<String>>,
    tactic_calls: Mutex<Vec<(usize, u64)>>,
    scopes: AtomicU64,
}

impl Stateful {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            occurrences: [AtomicU64::new(0), AtomicU64::new(0)],
            expansions: Mutex::new(Vec::new()),
            tactic_calls: Mutex::new(Vec::new()),
            scopes: AtomicU64::new(100),
        })
    }
}

impl TacticMacroExpander for Stateful {
    fn contains(&self, kind: &Name) -> bool {
        *kind == name("ident") || *kind == key()
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
        if syntax.kind() != Some(&key()) {
            return Ok(TacticMacroExpansion::Exhausted);
        }
        self.tactic_calls
            .lock()
            .unwrap()
            .push((candidate, macro_scope));
        let script = match candidate {
            0 => "exact badChain",
            1 => "exact goodChain",
            _ => return Ok(TacticMacroExpansion::Exhausted),
        };
        Ok(TacticMacroExpansion::Expanded {
            syntax: expansion(script),
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
        let Syntax::Ident { val, .. } = syntax else {
            return Ok(None);
        };
        let spelling = val.to_display_string();
        let expanded = match spelling.as_str() {
            "magicTrue" => {
                let call = self.occurrences[0].fetch_add(1, Ordering::Relaxed);
                numeral(11 + 100 * call)
            }
            "magicFalse" => {
                let call = self.occurrences[1].fetch_add(1, Ordering::Relaxed);
                numeral(22 + 100 * call)
            }
            "badChain" => identifier("Bool.true"),
            "goodChain" => identifier("goodTerminal"),
            "goodTerminal" => numeral(17),
            _ => return Ok(None),
        };
        self.expansions.lock().unwrap().push(spelling);
        Ok(Some(expanded))
    }
}

fn publish(environment: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
        panic!("equation fixture admission did not answer")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("the equation or source declaration failed ordinary admission")
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
        other => panic!("equation fixture publication: {other:?}"),
    }
}

fn realized(source: &str, written: &str, provider: Arc<Stateful>, tactics: bool) -> Environment {
    let environment = environment();
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider)),
        ..SourceScope::default()
    };
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let mut syntax = parsed.syntax().clone();
    if tactics {
        retag(&mut syntax);
    }
    let actual = trace::elaborate_definition(&syntax, &environment, budget(), &scope)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .candidate;
    assert!(actual.native_axioms.is_empty());
    assert!(actual.local_functions.is_empty());
    let record = actual
        .equation_info
        .expect("a representable macro RHS must retain its equation information");
    let written = fln_parse::parse_definition(written.as_bytes()).unwrap();
    let expected = trace::elaborate_definition(
        written.syntax(),
        &environment,
        budget(),
        &SourceScope::default(),
    )
    .unwrap()
    .candidate;
    assert_eq!(
        Some(&record),
        expected.equation_info.as_ref(),
        "equation statements must describe the expansions used by the actual body"
    );
    let mut environment = publish(&environment, actual.declaration);
    environment = equation_theorems::journal::push(&environment, &record).unwrap();
    let equations = equation_theorems::realize(
        &environment,
        &equation_theorems::Request::Equations(name("chosen")),
        budget(),
    )
    .expect("the requested equations must be generated");
    assert!(!equations.is_empty());
    for equation in equations {
        environment = publish(&environment, equation);
    }
    assert!(environment.contains(&name("chosen.eq_1")));
    assert!(environment.contains(&name("chosen.eq_2")));
    environment
}

fn checked(environment: &Environment, source: &str) {
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let declaration = elaborate_definition_in_scope_with_budget(
        parsed.syntax(),
        environment,
        budget(),
        &SourceScope::default(),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert!(
        matches!(
            fln_kernel::check(environment, &declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ),
        "{source}"
    );
}

#[test]
fn stateful_rhs_macros_preserve_realized_equations_and_original_values() {
    let provider = Stateful::new();
    let environment = realized(
        "def chosen (b : Bool) : Nat := match b with | true => magicTrue | false => magicFalse",
        "def chosen (b : Bool) : Nat := match b with | true => 11 | false => 22",
        provider.clone(),
        false,
    );
    for source in [
        "theorem first : chosen Bool.true = 11 := chosen.eq_1",
        "theorem second : chosen Bool.false = 22 := chosen.eq_2",
        "theorem computedFirst : chosen Bool.true = 11 := by rfl",
        "theorem computedSecond : chosen Bool.false = 22 := by rfl",
    ] {
        checked(&environment, source);
    }
    for source in [
        "theorem changed : chosen Bool.true = 111 := chosen.eq_1",
        "theorem changed : chosen Bool.false = 222 := chosen.eq_2",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert!(
            elaborate_definition_in_scope_with_budget(
                parsed.syntax(),
                &environment,
                budget(),
                &SourceScope::default(),
            )
            .is_err(),
            "a second macro result must never replace the original equation: {source}"
        );
    }
    assert_eq!(provider.occurrences[0].load(Ordering::Relaxed), 1);
    assert_eq!(provider.occurrences[1].load(Ordering::Relaxed), 1);
}

#[test]
fn equation_reconstruction_reuses_failed_tactic_candidates_and_term_chains() {
    let provider = Stateful::new();
    let environment = realized(
        "def chosen (b : Bool) : Nat := match b with | true => by skip | false => by skip",
        "def chosen (b : Bool) : Nat := match b with | true => 17 | false => 17",
        provider.clone(),
        true,
    );
    checked(
        &environment,
        "theorem first : chosen Bool.true = 17 := chosen.eq_1",
    );
    checked(
        &environment,
        "theorem second : chosen Bool.false = 17 := chosen.eq_2",
    );
    assert_eq!(
        *provider.expansions.lock().unwrap(),
        [
            "badChain",
            "goodChain",
            "goodTerminal",
            "badChain",
            "goodChain",
            "goodTerminal",
        ],
        "failed candidates and chained term expansions run once in each actual branch"
    );
    let calls = provider.tactic_calls.lock().unwrap();
    assert_eq!(calls.len(), 4);
    for invocation in calls.chunks_exact(2) {
        assert_eq!(invocation[0].0, 0);
        assert_eq!(invocation[1].0, 1);
        assert_eq!(invocation[0].1, invocation[1].1);
    }
}
