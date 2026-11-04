//! The native owned-Syntax boundary, independent of imported IR compilation.
//! Every accepted result is a real closed theorem checked by the kernel.
#![forbid(unsafe_code)]

use std::sync::{
    Arc, Mutex,
    atomic::{AtomicU64, Ordering},
};

use fln_core::{
    name::Name,
    outcome::{Inconclusive, InternalFault, Outcome},
};
use fln_elab::{
    NatDefinitionElabError, elaborate_definition_in_scope_with_budget,
    source::{SourceInferenceError, scope::SourceScope},
    tactic_macros::{
        TacticMacroError, TacticMacroExpander, TacticMacroExpansion, TacticMacroProvider,
    },
};
use fln_env::{
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    Declaration,
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
    verdict::{Budget, Verdict},
};
use fln_syntax::{source::SourceInfo, tree::Syntax};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn environment() -> Environment {
    let mut environment = Environment::new();
    for declaration in fln_elab::seed::source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&environment, declaration, budget()) else {
            panic!("seed nonanswer")
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed refused")
        };
        environment = match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("seed publication: {other:?}"),
        };
    }
    environment
}

fn key() -> Name {
    Name::from_components(["Test", "importedTactic"])
}

// Retag a parsed skip only at this raw-Syntax capability test boundary. The CLI
// regression separately obtains these kinds from real imported parser journals.
fn retag(syntax: &mut Syntax) {
    if let Syntax::Node { kind, args, .. } = syntax {
        if *kind == Name::from_components(["Lean", "Parser", "Tactic", "skip"]) {
            *kind = key();
        }
        for argument in args {
            retag(argument);
        }
    }
}

fn expansion(script: &str) -> Syntax {
    let parsed =
        fln_parse::parse_definition(format!("theorem generated : True := by {script}").as_bytes())
            .unwrap();
    let mut pending = vec![parsed.syntax()];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == Name::from_components(["Lean", "Parser", "Tactic", "tacticSeq1Indented"]) {
                let Syntax::Node { args: rows, .. } = &args[0] else {
                    panic!("sequence rows")
                };
                return Syntax::Node {
                    info: SourceInfo::None,
                    kind: Name::from_components(["null"]),
                    args: rows.iter().step_by(2).cloned().collect(),
                };
            }
            pending.extend(args.iter().rev());
        }
    }
    panic!("tactic sequence")
}

#[derive(Clone)]
enum Candidate {
    Expansion(Syntax),
    Decline,
    Diagnostic { no_fallback: bool },
    Stop(TacticMacroError),
}

struct Provider {
    candidates: Vec<Candidate>,
    next: AtomicU64,
    calls: Mutex<Vec<(usize, u64)>>,
}

impl Provider {
    fn new(candidates: Vec<Candidate>) -> Arc<Self> {
        Arc::new(Self {
            candidates,
            next: AtomicU64::new(100),
            calls: Mutex::new(Vec::new()),
        })
    }
}

impl TacticMacroExpander for Provider {
    fn contains(&self, kind: &Name) -> bool {
        *kind == key()
    }
    fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
        Ok(self.next.fetch_add(1, Ordering::Relaxed))
    }
    fn expand_tactic(
        &self,
        _: &Syntax,
        candidate: usize,
        scope: u64,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        let Some(action) = self.candidates.get(candidate) else {
            return Ok(TacticMacroExpansion::Exhausted);
        };
        self.calls.lock().unwrap().push((candidate, scope));
        Ok(match action {
            Candidate::Expansion(syntax) => TacticMacroExpansion::Expanded {
                syntax: syntax.clone(),
                no_fallback: false,
            },
            Candidate::Decline => TacticMacroExpansion::Unsupported,
            Candidate::Diagnostic { no_fallback } => TacticMacroExpansion::Diagnostic {
                error: TacticMacroError::Diagnostic {
                    declaration: key(),
                    message: "candidate failed".into(),
                },
                no_fallback: *no_fallback,
            },
            Candidate::Stop(error) => return Err(error.clone()),
        })
    }
    fn expand_term(
        &self,
        _: &Syntax,
        _: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        Ok(None)
    }
}

fn elaborate(source: &str, provider: Arc<Provider>) -> Result<Declaration, NatDefinitionElabError> {
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let mut syntax = parsed.syntax().clone();
    retag(&mut syntax);
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider)),
        ..SourceScope::default()
    };
    let environment = environment();
    let declaration =
        elaborate_definition_in_scope_with_budget(&syntax, &environment, budget(), &scope)?;
    assert!(matches!(
        fln_kernel::check(&environment, &declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Thm(theorem) = &declaration else {
        panic!("theorem")
    };
    assert!(!theorem.value.has_expr_mvar() && !theorem.value.has_fvar());
    Ok(declaration)
}

#[test]
fn owned_expansions_leave_goals_and_failed_candidates_restore_local_context() {
    let provider = Provider::new(vec![
        Candidate::Expansion(expansion("intro abandoned; fail")),
        Candidate::Expansion(expansion("intro h")),
    ]);
    elaborate(
        "theorem result (P : Prop) : P → P := by skip; exact h",
        provider.clone(),
    )
    .unwrap();
    let calls = provider.calls.lock().unwrap();
    assert_eq!(calls.len(), 2);
    assert_eq!(
        calls[0].1, calls[1].1,
        "candidate retries share evalTactic's scope"
    );
    assert!(
        provider.next.load(Ordering::Relaxed) > calls[0].1 + 3,
        "failed generated instructions do not refund scopes"
    );
}

#[test]
fn generated_constructor_and_nested_goal_controls_keep_all_goals() {
    let provider = Provider::new(Vec::new());
    elaborate(
        "theorem result (n : Nat) : Eq n n := by rfl",
        provider.clone(),
    )
    .unwrap();
    assert!(provider.calls.lock().unwrap().is_empty());
    assert_eq!(
        provider.next.load(Ordering::Relaxed),
        101,
        "pin evalTactic allocates its scope before discovering no macro candidate"
    );

    let provider = Provider::new(vec![Candidate::Expansion(expansion("constructor"))]);
    elaborate(
        "theorem result (P : Prop) (h : P) : And P P := by skip; all_goals exact h",
        provider,
    )
    .unwrap();
    let provider = Provider::new(vec![Candidate::Expansion(expansion("rfl"))]);
    elaborate(
        "theorem result (n : Nat) : And (Eq n n) (Eq n n) := by constructor; all_goals skip",
        provider,
    )
    .unwrap();
}

#[test]
fn unsupported_and_diagnostics_fallback_but_no_fallback_stops_candidates() {
    let provider = Provider::new(vec![
        Candidate::Decline,
        Candidate::Expansion(expansion("rfl")),
    ]);
    elaborate("theorem result (n : Nat) : Eq n n := by skip", provider).unwrap();
    let provider = Provider::new(vec![Candidate::Diagnostic { no_fallback: false }]);
    elaborate(
        "theorem result (n : Nat) : Eq n n := by first | skip | rfl",
        provider,
    )
    .unwrap();
    let provider = Provider::new(vec![
        Candidate::Diagnostic { no_fallback: true },
        Candidate::Expansion(expansion("rfl")),
    ]);
    assert!(matches!(
        elaborate(
            "theorem result (n : Nat) : Eq n n := by skip",
            provider.clone()
        ),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::TacticMacro(TacticMacroError::Diagnostic { .. })
        ))
    ));
    assert_eq!(provider.calls.lock().unwrap().len(), 1);
}

#[test]
fn capability_cancellation_and_internal_faults_never_select_another_branch() {
    for reason in [
        TacticMacroError::Unsupported("unimplemented primitive".into()),
        TacticMacroError::Inconclusive(Box::new(Inconclusive::cancelled("test macro"))),
        TacticMacroError::InternalFault(InternalFault::new("FL-INV-07", "test macro fault")),
    ] {
        let provider = Provider::new(vec![
            Candidate::Stop(reason.clone()),
            Candidate::Expansion(expansion("rfl")),
        ]);
        let error = elaborate(
            "theorem result (n : Nat) : Eq n n := by first | skip | rfl",
            provider.clone(),
        )
        .unwrap_err();
        assert!(
            matches!(error, NatDefinitionElabError::Inference(SourceInferenceError::TacticMacro(ref error)) if error == &reason)
        );
        assert_eq!(provider.calls.lock().unwrap().len(), 1);
    }
}

#[test]
fn primitive_reflexivity_candidates_keep_distinct_eq_and_heq_semantics() {
    let provider = || Provider::new(Vec::new());
    for source in [
        "theorem result (n : Nat) : Eq n n := by eq_refl",
        "theorem result (n : Nat) : Eq n n := by apply_rfl",
        "theorem result (n : Nat) : HEq n n := by apply_rfl",
        "theorem result (n : Nat) : HEq n n := by first | eq_refl | apply_rfl",
    ] {
        elaborate(source, provider()).unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
    for source in [
        "theorem result (n : Nat) : HEq n n := by eq_refl",
        "theorem result : Eq Nat.zero (Nat.succ Nat.zero) := by eq_refl",
        "theorem result : Eq Nat.zero (Nat.succ Nat.zero) := by apply_rfl",
    ] {
        assert!(elaborate(source, provider()).is_err(), "accepted {source}");
    }
}
