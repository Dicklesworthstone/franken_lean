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

#[path = "imported_tactic_runtime/atomic_terms.rs"]
mod atomic_terms;
#[path = "imported_tactic_runtime/equation_macro_duplicates.rs"]
mod equation_macro_duplicates;
#[path = "imported_tactic_runtime/equation_macros.rs"]
mod equation_macros;

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
    DepthExpansion {
        terminal_depth: usize,
        recursive: Syntax,
        terminal: Syntax,
    },
    Decline,
    Diagnostic {
        no_fallback: bool,
    },
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
        depth: usize,
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
            Candidate::DepthExpansion {
                terminal_depth,
                recursive,
                terminal,
            } => TacticMacroExpansion::Expanded {
                syntax: if depth < *terminal_depth {
                    recursive.clone()
                } else {
                    terminal.clone()
                },
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
    elaborate_syntax(&syntax, &scope)
}

fn elaborate_syntax(
    syntax: &Syntax,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    let environment = environment();
    let declaration =
        elaborate_definition_in_scope_with_budget(syntax, &environment, budget(), scope)?;
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

fn annotated(body: Syntax) -> Syntax {
    Syntax::Node {
        info: SourceInfo::None,
        kind: Name::from_components(["Lean", "Parser", "Tactic", "withAnnotateState"]),
        args: vec![
            Syntax::Atom {
                info: SourceInfo::None,
                val: "with_annotate_state".into(),
            },
            // This is deliberately executable failing syntax: the reference
            // is source metadata and must never run as a tactic.
            expansion("fail"),
            body,
        ],
    }
}

#[test]
fn state_annotations_preserve_the_complete_frontier_and_outer_continuation() {
    for (source, body) in [
        (
            "theorem result (P : Prop) : P → P := by skip; exact h",
            "intro h",
        ),
        (
            "theorem result (P : Prop) (h : P) : And P P := by skip; all_goals exact h",
            "constructor",
        ),
        (
            "theorem result (P : Prop) (h : P) : And P P := by constructor; skip",
            "all_goals assumption",
        ),
    ] {
        let provider = Provider::new(vec![Candidate::Expansion(annotated(expansion(body)))]);
        elaborate(source, provider).unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
}

#[test]
fn state_annotations_execute_the_body_even_when_the_frontier_is_empty() {
    for (body, succeeds) in [
        ("skip", true),
        ("(skip)", true),
        ("(try rfl)", true),
        ("(all_goals fail)", true),
        ("fail", false),
        ("(fail)", false),
        ("rfl", false),
        ("(rfl)", false),
    ] {
        let mut generated = expansion("rfl");
        let Syntax::Node { args, .. } = &mut generated else {
            panic!("sequence")
        };
        args.push(annotated(expansion(body)));
        let provider = Provider::new(vec![Candidate::Expansion(generated)]);
        let result = elaborate("theorem result (n : Nat) : Eq n n := by skip", provider);
        assert_eq!(result.is_ok(), succeeds, "{body}: {result:?}");
    }
}

#[test]
fn failed_annotated_candidates_restore_locals_and_goal_assignments() {
    let provider = Provider::new(vec![
        Candidate::Expansion(annotated(expansion("intro abandoned; fail"))),
        Candidate::Expansion(annotated(expansion("intro h"))),
    ]);
    elaborate(
        "theorem result (P : Prop) : P → P := by skip; exact h",
        provider.clone(),
    )
    .unwrap();
    let calls = provider.calls.lock().unwrap();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].1, calls[1].1);
}

#[test]
fn state_annotations_follow_get_arg_semantics_for_generated_syntax() {
    // The pin's builtin reads only children 1 and 2. A missing body is a
    // no-op; neither an altered keyword nor surplus children are executed.
    for retained in 0..3 {
        let mut generated = annotated(expansion("fail"));
        let Syntax::Node { args, .. } = &mut generated else {
            panic!("annotation")
        };
        args.truncate(retained);
        let provider = Provider::new(vec![Candidate::Expansion(generated)]);
        elaborate(
            "theorem result (n : Nat) : Eq n n := by skip; rfl",
            provider,
        )
        .unwrap();
    }
    let mut generated = annotated(expansion("rfl"));
    let Syntax::Node { args, .. } = &mut generated else {
        panic!("annotation")
    };
    args[0] = expansion("fail");
    args.push(expansion("fail"));
    let provider = Provider::new(vec![Candidate::Expansion(generated)]);
    elaborate("theorem result (n : Nat) : Eq n n := by skip", provider).unwrap();
}

#[test]
fn state_annotations_and_generic_syntax_execute_without_a_macro_provider() {
    fn replace_skip(syntax: &mut Syntax, replacement: &Syntax) {
        if syntax.kind() == Some(&Name::from_components(["Lean", "Parser", "Tactic", "skip"])) {
            *syntax = replacement.clone();
        } else if let Syntax::Node { args, .. } = syntax {
            for argument in args {
                replace_skip(argument, replacement);
            }
        }
    }

    let empty = Syntax::Node {
        info: SourceInfo::None,
        kind: Name::from_components(["null"]),
        args: Vec::new(),
    };
    let mut cases = vec![
        (annotated(Syntax::Missing), "skip; rfl", true),
        (annotated(expansion("rfl")), "skip", true),
        (annotated(Syntax::Missing), "rfl; skip", true),
        (annotated(empty), "rfl; skip", true),
        (annotated(expansion("fail")), "rfl; skip", false),
    ];
    for retained in 0..3 {
        let mut generated = annotated(expansion("fail"));
        let Syntax::Node { args, .. } = &mut generated else {
            panic!("annotation")
        };
        args.truncate(retained);
        cases.push((generated, "skip; rfl", true));
    }
    for (replacement, script, succeeds) in cases {
        let source = format!("theorem result (n : Nat) : Eq n n := by {script}");
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        let mut syntax = parsed.syntax().clone();
        replace_skip(&mut syntax, &replacement);
        let result = elaborate_syntax(&syntax, &SourceScope::default());
        if succeeds {
            result.unwrap_or_else(|error| panic!("{replacement:?}: {error:?}"));
        } else {
            assert!(matches!(
                result,
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::Tactic(fln_elab::source::TacticError::ExplicitFailure)
                ))
            ));
        }
    }
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
fn nested_generated_tactics_fit_two_mib_and_obey_the_owned_frame_limit() {
    // Pin the actual stack as well as budget(): a larger RUST_MIN_STACK on a
    // developer's host must not hide native-frame growth in owned expansions.
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let source = "theorem result (n : Nat) : Eq n n := by skip";
            let mut recursive = expansion("exact (by skip)");
            retag(&mut recursive);
            for terminal_depth in [6, 7] {
                let provider = Provider::new(vec![Candidate::DepthExpansion {
                    terminal_depth,
                    recursive: recursive.clone(),
                    terminal: expansion("rfl"),
                }]);
                elaborate(source, provider.clone()).unwrap();
                assert_eq!(provider.calls.lock().unwrap().len(), terminal_depth + 1);
            }

            // A generated descendant reenters the evaluator on every step.
            // Root-to-root macro chains alone do not exercise this stack path.
            let provider = Provider::new(vec![Candidate::Expansion(recursive)]);
            let error = elaborate(source, provider.clone()).unwrap_err();
            let NatDefinitionElabError::Inference(SourceInferenceError::TacticMacro(
                TacticMacroError::Inconclusive(reason),
            )) = error
            else {
                panic!("nested macro cycle must exhaust its owned frame limit: {error:?}");
            };
            assert!(matches!(
                reason.cause,
                fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
                    if matches!(usage.reason,
                        fln_core::diag::ResourceReason::RecursionDepth { limit: 8 })
                        && usage.allowed == 8 && usage.observed == 9
            ));
            assert_eq!(provider.calls.lock().unwrap().len(), 9);

            let recovered = Provider::new(vec![Candidate::Expansion(expansion("rfl"))]);
            elaborate(source, recovered.clone()).unwrap();
            assert_eq!(recovered.calls.lock().unwrap().len(), 1);
        })
        .unwrap()
        .join()
        .unwrap();
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
