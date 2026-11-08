//! A duplicated matrix row has one equation only when its observed macros agree.
#![forbid(unsafe_code)]

use super::*;
use fln_elab::source::{ElaboratedDeclaration, equation_theorems, trace};

const SOURCE: &str =
    "def duplicated (a b : Bool) : Nat := match a, b with | true, true => 0 | _, _ => magic";
const TACTIC_SOURCE: &str = "def duplicated (a b : Bool) : Nat := match a, b with | true, true => 0 | _, _ => by exact magic";
const WRITTEN: &str =
    "def duplicated (a b : Bool) : Nat := match a, b with | true, true => 0 | _, _ => 31";
const LET_SOURCE: &str = "def duplicated (a b : Bool) : Nat :=\n  match a, b with\n  | true, true => 0\n  | _, _ =>\n    (let f : Nat → Nat\n       | _ => magic\n     f 0)\n";
const LET_WRITTEN: &str = "def duplicated (a b : Bool) : Nat :=\n  match a, b with\n  | true, true => 0\n  | _, _ =>\n    (let f : Nat → Nat\n       | _ => 31\n     f 0)\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn matrix_syntax(source: &str) -> Syntax {
    fln_parse::parse_definition(source.as_bytes())
        .unwrap()
        .syntax()
        .clone()
}

struct MatrixProvider {
    changing: bool,
    calls: AtomicU64,
    scopes: AtomicU64,
}

impl TacticMacroExpander for MatrixProvider {
    fn contains(&self, kind: &Name) -> bool {
        *kind == name("ident")
    }

    fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
        Ok(self.scopes.fetch_add(1, Ordering::Relaxed))
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
        if !matches!(syntax, Syntax::Ident { val, .. } if *val == name("magic")) {
            return Ok(None);
        }
        let call = self.calls.fetch_add(1, Ordering::Relaxed);
        let value = 31 + if self.changing { call } else { 0 };
        Ok(Some(Syntax::node(
            name("num"),
            vec![Syntax::atom(SourceInfo::None, value.to_string())],
        )))
    }
}

fn elaborate_matrix(
    source: &str,
    changing: bool,
) -> (Environment, ElaboratedDeclaration, Arc<MatrixProvider>) {
    let environment = environment();
    let provider = Arc::new(MatrixProvider {
        changing,
        calls: AtomicU64::new(0),
        scopes: AtomicU64::new(100),
    });
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider.clone())),
        ..SourceScope::default()
    };
    let syntax = matrix_syntax(source);
    let actual = trace::elaborate_definition(&syntax, &environment, budget(), &scope)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .candidate;
    assert!(actual.native_axioms.is_empty());
    assert!(actual.local_functions.is_empty());
    assert!(
        matches!(
            fln_kernel::check(&environment, &actual.declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ),
        "the actual specialized branches must form a checked definition"
    );
    assert_eq!(
        provider.calls.load(Ordering::Relaxed),
        2,
        "the catchall is visited in two matrix branches; metadata must not call it again"
    );
    (environment, actual, provider)
}

fn publish(environment: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
        panic!("matrix equation admission did not answer")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("matrix equation failed admission")
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
        other => panic!("matrix equation publication: {other:?}"),
    }
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
    assert!(matches!(
        fln_kernel::check(environment, &declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
}

#[test]
fn incompatible_duplicate_row_expansions_decline_equation_metadata() {
    let (base, actual, provider) = elaborate_matrix(SOURCE, true);
    assert!(
        actual.equation_info.is_none(),
        "31 and 32 in different specializations cannot become one catchall equation"
    );
    let environment = publish(&base, actual.declaration);
    let error = equation_theorems::realize(
        &environment,
        &equation_theorems::Request::Equations(name("duplicated")),
        budget(),
    )
    .expect_err("unrepresentable source equations must refuse typed");
    match error {
        NatDefinitionElabError::Inference(SourceInferenceError::EquationTheorem(reason)) => {
            assert_eq!(reason.declaration, name("duplicated"));
            assert_eq!(
                reason.reason,
                equation_theorems::Unsupported::UnrecordedMatch
            );
        }
        other => panic!("expected a missing equation-information refusal: {other:?}"),
    }
    assert!(!environment.contains(&name("duplicated.eq_1")));
    assert!(!environment.contains(&name("duplicated.eq_2")));
    assert_eq!(provider.calls.load(Ordering::Relaxed), 2);
}

#[test]
fn identical_duplicate_row_expansions_keep_checked_equations() {
    for source in [SOURCE, TACTIC_SOURCE] {
        check_identical_duplicate_row(source, WRITTEN);
    }
}

#[test]
fn let_equation_preprocessing_preserves_original_macro_rows() {
    // Preparing the inner let equations rebuilds the entire match before matrix
    // specialization. The original catchall still needs one replayable trace.
    // One irrefutable inner row keeps the statement within the equation
    // realizer's supported fragment while exercising the same preparation pass.
    check_identical_duplicate_row(LET_SOURCE, LET_WRITTEN);
}

#[test]
fn fatal_macro_stop_survives_equation_recording_cleanup() {
    let mut stopped = Inconclusive::cancelled("equation row");
    stopped.diagnostic = Some(fln_core::diag::ErrorValue::SyntaxFailure {
        message: "x".repeat(1_100_000),
    });
    let reason = TacticMacroError::Inconclusive(Box::new(stopped));
    let provider = Provider::new(vec![
        Candidate::Stop(reason.clone()),
        Candidate::Expansion(expansion("exact 1")),
    ]);
    let parsed = fln_parse::parse_definition(
        b"def stopped (b : Bool) : Nat := match b with\n  | true => (by first | skip | exact 1)\n  | false => 0\n",
    )
    .unwrap();
    let mut syntax = parsed.syntax().clone();
    retag(&mut syntax);
    let scope = SourceScope {
        tactic_macros: Some(TacticMacroProvider(provider.clone())),
        ..SourceScope::default()
    };
    let error = trace::elaborate_definition(&syntax, &environment(), budget(), &scope)
        .err()
        .expect("cancellation is terminal even if recording its diagnostic exhausts the trace");
    match error {
        NatDefinitionElabError::Inference(SourceInferenceError::TacticMacro(error)) => {
            assert!(
                error == reason,
                "cleanup must preserve the original cancellation"
            );
        }
        _ => panic!("equation recording cleanup replaced the original cancellation"),
    }
    assert_eq!(provider.calls.lock().unwrap().len(), 1);
}

fn same_record_statements(
    left: &equation_theorems::journal::Record,
    right: &equation_theorems::journal::Record,
) -> bool {
    use fln_env::terms::alpha_canonical_digest;

    left.declaration == right.declaration
        && left.arity == right.arity
        && left.discriminants == right.discriminants
        && left.motive_names == right.motive_names
        && alpha_canonical_digest(&left.key) == alpha_canonical_digest(&right.key)
        && left.alternatives.len() == right.alternatives.len()
        && left
            .alternatives
            .iter()
            .zip(&right.alternatives)
            .all(|(left, right)| alpha_canonical_digest(left) == alpha_canonical_digest(right))
}

fn check_identical_duplicate_row(source: &str, written: &str) {
    let (base, actual, provider) = elaborate_matrix(source, false);
    assert_eq!(
        provider.scopes.load(Ordering::Relaxed),
        if source == TACTIC_SOURCE { 102 } else { 100 },
        "actual tactic visits have distinct scopes; replay must not allocate another"
    );
    let record = actual
        .equation_info
        .expect("identical actual row visits retain their equation information");
    let syntax = matrix_syntax(written);
    let expected = trace::elaborate_definition(&syntax, &base, budget(), &SourceScope::default())
        .unwrap()
        .candidate;
    // The private typed header consumes a fresh local during actual body
    // elaboration. Replayed and independently written nested lambdas can then
    // have different generated binder labels. Compare those labels modulo
    // alpha-renaming, retaining binder_info, non_dep, metadata, indices and
    // every free/constant name as well as the exact Record fields and order.
    assert!(
        same_record_statements(
            &record,
            expected
                .equation_info
                .as_ref()
                .expect("the written expansion retains its equations"),
        ),
        "the retained statements must match the source with the actual expansion"
    );
    let changed = matrix_syntax(&written.replace("31", "32"));
    let changed = trace::elaborate_definition(&changed, &base, budget(), &SourceScope::default())
        .unwrap()
        .candidate;
    assert!(
        !same_record_statements(
            &record,
            changed
                .equation_info
                .as_ref()
                .expect("changing the RHS literal preserves the equation shape"),
        ),
        "alpha comparison must still distinguish a changed captured RHS value"
    );
    let environment = publish(&base, actual.declaration);
    let mut environment = equation_theorems::journal::push(&environment, &record).unwrap();
    let equations = equation_theorems::realize(
        &environment,
        &equation_theorems::Request::Equations(name("duplicated")),
        budget(),
    )
    .expect("representable matrix equations are generated");
    assert!(equations.len() >= 2);
    for equation in equations {
        environment = publish(&environment, equation);
    }
    assert!(environment.contains(&name("duplicated.eq_1")));
    assert!(environment.contains(&name("duplicated.eq_2")));
    for source in [
        "theorem selected : duplicated Bool.true Bool.true = 0 := duplicated.eq_1",
        "theorem firstCatchall : duplicated Bool.false Bool.true = 31 := by rfl",
        "theorem secondCatchall : duplicated Bool.true Bool.false = 31 := by rfl",
    ] {
        checked(&environment, source);
    }
    assert_eq!(provider.calls.load(Ordering::Relaxed), 2);
}
