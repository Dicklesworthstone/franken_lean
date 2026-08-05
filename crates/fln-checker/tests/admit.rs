#![forbid(unsafe_code)]

//! KR-970 … KR-973 — the declaration-admission preamble.
//!
//! Every rule is covered by its acceptance *and* its refusal, and every refusal
//! is asserted on its **own typed variant** rather than on a generic rejection:
//! `matches!(v, Verdict::Rejected(_))` passes when the wrong law refused, which
//! is how a rule stops being tested without any test going red.

use std::cell::Cell;
use std::path::{Path, PathBuf};

use fln_checker::admit::{
    ADMISSION_SCHEMA, AdmissionBudget, AdmissionDeferred, AdmissionGround, AdmissionPhase,
    AdmissionRejection, AdmissionStop, Verdict, admit, admit_with,
};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    EnvironmentBudget, EnvironmentOutcome,
};
use fln_checker::infer::InferenceBudget;
use fln_checker::term::TermBudget;
use fln_checker::whnf::WhnfBudget;
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn primary_name(component: impl Into<String>) -> Name {
    Name::str(Name::anonymous(), component)
}

fn checker_name(component: impl Into<String>) -> WireName {
    let name = primary_name(component);
    match decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

/// `Sort 0` — a well-formed declared type, since its own type is `Sort 1`.
fn a_type() -> WireExpr {
    decoded(&Expr::sort(Level::zero()))
}

/// A Nat literal — a well-formed TERM whose type is `Nat`, which is not a sort.
/// This is the KR-972 subject: not malformed, just not a type.
fn not_a_type() -> WireExpr {
    decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(7))))
}

fn header(
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    kind: ConstantKind,
    safety: ConstantSafety,
) -> ConstantDeclaration {
    ConstantDeclaration::header(level_parameters, type_, kind, safety)
}

fn axiom(name: &str) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}

fn environment_of(entries: Vec<ConstantEntry>) -> ConstantEnvironment {
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("environment did not build: {other:?}"),
    }
}

/// The `Nat` constant KR-972's negative cell needs, so that inferring a Nat
/// literal's type succeeds and the run reaches the sort check rather than dying
/// earlier on an unknown constant.
fn nat_environment() -> ConstantEnvironment {
    environment_of(vec![ConstantEntry::new(
        checker_name("Nat"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Inductive,
            ConstantSafety::Safe,
        ),
    )])
}

// ---------------------------------------------------------------- KR-970

#[test]
fn kr970_a_name_already_in_the_environment_is_refused_and_named() {
    let environment = environment_of(vec![axiom("A")]);
    let verdict = admit(&environment, &axiom("A"), AdmissionBudget::unlimited());
    match verdict {
        Verdict::Rejected(AdmissionRejection::NameAlreadyDeclared { name }) => {
            assert_eq!(
                name,
                checker_name("A"),
                "KR-970 must NAME the colliding constant, not merely report a collision"
            );
        }
        other => panic!("expected KR-970's own rejection, got {other:?}"),
    }

    // Control: the same environment and the same shape under a fresh name is
    // admitted, so the cell above cannot be passing because admission is broken.
    assert!(
        admit(&environment, &axiom("B"), AdmissionBudget::unlimited()).is_admitted(),
        "a fresh name in the same environment must still be admitted"
    );
}

// ---------------------------------------------------------------- KR-971

#[test]
fn kr971_a_repeated_level_parameter_is_refused_naming_both_positions() {
    // [u, v, u] — the repeat is NOT adjacent, so a check comparing neighbours
    // passes here, and the two positions are 0 and 2 rather than n-1 and n.
    let candidate = ConstantEntry::new(
        checker_name("C"),
        header(
            vec![checker_name("u"), checker_name("v"), checker_name("u")],
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    match admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Rejected(AdmissionRejection::DuplicateLevelParameter {
            name,
            parameter,
            first,
            second,
        }) => {
            assert_eq!(name, checker_name("C"));
            assert_eq!(parameter, checker_name("u"), "the DUPLICATE must be named");
            assert_eq!(
                (first, second),
                (0, 2),
                "both positions are carried, and they are the first repeat in \
                 declaration order rather than the last"
            );
        }
        other => panic!("expected KR-971's own rejection, got {other:?}"),
    }

    // Control: distinct parameters over the identical shape are admitted, so the
    // refusal above is about the repeat and not about carrying parameters.
    let distinct = ConstantEntry::new(
        checker_name("C"),
        header(
            vec![checker_name("u"), checker_name("v")],
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    assert!(
        admit(
            &ConstantEnvironment::empty(),
            &distinct,
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "distinct level parameters must not be refused"
    );
}

#[test]
fn kr971_is_checked_before_the_context_that_would_also_refuse_it() {
    // `InferenceContext::new` refuses a repeated level parameter too, so KR-971
    // could ride on that refusal and look implemented while being absent. It is
    // checked FIRST and deliberately: this cell fails if the rule is ever
    // deleted, because the context's refusal surfaces as an InternalFault
    // (ContextUnbuildable) rather than as KR-971's rejection.
    let candidate = ConstantEntry::new(
        checker_name("C"),
        header(
            vec![checker_name("u"), checker_name("u")],
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    let verdict = admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    );
    assert!(
        matches!(
            verdict,
            Verdict::Rejected(AdmissionRejection::DuplicateLevelParameter { .. })
        ),
        "a repeat must be KR-971's REJECTION, never an internal fault from a \
         context that could not be built: got {verdict:?}"
    );
}

// ---------------------------------------------------------------- KR-972

#[test]
fn kr972_a_declared_type_that_is_not_a_type_is_refused_at_the_declaration() {
    // The declared type is `7`. That is a well-formed term whose type is `Nat`,
    // and `Nat` is not a sort — so this declaration is refused HERE rather than
    // at first use, which is the whole point of the rule.
    let candidate = ConstantEntry::new(
        checker_name("D"),
        header(
            Vec::new(),
            not_a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
        Verdict::Rejected(AdmissionRejection::DeclaredTypeIsNotASort { name }) => {
            assert_eq!(name, checker_name("D"));
        }
        other => panic!("expected KR-972's own rejection, got {other:?}"),
    }

    // Control: `Sort 0` in the SAME environment is admitted, so the refusal is
    // attributable to the declared type and not to the environment.
    assert!(
        admit(
            &nat_environment(),
            &axiom("D"),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "a declared type that IS a type must be admitted in the same environment"
    );
}

#[test]
fn kr972_a_declared_type_whose_inference_refuses_is_rejected_carrying_that_refusal() {
    // An unknown constant as the declared type. Inference refuses on its own
    // terms, and KR-972 must carry that refusal rather than flatten it.
    let candidate = ConstantEntry::new(
        checker_name("E"),
        header(
            Vec::new(),
            decoded(&Expr::const_(primary_name("Absent"), Vec::new())),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    match admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Rejected(AdmissionRejection::DeclaredTypeRefused { name, refusal }) => {
            assert_eq!(name, checker_name("E"));
            // The nested refusal is retained, not summarised into a boolean.
            let rendered = format!("{refusal:?}");
            assert!(
                rendered.contains("UnknownConstant"),
                "the inference refusal must be CARRIED, got {rendered}"
            );
        }
        other => panic!("expected KR-972's refusal-carrying rejection, got {other:?}"),
    }
}

// ---------------------------------------------------------------- KR-973

#[test]
fn kr973_an_axiom_whose_preamble_passes_is_admitted_end_to_end() {
    let verdict = admit(
        &ConstantEnvironment::empty(),
        &axiom("A"),
        AdmissionBudget::unlimited(),
    );
    match verdict {
        Verdict::Admitted(admission) => {
            assert_eq!(admission.name(), &checker_name("A"));
            assert_eq!(admission.ground(), AdmissionGround::AxiomPreamble);
            assert_eq!(admission.schema(), ADMISSION_SCHEMA);
        }
        other => panic!("an axiom with a clean preamble must be ADMITTED, got {other:?}"),
    }
}

#[test]
fn every_non_axiom_kind_defers_rather_than_rejecting_or_admitting() {
    // The deferral arm is the one that keeps this slice honest: a definition's
    // preamble is checkable here and its body is not, so a verdict either way
    // would be false. Swept over EVERY non-axiom kind, so a kind added to
    // `ConstantKind` and quietly routed to admission is caught.
    for kind in [
        ConstantKind::Theorem,
        ConstantKind::Opaque,
        ConstantKind::Definition,
        ConstantKind::Inductive,
        ConstantKind::Constructor,
        ConstantKind::Recursor,
        ConstantKind::Quotient,
    ] {
        let candidate = ConstantEntry::new(
            checker_name("K"),
            header(Vec::new(), a_type(), kind, ConstantSafety::Safe),
        );
        let verdict = admit(
            &ConstantEnvironment::empty(),
            &candidate,
            AdmissionBudget::unlimited(),
        );
        match verdict {
            Verdict::Deferred(AdmissionDeferred::BodyNotChecked {
                name,
                kind: deferred_kind,
            }) => {
                assert_eq!(name, checker_name("K"));
                assert_eq!(
                    deferred_kind, kind,
                    "the deferral must name the KIND it owes"
                );
            }
            other => panic!("{kind:?} must DEFER, not decide: got {other:?}"),
        }
    }
}

#[test]
fn an_unsafe_declaration_is_deferred_even_when_its_preamble_is_clean() {
    // KR-975/976 are not built. An unsafe axiom has a clean preamble and must
    // still get no decision — the direction that matters, since admitting it
    // would be the quarantine leaking.
    let candidate = ConstantEntry::new(
        checker_name("U"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    );
    match admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Deferred(AdmissionDeferred::UnsafeQuarantine { name, kind }) => {
            assert_eq!(name, checker_name("U"));
            assert_eq!(kind, ConstantKind::Axiom);
        }
        other => panic!("an unsafe axiom must defer to the quarantine, got {other:?}"),
    }

    // Control: the identical declaration marked Safe IS admitted, so the
    // deferral is attributable to the safety class alone.
    assert!(
        admit(
            &ConstantEnvironment::empty(),
            &axiom("U"),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "the same shape marked Safe must be admitted"
    );
}

// ------------------------------------------------------- FL-INV-07 family

#[test]
fn cancellation_at_every_preamble_checkpoint_is_inconclusive_and_names_its_phase() {
    // Sweep the poll count so each checkpoint is reached in turn. Every observed
    // verdict must be Inconclusive and NEVER a decision; the phases actually
    // reached are collected and required to cover the preamble, so a checkpoint
    // that stops being polled fails here rather than silently going unwatched.
    let environment = nat_environment();
    let candidate = axiom("A");
    let mut seen: Vec<AdmissionPhase> = Vec::new();
    let mut nested = 0_u32;

    // Swept well past the run's own poll count: inference consumes an unknown
    // number of polls between the DeclaredType and DeclaredTypeSort checkpoints,
    // so a sweep sized to the preamble alone can never reach the later ones.
    for budgeted_polls in 0..64_u32 {
        let polls = Cell::new(0_u32);
        let verdict = admit_with(
            &environment,
            &candidate,
            AdmissionBudget::unlimited(),
            || {
                let seen_so_far = polls.get();
                polls.set(seen_so_far + 1);
                seen_so_far >= budgeted_polls
            },
        );
        match verdict {
            Verdict::Inconclusive(AdmissionStop::Cancelled { name, phase }) => {
                assert_eq!(name, checker_name("A"));
                if !seen.contains(&phase) {
                    seen.push(phase);
                }
            }
            // Cancellation observed INSIDE a nested engine. The poll is handed
            // to `infer_with` and `whnf_with` rather than only checked between
            // them, so a long declared-type inference is interruptible; these
            // are the outcomes that prove it.
            Verdict::Inconclusive(
                AdmissionStop::DeclaredTypeInference { .. }
                | AdmissionStop::DeclaredTypeSortWhnf { .. },
            ) => nested += 1,
            Verdict::Admitted(_) => {
                // The poll budget outlived the run; the only non-stop outcome
                // permitted here.
            }
            other => panic!(
                "cancellation must be INCONCLUSIVE, never a decision or a fault: \
                 at {budgeted_polls} polls got {other:?}"
            ),
        }
    }

    assert!(
        nested > 0,
        "cancellation was never observed inside a nested engine, so the poll is \
         not actually reaching inference and a long declared-type check would \
         run to completion regardless"
    );

    for required in [
        AdmissionPhase::UniqueName,
        AdmissionPhase::LevelParameters,
        AdmissionPhase::DeclaredType,
        AdmissionPhase::DeclaredTypeSort,
        AdmissionPhase::Terminal,
    ] {
        assert!(
            seen.contains(&required),
            "no cancellation was observed at {required:?}; a checkpoint that is \
             never reached is a checkpoint that is not there. Reached: {seen:?}"
        );
    }
}

#[test]
fn an_exhausted_declared_type_budget_is_inconclusive_never_rejected() {
    // Resource exhaustion is not a verdict. A budget of zero steps must produce
    // the inconclusive arm carrying inference's own stop, not a rejection that
    // a caller would read as "this declaration is bad".
    let starved = AdmissionBudget::new(
        InferenceBudget::new(0, 0, TermBudget::unlimited(), TermBudget::unlimited()),
        WhnfBudget::unlimited(),
    );
    let verdict = admit(&ConstantEnvironment::empty(), &axiom("A"), starved);
    match verdict {
        Verdict::Inconclusive(AdmissionStop::DeclaredTypeInference { name, .. }) => {
            assert_eq!(name, checker_name("A"));
        }
        other => panic!("an exhausted budget must be INCONCLUSIVE, got {other:?}"),
    }

    // Control: the identical candidate under an unlimited budget is admitted, so
    // the stop above is the budget and not the declaration.
    assert!(
        admit(
            &ConstantEnvironment::empty(),
            &axiom("A"),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "the same candidate must be admitted when the budget allows it"
    );
}

#[test]
fn the_three_non_answers_are_never_reported_as_admitted() {
    // The FL-INV-07 conservation property stated directly: `is_admitted` and
    // `is_inconclusive_family` must never both hold, over every verdict this
    // suite can produce.
    let starved = AdmissionBudget::new(
        InferenceBudget::new(0, 0, TermBudget::unlimited(), TermBudget::unlimited()),
        WhnfBudget::unlimited(),
    );
    let unsafe_axiom = ConstantEntry::new(
        checker_name("U"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    );
    let verdicts = vec![
        admit(
            &ConstantEnvironment::empty(),
            &axiom("A"),
            AdmissionBudget::unlimited(),
        ),
        admit(
            &environment_of(vec![axiom("A")]),
            &axiom("A"),
            AdmissionBudget::unlimited(),
        ),
        admit(
            &ConstantEnvironment::empty(),
            &unsafe_axiom,
            AdmissionBudget::unlimited(),
        ),
        admit(&ConstantEnvironment::empty(), &axiom("A"), starved),
    ];
    let mut admitted = 0;
    for verdict in &verdicts {
        assert!(
            !(verdict.is_admitted() && verdict.is_inconclusive_family()),
            "a verdict may not be both admitted and a non-answer: {verdict:?}"
        );
        if verdict.is_admitted() {
            admitted += 1;
        }
    }
    assert_eq!(
        admitted, 1,
        "exactly one of these four is a genuine admission; a cell where nothing \
         is ever admitted satisfies the property above vacuously"
    );
}

// --------------------------------------------------------------- FL-INV-02

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels below the workspace root")
        .to_path_buf()
}

/// Needles assembled from parts so this scanner's OWN source cannot satisfy the
/// scan it performs — the self-exclusion trap this repository has paid for.
fn laundering_needles() -> Vec<String> {
    let from = String::from("impl ") + "From<";
    vec![
        from.clone() + "Admission>",
        from + "Verdict>",
        String::from("-> ") + "ConstantEntry",
        String::from("-> ") + "ConstantDeclaration",
        String::from("#[derive") + "(Clone)]",
    ]
}

/// Strip the `//`-comment tail of a line, so prose *describing* a forbidden
/// shape is not scored as the shape itself.
fn code_only(line: &str) -> &str {
    match line.find("//") {
        Some(at) => &line[..at],
        None => line,
    }
}

fn laundering_hits(source: &str) -> Vec<String> {
    let mut hits = Vec::new();
    for line in source.lines() {
        let code = code_only(line);
        for needle in laundering_needles() {
            if code.contains(&needle) {
                hits.push(format!("{needle} :: {}", code.trim()));
            }
        }
    }
    hits
}

#[test]
fn the_admission_verdict_is_not_a_capability() {
    // FL-INV-02: fln-checker is an evidence seat, never an alternative admission
    // authority. Two independent halves, because either alone is defeatable.

    // HALF 1 -- the structural fact, derived from the real manifest. No type
    // fln-kernel's admission consumes is even nameable here.
    let manifest = std::fs::read_to_string(workspace_root().join("crates/fln-checker/Cargo.toml"))
        .expect("fln-checker's manifest is readable");
    assert!(
        !manifest.contains("fln-kernel"),
        "fln-checker must not depend on fln-kernel, in any dependency table"
    );
    // Anti-vacuity: a manifest this scan could not read, or one that declares
    // nothing, would satisfy the assertion above while proving nothing.
    assert!(
        manifest.contains("fln-core"),
        "the manifest scan found no known dependency, so it is a broken scan \
         rather than a clean result"
    );

    // HALF 2 -- the surface itself carries no way out.
    let admit_source =
        std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/admit.rs"))
            .expect("the admission module is readable");
    let hits = laundering_hits(&admit_source);
    assert!(
        hits.is_empty(),
        "the admission surface must expose no conversion out of a verdict and no \
         Clone on one: {hits:?}"
    );

    // The scan must be shown CAPABLE of firing, or its empty result means
    // nothing. A decoy carrying each forbidden shape is scored by the same
    // function, and every needle must be found.
    let decoy = laundering_needles()
        .iter()
        .map(|needle| format!("    {needle} Admission {{ }}\n"))
        .collect::<String>();
    assert_eq!(
        laundering_hits(&decoy).len(),
        laundering_needles().len(),
        "the laundering scan did not fire on a planted decoy, so its clean \
         result on the real module is vacuous"
    );

    // And prose must NOT be scored, or the guard reddens on its own doc comment.
    let commented = laundering_needles()
        .iter()
        .map(|needle| format!("    // there is no {needle} here\n"))
        .collect::<String>();
    assert!(
        laundering_hits(&commented).is_empty(),
        "a comment describing a forbidden shape must not be scored as one"
    );
}

#[test]
fn an_axiom_cannot_be_constructed_with_a_body() {
    // `admit` deliberately carries NO "an axiom must not have a body" check,
    // because the state is unconstructible and an unreachable branch is one no
    // mutation can kill. That is a claim about `environment.rs`, so it is bound
    // here: the day a constructor lands that could produce the state, this fails
    // and the missing check becomes owed.
    let source =
        std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/environment.rs"))
            .expect("the environment module is readable");
    let declaration_impl = source
        .split_once("impl ConstantDeclaration {")
        .expect("ConstantDeclaration has an impl block")
        .1
        .split_once("\n}\n")
        .expect("that impl block ends")
        .0;
    let constructors: Vec<&str> = declaration_impl
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("pub fn ") || line.starts_with("pub const fn "))
        .filter(|line| line.contains("-> ConstantDeclaration") || line.ends_with('('))
        .filter(|line| !line.contains("(&self)"))
        .collect();
    assert_eq!(
        constructors.len(),
        2,
        "ConstantDeclaration gained or lost a constructor, so the reachability \
         of an axiom-with-a-body must be re-measured: {constructors:?}"
    );
    assert!(
        constructors
            .iter()
            .any(|line| line.contains("pub fn header(")),
        "expected the header constructor: {constructors:?}"
    );
    assert!(
        constructors
            .iter()
            .any(|line| line.contains("pub fn definition(")),
        "expected the definition constructor: {constructors:?}"
    );
    // `header` is the only constructor reachable with `ConstantKind::Axiom`, and
    // it hardcodes an absent body; `definition` hardcodes the Definition kind.
    assert!(
        declaration_impl.contains("definition: None,"),
        "the header constructor no longer hardcodes an absent definition body"
    );
    assert!(
        declaration_impl.contains("kind: ConstantKind::Definition,"),
        "the definition constructor no longer hardcodes the Definition kind"
    );
}
