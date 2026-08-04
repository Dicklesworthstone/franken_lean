//! Cross-boundary mutants for the complete Verdict `bv_decide` path.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::mode::{Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_kernel::verdict::RejectClass;
use fln_verdict::{
    BitblastLimits, BitblastOutcome, BitblastRefusal, BitblastSymbol, BoolExpr, BvComparison,
    BvDecideInputValue, BvDecideInternalFault, BvDecideLimits, BvDecideOutcome, BvDecideRefusal,
    BvDecideRequest, BvExpr, ProofCheckLimits, ProofCheckOutcome, ProofRefusal,
    ReflectedTheoremRefusal, SolverLimits, SolverOutcome, UnsupportedBvOp, bitblast, bv_decide,
    check_unsat_streams, solve,
};

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn sort_zero() -> Expr {
    Expr::sort(Level::zero())
}

fn identity_type() -> Expr {
    Expr::forall_e(
        name("p"),
        sort_zero(),
        Expr::forall_e(
            name("h"),
            Expr::bvar(0).expect("test bound variable is in range"),
            Expr::bvar(1).expect("test bound variable is in range"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    )
}

fn identity_proof() -> Expr {
    Expr::lam(
        name("p"),
        sort_zero(),
        Expr::lam(
            name("h"),
            Expr::bvar(0).expect("test bound variable is in range"),
            Expr::bvar(0).expect("test bound variable is in range"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    )
}

fn request(proposition: BoolExpr, theorem: &str) -> BvDecideRequest {
    BvDecideRequest::new(
        proposition,
        name(theorem),
        vec![],
        identity_type(),
        identity_proof(),
        Mode::Sound,
        ReproducibilityProfile::Standard,
    )
}

#[test]
fn translation_mutant_that_skips_negation_is_killed() {
    let environment = Environment::new();
    let correct = bv_decide(
        &environment,
        request(BoolExpr::Constant(true), "bv.mutant.negation"),
        BvDecideLimits::default(),
    );
    assert!(
        matches!(correct, BvDecideOutcome::Proved(_)),
        "the negation of true must be certified UNSAT"
    );

    let BitblastOutcome::Complete(mutant_cnf) =
        bitblast(&BoolExpr::Constant(true), BitblastLimits::default())
    else {
        panic!("the planted no-negation translation must complete");
    };
    assert!(
        matches!(
            solve(mutant_cnf.cnf(), SolverLimits::default()),
            SolverOutcome::Sat { .. }
        ),
        "the planted translation mutant must change the terminal class"
    );
}

#[test]
fn proof_mutant_is_refused_by_the_independent_checker() {
    let BitblastOutcome::Complete(bitblast) =
        bitblast(&BoolExpr::Constant(false), BitblastLimits::default())
    else {
        panic!("false must bitblast");
    };
    let SolverOutcome::Unsat { artifact, .. } = solve(bitblast.cnf(), SolverLimits::default())
    else {
        panic!("false must produce a checked UNSAT artifact");
    };
    assert!(matches!(
        check_unsat_streams(
            artifact.cnf_bytes(),
            artifact.proof_bytes(),
            ProofCheckLimits::default()
        ),
        ProofCheckOutcome::Verified(_)
    ));

    let mut corrupted = artifact.proof_bytes().to_vec();
    corrupted[0] ^= 0xff;
    assert!(matches!(
        check_unsat_streams(
            artifact.cnf_bytes(),
            corrupted.as_slice(),
            ProofCheckLimits::default()
        ),
        ProofCheckOutcome::Refused(ProofRefusal::InvalidMagic { .. })
    ));
}

#[test]
fn reflected_term_mutant_is_refused_by_the_kernel() {
    let environment = Environment::new();
    let invalid = BvDecideRequest::new(
        BoolExpr::Constant(true),
        name("bv.mutant.reflection"),
        vec![],
        Expr::sort(Level::one()),
        sort_zero(),
        Mode::Sound,
        ReproducibilityProfile::Standard,
    );
    let outcome = bv_decide(&environment, invalid, BvDecideLimits::default());

    assert!(matches!(
        outcome,
        BvDecideOutcome::Refused(BvDecideRefusal::Reflection(
            ReflectedTheoremRefusal::Kernel {
                class: RejectClass::TheoremNotProp,
                ..
            }
        ))
    ));
    assert!(environment.is_empty());
}

#[test]
fn unsupported_construct_is_refused_before_solver_or_publication() {
    let unsupported = BoolExpr::compare(
        BvComparison::Equal,
        BvExpr::unsupported(UnsupportedBvOp::RotateLeft, 1),
        BvExpr::constant(vec![false]),
    );
    let environment = Environment::new();
    let outcome = bv_decide(
        &environment,
        request(unsupported, "bv.mutant.unsupported"),
        BvDecideLimits::default(),
    );

    assert!(matches!(
        outcome,
        BvDecideOutcome::Refused(BvDecideRefusal::Bitblast(
            BitblastRefusal::UnsupportedConstruct { .. }
        ))
    ));
    assert!(environment.is_empty());
}

#[test]
fn sat_negation_returns_an_independently_checked_counterexample_only() {
    let symbol = BitblastSymbol::new(1).expect("test symbol is nonzero");
    let environment = Environment::new();
    let outcome = bv_decide(
        &environment,
        request(BoolExpr::Input(symbol), "bv.counterexample"),
        BvDecideLimits::default(),
    );
    let BvDecideOutcome::Counterexample(counterexample) = outcome else {
        panic!("a free Boolean proposition must have a counterexample");
    };

    assert_eq!(
        counterexample.input(symbol),
        Some(&BvDecideInputValue::Boolean(false))
    );
    assert!(!counterexample.cnf_bytes().is_empty());
    assert!(!counterexample.model_bytes().is_empty());
    assert!(environment.is_empty());
}

#[test]
fn every_internal_fault_shape_is_structurally_nonpublishing() {
    let outcome =
        BvDecideOutcome::InternalFault(BvDecideInternalFault::SatModelDoesNotSatisfyNegation);
    assert!(outcome.publication().is_none());
    assert!(outcome.counterexample().is_none());
}

#[test]
fn orchestration_source_has_no_unchecked_authority_route() {
    let source = include_str!("../src/bv_decide.rs");
    assert!(!source.contains("std::process::Command"));
    assert!(!source.contains(concat!("fln_kernel::", "check(")));
    assert!(!source.contains(concat!(".plan_", "add_decl(")));
    assert!(source.contains("publish_reflected_theorem("));
}
