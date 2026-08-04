//! **fln-verdict** — Verdict — the owned CDCL SAT solver with owned proof logging and
//! an owned proof checker behind `bv_decide`; the external-solver TCB, gone (plan
//! §12.5).
//!
//! The first implemented boundary is deliberately narrower than the final solver:
//! validated canonical CNF/model/LRAT-shaped artifacts, a bounded streaming codec,
//! and an outcome algebra which cannot promote cancellation, exhaustion, or an
//! internal fault to SAT/UNSAT. Proof semantic checking remains a separate authority.

#![forbid(unsafe_code)]

pub mod codec;
pub mod schema;

pub use codec::{
    CancellationProbe, NeverCancelled, VerdictCodecError, decode_cnf, decode_sat_model,
    decode_unsat_proof, decode_unsat_proof_with_cancellation, encode_cnf, encode_sat_model,
    encode_unsat_proof,
};
pub use schema::{
    CanonicalClause, CanonicalCnf, ClauseId, CnfRoot, InconclusiveReason, InternalFault, Literal,
    Polarity, ProofAction, RatHint, SatModel, SatModelRoot, SolverResource, SolverUsage,
    UnsatProof, UnsatProofRoot, UntrustedArtifactRef, UntrustedSolverOutcome, VariableId,
    VerdictError, VerdictFacts, VerdictLimits, VerdictResource,
};
