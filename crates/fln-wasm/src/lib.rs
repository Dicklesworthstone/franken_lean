//! **fln-wasm** — the WASM Judge: K1 + fln-checker + the sealed-capsule
//! verifier compiled to a single WASM artifact (plan §16.4b).
//!
//! The WASM Judge enables zero-install third-party verification: anyone with
//! a browser can independently verify FrankenLean proof certificates without
//! trusting the build machine. The artifact contains:
//!
//! - The trusted K1 kernel (§9).
//! - The independent checker (fln-checker).
//! - The capsule verifier: opens a sealed `.flnproof` capsule, replays
//!   declarations against K1, and produces a typed verdict.
//!
//! The WASM module exposes a small, stable C-ABI surface (`verify_capsule`,
//! `get_verdict`, `free_verdict`) that the host page calls via the standard
//! WebAssembly instantiation path. No JavaScript framework, no network
//! requests, no persistent state.

#![forbid(unsafe_code)]

use std::fmt;

use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §16.4b — capsule format
// ---------------------------------------------------------------------------

/// Magic bytes at the start of a `.flnproof` capsule.
pub const CAPSULE_MAGIC: &[u8; 8] = b"FLNPRF\x00\x01";

/// A sealed proof capsule ready for verification.
#[derive(Debug, Clone)]
pub struct SealedCapsule {
    /// Content hash of the capsule (for integrity check).
    pub content_hash: [u8; 32],
    /// Number of declarations in the capsule.
    pub declaration_count: u32,
    /// Axiom set fingerprint (must match the verifier's expected axiom set).
    pub axiom_fingerprint: [u8; 16],
    /// Compressed declaration payload size in bytes.
    pub payload_bytes: u64,
}

/// Capsule format error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapsuleError {
    /// Magic bytes do not match.
    BadMagic,
    /// Integrity check failed.
    IntegrityMismatch {
        expected: [u8; 32],
        observed: [u8; 32],
    },
    /// Unsupported capsule version.
    UnsupportedVersion(u8),
    /// Payload exceeds the verification budget.
    PayloadTooLarge {
        observed: u64,
        limit: u64,
    },
    /// Axiom fingerprint does not match the verifier's expected set.
    AxiomMismatch,
    /// Truncated or malformed capsule.
    Truncated,
}

impl fmt::Display for CapsuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadMagic => write!(f, "not a valid .flnproof capsule"),
            Self::IntegrityMismatch { .. } => write!(f, "capsule integrity check failed"),
            Self::UnsupportedVersion(v) => write!(f, "unsupported capsule version {v}"),
            Self::PayloadTooLarge { observed, limit } => {
                write!(f, "payload {observed} bytes exceeds limit {limit}")
            }
            Self::AxiomMismatch => write!(f, "axiom fingerprint mismatch"),
            Self::Truncated => write!(f, "truncated or malformed capsule"),
        }
    }
}

// ---------------------------------------------------------------------------
// §16.4b — verification verdict
// ---------------------------------------------------------------------------

/// The outcome of capsule verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Every declaration in the capsule was accepted by K1.
    Accepted {
        /// Number of declarations verified.
        declarations: u32,
    },
    /// K1 rejected one or more declarations.
    Rejected {
        /// Name of the first rejected declaration.
        first_rejection: Name,
        /// Total rejections found before the budget was exhausted.
        rejection_count: u32,
    },
    /// Verification could not complete within the budget.
    Inconclusive {
        /// Declarations verified before exhaustion.
        verified_so_far: u32,
        /// Reason for early termination.
        reason: String,
    },
    /// The capsule itself is malformed.
    Malformed(CapsuleError),
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accepted { declarations } => {
                write!(f, "accepted: {declarations} declarations verified")
            }
            Self::Rejected {
                first_rejection,
                rejection_count,
            } => {
                write!(
                    f,
                    "rejected: {rejection_count} rejections (first: {first_rejection:?})"
                )
            }
            Self::Inconclusive {
                verified_so_far,
                reason,
            } => {
                write!(
                    f,
                    "inconclusive: {verified_so_far} verified, stopped: {reason}"
                )
            }
            Self::Malformed(error) => write!(f, "malformed capsule: {error}"),
        }
    }
}

// ---------------------------------------------------------------------------
// §16.4b — verification budget
// ---------------------------------------------------------------------------

/// Resource budget for WASM verification.
#[derive(Debug, Clone, Copy)]
pub struct VerificationBudget {
    /// Maximum declarations to verify.
    pub max_declarations: u32,
    /// Maximum payload bytes to decompress.
    pub max_payload_bytes: u64,
    /// Maximum kernel reduction steps.
    pub max_steps: u64,
}

impl Default for VerificationBudget {
    fn default() -> Self {
        Self {
            max_declarations: 100_000,
            max_payload_bytes: 256 * 1024 * 1024,
            max_steps: 100_000_000,
        }
    }
}
