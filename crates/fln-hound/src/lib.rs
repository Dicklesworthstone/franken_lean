//! **fln-hound** — Bloodhound — in-toolchain library search: lexical + semantic
//! over statements, names, docstrings, and simp/instance membership, indexed
//! incrementally at Ledger commit (plan §16.1).
//!
//! Bloodhound serves `exact?`/`apply?`-class premise retrieval as a candidate
//! generator whose candidates are verified by actual elaboration — ranking is
//! UX, proofs are proofs. Results arrive as `CandidateCard`s in three grades:
//! **initial** (low-latency lexical channels), **refined** (structural
//! unification + graph ranking), and **verified** (kernel-accepted under the
//! exact snapshot).
//!
//! The search substrate is `frankensearch` (two-tier hybrid lexical+semantic);
//! graph ranking uses `franken_networkx` over Palimpsest causal-graph cones.

#![forbid(unsafe_code)]

use std::fmt;

use fln_core::expr::Expr;
use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §16.1 — candidate cards
// ---------------------------------------------------------------------------

/// A search result card returned by Bloodhound.
#[derive(Debug, Clone)]
pub struct CandidateCard {
    /// Fully qualified name of the candidate lemma/definition.
    pub name: Name,
    /// The candidate's type (statement).
    pub statement: Expr,
    /// Which retrieval channels contributed to finding this candidate.
    pub channels: Vec<RetrievalChannel>,
    /// Current grade of this candidate.
    pub grade: CandidateGrade,
    /// Rank score (higher is better).
    pub score: f64,
    /// Required imports to use this candidate.
    pub required_imports: Vec<Name>,
    /// Required instances that must be synthesized.
    pub required_instances: Vec<Name>,
    /// Optional docstring excerpt.
    pub docstring: Option<String>,
}

/// The grade of a candidate, reflecting how thoroughly it has been validated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CandidateGrade {
    /// Low-latency results from lexical / type-head / local-context channels.
    Initial,
    /// Structural unification, graph ranking, prior-use paths applied.
    Refined,
    /// Kernel-accepted under the exact elaboration snapshot.
    Verified,
}

/// A retrieval channel that contributed to finding a candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RetrievalChannel {
    /// Full-text search over declaration names.
    NameLexical,
    /// Full-text search over docstrings.
    DocstringLexical,
    /// Semantic embedding similarity.
    SemanticEmbedding,
    /// Type-head / discrimination-tree pattern match.
    TypeHead,
    /// Local context type-directed search.
    LocalContext,
    /// Instance membership lookup.
    InstanceMembership,
    /// Simp lemma membership.
    SimpMembership,
    /// Prior-use frequency in the current project.
    PriorUse,
    /// Loogle-style structural pattern match.
    TypeShapeFingerprint,
}

// ---------------------------------------------------------------------------
// §16.1 — search queries
// ---------------------------------------------------------------------------

/// A search query submitted to Bloodhound.
#[derive(Debug, Clone)]
pub struct SearchQuery {
    /// The query kind.
    pub kind: SearchQueryKind,
    /// Maximum number of candidates to return.
    pub limit: u32,
    /// Minimum grade to return (candidates below this are filtered).
    pub min_grade: CandidateGrade,
    /// Whether to attempt verification (kernel check) on refined candidates.
    pub verify: bool,
}

/// The kind of search query.
#[derive(Debug, Clone)]
pub enum SearchQueryKind {
    /// Free-text search over names and docstrings.
    Text(String),
    /// Type-directed search: find lemmas whose conclusion unifies with the
    /// given type pattern.
    TypeDirected {
        /// The goal type to search for.
        goal: Expr,
    },
    /// `exact?`-style: find a term of exactly the given type.
    Exact {
        /// The exact type to match.
        target: Expr,
    },
    /// `apply?`-style: find lemmas applicable to the given goal.
    Apply {
        /// The goal to close.
        goal: Expr,
    },
    /// Loogle-style structural pattern.
    TypePattern(String),
}

// ---------------------------------------------------------------------------
// §16.1 — search outcomes
// ---------------------------------------------------------------------------

/// Outcome of a Bloodhound search.
#[derive(Debug, Clone)]
pub struct SearchOutcome {
    /// Candidates found, ordered by score (descending).
    pub candidates: Vec<CandidateCard>,
    /// Total number of candidates before the limit was applied.
    pub total_matches: u64,
    /// Time spent in each search phase (nanoseconds).
    pub timing: SearchTiming,
}

/// Timing breakdown for a search operation.
#[derive(Debug, Clone, Copy)]
pub struct SearchTiming {
    /// Lexical retrieval phase (nanoseconds).
    pub lexical_ns: u64,
    /// Semantic retrieval phase (nanoseconds).
    pub semantic_ns: u64,
    /// Structural unification / refinement phase (nanoseconds).
    pub refinement_ns: u64,
    /// Kernel verification phase (nanoseconds, 0 if verification was skipped).
    pub verification_ns: u64,
}

// ---------------------------------------------------------------------------
// §16.1 — proof repair
// ---------------------------------------------------------------------------

/// A proof repair proposal from Bloodhound's repair pipeline.
#[derive(Debug, Clone)]
pub struct RepairProposal {
    /// The declaration whose proof broke.
    pub declaration: Name,
    /// Replacement candidates, each with a confidence score.
    pub replacements: Vec<RepairCandidate>,
}

/// A single repair candidate.
#[derive(Debug, Clone)]
pub struct RepairCandidate {
    /// The replacement term/tactic.
    pub replacement: Expr,
    /// Confidence score (0.0–1.0).
    pub confidence: f64,
    /// Whether the replacement has been kernel-verified.
    pub verified: bool,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for CandidateGrade {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Initial => write!(f, "initial"),
            Self::Refined => write!(f, "refined"),
            Self::Verified => write!(f, "verified"),
        }
    }
}

impl fmt::Display for RetrievalChannel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::NameLexical => "name-lexical",
            Self::DocstringLexical => "docstring-lexical",
            Self::SemanticEmbedding => "semantic-embedding",
            Self::TypeHead => "type-head",
            Self::LocalContext => "local-context",
            Self::InstanceMembership => "instance-membership",
            Self::SimpMembership => "simp-membership",
            Self::PriorUse => "prior-use",
            Self::TypeShapeFingerprint => "type-shape-fingerprint",
        };
        write!(f, "{name}")
    }
}
