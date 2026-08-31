//! **fln-anvil** — Anvil — the simp core on compiled discrimination-automata
//! rewrite indexes, the e-graph saturation lane with kernel-checked extraction,
//! and the `norm_num`/`omega` cores (plan §12).
//!
//! Anvil is an **untrusted accelerator**: every rewrite, simplification, and
//! decision-procedure result is a candidate that must cross Crucible's sole
//! kernel check authority before entering the environment. FL-INV-06 governs
//! this boundary.
//!
//! # Subsystems
//!
//! * **`simp`** — faithful `simp`/`dsimp`/`simp only` over discrimination-tree
//!   lookup, congruence closure, and attribute-driven extension sets (§12.1).
//! * **`dtree`** — compiled discrimination-tree automata shipped as per-library
//!   CAS indexes; the lookup substrate for `simp` and `aesop` (§12.2).
//! * **`egraph`** — equality-saturation lane over `simp`-set subsets with
//!   kernel-checked proof extraction (§12.3).
//! * **`norm_num`** — `norm_num`-class numeric evaluation with certificate
//!   production (§12.4).
//! * **`omega`** — `omega`-class linear-arithmetic decision procedure (§12.4).
//! * **`grind`** — congruence closure, e-matching, and pluggable theory hooks
//!   (§12.6).
//! * **`portfolio`** — speculative tactic racing with deterministic winner
//!   selection through structured-concurrency regions (§12.7).
//!
//! Verdict (§12.5) lives in its own crate `fln-verdict` at rank 13.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fmt;

use fln_core::expr::Expr;
use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §12.1 — simp driver
// ---------------------------------------------------------------------------

/// Transparency mode governing how `simp` unfolds definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Transparency {
    /// Unfold all definitions (default `simp`).
    All,
    /// Unfold only reducible definitions.
    Reducible,
    /// Unfold only instance-relevant definitions.
    Instances,
    /// No unfolding (`dsimp`-like behavior).
    None,
}

/// A single oriented rewrite rule in a `SimpSet`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpRule {
    /// Fully qualified name of the lemma backing this rule.
    pub name: Name,
    /// Universe parameters bound in this rule.
    pub level_params: Vec<Name>,
    /// Left-hand side pattern (the discrimination-tree key).
    pub lhs: Expr,
    /// Right-hand side replacement.
    pub rhs: Expr,
    /// Proof term witnessing `lhs = rhs` (or `lhs ↔ rhs`).
    pub proof: Expr,
    /// Priority for rule ordering (lower fires first).
    pub priority: u32,
}

/// A configured set of rewrite rules driving `simp`.
#[derive(Debug, Clone)]
pub struct SimpSet {
    /// Named rules keyed by their lemma name.
    pub rules: BTreeMap<Name, SimpRule>,
}

/// Configuration for a `simp` invocation.
#[derive(Debug, Clone)]
pub struct SimpConfig {
    /// Which definitions to unfold.
    pub transparency: Transparency,
    /// Maximum number of rewrite steps before declaring inconclusive.
    pub max_steps: u64,
    /// Whether to use congruence closure.
    pub use_congruence: bool,
    /// `simp only` mode: restrict to the named rules.
    pub only: bool,
}

impl Default for SimpConfig {
    fn default() -> Self {
        Self {
            transparency: Transparency::All,
            max_steps: 1_000_000,
            use_congruence: true,
            only: false,
        }
    }
}

/// Outcome of a `simp` invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpOutcome {
    /// Successfully simplified to a new expression with a proof.
    Simplified {
        result: Expr,
        proof: Expr,
        steps: u64,
    },
    /// The expression was already in normal form under the given rules.
    Unchanged,
    /// Budget exhausted before completing.
    Inconclusive { steps_used: u64, limit: u64 },
}

// ---------------------------------------------------------------------------
// §12.2 — discrimination-tree indexes
// ---------------------------------------------------------------------------

/// A key in the discrimination tree, representing a flattened term pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DTreeKey {
    /// A constant head (fully qualified name + arity).
    Const { name: Name, arity: u32 },
    /// A bound variable (de Bruijn index in the pattern).
    BVar(u32),
    /// A wildcard matching any subterm.
    Star,
    /// A literal value.
    Literal(DTreeLiteral),
}

/// Literal values in discrimination-tree keys.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DTreeLiteral {
    Nat(u64),
    String(String),
}

/// A compiled discrimination-tree automaton for fast rule lookup.
///
/// Per-library indexes are shipped as CAS artifacts (olean-next attachments)
/// and loaded at elaboration time. The content hash of the backing `SimpSet`
/// determines cache identity.
#[derive(Debug, Clone)]
pub struct DiscriminationTree {
    /// Content hash of the `SimpSet` this tree was compiled from.
    pub source_hash: [u8; 32],
    /// Number of rules indexed.
    pub rule_count: u32,
    /// The serialized automaton state (format is version-tagged).
    pub automaton: Vec<u8>,
}

// ---------------------------------------------------------------------------
// §12.3 — e-graph saturation lane
// ---------------------------------------------------------------------------

/// An opaque e-class identifier within an e-graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EClassId(pub u32);

/// An e-node: a term head with children represented as e-class IDs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ENode {
    /// The head symbol.
    pub head: Name,
    /// Children, each an e-class.
    pub children: Vec<EClassId>,
}

/// A recorded rewrite step for proof extraction from the e-graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteJustification {
    /// The rule that fired.
    pub rule: Name,
    /// Source e-class.
    pub from: EClassId,
    /// Target e-class.
    pub to: EClassId,
}

/// Configuration for e-graph saturation.
#[derive(Debug, Clone)]
pub struct EGraphConfig {
    /// Maximum number of saturation iterations.
    pub max_iterations: u32,
    /// Maximum number of e-nodes before stopping.
    pub max_enodes: u32,
}

impl Default for EGraphConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            max_enodes: 100_000,
        }
    }
}

/// Outcome of e-graph saturation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EGraphOutcome {
    /// Found a proof path between two expressions.
    ProofFound {
        justifications: Vec<RewriteJustification>,
    },
    /// Saturated without finding a connection.
    Saturated { iterations: u32, enodes: u32 },
    /// Resource limit reached.
    Inconclusive { iterations: u32, enodes: u32 },
}

// ---------------------------------------------------------------------------
// §12.4 — norm_num / omega
// ---------------------------------------------------------------------------

/// Outcome of `norm_num` evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NormNumOutcome {
    /// Successfully normalized to a numeral with a proof.
    Normalized { result: Expr, proof: Expr },
    /// Expression is not a supported numeric form.
    Unsupported,
    /// Budget exhausted.
    Inconclusive,
}

/// A linear constraint for `omega`: `coeffs[0]*x0 + coeffs[1]*x1 + ... ≤ bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearConstraint {
    /// Coefficients, indexed by variable ordinal.
    pub coeffs: Vec<i64>,
    /// Upper bound of the constraint.
    pub bound: i64,
}

/// Outcome of the `omega` decision procedure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OmegaOutcome {
    /// The system is unsatisfiable; proof certificate attached.
    Unsat { certificate: Vec<u8> },
    /// The system is satisfiable; a witness is attached.
    Sat { witness: Vec<i64> },
    /// Budget or scope exceeded.
    Inconclusive,
}

// ---------------------------------------------------------------------------
// §12.6 — grind (congruence closure + e-matching + theories)
// ---------------------------------------------------------------------------

/// A theory-hook identifier for pluggable `grind` extensions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TheoryHookId(pub Name);

/// Outcome of the `grind` tactic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrindOutcome {
    /// Closed the goal with a proof.
    Proved { proof: Expr },
    /// Simplified the goal but did not close it.
    Simplified { new_goal: Expr },
    /// No progress was made.
    Stuck,
    /// Budget exhausted.
    Inconclusive { steps_used: u64 },
}

// ---------------------------------------------------------------------------
// §12.7 — portfolio / speculative tactic racing
// ---------------------------------------------------------------------------

/// Policy for selecting the winner among speculative tactic runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RacingPolicy {
    /// First to succeed wins; losers are cancelled.
    FirstSuccess,
    /// All run to completion; shortest proof wins.
    ShortestProof,
}

/// Outcome of a portfolio race.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PortfolioOutcome {
    /// A tactic won the race.
    Winner {
        /// Index of the winning tactic in the input list.
        index: usize,
        /// The proof produced by the winner.
        proof: Expr,
    },
    /// All tactics failed or were inconclusive.
    AllFailed,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for Transparency {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::All => write!(f, "all"),
            Self::Reducible => write!(f, "reducible"),
            Self::Instances => write!(f, "instances"),
            Self::None => write!(f, "none"),
        }
    }
}

impl fmt::Display for EClassId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.0)
    }
}

impl fmt::Display for SimpOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Simplified { steps, .. } => write!(f, "simplified in {steps} steps"),
            Self::Unchanged => write!(f, "unchanged"),
            Self::Inconclusive {
                steps_used, limit, ..
            } => write!(f, "inconclusive ({steps_used}/{limit} steps)"),
        }
    }
}
