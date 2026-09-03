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

use fln_core::expr::{Expr, ExprNode, Literal};
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

impl DTreeKey {
    /// The number of immediate child subterms this key's node carries in a
    /// flattened preorder sequence: a `Const` head is followed by exactly `arity`
    /// child subterms; every other key is a leaf.
    const fn arity(&self) -> u32 {
        match self {
            DTreeKey::Const { arity, .. } => *arity,
            DTreeKey::BVar(_) | DTreeKey::Star | DTreeKey::Literal(_) => 0,
        }
    }
}

/// Literal values in discrimination-tree keys.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

/// Flatten an expression into the preorder discrimination-tree key sequence that
/// [`DTree`] indexes and queries.
///
/// This is the first-order approximation Lean's discrimination trees use: a
/// constant-headed application `f a₁ … aₙ` becomes
/// `[Const{f, n}, ⟨a₁⟩, …, ⟨aₙ⟩]`; a bare constant is `Const{name, 0}`; a bound
/// variable keeps its de Bruijn index; a `Nat`/`String` literal becomes a
/// `Literal`; and everything a first-order key cannot name precisely —
/// metavariables, free variables, sorts, binders, projections, a `Nat` literal
/// too large for `u64`, and a non-constant application head — collapses to
/// [`DTreeKey::Star`], which matches any subterm. `MData` wrappers are
/// transparent. Over-approximating with `Star` keeps retrieval sound as a
/// pre-filter: it never drops a genuine match, it only admits extra candidates
/// the caller confirms with real unification.
pub fn flatten(expr: &Expr) -> Vec<DTreeKey> {
    let mut keys = Vec::new();
    let mut stack = vec![expr];
    while let Some(mut current) = stack.pop() {
        while let ExprNode::MData { expr, .. } = current.node() {
            current = expr;
        }
        match current.node() {
            ExprNode::App { .. } => {
                let (head, arguments) = unwind_application(current);
                if let ExprNode::Const { name, .. } = head.node() {
                    keys.push(DTreeKey::Const {
                        name: name.clone(),
                        arity: u32::try_from(arguments.len()).unwrap_or(u32::MAX),
                    });
                    for argument in arguments.into_iter().rev() {
                        stack.push(argument);
                    }
                } else {
                    keys.push(DTreeKey::Star);
                }
            }
            ExprNode::Const { name, .. } => keys.push(DTreeKey::Const {
                name: name.clone(),
                arity: 0,
            }),
            ExprNode::BVar { idx } => keys.push(DTreeKey::BVar(*idx)),
            ExprNode::Lit { literal } => keys.push(match literal {
                Literal::Nat(value) => match value.to_u64() {
                    Some(value) => DTreeKey::Literal(DTreeLiteral::Nat(value)),
                    None => DTreeKey::Star,
                },
                Literal::Str(value) => DTreeKey::Literal(DTreeLiteral::String(value.clone())),
            }),
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lam { .. }
            | ExprNode::ForallE { .. }
            | ExprNode::LetE { .. }
            | ExprNode::Proj { .. } => keys.push(DTreeKey::Star),
            ExprNode::MData { .. } => unreachable!("MData is unwrapped above"),
        }
    }
    keys
}

/// Unwind an application spine `f a₁ … aₙ` into its head `f` (transparent through
/// `MData`) and its arguments in application order.
fn unwind_application(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut arguments = Vec::new();
    let mut head = expr;
    loop {
        while let ExprNode::MData { expr, .. } = head.node() {
            head = expr;
        }
        match head.node() {
            ExprNode::App { f, a } => {
                arguments.push(a);
                head = f;
            }
            _ => break,
        }
    }
    arguments.reverse();
    (head, arguments)
}

/// The index one past the complete subterm that begins at `start` in a flattened
/// preorder key sequence, computed from each key's [`DTreeKey::arity`].
fn subterm_end(keys: &[DTreeKey], start: usize) -> usize {
    let mut pending = 1usize;
    let mut position = start;
    while pending > 0 {
        let Some(key) = keys.get(position) else {
            break;
        };
        pending = pending - 1 + key.arity() as usize;
        position += 1;
    }
    position
}

/// A node in the live discrimination trie: rules that terminate here, and the
/// keyed edges to deeper positions. `BTreeMap` keeps child order deterministic.
#[derive(Debug, Clone, Default)]
struct DTreeNode {
    children: BTreeMap<DTreeKey, DTreeNode>,
    rules: Vec<Name>,
}

/// A live first-order discrimination tree: the in-memory lookup substrate `simp`
/// and `aesop` query for rewrite candidates. Rule left-hand sides are inserted as
/// flattened key sequences ([`flatten`]); a query term retrieves every rule whose
/// pattern could match it, by the standard wildcard-skip retrieval.
///
/// This is the queryable form; [`DiscriminationTree`] is its serialized CAS
/// artifact. Retrieval is a **sound pre-filter**: the returned candidates are a
/// superset of the true matches — a stored wildcard matches any subterm, so some
/// candidates still need real unification — ordered deterministically by rule
/// name. It never drops a genuine match.
#[derive(Debug, Clone, Default)]
pub struct DTree {
    root: DTreeNode,
    rule_count: u32,
}

impl DTree {
    /// An empty discrimination tree.
    pub fn new() -> Self {
        Self::default()
    }

    /// The number of rules indexed.
    pub fn rule_count(&self) -> u32 {
        self.rule_count
    }

    /// Index `rule` under the discrimination key of `pattern` (a rule's LHS).
    pub fn insert(&mut self, pattern: &Expr, rule: Name) {
        let mut node = &mut self.root;
        for key in flatten(pattern) {
            node = node.children.entry(key).or_default();
        }
        node.rules.push(rule);
        self.rule_count = self.rule_count.saturating_add(1);
    }

    /// Every indexed rule whose pattern could match `term`, deterministically
    /// ordered by rule name and deduplicated. A stored wildcard matches any
    /// subterm of `term`; a stored concrete key must equal the term's key at that
    /// position.
    pub fn candidates(&self, term: &Expr) -> Vec<Name> {
        let keys = flatten(term);
        let mut matches = Vec::new();
        // Explicit worklist rather than recursion: a deeply nested term must not
        // overflow the stack (the discipline the kernel term-walkers keep).
        let mut work = vec![(&self.root, 0usize)];
        while let Some((node, position)) = work.pop() {
            let Some(key) = keys.get(position) else {
                matches.extend(node.rules.iter().cloned());
                continue;
            };
            if let Some(child) = node.children.get(key) {
                work.push((child, position + 1));
            }
            // A stored wildcard matches the term's whole subterm at `position`.
            // Skip that branch when the term's own key is already a wildcard: the
            // exact edge above already followed it, and taking it twice would
            // double-count the same match.
            if *key != DTreeKey::Star
                && let Some(child) = node.children.get(&DTreeKey::Star)
            {
                work.push((child, subterm_end(&keys, position)));
            }
        }
        matches.sort();
        matches.dedup();
        matches
    }
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

#[cfg(test)]
mod dtree_tests {
    use super::{DTree, DTreeKey, DTreeLiteral, flatten};
    use fln_core::expr::{Expr, FVarId, Literal, MVarId, NatLit};
    use fln_core::name::Name;

    fn name(component: &str) -> Name {
        Name::from_components([component])
    }

    fn constant(component: &str) -> Expr {
        Expr::const_(name(component), Vec::new())
    }

    /// `head a₁ … aₙ` in application order.
    fn apply(head: Expr, args: Vec<Expr>) -> Expr {
        args.into_iter().fold(head, Expr::app)
    }

    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }

    fn mvar(component: &str) -> Expr {
        Expr::mvar(MVarId(name(component)))
    }

    fn key_const(component: &str, arity: u32) -> DTreeKey {
        DTreeKey::Const {
            name: name(component),
            arity,
        }
    }

    #[test]
    fn flatten_encodes_constant_headed_application_in_preorder() {
        // f g 5  ->  [Const{f,2}, Const{g,0}, Literal(Nat 5)]
        let term = apply(constant("f"), vec![constant("g"), nat(5)]);
        assert_eq!(
            flatten(&term),
            vec![
                key_const("f", 2),
                key_const("g", 0),
                DTreeKey::Literal(DTreeLiteral::Nat(5)),
            ]
        );
    }

    #[test]
    fn flatten_maps_metavariables_and_fvars_to_star() {
        assert_eq!(flatten(&mvar("x")), vec![DTreeKey::Star]);
        assert_eq!(
            flatten(&Expr::fvar(FVarId(name("y")))),
            vec![DTreeKey::Star]
        );
        // f ?x b  ->  [Const{f,2}, Star, Const{b,0}]
        let term = apply(constant("f"), vec![mvar("x"), constant("b")]);
        assert_eq!(
            flatten(&term),
            vec![key_const("f", 2), DTreeKey::Star, key_const("b", 0)]
        );
    }

    #[test]
    fn flatten_maps_oversized_nat_literal_to_star() {
        // A literal that does not fit u64 cannot be a `DTreeLiteral::Nat`; it must
        // over-approximate to a wildcard rather than silently truncate.
        let big = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1, 1])));
        assert_eq!(flatten(&big), vec![DTreeKey::Star]);
    }

    #[test]
    fn exact_match_is_head_arity_and_argument_sensitive() {
        let mut tree = DTree::new();
        tree.insert(
            &apply(constant("f"), vec![constant("a"), constant("b")]),
            name("R1"),
        );
        assert_eq!(tree.rule_count(), 1);

        // Exact same term matches.
        assert_eq!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("b")])),
            vec![name("R1")]
        );
        // A differing argument does not.
        assert!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("c")]))
                .is_empty()
        );
        // A differing head does not.
        assert!(
            tree.candidates(&apply(constant("g"), vec![constant("a"), constant("b")]))
                .is_empty()
        );
    }

    #[test]
    fn wildcard_pattern_matches_any_subterm_at_that_position() {
        // Pattern: f ?x b
        let mut tree = DTree::new();
        tree.insert(
            &apply(constant("f"), vec![mvar("x"), constant("b")]),
            name("R"),
        );

        // ?x binds a bare constant.
        assert_eq!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("b")])),
            vec![name("R")]
        );
        // ?x binds a whole application subterm; the trailing `b` still matches.
        assert_eq!(
            tree.candidates(&apply(
                constant("f"),
                vec![apply(constant("g"), vec![constant("y")]), constant("b")]
            )),
            vec![name("R")]
        );
        // The fixed trailing argument still has to match.
        assert!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("c")]))
                .is_empty()
        );
    }

    #[test]
    fn wildcard_skips_a_whole_multi_argument_subterm() {
        // Pattern: f ?x   (Const{f,1})
        let mut tree = DTree::new();
        tree.insert(&apply(constant("f"), vec![mvar("x")]), name("R"));

        // ?x binds `h a b c`, whose flattening is four keys the skip must consume.
        assert_eq!(
            tree.candidates(&apply(
                constant("f"),
                vec![apply(
                    constant("h"),
                    vec![constant("a"), constant("b"), constant("c")]
                )]
            )),
            vec![name("R")]
        );
        // `f a b` is Const{f,2}, not Const{f,1}: arity distinguishes it, no match.
        assert!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("b")]))
                .is_empty()
        );
    }

    #[test]
    fn arity_distinguishes_the_same_head() {
        let mut tree = DTree::new();
        tree.insert(&apply(constant("f"), vec![constant("a")]), name("Unary"));
        tree.insert(
            &apply(constant("f"), vec![constant("a"), constant("b")]),
            name("Binary"),
        );

        assert_eq!(
            tree.candidates(&apply(constant("f"), vec![constant("a")])),
            vec![name("Unary")]
        );
        assert_eq!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("b")])),
            vec![name("Binary")]
        );
    }

    #[test]
    fn candidates_are_deterministic_and_deduplicated() {
        // Two rules match `f a`: an exact one and a wildcard one. The result is
        // sorted by rule name regardless of insertion order.
        let mut tree = DTree::new();
        tree.insert(&apply(constant("f"), vec![mvar("x")]), name("Zebra"));
        tree.insert(&apply(constant("f"), vec![constant("a")]), name("Alpha"));

        let found = tree.candidates(&apply(constant("f"), vec![constant("a")]));
        assert_eq!(found, vec![name("Alpha"), name("Zebra")]);
    }

    #[test]
    fn empty_tree_and_pure_wildcard_pattern_behave() {
        let empty = DTree::new();
        assert!(empty.candidates(&constant("anything")).is_empty());
        assert_eq!(empty.rule_count(), 0);

        // A bare metavariable pattern (`?x`) matches every term.
        let mut tree = DTree::new();
        tree.insert(&mvar("x"), name("CatchAll"));
        assert_eq!(tree.candidates(&constant("k")), vec![name("CatchAll")]);
        assert_eq!(
            tree.candidates(&apply(constant("f"), vec![constant("a"), constant("b")])),
            vec![name("CatchAll")]
        );
        assert_eq!(tree.candidates(&nat(42)), vec![name("CatchAll")]);
    }
}
