//! The Grimoire environment (plan §7.1): semantically the Reference's name→constant
//! map plus contract-registered extensions; mechanically ours — persistent maps with
//! structural sharing, so a snapshot is an O(1) clone and mutation after a fork is
//! invisible to the fork (the primitive under Athanor's speculative parallelism,
//! Lantern's per-request views, and Envoy's search trees).
//!
//! Every commit exposes two roots: the **logical root** (declarations + extension
//! deltas + options; the cache key the Ledger, receipts, and Envoy speak) and a
//! separate **operational-metadata root** — two hosts producing the same trusted
//! environment share a logical root even when their operational manifests differ.

use std::sync::Arc;

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::Expr;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::{LogicalRoot, LogicalRootBuilder};

use crate::constants::{ConstantInfo, DefinitionSafety, QuotKind, ReducibilityHints};
use crate::extensions::{
    CheckpointError, CheckpointLimits, CheckpointSemantics, ExtensionCheckpoint,
    ExtensionDescriptor, ExtensionState, ProofBudget,
};
#[cfg(test)]
use crate::extensions::{MergeSemantics, PayloadProvenance};
use crate::modules::{CancellationProbe, ModuleEpoch};
use crate::pmap::{CollisionBudget, PKey, PMap};
use crate::terms::WeightBudget;

/// Stable `Domain::DeclContent` tags. These are schema values, not Rust enum
/// discriminants: changing them requires an explicit identity/epoch decision.
#[forbid(clippy::as_conversions)]
const fn definition_safety_tag(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Unsafe => 0,
        DefinitionSafety::Safe => 1,
        DefinitionSafety::Partial => 2,
    }
}

#[forbid(clippy::as_conversions)]
const fn quot_kind_tag(kind: QuotKind) -> u8 {
    match kind {
        QuotKind::Type => 0,
        QuotKind::Ctor => 1,
        QuotKind::Lift => 2,
        QuotKind::Ind => 3,
    }
}

/// Lossless on FrankenLean's certified Rust targets, whose pointer widths are at
/// most 64 bits. This conversion stays outside the enum-tag cast prohibition so
/// that the policy does not introduce a fallible or panicking length path.
#[allow(clippy::as_conversions)]
const fn usize_to_u64(value: usize) -> u64 {
    value as u64
}

/// Write a mutual-block membership list into declaration identity.
///
/// The order and multiplicity are semantic input. Keep this as one forward pass:
/// no sorting, deduplication, or structure proportional to the containing
/// [`Environment`] belongs in declaration identity.
/// Which declaration row family bound a [`DeclarationBudget`].
///
/// This is a fact on the outcome's own report, deliberately **not** a new
/// [`StructuralUnit`]. All four families are `ProducedNodes` under the closed D8
/// taxonomy, whose stated bar for a new unit is not "it is a different number" but
/// "a caller has to react differently" — and a caller reacts to all four the same
/// way, by shrinking the declaration. The finer fact still has to survive, so it
/// lives here rather than growing a closed taxonomy that breaks every consumer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationDimension {
    LevelParams,
    MutualRows,
    ConstructorRows,
    RecursorRules,
    /// Bytes the canonical `Domain::DeclContent` encoder emits.
    ///
    /// Reported through `StructuralUnit::InputBytes` rather than a fourth D8 unit,
    /// because a caller reacts to a byte bound the same way it reacts to a row bound —
    /// by shrinking the declaration — and that reaction, not the number, is the
    /// taxonomy's stated bar for a new unit. Which side of the codec the bytes are on is
    /// the finer fact, and it lives here, exactly as the four row families' finer facts
    /// do.
    CanonicalBytes,
}

/// Frozen cancellation observation points for declaration preflight.
///
/// Numbered and fixed, because "cancellation is checked somewhere in here" is not a
/// contract a caller can rely on: a probe that trips must produce the *same*
/// checkpoint every run, or the outcome is schedule-dependent.
///
/// The row families are not a checkpoint. There is nothing to abandon there — every
/// count is a `len()` on a materialized vector — and claiming a checkpoint that
/// cannot fire would be an untruthful contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationCheckpoint {
    /// Before measuring the expression at this frozen index. See
    /// [`declaration_expressions`] for the order.
    BeforeExpression(usize),
    /// After a plan revalidated its base and before it publishes. The last point at
    /// which a caller who gave up can still prevent a declaration being published on
    /// their behalf.
    BeforePublication,
}

impl std::fmt::Display for DeclarationCheckpoint {
    /// The wire form a cancellation carries in its `at` field. Stable, because a test
    /// pins it and a caller distinguishing checkpoints reads it.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeclarationCheckpoint::BeforeExpression(index) => {
                write!(f, "before-expression/{index}")
            }
            DeclarationCheckpoint::BeforePublication => write!(f, "before-publication"),
        }
    }
}

/// The schema of a [`PreparedDeclarationAdmission`]. Bumping it invalidates every plan
/// in flight, which is the point: a plan decided under one identity schema must not be
/// committed under another.
const DECLARATION_PLAN_SCHEMA: u16 = 1;

/// What preflighting one declaration against a base concluded.
///
/// A duplicate name is [`DeclarationPlan::DuplicateName`] rather than a non-answer,
/// because it is a *completed determination about the declaration* — the bounded lookup
/// finished and the answer is no. Per decision `fln-um4a` a domain rejection belongs
/// inside [`Outcome::Complete`], never beside `Inconclusive` where the two would look
/// symmetric and invite one being read as the other.
#[derive(Debug)]
pub enum DeclarationPlan {
    /// Admissible as far as this base can tell. Commit to publish.
    Prepared(PreparedDeclarationAdmission),
    /// Already present. No plan exists, because there is nothing to publish.
    DuplicateName { name: Name },
}

/// One published declaration, with the identity that publication made authoritative.
#[derive(Debug, Clone)]
pub struct DeclarationPublication {
    /// The one immutable environment this transaction published.
    pub environment: Environment,
    /// The content digest of the admitted declaration.
    ///
    /// Authoritative **because it was published**. The same value existed inside the
    /// plan as a provisional digest with no accessor, so a plan that never commits
    /// cannot hand it out, log it, or have it cached — a provisional identity that
    /// escapes is a cache key for a declaration nobody admitted.
    pub digest: Digest,
    /// Exact preflight facts for the admitted declaration.
    pub usage: DeclarationUsage,
}

/// The result of committing a prepared admission.
#[derive(Debug, Clone)]
pub enum DeclarationCommitted {
    Published(DeclarationPublication),
    /// The name was taken between planning and committing. A completed determination,
    /// not a non-answer: the lookup finished.
    DuplicateName {
        name: Name,
    },
}

/// An immutable, non-authoritative declaration admission decided against one base.
///
/// Holding material is not authority. Nothing here is reachable as an environment, it
/// is never cacheable, and [`Self::commit`] revalidates before publishing. The type is
/// the twin of `ModuleGraphAdmissionPlan`/`PreparedAdmission` in
/// [`crate::modules`] on purpose rather than a second invention: one plan shape in the
/// crate, so a reader who has understood one has understood both.
#[derive(Debug)]
pub struct PreparedDeclarationAdmission {
    schema: u16,
    info: Arc<ConstantInfo>,
    /// Never exposed. See [`DeclarationPublication::digest`].
    provisional_digest: Digest,
    usage: DeclarationUsage,
    /// The base this plan was decided against, held as an O(1) persistent snapshot.
    base: Environment,
    /// The insertion weight to charge, **measured** rather than supplied.
    admission_weight: u64,
    collision_budget: CollisionBudget,
}

impl PreparedDeclarationAdmission {
    /// **Never.** A plan is a decision in flight, not a result.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// The declaration this plan would admit.
    pub fn declaration(&self) -> &ConstantInfo {
        &self.info
    }

    /// Exact preflight facts. Available before commit because they describe the
    /// *input*, which is already known; the identity they support is not.
    pub const fn usage(&self) -> &DeclarationUsage {
        &self.usage
    }

    /// Whether this plan is still meaningful against `env`.
    ///
    /// Same constants map by construction. Deliberately conservative: an environment
    /// rebuilt to identical contents answers `false` and the plan must be re-decided,
    /// which is inconclusive and recoverable. The alternative — accepting it — would
    /// publish a measured insertion weight taken against a different trie shape.
    pub fn is_valid_for(&self, env: &Environment) -> bool {
        self.schema == DECLARATION_PLAN_SCHEMA
            && self.base.constants.is_same_structure(&env.constants)
    }

    /// Revalidate against `env` and publish exactly once.
    ///
    /// Four things are rechecked immediately before publication and **nothing is
    /// recomputed**: the plan's own schema, the duplicate-name observation, the base
    /// binding, and cancellation — in that order, because a taken name is a complete
    /// verdict about the declaration that publishes nothing, whereas a moved base is
    /// only a statement about this plan. Checking the base first would make the
    /// duplicate branch unreachable, since an environment that gained a name is a
    /// different persistent value. The canonical bytes, the digest, and the measured
    /// insertion weight are consumed as decided — recomputing them here would make the
    /// commit a second measurement that could disagree with the one the plan was
    /// decided on, and charging the insertion twice is one of the defects this bead
    /// names.
    ///
    /// A superseded base is [`InconclusiveCause::AuthorityIncomplete`]: its own
    /// definition is a source that changed underfoot, and the base moving says nothing
    /// about whether this declaration is admissible. Caching it as a refusal would
    /// record "the environment was busy" as "this declaration is invalid".
    ///
    /// Atomicity is structural, not procedural. `Environment` is immutable and
    /// persistent, so no path through this function can mutate `env`: every non-published
    /// arm leaves the caller's environment the same value it already held, with the same
    /// logical root and the same structural sharing. There is no partial-insert state to
    /// roll back because there is no in-place insert.
    pub fn commit(
        self,
        env: &Environment,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<DeclarationCommitted> {
        if self.schema != DECLARATION_PLAN_SCHEMA {
            return Outcome::Inconclusive(Inconclusive::authority_incomplete(
                "declaration admission plan carries a superseded schema",
            ));
        }
        // Re-observed on the commit target, not trusted from the plan, and deliberately
        // *before* the base binding.
        //
        // The name being taken is a complete determination about this declaration and it
        // is true of the environment being committed against, whichever base the plan was
        // decided on — and reporting it publishes nothing, so no stale fact is consumed.
        // Checking the base first would make this branch unreachable: an environment that
        // gained a name is a different persistent value, so the base binding would
        // already have refused, and "superseded" is strictly less informative than
        // "that name is taken". A check that cannot fire is not defence in depth, it is
        // an untruthful contract.
        let name = self.info.name().clone();
        if env.constants.contains_key(&name) {
            return Outcome::complete(DeclarationCommitted::DuplicateName { name });
        }
        if !self.is_valid_for(env) {
            return Outcome::Inconclusive(Inconclusive::authority_incomplete(
                "declaration admission plan decided against a superseded environment",
            ));
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                DeclarationCheckpoint::BeforePublication.to_string(),
            ));
        }
        // The PMap insert now speaks the shared vocabulary, so this is a fold rather than a
        // translation. The `InternalFault` that used to live here — for a collision overage
        // that could not be expressed in `ResourceUsage`'s `u64` fields — is GONE, because
        // `CollisionBudget::max_expanded_weight` is now a `u64` limit and the numbers fit by
        // construction (bead `franken_lean-pmap-refusal-outcome-taxonomy-i1z9`). Deleting it
        // is how that bead proves it closed the gap instead of papering it.
        env.constants
            .try_insert_with_budget(
                name,
                Arc::clone(&self.info),
                self.admission_weight,
                self.collision_budget,
            )
            .map_complete(|constants| {
                DeclarationCommitted::Published(DeclarationPublication {
                    environment: Environment {
                        constants,
                        extensions: env.extensions.clone(),
                    },
                    digest: self.provisional_digest,
                    usage: self.usage,
                })
            })
    }
}

impl DeclarationDimension {
    /// Frozen order, and it is the reported-reason order for simultaneous breaches
    /// (bead `franken_lean-j8h`). Signature before membership before the
    /// per-variant families: most general first, so the primary reason names the
    /// dimension a caller can act on with the least knowledge of the variant.
    ///
    /// Schedule-independent by construction — the scan is a fixed sequence over an
    /// immutable value, so two threads preflighting the same declaration report the
    /// same primary dimension.
    const ORDER: [DeclarationDimension; 5] = [
        DeclarationDimension::LevelParams,
        DeclarationDimension::MutualRows,
        DeclarationDimension::ConstructorRows,
        DeclarationDimension::RecursorRules,
        // Last, because it is the only dimension whose exact value is not known until
        // the encoder has run. The frozen order is still what selects the primary reason,
        // so a declaration over both rows and bytes reports the cheap dimension.
        DeclarationDimension::CanonicalBytes,
    ];

    const fn as_str(self) -> &'static str {
        match self {
            DeclarationDimension::LevelParams => "level_params",
            DeclarationDimension::MutualRows => "mutual_rows",
            DeclarationDimension::ConstructorRows => "constructor_rows",
            DeclarationDimension::RecursorRules => "recursor_rules",
            DeclarationDimension::CanonicalBytes => "canonical_bytes",
        }
    }

    /// The D8 unit a refusal on this dimension reports.
    const fn unit(self) -> StructuralUnit {
        match self {
            DeclarationDimension::LevelParams
            | DeclarationDimension::MutualRows
            | DeclarationDimension::ConstructorRows
            | DeclarationDimension::RecursorRules => StructuralUnit::ProducedNodes,
            // The byte-shaped unit. Its documented wording says "consumed", which is the
            // one wart; the dimension name in `progress` carries the side, and widening
            // that wording is fln-core's call and is not needed for this to be truthful.
            DeclarationDimension::CanonicalBytes => StructuralUnit::InputBytes,
        }
    }
}

/// Exact logical row facts for one declaration (bead `franken_lean-j8h`).
///
/// **Logical and reproducible**, which is the whole claim: these are counts of rows
/// the canonical encoding visits, not CPU instructions, allocator-resident bytes, or
/// unique `Arc` node counts. Two runs over the same declaration produce identical
/// facts on any schedule.
///
/// # Maximum logical depth is now reported, and it is a fact rather than a limit
///
/// This block previously recorded depth as the one dimension `franken_lean-j8h` names
/// that was not reported, because [`crate::terms::WeightReport`] did not carry it.
/// It does now: depth folds beside the weight over the same post-order traversal, so
/// the fact costs one `u64` per distinct node and no second walk.
///
/// It is reported as an exact usage fact and is deliberately **not** yet a budgeted
/// [`DeclarationDimension`]. A dimension needs a `StructuralUnit`, and none of the three
/// says what a depth bound means: `InputBytes` and `ExpandedWeight` describe sizes, and
/// `ProducedNodes` would render a depth stop as "produced nodes: 65, allowed 64" when
/// the declaration in fact produced far more nodes than 65 — a false fact, which is the
/// thing this whole struct exists to avoid. Adding the limit is a `fln-core` taxonomy
/// question and is asked there rather than answered here.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DeclarationUsage {
    /// Level parameters on the constant's signature.
    pub level_params: u64,
    /// Mutual-block member rows (`all`) on an all-bearing variant.
    pub mutual_rows: u64,
    /// Constructor-name rows on an inductive.
    pub constructor_rows: u64,
    /// Recursor rule rows.
    pub recursor_rules: u64,
    /// Bytes the canonical encoder emits for this declaration. Exact, because it is the
    /// length of the one stream the digest is taken over rather than a model of it.
    pub canonical_bytes: u64,
    /// Expressions measured: the signature type, a body if the variant has one, and
    /// one per recursor rule.
    pub expressions: u64,
    /// Distinct expression nodes stored across every expression, summed with checked
    /// arithmetic.
    pub expr_nodes: u64,
    /// Total denoted (fully expanded) tree size across every expression, computed
    /// without expanding it. `u128` because a shared graph denotes a tree that can
    /// exceed `u64` while the graph itself stays small.
    pub expanded_weight: u128,
    /// Deepest root-to-leaf path across every expression of this declaration.
    ///
    /// The **maximum** of the per-expression depths, not their sum: a declaration is as
    /// deep as its deepest expression, and adding a second shallow expression does not
    /// make it deeper. Every other expression fact on this struct is a total, which is
    /// exactly why this one says so.
    pub max_logical_depth: u64,
}

impl DeclarationUsage {
    const fn get(&self, dimension: DeclarationDimension) -> u64 {
        match dimension {
            DeclarationDimension::LevelParams => self.level_params,
            DeclarationDimension::MutualRows => self.mutual_rows,
            DeclarationDimension::ConstructorRows => self.constructor_rows,
            DeclarationDimension::RecursorRules => self.recursor_rules,
            DeclarationDimension::CanonicalBytes => self.canonical_bytes,
        }
    }
}

/// What a caller allows one declaration's row families to cost.
///
/// `UNBOUNDED` and the `Default` impl mirror [`CollisionBudget`] rather than
/// inventing a second convention: an unset budget must behave exactly as the
/// pre-budget code did, or adding the parameter would silently change identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarationBudget {
    pub max_level_params: u64,
    pub max_mutual_rows: u64,
    pub max_constructor_rows: u64,
    pub max_recursor_rules: u64,
    /// Bytes the canonical encoder may emit for this declaration.
    pub max_canonical_bytes: u64,
    /// Distinct expression nodes across **the whole declaration**, not per expression.
    pub max_expr_nodes: u64,
    /// Denoted tree size across the whole declaration.
    pub max_expanded_weight: u64,
}

impl DeclarationBudget {
    pub const UNBOUNDED: DeclarationBudget = DeclarationBudget {
        max_level_params: u64::MAX,
        max_mutual_rows: u64::MAX,
        max_constructor_rows: u64::MAX,
        max_recursor_rules: u64::MAX,
        max_canonical_bytes: u64::MAX,
        max_expr_nodes: u64::MAX,
        max_expanded_weight: u64::MAX,
    };

    const fn get(&self, dimension: DeclarationDimension) -> u64 {
        match dimension {
            DeclarationDimension::LevelParams => self.max_level_params,
            DeclarationDimension::MutualRows => self.max_mutual_rows,
            DeclarationDimension::ConstructorRows => self.max_constructor_rows,
            DeclarationDimension::RecursorRules => self.max_recursor_rules,
            DeclarationDimension::CanonicalBytes => self.max_canonical_bytes,
        }
    }
}

impl Default for DeclarationBudget {
    fn default() -> Self {
        Self::UNBOUNDED
    }
}

/// Count the row families of `info`, then refuse if any exceeds `budget`.
///
/// This is the cheap half of declaration preflight and it runs first for the same
/// reason [`Environment::try_add_decl_with_budget`] evaluates duplicate names first:
/// every count here is a `len()` on an already-materialized vector, so the whole
/// determination is constant work per family and cannot itself be the unbounded path.
/// What it buys is refusing *before* the encoder is entered, so a declaration with a
/// million mutual members never reaches the loop that would write a million rows.
///
/// # Authority
///
/// Exhaustion is [`Outcome::Inconclusive`], never a rejection: a declaration over
/// budget has not been judged ill-formed, and the outcome's own `cache_admission`
/// refuses to memoize it. Exact totals are returned only inside
/// [`Outcome::Complete`]; a refusal carries its consumption as diagnostic `progress`
/// rather than as authoritative facts, so there is no partial-work field for a caller
/// to read while skipping the authority check (decision `fln-um4a`).
///
/// Nothing is published, computed, or cached on refusal — in particular no provisional
/// digest exists to leak, because this runs before any hashing.
///
/// Cancellation is not sampled here and no checkpoint is claimed: there is no
/// input-sized traversal to abandon. It arrives with the expression dimensions.
pub fn preflight_declaration_rows(
    info: &ConstantInfo,
    budget: DeclarationBudget,
) -> Outcome<DeclarationUsage> {
    let base = info.constant_val();
    let usage = DeclarationUsage {
        level_params: usize_to_u64(base.level_params.len()),
        mutual_rows: usize_to_u64(declaration_mutual_members(info).len()),
        constructor_rows: match info {
            ConstantInfo::Induct(v) => usize_to_u64(v.ctors.len()),
            _ => 0,
        },
        recursor_rules: match info {
            ConstantInfo::Rec(v) => usize_to_u64(v.rules.len()),
            _ => 0,
        },
        // Exact, and computed here rather than modelled: the encoder is run once and its
        // stream length taken. It is the length of the SAME bytes the digest is over, so
        // the fact cannot describe a different encoding. Running it costs one pass over a
        // declaration whose structure the row families have not yet bounded, which is why
        // the byte dimension is checked LAST in the frozen order — see `ORDER`.
        canonical_bytes: usize_to_u64(Environment::decl_content_bytes(info).len()),
        expressions: 0,
        expr_nodes: 0,
        expanded_weight: 0,
        // Zero until an expression is measured. Zero is the honest starting value and
        // also the honest final value for a declaration with no expressions: a
        // declaration with nothing to descend into has no depth, rather than depth 1.
        max_logical_depth: 0,
    };

    for dimension in DeclarationDimension::ORDER {
        let allowed = budget.get(dimension);
        let observed = usage.get(dimension);
        if observed > allowed {
            return Outcome::Inconclusive(
                Inconclusive::resource(ResourceUsage {
                    // Per dimension, not hardcoded: the row families are ProducedNodes and
                    // canonical bytes is InputBytes. Hardcoding one unit would have made
                    // the taxonomy decision true in the docs and false in the refusal.
                    reason: ResourceReason::StructuralBudget {
                        unit: dimension.unit(),
                    },
                    allowed,
                    // A stop must report spending past its allowance or it is not a
                    // stop; `is_genuine_exhaustion` depends on it, and an
                    // `observed == allowed` refusal is self-contradictory. The scan
                    // has the exact count here, so the max is a floor, not a guess.
                    observed: observed.max(allowed.saturating_add(1)),
                })
                .with_progress(dimension.as_str()),
            );
        }
    }
    Outcome::complete(usage)
}

/// Preflight one declaration's identity work in full: rows, then expressions.
///
/// Cheap dimensions first, and the order is the point rather than an optimisation.
/// The row families are constant work per family, so refusing there costs nothing and
/// prevents entering an input-sized traversal at all; only a declaration whose rows
/// already fit pays for its expressions to be measured.
///
/// # Authority
///
/// One [`Outcome`]. Exhaustion and cancellation are both
/// [`Outcome::Inconclusive`] — never a rejection, never an acceptance — and neither is
/// cacheable. Exact totals exist only inside [`Outcome::Complete`]; on any non-answer
/// the partial facts are deliberately not returned, because a partial usage total is a
/// number that understates the work while looking like a measurement.
///
/// Nothing is hashed, published, or cached here on any path. In particular no
/// provisional digest exists to be returned, logged, or cached, because preflight
/// completes before hashing begins.
///
/// # Maximum logical depth is reported here as a fact, and is not a budget dimension
///
/// Depth's *safety* role was always discharged — the traversal is iterative, so a deep
/// term is a measurement rather than a stack overflow — but the fact itself used to be
/// unavailable. It is now measured exactly, as the maximum across the declaration's
/// expressions. It is not a budgeted dimension; see [`DeclarationUsage`] for why that
/// half is a `fln-core` taxonomy question rather than an omission.
///
/// Canonical bytes ARE now reported, and exactly rather than modelled — the encoder runs
/// once and its stream length is taken, so the fact describes the same bytes the digest is
/// over. The cost is that the byte dimension is the one whose exact value is not known
/// until the encoder has run, which is why it sits LAST in
/// [`DeclarationDimension::ORDER`]: a declaration over both rows and bytes reports the
/// cheap dimension, and the expensive one is only consulted when the cheap ones passed.
pub fn preflight_declaration(
    info: &ConstantInfo,
    budget: DeclarationBudget,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<DeclarationUsage> {
    let mut usage = match preflight_declaration_rows(info, budget).non_answer_for() {
        Ok(non_answer) => return non_answer,
        Err(usage) => usage,
    };
    if let Some(non_answer) =
        preflight_declaration_expressions(info, budget, cancellation, &mut usage)
    {
        return non_answer;
    }
    Outcome::complete(usage)
}

/// Every expression one declaration carries, in a frozen order.
///
/// The order is part of the contract, not an implementation detail: it is the order
/// cancellation checkpoints are numbered in and the order a shared budget is spent
/// in, so two runs over the same declaration abandon at the same expression and
/// report the same primary stop. Signature type first, then the body a
/// value-bearing variant has, then recursor rule right-hand sides in rule order.
fn declaration_expressions(info: &ConstantInfo) -> Vec<&Expr> {
    let mut expressions = vec![&info.constant_val().type_];
    match info {
        ConstantInfo::Defn(v) => expressions.push(&v.value),
        ConstantInfo::Thm(v) => expressions.push(&v.value),
        ConstantInfo::Opaque(v) => expressions.push(&v.value),
        ConstantInfo::Rec(v) => expressions.extend(v.rules.iter().map(|rule| &rule.rhs)),
        ConstantInfo::Axiom(_)
        | ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_) => {}
    }
    expressions
}

/// Measure every expression `info` carries, spending one shared budget across them.
///
/// # The budget is shared, not per-expression
///
/// A per-expression limit would be no limit at all for a recursor: a thousand rules
/// each just under the cap costs a thousand times the cap. So each expression is
/// measured against what is *left*, which is also why the expression order is frozen.
///
/// # Cancellation
///
/// Sampled once before each expression, at a fixed, numbered checkpoint. Cancellation
/// is [`InconclusiveCause::Cancelled`], never a resource stop and never a rejection:
/// `is_genuine_exhaustion` refuses a cancellation precisely so the two cannot be
/// conflated, and the probe is an abstraction rather than a bare flag so a test can
/// trip a chosen sample instead of always the first.
///
/// # Folding someone else's refusal
///
/// A stop inside [`crate::terms::expanded_weight`] is propagated **unchanged**, via
/// [`Outcome::non_answer_for`]. Its `ResourceUsage` already carries the exact unit and
/// numbers and its `progress` already names the unit that bound, so restating it in
/// this layer's vocabulary would paraphrase a measurement this function did not make.
/// The consequence is deliberate and worth knowing: on that path the reported stop
/// speaks in the term-measurement vocabulary, and the partial declaration-level facts
/// consumed so far are *not* claimed, because they are partial.
fn preflight_declaration_expressions(
    info: &ConstantInfo,
    budget: DeclarationBudget,
    cancellation: Option<&dyn CancellationProbe>,
    usage: &mut DeclarationUsage,
) -> Option<Outcome<DeclarationUsage>> {
    for (index, expr) in declaration_expressions(info).into_iter().enumerate() {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Some(Outcome::Inconclusive(Inconclusive::cancelled(
                DeclarationCheckpoint::BeforeExpression(index).to_string(),
            )));
        }

        // What is left, so the limit is over the declaration rather than over each
        // expression independently.
        let remaining_nodes = budget.max_expr_nodes.saturating_sub(usage.expr_nodes);
        let remaining_weight = u64::try_from(
            u128::from(budget.max_expanded_weight).saturating_sub(usage.expanded_weight),
        )
        .unwrap_or(u64::MAX);
        let measured = crate::terms::expanded_weight(
            expr,
            &WeightBudget::new(remaining_weight, remaining_nodes),
        );
        let report = match measured.non_answer_for::<DeclarationUsage>() {
            Ok(non_answer) => return Some(non_answer),
            Err(report) => report,
        };

        usage.expressions += 1;
        // Checked, not saturating: a wrapped or clamped total is a usage fact that
        // silently understates the work, which is worse than refusing to report one.
        let Some(nodes) = usage.expr_nodes.checked_add(report.distinct_nodes) else {
            return Some(Outcome::InternalFault(InternalFault::new(
                "fln-env.declaration-usage.node-total-overflow",
                "declaration expression node total overflowed u64",
            )));
        };
        let Some(weight) = usage.expanded_weight.checked_add(report.expanded_weight) else {
            return Some(Outcome::InternalFault(InternalFault::new(
                "fln-env.declaration-usage.weight-total-overflow",
                "declaration expanded-weight total overflowed u128",
            )));
        };
        usage.expr_nodes = nodes;
        usage.expanded_weight = weight;
        // MAX, not a running total, and not checked-add for that reason: a declaration is
        // as deep as its deepest expression. There is no overflow to guard — the value
        // never exceeds one expression's own depth, which `expanded_weight` already
        // bounded by its distinct-node budget.
        usage.max_logical_depth = usage.max_logical_depth.max(report.max_logical_depth);
    }
    None
}

/// The mutual-block members of `info`, or an empty slice for a variant that has none.
///
/// One place, so the preflight counts exactly the rows
/// [`write_mutual_membership`] would write. Two independent lists is how a usage fact
/// drifts from the work it claims to describe.
fn declaration_mutual_members(info: &ConstantInfo) -> &[Name] {
    match info {
        ConstantInfo::Defn(v) => &v.all,
        ConstantInfo::Thm(v) => &v.all,
        ConstantInfo::Opaque(v) => &v.all,
        ConstantInfo::Induct(v) => &v.all,
        ConstantInfo::Rec(v) => &v.all,
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) | ConstantInfo::Ctor(_) => &[],
    }
}

fn write_mutual_membership(w: &mut CanonWriter, members: &[Name]) {
    w.u64(usize_to_u64(members.len()));
    for member in members {
        member.write_body(w);
    }
}

impl PKey for Name {
    fn key_hash(&self) -> u64 {
        // The stored Reference-observable hash; collisions are handled by the trie's
        // buckets, equality stays structural.
        self.hash()
    }
}

/// Typed refusals — an environment mutation never panics and never silently drops.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvError {
    /// The kernel's already-declared law: one name, one constant.
    DuplicateDeclaration {
        name: Name,
    },
    DuplicateExtension {
        name: Name,
    },
    UnknownExtension {
        name: Name,
    },
    Checkpoint(CheckpointError),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::DuplicateDeclaration { name } => {
                write!(
                    f,
                    "constant `{}` is already declared",
                    name.to_display_string()
                )
            }
            EnvError::DuplicateExtension { name } => {
                write!(
                    f,
                    "extension `{}` is already registered",
                    name.to_display_string()
                )
            }
            EnvError::UnknownExtension { name } => {
                write!(
                    f,
                    "extension `{}` is not registered",
                    name.to_display_string()
                )
            }
            EnvError::Checkpoint(error) => error.fmt(f),
        }
    }
}

/// The typed outcome of a resource-bounded declaration admission (bead `fln-amv.13`).
///
/// Three-way by construction, so FL-INV-07's law is a type error to violate rather
/// than a convention to remember: a caller cannot read exhaustion as acceptance or as
/// rejection, because there is no `Result` whose `Err` means both. The distinction is
/// load-bearing — a rejection says *this declaration is not admissible*, while an
/// inconclusive says *we did not find out*, and only the first may ever be cached,
/// counted, or reported as a verdict.
/// # Migrated onto the shared taxonomy
/// (bead `franken_lean-pmap-refusal-outcome-taxonomy-i1z9`)
///
/// The `Inconclusive` arm used to carry a bespoke `CollisionExhausted`, which was a
/// `std::error::Error` — so a non-answer could be `?`-propagated into an ordinary error
/// path and reported as a failure. It now carries the shared [`Inconclusive`], the same
/// value every other bounded path in this crate reports, so folding several bounded
/// operations no longer needs a special case for this one. Special cases are where an
/// inconclusive gets read as a rejection.
#[derive(Debug, Clone, PartialEq)]
pub enum DeclAdmission {
    /// The declaration entered the returned environment.
    Admitted(Environment),
    /// A complete, resource-independent determination that the declaration is not
    /// admissible — today, the kernel's one-name-one-constant law.
    Rejected(EnvError),
    /// The adversarial-collision budget bound before any mutation. Not accepted, not
    /// rejected, not checked, not cacheable; the receiving environment is unchanged.
    /// A hash collision alone never produces this — only a collision large or heavy
    /// enough to exceed the reviewed envelope does.
    Inconclusive(Inconclusive),
    /// A broken internal invariant. Not a verdict about the declaration and not a
    /// resource stop — a fourth arm rather than a reuse of either, because reusing one
    /// would make a fault indistinguishable from the thing it was folded into.
    InternalFault(InternalFault),
}

impl DeclAdmission {
    /// Stable evidence label, matching the vocabulary
    /// [`DeclClosureStatus`](crate::decl_closure::DeclClosureStatus) already uses.
    pub fn outcome_label(&self) -> &'static str {
        match self {
            DeclAdmission::Admitted(_) => "admitted",
            DeclAdmission::Rejected(_) => "rejected",
            DeclAdmission::Inconclusive(_) => "inconclusive-collision-budget",
            DeclAdmission::InternalFault(_) => "internal-fault",
        }
    }

    /// Only an admitted declaration may feed a cache. Inconclusive outcomes are not
    /// publication-grade, and re-admitting one later must redo the work rather than
    /// replay a stored refusal.
    pub fn is_cacheable(&self) -> bool {
        matches!(self, DeclAdmission::Admitted(_))
    }

    /// The environment to carry forward, if any. `None` for both non-admitted arms —
    /// the caller keeps the environment it already held, unchanged.
    pub fn environment(&self) -> Option<&Environment> {
        match self {
            DeclAdmission::Admitted(environment) => Some(environment),
            DeclAdmission::Rejected(_)
            | DeclAdmission::Inconclusive(_)
            | DeclAdmission::InternalFault(_) => None,
        }
    }

    /// Whether this outcome is in the inconclusive family. Kept explicit so evidence
    /// rows never have to pattern-match a shape that may gain arms later.
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, DeclAdmission::Inconclusive(_))
    }
}

/// The environment. `Clone` IS `snapshot`: O(1), fully isolated.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Environment {
    constants: PMap<Name, Arc<ConstantInfo>>,
    extensions: PMap<Name, Arc<ExtensionState>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment::default()
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    /// `Environment.find`.
    pub fn find(&self, name: &Name) -> Option<&ConstantInfo> {
        self.constants.get(name).map(Arc::as_ref)
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.constants.contains_key(name)
    }

    /// Add a constant. One name, one constant — a duplicate is a typed refusal
    /// (the kernel's admission law; nothing here can overwrite a declaration).
    ///
    /// # NOT AUTHORITATIVE FOR RESOURCE PURPOSES (bead `franken_lean-j8h`)
    ///
    /// This path reports **no declaration work at all**. It traverses and buffers
    /// input-sized state with no limit, no cancellation, and no usage facts, and its
    /// `Result` has no way to express the difference between "this declaration is
    /// invalid" and "we did not finish deciding" — so a caller cannot uphold FL-INV-07
    /// through it even by trying. It survives as a convenience for fixtures and for
    /// callers that have already established their input is trusted and bounded, and it
    /// is named here as non-authoritative rather than quietly left looking equivalent.
    ///
    /// **Production admission of untrusted input goes through
    /// [`Environment::plan_add_decl`]**, which measures the work, refuses as typed
    /// [`Outcome::Inconclusive`], and makes hashing and insertion one atomic
    /// transaction. `franken_lean-j8h` owns removing the remaining production callers
    /// of this method; the ones outside this crate live in `fln-kernel` and are tracked
    /// separately, so this is deliberately **not** `#[deprecated]` — turning a peer
    /// crate red under `-D warnings` is not a migration.
    ///
    /// This is the unbounded *semantic* operation in the narrower sense too: it never
    /// refuses a valid declaration merely because its 64-bit hash collides with
    /// another's. [`Environment::try_add_decl_with_budget`] bounds that specific
    /// adversarial collision work — but only that, and it takes the declaration's
    /// weight as an unverified caller-supplied number, which is the defect
    /// `plan_add_decl` fixes by measuring it.
    pub fn add_decl(&self, info: ConstantInfo) -> Result<Environment, EnvError> {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return Err(EnvError::DuplicateDeclaration { name });
        }
        Ok(Environment {
            constants: self.constants.insert(name, Arc::new(info)),
            extensions: self.extensions.clone(),
        })
    }

    /// Resource-bounded declaration admission (bead `fln-amv.13`).
    ///
    /// `add_decl`'s duplicate law still applies and is evaluated first, because it
    /// is a complete determination that costs a single bounded lookup. Only then is
    /// the insertion preflighted against `budget`, so a crafted family of names
    /// sharing one `key_hash` cannot drive unbounded work through this boundary.
    ///
    /// Exhaustion is atomic and **inconclusive**, never a rejection: `self` is
    /// unchanged, nothing is published, and the caller learns that no verdict was
    /// reached about this declaration (FL-INV-07). Refusing the *insertion* is not
    /// the same as refusing the *declaration*, and the three-way
    /// [`DeclAdmission`] makes conflating them a type error rather than a
    /// convention.
    ///
    /// `expanded_weight` is supplied by the caller because a generic map cannot
    /// infer the semantic weight of an opaque declaration; the decoder or
    /// admission boundary that parsed it can.
    ///
    /// # Partially authoritative, and the part it lacks is the point
    /// (bead `franken_lean-j8h`)
    ///
    /// This bounds the persistent-map insertion and nothing else. `expanded_weight` is
    /// an **unverified number crossing the boundary**: the caller asserts the
    /// declaration's weight and this method charges what it was told, so a caller that
    /// understates it buys unbounded insertion work with a small integer. It also
    /// reports no identity work — nothing about canonical bytes, expression nodes, rows,
    /// or depth — and its refusal is a `CollisionExhausted` error rather than a typed
    /// [`Outcome::Inconclusive`], so it composes with `?` into ordinary error paths
    /// where a non-answer can be read as a failure.
    ///
    /// [`Environment::plan_add_decl`] measures the weight instead of trusting it and
    /// folds the refusal through the shared authority vocabulary.
    /// `franken_lean-pmap-refusal-outcome-taxonomy-i1z9` owns migrating this signature.
    pub fn try_add_decl_with_budget(
        &self,
        info: ConstantInfo,
        expanded_weight: u64,
        budget: CollisionBudget,
    ) -> DeclAdmission {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return DeclAdmission::Rejected(EnvError::DuplicateDeclaration { name });
        }
        match self
            .constants
            .try_insert_with_budget(name, Arc::new(info), expanded_weight, budget)
        {
            Outcome::Complete(constants) => DeclAdmission::Admitted(Environment {
                constants,
                extensions: self.extensions.clone(),
            }),
            Outcome::Inconclusive(stop) => DeclAdmission::Inconclusive(stop),
            // A fault is neither a verdict nor an exhaustion, so it gets its own arm. The
            // bounded insert has no fault path today and this is unreachable — but mapping
            // it onto `Rejected` would launder a broken invariant into "this declaration is
            // inadmissible", and onto `Inconclusive` would report it as a budget stop.
            // Both are the conflation this bead exists to remove.
            Outcome::InternalFault(fault) => DeclAdmission::InternalFault(fault),
        }
    }

    /// Preflight one declaration's identity and admission as a single decision
    /// (bead `franken_lean-j8h`).
    ///
    /// This is the bounded entry point: hashing and admission become one preflighted
    /// transaction rather than two independent calls, so there is no window in which a
    /// declaration has been hashed but not admitted and no way to publish work facts
    /// that describe a different base.
    ///
    /// # Order, and why it is this order
    ///
    /// 1. **Duplicate name.** A single bounded lookup and a complete determination, so
    ///    it runs first and nothing further is spent on a declaration that cannot be
    ///    admitted.
    /// 2. **Row families.** Constant work per family, and refusing here means the
    ///    encoder is never entered.
    /// 3. **Expressions.** The only input-sized measurement, bounded and cancellable.
    /// 4. **The digest.** Computed last, so a declaration that was going to be refused
    ///    never had a provisional identity computed for it at all.
    ///
    /// # The insertion weight is measured, not supplied
    ///
    /// [`Environment::try_add_decl_with_budget`] takes `expanded_weight` as a caller
    /// -supplied `u64`, which means that boundary trusts a number instead of measuring
    /// one — the concrete form of this bead's complaint that no API can truthfully
    /// report declaration work. Here the weight comes from the preflight's own
    /// measurement. A total that exceeds `u64` saturates to `u64::MAX`, which charges
    /// the most rather than the least: the conservative direction refuses, and a charge
    /// that silently understated the work would be the untruthful fact.
    ///
    /// # KERNEL-ONLY BY D6 (bead `franken_lean-oof9`)
    ///
    /// Bounded is not the same as authorised. This path measures and refuses truthfully,
    /// but it does not require that anything CHECKED the declaration — so under D6
    /// ("nothing but the kernel may admit a constant") the only legitimate production
    /// callers are in `fln-kernel`, and today there are exactly two:
    /// `fln-kernel/src/admit.rs` and `fln-kernel/src/capability.rs`.
    ///
    /// That restriction cannot be expressed in this signature. `fln-env` is rank 4 and
    /// `fln-kernel` sits above it, so a kernel-bound capability type can never appear
    /// here without inverting a layering edge. A sealed trait does not help either: sealing
    /// means only `fln-env` may implement, which excludes the one crate that should. So the
    /// property is enforced by a structure-guard allowlist rather than by the type system,
    /// and this comment exists so the next reader knows that is a deliberate limit rather
    /// than an oversight.
    ///
    /// [`Environment::add_decl`] is the *unbounded* sibling and has no legitimate
    /// production caller anywhere.
    pub fn plan_add_decl(
        &self,
        info: ConstantInfo,
        budget: DeclarationBudget,
        collision_budget: CollisionBudget,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<DeclarationPlan> {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return Outcome::complete(DeclarationPlan::DuplicateName { name });
        }
        let usage = match preflight_declaration(&info, budget, cancellation).non_answer_for() {
            Ok(non_answer) => return non_answer,
            Err(usage) => usage,
        };
        let provisional_digest = Environment::decl_content_digest(&info);
        Outcome::complete(DeclarationPlan::Prepared(PreparedDeclarationAdmission {
            schema: DECLARATION_PLAN_SCHEMA,
            info: Arc::new(info),
            provisional_digest,
            usage,
            base: self.clone(),
            admission_weight: u64::try_from(usage.expanded_weight).unwrap_or(u64::MAX),
            collision_budget,
        }))
    }

    /// Register an extension with its declared contracts.
    pub fn register_extension(
        &self,
        descriptor: ExtensionDescriptor,
    ) -> Result<Environment, EnvError> {
        let name = descriptor.name.clone();
        if self.extensions.contains_key(&name) {
            return Err(EnvError::DuplicateExtension { name });
        }
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self
                .extensions
                .insert(name, Arc::new(ExtensionState::new(descriptor))),
        })
    }

    /// Append one replay entry to a registered extension.
    pub fn push_extension_entry(
        &self,
        extension: &Name,
        payload: impl Into<Arc<[u8]>>,
    ) -> Result<Environment, EnvError> {
        let Some(state) = self.extensions.get(extension) else {
            return Err(EnvError::UnknownExtension {
                name: extension.clone(),
            });
        };
        let next = state.push_entry(payload);
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(extension.clone(), Arc::new(next)),
        })
    }

    pub fn extension(&self, name: &Name) -> Option<&ExtensionState> {
        self.extensions.get(name).map(Arc::as_ref)
    }

    /// Capture one registered extension under its declared checkpoint contract.
    /// A suffix base is another immutable environment snapshot; full-journal mode
    /// requires `None` and carries no ambient extension history.
    /// Cancellation is threaded through because capture proves ancestry by exact
    /// comparison when the digest accelerator only passes, and an input-sized proof a
    /// caller has withdrawn from must be abandonable. Exhaustion and cancellation are
    /// FL-INV-07 non-answers and arrive as [`Outcome::Inconclusive`]; a wrong descriptor
    /// or a non-prefix base is a completed verdict and arrives as `Err` inside
    /// [`Outcome::Complete`] (bead `fln-extension-history-checkpoint-identity-41s`).
    pub fn checkpoint_extension(
        &self,
        extension: &Name,
        base: Option<&Environment>,
        limits: CheckpointLimits,
        proof: ProofBudget,
        epoch: &ModuleEpoch,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<ExtensionCheckpoint, EnvError>> {
        let Some(state) = self.extension(extension) else {
            return Outcome::complete(Err(EnvError::UnknownExtension {
                name: extension.clone(),
            }));
        };
        let base_state = match base {
            Some(base) => match base.extension(extension) {
                Some(state) => Some(state),
                None => {
                    return Outcome::complete(Err(EnvError::UnknownExtension {
                        name: extension.clone(),
                    }));
                }
            },
            None => None,
        };
        state
            .try_checkpoint(base_state, limits, proof, epoch, cancellation)
            .map_complete(|captured| captured.map_err(EnvError::Checkpoint))
    }

    /// Apply a checkpoint to the matching registry slot and return a new isolated
    /// environment snapshot. Declarations and unrelated extensions remain shared.
    /// Non-answers are threaded for the same reason as
    /// [`Environment::checkpoint_extension`]: restore proves base identity by exact
    /// comparison when structural identity does not apply, and a cancelled or exhausted
    /// proof reached no verdict about the checkpoint.
    pub fn apply_extension_checkpoint(
        &self,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
        proof: ProofBudget,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<Environment, EnvError>> {
        let name = &checkpoint.descriptor().name;
        let Some(registered) = self.extension(name) else {
            return Outcome::complete(Err(EnvError::UnknownExtension { name: name.clone() }));
        };
        if checkpoint.mode() == CheckpointSemantics::FullJournal
            && registered.descriptor != *checkpoint.descriptor()
        {
            let error = if registered.descriptor.name != checkpoint.descriptor().name {
                CheckpointError::ExtensionNameMismatch {
                    expected: checkpoint.descriptor().name.clone(),
                    actual: registered.descriptor.name.clone(),
                }
            } else {
                CheckpointError::ContractMismatch {
                    expected: checkpoint.descriptor().clone(),
                    actual: registered.descriptor.clone(),
                }
            };
            return Outcome::complete(Err(EnvError::Checkpoint(error)));
        }
        let base = match checkpoint.mode() {
            CheckpointSemantics::JournalSuffix => Some(registered),
            CheckpointSemantics::FullJournal => None,
        };
        ExtensionState::try_restore(base, checkpoint, limits, proof, cancellation).map_complete(
            |restored| {
                restored
                    .map(|state| Environment {
                        constants: self.constants.clone(),
                        extensions: self.extensions.insert(name.clone(), Arc::new(state)),
                    })
                    .map_err(EnvError::Checkpoint)
            },
        )
    }

    /// The canonical content digest of one constant (Domain::DeclContent): the
    /// deterministic projection the logical root aggregates. Byte-level olean parity
    /// is the codec's business; this digest is FrankenLean's own identity.
    #[forbid(clippy::as_conversions)]
    pub fn decl_content_digest(info: &ConstantInfo) -> Digest {
        hash(Domain::DeclContent, &Environment::decl_content_bytes(info))
    }

    /// The canonical `Domain::DeclContent` byte stream for one constant.
    ///
    /// One encoder, so the digest and the canonical-byte usage fact cannot diverge — a
    /// measured byte count taken from a second implementation would be a fact about the
    /// wrong bytes (bead `franken_lean-j8h`).
    fn decl_content_bytes(info: &ConstantInfo) -> Vec<u8> {
        let mut w = CanonWriter::new();
        w.str(info.kind_name());
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(usize_to_u64(base.level_params.len()));
        for p in &base.level_params {
            p.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Axiom(v) => w.bool(v.is_unsafe),
            ConstantInfo::Defn(v) => {
                v.value.write_body(&mut w);
                match v.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(h) => {
                        w.u8(2);
                        w.u32(h);
                    }
                }
                w.u8(definition_safety_tag(v.safety));
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Thm(v) => {
                v.value.write_body(&mut w);
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Opaque(v) => {
                v.value.write_body(&mut w);
                w.bool(v.is_unsafe);
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Quot(v) => w.u8(quot_kind_tag(v.kind)),
            ConstantInfo::Induct(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_nested);
                w.bool(v.is_rec);
                w.bool(v.is_unsafe);
                w.bool(v.is_reflexive);
                w.u64(usize_to_u64(v.ctors.len()));
                for n in &v.ctors {
                    n.write_body(&mut w);
                }
                // The mutual-inductive block is part of the declaration's content
                // (as it is for `Defn`/`Thm`): two inductives identical except for
                // their block grouping are distinct declarations and must not share
                // a content digest.
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Ctor(v) => {
                v.induct.write_body(&mut w);
                w.u32(v.cidx);
                w.u32(v.num_params);
                w.u32(v.num_fields);
                w.bool(v.is_unsafe);
            }
            ConstantInfo::Rec(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_motives);
                w.u32(v.num_minors);
                w.bool(v.k);
                w.bool(v.is_unsafe);
                w.u64(usize_to_u64(v.rules.len()));
                for rule in &v.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                // The mutual block is content here too (mirrors `Defn`/`Thm`).
                write_mutual_membership(&mut w, &v.all);
            }
        }
        w.into_bytes()
    }

    /// The logical root of this commit: declarations + extension deltas + options —
    /// and nothing else (wall-clock, paths, and schedule have no way in).
    pub fn logical_root(&self, options: &KVMap) -> LogicalRoot {
        let mut builder = LogicalRootBuilder::new();
        for (name, info) in self.constants.iter() {
            builder.add_decl(name, Environment::decl_content_digest(info));
        }
        for (name, state) in self.extensions.iter() {
            builder.add_extension_delta(name, state.content_digest());
        }
        builder.set_options(options);
        builder.finalize()
    }

    /// The operational-metadata root: host facts, paths, timings — everything the
    /// logical root deliberately excludes, digested separately so receipts can carry
    /// both without ever mixing them.
    pub fn operational_root(metadata: &KVMap) -> Digest {
        hash(Domain::OperationalMeta, &metadata.to_canonical_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{
        AxiomVal, ConstantVal, ConstructorVal, DefinitionVal, InductiveVal, OpaqueVal, QuotVal,
        RecursorRule, RecursorVal, TheoremVal,
    };
    use crate::pmap::CollisionResource;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::DataValue;
    use fln_core::outcome::{Authority, CacheAdmission, InconclusiveCause};
    use std::collections::HashSet;

    fn n(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn axiom(name: &str) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }

    /// Successor chains over every enum whose variants reach `Domain::DeclContent`.
    ///
    /// `definition_safety_tag` and `quot_kind_tag` already force a new variant to be
    /// *tagged*, because their matches are exhaustive. Nothing forced a new variant
    /// into the *test matrix* while `DeclarationTagCase::ALL` was a hand-written
    /// array: the author would satisfy the tag matches, ship, and the variant would
    /// carry no golden, no pairwise-distinction row, no named mutant and no E2E
    /// record — silently untested identity, which is this bead's own failure mode one
    /// level up. Rust has no enum reflection, so the forcing function has to be an
    /// exhaustive match that *generates* the matrix rather than one that merely
    /// validates it. Adding a variant fails to compile here until it is placed in a
    /// chain, and the chains are what build `ALL`, so tagging a variant and covering
    /// it become the same edit.
    const fn succ_definition_safety(safety: DefinitionSafety) -> Option<DefinitionSafety> {
        match safety {
            DefinitionSafety::Unsafe => Some(DefinitionSafety::Safe),
            DefinitionSafety::Safe => Some(DefinitionSafety::Partial),
            DefinitionSafety::Partial => None,
        }
    }

    const fn succ_quot_kind(kind: QuotKind) -> Option<QuotKind> {
        match kind {
            QuotKind::Type => Some(QuotKind::Ctor),
            QuotKind::Ctor => Some(QuotKind::Lift),
            QuotKind::Lift => Some(QuotKind::Ind),
            QuotKind::Ind => None,
        }
    }

    const FIRST_DEFINITION_SAFETY: DefinitionSafety = DefinitionSafety::Unsafe;
    const FIRST_QUOT_KIND: QuotKind = QuotKind::Type;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DeclarationTagCase {
        Definition(DefinitionSafety),
        Quotient(QuotKind),
    }

    impl DeclarationTagCase {
        /// Frozen number of declaration-tag cases, and the count
        /// `scripts/evidence.py`'s strict `declaration-tag-matrix` validator pins;
        /// the two move together.
        ///
        /// Lengthening a successor chain without bumping this fails const evaluation
        /// of `derive_all`. Shortening one fails it too — that is the single way to
        /// satisfy an exhaustive match while orphaning a variant (write
        /// `New => None` and drop the arm that reached `Partial`), so the count is
        /// asserted in both directions rather than as an upper bound.
        const COUNT: usize = 7;

        const FIRST: DeclarationTagCase = DeclarationTagCase::Definition(FIRST_DEFINITION_SAFETY);

        /// Derived from the successor chains, never hand-written. Every golden, every
        /// pairwise-distinction check, every named mutant and the E2E producer iterate
        /// this, so generating it is what makes coverage total rather than customary.
        const ALL: [DeclarationTagCase; Self::COUNT] = Self::derive_all();

        const fn succ(self) -> Option<DeclarationTagCase> {
            match self {
                DeclarationTagCase::Definition(safety) => match succ_definition_safety(safety) {
                    Some(next) => Some(DeclarationTagCase::Definition(next)),
                    // The families are chained end to end so that one walk enumerates
                    // the whole matrix: the definition chain running out enters the
                    // quotient chain.
                    None => Some(DeclarationTagCase::Quotient(FIRST_QUOT_KIND)),
                },
                DeclarationTagCase::Quotient(kind) => match succ_quot_kind(kind) {
                    Some(next) => Some(DeclarationTagCase::Quotient(next)),
                    None => None,
                },
            }
        }

        const fn derive_all() -> [DeclarationTagCase; Self::COUNT] {
            let mut cases = [Self::FIRST; Self::COUNT];
            let mut cursor = Self::FIRST;
            let mut filled = 1;
            while let Some(next) = cursor.succ() {
                // A chain that is too long, or one that cycles, is caught here rather
                // than by writing past the end of the array.
                assert!(
                    filled < Self::COUNT,
                    "declaration-tag successor chains yield more cases than DeclarationTagCase::COUNT"
                );
                cases[filled] = next;
                cursor = next;
                filled += 1;
            }
            assert!(
                filled == Self::COUNT,
                "declaration-tag successor chains yield fewer cases than DeclarationTagCase::COUNT: a variant is orphaned"
            );
            cases
        }

        const fn family(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(_) => "definition_safety",
                DeclarationTagCase::Quotient(_) => "quot_kind",
            }
        }

        const fn variant(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => "unsafe",
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => "safe",
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => "partial",
                DeclarationTagCase::Quotient(QuotKind::Type) => "type",
                DeclarationTagCase::Quotient(QuotKind::Ctor) => "ctor",
                DeclarationTagCase::Quotient(QuotKind::Lift) => "lift",
                DeclarationTagCase::Quotient(QuotKind::Ind) => "ind",
            }
        }

        const fn kind_name(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(_) => "definition",
                DeclarationTagCase::Quotient(_) => "quotient",
            }
        }

        const fn canonical_tag(self) -> u8 {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => 0,
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => 1,
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => 2,
                DeclarationTagCase::Quotient(QuotKind::Type) => 0,
                DeclarationTagCase::Quotient(QuotKind::Ctor) => 1,
                DeclarationTagCase::Quotient(QuotKind::Lift) => 2,
                DeclarationTagCase::Quotient(QuotKind::Ind) => 3,
            }
        }

        const fn production_tag(self) -> u8 {
            match self {
                DeclarationTagCase::Definition(safety) => definition_safety_tag(safety),
                DeclarationTagCase::Quotient(kind) => quot_kind_tag(kind),
            }
        }

        /// Frozen `rich-same-name-v1` complete-stream goldens. These constants
        /// prevent coordinated drift in both the production encoder and the
        /// independent in-file model from silently redefining declaration identity.
        const fn golden_stream_bytes(self) -> usize {
            match self {
                DeclarationTagCase::Definition(_) => 286,
                DeclarationTagCase::Quotient(_) => 157,
            }
        }

        const fn golden_stream_hash(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => {
                    "157d1d61733828db775de4ee898c84ab608f57ca609965b7d8aba3ef9e3a1a5e"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => {
                    "e3a242872a3ffd8c515331f5821c1b42f81780060413feb33f2d63ca8aeb697d"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => {
                    "00a37c5b26ce2df45b79a0e5ddc0b32fe7ba3fd16e2267a8b199a3a2a5421f52"
                }
                DeclarationTagCase::Quotient(QuotKind::Type) => {
                    "d85f3e7116bf264784bad45e2d9a9acc9ad69ca15c2387f73d390b51c1a52674"
                }
                DeclarationTagCase::Quotient(QuotKind::Ctor) => {
                    "7a209bee80a459d0eddd0e82ced0b96345895dfdf11cb420729783eff42fe0a0"
                }
                DeclarationTagCase::Quotient(QuotKind::Lift) => {
                    "706326aa022cfa4b76f80ea32c04ad0aef70d796da8762b86771b3b4d42937ad"
                }
                DeclarationTagCase::Quotient(QuotKind::Ind) => {
                    "32cecea0df45330f5ea249486eb8c0dd4ff236dc27ca90e79122de9f7e3d365a"
                }
            }
        }

        const fn golden_digest(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => {
                    "e6e48d3267b42c87425ac704373120f0c4624c591f6c3218412cdfd5464443ab"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => {
                    "5995ca5cc9f678192cb1700abb6bc18a87af673a6f3285cc9d55caa9b20bb6b0"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => {
                    "5a313316b29da1dab36b88cd02d1d52b96b025a3cb6b9682d0ba10eb59ae76d1"
                }
                DeclarationTagCase::Quotient(QuotKind::Type) => {
                    "64a010c5b799b51b464f4394db8f06a4d7f0c8f98a89bc634cddf3936f3a431f"
                }
                DeclarationTagCase::Quotient(QuotKind::Ctor) => {
                    "d8fc3394629ba859ee37b56dd6d937d787aa86b607b02941091a8699983e0589"
                }
                DeclarationTagCase::Quotient(QuotKind::Lift) => {
                    "804e0ddc5baea6f095d63662b95d303a11c7f33cc92c8d5c77efeb96df021706"
                }
                DeclarationTagCase::Quotient(QuotKind::Ind) => {
                    "7e0d5346e053845bda23a4fb2f3edf80f7daa3f86898a129d66d0531e0e22066"
                }
            }
        }

        const fn golden_root(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => {
                    "87d17589cf2a1222d19498e2c4b398107043556cf546281992f223cb9f5a94a9"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => {
                    "69a4eda482d75712ead5edea8d70692319ac48b9b532b9944bd681e5d94b19ac"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => {
                    "d234cc1f558ec38a8a8c6ba090236f2239dcd3694b38ea955262cb709016ec47"
                }
                DeclarationTagCase::Quotient(QuotKind::Type) => {
                    "4bf46c6cd5c5282272a303bed04d36d4a5c3d84684b3b588e821564368e10a54"
                }
                DeclarationTagCase::Quotient(QuotKind::Ctor) => {
                    "05b8fe41a9783da42b03c43ec645d7fd239f924ac1996c2112819d7046aa26fe"
                }
                DeclarationTagCase::Quotient(QuotKind::Lift) => {
                    "08dc046203aec4b81143baad0afcebd7655e77e9a4fc813d61fd67fb304edae5"
                }
                DeclarationTagCase::Quotient(QuotKind::Ind) => {
                    "4edbf7598d4cbc73861526c523b02b126a13eaaa29e5f16b6a4a5b55e39b6414"
                }
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DeclarationTagDigestModel {
        Canonical,
        OmitTag,
        DebugText,
        CastAfterSourceReorder,
        MoveTagAcrossAdjacentField,
        WrongDomain,
    }

    fn tagged_declaration(case: DeclarationTagCase, unique_name: bool) -> ConstantInfo {
        let name = if unique_name {
            format!("tagged.{}.{}", case.family(), case.variant())
        } else {
            "tagged".to_owned()
        };
        let name = Name::str(Name::anonymous(), name);
        let base = ConstantVal {
            name: name.clone(),
            level_params: vec![n("u"), n("v")],
            type_: Expr::app(
                Expr::sort(Level::param(n("u"))),
                Expr::const_(n("carrier"), vec![Level::param(n("v"))]),
            ),
        };
        match case {
            DeclarationTagCase::Definition(safety) => ConstantInfo::Defn(DefinitionVal {
                base,
                value: Expr::app(
                    Expr::const_(n("body"), vec![Level::param(n("u"))]),
                    Expr::sort(Level::param(n("v"))),
                ),
                hints: ReducibilityHints::Regular(0xa1b2_c3d4),
                safety,
                all: vec![name, n("peer")],
            }),
            DeclarationTagCase::Quotient(kind) => ConstantInfo::Quot(QuotVal { base, kind }),
        }
    }

    fn write_modeled_declaration_tag(
        w: &mut CanonWriter,
        case: DeclarationTagCase,
        model: DeclarationTagDigestModel,
    ) {
        match model {
            DeclarationTagDigestModel::OmitTag => {}
            DeclarationTagDigestModel::DebugText => w.str(case.variant()),
            DeclarationTagDigestModel::CastAfterSourceReorder => {
                let source_order_tag = match case {
                    DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => 1,
                    DeclarationTagCase::Definition(DefinitionSafety::Safe) => 2,
                    DeclarationTagCase::Definition(DefinitionSafety::Partial) => 0,
                    DeclarationTagCase::Quotient(QuotKind::Type) => 1,
                    DeclarationTagCase::Quotient(QuotKind::Ctor) => 2,
                    DeclarationTagCase::Quotient(QuotKind::Lift) => 3,
                    DeclarationTagCase::Quotient(QuotKind::Ind) => 0,
                };
                w.u8(source_order_tag);
            }
            DeclarationTagDigestModel::Canonical
            | DeclarationTagDigestModel::MoveTagAcrossAdjacentField
            | DeclarationTagDigestModel::WrongDomain => w.u8(case.canonical_tag()),
        }
    }

    /// Control-flow-independent model of the complete Definition/Quotient
    /// declaration streams. It intentionally avoids production kind/base/tag and
    /// mutual-membership helpers.
    fn modeled_tagged_declaration_bytes(
        case: DeclarationTagCase,
        info: &ConstantInfo,
        model: DeclarationTagDigestModel,
    ) -> Vec<u8> {
        let base = match (case, info) {
            (DeclarationTagCase::Definition(_), ConstantInfo::Defn(value)) => &value.base,
            (DeclarationTagCase::Quotient(_), ConstantInfo::Quot(value)) => &value.base,
            _ => unreachable!("tagged declaration case and fixture must agree"),
        };
        let mut w = CanonWriter::new();
        w.str(case.kind_name());
        base.name.write_body(&mut w);
        w.u64(usize_to_u64(base.level_params.len()));
        for parameter in &base.level_params {
            parameter.write_body(&mut w);
        }
        if matches!(
            (case, model),
            (
                DeclarationTagCase::Quotient(_),
                DeclarationTagDigestModel::MoveTagAcrossAdjacentField
            )
        ) {
            write_modeled_declaration_tag(&mut w, case, model);
        }
        base.type_.write_body(&mut w);
        match (case, info) {
            (DeclarationTagCase::Definition(_), ConstantInfo::Defn(value)) => {
                value.value.write_body(&mut w);
                let move_tag_across_adjacent_field =
                    matches!(model, DeclarationTagDigestModel::MoveTagAcrossAdjacentField);
                if move_tag_across_adjacent_field {
                    write_modeled_declaration_tag(&mut w, case, model);
                }
                match value.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(height) => {
                        w.u8(2);
                        w.u32(height);
                    }
                }
                if !move_tag_across_adjacent_field {
                    write_modeled_declaration_tag(&mut w, case, model);
                }
                w.u64(usize_to_u64(value.all.len()));
                for member in &value.all {
                    member.write_body(&mut w);
                }
            }
            (DeclarationTagCase::Quotient(_), ConstantInfo::Quot(_)) => {
                if !matches!(model, DeclarationTagDigestModel::MoveTagAcrossAdjacentField) {
                    write_modeled_declaration_tag(&mut w, case, model);
                }
            }
            _ => unreachable!("tagged declaration case and fixture must agree"),
        }
        w.into_bytes()
    }

    fn modeled_tagged_declaration_digest(
        case: DeclarationTagCase,
        info: &ConstantInfo,
        model: DeclarationTagDigestModel,
    ) -> Digest {
        let bytes = modeled_tagged_declaration_bytes(case, info, model);
        let domain = if matches!(model, DeclarationTagDigestModel::WrongDomain) {
            Domain::Fixture
        } else {
            Domain::DeclContent
        };
        hash(domain, &bytes)
    }

    fn tagged_environment(cases: impl IntoIterator<Item = DeclarationTagCase>) -> Environment {
        let mut environment = Environment::new();
        for case in cases {
            environment = environment
                .add_decl(tagged_declaration(case, true))
                .expect("tagged declaration fixture builds");
        }
        environment
    }

    fn permuted_tag_cases(
        cases: &[DeclarationTagCase],
        worker_index: usize,
    ) -> Vec<DeclarationTagCase> {
        let start = worker_index % cases.len();
        let step = 1 + (worker_index / cases.len()) % (cases.len() - 1);
        (0..cases.len())
            .map(|offset| cases[(start + offset * step) % cases.len()])
            .collect()
    }

    fn tag_case_order_id(cases: &[DeclarationTagCase]) -> Digest {
        let mut w = CanonWriter::new();
        w.str("fln.test.declaration-tag-order");
        w.u16(1);
        w.u64(usize_to_u64(cases.len()));
        for case in cases {
            w.str(case.family());
            w.str(case.variant());
        }
        hash(Domain::Fixture, &w.into_bytes())
    }

    #[derive(Debug, Clone, Copy)]
    enum AllBearingKind {
        Definition,
        Theorem,
        Opaque,
        Inductive,
        Recursor,
    }

    impl AllBearingKind {
        const ALL: [AllBearingKind; 5] = [
            AllBearingKind::Definition,
            AllBearingKind::Theorem,
            AllBearingKind::Opaque,
            AllBearingKind::Inductive,
            AllBearingKind::Recursor,
        ];

        const fn label(self) -> &'static str {
            match self {
                AllBearingKind::Definition => "definition",
                AllBearingKind::Theorem => "theorem",
                AllBearingKind::Opaque => "opaque",
                AllBearingKind::Inductive => "inductive",
                AllBearingKind::Recursor => "recursor",
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    enum MembershipModel {
        Canonical,
        DropList,
        OmitCount,
        SortMembers,
    }

    fn all_bearing_decl(kind: AllBearingKind, all: Vec<Name>) -> ConstantInfo {
        let body = || Expr::const_(n("body"), vec![Level::param(n("u"))]);
        let base = || ConstantVal {
            name: n("d"),
            level_params: vec![n("u")],
            type_: Expr::sort(Level::param(n("u"))),
        };
        match kind {
            AllBearingKind::Definition => ConstantInfo::Defn(DefinitionVal {
                base: base(),
                value: body(),
                hints: ReducibilityHints::Regular(7),
                safety: DefinitionSafety::Partial,
                all,
            }),
            AllBearingKind::Theorem => ConstantInfo::Thm(TheoremVal {
                base: base(),
                value: body(),
                all,
            }),
            AllBearingKind::Opaque => ConstantInfo::Opaque(OpaqueVal {
                base: base(),
                value: body(),
                is_unsafe: true,
                all,
            }),
            AllBearingKind::Inductive => ConstantInfo::Induct(InductiveVal {
                base: base(),
                num_params: 2,
                num_indices: 1,
                all,
                ctors: vec![n("mk"), n("mkAlt")],
                num_nested: 3,
                is_rec: true,
                is_unsafe: true,
                is_reflexive: true,
            }),
            AllBearingKind::Recursor => ConstantInfo::Rec(RecursorVal {
                base: base(),
                all,
                num_params: 2,
                num_indices: 1,
                num_motives: 1,
                num_minors: 2,
                rules: vec![
                    RecursorRule {
                        ctor: n("mk"),
                        nfields: 3,
                        rhs: body(),
                    },
                    RecursorRule {
                        ctor: n("mkAlt"),
                        nfields: 4,
                        rhs: Expr::const_(n("bodyAlt"), vec![Level::zero()]),
                    },
                ],
                k: true,
                is_unsafe: true,
            }),
        }
    }

    fn write_membership_model(w: &mut CanonWriter, members: &[Name], model: MembershipModel) {
        match model {
            MembershipModel::Canonical => {
                w.u64(usize_to_u64(members.len()));
                for member in members {
                    member.write_body(w);
                }
            }
            MembershipModel::DropList => {}
            MembershipModel::OmitCount => {
                for member in members {
                    member.write_body(w);
                }
            }
            MembershipModel::SortMembers => {
                let mut sorted = members.to_vec();
                sorted.sort();
                w.u64(usize_to_u64(sorted.len()));
                for member in &sorted {
                    member.write_body(w);
                }
            }
        }
    }

    /// Control-flow-independent declaration layout model for the five variants
    /// carrying mutual-block membership. It intentionally shares only the primitive
    /// canonical codecs and registered hash implementation with production.
    fn modeled_all_bearing_digest(
        info: &ConstantInfo,
        membership_model: MembershipModel,
        domain: Domain,
    ) -> Digest {
        let mut w = CanonWriter::new();
        let kind_name = match info {
            ConstantInfo::Defn(_) => "definition",
            ConstantInfo::Thm(_) => "theorem",
            ConstantInfo::Opaque(_) => "opaque",
            ConstantInfo::Induct(_) => "inductive",
            ConstantInfo::Rec(_) => "recursor",
            _ => unreachable!("the model accepts only all-bearing declarations"),
        };
        w.str(kind_name);
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(usize_to_u64(base.level_params.len()));
        for parameter in &base.level_params {
            parameter.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Defn(value) => {
                value.value.write_body(&mut w);
                match value.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(height) => {
                        w.u8(2);
                        w.u32(height);
                    }
                }
                let safety_tag = match value.safety {
                    DefinitionSafety::Unsafe => 0,
                    DefinitionSafety::Safe => 1,
                    DefinitionSafety::Partial => 2,
                };
                w.u8(safety_tag);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Thm(value) => {
                value.value.write_body(&mut w);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Opaque(value) => {
                value.value.write_body(&mut w);
                w.bool(value.is_unsafe);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Induct(value) => {
                w.u32(value.num_params);
                w.u32(value.num_indices);
                w.u32(value.num_nested);
                w.bool(value.is_rec);
                w.bool(value.is_unsafe);
                w.bool(value.is_reflexive);
                w.u64(usize_to_u64(value.ctors.len()));
                for ctor in &value.ctors {
                    ctor.write_body(&mut w);
                }
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Rec(value) => {
                w.u32(value.num_params);
                w.u32(value.num_indices);
                w.u32(value.num_motives);
                w.u32(value.num_minors);
                w.bool(value.k);
                w.bool(value.is_unsafe);
                w.u64(usize_to_u64(value.rules.len()));
                for rule in &value.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                write_membership_model(&mut w, &value.all, membership_model);
            }
            _ => unreachable!("the model accepts only all-bearing declarations"),
        }
        hash(domain, &w.into_bytes())
    }

    fn canonical_name_body_bytes(names: &[Name]) -> usize {
        names
            .iter()
            .map(|name| {
                let mut w = CanonWriter::new();
                name.write_body(&mut w);
                w.into_bytes().len()
            })
            .sum()
    }

    fn descriptor(name: &str) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: n(name),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        }
    }

    #[test]
    fn add_find_and_the_one_name_one_constant_law() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        assert_eq!(env.len(), 1);
        assert_eq!(env.find(&n("a")).expect("found").kind_name(), "axiom");
        assert!(env.find(&n("b")).is_none());
        let dup = env.add_decl(axiom("a")).expect_err("duplicate refused");
        assert_eq!(dup, EnvError::DuplicateDeclaration { name: n("a") });
    }

    #[test]
    fn snapshots_are_isolated_forks() {
        let base = Environment::new().add_decl(axiom("a")).expect("adds");
        let fork = base.clone(); // O(1) snapshot
        let extended = base.add_decl(axiom("b")).expect("adds");
        assert_eq!(
            fork.len(),
            1,
            "mutation after fork is invisible to the fork"
        );
        assert_eq!(extended.len(), 2);
        assert!(fork.find(&n("b")).is_none());
        // And the fork can diverge independently.
        let fork2 = fork.add_decl(axiom("c")).expect("adds");
        assert!(extended.find(&n("c")).is_none());
        assert!(fork2.find(&n("b")).is_none());
    }

    #[test]
    fn logical_roots_are_insertion_order_independent_and_semantic() {
        let forward = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("c")))
            .expect("builds");
        let reverse = Environment::new()
            .add_decl(axiom("c"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("a")))
            .expect("builds");
        let opts = KVMap::new();
        assert_eq!(forward.logical_root(&opts), reverse.logical_root(&opts));

        // Different content ⇒ different root.
        let other = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .expect("builds");
        assert_ne!(forward.logical_root(&opts), other.logical_root(&opts));

        // Options are part of the logical root.
        let mut opts2 = KVMap::new();
        opts2.insert(n("maxHeartbeats"), DataValue::OfNat(400_000));
        assert_ne!(forward.logical_root(&opts), forward.logical_root(&opts2));
    }

    #[test]
    fn extension_entries_enter_the_logical_root_in_order() {
        let opts = KVMap::new();
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers");
        let one = env
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let two = one
            .push_extension_entry(&n("simpExt"), &b"e2"[..])
            .expect("pushes");
        assert_ne!(env.logical_root(&opts), one.logical_root(&opts));
        assert_ne!(one.logical_root(&opts), two.logical_root(&opts));
        // Replay order is preserved exactly.
        let entries: Vec<&[u8]> = two
            .extension(&n("simpExt"))
            .expect("registered")
            .entries()
            .map(|e| &*e.payload)
            .collect();
        assert_eq!(entries, vec![b"e1".as_slice(), b"e2"]);
        // Unknown extension is a typed refusal.
        assert_eq!(
            env.push_extension_entry(&n("ghost"), &b"x"[..]),
            Err(EnvError::UnknownExtension { name: n("ghost") })
        );
    }

    #[test]
    fn environment_checkpoint_apply_preserves_exact_roots_and_unrelated_state() {
        let limits = CheckpointLimits::new(100, 10_000);
        let base = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"base"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("base environment builds");
        let target = base
            .push_extension_entry(&n("simpExt"), &b"suffix-a"[..])
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"suffix-b"[..]))
            .expect("target environment builds");
        let checkpoint = completed(target.checkpoint_extension(
            &n("simpExt"),
            Some(&base),
            limits,
            ProofBudget::UNBOUNDED,
            &crate::extensions::fixture_epoch(),
            None,
        ))
        .expect("environment suffix captures");
        let restored = completed(base.apply_extension_checkpoint(
            &checkpoint,
            limits,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect("environment suffix applies");

        assert_eq!(restored, target);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            target.logical_root(&KVMap::new())
        );
        assert_eq!(restored.find(&n("a")), target.find(&n("a")));
        assert_eq!(
            restored.extension(&n("otherExt")),
            target.extension(&n("otherExt"))
        );

        let divergent = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"wrong"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("same-length divergent branch builds");
        assert!(matches!(
            completed(divergent.apply_extension_checkpoint(
                &checkpoint,
                limits,
                ProofBudget::UNBOUNDED,
                None
            )),
            Err(EnvError::Checkpoint(
                CheckpointError::BaseHistoryMismatch { .. }
            ))
        ));
        assert_eq!(
            divergent
                .extension(&n("simpExt"))
                .expect("still registered")
                .entries()
                .last()
                .expect("one entry")
                .payload
                .as_ref(),
            b"wrong"
        );
    }

    #[test]
    fn environment_full_checkpoint_replaces_only_the_registered_journal() {
        let limits = CheckpointLimits::new(100, 10_000);
        let full_descriptor = ExtensionDescriptor {
            checkpoint: CheckpointSemantics::FullJournal,
            ..descriptor("fullExt")
        };
        let destination = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(full_descriptor))
            .expect("destination builds");
        let source = destination
            .push_extension_entry(&n("fullExt"), &b"one"[..])
            .and_then(|env| env.push_extension_entry(&n("fullExt"), &b"two"[..]))
            .expect("source builds");
        let checkpoint = completed(source.checkpoint_extension(
            &n("fullExt"),
            None,
            limits,
            ProofBudget::UNBOUNDED,
            &crate::extensions::fixture_epoch(),
            None,
        ))
        .expect("full environment checkpoint captures");
        let restored = completed(destination.apply_extension_checkpoint(
            &checkpoint,
            limits,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect("full checkpoint applies without a semantic base");
        assert_eq!(restored, source);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            source.logical_root(&KVMap::new())
        );
        assert!(matches!(
            completed(source.checkpoint_extension(
                &n("ghost"),
                None,
                limits,
                ProofBudget::UNBOUNDED,
                &crate::extensions::fixture_epoch(),
                None
            )),
            Err(EnvError::UnknownExtension { .. })
        ));
    }

    #[test]
    fn extension_contracts_enter_the_logical_root() {
        let root = |merge, checkpoint, provenance| {
            let descriptor = ExtensionDescriptor {
                name: n("contractExt"),
                merge,
                checkpoint,
                provenance,
            };
            Environment::new()
                .register_extension(descriptor)
                .and_then(|env| env.push_extension_entry(&n("contractExt"), &b"entry"[..]))
                .expect("extension environment builds")
                .logical_root(&KVMap::new())
        };

        let append = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let append_again = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_eq!(
            append, append_again,
            "identical extension contracts and journals have stable identity"
        );

        let set_union = root(
            MergeSemantics::SetUnion,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let review = root(
            MergeSemantics::ConflictsRequireReview,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, set_union, "merge semantics enter the root");
        assert_ne!(append, review, "merge semantics enter the root");
        assert_ne!(
            set_union, review,
            "every merge variant has distinct identity"
        );

        let full_journal = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::FullJournal,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, full_journal, "checkpoint semantics enter the root");

        let opaque = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Opaque,
        );
        assert_ne!(append, opaque, "payload provenance enters the root");
    }

    #[test]
    fn add_decl_preserves_extension_state() {
        // The mutant this kills: add_decl rebuilding the environment with empty
        // extensions (state silently dropped) — found surviving by the
        // env_snapshots E2E mutation lane, then pinned here forever.
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers")
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let with_decl = env.add_decl(axiom("a")).expect("adds");
        let state = with_decl
            .extension(&n("simpExt"))
            .expect("extension state survives add_decl");
        assert_eq!(state.len(), 1);
        // And the delta still reaches the logical root after the decl lands.
        let opts = KVMap::new();
        let bare = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.register_extension(descriptor("simpExt")))
            .expect("builds");
        assert_ne!(with_decl.logical_root(&opts), bare.logical_root(&opts));
    }

    #[test]
    fn operational_metadata_never_touches_the_logical_root() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        let opts = KVMap::new();
        let root = env.logical_root(&opts);

        let mut host_a = KVMap::new();
        host_a.insert(n("host"), DataValue::OfString("machine-a".into()));
        let mut host_b = KVMap::new();
        host_b.insert(n("host"), DataValue::OfString("machine-b".into()));

        // Same trusted environment, different hosts: same logical root, different
        // operational roots.
        assert_eq!(root, env.logical_root(&opts));
        assert_ne!(
            Environment::operational_root(&host_a),
            Environment::operational_root(&host_b)
        );
    }

    #[test]
    fn declaration_identity_tag_policy_is_const_exhaustive_and_cast_free() {
        const DEFINITION_TAGS: [u8; 3] = [
            definition_safety_tag(DefinitionSafety::Unsafe),
            definition_safety_tag(DefinitionSafety::Safe),
            definition_safety_tag(DefinitionSafety::Partial),
        ];
        const QUOTIENT_TAGS: [u8; 4] = [
            quot_kind_tag(QuotKind::Type),
            quot_kind_tag(QuotKind::Ctor),
            quot_kind_tag(QuotKind::Lift),
            quot_kind_tag(QuotKind::Ind),
        ];
        assert_eq!(DEFINITION_TAGS, [0, 1, 2]);
        assert_eq!(QUOTIENT_TAGS, [0, 1, 2, 3]);

        // The exact seven-row tag table, asserted against the *derived* case list
        // rather than against a hand-written one. A new variant cannot reach a digest
        // without joining a successor chain, joining one grows `ALL`, and growing
        // `ALL` changes this array's length — so the row must be written here before
        // the crate compiles again.
        const EXPECTED_TAG_TABLE: [(&str, &str, u8); DeclarationTagCase::COUNT] = [
            ("definition_safety", "unsafe", 0),
            ("definition_safety", "safe", 1),
            ("definition_safety", "partial", 2),
            ("quot_kind", "type", 0),
            ("quot_kind", "ctor", 1),
            ("quot_kind", "lift", 2),
            ("quot_kind", "ind", 3),
        ];
        let observed_tag_table: Vec<(&str, &str, u8)> = DeclarationTagCase::ALL
            .iter()
            .map(|case| (case.family(), case.variant(), case.production_tag()))
            .collect();
        assert_eq!(
            observed_tag_table.as_slice(),
            EXPECTED_TAG_TABLE.as_slice(),
            "the derived declaration-tag table drifted from its frozen seven rows"
        );

        let definition_variant_count = DeclarationTagCase::ALL
            .iter()
            .filter(|case| matches!(case, DeclarationTagCase::Definition(_)))
            .count();
        let quotient_variant_count = DeclarationTagCase::ALL
            .iter()
            .filter(|case| matches!(case, DeclarationTagCase::Quotient(_)))
            .count();
        assert_eq!(definition_variant_count, DEFINITION_TAGS.len());
        assert_eq!(quotient_variant_count, QUOTIENT_TAGS.len());

        for case in DeclarationTagCase::ALL {
            assert_eq!(
                case.production_tag(),
                case.canonical_tag(),
                "production and independently frozen tag tables diverged for {}/{}",
                case.family(),
                case.variant()
            );
        }
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-work\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"closed-tag-projection-policy\",\
             \"claim_scope\":\"closed_enum_tag_projection_only\",\
             \"evidence\":\"const_exhaustive_match_plus_forbid_as_conversions\",\
             \"matrix_source\":\"generated_from_exhaustive_succ_chains\",\
             \"definition_variant_count\":{definition_variant_count},\
             \"quotient_variant_count\":{quotient_variant_count},\
             \"tag_helper_output_bytes\":1,\
             \"tag_helper_input_dependent_iterations\":0,\
             \"tag_helper_owned_allocations\":0,\
             \"tag_helper_independent_cancellation_points\":0,\
             \"tag_helper_separate_resource_limit_required\":false,\
             \"enclosing_decl_content_budget_claim\":\"not_made\",\
             \"enclosing_decl_content_budget_api\":\"absent\",\
             \"resource_followup\":\"franken_lean-j8h\",\
             \"status\":\"pass\"}}"
        );
    }

    /// The coverage half of the `fln-amv.12` guard.
    ///
    /// The tag matches force a new variant to be *tagged*; the successor chains force
    /// it to be *covered*, and this proves the chains actually generate the matrix the
    /// goldens, mutants and E2E producer iterate. The three-way expectation for every
    /// enum that reaches declaration identity: a source-order **reorder** must change
    /// nothing, because the tags bind variant names rather than positions and a test
    /// that went red on a reorder would be asserting the bug; an **added** variant must
    /// fail to compile; a **changed tag value** must fail a frozen golden.
    #[test]
    fn declaration_identity_tag_matrix_is_generated_by_exhaustive_succ_chains() {
        // Walk each family's chain independently of `ALL`, so the generated matrix is
        // checked against the chains rather than against itself.
        let mut definition_chain: Vec<DefinitionSafety> = Vec::new();
        let mut safety = Some(FIRST_DEFINITION_SAFETY);
        while let Some(current) = safety {
            assert!(
                !definition_chain.contains(&current),
                "the DefinitionSafety successor chain revisits {current:?}, which would \
                 silently drop every variant after the cycle"
            );
            definition_chain.push(current);
            safety = succ_definition_safety(current);
        }
        let mut quotient_chain: Vec<QuotKind> = Vec::new();
        let mut kind = Some(FIRST_QUOT_KIND);
        while let Some(current) = kind {
            assert!(
                !quotient_chain.contains(&current),
                "the QuotKind successor chain revisits {current:?}, which would silently \
                 drop every variant after the cycle"
            );
            quotient_chain.push(current);
            kind = succ_quot_kind(current);
        }
        assert_eq!(
            definition_chain.as_slice(),
            [
                DefinitionSafety::Unsafe,
                DefinitionSafety::Safe,
                DefinitionSafety::Partial,
            ]
            .as_slice(),
            "the DefinitionSafety chain no longer enumerates every variant"
        );
        assert_eq!(
            quotient_chain.as_slice(),
            [
                QuotKind::Type,
                QuotKind::Ctor,
                QuotKind::Lift,
                QuotKind::Ind,
            ]
            .as_slice(),
            "the QuotKind chain no longer enumerates every variant"
        );

        // Exact equality, which is the both-directions assertion: every chain member
        // reaches the matrix, and the matrix contains nothing that is not a chain
        // member. Either direction alone would accept a matrix that quietly dropped a
        // variant or invented one.
        let expected: Vec<DeclarationTagCase> = definition_chain
            .iter()
            .copied()
            .map(DeclarationTagCase::Definition)
            .chain(
                quotient_chain
                    .iter()
                    .copied()
                    .map(DeclarationTagCase::Quotient),
            )
            .collect();
        assert_eq!(
            DeclarationTagCase::ALL.as_slice(),
            expected.as_slice(),
            "the generated declaration-tag matrix diverged from the successor chains"
        );

        for (index, lhs) in DeclarationTagCase::ALL.iter().enumerate() {
            for rhs in &DeclarationTagCase::ALL[index + 1..] {
                assert_ne!(
                    lhs, rhs,
                    "the generated matrix repeats a case, so one variant carries two \
                     rows and another carries none"
                );
            }
        }

        // Tags must be pairwise distinct within a family, and deliberately *not*
        // dense: retiring a variant should retire its tag forever rather than force a
        // renumbering, and renumbering is precisely the silent identity rewrite this
        // bead exists to prevent.
        for family in [
            DeclarationTagCase::ALL
                .iter()
                .filter(|case| matches!(case, DeclarationTagCase::Definition(_)))
                .collect::<Vec<_>>(),
            DeclarationTagCase::ALL
                .iter()
                .filter(|case| matches!(case, DeclarationTagCase::Quotient(_)))
                .collect::<Vec<_>>(),
        ] {
            for (index, lhs) in family.iter().enumerate() {
                for rhs in &family[index + 1..] {
                    assert_ne!(
                        lhs.production_tag(),
                        rhs.production_tag(),
                        "{}/{} and {}/{} share a tag, so two declarations that differ \
                         collide on one identity",
                        lhs.family(),
                        lhs.variant(),
                        rhs.family(),
                        rhs.variant()
                    );
                }
            }
        }

        // Every frozen count in this file's declaration-tag coverage is pinned to
        // `COUNT`, so growing the matrix cannot leave a stale expectation quietly
        // passing on a subset. `scripts/evidence.py`'s strict validator pins the same
        // 7 for the `fln.e2e.declaration-tag-matrix` bundle.
        assert_eq!(DeclarationTagCase::COUNT, 7);
        assert_eq!(
            DeclarationTagCase::COUNT * (DeclarationTagCase::COUNT - 1) / 2,
            21,
            "the frozen 21 pairwise comparisons no longer match the matrix size"
        );
        assert_eq!(
            DeclarationTagCase::COUNT * 5,
            35,
            "the frozen 35 mutant discriminations no longer match the matrix size"
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-coverage\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"generated-tag-case-matrix\",\
             \"claim_scope\":\"declaration_tag_case_coverage_only\",\
             \"matrix_source\":\"generated_from_exhaustive_succ_chains\",\
             \"guard_kind\":\"compile_time_and_const_eval\",\
             \"added_variant_outcome\":\"compile_error\",\
             \"source_reorder_outcome\":\"no_digest_change\",\
             \"retagged_variant_outcome\":\"frozen_golden_failure\",\
             \"shortened_chain_outcome\":\"const_eval_assert\",\
             \"definition_chain_length\":{},\"quotient_chain_length\":{},\
             \"generated_case_count\":{},\"frozen_case_count\":{},\
             \"tag_density_asserted\":false,\
             \"tag_pairwise_distinct_within_family\":true,\
             \"status\":\"pass\"}}",
            definition_chain.len(),
            quotient_chain.len(),
            DeclarationTagCase::ALL.len(),
            DeclarationTagCase::COUNT
        );
    }

    #[test]
    fn declaration_identity_tag_matrix_matches_independent_model_and_roots() {
        let options = KVMap::new();
        let mut rows = Vec::with_capacity(DeclarationTagCase::ALL.len());
        for case in DeclarationTagCase::ALL {
            let info = tagged_declaration(case, false);
            let canonical_bytes =
                modeled_tagged_declaration_bytes(case, &info, DeclarationTagDigestModel::Canonical);
            let expected_digest = hash(Domain::DeclContent, &canonical_bytes);
            let actual_digest = Environment::decl_content_digest(&info);
            assert_eq!(
                actual_digest,
                expected_digest,
                "production declaration identity diverged from the independent model for {}/{}",
                case.family(),
                case.variant()
            );
            let repeated_digest =
                Environment::decl_content_digest(&tagged_declaration(case, false));
            assert_eq!(
                actual_digest,
                repeated_digest,
                "declaration digest was not repeatable for {}/{}",
                case.family(),
                case.variant()
            );

            let environment = Environment::new()
                .add_decl(info.clone())
                .expect("single tagged declaration fixture builds");
            let actual_root = environment.logical_root(&options);
            let mut expected_root_builder = LogicalRootBuilder::new();
            expected_root_builder.add_decl(info.name(), expected_digest);
            expected_root_builder.set_options(&options);
            let expected_root = expected_root_builder.finalize();
            assert_eq!(
                actual_root, expected_root,
                "tagged declaration digest did not propagate exactly into the logical root"
            );
            let repeated_root = Environment::new()
                .add_decl(tagged_declaration(case, false))
                .expect("repeated tagged declaration fixture builds")
                .logical_root(&options);
            assert_eq!(
                actual_root,
                repeated_root,
                "logical root was not repeatable for {}/{}",
                case.family(),
                case.variant()
            );

            let modeled_stream_hash = hash(Domain::Fixture, &canonical_bytes);
            assert_eq!(
                canonical_bytes.len(),
                case.golden_stream_bytes(),
                "complete modeled stream byte count drifted for {}/{}",
                case.family(),
                case.variant()
            );
            assert_eq!(
                modeled_stream_hash.to_hex(),
                case.golden_stream_hash(),
                "complete modeled stream hash drifted for {}/{}",
                case.family(),
                case.variant()
            );
            assert_eq!(
                actual_digest.to_hex(),
                case.golden_digest(),
                "declaration digest golden drifted for {}/{}",
                case.family(),
                case.variant()
            );
            assert_eq!(
                actual_root.0.to_hex(),
                case.golden_root(),
                "logical root golden drifted for {}/{}",
                case.family(),
                case.variant()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.declaration-tag-identity\",\"version\":1,\
                 \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
                 \"scenario\":\"rich-same-name-seven-row-matrix\",\
                 \"family\":\"{}\",\"variant\":\"{}\",\"canonical_tag\":{},\
                 \"fixture_id\":\"rich-same-name-v1\",\
                 \"modeled_canonical_stream_bytes\":{},\
                 \"modeled_canonical_stream_hash\":\"{modeled_stream_hash}\",\
                 \"expected_digest\":\"{expected_digest}\",\
                 \"actual_digest\":\"{actual_digest}\",\
                 \"repeated_digest\":\"{repeated_digest}\",\
                 \"expected_root\":\"{expected_root}\",\
                 \"actual_root\":\"{actual_root}\",\
                 \"repeated_root\":\"{repeated_root}\",\
                 \"frozen_stream_digest_root_goldens\":\"match\",\
                 \"root_propagation\":\"exact\",\"status\":\"pass\"}}",
                case.family(),
                case.variant(),
                case.canonical_tag(),
                canonical_bytes.len()
            );
            rows.push((case, actual_digest));
        }

        let unique_digests: HashSet<_> = rows.iter().map(|(_, digest)| *digest).collect();
        assert_eq!(
            unique_digests.len(),
            DeclarationTagCase::ALL.len(),
            "all seven declaration tag cases must have distinct content identity"
        );
        let mut pairwise_comparisons = 0usize;
        for (index, (lhs_case, lhs_digest)) in rows.iter().enumerate() {
            for (rhs_case, rhs_digest) in &rows[index + 1..] {
                assert_ne!(
                    lhs_digest,
                    rhs_digest,
                    "distinct tag cases aliased: {}/{} and {}/{}",
                    lhs_case.family(),
                    lhs_case.variant(),
                    rhs_case.family(),
                    rhs_case.variant()
                );
                pairwise_comparisons += 1;
            }
        }
        assert_eq!(pairwise_comparisons, 21);
        let case_count = DeclarationTagCase::COUNT;
        let unique_digest_count = unique_digests.len();
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-identity-summary\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"rich-same-name-seven-row-matrix\",\
             \"case_count\":{case_count},\"unique_digest_count\":{unique_digest_count},\
             \"pairwise_comparisons\":{pairwise_comparisons},\
             \"expected_pairwise_comparisons\":21,\
             \"model\":\"independent-complete-definition-quotient-stream-v1\",\
             \"root_propagation\":\"production-environment-exact\",\
             \"status\":\"pass\"}}"
        );
    }

    #[test]
    fn declaration_identity_tag_named_mutants_are_discriminated() {
        let options = KVMap::new();
        let mut digest_discriminations = 0usize;
        let mut root_propagation_discriminations = 0usize;
        for case in DeclarationTagCase::ALL {
            let info = tagged_declaration(case, false);
            let canonical_bytes =
                modeled_tagged_declaration_bytes(case, &info, DeclarationTagDigestModel::Canonical);
            let canonical_digest = Environment::decl_content_digest(&info);
            assert_eq!(
                canonical_digest,
                hash(Domain::DeclContent, &canonical_bytes),
                "production digest must equal the independent canonical stream model"
            );
            let canonical_stream_hash = hash(Domain::Fixture, &canonical_bytes);
            let canonical_environment = Environment::new()
                .add_decl(info.clone())
                .expect("single tagged declaration fixture builds");
            let canonical_root = canonical_environment.logical_root(&options);
            let mut canonical_model_root_builder = LogicalRootBuilder::new();
            canonical_model_root_builder.add_decl(info.name(), canonical_digest);
            canonical_model_root_builder.set_options(&options);
            assert_eq!(
                canonical_root,
                canonical_model_root_builder.finalize(),
                "production logical root must propagate the canonical modeled digest exactly"
            );

            for (mutation, model) in [
                ("omit_tag", DeclarationTagDigestModel::OmitTag),
                ("debug_text", DeclarationTagDigestModel::DebugText),
                (
                    "cast_after_source_reorder",
                    DeclarationTagDigestModel::CastAfterSourceReorder,
                ),
                (
                    "move_tag_across_adjacent_field",
                    DeclarationTagDigestModel::MoveTagAcrossAdjacentField,
                ),
                ("wrong_domain", DeclarationTagDigestModel::WrongDomain),
            ] {
                let mutated_bytes = modeled_tagged_declaration_bytes(case, &info, model);
                let mutated_digest = modeled_tagged_declaration_digest(case, &info, model);
                assert_ne!(
                    canonical_digest,
                    mutated_digest,
                    "{mutation} mutant survived for {}/{}",
                    case.family(),
                    case.variant()
                );
                match model {
                    DeclarationTagDigestModel::OmitTag => {
                        assert_eq!(
                            canonical_bytes.len(),
                            mutated_bytes.len() + 1,
                            "omitting the fixed tag must remove exactly one byte"
                        );
                        assert_ne!(
                            mutated_bytes, canonical_bytes,
                            "omitting the fixed tag must change the modeled stream"
                        );
                    }
                    DeclarationTagDigestModel::DebugText => {
                        assert_eq!(
                            mutated_bytes.len(),
                            canonical_bytes.len() + 7 + case.variant().len(),
                            "debug text must replace one byte with a length-prefixed variant"
                        );
                        assert_ne!(
                            mutated_bytes, canonical_bytes,
                            "debug text must change the modeled stream"
                        );
                    }
                    DeclarationTagDigestModel::CastAfterSourceReorder
                    | DeclarationTagDigestModel::MoveTagAcrossAdjacentField => {
                        assert_eq!(
                            mutated_bytes.len(),
                            canonical_bytes.len(),
                            "{mutation} must isolate value/order rather than stream size"
                        );
                        assert_ne!(
                            mutated_bytes, canonical_bytes,
                            "{mutation} must change bytes while preserving stream size"
                        );
                    }
                    DeclarationTagDigestModel::WrongDomain => {
                        assert_eq!(
                            mutated_bytes, canonical_bytes,
                            "wrong-domain mutation must change only domain separation"
                        );
                    }
                    DeclarationTagDigestModel::Canonical => {
                        unreachable!("canonical is not a mutation")
                    }
                }

                let mutated_stream_hash = hash(Domain::Fixture, &mutated_bytes);
                let mut mutated_root_builder = LogicalRootBuilder::new();
                mutated_root_builder.add_decl(info.name(), mutated_digest);
                mutated_root_builder.set_options(&options);
                let mutated_root = mutated_root_builder.finalize();
                assert_ne!(
                    canonical_root,
                    mutated_root,
                    "{mutation} root-propagation mutant survived for {}/{}",
                    case.family(),
                    case.variant()
                );
                digest_discriminations += 1;
                root_propagation_discriminations += 1;
                eprintln!(
                    "{{\"schema\":\"fln.unit.declaration-tag-mutant\",\"version\":1,\
                     \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
                     \"scenario\":\"named-tag-identity-mutants\",\
                     \"family\":\"{}\",\"variant\":\"{}\",\
                     \"mutation\":\"{mutation}\",\"canonical_tag\":{},\
                     \"root_mutation\":\"failed_root_propagation\",\
                     \"modeled_canonical_stream_bytes\":{},\
                     \"modeled_mutated_stream_bytes\":{},\
                     \"modeled_canonical_stream_hash\":\"{canonical_stream_hash}\",\
                     \"modeled_mutated_stream_hash\":\"{mutated_stream_hash}\",\
                     \"canonical_digest\":\"{canonical_digest}\",\
                     \"mutated_digest\":\"{mutated_digest}\",\
                     \"production_canonical_root\":\"{canonical_root}\",\
                     \"modeled_mutated_root\":\"{mutated_root}\",\
                     \"expected_digest_relation\":\"different\",\
                     \"actual_digest_relation\":\"different\",\
                     \"expected_root_relation\":\"different\",\
                     \"actual_root_relation\":\"different\",\"status\":\"pass\"}}",
                    case.family(),
                    case.variant(),
                    case.canonical_tag(),
                    canonical_bytes.len(),
                    mutated_bytes.len()
                );
            }
        }
        assert_eq!(
            digest_discriminations, 35,
            "five digest mutants must be killed for all seven cases"
        );
        assert_eq!(
            root_propagation_discriminations, 35,
            "all five digest mutants must propagate to distinct roots for all seven cases"
        );
        let case_count = DeclarationTagCase::COUNT;
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-mutants-summary\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"named-tag-identity-mutants\",\
             \"case_count\":{case_count},\"digest_mutation_classes\":5,\
             \"root_mutation_class\":\"failed_root_propagation\",\
             \"root_propagation_input_classes\":5,\
             \"digest_discriminations\":{digest_discriminations},\
             \"root_propagation_discriminations\":{root_propagation_discriminations},\
             \"total_discriminations\":{},\"status\":\"pass\"}}",
            digest_discriminations + root_propagation_discriminations
        );
    }

    #[test]
    fn declaration_identity_tag_is_stable_across_1_8_32_concurrent_complete_builds() {
        let cases = DeclarationTagCase::ALL.to_vec();
        let options = KVMap::new();
        let canonical_environment = tagged_environment(cases.iter().copied());

        let mut expected_root_builder = LogicalRootBuilder::new();
        for case in cases.iter().copied() {
            let info = tagged_declaration(case, true);
            let digest = modeled_tagged_declaration_digest(
                case,
                &info,
                DeclarationTagDigestModel::Canonical,
            );
            expected_root_builder.add_decl(info.name(), digest);
        }
        expected_root_builder.set_options(&options);
        let expected_root = expected_root_builder.finalize();
        assert_eq!(
            canonical_environment.logical_root(&options),
            expected_root,
            "canonical seven-declaration environment diverged from the aggregate model"
        );

        let omitted_root = tagged_environment(cases.iter().copied().skip(1)).logical_root(&options);
        assert_ne!(
            omitted_root, expected_root,
            "omitting one tagged declaration must change the aggregate root"
        );
        let mut source_order_root_builder = LogicalRootBuilder::new();
        for (index, case) in cases.iter().copied().enumerate() {
            let info = tagged_declaration(case, true);
            let model = if index == 0 {
                DeclarationTagDigestModel::CastAfterSourceReorder
            } else {
                DeclarationTagDigestModel::Canonical
            };
            source_order_root_builder.add_decl(
                info.name(),
                modeled_tagged_declaration_digest(case, &info, model),
            );
        }
        source_order_root_builder.set_options(&options);
        let source_order_root = source_order_root_builder.finalize();
        assert_ne!(
            source_order_root, expected_root,
            "one source-order-dependent tag must change the aggregate root"
        );

        for worker_count in [1usize, 8, 32] {
            let results = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker_index| {
                        let permutation = permuted_tag_cases(&cases, worker_index);
                        scope.spawn(move || {
                            let order_id = tag_case_order_id(&permutation);
                            let raw_order = permutation
                                .iter()
                                .map(|case| (case.family(), case.variant()))
                                .collect::<Vec<_>>();
                            let environment = tagged_environment(permutation.iter().copied());
                            let root = environment.logical_root(&KVMap::new());
                            (order_id, raw_order, environment, root)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("declaration tag worker joins"))
                    .collect::<Vec<_>>()
            });
            assert_eq!(results.len(), worker_count);
            let order_ids: HashSet<_> = results
                .iter()
                .map(|(order_id, _, _, _)| *order_id)
                .collect();
            let raw_orders: HashSet<_> = results
                .iter()
                .map(|(_, raw_order, _, _)| raw_order.clone())
                .collect();
            let distinct_full_permutations = raw_orders.len();
            assert_eq!(
                distinct_full_permutations, worker_count,
                "every worker must receive a distinct raw seven-case permutation"
            );
            assert_eq!(
                order_ids.len(),
                distinct_full_permutations,
                "hashed order ids must preserve the measured raw permutation cardinality"
            );

            let mut worker_roots = Vec::with_capacity(results.len());
            for (worker_index, (order_id, raw_order, environment, actual_root)) in
                results.iter().enumerate()
            {
                assert_eq!(
                    raw_order.len(),
                    DeclarationTagCase::ALL.len(),
                    "every worker order must contain all seven declaration-tag cases"
                );
                let raw_input_order_labels = raw_order
                    .iter()
                    .map(|(family, variant)| format!("{family}/{variant}"))
                    .collect::<Vec<_>>()
                    .join(">");
                assert_eq!(
                    environment, &canonical_environment,
                    "{worker_count}-worker environment diverged for order {order_id}"
                );
                assert_eq!(
                    *actual_root, expected_root,
                    "{worker_count}-worker root diverged for order {order_id}"
                );
                assert_eq!(
                    environment.logical_root(&options),
                    *actual_root,
                    "worker root was not repeatable"
                );
                for case in cases.iter().copied() {
                    let expected_info = tagged_declaration(case, true);
                    let actual_info = environment
                        .find(expected_info.name())
                        .expect("worker retains every tagged declaration");
                    assert_eq!(actual_info, &expected_info);
                    assert_eq!(
                        Environment::decl_content_digest(actual_info),
                        modeled_tagged_declaration_digest(
                            case,
                            &expected_info,
                            DeclarationTagDigestModel::Canonical,
                        ),
                        "worker declaration digest diverged for {}/{}",
                        case.family(),
                        case.variant()
                    );
                }
                worker_roots.push(*actual_root);
                let case_count = DeclarationTagCase::COUNT;
                eprintln!(
                    "{{\"schema\":\"fln.unit.declaration-tag-concurrent-build\",\
                     \"version\":1,\"bead\":\"fln-amv.12\",\
                     \"claim_type\":\"bounded_model\",\
                     \"scenario\":\"complete-environment-thread-matrix\",\
                     \"invariant_relation\":\"supports-local-environment-identity-slice\",\
                     \"gate_relation\":\"partial-component-evidence\",\
                     \"execution_model\":\"independent_complete_build_per_worker\",\
                     \"concurrent_worker_count\":{worker_count},\
                     \"worker_index\":{worker_index},\
                     \"input_order_id\":\"{order_id}\",\
                     \"raw_input_order_case_count\":{},\
                     \"raw_input_order_labels\":\"{raw_input_order_labels}\",\
                     \"declaration_cases\":{case_count},\"actual_root\":\"{actual_root}\",\
                     \"expected_root\":\"{expected_root}\",\
                     \"full_environment_equal\":true,\
                     \"per_name_digest_equal\":true,\"status\":\"pass\"}}",
                    raw_order.len()
                );
            }

            let mut sorted_order_ids: Vec<_> = order_ids.into_iter().collect();
            sorted_order_ids.sort_unstable();
            let mut order_set_writer = CanonWriter::new();
            order_set_writer.str("fln.test.declaration-tag-order-set");
            order_set_writer.u16(1);
            order_set_writer.u64(usize_to_u64(sorted_order_ids.len()));
            for order_id in sorted_order_ids {
                order_set_writer.bytes(&order_id.0);
            }
            let order_set_hash = hash(Domain::Fixture, &order_set_writer.into_bytes());

            worker_roots.sort_unstable();
            let mut root_set_writer = CanonWriter::new();
            root_set_writer.str("fln.test.declaration-tag-worker-roots");
            root_set_writer.u16(1);
            root_set_writer.u64(usize_to_u64(worker_roots.len()));
            for root in worker_roots {
                root_set_writer.bytes(&root.0.0);
            }
            let worker_roots_hash = hash(Domain::Fixture, &root_set_writer.into_bytes());
            let case_count = DeclarationTagCase::COUNT;
            eprintln!(
                "{{\"schema\":\"fln.unit.declaration-tag-concurrent-build-summary\",\
                 \"version\":1,\"bead\":\"fln-amv.12\",\
                 \"claim_type\":\"bounded_model\",\
                 \"scenario\":\"complete-environment-thread-matrix\",\
                 \"invariant_relation\":\"supports-local-environment-identity-slice\",\
                 \"gate_relation\":\"partial-component-evidence\",\
                 \"permutation_scheme\":\"affine-modulo-seven-v1\",\
                 \"concurrent_worker_count\":{worker_count},\
                 \"productive_workers\":{},\"distinct_full_permutations\":{},\
                 \"declaration_cases_per_worker\":{case_count},\
                 \"order_set_hash\":\"{order_set_hash}\",\
                 \"worker_roots_hash\":\"{worker_roots_hash}\",\
                 \"expected_root\":\"{expected_root}\",\
                 \"omitted_declaration_root\":\"{omitted_root}\",\
                 \"source_order_mutant_root\":\"{source_order_root}\",\
                 \"full_environment_equal\":true,\
                 \"per_name_digest_equal\":true,\
                 \"omission_negative_control\":\"pass\",\
                 \"source_order_negative_control\":\"pass\",\"status\":\"pass\"}}",
                results.len(),
                distinct_full_permutations
            );
        }
    }

    /// The `fln-amv.12` child matrix, as lane-consumable evidence.
    ///
    /// The unit coverage above already proves the substance; what it emits is
    /// `fln.unit.*` on stderr, which is a developer-facing summary rather than a
    /// record the shared env_snapshots lane can validate. This emits the same facts
    /// as `fln.e2e.declaration-tag-matrix/1` on stdout, one row per tag case plus a
    /// summary, so `fln-amv.14`'s authoritative bundle can carry a separately
    /// identifiable fln-amv.12 child instead of citing unit-only evidence.
    ///
    /// Every number here is produced by real work through the real API in this run.
    /// Nothing is restated from the unit test.
    #[test]
    fn declaration_tag_matrix_e2e_emits_detailed_real_path_evidence() {
        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );
        let options = KVMap::new();
        let started = std::time::Instant::now();
        let mut digests = Vec::with_capacity(DeclarationTagCase::ALL.len());

        for case in DeclarationTagCase::ALL {
            let case_started = std::time::Instant::now();
            let info = tagged_declaration(case, false);
            let canonical_bytes =
                modeled_tagged_declaration_bytes(case, &info, DeclarationTagDigestModel::Canonical);
            let expected_digest = hash(Domain::DeclContent, &canonical_bytes);
            let actual_digest = Environment::decl_content_digest(&info);
            let repeated_digest =
                Environment::decl_content_digest(&tagged_declaration(case, false));
            let stream_hash = hash(Domain::Fixture, &canonical_bytes);
            let environment = Environment::new()
                .add_decl(info.clone())
                .expect("single tagged declaration fixture builds");
            let actual_root = environment.logical_root(&options);
            let mut expected_root_builder = LogicalRootBuilder::new();
            expected_root_builder.add_decl(info.name(), expected_digest);
            expected_root_builder.set_options(&options);
            let expected_root = expected_root_builder.finalize();

            // The production tag must equal the frozen canonical tag: that identity is
            // the whole point of fln-amv.12, since `as u8` would silently track source
            // order instead.
            assert_eq!(
                case.production_tag(),
                case.canonical_tag(),
                "{}/{} production tag drifted from its frozen canonical tag",
                case.family(),
                case.variant()
            );
            assert_eq!(actual_digest, expected_digest);
            assert_eq!(actual_digest, repeated_digest);
            assert_eq!(actual_root, expected_root);
            assert_eq!(canonical_bytes.len(), case.golden_stream_bytes());
            assert_eq!(stream_hash.to_string(), case.golden_stream_hash());
            assert_eq!(actual_digest.to_string(), case.golden_digest());
            digests.push((case, actual_digest));

            println!(
                "{{\"schema\":\"fln.e2e.declaration-tag-matrix\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.12\",\"fln-amv.14\"],\
                 \"scenario\":\"declaration-tag-matrix\",\"case\":\"{}/{}\",\
                 \"family\":\"{}\",\"variant\":\"{}\",\"kind\":\"{}\",\
                 \"canonical_tag\":{},\"production_tag\":{},\
                 \"tag_source\":\"explicit_exhaustive_match\",\
                 \"stream_bytes\":{},\"golden_stream_bytes\":{},\
                 \"stream_hash\":\"{stream_hash}\",\"golden_stream_hash\":\"{}\",\
                 \"expected_digest\":\"{expected_digest}\",\"actual_digest\":\"{actual_digest}\",\
                 \"golden_digest\":\"{}\",\"repeated_digest\":\"{repeated_digest}\",\
                 \"digest_relation\":\"equal\",\"repeat_relation\":\"equal\",\
                 \"expected_root\":\"{expected_root}\",\"actual_root\":\"{actual_root}\",\
                 \"root_relation\":\"equal\",\"model\":\"independent-complete-stream-v1\",\
                 \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
                case.family(),
                case.variant(),
                case.family(),
                case.variant(),
                case.kind_name(),
                case.canonical_tag(),
                case.production_tag(),
                canonical_bytes.len(),
                case.golden_stream_bytes(),
                case.golden_stream_hash(),
                case.golden_digest(),
                case_started.elapsed().as_micros()
            );
        }

        // Pairwise distinctness, counted rather than asserted in bulk, so the record
        // states how much comparison actually happened.
        let mut pairwise_comparisons = 0usize;
        for (index, (_, lhs)) in digests.iter().enumerate() {
            for (_, rhs) in &digests[index + 1..] {
                assert_ne!(lhs, rhs, "two declaration tag cases aliased");
                pairwise_comparisons += 1;
            }
        }
        assert_eq!(pairwise_comparisons, 21);

        // The thread matrix, run for real: every worker builds the full seven-case
        // environment under its own permutation and must land on one root.
        let cases = DeclarationTagCase::ALL.to_vec();
        let canonical_environment = tagged_environment(cases.iter().copied());
        let canonical_root = canonical_environment.logical_root(&options);
        let mut thread_rows = Vec::new();
        for worker_count in [1usize, 8, 32] {
            let thread_started = std::time::Instant::now();
            let roots = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker_index| {
                        let permutation = permuted_tag_cases(&cases, worker_index);
                        scope.spawn(move || {
                            tagged_environment(permutation.iter().copied())
                                .logical_root(&KVMap::new())
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("tag matrix worker joins"))
                    .collect::<Vec<_>>()
            });
            assert_eq!(roots.len(), worker_count);
            let distinct: HashSet<_> = roots.iter().collect();
            assert_eq!(
                distinct.len(),
                1,
                "{worker_count} workers disagreed on the aggregate root"
            );
            assert_eq!(roots[0], canonical_root);
            thread_rows.push((worker_count, thread_started.elapsed().as_micros()));
            println!(
                "{{\"schema\":\"fln.e2e.declaration-tag-matrix\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.12\",\"fln-amv.14\"],\
                 \"scenario\":\"declaration-tag-thread-matrix\",\
                 \"worker_count\":{worker_count},\"distinct_root_count\":1,\
                 \"expected_root\":\"{canonical_root}\",\"actual_root\":\"{}\",\
                 \"root_relation\":\"equal\",\"order_independence\":\"proven\",\
                 \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
                roots[0],
                thread_started.elapsed().as_micros()
            );
        }

        // The named defect: one tag encoded by source-order cast instead of its frozen
        // value must move the aggregate root. Without this the matrix above would pass
        // just as happily against a cast-based encoder.
        let mut source_order_builder = LogicalRootBuilder::new();
        for (index, case) in cases.iter().copied().enumerate() {
            let info = tagged_declaration(case, true);
            let model = if index == 0 {
                DeclarationTagDigestModel::CastAfterSourceReorder
            } else {
                DeclarationTagDigestModel::Canonical
            };
            source_order_builder.add_decl(
                info.name(),
                modeled_tagged_declaration_digest(case, &info, model),
            );
        }
        source_order_builder.set_options(&options);
        let source_order_root = source_order_builder.finalize();
        assert_ne!(source_order_root, canonical_root);

        let omitted_root = tagged_environment(cases.iter().copied().skip(1)).logical_root(&options);
        assert_ne!(omitted_root, canonical_root);

        println!(
            "{{\"schema\":\"fln.e2e.declaration-tag-matrix\",\"version\":1,\
             \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.12\",\"fln-amv.14\"],\
             \"scenario\":\"declaration-tag-summary\",\"case_count\":{},\
             \"unique_digest_count\":{},\"pairwise_comparisons\":{pairwise_comparisons},\
             \"expected_pairwise_comparisons\":21,\"thread_matrix\":[1,8,32],\
             \"thread_matrix_roots_distinct\":1,\
             \"canonical_root\":\"{canonical_root}\",\
             \"source_order_defect_root\":\"{source_order_root}\",\
             \"source_order_defect_relation\":\"differs\",\
             \"omitted_declaration_root\":\"{omitted_root}\",\
             \"omitted_declaration_relation\":\"differs\",\
             \"named_defects_discriminated\":[\"cast_after_source_reorder\",\
             \"omitted_declaration\"],\"claim_type\":\"bounded_model\",\
             \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            DeclarationTagCase::ALL.len(),
            digests
                .iter()
                .map(|(_, digest)| *digest)
                .collect::<HashSet<_>>()
                .len(),
            started.elapsed().as_micros()
        );
        assert_eq!(thread_rows.len(), 3);
    }

    /// The `fln-amv.1` child matrix, as lane-consumable evidence.
    ///
    /// Companion to `declaration_tag_matrix_e2e_emits_detailed_real_path_evidence`
    /// and the same division of labour: the unit test above proves the boundaries and
    /// keeps its `fln.unit.*` summary on stderr; this emits
    /// `fln.e2e.declaration-membership/1` on stdout so `fln-amv.14`'s bundle can carry
    /// a separately identifiable fln-amv.1 child.
    ///
    /// One row per (kind, membership boundary), one defect row per kind, one summary.
    #[test]
    fn declaration_membership_matrix_e2e_emits_detailed_real_path_evidence() {
        const LARGE_MEMBER_COUNT: usize = 4_096;
        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );
        let options = KVMap::new();
        let started = std::time::Instant::now();
        let large_members: Vec<Name> = (0..LARGE_MEMBER_COUNT)
            .map(|index| Name::num(n("member"), usize_to_u64(index)))
            .collect();
        // The boundary set the bead names, in a fixed order so a validator can key on
        // it: empty, singleton, repeated, ordered, reordered, renamed, declared-large.
        let boundary_cases: Vec<(&str, Vec<Name>)> = vec![
            ("empty", Vec::new()),
            ("singleton", vec![n("d")]),
            ("repeated", vec![n("d"), n("d")]),
            ("ordered", vec![n("d"), n("e")]),
            ("reordered", vec![n("e"), n("d")]),
            ("renamed", vec![n("d"), n("f")]),
            ("declared_large", large_members),
        ];
        let mut total_rows = 0usize;

        for kind in AllBearingKind::ALL {
            let mut digests = Vec::with_capacity(boundary_cases.len());
            for (case, members) in &boundary_cases {
                let case_started = std::time::Instant::now();
                let info = all_bearing_decl(kind, members.clone());
                let actual_digest = Environment::decl_content_digest(&info);
                let expected_digest = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                let repeated_digest =
                    Environment::decl_content_digest(&all_bearing_decl(kind, members.clone()));
                assert_eq!(actual_digest, expected_digest);
                assert_eq!(actual_digest, repeated_digest);

                // Root propagation, proved rather than assumed: the environment's root
                // must equal a root built independently from this exact digest.
                let environment = Environment::new()
                    .add_decl(info.clone())
                    .expect("fixture declaration is valid");
                let actual_root = environment.logical_root(&options);
                let mut expected_root_builder = LogicalRootBuilder::new();
                expected_root_builder.add_decl(info.name(), actual_digest);
                expected_root_builder.set_options(&options);
                let expected_root = expected_root_builder.finalize();
                assert_eq!(actual_root, expected_root);
                digests.push(actual_digest);
                total_rows += 1;

                println!(
                    "{{\"schema\":\"fln.e2e.declaration-membership\",\"version\":1,\
                     \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.1\",\"fln-amv.14\"],\
                     \"scenario\":\"declaration-membership-matrix\",\"kind\":\"{}\",\
                     \"membership_case\":\"{case}\",\"member_count\":{},\
                     \"expected_digest\":\"{expected_digest}\",\
                     \"actual_digest\":\"{actual_digest}\",\
                     \"repeated_digest\":\"{repeated_digest}\",\
                     \"digest_relation\":\"equal\",\"repeat_relation\":\"equal\",\
                     \"expected_root\":\"{expected_root}\",\"actual_root\":\"{actual_root}\",\
                     \"root_relation\":\"equal\",\"root_propagation\":\"exact\",\
                     \"model\":\"independent-canonical-membership-v1\",\
                     \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
                    kind.label(),
                    members.len(),
                    case_started.elapsed().as_micros()
                );
            }

            // Every boundary distinction the bead names, counted so the record states
            // how much discrimination actually happened rather than asserting in bulk.
            let distinctions = [
                ("empty_vs_singleton", digests[0], digests[1]),
                ("singleton_vs_repeated", digests[1], digests[2]),
                ("solo_vs_grouped", digests[1], digests[3]),
                ("multiplicity_vs_identity", digests[2], digests[3]),
                ("membership_order", digests[3], digests[4]),
                ("member_names", digests[3], digests[5]),
                ("declared_large_boundary", digests[5], digests[6]),
            ];
            for (label, left, right) in distinctions {
                assert_ne!(left, right, "{} lost the {label} distinction", kind.label());
            }

            // The named defect models. Each must move the digest away from canonical;
            // a model that agreed would mean the defect is unobservable here, which is
            // precisely what fln-amv.1 was filed about for OpaqueVal.all.
            let grouped = all_bearing_decl(kind, vec![n("d"), n("e")]);
            let canonical = Environment::decl_content_digest(&grouped);
            let dropped = modeled_all_bearing_digest(
                &grouped,
                MembershipModel::DropList,
                Domain::DeclContent,
            );
            let omitted_count = modeled_all_bearing_digest(
                &grouped,
                MembershipModel::OmitCount,
                Domain::DeclContent,
            );
            let sorted = modeled_all_bearing_digest(
                &all_bearing_decl(kind, vec![n("e"), n("d")]),
                MembershipModel::SortMembers,
                Domain::DeclContent,
            );
            let wrong_domain =
                modeled_all_bearing_digest(&grouped, MembershipModel::Canonical, Domain::Fixture);
            assert_ne!(canonical, dropped, "{} dropped-list", kind.label());
            assert_ne!(canonical, omitted_count, "{} omitted-count", kind.label());
            assert_ne!(canonical, wrong_domain, "{} wrong-domain", kind.label());
            // Sorting members erases the ordered/reordered distinction. The defect is
            // the COLLAPSE, not a difference: the model maps [d,e] and [e,d] onto one
            // value while the real encoder keeps them apart. Comparing the model
            // against canonical([d,e]) finds them equal and proves nothing -- the
            // discriminating comparison is against the real encoder on the SAME
            // reordered input.
            let sorted_forward = modeled_all_bearing_digest(
                &grouped,
                MembershipModel::SortMembers,
                Domain::DeclContent,
            );
            let canonical_reordered =
                Environment::decl_content_digest(&all_bearing_decl(kind, vec![n("e"), n("d")]));
            assert_eq!(
                sorted,
                sorted_forward,
                "{} sort-members model must collapse the two orders",
                kind.label()
            );
            assert_ne!(
                sorted,
                canonical_reordered,
                "{} order-erasing model must differ from the real encoder on [e,d]",
                kind.label()
            );
            assert_ne!(
                canonical,
                canonical_reordered,
                "{} real encoder must keep the two orders distinct",
                kind.label()
            );

            // Failed root propagation: a root built from the dropped-list digest must
            // differ from the real one, so a stale digest cannot reach the same root.
            let mut stale_root_builder = LogicalRootBuilder::new();
            stale_root_builder.add_decl(grouped.name(), dropped);
            stale_root_builder.set_options(&options);
            let stale_root = stale_root_builder.finalize();
            let real_root = Environment::new()
                .add_decl(grouped.clone())
                .expect("grouped fixture is valid")
                .logical_root(&options);
            assert_ne!(stale_root, real_root, "{} root propagation", kind.label());
            total_rows += 1;

            println!(
                "{{\"schema\":\"fln.e2e.declaration-membership\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.1\",\"fln-amv.14\"],\
                 \"scenario\":\"declaration-membership-defects\",\"kind\":\"{}\",\
                 \"canonical_digest\":\"{canonical}\",\
                 \"dropped_list_digest\":\"{dropped}\",\"dropped_list_relation\":\"differs\",\
                 \"omitted_count_digest\":\"{omitted_count}\",\
                 \"omitted_count_relation\":\"differs\",\
                 \"sorted_members_digest\":\"{sorted}\",\"sorted_members_relation\":\"differs\",\
                 \"sorted_members_order_collapse\":true,\
                 \"wrong_domain_digest\":\"{wrong_domain}\",\"wrong_domain_relation\":\"differs\",\
                 \"real_root\":\"{real_root}\",\"stale_digest_root\":\"{stale_root}\",\
                 \"root_propagation_relation\":\"differs\",\
                 \"named_defects_discriminated\":[\"dropped_list\",\"omitted_count\",\
                 \"reordered_membership\",\"wrong_domain\",\"failed_root_propagation\"],\
                 \"boundary_distinctions\":{},\"status\":\"pass\",\"final_state\":\"verified\"}}",
                kind.label(),
                distinctions.len()
            );
        }

        // The original regression this bead was filed for, kept explicit: two opaque
        // declarations differing only in mutual-block membership must not alias.
        let opaque_solo = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d")],
        ));
        let opaque_grouped = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d"), n("e")],
        ));
        assert_ne!(opaque_solo, opaque_grouped);

        println!(
            "{{\"schema\":\"fln.e2e.declaration-membership\",\"version\":1,\
             \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.1\",\"fln-amv.14\"],\
             \"scenario\":\"declaration-membership-summary\",\"kind_count\":{},\
             \"membership_case_count\":{},\"matrix_rows\":{},\
             \"large_member_count\":{LARGE_MEMBER_COUNT},\
             \"opaque_solo_digest\":\"{opaque_solo}\",\
             \"opaque_grouped_digest\":\"{opaque_grouped}\",\
             \"opaque_regression_relation\":\"differs\",\
             \"root_propagation\":\"exact\",\"claim_type\":\"bounded_model\",\
             \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            AllBearingKind::ALL.len(),
            boundary_cases.len(),
            total_rows,
            started.elapsed().as_micros()
        );
        assert_eq!(
            total_rows,
            AllBearingKind::ALL.len() * (boundary_cases.len() + 1)
        );
    }

    #[test]
    fn mutual_block_membership_changes_the_content_digest() {
        const LARGE_MEMBER_COUNT: usize = 4_096;
        let large_members: Vec<Name> = (0..LARGE_MEMBER_COUNT)
            .map(|index| Name::num(n("member"), usize_to_u64(index)))
            .collect();
        let boundary_cases = vec![
            ("empty", Vec::new()),
            ("singleton", vec![n("d")]),
            ("repeated", vec![n("d"), n("d")]),
            ("ordered", vec![n("d"), n("e")]),
            ("reordered", vec![n("e"), n("d")]),
            ("renamed", vec![n("d"), n("f")]),
            ("declared_large", large_members),
        ];
        let options = KVMap::new();

        for kind in AllBearingKind::ALL {
            let mut digests = Vec::with_capacity(boundary_cases.len());
            for (case, members) in &boundary_cases {
                let info = all_bearing_decl(kind, members.clone());
                let actual = Environment::decl_content_digest(&info);
                let expected = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                assert_eq!(
                    actual,
                    expected,
                    "{} {case} membership diverged from the independent canonical model",
                    kind.label()
                );

                let rebuilt = all_bearing_decl(kind, members.clone());
                assert_eq!(
                    actual,
                    Environment::decl_content_digest(&rebuilt),
                    "{} {case} membership was not repeatable",
                    kind.label()
                );

                let environment = Environment::new()
                    .add_decl(info)
                    .expect("fixture declaration is valid");
                let actual_root = environment.logical_root(&options);
                let mut expected_root = LogicalRootBuilder::new();
                expected_root.add_decl(rebuilt.name(), actual);
                expected_root.set_options(&options);
                assert_eq!(
                    actual_root,
                    expected_root.finalize(),
                    "{} {case} digest did not propagate exactly into the logical root",
                    kind.label()
                );
                let repeated_root = Environment::new()
                    .add_decl(rebuilt)
                    .expect("repeated fixture declaration is valid")
                    .logical_root(&options);
                assert_eq!(
                    actual_root,
                    repeated_root,
                    "{} {case} logical root was not repeatable",
                    kind.label()
                );
                digests.push(actual);
            }

            assert_ne!(
                digests[0],
                digests[1],
                "{} must distinguish empty and singleton membership",
                kind.label()
            );
            assert_ne!(
                digests[1],
                digests[2],
                "{} must preserve repeated membership",
                kind.label()
            );
            assert_ne!(
                digests[1],
                digests[3],
                "{} must distinguish solo and grouped membership",
                kind.label()
            );
            assert_ne!(
                digests[2],
                digests[3],
                "{} must distinguish multiplicity and member identity",
                kind.label()
            );
            assert_ne!(
                digests[3],
                digests[4],
                "{} must preserve membership order",
                kind.label()
            );
            assert_ne!(
                digests[3],
                digests[5],
                "{} must preserve member names",
                kind.label()
            );
            assert_ne!(
                digests[5],
                digests[6],
                "{} must cover the declared large-member boundary",
                kind.label()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-boundaries\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"kind\":\"{}\",\"case_count\":7,\"large_member_count\":4096,\
                 \"empty_digest\":\"{}\",\"solo_digest\":\"{}\",\
                 \"grouped_digest\":\"{}\",\"reordered_digest\":\"{}\",\
                 \"large_digest\":\"{}\",\"root_propagation\":\"exact\",\
                 \"repeatability\":\"pass\",\"status\":\"pass\"}}",
                kind.label(),
                digests[0],
                digests[1],
                digests[3],
                digests[4],
                digests[6]
            );
        }

        let opaque_solo = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d")],
        ));
        let opaque_grouped = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d"), n("e")],
        ));
        assert_ne!(
            opaque_solo, opaque_grouped,
            "OpaqueVal.all must distinguish the original solo-versus-grouped regression"
        );
    }

    #[test]
    fn mutual_block_membership_named_mutants_are_discriminated() {
        let witness = vec![n("e"), n("d"), n("e"), n("f")];
        let options = KVMap::new();

        for kind in AllBearingKind::ALL {
            let info = all_bearing_decl(kind, witness.clone());
            let canonical = Environment::decl_content_digest(&info);
            for (mutation, model) in [
                ("drop_membership", MembershipModel::DropList),
                ("omit_member_count", MembershipModel::OmitCount),
                ("reorder_membership", MembershipModel::SortMembers),
            ] {
                let mutated = modeled_all_bearing_digest(&info, model, Domain::DeclContent);
                assert_ne!(
                    canonical,
                    mutated,
                    "{mutation} mutant survived for {}",
                    kind.label()
                );
            }

            let wrong_domain =
                modeled_all_bearing_digest(&info, MembershipModel::Canonical, Domain::LogicalRoot);
            assert_ne!(
                canonical,
                wrong_domain,
                "wrong_digest_domain mutant survived for {}",
                kind.label()
            );

            let actual_root = Environment::new()
                .add_decl(info.clone())
                .expect("fixture declaration is valid")
                .logical_root(&options);
            let dropped_digest =
                modeled_all_bearing_digest(&info, MembershipModel::DropList, Domain::DeclContent);
            let mut dropped_root = LogicalRootBuilder::new();
            dropped_root.add_decl(info.name(), dropped_digest);
            dropped_root.set_options(&options);
            assert_ne!(
                actual_root,
                dropped_root.finalize(),
                "fail_to_propagate_membership mutant survived for {}",
                kind.label()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-mutants\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"kind\":\"{}\",\"witness_member_count\":4,\
                 \"canonical_digest\":\"{canonical}\",\"logical_root\":\"{actual_root}\",\
                 \"mutations\":[\"drop_membership\",\"omit_member_count\",\
                 \"reorder_membership\",\"wrong_digest_domain\",\
                 \"fail_to_propagate_membership\"],\"killed\":5,\
                 \"status\":\"pass\"}}",
                kind.label()
            );
        }
    }

    #[test]
    fn mutual_block_membership_matches_model_for_generated_cases() {
        const GENERATED_CASES: usize = 96;
        const MAX_GENERATED_MEMBERS: usize = 48;
        let mut assertions = 0usize;

        for case_index in 0..GENERATED_CASES {
            let member_count = (case_index * 17) % (MAX_GENERATED_MEMBERS + 1);
            let mut members: Vec<Name> = (0..member_count)
                .map(|member_index| {
                    let root = if (case_index + member_index) % 2 == 0 {
                        n("left")
                    } else {
                        n("right")
                    };
                    let numbered = Name::num(
                        root,
                        usize_to_u64((case_index * 13 + member_index * 7) % 11),
                    );
                    if (case_index + member_index) % 3 == 0 {
                        Name::str(numbered, "leaf")
                    } else {
                        numbered
                    }
                })
                .collect();

            if members.len() > 1 && case_index % 3 == 0 {
                let repeated = members[0].clone();
                let last = members.len() - 1;
                members[last] = repeated;
            }
            if !members.is_empty() {
                match case_index % 4 {
                    1 => members.reverse(),
                    2 => {
                        let shift = case_index % members.len();
                        members.rotate_left(shift);
                    }
                    3 => {
                        let shift = (case_index * 3) % members.len();
                        members.rotate_right(shift);
                    }
                    _ => {}
                }
            }

            for kind in AllBearingKind::ALL {
                let info = all_bearing_decl(kind, members.clone());
                let actual = Environment::decl_content_digest(&info);
                let expected = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                assert_eq!(
                    actual,
                    expected,
                    "generated case {case_index} diverged for {}",
                    kind.label()
                );
                assert_eq!(
                    actual,
                    Environment::decl_content_digest(&all_bearing_decl(kind, members.clone())),
                    "generated case {case_index} was not repeatable for {}",
                    kind.label()
                );
                assertions += 2;
            }
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.mutual-membership-generated\",\"version\":1,\
             \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
             \"generated_cases\":{GENERATED_CASES},\"variant_count\":5,\
             \"max_member_count\":{MAX_GENERATED_MEMBERS},\
             \"assertions\":{assertions},\"name_depth_max\":3,\
             \"features\":[\"duplicates\",\"string_components\",\"numeric_components\",\
             \"reversal\",\"rotation\"],\"status\":\"pass\"}}"
        );
    }

    #[test]
    fn mutual_membership_writer_has_canonical_stream_shape() {
        for member_count in [0usize, 1, 32, 4_096] {
            let members: Vec<Name> = (0..member_count)
                .map(|index| Name::num(n("member"), usize_to_u64(index)))
                .collect();
            let canonical_member_bytes = canonical_name_body_bytes(&members);

            let mut actual = CanonWriter::new();
            write_mutual_membership(&mut actual, &members);
            let actual = actual.into_bytes();

            let mut expected = CanonWriter::new();
            write_membership_model(&mut expected, &members, MembershipModel::Canonical);
            let expected = expected.into_bytes();

            assert_eq!(
                actual, expected,
                "membership writer must be exactly count plus one ordered body per member"
            );
            assert_eq!(
                actual.len(),
                8 + canonical_member_bytes,
                "membership stream work must grow with count-prefix plus canonical member bytes"
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-work\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"evidence\":\"canonical_stream_shape\",\
                 \"member_count\":{member_count},\
                 \"canonical_member_bytes\":{canonical_member_bytes},\
                 \"expected_stream_bytes\":{},\"observed_stream_bytes\":{},\
                 \"status\":\"pass\"}}",
                8 + canonical_member_bytes,
                actual.len()
            );
        }
    }

    #[test]
    fn logical_root_is_schedule_independent_across_threads() {
        let names: Vec<String> = (0..64).map(|i| format!("decl{i}")).collect();
        let sequential = {
            let mut env = Environment::new();
            for name in &names {
                env = env.add_decl(axiom(name)).expect("adds");
            }
            env.logical_root(&KVMap::new())
        };
        for threads in [2usize, 8] {
            let chunks: Vec<Vec<String>> = names
                .chunks(names.len().div_ceil(threads))
                .map(<[String]>::to_vec)
                .collect();
            let root = std::thread::scope(|scope| {
                let handles: Vec<_> = chunks
                    .iter()
                    .map(|chunk| scope.spawn(move || chunk.clone()))
                    .collect();
                let mut env = Environment::new();
                for handle in handles {
                    for name in handle.join().expect("worker") {
                        env = env.add_decl(axiom(&name)).expect("adds");
                    }
                }
                env.logical_root(&KVMap::new())
            });
            assert_eq!(root, sequential, "{threads}-thread interleaving diverged");
        }
    }

    /// The boundary an attacker actually reaches (bead `fln-amv.13`). The budget
    /// machinery living in `pmap` proves nothing if no admission path calls it, so
    /// this pins the wiring and the FL-INV-07 typing at `Environment`.
    ///
    /// A zero-entry budget is used to drive the refusal: real `Name` keys do not
    /// collide on demand — engineering one would be a hash collision — so the
    /// adversarial *family* is modelled in `pmap::tests` with keys that genuinely
    /// share a hash, while the boundary test drives the same refusal through the
    /// budget's zero case. Both exercise the identical production path.
    #[test]
    fn budgeted_admission_is_inconclusive_not_a_rejection_and_leaves_the_environment_intact() {
        let base = Environment::new()
            .add_decl(axiom("Held"))
            .expect("the baseline declaration admits");
        let before_root = base.logical_root(&KVMap::new());

        // Zero entries: no insertion can fit, so the envelope binds immediately.
        let zero = CollisionBudget {
            max_collision_entries: 0,
            ..CollisionBudget::UNBOUNDED
        };
        let outcome = base.try_add_decl_with_budget(axiom("Fresh"), 1, zero);

        assert!(
            outcome.is_inconclusive(),
            "expected inconclusive: {outcome:?}"
        );
        assert_eq!(outcome.outcome_label(), "inconclusive-collision-budget");
        // FL-INV-07: never acceptance, never rejection, never cacheable.
        assert!(!outcome.is_cacheable());
        assert_eq!(outcome.environment(), None);
        assert!(
            !matches!(outcome, DeclAdmission::Rejected(_)),
            "resource exhaustion must never be reported as a rejection"
        );
        let DeclAdmission::Inconclusive(exhausted) = &outcome else {
            unreachable!("asserted inconclusive above")
        };
        // The refusal's finer facts moved from typed fields onto the shared outcome when
        // the PMap stop folded onto the FL-INV-07 taxonomy: the numbers are in
        // `ResourceUsage`, and which collision resource tripped is in `progress`.
        let fln_core::outcome::InconclusiveCause::ResourceExhausted { usage } = &exhausted.cause
        else {
            unreachable!("a collision-budget stop is resource exhaustion")
        };
        assert_eq!(usage.allowed, 0);
        assert!(
            exhausted
                .progress
                .as_ref()
                .is_some_and(|p| p.text().contains("collision_entries")),
            "the refused resource must remain identifiable: {:?}",
            exhausted.progress
        );

        // Atomic: the receiver is untouched, down to its logical root.
        assert!(!base.contains(&n("Fresh")));
        assert!(base.contains(&n("Held")));
        assert_eq!(base.logical_root(&KVMap::new()), before_root);

        // Recovery proves the refusal was about the envelope, not the declaration:
        // the very same declaration admits once the budget allows it.
        let admitted = base.try_add_decl_with_budget(axiom("Fresh"), 1, CollisionBudget::UNBOUNDED);
        assert_eq!(admitted.outcome_label(), "admitted");
        assert!(admitted.is_cacheable());
        let grown = admitted
            .environment()
            .expect("an admitted outcome carries the environment");
        assert!(grown.contains(&n("Fresh")));
        assert_ne!(grown.logical_root(&KVMap::new()), before_root);

        // A duplicate is a *rejection* — a complete determination that costs one
        // bounded lookup — and stays a rejection under a budget that would otherwise
        // bind. Exhaustion must not be able to mask or masquerade as the kernel's
        // one-name-one-constant law, in either direction.
        for budget in [CollisionBudget::UNBOUNDED, zero] {
            let duplicate = base.try_add_decl_with_budget(axiom("Held"), 1, budget);
            assert_eq!(duplicate.outcome_label(), "rejected");
            assert!(!duplicate.is_inconclusive());
            assert!(!duplicate.is_cacheable());
            assert_eq!(duplicate.environment(), None);
            assert!(matches!(
                duplicate,
                DeclAdmission::Rejected(EnvError::DuplicateDeclaration { .. })
            ));
        }

        // The unbudgeted semantic operation is unchanged: it never refuses for
        // resource reasons, which is why the budgeted path had to be a sibling
        // rather than a replacement.
        assert!(base.add_decl(axiom("Fresh")).is_ok());
    }

    fn constructor_decl() -> ConstantInfo {
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: n("d"),
                level_params: vec![n("u")],
                type_: Expr::sort(Level::param(n("u"))),
            },
            induct: n("Parent"),
            cidx: 0,
            num_params: 2,
            num_fields: 3,
            is_unsafe: false,
        })
    }

    /// The resource facts and bound dimension of a preflight stop, or `None` if the
    /// outcome was not a resource stop at all. Returning an `Option` rather than
    /// destructuring at each site keeps one extraction path and lets callers use the
    /// crate's usual `expect`, instead of three hand-written panics that would each
    /// have to agree about what a stop looks like.
    /// Fold a checkpoint outcome to the `Result` these fixtures expect.
    ///
    /// Every fixture passes no cancellation probe, so a non-answer here is a test bug
    /// rather than a scenario — surfaced as one instead of silently becoming an `Err`,
    /// which is exactly the collapse the widened signature exists to prevent.
    fn completed<T: std::fmt::Debug, E: std::fmt::Debug>(
        outcome: Outcome<Result<T, E>>,
    ) -> Result<T, E> {
        assert!(
            matches!(outcome, Outcome::Complete(_)),
            "fixtures pass no probe, so a non-answer is a test bug: {outcome:?}"
        );
        match outcome {
            Outcome::Complete(result) => result,
            _ => unreachable!("asserted just above"),
        }
    }

    fn resource_stop(
        outcome: &Outcome<DeclarationUsage>,
    ) -> Option<(&ResourceUsage, Option<&str>)> {
        let Outcome::Inconclusive(inconclusive) = outcome else {
            return None;
        };
        let InconclusiveCause::ResourceExhausted { usage } = &inconclusive.cause else {
            return None;
        };
        Some((
            usage,
            inconclusive
                .progress
                .as_ref()
                .map(|progress| progress.text()),
        ))
    }

    fn row_usage(info: &ConstantInfo) -> DeclarationUsage {
        preflight_declaration_rows(info, DeclarationBudget::UNBOUNDED)
            .into_complete()
            .expect("an unbounded budget cannot refuse")
    }

    /// Exact row facts for every `ConstantInfo` variant, including the three that
    /// carry no mutual block. Zero is a reported fact here, not an absent one: a
    /// dimension that silently had no value would be a dimension a caller cannot
    /// budget.
    #[test]
    fn declaration_row_usage_is_exact_for_every_variant() {
        let members = vec![n("d"), n("peer"), n("third")];
        for kind in AllBearingKind::ALL {
            let info = all_bearing_decl(kind, members.clone());
            let usage = row_usage(&info);
            assert_eq!(usage.level_params, 1, "{}", kind.label());
            assert_eq!(usage.mutual_rows, 3, "{}", kind.label());
            assert_eq!(
                usage.constructor_rows,
                u64::from(matches!(kind, AllBearingKind::Inductive)) * 2,
                "only an inductive carries constructor rows ({})",
                kind.label()
            );
            assert_eq!(
                usage.recursor_rules,
                u64::from(matches!(kind, AllBearingKind::Recursor)) * 2,
                "only a recursor carries rule rows ({})",
                kind.label()
            );
        }

        // The three variants with no mutual block report zero rather than being
        // exempt from accounting.
        let axiom_usage = row_usage(&axiom("A"));
        assert_eq!(axiom_usage.mutual_rows, 0);
        assert_eq!(axiom_usage.level_params, 0);
        let quot_usage = row_usage(&tagged_declaration(
            DeclarationTagCase::Quotient(QuotKind::Lift),
            false,
        ));
        assert_eq!(quot_usage.mutual_rows, 0);
        assert_eq!(quot_usage.level_params, 2);
        let ctor_usage = row_usage(&constructor_decl());
        assert_eq!(ctor_usage.mutual_rows, 0);
        assert_eq!(ctor_usage.constructor_rows, 0);
        assert_eq!(ctor_usage.recursor_rules, 0);
    }

    /// The counted rows are the rows the encoder writes.
    ///
    /// Both directions, because a count that merely *looks* right is how a usage fact
    /// drifts from the work it claims to describe: the counted membership must equal
    /// the list the encoder is handed, and adding one row must move the content
    /// digest — proving the rows counted are content-bearing rather than incidental.
    #[test]
    fn declaration_row_usage_counts_exactly_what_the_encoder_writes() {
        for kind in AllBearingKind::ALL {
            for rows in 0..4usize {
                let members: Vec<Name> = (0..rows).map(|i| n(&format!("m{i}"))).collect();
                let info = all_bearing_decl(kind, members.clone());
                assert_eq!(
                    row_usage(&info).mutual_rows,
                    usize_to_u64(declaration_mutual_members(&info).len()),
                    "counted membership diverged from the encoder's list ({})",
                    kind.label()
                );
                assert_eq!(row_usage(&info).mutual_rows, usize_to_u64(rows));

                let mut grown = members;
                grown.push(n("extra"));
                assert_ne!(
                    Environment::decl_content_digest(&info),
                    Environment::decl_content_digest(&all_bearing_decl(kind, grown)),
                    "a counted row did not reach the content digest ({})",
                    kind.label()
                );
            }
        }
    }

    /// The canonical-byte fact is the length of the bytes the DIGEST is over.
    ///
    /// One encoder, so the fact and the identity cannot describe different streams. This
    /// asserts that directly against every all-bearing variant rather than trusting the
    /// refactor — a byte count taken from a second implementation would be a fact about
    /// the wrong bytes, which is the failure mode the shared encoder exists to remove.
    #[test]
    fn the_canonical_byte_fact_measures_the_stream_the_digest_is_taken_over() {
        for kind in AllBearingKind::ALL {
            let info = all_bearing_decl(kind, vec![n("a"), n("b")]);
            let bytes = Environment::decl_content_bytes(&info);
            assert_eq!(
                row_usage(&info).canonical_bytes,
                usize_to_u64(bytes.len()),
                "the reported byte count must be the encoder's own length ({})",
                kind.label()
            );
            // And those bytes are the digest's preimage, not a parallel encoding.
            assert_eq!(
                hash(Domain::DeclContent, &bytes),
                Environment::decl_content_digest(&info),
                "the measured bytes must be the digest's preimage ({})",
                kind.label()
            );
        }

        // A larger declaration reports more bytes: the fact tracks the input rather than
        // being a constant that happens to match.
        let small = all_bearing_decl(AllBearingKind::Definition, vec![n("a")]);
        let large = all_bearing_decl(
            AllBearingKind::Definition,
            (0..16).map(|i| n(&format!("m{i}"))).collect(),
        );
        assert!(
            row_usage(&large).canonical_bytes > row_usage(&small).canonical_bytes,
            "more membership rows must encode to more bytes"
        );

        // The unit a byte refusal reports, pinned so the decision is visible in a test and
        // not only in a doc comment.
        assert_eq!(
            DeclarationDimension::CanonicalBytes.unit(),
            StructuralUnit::InputBytes
        );
        for dimension in [
            DeclarationDimension::LevelParams,
            DeclarationDimension::MutualRows,
            DeclarationDimension::ConstructorRows,
            DeclarationDimension::RecursorRules,
        ] {
            assert_eq!(
                dimension.unit(),
                StructuralUnit::ProducedNodes,
                "the row families stay on ProducedNodes ({})",
                dimension.as_str()
            );
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-canonical-bytes\",\"version\":1,\
             \"bead\":\"franken_lean-j8h\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"canonical-bytes-exact-not-modelled\",\
             \"measurement\":\"length_of_the_digest_preimage\",\
             \"modelled\":false,\"shared_encoder\":true,\
             \"unit\":\"input_bytes\",\"new_structural_unit_added\":false,\
             \"decision\":\"no_fourth_d8_unit\",\
             \"decision_reason\":\"a caller reacts to a byte bound the same way it reacts \
             to a row bound, so the taxonomy's bar for a new unit is not met\",\
             \"finer_fact_home\":\"declaration_dimension_on_the_report\",\
             \"order_position\":\"last\",\"status\":\"pass\"}}"
        );
    }

    /// Exact admits, one-over refuses, per dimension.
    #[test]
    fn declaration_row_preflight_admits_at_exact_and_refuses_one_over() {
        let members = vec![n("d"), n("peer"), n("third")];
        // The canonical-bytes case takes its exact value from the encoder itself rather
        // than a literal, because a hardcoded byte count would pin the encoding here as
        // well as in the goldens and the two would drift apart independently.
        let bytes_fixture = all_bearing_decl(AllBearingKind::Theorem, members.clone());
        let exact_bytes = row_usage(&bytes_fixture).canonical_bytes;
        assert!(exact_bytes > 0, "the fixture must encode to something");
        let cases: [(DeclarationDimension, ConstantInfo, u64); 4] = [
            (
                DeclarationDimension::CanonicalBytes,
                bytes_fixture,
                exact_bytes,
            ),
            (
                DeclarationDimension::MutualRows,
                all_bearing_decl(AllBearingKind::Definition, members.clone()),
                3,
            ),
            (
                DeclarationDimension::ConstructorRows,
                all_bearing_decl(AllBearingKind::Inductive, members.clone()),
                2,
            ),
            (
                DeclarationDimension::RecursorRules,
                all_bearing_decl(AllBearingKind::Recursor, members.clone()),
                2,
            ),
        ];
        for (dimension, info, exact) in cases {
            let at_exact = match dimension {
                DeclarationDimension::MutualRows => DeclarationBudget {
                    max_mutual_rows: exact,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::ConstructorRows => DeclarationBudget {
                    max_constructor_rows: exact,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::RecursorRules => DeclarationBudget {
                    max_recursor_rules: exact,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::CanonicalBytes => DeclarationBudget {
                    max_canonical_bytes: exact,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::LevelParams => unreachable!(),
            };
            assert!(
                matches!(
                    preflight_declaration_rows(&info, at_exact),
                    Outcome::Complete(_)
                ),
                "an exact budget must admit ({})",
                dimension.as_str()
            );

            let one_under = match dimension {
                DeclarationDimension::MutualRows => DeclarationBudget {
                    max_mutual_rows: exact - 1,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::ConstructorRows => DeclarationBudget {
                    max_constructor_rows: exact - 1,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::RecursorRules => DeclarationBudget {
                    max_recursor_rules: exact - 1,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::CanonicalBytes => DeclarationBudget {
                    max_canonical_bytes: exact - 1,
                    ..DeclarationBudget::UNBOUNDED
                },
                DeclarationDimension::LevelParams => unreachable!(),
            };
            let refused = preflight_declaration_rows(&info, one_under);
            assert!(
                resource_stop(&refused).is_some(),
                "one over budget must refuse with a resource stop ({})",
                dimension.as_str()
            );
            let (usage, progress) = resource_stop(&refused).expect("asserted just above");
            assert_eq!(usage.allowed, exact - 1);
            assert!(
                usage.observed > usage.allowed,
                "a stop that did not report spending past its allowance is not a stop"
            );
            assert!(usage.is_genuine_exhaustion());
            // The reported unit is the DIMENSION's unit, so a byte refusal says
            // InputBytes and a row refusal says ProducedNodes. Asserting the dimension's
            // own answer rather than a constant is what makes this catch a hardcoded unit.
            assert_eq!(
                usage.reason,
                ResourceReason::StructuralBudget {
                    unit: dimension.unit()
                }
            );
            assert_eq!(
                progress,
                Some(dimension.as_str()),
                "a stop must name the dimension it bound"
            );
        }
    }

    /// A refusal is inconclusive, never a rejection, and is not cacheable.
    #[test]
    fn declaration_row_preflight_refusal_is_inconclusive_and_uncacheable() {
        let info = all_bearing_decl(AllBearingKind::Definition, vec![n("a"), n("b")]);
        let refused = preflight_declaration_rows(
            &info,
            DeclarationBudget {
                max_mutual_rows: 0,
                ..DeclarationBudget::UNBOUNDED
            },
        );
        assert_eq!(refused.authority(), Authority::NonAuthoritative);
        assert_eq!(
            refused.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );
        // The domain result is unreachable without handling the non-answer: there is
        // no partial-usage field to read while skipping the authority check.
        assert!(refused.into_complete().is_err());

        // And the declaration itself was not judged: the same declaration under an
        // adequate budget is admitted with the same facts, so the refusal said
        // nothing about admissibility.
        let retried = preflight_declaration_rows(&info, DeclarationBudget::UNBOUNDED);
        assert_eq!(
            retried.into_complete().expect("adequate budget admits"),
            row_usage(&info)
        );
    }

    /// Simultaneous breaches report the frozen primary dimension.
    #[test]
    fn declaration_row_preflight_primary_dimension_is_frozen_under_simultaneous_breach() {
        // A recursor breaching membership AND rules at once: `ORDER` puts membership
        // first, so that is the reported reason while the rule overage is equally real.
        let info = all_bearing_decl(AllBearingKind::Recursor, vec![n("a"), n("b"), n("c")]);
        let refused = preflight_declaration_rows(
            &info,
            DeclarationBudget {
                max_mutual_rows: 1,
                max_recursor_rules: 1,
                ..DeclarationBudget::UNBOUNDED
            },
        );
        assert!(
            resource_stop(&refused).is_some(),
            "a double breach must refuse"
        );
        let (_, progress) = resource_stop(&refused).expect("asserted just above");
        assert_eq!(
            progress,
            Some(DeclarationDimension::MutualRows.as_str()),
            "the frozen order must select the primary reason"
        );
        assert_eq!(
            DeclarationDimension::ORDER,
            [
                DeclarationDimension::LevelParams,
                DeclarationDimension::MutualRows,
                DeclarationDimension::ConstructorRows,
                DeclarationDimension::RecursorRules,
                DeclarationDimension::CanonicalBytes,
            ],
            "the reported-reason order is frozen; changing it changes which reason \
             callers see for the same declaration"
        );

        // Schedule independence: the scan is a fixed sequence over an immutable
        // value, so repeating it cannot select a different primary dimension.
        for _ in 0..8 {
            let again = preflight_declaration_rows(
                &info,
                DeclarationBudget {
                    max_mutual_rows: 1,
                    max_recursor_rules: 1,
                    ..DeclarationBudget::UNBOUNDED
                },
            );
            assert_eq!(again, refused);
        }
    }

    /// A probe that trips at a chosen sample rather than always the first, so a test
    /// can pin the exact checkpoint instead of only proving that cancellation happens.
    struct TripAt {
        trip_on: std::cell::Cell<u32>,
    }

    impl TripAt {
        fn new(sample: u32) -> TripAt {
            TripAt {
                trip_on: std::cell::Cell::new(sample),
            }
        }
    }

    impl CancellationProbe for TripAt {
        fn is_cancelled(&self) -> bool {
            let remaining = self.trip_on.get();
            if remaining == 0 {
                return true;
            }
            self.trip_on.set(remaining - 1);
            false
        }
    }

    /// Expression facts are exact, and the expression set is the frozen one.
    #[test]
    fn declaration_expression_usage_is_exact_and_covers_every_carried_expression() {
        // Signature type only.
        let axiom_usage = preflight_declaration(&axiom("A"), DeclarationBudget::UNBOUNDED, None)
            .into_complete()
            .expect("unbounded admits");
        assert_eq!(axiom_usage.expressions, 1);
        assert!(axiom_usage.expr_nodes >= 1);

        // Signature plus a body.
        let defn = all_bearing_decl(AllBearingKind::Definition, vec![n("a")]);
        let defn_usage = preflight_declaration(&defn, DeclarationBudget::UNBOUNDED, None)
            .into_complete()
            .expect("unbounded admits");
        assert_eq!(defn_usage.expressions, 2);

        // Signature plus one right-hand side per recursor rule: the fixture has two.
        let rec = all_bearing_decl(AllBearingKind::Recursor, vec![n("a")]);
        let rec_usage = preflight_declaration(&rec, DeclarationBudget::UNBOUNDED, None)
            .into_complete()
            .expect("unbounded admits");
        assert_eq!(rec_usage.expressions, 3);
        assert_eq!(
            rec_usage.expressions,
            usize_to_u64(declaration_expressions(&rec).len()),
            "the measured expression count must equal the frozen expression set"
        );

        // Repeatable: the same declaration measured twice reports identical facts, so
        // the facts are a property of the value rather than of the run.
        assert_eq!(
            rec_usage,
            preflight_declaration(&rec, DeclarationBudget::UNBOUNDED, None)
                .into_complete()
                .expect("unbounded admits")
        );
    }

    /// A recursor whose signature and every rule right-hand side is genuinely
    /// multi-node. The shared `all_bearing_decl` fixture uses single-node bodies, which
    /// cannot distinguish a shared budget from a per-expression one — with one node per
    /// expression the two agree.
    fn multi_node_recursor() -> ConstantInfo {
        let multi = |head: &str| {
            Expr::app(
                Expr::const_(n(head), vec![Level::param(n("u"))]),
                Expr::sort(Level::param(n("u"))),
            )
        };
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: n("d"),
                level_params: vec![n("u")],
                type_: multi("carrier"),
            },
            all: vec![n("d")],
            num_params: 2,
            num_indices: 1,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule {
                    ctor: n("mk"),
                    nfields: 3,
                    rhs: multi("body"),
                },
                RecursorRule {
                    ctor: n("mkAlt"),
                    nfields: 4,
                    rhs: multi("bodyAlt"),
                },
            ],
            k: true,
            is_unsafe: true,
        })
    }

    /// The node budget is shared across the declaration, not granted per expression.
    #[test]
    fn declaration_expression_budget_is_shared_across_expressions() {
        let rec = multi_node_recursor();
        let total = preflight_declaration(&rec, DeclarationBudget::UNBOUNDED, None)
            .into_complete()
            .expect("unbounded admits");
        assert!(
            total.expressions > 1 && total.expr_nodes > total.expressions,
            "the fixture must carry several multi-node expressions for this to mean anything"
        );

        // Exactly enough for the whole declaration admits.
        assert!(
            matches!(
                preflight_declaration(
                    &rec,
                    DeclarationBudget {
                        max_expr_nodes: total.expr_nodes,
                        ..DeclarationBudget::UNBOUNDED
                    },
                    None,
                ),
                Outcome::Complete(_)
            ),
            "a budget equal to the exact total must admit"
        );

        // One short refuses, and it refuses as a non-answer rather than a rejection.
        let refused = preflight_declaration(
            &rec,
            DeclarationBudget {
                max_expr_nodes: total.expr_nodes - 1,
                ..DeclarationBudget::UNBOUNDED
            },
            None,
        );
        assert_eq!(refused.authority(), Authority::NonAuthoritative);
        assert_eq!(
            refused.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );
        let (usage, _) = resource_stop(&refused).expect("one short must be a resource stop");
        assert!(usage.is_genuine_exhaustion());

        // The shared-budget claim, stated as the thing a per-expression limit would
        // get wrong: the largest single expression fits well inside the total, so a
        // per-expression cap of that size would have admitted a declaration whose
        // aggregate exceeds it.
        let largest = declaration_expressions(&rec)
            .into_iter()
            .map(|expr| {
                crate::terms::expanded_weight(expr, &WeightBudget::new(u64::MAX, u64::MAX))
                    .into_complete()
                    .expect("unbounded admits")
                    .distinct_nodes
            })
            .max()
            .expect("the fixture carries expressions");
        assert!(
            largest < total.expr_nodes,
            "a per-expression budget would not have bound this declaration"
        );
    }

    /// Cancellation is a distinct non-answer at a frozen, numbered checkpoint.
    #[test]
    fn declaration_preflight_cancellation_is_typed_at_a_frozen_checkpoint() {
        let rec = all_bearing_decl(AllBearingKind::Recursor, vec![n("a")]);
        for sample in 0..3u32 {
            let probe = TripAt::new(sample);
            let cancelled = preflight_declaration(&rec, DeclarationBudget::UNBOUNDED, Some(&probe));
            let Outcome::Inconclusive(inconclusive) = &cancelled else {
                unreachable!("a tripped probe must stop preflight")
            };
            let InconclusiveCause::Cancelled { at } = &inconclusive.cause else {
                unreachable!("cancellation must not be reported as exhaustion")
            };
            assert_eq!(
                at.text(),
                DeclarationCheckpoint::BeforeExpression(sample as usize).to_string(),
                "the probe must stop at the checkpoint it was set for"
            );
            // Cancellation is not exhaustion, and the taxonomy enforces that rather
            // than leaving it to convention.
            assert!(resource_stop(&cancelled).is_none());
            assert_eq!(cancelled.authority(), Authority::NonAuthoritative);
        }

        // An untripped probe must not change the answer.
        let probe = TripAt::new(u32::MAX);
        assert_eq!(
            preflight_declaration(&rec, DeclarationBudget::UNBOUNDED, Some(&probe))
                .into_complete()
                .expect("an untripped probe admits"),
            preflight_declaration(&rec, DeclarationBudget::UNBOUNDED, None)
                .into_complete()
                .expect("no probe admits")
        );
    }

    /// A refused preflight leaves the environment value-, root- and sharing-identical,
    /// and an adequate-budget retry produces the same digest and root.
    #[test]
    fn refused_declaration_preflight_publishes_nothing_and_retries_identically() {
        let options = KVMap::new();
        let base = Environment::new()
            .add_decl(axiom("Existing"))
            .expect("base builds");
        let base_root = base.logical_root(&options);
        let info = all_bearing_decl(AllBearingKind::Recursor, vec![n("a"), n("b")]);

        let refused = preflight_declaration(
            &info,
            DeclarationBudget {
                max_expr_nodes: 1,
                ..DeclarationBudget::UNBOUNDED
            },
            None,
        );
        assert!(refused.into_complete().is_err(), "the budget must bind");

        // Untouched: same value, same logical root, and still sharing with the
        // snapshot taken before the refusal.
        let after = base.clone();
        assert_eq!(base_root, base.logical_root(&options));
        assert_eq!(base_root, after.logical_root(&options));
        assert!(base.find(&n("Existing")).is_some());
        assert!(
            base.find(info.name()).is_none(),
            "a refused declaration must not be reachable"
        );

        // The retry is identical, which is the claim that makes a refusal safe to
        // recover from rather than merely safe to observe.
        let admitted = preflight_declaration(&info, DeclarationBudget::UNBOUNDED, None)
            .into_complete()
            .expect("adequate budget admits");
        assert_eq!(admitted.expressions, 3);
        let published = base.add_decl(info.clone()).expect("admission succeeds");
        let published_again = base
            .add_decl(info.clone())
            .expect("admission succeeds again");
        assert_eq!(
            Environment::decl_content_digest(&info),
            Environment::decl_content_digest(&info)
        );
        assert_eq!(
            published.logical_root(&options),
            published_again.logical_root(&options),
            "an adequate-budget retry must reproduce the same logical root"
        );
        assert_ne!(base_root, published.logical_root(&options));
    }

    fn prepared(
        env: &Environment,
        info: ConstantInfo,
        budget: DeclarationBudget,
    ) -> PreparedDeclarationAdmission {
        match env
            .plan_add_decl(info, budget, CollisionBudget::UNBOUNDED, None)
            .into_complete()
            .expect("planning admits")
        {
            DeclarationPlan::Prepared(plan) => plan,
            DeclarationPlan::DuplicateName { name } => {
                unreachable!("fixture name {name:?} must be fresh")
            }
        }
    }

    /// One preflighted transaction: plan then commit, publishing exactly once.
    #[test]
    fn declaration_admission_is_one_preflighted_transaction() {
        let options = KVMap::new();
        let base = Environment::new()
            .add_decl(axiom("Existing"))
            .expect("base builds");
        let info = multi_node_recursor();

        let plan = prepared(&base, info.clone(), DeclarationBudget::UNBOUNDED);
        // A plan is material, not authority, and it is never cacheable.
        assert!(!plan.is_cacheable());
        assert_eq!(plan.declaration(), &info);
        assert!(plan.is_valid_for(&base));
        assert_eq!(plan.usage().expressions, 3);

        let committed = plan
            .commit(&base, None)
            .into_complete()
            .expect("commit publishes");
        let DeclarationCommitted::Published(publication) = committed else {
            unreachable!("a fresh name must publish")
        };
        // The digest becomes reachable only through publication, and it is the same
        // value the unbudgeted encoder produces — the transaction does not redefine
        // identity, it only bounds the work of establishing it.
        assert_eq!(publication.digest, Environment::decl_content_digest(&info));
        assert_eq!(publication.environment.len(), base.len() + 1);
        assert!(publication.environment.find(info.name()).is_some());
        assert_ne!(
            base.logical_root(&options),
            publication.environment.logical_root(&options)
        );
    }

    /// A forced failure leaves the base observably identical — proved by comparing
    /// roots, contents and sharing before and after, not by reading the code path.
    #[test]
    fn a_failed_declaration_admission_leaves_the_base_untouched() {
        let options = KVMap::new();
        let base = Environment::new()
            .add_decl(axiom("Existing"))
            .expect("base builds")
            .add_decl(axiom("Second"))
            .expect("base builds");
        let info = multi_node_recursor();

        let root_before = base.logical_root(&options);
        let operational_before = Environment::operational_root(&options);
        let len_before = base.len();
        // A snapshot taken before the failure: if a failure disturbed structural
        // sharing, this and `base` would stop agreeing.
        let snapshot = base.clone();

        // Three independent forced failures, each a different arm.
        let starved = base
            .plan_add_decl(
                info.clone(),
                DeclarationBudget {
                    max_expr_nodes: 1,
                    ..DeclarationBudget::UNBOUNDED
                },
                CollisionBudget::UNBOUNDED,
                None,
            )
            .into_complete();
        assert!(starved.is_err(), "the node budget must bind");

        let probe = TripAt::new(0);
        let cancelled = base
            .plan_add_decl(
                info.clone(),
                DeclarationBudget::UNBOUNDED,
                CollisionBudget::UNBOUNDED,
                Some(&probe),
            )
            .into_complete();
        assert!(cancelled.is_err(), "a tripped probe must stop planning");

        // A plan committed against a moved base: superseded, and inconclusive rather
        // than a rejection, because the base moving says nothing about admissibility.
        let plan = prepared(&base, info.clone(), DeclarationBudget::UNBOUNDED);
        let moved = base.add_decl(axiom("Interloper")).expect("base moves");
        assert!(!plan.is_valid_for(&moved));
        let superseded = plan.commit(&moved, None);
        let Outcome::Inconclusive(inconclusive) = &superseded else {
            unreachable!("a superseded plan must not publish")
        };
        assert!(
            matches!(
                inconclusive.cause,
                InconclusiveCause::AuthorityIncomplete { .. }
            ),
            "a base that changed underfoot is an authority failure, not exhaustion"
        );
        assert_eq!(superseded.authority(), Authority::NonAuthoritative);
        assert_eq!(
            superseded.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );

        // The base is untouched after all three: same value, same roots, same length,
        // same contents, and still sharing with the pre-failure snapshot.
        assert_eq!(root_before, base.logical_root(&options));
        assert_eq!(root_before, snapshot.logical_root(&options));
        assert_eq!(operational_before, Environment::operational_root(&options));
        assert_eq!(len_before, base.len());
        assert_eq!(base, snapshot);
        assert!(base.find(&n("Existing")).is_some());
        assert!(base.find(&n("Second")).is_some());
        assert!(
            base.find(info.name()).is_none(),
            "a refused declaration must be unreachable in the base"
        );
        assert!(
            base.find(&n("Interloper")).is_none(),
            "publishing onto a fork must not touch the fork's base"
        );
    }

    /// An adequate-budget retry yields the same digest and root as the unlimited model.
    #[test]
    fn an_adequate_budget_retry_matches_the_unlimited_model() {
        let options = KVMap::new();
        let base = Environment::new()
            .add_decl(axiom("Existing"))
            .expect("base builds");
        let info = multi_node_recursor();

        // The unlimited mathematical model: the unbudgeted path, which is what the
        // bounded transaction must agree with exactly.
        let unlimited = base.add_decl(info.clone()).expect("unbudgeted admits");
        let unlimited_root = unlimited.logical_root(&options);
        let unlimited_digest = Environment::decl_content_digest(&info);

        // Refuse first, so the retry is a genuine retry after a failure.
        assert!(
            base.plan_add_decl(
                info.clone(),
                DeclarationBudget {
                    max_expr_nodes: 1,
                    ..DeclarationBudget::UNBOUNDED
                },
                CollisionBudget::UNBOUNDED,
                None,
            )
            .into_complete()
            .is_err()
        );

        let publication = match prepared(&base, info.clone(), DeclarationBudget::UNBOUNDED)
            .commit(&base, None)
            .into_complete()
            .expect("the retry publishes")
        {
            DeclarationCommitted::Published(publication) => publication,
            DeclarationCommitted::DuplicateName { name } => {
                unreachable!("{name:?} was refused, not admitted")
            }
        };
        assert_eq!(publication.digest, unlimited_digest);
        assert_eq!(
            publication.environment.logical_root(&options),
            unlimited_root,
            "the bounded transaction must land on the unlimited model's root"
        );
        assert_eq!(publication.environment, unlimited);

        // And repeating the whole transaction reproduces it, so the agreement is a
        // property of the operation rather than of one run.
        let again = match prepared(&base, info.clone(), DeclarationBudget::UNBOUNDED)
            .commit(&base, None)
            .into_complete()
            .expect("publishes again")
        {
            DeclarationCommitted::Published(publication) => publication,
            DeclarationCommitted::DuplicateName { .. } => unreachable!("still fresh"),
        };
        assert_eq!(again.digest, publication.digest);
        assert_eq!(
            again.environment.logical_root(&options),
            publication.environment.logical_root(&options)
        );
    }

    /// A duplicate is a completed verdict at both stages, never a non-answer.
    #[test]
    fn a_duplicate_name_is_a_completed_verdict_not_a_non_answer() {
        let info = multi_node_recursor();
        let occupied = Environment::new()
            .add_decl(info.clone())
            .expect("first admission");

        // At planning time: complete, with the verdict inside.
        let planned = occupied
            .plan_add_decl(
                info.clone(),
                DeclarationBudget::UNBOUNDED,
                CollisionBudget::UNBOUNDED,
                None,
            )
            .into_complete()
            .expect("a duplicate is a completed determination, not a stop");
        assert!(matches!(planned, DeclarationPlan::DuplicateName { .. }));

        // And at commit time, for a name taken after the plan was made: the plan is
        // still valid for its base, so this is a verdict rather than a supersession.
        let base = Environment::new();
        let plan = prepared(&base, info.clone(), DeclarationBudget::UNBOUNDED);
        let committed = plan
            .commit(&occupied, None)
            .into_complete()
            .expect("a duplicate at commit is still a completed determination");
        assert!(matches!(
            committed,
            DeclarationCommitted::DuplicateName { .. }
        ));
    }

    /// Named single-defect models for the declaration admission transaction.
    ///
    /// Each is an independent model of a *wrong* implementation, and each is killed by
    /// an assertion on the specific typed signal that defect would corrupt. That
    /// requirement is the point: a mutant that dies from a generic "the two differ"
    /// assertion proves the suite is noisy, not that the check it targets exists.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum AdmissionMutant {
        /// Omits one budget dimension, so a declaration over only that dimension is
        /// admitted. Killed on **authority**.
        MissingCheck,
        /// Measures the expensive expression dimensions before the cheap row families,
        /// so a doubly-over declaration reports the wrong primary reason. Killed on the
        /// **reported dimension**, which is what makes the order observable at all.
        LateCheck,
        /// Publishes into the base and only then discovers the refusal. Killed on the
        /// **base logical root** across the refusal path.
        PartialInsert,
        /// Reports an `observed` that does not exceed `allowed`. Killed by
        /// **`is_genuine_exhaustion`**, the typed predicate that exists for this.
        WrongActual,
        /// Reports cancellation as resource exhaustion. Killed on the **inconclusive
        /// cause discriminant**.
        CancellationAsRejection,
        /// Publishes a digest that is not the canonical encoder's. Killed on **digest
        /// equality** against the independent unbudgeted path.
        DigestDrift,
    }

    impl AdmissionMutant {
        const ALL: [AdmissionMutant; 6] = [
            AdmissionMutant::MissingCheck,
            AdmissionMutant::LateCheck,
            AdmissionMutant::PartialInsert,
            AdmissionMutant::WrongActual,
            AdmissionMutant::CancellationAsRejection,
            AdmissionMutant::DigestDrift,
        ];

        const fn label(self) -> &'static str {
            match self {
                AdmissionMutant::MissingCheck => "missing_check",
                AdmissionMutant::LateCheck => "late_check",
                AdmissionMutant::PartialInsert => "partial_insert",
                AdmissionMutant::WrongActual => "wrong_actual",
                AdmissionMutant::CancellationAsRejection => "cancellation_as_rejection",
                AdmissionMutant::DigestDrift => "digest_drift",
            }
        }

        /// The typed signal that kills this mutant, recorded so the evidence states
        /// *how* each died rather than only that it did.
        const fn kill_signal(self) -> &'static str {
            match self {
                AdmissionMutant::MissingCheck => "outcome_authority",
                AdmissionMutant::LateCheck => "reported_primary_dimension",
                AdmissionMutant::PartialInsert => "base_logical_root",
                AdmissionMutant::WrongActual => "is_genuine_exhaustion",
                AdmissionMutant::CancellationAsRejection => "inconclusive_cause_discriminant",
                AdmissionMutant::DigestDrift => "published_digest_vs_unbudgeted_encoder",
            }
        }
    }

    /// Every named mutant dies for its own typed reason.
    #[test]
    fn declaration_admission_named_mutants_are_each_killed_by_their_own_typed_signal() {
        let options = KVMap::new();
        let base = Environment::new()
            .add_decl(axiom("Existing"))
            .expect("base builds");
        let mut killed = Vec::new();

        // ---- missing_check: killed on AUTHORITY -------------------------------------
        // A declaration over the membership dimension only. Canonical refuses; a
        // preflight that never consults that dimension admits.
        let over_rows = all_bearing_decl(
            AllBearingKind::Definition,
            (0..6).map(|i| n(&format!("m{i}"))).collect(),
        );
        let bound = DeclarationBudget {
            max_mutual_rows: 2,
            ..DeclarationBudget::UNBOUNDED
        };
        let canonical = preflight_declaration(&over_rows, bound, None);
        let mutant = preflight_declaration(
            &over_rows,
            DeclarationBudget {
                // The modelled defect: this dimension is simply not checked.
                max_mutual_rows: u64::MAX,
                ..bound
            },
            None,
        );
        assert_eq!(canonical.authority(), Authority::NonAuthoritative);
        assert_eq!(
            mutant.authority(),
            Authority::Authoritative,
            "the missing-check model must admit, or it is not modelling a missing check"
        );
        killed.push(AdmissionMutant::MissingCheck);

        // ---- late_check: killed on the REPORTED PRIMARY DIMENSION ------------------
        // Over BOTH rows and expressions. The frozen order puts rows first, so
        // canonical names a row dimension; a preflight that measured expressions first
        // names a structural unit instead. Same input, same refusal, different reason —
        // which is precisely what makes the ordering observable rather than a comment.
        let doubly_over = multi_node_recursor();
        let both_bound = DeclarationBudget {
            max_mutual_rows: 0,
            max_expr_nodes: 1,
            ..DeclarationBudget::UNBOUNDED
        };
        let canonical_reason = preflight_declaration(&doubly_over, both_bound, None);
        let (_, canonical_progress) =
            resource_stop(&canonical_reason).expect("a double breach must refuse");
        assert_eq!(
            canonical_progress,
            Some(DeclarationDimension::MutualRows.as_str()),
            "the cheap dimension must be the reported reason"
        );
        let mut late_usage = DeclarationUsage::default();
        let late =
            preflight_declaration_expressions(&doubly_over, both_bound, None, &mut late_usage)
                .expect("the expression budget also binds, which is why this input is doubly over");
        let (_, late_progress) = resource_stop(&late).expect("the late model refuses too");
        assert_ne!(
            late_progress, canonical_progress,
            "expression-first ordering must report a different primary reason"
        );
        killed.push(AdmissionMutant::LateCheck);

        // ---- partial_insert: killed on the BASE LOGICAL ROOT ----------------------
        let root_before = base.logical_root(&options);
        let refused = base
            .plan_add_decl(
                doubly_over.clone(),
                both_bound,
                CollisionBudget::UNBOUNDED,
                None,
            )
            .into_complete();
        assert!(refused.is_err(), "the budget must bind");
        assert_eq!(
            root_before,
            base.logical_root(&options),
            "the canonical refusal must leave the base root identical"
        );
        // The modelled defect: it inserted anyway. Its base root moves.
        let partially_inserted = base
            .add_decl(doubly_over.clone())
            .expect("the model inserts unconditionally");
        assert_ne!(
            root_before,
            partially_inserted.logical_root(&options),
            "the partial-insert model must move the root, or it is not modelling a partial insert"
        );
        killed.push(AdmissionMutant::PartialInsert);

        // ---- wrong_actual: killed by IS_GENUINE_EXHAUSTION -----------------------
        let (canonical_usage, _) =
            resource_stop(&canonical).expect("the membership stop is a resource stop");
        assert!(
            canonical_usage.is_genuine_exhaustion(),
            "a canonical stop must report spending past its allowance"
        );
        let wrong_actual = ResourceUsage {
            reason: canonical_usage.reason.clone(),
            allowed: canonical_usage.allowed,
            // The modelled defect: the actual is reported as the limit, so the stop
            // claims a breach it does not evidence.
            observed: canonical_usage.allowed,
        };
        assert!(
            !wrong_actual.is_genuine_exhaustion(),
            "the wrong-actual model must fail the typed exhaustion predicate"
        );
        killed.push(AdmissionMutant::WrongActual);

        // ---- cancellation_as_rejection: killed on the CAUSE DISCRIMINANT ---------
        let probe = TripAt::new(0);
        let cancelled =
            preflight_declaration(&doubly_over, DeclarationBudget::UNBOUNDED, Some(&probe));
        let Outcome::Inconclusive(inconclusive) = &cancelled else {
            unreachable!("a tripped probe must stop preflight")
        };
        assert!(
            matches!(inconclusive.cause, InconclusiveCause::Cancelled { .. }),
            "cancellation must be reported as cancellation"
        );
        assert!(
            resource_stop(&cancelled).is_none(),
            "cancellation must not present as a resource stop"
        );
        // And the taxonomy refuses the conflation from the other side too: a
        // ResourceReason::Cancelled is not genuine exhaustion, so a model that dressed
        // a cancellation as a budget overrun fails its own predicate.
        let dressed_as_resource = ResourceUsage {
            reason: ResourceReason::Cancelled,
            allowed: 1,
            observed: 2,
        };
        assert!(
            !dressed_as_resource.is_genuine_exhaustion(),
            "a cancellation dressed as exhaustion must not pass as exhaustion"
        );
        killed.push(AdmissionMutant::CancellationAsRejection);

        // ---- digest_drift: killed on PUBLISHED DIGEST vs THE UNBUDGETED ENCODER --
        let fresh = multi_node_recursor();
        let published = match prepared(&base, fresh.clone(), DeclarationBudget::UNBOUNDED)
            .commit(&base, None)
            .into_complete()
            .expect("commit publishes")
        {
            DeclarationCommitted::Published(publication) => publication,
            DeclarationCommitted::DuplicateName { .. } => unreachable!("fresh name"),
        };
        let independent = Environment::decl_content_digest(&fresh);
        assert_eq!(
            published.digest, independent,
            "the transaction must publish the canonical encoder's digest"
        );
        // The modelled defect: any other declaration's digest. Distinct by construction.
        let drifted = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Definition,
            vec![n("drift")],
        ));
        assert_ne!(
            published.digest, drifted,
            "the digest-drift model must differ, or it is not modelling drift"
        );
        killed.push(AdmissionMutant::DigestDrift);

        // Coverage: every named mutant, each with a distinct kill signal, so no two are
        // being killed by the same assertion wearing two names.
        assert_eq!(killed.len(), AdmissionMutant::ALL.len());
        for mutant in AdmissionMutant::ALL {
            assert!(
                killed.contains(&mutant),
                "{} was not killed",
                mutant.label()
            );
        }
        let signals: HashSet<&str> = AdmissionMutant::ALL
            .iter()
            .map(|mutant| mutant.kill_signal())
            .collect();
        assert_eq!(
            signals.len(),
            AdmissionMutant::ALL.len(),
            "two mutants share a kill signal, so one of them is not independently proved"
        );

        for mutant in AdmissionMutant::ALL {
            eprintln!(
                "{{\"schema\":\"fln.unit.declaration-admission-mutant\",\"version\":1,\
                 \"bead\":\"franken_lean-j8h\",\"claim_type\":\"bounded_model\",\
                 \"scenario\":\"named-admission-mutants\",\"mutant\":\"{}\",\
                 \"kill_signal\":\"{}\",\"generic_assertion_used\":false,\
                 \"status\":\"killed\"}}",
                mutant.label(),
                mutant.kill_signal()
            );
        }
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-admission-mutant-summary\",\"version\":1,\
             \"bead\":\"franken_lean-j8h\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"named-admission-mutants\",\"mutants\":{},\
             \"distinct_kill_signals\":{},\"status\":\"pass\"}}",
            AdmissionMutant::ALL.len(),
            signals.len()
        );
    }

    /// Fixed seed for the schedule matrix. A constant, not a clock or an RNG: a
    /// schedule proof whose input cannot be reproduced is a story about one run.
    const SCHEDULE_SEED: u64 = 0x9e37_79b9_7f4a_7c15;

    /// Declaration count for the schedule matrix. Chosen so that the widest schedule
    /// still gives every worker real work — 64 over 32 workers is two each, and the
    /// test asserts no partition is empty.
    const SCHEDULE_DECLARATIONS: usize = 64;

    /// A declaration derived deterministically from `(seed, index)`.
    ///
    /// Shape varies with the index as well as the name, so workers are not all
    /// measuring the same structure: a matrix where every item is identical cannot
    /// distinguish a shared aggregate from a repeated one.
    fn seeded_declaration(seed: u64, index: usize) -> ConstantInfo {
        let mixed = seed ^ (usize_to_u64(index).wrapping_mul(0x1000_0000_01b3));
        let members = (0..(mixed % 3) + 1)
            .map(|member| n(&format!("member.{index}.{member}")))
            .collect();
        let depth = (mixed >> 8) % 3;
        let mut value = Expr::const_(n(&format!("body.{index}")), vec![Level::param(n("u"))]);
        for _ in 0..depth {
            value = Expr::app(value, Expr::sort(Level::param(n("u"))));
        }
        ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(&format!("scheduled.{index}")),
                level_params: vec![n("u")],
                type_: Expr::sort(Level::param(n("u"))),
            },
            value,
            hints: ReducibilityHints::Regular(u32::try_from(mixed % 4096).unwrap_or(0)),
            safety: DefinitionSafety::Safe,
            all: members,
        })
    }

    /// Canonical, order-independent reduction over admitted declarations.
    fn schedule_reduction(mut admitted: Vec<(Vec<u8>, Digest)>) -> Digest {
        admitted.sort_unstable();
        let mut w = CanonWriter::new();
        w.str("fln.test.declaration-admission-schedule");
        w.u16(1);
        w.u64(usize_to_u64(admitted.len()));
        for (name_bytes, digest) in admitted {
            w.bytes(&name_bytes);
            w.bytes(&digest.0);
        }
        hash(Domain::Fixture, &w.into_bytes())
    }

    fn canonical_name_bytes(name: &Name) -> Vec<u8> {
        let mut w = CanonWriter::new();
        name.write_body(&mut w);
        w.into_bytes()
    }

    /// The 1/8/32 schedule matrix: productive partitions, real threads, one reduction.
    ///
    /// Productive is asserted, not asserted-by-labelling. Every partition must be
    /// nonempty and the number of *distinct thread ids that did work* must equal the
    /// worker count — so a step that quietly ran serially under a thread-count label
    /// fails here rather than filling the matrix. That relabelling is itself a named
    /// mutant elsewhere in this epic, which is why it gets an assertion and not a
    /// comment.
    ///
    /// Workers do not share mutable state: each takes an O(1) persistent snapshot of
    /// the base and grows its own fork, which is what makes concurrent admission
    /// meaningful for a structurally-shared environment rather than a lock benchmark.
    ///
    /// Honest scope: this is bounded component evidence for declaration admission under
    /// concurrency, not full closure for the bead.
    #[test]
    fn declaration_admission_is_stable_across_1_8_32_productive_schedules() {
        let base = Environment::new()
            .add_decl(axiom("Existing"))
            .expect("base builds");
        let declarations: Vec<ConstantInfo> = (0..SCHEDULE_DECLARATIONS)
            .map(|index| seeded_declaration(SCHEDULE_SEED, index))
            .collect();

        // The sequential model, built independently of any schedule.
        let sequential: Vec<(Vec<u8>, Digest)> = declarations
            .iter()
            .map(|info| {
                (
                    canonical_name_bytes(info.name()),
                    Environment::decl_content_digest(info),
                )
            })
            .collect();
        let expected_reduction = schedule_reduction(sequential.clone());

        let mut reductions = Vec::new();
        for worker_count in [1usize, 8, 32] {
            let (admitted, partition_sizes, thread_ids) = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker| {
                        let base = base.clone();
                        let declarations = &declarations;
                        scope.spawn(move || {
                            let mut env = base;
                            let mut mine = Vec::new();
                            for (index, info) in declarations.iter().enumerate() {
                                if index % worker_count != worker {
                                    continue;
                                }
                                let plan = match env
                                    .plan_add_decl(
                                        info.clone(),
                                        DeclarationBudget::UNBOUNDED,
                                        CollisionBudget::UNBOUNDED,
                                        None,
                                    )
                                    .into_complete()
                                    .expect("unbounded planning admits")
                                {
                                    DeclarationPlan::Prepared(plan) => plan,
                                    DeclarationPlan::DuplicateName { name } => {
                                        unreachable!("seeded name {name:?} must be unique")
                                    }
                                };
                                let published = match plan
                                    .commit(&env, None)
                                    .into_complete()
                                    .expect("commit publishes")
                                {
                                    DeclarationCommitted::Published(publication) => publication,
                                    DeclarationCommitted::DuplicateName { .. } => {
                                        unreachable!("seeded names are unique")
                                    }
                                };
                                mine.push((canonical_name_bytes(info.name()), published.digest));
                                env = published.environment;
                            }
                            (mine, std::thread::current().id())
                        })
                    })
                    .collect();
                let mut admitted = Vec::new();
                let mut sizes = Vec::new();
                let mut ids = HashSet::new();
                for handle in handles {
                    let (mine, id) = handle.join().expect("worker completes");
                    sizes.push(mine.len());
                    ids.insert(id);
                    admitted.extend(mine);
                }
                (admitted, sizes, ids)
            });

            // Productive: no idle worker, and as many real threads as workers.
            assert_eq!(partition_sizes.len(), worker_count);
            assert!(
                partition_sizes.iter().all(|size| *size > 0),
                "an empty partition means this worker count is a label, not a schedule \
                 (sizes {partition_sizes:?})"
            );
            assert_eq!(
                partition_sizes.iter().sum::<usize>(),
                SCHEDULE_DECLARATIONS,
                "the partitions must cover every declaration exactly once"
            );
            assert_eq!(
                thread_ids.len(),
                worker_count,
                "work must be done by {worker_count} distinct threads, not relabelled serial work"
            );

            let reduction = schedule_reduction(admitted.clone());
            assert_eq!(
                reduction, expected_reduction,
                "schedule with {worker_count} workers diverged from the sequential model"
            );
            reductions.push((worker_count, reduction, partition_sizes, thread_ids.len()));
        }

        // One reduction across the whole matrix.
        let distinct: HashSet<Digest> = reductions
            .iter()
            .map(|(_, reduction, _, _)| *reduction)
            .collect();
        assert_eq!(
            distinct.len(),
            1,
            "the reduction must not depend on the worker count"
        );

        // `distinct_worker_threads` carries the MEASURED thread count, not the worker
        // count it was asserted equal to. Emitting the input where the row promises an
        // observation is how a matrix comes to describe work it did not do.
        for (worker_count, reduction, sizes, measured_threads) in &reductions {
            let min = sizes.iter().min().copied().unwrap_or_default();
            let max = sizes.iter().max().copied().unwrap_or_default();
            eprintln!(
                "{{\"schema\":\"fln.unit.declaration-admission-schedule\",\"version\":1,\
                 \"bead\":\"franken_lean-j8h\",\"claim_type\":\"bounded_model\",\
                 \"gate_relation\":\"partial-component-evidence\",\
                 \"scenario\":\"productive-1-8-32-admission-matrix\",\
                 \"seed\":\"{SCHEDULE_SEED:#018x}\",\
                 \"declarations\":{SCHEDULE_DECLARATIONS},\
                 \"worker_count\":{worker_count},\
                 \"distinct_worker_threads\":{measured_threads},\
                 \"partition_scheme\":\"index-modulo-worker-count-v1\",\
                 \"min_partition\":{min},\"max_partition\":{max},\
                 \"empty_partitions\":0,\
                 \"execution_model\":\"independent_persistent_fork_per_worker\",\
                 \"reduction\":\"canonical-sorted-name-digest-set-v1\",\
                 \"reduction_digest\":\"{reduction}\",\
                 \"matches_sequential_model\":true,\"status\":\"pass\"}}"
            );
        }
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-admission-schedule-summary\",\"version\":1,\
             \"bead\":\"franken_lean-j8h\",\"claim_type\":\"bounded_model\",\
             \"gate_relation\":\"partial-component-evidence\",\
             \"scenario\":\"productive-1-8-32-admission-matrix\",\
             \"seed\":\"{SCHEDULE_SEED:#018x}\",\"worker_counts\":[1,8,32],\
             \"declarations\":{SCHEDULE_DECLARATIONS},\
             \"distinct_reductions\":{},\"expected_distinct_reductions\":1,\
             \"reduction_digest\":\"{expected_reduction}\",\"status\":\"pass\"}}",
            distinct.len()
        );
    }

    /// An unset budget behaves exactly as the pre-budget code did, and preflight
    /// moves no identity.
    #[test]
    fn declaration_row_preflight_is_identity_neutral_at_the_default_budget() {
        assert_eq!(DeclarationBudget::default(), DeclarationBudget::UNBOUNDED);
        for kind in AllBearingKind::ALL {
            let info = all_bearing_decl(kind, vec![n("a"), n("b")]);
            let before = Environment::decl_content_digest(&info);
            let admitted = preflight_declaration_rows(&info, DeclarationBudget::default());
            assert!(matches!(admitted, Outcome::Complete(_)));
            assert_eq!(
                before,
                Environment::decl_content_digest(&info),
                "preflight must be a pure measurement ({})",
                kind.label()
            );
        }
    }
}
