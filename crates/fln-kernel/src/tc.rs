//! K1 bootstrap: the certified checker's typing, reduction, and defeq core
//! (bead franken_lean-zht; every rule tagged to KERNEL_CONTRACT.md).
//!
//! Slice scope (recorded on beads franken_lean-zht + franken_lean-5p2):
//! KR-100..112 typing, whnf with beta/zeta/mdata/proj/delta (KR-200..204) and
//! recursor dispatch (KR-205) — quotient computation (KR-955), inductive iota
//! (KR-316) with K conversion (KR-317), Nat-literal-to-constructor, and
//! structure-eta coercion — defeq with quick/bindings/levels/proof-irrelevance/
//! lazy-delta/function-eta/app-congruence (KR-300..312 subset), Nat literal
//! acceleration (KR-313: `reduce_nat` in the whnf loop plus the offset and
//! Bool.true-reflection machinery in defeq, wired to fln-bignum), String literal
//! expansion (KR-314: recursor major, projection scrutinee, and the defeq
//! `String.ofList` rung), unit-like eta (KR-315), structure eta in defeq
//! (KR-903), and declaration admission for axioms, definitions, theorems,
//! opaques, and non-safe mutual definitions (KR-970..977). `reduce_native`
//! (`Lean.reduceBool`/`Lean.reduceNat` — the native_decide trust surface) and
//! receipts are follow-up slices; neither absence widens acceptance — an
//! unimplemented reduction can only make defeq FAIL (a rejection), never
//! succeed.
//!
//! Traversal discipline (§8.2c): every recursive descent charges the step budget
//! and carries an explicit depth that is checked BEFORE descending, so
//! attacker-controlled term depth converts to a typed `Inconclusive`, never a stack
//! fault. Flag pruning (loose-bvar ranges, has-level-param) keeps substitution
//! linear in the touched region only.

use std::collections::HashMap;

use fln_bignum::interop::{bignat_from_literal, literal_from_bignat};
use fln_bignum::nat::BigNat;
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{
    ConstantInfo, DefinitionSafety, QuotKind, RecursorVal, ReducibilityHints,
};
use fln_env::environment::Environment;

use crate::verdict::{Budget, Consumption, ExhaustionReason, RejectClass};

/// Internal control flow: a real rejection or a budget stop. Never observable
/// outside `check`/`check_defeq`, which convert to [`Verdict`].
#[derive(Debug)]
pub(crate) enum Stop {
    Reject(RejectClass, String),
    Exhausted(ExhaustionReason),
    /// Private continuation signal used to unwind a newly exposed nested
    /// recursor back to `whnf_recursor_chain`. It is caught inside `tc.rs` and
    /// must never cross the kernel authority boundary.
    DeferredRecursor {
        frame: Box<InductiveReductionFrame>,
        major: Expr,
    },
    /// OUR accounting contradicted itself — not a statement about the
    /// declaration. Added for the bounded admission migration
    /// (`fln-kernel-bounded-decl-admission-ukzx`): the bounded environment path
    /// can return an InternalFault, and the two existing arms could only have
    /// reported it as a rejection (an FL-INV-07 collapse — "we broke" recorded
    /// as "your declaration is invalid") or as resource exhaustion (a
    /// misreport, since ExhaustionReason is Steps|Depth and neither happened).
    Fault(String),
}

type KResult<T> = Result<T, Stop>;

fn reject<T>(class: RejectClass, message: impl Into<String>) -> KResult<T> {
    Err(Stop::Reject(class, message.into()))
}

// The Reference type-checker state memoizes inference, whnf-core, whnf, and
// established definitional equalities (KR-1xx/KR-200/KR-300). K1 used to
// recompute all four. These caches are deliberately per-TypeChecker: their
// contents are an optimization inside one governed check, never durable
// authority and never shared across environments, safety modes, or budgets.
//
// A hostile term controls the cached expressions and their 32-bit Reference
// hashes, so the row, collision, dependency-cell, and dependency-scan counts
// are bounded. Four structural candidates per packed-data bucket cap collision
// work; 65,536 rows cap reuse. Fvar-bearing rows may retain at most 262,144
// local-generation snapshots per cache, with no one row retaining more than
// 256 or scanning more than 65,536 distinct expression allocations to discover
// them. Each cache may spend at most 33,554,432 node visits on dependency
// discovery in total. A bounded packed-key refusal set prevents an expression
// beyond those limits from repeatedly consuming that allowance; a hash
// collision can therefore suppress reuse, never manufacture a result.
// Dead-generation rows are reclaimed from a touched bucket before its collision
// cap is applied. These are shallow cardinality bounds: retained Expr DAG weight,
// allocator failure, cancellation, and Consumption-accounted cache bookkeeping
// remain outside them, so they do not by themselves close FL-INV-07.
// Saturation simply stops admitting new cache rows. It cannot evict an answer,
// change a completed result, or turn an interrupted computation into one.
const TYPE_CHECKER_CACHE_MAX_ENTRIES: usize = 65_536;
const TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES: usize = 4;
const TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS: usize = 262_144;
const TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCIES_PER_ENTRY: usize = 256;
const TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES: usize = 33_554_432;
const TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES_PER_ENTRY: usize = 65_536;

#[derive(Clone, Copy, PartialEq, Eq)]
enum InferMode {
    Check,
    Only,
}

/// One local binding on which a cached result actually depends.
///
/// The Reference keeps established equivalences across temporary binder
/// pushes.  Keying every fvar-bearing result by the whole telescope epoch
/// throws that reuse away whenever an unrelated binder is opened or closed.
/// The opposite shortcut -- treating fvar terms as closed -- is unsound when
/// an externally adopted identifier is later reused with another binding.
/// Store the transitive binding slice instead: a hit is valid exactly while
/// every referenced local still names the same immutable binding generation.
#[derive(Clone, PartialEq, Eq)]
struct LocalDependency {
    id: FVarId,
    generation: u64,
}

/// One local binder introduced during descent.
struct LocalDecl {
    id: FVarId,
    previous_same_id: Option<usize>,
    /// Monotonic identity for this immutable binding within one checker.
    /// `None` disables fvar-bearing cache rows after theoretical u64 overflow.
    generation: Option<u64>,
    type_: Expr,
    /// Present for let-bound locals (zeta target, KR-203).
    value: Option<Expr>,
}

fn collect_fvar_ids(
    expr: &Expr,
    ids: &mut Vec<FVarId>,
    seen_ids: &mut HashMap<FVarId, ()>,
    seen_nodes: &mut HashMap<usize, ()>,
    nodes_left: &mut usize,
) -> bool {
    if !expr.has_fvar() {
        return true;
    }
    let mut pending = vec![expr.clone()];
    while let Some(current) = pending.pop() {
        if seen_nodes
            .insert(current.allocation_identity(), ())
            .is_some()
        {
            continue;
        }
        let Some(remaining) = nodes_left.checked_sub(1) else {
            return false;
        };
        *nodes_left = remaining;
        if !current.has_fvar() {
            continue;
        }
        match current.node() {
            ExprNode::FVar { id } => {
                if seen_ids.insert(id.clone(), ()).is_none() {
                    ids.push(id.clone());
                    if ids.len() > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCIES_PER_ENTRY {
                        return false;
                    }
                }
            }
            ExprNode::App { f, a } => {
                pending.push(f.clone());
                pending.push(a.clone());
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type.clone());
                pending.push(body.clone());
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(type_.clone());
                pending.push(value.clone());
                pending.push(body.clone());
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                pending.push(expr.clone());
            }
            ExprNode::BVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    true
}

fn local_dependencies(
    expressions: &[&Expr],
    locals: &[LocalDecl],
    local_positions: &HashMap<FVarId, usize>,
    nodes_left: &mut usize,
) -> Option<Vec<LocalDependency>> {
    let mut ids = Vec::new();
    let mut seen_ids = HashMap::new();
    let mut seen_nodes = HashMap::new();
    for expression in expressions {
        if !collect_fvar_ids(
            expression,
            &mut ids,
            &mut seen_ids,
            &mut seen_nodes,
            nodes_left,
        ) {
            return None;
        }
    }
    if ids.len() > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCIES_PER_ENTRY {
        return None;
    }
    let mut next = 0;
    let mut dependencies = Vec::new();
    while let Some(id) = ids.get(next).cloned() {
        next += 1;
        let local = local_positions
            .get(&id)
            .and_then(|position| locals.get(*position))?;
        if !collect_fvar_ids(
            &local.type_,
            &mut ids,
            &mut seen_ids,
            &mut seen_nodes,
            nodes_left,
        ) {
            return None;
        }
        if let Some(value) = &local.value
            && !collect_fvar_ids(value, &mut ids, &mut seen_ids, &mut seen_nodes, nodes_left)
        {
            return None;
        }
        if ids.len() > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCIES_PER_ENTRY {
            return None;
        }
        dependencies.push(LocalDependency {
            id,
            generation: local.generation?,
        });
    }
    dependencies.sort_by(|left, right| left.id.0.cmp(&right.id.0));
    Some(dependencies)
}

fn dependencies_are_live(
    dependencies: &[LocalDependency],
    locals: &[LocalDecl],
    local_positions: &HashMap<FVarId, usize>,
) -> bool {
    dependencies.iter().all(|dependency| {
        local_positions
            .get(&dependency.id)
            .and_then(|position| locals.get(*position))
            .is_some_and(|local| local.generation == Some(dependency.generation))
    })
}

struct ExprResultCacheEntry {
    key: Expr,
    value: Expr,
    dependencies: Vec<LocalDependency>,
}

struct ExprResultCache {
    buckets: HashMap<u64, Vec<ExprResultCacheEntry>>,
    dependency_scan_refusals: HashMap<u64, ()>,
    entries: usize,
    local_dependency_cells: usize,
    local_dependency_scan_nodes: usize,
    max_entries: usize,
    max_bucket_entries: usize,
}

impl ExprResultCache {
    fn new() -> Self {
        Self::bounded(
            TYPE_CHECKER_CACHE_MAX_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        )
    }

    fn bounded(max_entries: usize, max_bucket_entries: usize) -> Self {
        Self {
            buckets: HashMap::new(),
            dependency_scan_refusals: HashMap::new(),
            entries: 0,
            local_dependency_cells: 0,
            local_dependency_scan_nodes: 0,
            max_entries,
            max_bucket_entries,
        }
    }

    fn get(
        &self,
        key: &Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) -> Option<Expr> {
        self.buckets.get(&key.data().0)?.iter().find_map(|entry| {
            (entry.key == *key
                && dependencies_are_live(&entry.dependencies, locals, local_positions))
            .then(|| entry.value.clone())
        })
    }

    fn insert(
        &mut self,
        key: Expr,
        value: Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) {
        let packed = key.data().0;
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            let before = bucket.len();
            let mut removed_cells = 0_usize;
            bucket.retain(|entry| {
                let live = dependencies_are_live(&entry.dependencies, locals, local_positions);
                if !live {
                    removed_cells += entry.dependencies.len();
                }
                live
            });
            self.entries -= before - bucket.len();
            self.local_dependency_cells -= removed_cells;
        }
        if self.buckets.get(&packed).is_some_and(Vec::is_empty) {
            self.buckets.remove(&packed);
        }
        if self.entries >= self.max_entries
            || self.max_bucket_entries == 0
            || self
                .buckets
                .get(&packed)
                .is_some_and(|bucket| bucket.len() >= self.max_bucket_entries)
        {
            return;
        }
        if self.local_dependency_cells >= TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS
            && (key.has_fvar() || value.has_fvar())
        {
            return;
        }
        if self.dependency_scan_refusals.contains_key(&packed)
            || self.dependency_scan_refusals.len() >= self.max_entries
        {
            return;
        }
        let scan_limit = TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES
            .saturating_sub(self.local_dependency_scan_nodes)
            .min(TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES_PER_ENTRY);
        let mut nodes_left = scan_limit;
        let dependencies =
            local_dependencies(&[&key, &value], locals, local_positions, &mut nodes_left);
        self.local_dependency_scan_nodes += scan_limit - nodes_left;
        let Some(dependencies) = dependencies else {
            if self.dependency_scan_refusals.len() < self.max_entries {
                self.dependency_scan_refusals.insert(packed, ());
            }
            return;
        };
        let dependency_count = dependencies.len();
        if self
            .local_dependency_cells
            .checked_add(dependency_count)
            .is_none_or(|cells| cells > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS)
        {
            if self.dependency_scan_refusals.len() < self.max_entries {
                self.dependency_scan_refusals.insert(packed, ());
            }
            return;
        }
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if let Some(existing) = bucket
                .iter_mut()
                .find(|entry| entry.key == key && entry.dependencies == dependencies)
            {
                existing.value = value;
                return;
            }
            bucket.push(ExprResultCacheEntry {
                key,
                value,
                dependencies,
            });
            self.entries += 1;
            self.local_dependency_cells += dependency_count;
            return;
        }
        self.buckets.insert(
            packed,
            vec![ExprResultCacheEntry {
                key,
                value,
                dependencies,
            }],
        );
        self.entries += 1;
        self.local_dependency_cells += dependency_count;
    }
}

struct PositiveDefEqCache {
    buckets: HashMap<(u64, u64), Vec<PositiveDefEqCacheEntry>>,
    dependency_scan_refusals: HashMap<(u64, u64), ()>,
    entries: usize,
    local_dependency_cells: usize,
    local_dependency_scan_nodes: usize,
    max_entries: usize,
    max_bucket_entries: usize,
}

struct PositiveDefEqCacheEntry {
    left: Expr,
    right: Expr,
    dependencies: Vec<LocalDependency>,
}

impl PositiveDefEqCache {
    fn new() -> Self {
        Self::bounded(
            TYPE_CHECKER_CACHE_MAX_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        )
    }

    fn bounded(max_entries: usize, max_bucket_entries: usize) -> Self {
        Self {
            buckets: HashMap::new(),
            dependency_scan_refusals: HashMap::new(),
            entries: 0,
            local_dependency_cells: 0,
            local_dependency_scan_nodes: 0,
            max_entries,
            max_bucket_entries,
        }
    }

    fn packed_key(left: &Expr, right: &Expr) -> (u64, u64) {
        let left = left.data().0;
        let right = right.data().0;
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    }

    fn contains(
        &self,
        left: &Expr,
        right: &Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) -> bool {
        self.buckets
            .get(&Self::packed_key(left, right))
            .is_some_and(|bucket| {
                bucket.iter().any(|entry| {
                    ((entry.left == *left && entry.right == *right)
                        || (entry.left == *right && entry.right == *left))
                        && dependencies_are_live(&entry.dependencies, locals, local_positions)
                })
            })
    }

    fn insert(
        &mut self,
        left: Expr,
        right: Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) {
        let packed = Self::packed_key(&left, &right);
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            let before = bucket.len();
            let mut removed_cells = 0_usize;
            bucket.retain(|entry| {
                let live = dependencies_are_live(&entry.dependencies, locals, local_positions);
                if !live {
                    removed_cells += entry.dependencies.len();
                }
                live
            });
            self.entries -= before - bucket.len();
            self.local_dependency_cells -= removed_cells;
        }
        if self.buckets.get(&packed).is_some_and(Vec::is_empty) {
            self.buckets.remove(&packed);
        }
        if self.entries >= self.max_entries
            || self.max_bucket_entries == 0
            || self
                .buckets
                .get(&packed)
                .is_some_and(|bucket| bucket.len() >= self.max_bucket_entries)
        {
            return;
        }
        if self.local_dependency_cells >= TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS
            && (left.has_fvar() || right.has_fvar())
        {
            return;
        }
        if self.dependency_scan_refusals.contains_key(&packed)
            || self.dependency_scan_refusals.len() >= self.max_entries
        {
            return;
        }
        let scan_limit = TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES
            .saturating_sub(self.local_dependency_scan_nodes)
            .min(TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES_PER_ENTRY);
        let mut nodes_left = scan_limit;
        let dependencies =
            local_dependencies(&[&left, &right], locals, local_positions, &mut nodes_left);
        self.local_dependency_scan_nodes += scan_limit - nodes_left;
        let Some(dependencies) = dependencies else {
            if self.dependency_scan_refusals.len() < self.max_entries {
                self.dependency_scan_refusals.insert(packed, ());
            }
            return;
        };
        let dependency_count = dependencies.len();
        if self
            .local_dependency_cells
            .checked_add(dependency_count)
            .is_none_or(|cells| cells > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS)
        {
            if self.dependency_scan_refusals.len() < self.max_entries {
                self.dependency_scan_refusals.insert(packed, ());
            }
            return;
        }
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if bucket.iter().any(|entry| {
                ((entry.left == left && entry.right == right)
                    || (entry.left == right && entry.right == left))
                    && entry.dependencies == dependencies
            }) {
                return;
            }
            bucket.push(PositiveDefEqCacheEntry {
                left,
                right,
                dependencies,
            });
            self.entries += 1;
            self.local_dependency_cells += dependency_count;
            return;
        }
        self.buckets.insert(
            packed,
            vec![PositiveDefEqCacheEntry {
                left,
                right,
                dependencies,
            }],
        );
        self.entries += 1;
        self.local_dependency_cells += dependency_count;
    }
}

type InstantiateCacheKey = (u64, u32, u64);
type InstantiateCacheEntry = (Expr, u32, Expr, Expr);

struct InstantiateCache {
    buckets: HashMap<InstantiateCacheKey, Vec<InstantiateCacheEntry>>,
    entries: usize,
    max_entries: usize,
    max_bucket_entries: usize,
}

impl InstantiateCache {
    fn new() -> Self {
        Self::bounded(
            TYPE_CHECKER_CACHE_MAX_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        )
    }

    fn bounded(max_entries: usize, max_bucket_entries: usize) -> Self {
        Self {
            buckets: HashMap::new(),
            entries: 0,
            max_entries,
            max_bucket_entries,
        }
    }

    fn packed_key(source: &Expr, binder: u32, substitute: &Expr) -> InstantiateCacheKey {
        (source.data().0, binder, substitute.data().0)
    }

    fn get(&self, source: &Expr, binder: u32, substitute: &Expr) -> Option<Expr> {
        self.buckets
            .get(&Self::packed_key(source, binder, substitute))?
            .iter()
            .find_map(
                |(candidate_source, candidate_binder, candidate_substitute, result)| {
                    (candidate_source == source
                        && *candidate_binder == binder
                        && candidate_substitute == substitute)
                        .then(|| result.clone())
                },
            )
    }

    fn insert(&mut self, source: Expr, binder: u32, substitute: Expr, result: Expr) {
        let packed = Self::packed_key(&source, binder, &substitute);
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if let Some((_, _, _, existing)) = bucket.iter_mut().find(
                |(candidate_source, candidate_binder, candidate_substitute, _)| {
                    candidate_source == &source
                        && *candidate_binder == binder
                        && candidate_substitute == &substitute
                },
            ) {
                *existing = result;
                return;
            }
            if self.entries >= self.max_entries || bucket.len() >= self.max_bucket_entries {
                return;
            }
            bucket.push((source, binder, substitute, result));
            self.entries += 1;
            return;
        }
        if self.entries >= self.max_entries || self.max_bucket_entries == 0 {
            return;
        }
        self.buckets
            .insert(packed, vec![(source, binder, substitute, result)]);
        self.entries += 1;
    }
}

type InstantiateRevCacheKey = (u64, u32);
type InstantiateRevCacheEntry = (Expr, u32, Expr);

struct InstantiateRevCache {
    buckets: HashMap<InstantiateRevCacheKey, Vec<InstantiateRevCacheEntry>>,
    entries: usize,
    max_entries: usize,
    max_bucket_entries: usize,
}

impl InstantiateRevCache {
    fn new() -> Self {
        Self {
            buckets: HashMap::new(),
            entries: 0,
            max_entries: TYPE_CHECKER_CACHE_MAX_ENTRIES,
            max_bucket_entries: TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        }
    }

    fn get(&self, source: &Expr, bound: u32) -> Option<Expr> {
        self.buckets
            .get(&(source.data().0, bound))?
            .iter()
            .find_map(|(candidate, candidate_bound, result)| {
                (candidate == source && *candidate_bound == bound).then(|| result.clone())
            })
    }

    fn insert(&mut self, source: Expr, bound: u32, result: Expr) {
        let packed = (source.data().0, bound);
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if let Some((_, _, existing)) =
                bucket.iter_mut().find(|(candidate, candidate_bound, _)| {
                    candidate == &source && *candidate_bound == bound
                })
            {
                *existing = result;
                return;
            }
            if self.entries >= self.max_entries || bucket.len() >= self.max_bucket_entries {
                return;
            }
            bucket.push((source, bound, result));
            self.entries += 1;
            return;
        }
        if self.entries >= self.max_entries || self.max_bucket_entries == 0 {
            return;
        }
        self.buckets.insert(packed, vec![(source, bound, result)]);
        self.entries += 1;
    }
}

struct LParamContext {
    params: Vec<Name>,
    levels: Vec<Level>,
    id: u32,
}

struct InstantiateLParamsCache {
    contexts: HashMap<(u64, u64, usize, usize), Vec<LParamContext>>,
    context_count: usize,
    results: HashMap<(u32, u64), Vec<(Expr, Expr)>>,
    entries: usize,
    max_contexts: usize,
    max_entries: usize,
    max_bucket_entries: usize,
}

impl InstantiateLParamsCache {
    fn new() -> Self {
        Self::bounded(
            TYPE_CHECKER_CACHE_MAX_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        )
    }

    fn bounded(max_entries: usize, max_bucket_entries: usize) -> Self {
        Self {
            contexts: HashMap::new(),
            context_count: 0,
            results: HashMap::new(),
            entries: 0,
            max_contexts: max_entries.min(1_024),
            max_entries,
            max_bucket_entries,
        }
    }

    fn context_key(params: &[Name], levels: &[Level]) -> (u64, u64, usize, usize) {
        fn fold_hashes(values: impl Iterator<Item = u64>) -> u64 {
            values.fold(0x9e37_79b9_7f4a_7c15, |state, value| {
                state.rotate_left(11) ^ value.wrapping_add(0x517c_c1b7_2722_0a95)
            })
        }
        (
            fold_hashes(params.iter().map(Name::hash)),
            fold_hashes(levels.iter().map(Level::hash)),
            params.len(),
            levels.len(),
        )
    }

    fn context_id(&self, params: &[Name], levels: &[Level]) -> Option<u32> {
        self.contexts
            .get(&Self::context_key(params, levels))?
            .iter()
            .find_map(|context| {
                (context.params == params && context.levels == levels).then_some(context.id)
            })
    }

    fn get(&self, source: &Expr, params: &[Name], levels: &[Level]) -> Option<Expr> {
        let context = self.context_id(params, levels)?;
        self.results
            .get(&(context, source.data().0))?
            .iter()
            .find_map(|(candidate, result)| (candidate == source).then(|| result.clone()))
    }

    fn ensure_context(&mut self, params: &[Name], levels: &[Level]) -> Option<u32> {
        let key = Self::context_key(params, levels);
        if let Some(bucket) = self.contexts.get_mut(&key) {
            if let Some(context) = bucket
                .iter()
                .find(|context| context.params == params && context.levels == levels)
            {
                return Some(context.id);
            }
            if self.context_count >= self.max_contexts || bucket.len() >= self.max_bucket_entries {
                return None;
            }
            let id = u32::try_from(self.context_count).ok()?;
            bucket.push(LParamContext {
                params: params.to_vec(),
                levels: levels.to_vec(),
                id,
            });
            self.context_count += 1;
            return Some(id);
        }
        if self.context_count >= self.max_contexts || self.max_bucket_entries == 0 {
            return None;
        }
        let id = u32::try_from(self.context_count).ok()?;
        self.contexts.insert(
            key,
            vec![LParamContext {
                params: params.to_vec(),
                levels: levels.to_vec(),
                id,
            }],
        );
        self.context_count += 1;
        Some(id)
    }

    fn insert(&mut self, source: Expr, params: &[Name], levels: &[Level], result: Expr) {
        if self.entries >= self.max_entries {
            return;
        }
        let Some(context) = self.ensure_context(params, levels) else {
            return;
        };
        let packed = (context, source.data().0);
        if let Some(bucket) = self.results.get_mut(&packed) {
            if let Some((_, existing)) = bucket
                .iter_mut()
                .find(|(candidate, _)| candidate == &source)
            {
                *existing = result;
                return;
            }
            if bucket.len() >= self.max_bucket_entries {
                return;
            }
            bucket.push((source, result));
            self.entries += 1;
            return;
        }
        if self.max_bucket_entries == 0 {
            return;
        }
        self.results.insert(packed, vec![(source, result)]);
        self.entries += 1;
    }
}

struct RecursorMajorCache {
    buckets: HashMap<u64, Vec<(Name, Option<Name>)>>,
    entries: usize,
    max_entries: usize,
    max_bucket_entries: usize,
}

impl RecursorMajorCache {
    fn new() -> Self {
        Self {
            buckets: HashMap::new(),
            entries: 0,
            max_entries: 1_024,
            max_bucket_entries: TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        }
    }

    fn get(&self, recursor: &Name) -> Option<Option<Name>> {
        self.buckets
            .get(&recursor.hash())?
            .iter()
            .find_map(|(candidate, result)| (candidate == recursor).then(|| result.clone()))
    }

    fn insert(&mut self, recursor: Name, result: Option<Name>) {
        let packed = recursor.hash();
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if let Some((_, existing)) = bucket
                .iter_mut()
                .find(|(candidate, _)| candidate == &recursor)
            {
                *existing = result;
                return;
            }
            if self.entries >= self.max_entries || bucket.len() >= self.max_bucket_entries {
                return;
            }
            bucket.push((recursor, result));
            self.entries += 1;
            return;
        }
        if self.entries >= self.max_entries || self.max_bucket_entries == 0 {
            return;
        }
        self.buckets.insert(packed, vec![(recursor, result)]);
        self.entries += 1;
    }
}

#[derive(Debug)]
pub(crate) struct InductiveReductionFrame {
    original: Expr,
    rec: RecursorVal,
    levels: Vec<Level>,
    rec_args: Vec<Expr>,
    major_idx: usize,
}

enum WhnfRecursorContinuation {
    Finish(InductiveReductionFrame),
    Cache(Expr),
    Retry(Expr),
}

pub(crate) struct TypeChecker<'a> {
    env: &'a Environment,
    lparams: &'a [Name],
    locals: Vec<LocalDecl>,
    local_positions: HashMap<FVarId, usize>,
    fresh: u64,
    next_local_generation: Option<u64>,
    budget: Budget,
    used: Consumption,
    /// The checking context's safety mode (pin `m_definition_safety`): gates
    /// KR-973 constant references. `Safe` everywhere except unsafe-declaration
    /// bodies and unsafe inductive blocks.
    safety: DefinitionSafety,
    /// The pin maintains separate tables because an infer-only result proves
    /// a type but deliberately skips the checking-mode safety and well-formedness
    /// obligations. Sharing either direction would turn an optimization into
    /// authority.
    infer_cache: ExprResultCache,
    infer_only_cache: ExprResultCache,
    whnf_core_cache: ExprResultCache,
    whnf_cache: ExprResultCache,
    positive_def_eq_cache: PositiveDefEqCache,
    instantiate_cache: InstantiateCache,
    instantiate_lparams_cache: InstantiateLParamsCache,
    recursor_major_cache: RecursorMajorCache,
    defer_recursor_major: bool,
}

impl<'a> TypeChecker<'a> {
    pub(crate) fn new(env: &'a Environment, lparams: &'a [Name], budget: Budget) -> Self {
        TypeChecker::new_with_safety(env, lparams, budget, DefinitionSafety::Safe)
    }

    pub(crate) fn new_with_safety(
        env: &'a Environment,
        lparams: &'a [Name],
        budget: Budget,
        safety: DefinitionSafety,
    ) -> Self {
        TypeChecker {
            env,
            lparams,
            locals: Vec::new(),
            local_positions: HashMap::new(),
            fresh: 0,
            next_local_generation: Some(1),
            budget,
            used: Consumption::default(),
            safety,
            infer_cache: ExprResultCache::new(),
            infer_only_cache: ExprResultCache::new(),
            whnf_core_cache: ExprResultCache::new(),
            whnf_cache: ExprResultCache::new(),
            positive_def_eq_cache: PositiveDefEqCache::new(),
            instantiate_cache: InstantiateCache::new(),
            instantiate_lparams_cache: InstantiateLParamsCache::new(),
            recursor_major_cache: RecursorMajorCache::new(),
            defer_recursor_major: false,
        }
    }

    /// Adopt an externally-created local (the admission engine's telescopes,
    /// bead franken_lean-ap6) so `infer`/`whnf`/`def_eq` resolve its fvar.
    pub(crate) fn adopt_local(&mut self, id: FVarId, type_: Expr) {
        self.push_local(id, type_, None);
    }

    pub(crate) fn consumption(&self) -> Consumption {
        self.used
    }

    /// Crate-facing whnf (the admission path's sort checks).
    pub(crate) fn whnf_public(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.whnf(e, depth)
    }

    /// Crate-facing defeq (admission bodies and the standalone query surface).
    pub(crate) fn def_eq_public(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        self.is_def_eq(t, s, depth)
    }

    /// The counted hook (KR-400..403): every step charges; depth checks precede
    /// every descent.
    fn step(&mut self, depth: u32) -> KResult<()> {
        self.used.steps_used += 1;
        self.used.max_depth = self.used.max_depth.max(depth);
        if self.used.steps_used > self.budget.steps {
            return Err(Stop::Exhausted(ExhaustionReason::Steps));
        }
        if depth > self.budget.depth {
            return Err(Stop::Exhausted(ExhaustionReason::Depth));
        }
        Ok(())
    }

    fn fresh_fvar(&mut self, type_: Expr, value: Option<Expr>) -> FVarId {
        self.fresh += 1;
        let id = FVarId(Name::num(
            Name::str(Name::anonymous(), "_kernel"),
            self.fresh,
        ));
        self.push_local(id.clone(), type_, value);
        id
    }

    fn drop_local(&mut self) {
        let Some(local) = self.locals.pop() else {
            return;
        };
        if let Some(previous) = local.previous_same_id {
            self.local_positions.insert(local.id, previous);
        } else {
            self.local_positions.remove(&local.id);
        }
    }

    fn truncate_locals(&mut self, len: usize) {
        while self.locals.len() > len {
            self.drop_local();
        }
    }

    fn find_local(&self, id: &FVarId) -> Option<&LocalDecl> {
        self.local_positions
            .get(id)
            .and_then(|position| self.locals.get(*position))
    }

    fn take_local_generation(&mut self) -> Option<u64> {
        let generation = self.next_local_generation?;
        self.next_local_generation = generation.checked_add(1);
        Some(generation)
    }

    fn push_local(&mut self, id: FVarId, type_: Expr, value: Option<Expr>) {
        let generation = self.take_local_generation();
        let previous_same_id = self.local_positions.insert(id.clone(), self.locals.len());
        self.locals.push(LocalDecl {
            id,
            previous_same_id,
            generation,
            type_,
            value,
        });
    }

    // ---- de Bruijn machinery -----------------------------------------------------------

    /// Replace loose `bvar k` by `subst` (which must be closed w.r.t. bvars, as all
    /// kernel substitution values here are: fvars or closed terms), decrementing
    /// looser indices. Flag-pruned: subtrees without loose bvars ≥ k are shared.
    pub(crate) fn instantiate(
        &mut self,
        e: &Expr,
        k: u32,
        subst: &Expr,
        depth: u32,
    ) -> KResult<Expr> {
        self.step(depth)?;
        if let Some(cached) = self.instantiate_cache.get(e, k, subst) {
            return Ok(cached);
        }
        if e.loose_bvar_range() <= k {
            return Ok(e.clone());
        }
        let result = match e.node() {
            ExprNode::BVar { idx } => {
                if *idx == k {
                    subst.clone()
                } else if *idx > k {
                    Expr::bvar(idx - 1).unwrap_or_else(|_| e.clone())
                } else {
                    e.clone()
                }
            }
            ExprNode::App { f, a } => {
                let f2 = self.instantiate(f, k, subst, depth + 1)?;
                let a2 = self.instantiate(a, k, subst, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate(binder_type, k, subst, depth + 1)?;
                let b2 = self.instantiate(body, k + 1, subst, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate(binder_type, k, subst, depth + 1)?;
                let b2 = self.instantiate(body, k + 1, subst, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.instantiate(type_, k, subst, depth + 1)?;
                let v2 = self.instantiate(value, k, subst, depth + 1)?;
                let b2 = self.instantiate(body, k + 1, subst, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.instantiate(expr, k, subst, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.instantiate(expr, k, subst, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            // Range-0 kinds are unreachable here thanks to the pruning guard.
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => e.clone(),
        };
        if result != *e {
            self.instantiate_cache
                .insert(e.clone(), k, subst.clone(), result.clone());
        }
        Ok(result)
    }

    /// Instantiate a binder body with an fvar (the standard descent move).
    fn open_binder(&mut self, body: &Expr, id: &FVarId, depth: u32) -> KResult<Expr> {
        let fv = Expr::fvar(id.clone());
        self.instantiate(body, 0, &fv, depth)
    }

    /// Pin `instantiate_rev(e, values)`: simultaneously consume an outer
    /// binder telescope. Values are stored outermost-to-innermost, so bvar 0
    /// receives the last value. The same primitive opens binders with fvars
    /// and performs batched beta-reduction without repeated body traversals.
    fn instantiate_rev(
        &mut self,
        e: &Expr,
        fvars: &[Expr],
        bound: u32,
        depth: u32,
    ) -> KResult<Expr> {
        let mut cache = InstantiateRevCache::new();
        self.instantiate_rev_cached(e, fvars, bound, depth, &mut cache)
    }

    fn instantiate_rev_cached(
        &mut self,
        e: &Expr,
        fvars: &[Expr],
        bound: u32,
        depth: u32,
        cache: &mut InstantiateRevCache,
    ) -> KResult<Expr> {
        self.step(depth)?;
        if let Some(cached) = cache.get(e, bound) {
            return Ok(cached);
        }
        if e.loose_bvar_range() <= bound || fvars.is_empty() {
            return Ok(e.clone());
        }
        let count =
            u32::try_from(fvars.len()).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
        let result = match e.node() {
            ExprNode::BVar { idx } if *idx >= bound => {
                let relative = *idx - bound;
                if relative < count {
                    fvars[(count - 1 - relative) as usize].clone()
                } else {
                    Expr::bvar(idx - count).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
                }
            }
            ExprNode::BVar { .. } => e.clone(),
            ExprNode::App { f, a } => Expr::app(
                self.instantiate_rev_cached(f, fvars, bound, depth + 1, cache)?,
                self.instantiate_rev_cached(a, fvars, bound, depth + 1, cache)?,
            ),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                self.instantiate_rev_cached(binder_type, fvars, bound, depth + 1, cache)?,
                self.instantiate_rev_cached(body, fvars, bound + 1, depth + 1, cache)?,
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                self.instantiate_rev_cached(binder_type, fvars, bound, depth + 1, cache)?,
                self.instantiate_rev_cached(body, fvars, bound + 1, depth + 1, cache)?,
                *binder_info,
            ),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => Expr::let_e(
                decl_name.clone(),
                self.instantiate_rev_cached(type_, fvars, bound, depth + 1, cache)?,
                self.instantiate_rev_cached(value, fvars, bound, depth + 1, cache)?,
                self.instantiate_rev_cached(body, fvars, bound + 1, depth + 1, cache)?,
                *non_dep,
            ),
            ExprNode::MData { data, expr } => Expr::mdata(
                data.clone(),
                self.instantiate_rev_cached(expr, fvars, bound, depth + 1, cache)?,
            ),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(
                struct_name.clone(),
                *idx,
                self.instantiate_rev_cached(expr, fvars, bound, depth + 1, cache)?,
            ),
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => e.clone(),
        };
        cache.insert(e.clone(), bound, result.clone());
        Ok(result)
    }

    /// Substitute declared level parameters by concrete levels throughout a type
    /// (KR-105). Flag-pruned on has-level-param. `pub(crate)`: the nested-inductive
    /// translation (admit.rs, KR-608) instantiates copied specs at the nested
    /// occurrence's levels with the same budgeted walk.
    pub(crate) fn instantiate_lparams(
        &mut self,
        e: &Expr,
        params: &[Name],
        levels: &[Level],
        depth: u32,
    ) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_level_param() {
            return Ok(e.clone());
        }
        if let Some(cached) = self.instantiate_lparams_cache.get(e, params, levels) {
            return Ok(cached);
        }
        let subst_level = |l: &Level| -> Level { substitute_level(l, params, levels) };
        let result = match e.node() {
            ExprNode::Sort { level } => Expr::sort(subst_level(level)),
            ExprNode::Const { name, levels: ls } => {
                Expr::const_(name.clone(), ls.iter().map(subst_level).collect())
            }
            ExprNode::App { f, a } => {
                let f2 = self.instantiate_lparams(f, params, levels, depth + 1)?;
                let a2 = self.instantiate_lparams(a, params, levels, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate_lparams(binder_type, params, levels, depth + 1)?;
                let b2 = self.instantiate_lparams(body, params, levels, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate_lparams(binder_type, params, levels, depth + 1)?;
                let b2 = self.instantiate_lparams(body, params, levels, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.instantiate_lparams(type_, params, levels, depth + 1)?;
                let v2 = self.instantiate_lparams(value, params, levels, depth + 1)?;
                let b2 = self.instantiate_lparams(body, params, levels, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.instantiate_lparams(expr, params, levels, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.instantiate_lparams(expr, params, levels, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            _ => e.clone(),
        };
        if result != *e {
            self.instantiate_lparams_cache
                .insert(e.clone(), params, levels, result.clone());
        }
        Ok(result)
    }

    // ---- whnf (KR-200..204) ------------------------------------------------------------

    /// KR-200: whnf-core then delta, looped to a fixpoint — with KR-313 literal
    /// arithmetic (`reduce_nat`) tried on every whnf-core'd form before delta,
    /// exactly the pin's loop order (type_checker.cpp:663). `reduce_native`
    /// (`Lean.reduceBool`/`Lean.reduceNat`) is the native_decide surface, a
    /// follow-up slice: its absence leaves those applications stuck —
    /// under-acceptance, never over-acceptance.
    fn whnf(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        if let Some(cached) = self.whnf_cache.get(e, &self.locals, &self.local_positions) {
            return Ok(cached);
        }
        let mut current = self.whnf_core(e, depth)?;
        let result = loop {
            if let Some(value) = self.reduce_nat(&current, depth)? {
                break value;
            }
            match self.unfold_definition(&current, depth)? {
                Some(next) => current = self.whnf_core(&next, depth)?,
                None => break current,
            }
        };
        self.whnf_cache.insert(
            e.clone(),
            result.clone(),
            &self.locals,
            &self.local_positions,
        );
        Ok(result)
    }

    /// KR-201..204: mdata, beta (batched), zeta (let + let-fvar), proj.
    fn whnf_core(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        if let Some(cached) = self
            .whnf_core_cache
            .get(e, &self.locals, &self.local_positions)
        {
            return Ok(cached);
        }
        let result = match e.node() {
            ExprNode::MData { expr, .. } => self.whnf_core(expr, depth + 1)?,
            ExprNode::FVar { id } => match self.find_local(id).and_then(|d| d.value.clone()) {
                // KR-203: a let-bound fvar unfolds to its value.
                Some(value) => self.whnf_core(&value, depth + 1)?,
                None => e.clone(),
            },
            ExprNode::LetE { value, body, .. } => {
                // KR-203 zeta.
                let value = value.clone();
                let body = body.clone();
                let reduced = self.instantiate(&body, 0, &value, depth + 1)?;
                self.whnf_core(&reduced, depth + 1)?
            }
            ExprNode::App { .. } => {
                // Collect the spine, whnf the head, then KR-202 batched beta.
                let (head0, args) = app_spine(e);
                let head = self.whnf_core(&head0, depth + 1)?;
                if matches!(head.node(), ExprNode::Lam { .. }) {
                    let mut body = head;
                    let mut consumed = 0usize;
                    while consumed < args.len() {
                        self.step(depth)?;
                        let ExprNode::Lam {
                            body: next_body, ..
                        } = body.node()
                        else {
                            break;
                        };
                        body = next_body.clone();
                        consumed += 1;
                    }
                    let mut current =
                        self.instantiate_rev(&body, &args[..consumed], 0, depth + 1)?;
                    for arg in &args[consumed..] {
                        current = Expr::app(current, arg.clone());
                    }
                    self.whnf_core(&current, depth + 1)?
                } else if head == head0 {
                    // KR-205: the head is stable — try quotient computation, then
                    // inductive iota, on the original application.
                    match self.reduce_recursor(e, depth + 1)? {
                        Some(reduced) => self.whnf_core(&reduced, depth + 1)?,
                        None => e.clone(),
                    }
                } else {
                    // The head changed (let-fvar zeta, mdata strip): rebuild and
                    // continue, as the pin re-enters whnf_core on the update.
                    let mut rebuilt = head;
                    for arg in args {
                        rebuilt = Expr::app(rebuilt, arg);
                    }
                    self.whnf_core(&rebuilt, depth + 1)?
                }
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                // KR-204: projection of a constructor application.
                let struct_name = struct_name.clone();
                let idx = *idx;
                let scrutinee = self.whnf(&expr.clone(), depth + 1)?;
                // KR-314 (pin reduce_proj_core, type_checker.cpp:358): a
                // String-literal scrutinee expands to its constructor spine
                // (whnf'd so `String.ofList` unfolds to the real constructor)
                // before field extraction.
                let scrutinee = if let ExprNode::Lit {
                    literal: Literal::Str(value),
                } = scrutinee.node()
                {
                    let expanded = string_lit_to_constructor(value);
                    self.whnf(&expanded, depth + 1)?
                } else {
                    scrutinee
                };
                match self.reduce_proj(&struct_name, idx, &scrutinee) {
                    Some(field) => self.whnf_core(&field, depth + 1)?,
                    None => Expr::proj(struct_name, idx, scrutinee),
                }
            }
            _ => e.clone(),
        };
        // The explicit recursor continuation may retry an outer application
        // after normalizing a newly exposed nested major. A completed stuck
        // application is therefore useful information: without retaining the
        // identity result, every retry re-walks the same stable prefix. Easy
        // leaves remain uncached, and an interrupted/deferred computation
        // never reaches this insertion point.
        let cache_identity = matches!(
            e.node(),
            ExprNode::App { .. } | ExprNode::LetE { .. } | ExprNode::Proj { .. }
        );
        if result != *e || cache_identity {
            self.whnf_core_cache.insert(
                e.clone(),
                result.clone(),
                &self.locals,
                &self.local_positions,
            );
        }
        Ok(result)
    }

    /// KR-204's constructor recognition: `proj I idx (mk params fields)`.
    fn reduce_proj(&self, _struct_name: &Name, idx: u64, scrutinee: &Expr) -> Option<Expr> {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = scrutinee;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        let ConstantInfo::Ctor(ctor) = self.env.find(name)? else {
            return None;
        };
        let field_index = usize::try_from(ctor.num_params as u64 + idx).ok()?;
        args.get(field_index).map(|e| (*e).clone())
    }

    /// Delta (whnf layer, KR-200): unfold a safe definition at the application head.
    /// Slice note: theorems and opaques are NOT unfolded here (proof irrelevance
    /// covers theorem bodies; opaque unfolding is a follow-up refinement) — an
    /// under-unfolding can only under-accept, never over-accept.
    fn unfold_definition(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        let mut args: Vec<Expr> = Vec::new();
        let mut head = e.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(defn)) = self.env.find(name) else {
            return Ok(None);
        };
        if defn.safety != DefinitionSafety::Safe {
            return Ok(None);
        }
        let value = defn.value.clone();
        let params = defn.base.level_params.clone();
        let levels = levels.clone();
        let mut unfolded = self.instantiate_lparams(&value, &params, &levels, depth + 1)?;
        for arg in args {
            unfolded = Expr::app(unfolded, arg);
        }
        Ok(Some(unfolded))
    }

    fn definition_height(&self, e: &Expr) -> Option<u32> {
        let mut head = e;
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        match self.env.find(name)? {
            ConstantInfo::Defn(d) if d.safety == DefinitionSafety::Safe => {
                Some(match d.hints {
                    ReducibilityHints::Regular(h) => h,
                    // Abbrev unfolds eagerly (treated as tall); Opaque as height 0.
                    ReducibilityHints::Abbrev => u32::MAX,
                    ReducibilityHints::Opaque => 0,
                })
            }
            _ => None,
        }
    }

    /// Bulk budget charge for literal arithmetic whose result size is bounded in
    /// advance: a computation whose OUTPUT would dwarf the step budget converts
    /// to typed exhaustion BEFORE any allocation (FL-INV-07) — where the pin
    /// simply grinds or exhausts memory (Behavior Note on franken_lean-irm).
    fn charge_bulk(&mut self, units: u64) -> KResult<()> {
        self.used.steps_used = self.used.steps_used.saturating_add(units);
        if self.used.steps_used > self.budget.steps {
            return Err(Stop::Exhausted(ExhaustionReason::Steps));
        }
        Ok(())
    }

    /// KR-313 (`reduce_nat`, pin type_checker.cpp:609): literal Nat arithmetic.
    /// `Nat.succ` at one argument; at two, the pin's exact table — add sub mul
    /// pow gcd mod div beq ble land lor xor shiftLeft shiftRight (divergence
    /// note, pinned by test: no `Nat.blt` at this pin). Arguments are whnf'd and
    /// accepted when literal or `Nat.zero` (`is_nat_lit_ext`); `pow` refuses
    /// exponents above 2^24 (`ReducePowMaxExp`) exactly as the pin does;
    /// `beq`/`ble` produce `Bool.true`/`Bool.false`. All arithmetic is
    /// fln-bignum; results re-enter the term plane loss-free via interop.
    fn reduce_nat(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        const REDUCE_POW_MAX_EXP: u64 = 1 << 24;
        let (head, args) = app_spine(e);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        let Some(op) = nat_op_leaf(name) else {
            return Ok(None);
        };
        if args.len() == 1 {
            if op != "succ" {
                return Ok(None);
            }
            let arg = self.whnf(&args[0], depth + 1)?;
            let Some(value) = nat_lit_ext_value(&arg) else {
                return Ok(None);
            };
            return Ok(Some(nat_lit_expr(&value.add(&BigNat::from_u64(1)))));
        }
        if args.len() != 2
            || !matches!(
                op,
                "add"
                    | "sub"
                    | "mul"
                    | "pow"
                    | "gcd"
                    | "mod"
                    | "div"
                    | "beq"
                    | "ble"
                    | "land"
                    | "lor"
                    | "xor"
                    | "shiftLeft"
                    | "shiftRight"
            )
        {
            return Ok(None);
        }
        let a = self.whnf(&args[0], depth + 1)?;
        let Some(va) = nat_lit_ext_value(&a) else {
            return Ok(None);
        };
        let b = self.whnf(&args[1], depth + 1)?;
        let Some(vb) = nat_lit_ext_value(&b) else {
            return Ok(None);
        };
        // Operand-proportional charge: the operands came from the term, so this
        // is linear in input; result-proportional charges follow per op.
        let limbs_a = va.limbs_le().len() as u64;
        let limbs_b = vb.limbs_le().len() as u64;
        self.charge_bulk(1 + limbs_a + limbs_b)?;
        let result = match op {
            "add" => va.add(&vb),
            "sub" => va.sub(&vb),
            "mul" => va.mul(&vb),
            "pow" => {
                // Pin cap first (exponents above it leave the term stuck) …
                match vb.to_u64() {
                    Some(exp) if exp <= REDUCE_POW_MAX_EXP => {
                        // … then a result-size charge: ~bit_length(a)·exp bits.
                        let result_limbs = (u128::from(va.bit_length()) * u128::from(exp) / 64)
                            .try_into()
                            .unwrap_or(u64::MAX);
                        self.charge_bulk(result_limbs)?;
                        va.pow(u32::try_from(exp).unwrap_or(u32::MAX))
                    }
                    _ => return Ok(None),
                }
            }
            "gcd" => va.gcd(&vb),
            "mod" => va.rem(&vb),
            "div" => va.div(&vb),
            "beq" => return Ok(Some(bool_const_expr(va.beq(&vb)))),
            "ble" => return Ok(Some(bool_const_expr(va.ble(&vb)))),
            "land" => va.land(&vb),
            "lor" => va.lor(&vb),
            "xor" => va.lxor(&vb),
            "shiftLeft" => {
                // Result size is input bits + shift count: charge it up front.
                let Some(count) = vb.to_u64() else {
                    // A shift count beyond u64 is beyond any feasible memory:
                    // charge the smallest representable over-budget forecast so
                    // the typed exhaustion carries genuine allowed/observed facts,
                    // never an attempted allocation or a fabricated completion.
                    self.used.steps_used = self.budget.steps.saturating_add(1);
                    return Err(Stop::Exhausted(ExhaustionReason::Steps));
                };
                self.charge_bulk(count / 64 + 1)?;
                va.shl(count)
            }
            "shiftRight" => match vb.to_u64() {
                Some(count) => va.shr(count),
                // Shifting right by more than u64::MAX zeroes any operand that
                // fits in memory.
                None => BigNat::zero(),
            },
            // The guard above closes the op list; a drift here degrades to
            // under-reduction (stuck term), never a panic or a wrong value.
            _ => return Ok(None),
        };
        Ok(Some(nat_lit_expr(&result)))
    }

    // ---- recursor reduction (KR-205/316/317/955) ---------------------------------------

    /// KR-205 (`reduce_recursor`): when an application head is stable, try
    /// quotient computation first, then inductive iota. `None` means no rule
    /// fires — the term is simply stuck, never an error.
    fn reduce_recursor(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        self.step(depth)?;
        if let Some(reduced) = self.quot_reduce_rec(e, depth)? {
            return Ok(Some(reduced));
        }
        self.inductive_reduce_rec(e, depth)
    }

    /// KR-955 (`quot_reduce_rec`): `Quot.lift f h (Quot.mk r a) ⟶ f a` (mk at
    /// argument 5, f at 3); `Quot.ind p (Quot.mk r a) ⟶ p a` (mk at 4, p at 3);
    /// trailing arguments preserved. Dispatch is by the head constant's
    /// environment kind (`QuotKind::Lift`/`Ind`, scrutinee head `QuotKind::Ctor`
    /// with exactly three arguments), so the lane is active exactly when
    /// quotients are initialized in this environment.
    fn quot_reduce_rec(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        let (head, args) = app_spine(e);
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let kind = match self.env.find(name) {
            Some(ConstantInfo::Quot(quot)) => quot.kind,
            _ => return Ok(None),
        };
        let (mk_pos, arg_pos) = match kind {
            QuotKind::Lift => (5usize, 3usize),
            QuotKind::Ind => (4, 3),
            QuotKind::Type | QuotKind::Ctor => return Ok(None),
        };
        if args.len() <= mk_pos {
            return Ok(None);
        }
        let mk = self.whnf(&args[mk_pos], depth + 1)?;
        let (mk_head, mk_args) = app_spine(&mk);
        let ExprNode::Const { name: mk_name, .. } = mk_head.node() else {
            return Ok(None);
        };
        let mk_is_quot_ctor = matches!(
            self.env.find(mk_name),
            Some(ConstantInfo::Quot(quot)) if quot.kind == QuotKind::Ctor
        );
        if !mk_is_quot_ctor || mk_args.len() != 3 {
            return Ok(None);
        }
        // `Quot.mk r a`'s last argument is the underlying element.
        let mut reduced = Expr::app(args[arg_pos].clone(), mk_args[2].clone());
        for extra in &args[mk_pos + 1..] {
            reduced = Expr::app(reduced, extra.clone());
        }
        Ok(Some(reduced))
    }

    /// KR-316 (`inductive_reduce_rec`): a recursor application fires when its
    /// major premise — at `nparams + nmotives + nminors + nindices` — reduces to
    /// a constructor of the right inductive, after K conversion (KR-317) and
    /// Nat-literal-to-constructor / structure-eta coercion. The matching rule's
    /// right-hand side is instantiated with the recursor's levels and applied to
    /// params+motives+minors from the recursor spine, the constructor's fields,
    /// and the trailing arguments. Literal majors convert first: Nat via
    /// `nat_lit_to_constructor`, String via KR-314 expansion (inductive.h:93-95).
    fn inductive_reduce_rec(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        let Some((frame, major)) = self.prepare_inductive_reduction(e, depth)? else {
            return Ok(None);
        };
        if self.defer_recursor_major {
            return Err(Stop::DeferredRecursor {
                frame: Box::new(frame),
                major,
            });
        }
        let major = self.whnf_recursor_chain(&major, depth + 1)?;
        self.finish_inductive_reduction(&frame, major, depth)
    }

    fn prepare_inductive_reduction(
        &mut self,
        e: &Expr,
        depth: u32,
    ) -> KResult<Option<(InductiveReductionFrame, Expr)>> {
        let (head, rec_args) = app_spine(e);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(rec)) = self.env.find(name) else {
            return Ok(None);
        };
        let rec = rec.clone();
        let levels = levels.clone();
        let major_idx =
            (rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices) as usize;
        if rec_args.len() <= major_idx {
            return Ok(None);
        }
        let mut major = rec_args[major_idx].clone();
        if rec.k {
            major = self.major_to_cnstr_when_k(&rec, &major, depth)?;
        }
        Ok(Some((
            InductiveReductionFrame {
                original: e.clone(),
                rec,
                levels,
                rec_args,
                major_idx,
            },
            major,
        )))
    }

    /// Normalize nested inductive-recursor majors with an explicit
    /// continuation stack. Reference `whnf` naturally recurses here; K1's
    /// resource contract measures native stack, so the same reduction chain
    /// must spend steps without growing host frames.
    fn whnf_recursor_chain(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        let mut continuations = Vec::new();
        let mut current = e.clone();
        loop {
            let mut normalized = if let Some(cached) =
                self.whnf_cache
                    .get(&current, &self.locals, &self.local_positions)
            {
                cached
            } else if let Some((frame, major)) =
                self.prepare_inductive_reduction(&current, depth)?
            {
                self.step(depth)?;
                continuations.push(WhnfRecursorContinuation::Finish(frame));
                current = major;
                continue;
            } else {
                let previous = self.defer_recursor_major;
                self.defer_recursor_major = true;
                let result = self.whnf(&current, depth);
                self.defer_recursor_major = previous;
                match result {
                    Ok(normalized) => normalized,
                    Err(Stop::DeferredRecursor { frame, major }) => {
                        continuations.push(WhnfRecursorContinuation::Retry(current.clone()));
                        continuations.push(WhnfRecursorContinuation::Finish(*frame));
                        current = major;
                        continue;
                    }
                    Err(stop) => return Err(stop),
                }
            };

            loop {
                match continuations.pop() {
                    Some(WhnfRecursorContinuation::Cache(origin)) => {
                        self.whnf_cache.insert(
                            origin.clone(),
                            normalized.clone(),
                            &self.locals,
                            &self.local_positions,
                        );
                        // A recursor is reduced from `whnf_core`. If its RHS
                        // reaches a stuck nested match, the enclosing retry
                        // re-enters through that same layer rather than through
                        // full `whnf`; publish the completed continuation to
                        // both tables or the predecessor reduction repeats
                        // indefinitely.
                        self.whnf_core_cache.insert(
                            origin,
                            normalized.clone(),
                            &self.locals,
                            &self.local_positions,
                        );
                    }
                    Some(WhnfRecursorContinuation::Retry(retry)) => {
                        current = retry;
                        break;
                    }
                    Some(WhnfRecursorContinuation::Finish(frame)) => {
                        match self.finish_inductive_reduction(&frame, normalized, depth)? {
                            Some(reduced) => {
                                continuations.push(WhnfRecursorContinuation::Cache(frame.original));
                                current = reduced;
                                break;
                            }
                            None => {
                                normalized = self.cache_stuck_recursor(frame.original);
                            }
                        }
                    }
                    None => return Ok(normalized),
                }
            }
        }
    }

    fn finish_inductive_reduction(
        &mut self,
        frame: &InductiveReductionFrame,
        mut major: Expr,
        depth: u32,
    ) -> KResult<Option<Expr>> {
        match major.node() {
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } => {
                major = nat_lit_to_constructor(value);
            }
            ExprNode::Lit {
                literal: Literal::Str(value),
            } => {
                // KR-314 (inductive.h:95): a String-literal major expands to its
                // constructor spine, whnf'd so `String.ofList` delta-unfolds to
                // the actual constructor application.
                major = self.whnf(&string_lit_to_constructor(value), depth + 1)?;
            }
            _ => major = self.major_to_cnstr_when_structure(&frame.rec, &major, depth)?,
        }
        let (major_head, major_args) = app_spine(&major);
        let ExprNode::Const {
            name: ctor_name, ..
        } = major_head.node()
        else {
            return Ok(None);
        };
        let Some(rule) = frame.rec.rules.iter().find(|rule| &rule.ctor == ctor_name) else {
            return Ok(None);
        };
        let nfields = rule.nfields as usize;
        if nfields > major_args.len() {
            return Ok(None);
        }
        if frame.levels.len() != frame.rec.base.level_params.len() {
            return Ok(None);
        }
        let mut rhs = self.instantiate_lparams(
            &rule.rhs,
            &frame.rec.base.level_params,
            &frame.levels,
            depth + 1,
        )?;
        // Params, motives, and minors come from the recursor application (the
        // indices are consumed by the motive, never applied to the rule).
        let from_rec =
            (frame.rec.num_params + frame.rec.num_motives + frame.rec.num_minors) as usize;
        for arg in frame.rec_args.iter().take(from_rec) {
            rhs = Expr::app(rhs, arg.clone());
        }
        // The constructor's parameter count can differ from the recursor's under
        // nested inductives: the fields are always the LAST `nfields` arguments.
        for field in &major_args[major_args.len() - nfields..] {
            rhs = Expr::app(rhs, field.clone());
        }
        for extra in &frame.rec_args[frame.major_idx + 1..] {
            rhs = Expr::app(rhs, extra.clone());
        }
        Ok(Some(rhs))
    }

    /// `recursor_val::get_major_induct` (declaration.cpp:145): walk `major_idx`
    /// binders of the recursor's type; the next binder's domain head names the
    /// inductive of the major premise.
    fn recursor_major_induct(&mut self, rec: &RecursorVal, depth: u32) -> KResult<Option<Name>> {
        if let Some(cached) = self.recursor_major_cache.get(&rec.base.name) {
            return Ok(cached);
        }
        let result = (|| {
            let major_idx = rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices;
            let mut telescope = rec.base.type_.clone();
            for _ in 0..major_idx {
                self.step(depth)?;
                let ExprNode::ForallE { body, .. } = telescope.node() else {
                    return Ok(None);
                };
                telescope = body.clone();
            }
            let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
                return Ok(None);
            };
            let (head, _) = app_spine(binder_type);
            match head.node() {
                ExprNode::Const { name, .. } => Ok(Some(name.clone())),
                _ => Ok(None),
            }
        })()?;
        self.recursor_major_cache
            .insert(rec.base.name.clone(), result.clone());
        Ok(result)
    }

    /// KR-317 (`to_cnstr_when_K`): a K-flagged recursor replaces any major
    /// premise whose (whnf'd, inferred) type has the recursor's inductive at its
    /// head with the nullary constructor of that type — gated on the constructed
    /// term's type being defeq to the major's. Any gate failure returns the
    /// original major unchanged (reduction without matching the syntactic proof).
    fn major_to_cnstr_when_k(
        &mut self,
        rec: &RecursorVal,
        major: &Expr,
        depth: u32,
    ) -> KResult<Expr> {
        let Some(major_induct) = self.recursor_major_induct(rec, depth)? else {
            return Ok(major.clone());
        };
        let app_type = match self.infer_only(major, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        let app_type = self.whnf(&app_type, depth + 1)?;
        let (type_head, type_args) = app_spine(&app_type);
        let ExprNode::Const {
            name: type_name,
            levels: type_levels,
        } = type_head.node()
        else {
            return Ok(major.clone());
        };
        if type_name != &major_induct {
            return Ok(major.clone());
        }
        // `mk_nullary_cnstr`: the FIRST constructor, applied to the type's params.
        let ctor_name = match self.env.find(type_name) {
            Some(ConstantInfo::Induct(ind)) => match ind.ctors.first() {
                Some(ctor_name) => ctor_name.clone(),
                None => return Ok(major.clone()),
            },
            _ => return Ok(major.clone()),
        };
        let mut new_ctor = Expr::const_(ctor_name, type_levels.clone());
        for arg in type_args.iter().take(rec.num_params as usize) {
            new_ctor = Expr::app(new_ctor, arg.clone());
        }
        let new_type = match self.infer_only(&new_ctor, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        if !self.is_def_eq(&app_type, &new_type, depth + 1)? {
            return Ok(major.clone());
        }
        Ok(new_ctor)
    }

    /// KR-316's structure-eta coercion (`to_cnstr_when_structure`): a major of a
    /// one-constructor, index-free, non-recursive, non-Prop structure type that
    /// is not already a constructor application becomes
    /// `mk params (proj 0 major) … (proj n-1 major)`. Any gate failure returns
    /// the original major unchanged.
    fn major_to_cnstr_when_structure(
        &mut self,
        rec: &RecursorVal,
        major: &Expr,
        depth: u32,
    ) -> KResult<Expr> {
        let Some(induct_name) = self.recursor_major_induct(rec, depth)? else {
            return Ok(major.clone());
        };
        if !self.is_non_rec_structure(&induct_name) {
            return Ok(major.clone());
        }
        let (major_head, _) = app_spine(major);
        if let ExprNode::Const { name, .. } = major_head.node()
            && matches!(self.env.find(name), Some(ConstantInfo::Ctor(_)))
        {
            return Ok(major.clone());
        }
        let e_type = match self.infer_only(major, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        let e_type = self.whnf(&e_type, depth + 1)?;
        let (type_head, type_args) = app_spine(&e_type);
        let ExprNode::Const {
            name: type_name,
            levels: type_levels,
        } = type_head.node()
        else {
            return Ok(major.clone());
        };
        if type_name != &induct_name {
            return Ok(major.clone());
        }
        // Prop-valued structures are excluded (proof irrelevance covers them).
        let type_sort = match self.infer_only(&e_type, depth) {
            Ok(sort) => sort,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        let type_sort = self.whnf(&type_sort, depth + 1)?;
        if matches!(type_sort.node(), ExprNode::Sort { level } if level.is_equiv(&Level::zero())) {
            return Ok(major.clone());
        }
        // `expand_eta_struct`: ctor params from the type, then one proj per field.
        let (ctor_name, ctor_num_params, num_fields) = {
            let ctor_name = match self.env.find(&induct_name) {
                Some(ConstantInfo::Induct(ind)) => match ind.ctors.first() {
                    Some(ctor_name) => ctor_name.clone(),
                    None => return Ok(major.clone()),
                },
                _ => return Ok(major.clone()),
            };
            match self.env.find(&ctor_name) {
                Some(ConstantInfo::Ctor(ctor)) => (
                    ctor_name,
                    ctor.num_params as usize,
                    u64::from(ctor.num_fields),
                ),
                _ => return Ok(major.clone()),
            }
        };
        let mut expanded = Expr::const_(ctor_name, type_levels.clone());
        for arg in type_args.iter().take(ctor_num_params) {
            expanded = Expr::app(expanded, arg.clone());
        }
        for i in 0..num_fields {
            expanded = Expr::app(expanded, Expr::proj(induct_name.clone(), i, major.clone()));
        }
        Ok(expanded)
    }

    // ---- defeq (KR-300..312 subset) ----------------------------------------------------

    /// KR-301/302/303 — the decisive head rules, extracted so they can re-run
    /// on the REDUCED pair after every reduction stage (the pin re-runs its
    /// quick check after whnf_core and inside every lazy-delta iteration; a
    /// pair that only becomes Sort ≟ Sort or binder ≟ binder after reduction
    /// must not fall through to rules that cannot decide it). `None` = this
    /// pair's heads are not covered here — continue down the ladder.
    fn quick_def_eq_rules(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<Option<bool>> {
        // KR-301 positive equivalence cache, then quick structural equality
        // (data-word fast path inside Expr::eq).
        if self
            .positive_def_eq_cache
            .contains(t, s, &self.locals, &self.local_positions)
        {
            return Ok(Some(true));
        }
        if t == s {
            return Ok(Some(true));
        }
        // KR-301's literal half (pin quick_is_def_eq, Lit case): a literal pair
        // decides by value — and DECISIVELY, since two distinct literals are
        // both normal forms no later rule can equate.
        if let (ExprNode::Lit { literal: l1 }, ExprNode::Lit { literal: l2 }) = (t.node(), s.node())
        {
            return Ok(Some(l1 == l2));
        }
        // KR-303 sorts by level equivalence.
        if let (ExprNode::Sort { level: lt }, ExprNode::Sort { level: ls }) = (t.node(), s.node()) {
            return Ok(Some(lt.is_equiv(ls)));
        }
        // KR-302 binder congruence.
        match (t.node(), s.node()) {
            (
                ExprNode::Lam {
                    binder_type: t1,
                    body: b1,
                    ..
                },
                ExprNode::Lam {
                    binder_type: t2,
                    body: b2,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: t1,
                    body: b1,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: t2,
                    body: b2,
                    ..
                },
            ) => {
                let (t1, b1, t2, b2) = (t1.clone(), b1.clone(), t2.clone(), b2.clone());
                if !self.is_def_eq(&t1, &t2, depth + 1)? {
                    return Ok(Some(false));
                }
                let id = self.fresh_fvar(t1, None);
                let ob1 = self.open_binder(&b1, &id, depth + 1)?;
                let ob2 = self.open_binder(&b2, &id, depth + 1)?;
                let result = self.is_def_eq(&ob1, &ob2, depth + 1);
                self.drop_local();
                Ok(Some(result?))
            }
            _ => Ok(None),
        }
    }

    fn is_def_eq(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let result = self.is_def_eq_core(t, s, depth);
        if matches!(result, Ok(true)) {
            self.positive_def_eq_cache.insert(
                t.clone(),
                s.clone(),
                &self.locals,
                &self.local_positions,
            );
        }
        result
    }

    fn is_def_eq_core(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        self.step(depth)?; // KR-300 resource hook
        if let Some(decided) = self.quick_def_eq_rules(t, s, depth)? {
            return Ok(decided);
        }
        // KR-313's reflection fast path (pin type_checker.cpp:1062): `t` closed
        // and `s` literally `Bool.true` — fully reduce `t` and compare. This is
        // how `decide`-style proofs (`Eq.refl true : decide p = true`) close.
        // One-sided at the pin; the symmetric case still closes through delta.
        if !t.has_fvar()
            && matches!(s.node(), ExprNode::Const { name, .. } if is_name2(name, "Bool", "true"))
        {
            let reduced = self.whnf(t, depth + 1)?;
            if matches!(reduced.node(), ExprNode::Const { name, .. } if is_name2(name, "Bool", "true"))
            {
                return Ok(true);
            }
        }
        // KR-305: normalize both sides without delta, then RE-RUN the head
        // rules on the reduced pair (beta/zeta/iota can expose Sort or binder
        // heads whose levels are equivalent but not structurally equal).
        let tn = self.whnf_core(t, depth + 1)?;
        let sn = self.whnf_core(s, depth + 1)?;
        if (tn != *t || sn != *s)
            && let Some(decided) = self.quick_def_eq_rules(&tn, &sn, depth)?
        {
            return Ok(decided);
        }
        // KR-306 definitional proof irrelevance in Prop.
        if self.proof_irrel_eq(&tn, &sn, depth + 1)? {
            return Ok(true);
        }
        // KR-307/309 lazy delta by definitional height — with the KR-313 offset
        // and literal-arithmetic machinery woven into every iteration, as at
        // the pin — then the head rules once more: delta is exactly how an
        // abbrev (`outParam`, `ReaderT`, `Not`) exposes its Sort or Π structure.
        let (tn, sn) = match self.lazy_delta(tn, sn, depth + 1)? {
            LazyDelta::Decided(decided) => return Ok(decided),
            LazyDelta::Stuck(t, s) => (t, s),
        };
        if let Some(decided) = self.quick_def_eq_rules(&tn, &sn, depth)? {
            return Ok(decided);
        }
        // KR-310: same-name constants with equivalent levels.
        if let (
            ExprNode::Const {
                name: n1,
                levels: l1,
            },
            ExprNode::Const {
                name: n2,
                levels: l2,
            },
        ) = (tn.node(), sn.node())
            && n1 == n2
            && l1.len() == l2.len()
            && l1.iter().zip(l2).all(|(a, b)| a.is_equiv(b))
        {
            return Ok(true);
        }
        // KR-310's projection half (pin is_def_eq_core:1101 via
        // lazy_delta_proj_reduction): same-index projections close on defeq
        // scrutinees. Not decisive on failure — the pin falls through to the
        // rest of the ladder. (Our whnf_core reduces projections with full
        // whnf, so the pin's deferred-projection retry is already spent by the
        // time a Proj pair is stuck here — both scrutinees are maximally
        // reduced non-constructors, e.g. recursors stuck on a free variable.)
        if let (
            ExprNode::Proj {
                idx: i1, expr: e1, ..
            },
            ExprNode::Proj {
                idx: i2, expr: e2, ..
            },
        ) = (tn.node(), sn.node())
            && i1 == i2
        {
            let (e1, e2) = (e1.clone(), e2.clone());
            if self.is_def_eq(&e1, &e2, depth + 1)? {
                return Ok(true);
            }
        }
        // KR-311 application congruence.
        if let (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) =
            (tn.node(), sn.node())
        {
            let (f1, a1, f2, a2) = (f1.clone(), a1.clone(), f2.clone(), a2.clone());
            if self.is_def_eq(&f1, &f2, depth + 1)? && self.is_def_eq(&a1, &a2, depth + 1)? {
                return Ok(true);
            }
        }
        // KR-312 function eta, both directions.
        if self.try_eta(&tn, &sn, depth + 1)? || self.try_eta(&sn, &tn, depth + 1)? {
            return Ok(true);
        }
        // KR-903 structure eta, both directions (pin: try_eta_struct).
        if self.try_eta_struct(&tn, &sn, depth + 1)? || self.try_eta_struct(&sn, &tn, depth + 1)? {
            return Ok(true);
        }
        // KR-314 defeq half (pin try_string_lit_expansion, type_checker.cpp:1030):
        // a String literal against a `String.ofList _` spine — decisive when the
        // shape matches, either side.
        if let Some(decided) = self.try_string_lit_expansion(&tn, &sn, depth + 1)? {
            return Ok(decided);
        }
        // KR-315 unit-like structures (pin: is_def_eq_unit_like, one-sided).
        if self.is_def_eq_unit_like(&tn, &sn, depth + 1)? {
            return Ok(true);
        }
        Ok(false)
    }

    /// Is `name` a one-constructor, index-free, non-recursive structure?
    /// (pin: `is_non_rec_structure`, inductive.cpp:27.)
    fn is_non_rec_structure(&self, name: &Name) -> bool {
        matches!(
            self.env.find(name),
            Some(ConstantInfo::Induct(ind))
                if ind.ctors.len() == 1 && ind.num_indices == 0 && !ind.is_rec
        )
    }

    /// KR-903 (`try_eta_struct_core`): `t ≟ mk as fs` for a one-constructor,
    /// index-free, non-recursive structure holds when the types agree and
    /// every field `fᵢ` of `s` is defeq to `t.i`. The type-agreement gate is
    /// load-bearing: without it a zero-field constructor would equate values
    /// of DIFFERENT unit-like types.
    fn try_eta_struct(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        self.step(depth)?;
        let (s_head, s_args) = app_spine(s);
        let ExprNode::Const {
            name: ctor_name, ..
        } = s_head.node()
        else {
            return Ok(false);
        };
        let (induct, num_params, num_fields) = match self.env.find(ctor_name) {
            Some(ConstantInfo::Ctor(ctor)) => (
                ctor.induct.clone(),
                ctor.num_params as usize,
                ctor.num_fields as usize,
            ),
            _ => return Ok(false),
        };
        if s_args.len() != num_params + num_fields || !self.is_non_rec_structure(&induct) {
            return Ok(false);
        }
        let t_type = match self.infer_only(t, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        let s_type = match self.infer_only(s, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        if !self.is_def_eq(&t_type, &s_type, depth + 1)? {
            return Ok(false);
        }
        for (i, field) in s_args.iter().enumerate().skip(num_params) {
            let projected = Expr::proj(induct.clone(), (i - num_params) as u64, t.clone());
            if !self.is_def_eq(&projected, field, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// KR-315 (`is_def_eq_unit_like`): two terms of the same one-constructor,
    /// ZERO-field structure type are defeq when their types are. One-sided,
    /// as at the pin — full whnf of `t`'s type unfolds any abbrev first.
    fn is_def_eq_unit_like(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let t_type = match self.infer_only(t, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        let t_type = self.whnf(&t_type, depth + 1)?;
        let (type_head, _) = app_spine(&t_type);
        let ExprNode::Const { name, .. } = type_head.node() else {
            return Ok(false);
        };
        if !self.is_non_rec_structure(name) {
            return Ok(false);
        }
        let zero_fields = match self.env.find(name) {
            Some(ConstantInfo::Induct(ind)) => match ind.ctors.first() {
                Some(ctor_name) => matches!(
                    self.env.find(ctor_name),
                    Some(ConstantInfo::Ctor(ctor)) if ctor.num_fields == 0
                ),
                None => false,
            },
            _ => false,
        };
        if !zero_fields {
            return Ok(false);
        }
        let s_type = match self.infer_only(s, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        self.is_def_eq(&t_type, &s_type, depth + 1)
    }

    /// KR-306: if `t`'s type is a Prop, t ≟ s reduces to type-defeq.
    fn proof_irrel_eq(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let t_type = match self.infer_only(t, depth) {
            Ok(ty) => ty,
            // A term that fails to type here cannot claim irrelevance; let the
            // main ladder produce the real verdict.
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        if !self.is_prop(&t_type, depth)? {
            return Ok(false);
        }
        let s_type = match self.infer_only(s, depth) {
            Ok(ty) => ty,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        self.is_def_eq(&t_type, &s_type, depth)
    }

    /// Is `type_` a proposition — i.e., does it live in `Sort 0`? (The pin's
    /// `is_prop(e)` = `whnf(infer_type(e)) == Prop`.)
    fn is_prop(&mut self, type_: &Expr, depth: u32) -> KResult<bool> {
        let sort = self.infer_only_core(type_, depth)?;
        let sort = self.whnf(&sort, depth)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.is_equiv(&Level::zero())))
    }

    /// KR-309: unfold the taller definition first; equal heights unfold both —
    /// with the pin's per-iteration literal machinery (`lazy_delta_reduction`,
    /// type_checker.cpp:973): the KR-313 offset check and, on closed pairs,
    /// literal arithmetic on either side run BEFORE every unfold step, so a
    /// side that delta-exposes a literal (the decoded `OfNat.ofNat … ≟
    /// Nat.zero` residual family) decides here instead of falling through.
    fn lazy_delta(&mut self, mut t: Expr, mut s: Expr, depth: u32) -> KResult<LazyDelta> {
        loop {
            self.step(depth)?;
            if let Some(decided) = self.is_def_eq_offset(&t, &s, depth)? {
                return Ok(LazyDelta::Decided(decided));
            }
            if !t.has_fvar() && !s.has_fvar() {
                if let Some(value) = self.reduce_nat(&t, depth)? {
                    return Ok(LazyDelta::Decided(self.is_def_eq(&value, &s, depth + 1)?));
                }
                if let Some(value) = self.reduce_nat(&s, depth)? {
                    return Ok(LazyDelta::Decided(self.is_def_eq(&t, &value, depth + 1)?));
                }
            }
            // (`reduce_native` would run here at the pin — native_decide
            // surface, follow-up slice; omission only under-reduces.)
            // Pin `lazy_delta_reduction_step`: before unfolding two
            // applications of the SAME regular definition, compare their
            // arguments. This is more than a micro-optimization. Class methods
            // such as `HMod.hMod` can have proof-producing implementations;
            // unfolding equal heads before noticing that only a closed numeric
            // argument differs turns a tiny congruence query into evaluation of
            // that proof program. A failed argument comparison is not
            // decisive: exactly as at the pin, lazy delta then continues with
            // the ordinary unfolding order.
            if self.regular_same_head_apps_def_eq(&t, &s, depth + 1)? {
                return Ok(LazyDelta::Decided(true));
            }
            let ht = self.definition_height(&t);
            let hs = self.definition_height(&s);
            match (ht, hs) {
                (None, None) => return Ok(LazyDelta::Stuck(t, s)),
                (Some(_), None) => match self.unfold_definition(&t, depth)? {
                    Some(next) => t = self.whnf_core(&next, depth)?,
                    None => return Ok(LazyDelta::Stuck(t, s)),
                },
                (None, Some(_)) => match self.unfold_definition(&s, depth)? {
                    Some(next) => s = self.whnf_core(&next, depth)?,
                    None => return Ok(LazyDelta::Stuck(t, s)),
                },
                (Some(a), Some(b)) => {
                    if a >= b {
                        match self.unfold_definition(&t, depth)? {
                            Some(next) => t = self.whnf_core(&next, depth)?,
                            None => return Ok(LazyDelta::Stuck(t, s)),
                        }
                    }
                    if b >= a {
                        match self.unfold_definition(&s, depth)? {
                            Some(next) => s = self.whnf_core(&next, depth)?,
                            None => return Ok(LazyDelta::Stuck(t, s)),
                        }
                    }
                    if t == s {
                        return Ok(LazyDelta::Stuck(t, s));
                    }
                }
            }
        }
    }

    /// The positive branch of the pin's equal-regular-definition shortcut.
    ///
    /// Requiring the same constant head makes every recursive query strictly
    /// smaller (arguments only), so this cannot re-enter on the original pair.
    /// Structural identity still decides cache hits elsewhere; the packed
    /// expression hash is never authority here.
    fn regular_same_head_apps_def_eq(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let (t_head, t_args) = app_spine(t);
        let (s_head, s_args) = app_spine(s);
        if t_args.is_empty() || t_args.len() != s_args.len() {
            return Ok(false);
        }
        let (
            ExprNode::Const {
                name: t_name,
                levels: t_levels,
            },
            ExprNode::Const {
                name: s_name,
                levels: s_levels,
            },
        ) = (t_head.node(), s_head.node())
        else {
            return Ok(false);
        };
        if t_name != s_name
            || t_levels.len() != s_levels.len()
            || !t_levels
                .iter()
                .zip(s_levels)
                .all(|(t_level, s_level)| t_level.is_equiv(s_level))
        {
            return Ok(false);
        }
        if !matches!(
            self.env.find(t_name),
            Some(ConstantInfo::Defn(defn))
                if defn.safety == DefinitionSafety::Safe
                    && matches!(defn.hints, ReducibilityHints::Regular(_))
        ) {
            return Ok(false);
        }
        for (t_arg, s_arg) in t_args.iter().zip(&s_args) {
            if !self.is_def_eq(t_arg, s_arg, depth)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `is_def_eq_offset` (pin type_checker.cpp:961): both sides Nat-zero
    /// (`Nat.zero` or literal `0`) — defeq; both `succ`-peelable (a positive
    /// literal peels to its predecessor literal, `Nat.succ x` peels to `x`) —
    /// defeq of the predecessors, decisively. `None`: not an offset pair.
    fn is_def_eq_offset(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<Option<bool>> {
        if is_nat_zero_expr(t) && is_nat_zero_expr(s) {
            return Ok(Some(true));
        }
        match (nat_succ_peel(t), nat_succ_peel(s)) {
            (Some(pt), Some(ps)) => Ok(Some(self.is_def_eq(&pt, &ps, depth + 1)?)),
            _ => Ok(None),
        }
    }

    /// KR-314 defeq half (`try_string_lit_expansion`, pin type_checker.cpp:1030):
    /// tries both orientations of literal-vs-`String.ofList` spine.
    fn try_string_lit_expansion(
        &mut self,
        t: &Expr,
        s: &Expr,
        depth: u32,
    ) -> KResult<Option<bool>> {
        if let Some(decided) = self.try_string_lit_expansion_core(t, s, depth)? {
            return Ok(Some(decided));
        }
        self.try_string_lit_expansion_core(s, t, depth)
    }

    /// One orientation: `t` a String literal, `s` exactly `String.ofList _`
    /// (a one-argument application of the levels-free constant, as the pin's
    /// whole-expression comparison against `g_string_mk` requires). Expands the
    /// literal (whnf'd, so `ofList` unfolds to the real constructor) and
    /// recurses; the answer is decisive.
    fn try_string_lit_expansion_core(
        &mut self,
        t: &Expr,
        s: &Expr,
        depth: u32,
    ) -> KResult<Option<bool>> {
        let ExprNode::Lit {
            literal: Literal::Str(value),
        } = t.node()
        else {
            return Ok(None);
        };
        let ExprNode::App { f, .. } = s.node() else {
            return Ok(None);
        };
        let ExprNode::Const { name, levels } = f.node() else {
            return Ok(None);
        };
        if !levels.is_empty() || !is_name2(name, "String", "ofList") {
            return Ok(None);
        }
        let expanded = self.whnf(&string_lit_to_constructor(value), depth + 1)?;
        Ok(Some(self.is_def_eq(&expanded, s, depth + 1)?))
    }

    /// KR-312 (function half): `t` a lambda, `s` not — eta-expand `s` through its
    /// Π-type and retry.
    fn try_eta(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        if !matches!(t.node(), ExprNode::Lam { .. }) || matches!(s.node(), ExprNode::Lam { .. }) {
            return Ok(false);
        }
        let s_type = match self.infer_only(s, depth) {
            Ok(ty) => ty,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        let s_type = self.whnf(&s_type, depth)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            ..
        } = s_type.node()
        else {
            return Ok(false);
        };
        let expanded = Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            Expr::app(s.clone(), Expr::bvar(0).unwrap_or_else(|_| s.clone())),
            *binder_info,
        );
        self.is_def_eq(t, &expanded, depth)
    }

    // ---- typing (KR-100..112) ----------------------------------------------------------

    pub(crate) fn infer(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.infer_entry(e, depth, InferMode::Check)
    }

    /// The pin's `infer_type`: compute the type without re-checking the term.
    /// Defeq, reduction, eta, and proof-irrelevance use this mode. Its cache is
    /// disjoint from checking mode because this path intentionally skips
    /// safety, universe-well-formedness, and argument-type obligations.
    fn infer_only(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.infer_entry(e, depth, InferMode::Only)
    }

    fn infer_entry(&mut self, e: &Expr, depth: u32, mode: InferMode) -> KResult<Expr> {
        self.step(depth)?;
        // KR-100: closed terms only.
        if e.has_loose_bvars() {
            return reject(
                RejectClass::LooseBVar,
                "kernel terms must be closed; replace loose bound variables with free variables",
            );
        }
        // KR-103: no metavariables.
        if e.has_expr_mvar() || e.has_level_mvar() {
            return reject(
                RejectClass::MVarInKernel,
                "kernel does not accept metavariables",
            );
        }
        self.infer_core_mode(e, depth, mode)
    }

    fn infer_core(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.infer_core_mode(e, depth, InferMode::Check)
    }

    fn infer_only_core(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.infer_core_mode(e, depth, InferMode::Only)
    }

    fn infer_core_mode(&mut self, e: &Expr, depth: u32, mode: InferMode) -> KResult<Expr> {
        self.step(depth)?;
        let cached = match mode {
            InferMode::Check => self.infer_cache.get(e, &self.locals, &self.local_positions),
            InferMode::Only => self
                .infer_only_cache
                .get(e, &self.locals, &self.local_positions),
        };
        if let Some(cached) = cached {
            return Ok(cached);
        }
        let result = match e.node() {
            // KR-101: unreachable given the closed-term precondition; still a typed
            // rejection, never a panic.
            ExprNode::BVar { .. } => reject(
                RejectClass::LooseBVar,
                "bound variable escaped the binder telescope",
            ),
            ExprNode::MVar { .. } => {
                reject(RejectClass::MVarInKernel, "metavariable in kernel term")
            }
            // KR-102.
            ExprNode::FVar { id } => match self.find_local(id) {
                Some(decl) => Ok(decl.type_.clone()),
                None => reject(RejectClass::UnknownFVar, "unknown free variable"),
            },
            // KR-104.
            ExprNode::Sort { level } => {
                if mode == InferMode::Check {
                    self.check_level(level)?;
                }
                Ok(Expr::sort(
                    level
                        .clone()
                        .succ()
                        .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?,
                ))
            }
            // KR-105.
            ExprNode::Const { name, levels } => {
                let Some(info) = self.env.find(name) else {
                    return reject(
                        RejectClass::UnknownConstant,
                        format!("unknown constant `{}`", name.to_display_string()),
                    );
                };
                let params = &info.constant_val().level_params;
                if params.len() != levels.len() {
                    return reject(
                        RejectClass::UniverseArityMismatch,
                        format!(
                            "`{}` expects {} universe level(s), given {}",
                            name.to_display_string(),
                            params.len(),
                            levels.len()
                        ),
                    );
                }
                if mode == InferMode::Check {
                    for level in levels {
                        self.check_level(level)?;
                    }
                    // KR-973 (pin type_checker.cpp:101/105): a non-unsafe
                    // checking context may not reference unsafe declarations,
                    // and a SAFE context may not reference partial
                    // definitions. Infer-only deliberately skips both.
                    if constant_is_unsafe(info) && self.safety != DefinitionSafety::Unsafe {
                        return reject(
                            RejectClass::SafetyViolation,
                            format!(
                                "declaration uses unsafe declaration `{}`",
                                name.to_display_string()
                            ),
                        );
                    }
                    if let ConstantInfo::Defn(d) = info
                        && d.safety == DefinitionSafety::Partial
                        && self.safety == DefinitionSafety::Safe
                    {
                        return reject(
                            RejectClass::SafetyViolation,
                            format!(
                                "safe declaration must not contain partial declaration `{}`",
                                name.to_display_string()
                            ),
                        );
                    }
                }
                let params = params.clone();
                let type_ = info.constant_val().type_.clone();
                let levels = levels.clone();
                self.instantiate_lparams(&type_, &params, &levels, depth + 1)
            }
            // KR-106. Both modes flatten the left-associated application
            // spine. Infer-only matches the pin directly; checking mode is the
            // same judgment expressed as a loop so adversarial arity consumes
            // steps instead of native stack.
            ExprNode::App { .. } => {
                let result = match mode {
                    InferMode::Check => self.infer_app_check(e, depth + 1),
                    InferMode::Only => self.infer_app_only(e, depth + 1),
                };
                if let Ok(inferred) = &result {
                    match mode {
                        InferMode::Check => self.infer_cache.insert(
                            e.clone(),
                            inferred.clone(),
                            &self.locals,
                            &self.local_positions,
                        ),
                        InferMode::Only => {
                            self.infer_only_cache.insert(
                                e.clone(),
                                inferred.clone(),
                                &self.locals,
                                &self.local_positions,
                            );
                        }
                    }
                }
                return result;
            }
            // KR-107.
            ExprNode::Lam { .. } => {
                let result = self.infer_lambda_spine(e, depth + 1, mode);
                if let Ok(inferred) = &result {
                    match mode {
                        InferMode::Check => self.infer_cache.insert(
                            e.clone(),
                            inferred.clone(),
                            &self.locals,
                            &self.local_positions,
                        ),
                        InferMode::Only => {
                            self.infer_only_cache.insert(
                                e.clone(),
                                inferred.clone(),
                                &self.locals,
                                &self.local_positions,
                            );
                        }
                    }
                }
                return result;
            }
            // KR-108: the imax rule.
            ExprNode::ForallE { .. } => {
                let result = self.infer_pi_spine(e, depth + 1, mode);
                if let Ok(inferred) = &result {
                    match mode {
                        InferMode::Check => self.infer_cache.insert(
                            e.clone(),
                            inferred.clone(),
                            &self.locals,
                            &self.local_positions,
                        ),
                        InferMode::Only => {
                            self.infer_only_cache.insert(
                                e.clone(),
                                inferred.clone(),
                                &self.locals,
                                &self.local_positions,
                            );
                        }
                    }
                }
                return result;
            }
            // KR-109.
            ExprNode::LetE { .. } => {
                let result = self.infer_let_spine(e, depth + 1, mode);
                if let Ok(inferred) = &result {
                    match mode {
                        InferMode::Check => self.infer_cache.insert(
                            e.clone(),
                            inferred.clone(),
                            &self.locals,
                            &self.local_positions,
                        ),
                        InferMode::Only => {
                            self.infer_only_cache.insert(
                                e.clone(),
                                inferred.clone(),
                                &self.locals,
                                &self.local_positions,
                            );
                        }
                    }
                }
                return result;
            }
            // KR-110.
            ExprNode::Lit { literal } => Ok(Expr::const_(
                Name::str(
                    Name::anonymous(),
                    match literal {
                        fln_core::expr::Literal::Nat(_) => "Nat",
                        fln_core::expr::Literal::Str(_) => "String",
                    },
                ),
                Vec::new(),
            )),
            // KR-111.
            ExprNode::MData { expr, .. } => {
                let expr = expr.clone();
                self.infer_core_mode(&expr, depth + 1, mode)
            }
            // KR-112 (+ KR-901 Prop guard).
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let (struct_name, idx, scrutinee) = (struct_name.clone(), *idx, expr.clone());
                self.infer_proj(&struct_name, idx, &scrutinee, depth + 1, mode)
            }
        };
        if let Ok(inferred) = &result {
            match mode {
                InferMode::Check => {
                    self.infer_cache.insert(
                        e.clone(),
                        inferred.clone(),
                        &self.locals,
                        &self.local_positions,
                    );
                }
                InferMode::Only => {
                    self.infer_only_cache.insert(
                        e.clone(),
                        inferred.clone(),
                        &self.locals,
                        &self.local_positions,
                    );
                }
            }
        }
        result
    }

    /// Checking-mode KR-106 over a flattened application spine. This is
    /// judgment-isomorphic to recursively checking `app_fn` first: head type,
    /// then each argument left-to-right, instantiating the Π body after every
    /// successful comparison. Prefix results are retained just as the
    /// recursive implementation would cache them while unwinding.
    fn infer_app_check(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        let (head, args) = app_spine(e);
        let mut prefix = head.clone();
        let mut function_type = self.infer_core(&head, depth)?;
        for argument in args {
            self.step(depth)?;
            function_type = self.whnf(&function_type, depth)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = function_type.node()
            else {
                return reject(RejectClass::FunctionExpected, "function expected");
            };
            let (binder_type, body) = (binder_type.clone(), body.clone());
            let argument_type = self.infer_core(&argument, depth)?;
            if !self.is_def_eq(&argument_type, &binder_type, depth)? {
                return reject(
                    RejectClass::TypeMismatch,
                    format!(
                        "application type mismatch: argument `{}` has type `{}` but the function expects `{}`{}",
                        brief_expr(&argument, 4),
                        brief_expr(&argument_type, 5),
                        brief_expr(&binder_type, 5),
                        match first_divergence(&argument_type, &binder_type) {
                            Some(divergence) =>
                                format!(" (first structural divergence: {divergence})"),
                            None => String::new(),
                        }
                    ),
                );
            }
            function_type = self.instantiate(&body, 0, &argument, depth)?;
            prefix = Expr::app(prefix, argument);
            self.infer_cache.insert(
                prefix.clone(),
                function_type.clone(),
                &self.locals,
                &self.local_positions,
            );
        }
        Ok(function_type)
    }

    /// Pin `infer_app(..., infer_only=true)`: flatten a left-associated
    /// application spine, infer only the head, and delay substitution while
    /// its type remains syntactically Π. A dependent telescope is instantiated
    /// once per exposed non-Π boundary (and once at the end), matching the pin;
    /// substituting every argument immediately would rewalk the whole remaining
    /// telescope and turn linear arity into quadratic step consumption.
    fn infer_app_only(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        let (head, args) = app_spine(e);
        let mut function_type = self.infer_only_core(&head, depth)?;
        let mut pending_start = 0usize;
        for i in 0..args.len() {
            self.step(depth)?;
            if !matches!(function_type.node(), ExprNode::ForallE { .. }) {
                function_type =
                    self.instantiate_rev(&function_type, &args[pending_start..i], 0, depth)?;
                function_type = self.whnf(&function_type, depth)?;
                pending_start = i;
            }
            let ExprNode::ForallE { body, .. } = function_type.node() else {
                return reject(RejectClass::FunctionExpected, "function expected");
            };
            function_type = body.clone();
        }
        self.instantiate_rev(&function_type, &args[pending_start..], 0, depth)
    }

    /// Pin `infer_lambda`: peel a consecutive lambda telescope iteratively,
    /// open its domains/body simultaneously, infer the body once, and close
    /// the resulting Π telescope in one abstraction traversal.
    fn infer_lambda_spine(&mut self, e: &Expr, depth: u32, mode: InferMode) -> KResult<Expr> {
        let saved_locals = self.locals.len();
        let result = (|| {
            let mut current = e.clone();
            let mut opened_fvars = Vec::new();
            let mut ordinals = HashMap::new();
            let mut binders: Vec<(Name, Expr, BinderInfo, FVarId)> = Vec::new();
            while let ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = current.node()
            {
                self.step(depth)?;
                let binder_name = binder_name.clone();
                let binder_type = self.instantiate_rev(binder_type, &opened_fvars, 0, depth)?;
                let body = body.clone();
                let binder_info = *binder_info;
                if mode == InferMode::Check {
                    self.ensure_sort_of(&binder_type, depth)?;
                }
                let active = u32::try_from(opened_fvars.len())
                    .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
                let closed_type =
                    self.abstract_fvar_set(&binder_type, &ordinals, active, 0, depth)?;
                let id = self.fresh_fvar(binder_type.clone(), None);
                ordinals.insert(id.clone(), active);
                opened_fvars.push(Expr::fvar(id.clone()));
                binders.push((binder_name, closed_type, binder_info, id));
                current = body;
            }
            let body = self.instantiate_rev(&current, &opened_fvars, 0, depth)?;
            let body_type = self.infer_core_mode(&body, depth, mode)?;
            let active = u32::try_from(opened_fvars.len())
                .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
            let mut result = self.abstract_fvar_set(&body_type, &ordinals, active, 0, depth)?;
            for (binder_name, binder_type, binder_info, _) in binders.into_iter().rev() {
                result = Expr::forall_e(binder_name, binder_type, result, binder_info);
            }
            Ok(result)
        })();
        self.truncate_locals(saved_locals);
        result
    }

    /// Pin `infer_pi`: consecutive Π binders are a telescope loop, not a
    /// recursive type-checker call chain.
    fn infer_pi_spine(&mut self, e: &Expr, depth: u32, mode: InferMode) -> KResult<Expr> {
        let saved_locals = self.locals.len();
        let result = (|| {
            let mut current = e.clone();
            let mut opened_fvars = Vec::new();
            let mut domain_levels = Vec::new();
            while let ExprNode::ForallE {
                binder_name: _,
                binder_type,
                body,
                binder_info: _,
            } = current.node()
            {
                self.step(depth)?;
                let binder_type = self.instantiate_rev(binder_type, &opened_fvars, 0, depth)?;
                let body = body.clone();
                let domain_level = self.ensure_sort_of_mode(&binder_type, depth, mode)?;
                let id = self.fresh_fvar(binder_type, None);
                opened_fvars.push(Expr::fvar(id));
                domain_levels.push(domain_level);
                current = body;
            }
            let codomain = self.instantiate_rev(&current, &opened_fvars, 0, depth)?;
            let codomain_type = self.infer_core_mode(&codomain, depth, mode)?;
            let codomain_sort = self.whnf(&codomain_type, depth)?;
            let ExprNode::Sort { level } = codomain_sort.node() else {
                return reject(RejectClass::SortExpected, "Π codomain is not a sort");
            };
            let mut result_level = level.clone();
            for domain_level in domain_levels.into_iter().rev() {
                result_level = Level::try_kernel_imax(domain_level, result_level)
                    .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
            }
            Ok(Expr::sort(result_level))
        })();
        self.truncate_locals(saved_locals);
        result
    }

    /// Pin `infer_let`: open a consecutive let telescope iteratively, perform
    /// checking-mode obligations at each row, then zeta-close the final body
    /// type from innermost local to outermost.
    fn infer_let_spine(&mut self, e: &Expr, depth: u32, mode: InferMode) -> KResult<Expr> {
        let saved_locals = self.locals.len();
        let result = (|| {
            let mut current = e.clone();
            let mut opened_fvars = Vec::new();
            let mut replacements = Vec::new();
            while let ExprNode::LetE {
                decl_name: _,
                type_,
                value,
                body,
                non_dep: _,
            } = current.node()
            {
                self.step(depth)?;
                let type_ = self.instantiate_rev(type_, &opened_fvars, 0, depth)?;
                let value = self.instantiate_rev(value, &opened_fvars, 0, depth)?;
                let body = body.clone();
                if mode == InferMode::Check {
                    self.ensure_sort_of(&type_, depth)?;
                    let value_type = self.infer_core(&value, depth)?;
                    if !self.is_def_eq(&value_type, &type_, depth)? {
                        return reject(RejectClass::TypeMismatch, "let value type mismatch");
                    }
                }
                let id = self.fresh_fvar(type_, Some(value.clone()));
                opened_fvars.push(Expr::fvar(id.clone()));
                replacements.push((id, value));
                current = body;
            }
            let body = self.instantiate_rev(&current, &opened_fvars, 0, depth)?;
            let mut result = self.infer_core_mode(&body, depth, mode)?;
            for (id, value) in replacements.into_iter().rev() {
                result = self.replace_fvar(&result, &id, &value, depth)?;
            }
            Ok(result)
        })();
        self.truncate_locals(saved_locals);
        result
    }

    fn check_level(&self, level: &Level) -> KResult<()> {
        // KR-140-class: every named parameter must be declared.
        let mut undeclared = None;
        collect_undeclared_param(level, self.lparams, &mut undeclared);
        match undeclared {
            Some(name) => reject(
                RejectClass::UndefinedLevelParam,
                format!(
                    "undefined universe level parameter `{}`",
                    name.to_display_string()
                ),
            ),
            None => Ok(()),
        }
    }

    /// whnf the type of `e`'s sort-hood: returns the sort level or rejects.
    fn ensure_sort_of(&mut self, e: &Expr, depth: u32) -> KResult<Level> {
        self.ensure_sort_of_mode(e, depth, InferMode::Check)
    }

    fn ensure_sort_of_mode(&mut self, e: &Expr, depth: u32, mode: InferMode) -> KResult<Level> {
        let type_ = self.infer_core_mode(e, depth, mode)?;
        let sorted = self.whnf(&type_, depth)?;
        match sorted.node() {
            ExprNode::Sort { level } => Ok(level.clone()),
            _ => reject(RejectClass::SortExpected, "type expected (not a sort)"),
        }
    }

    /// Close a whole local telescope in one traversal. `ordinals` assigns
    /// outermost=0; among the first `active` locals, the innermost becomes
    /// `bvar 0`. This avoids the quadratic repeated abstraction that a deep
    /// lambda spine would otherwise perform while rebuilding its Π type.
    fn abstract_fvar_set(
        &mut self,
        e: &Expr,
        ordinals: &HashMap<FVarId, u32>,
        active: u32,
        bound: u32,
        depth: u32,
    ) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_fvar() || active == 0 {
            return Ok(e.clone());
        }
        Ok(match e.node() {
            ExprNode::FVar { id } => match ordinals.get(id).copied() {
                Some(ordinal) if ordinal < active => {
                    let index = bound
                        .checked_add(active - 1 - ordinal)
                        .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                    Expr::bvar(index).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
                }
                _ => e.clone(),
            },
            ExprNode::App { f, a } => Expr::app(
                self.abstract_fvar_set(f, ordinals, active, bound, depth + 1)?,
                self.abstract_fvar_set(a, ordinals, active, bound, depth + 1)?,
            ),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                self.abstract_fvar_set(binder_type, ordinals, active, bound, depth + 1)?,
                self.abstract_fvar_set(body, ordinals, active, bound + 1, depth + 1)?,
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                self.abstract_fvar_set(binder_type, ordinals, active, bound, depth + 1)?,
                self.abstract_fvar_set(body, ordinals, active, bound + 1, depth + 1)?,
                *binder_info,
            ),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => Expr::let_e(
                decl_name.clone(),
                self.abstract_fvar_set(type_, ordinals, active, bound, depth + 1)?,
                self.abstract_fvar_set(value, ordinals, active, bound, depth + 1)?,
                self.abstract_fvar_set(body, ordinals, active, bound + 1, depth + 1)?,
                *non_dep,
            ),
            ExprNode::MData { data, expr } => Expr::mdata(
                data.clone(),
                self.abstract_fvar_set(expr, ordinals, active, bound, depth + 1)?,
            ),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(
                struct_name.clone(),
                *idx,
                self.abstract_fvar_set(expr, ordinals, active, bound, depth + 1)?,
            ),
            ExprNode::BVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => e.clone(),
        })
    }

    fn replace_fvar(&mut self, e: &Expr, id: &FVarId, with: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_fvar() {
            return Ok(e.clone());
        }
        Ok(match e.node() {
            ExprNode::FVar { id: found } if found == id => with.clone(),
            ExprNode::App { f, a } => {
                let f2 = self.replace_fvar(f, id, with, depth + 1)?;
                let a2 = self.replace_fvar(a, id, with, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.replace_fvar(binder_type, id, with, depth + 1)?;
                let b2 = self.replace_fvar(body, id, with, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.replace_fvar(binder_type, id, with, depth + 1)?;
                let b2 = self.replace_fvar(body, id, with, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.replace_fvar(type_, id, with, depth + 1)?;
                let v2 = self.replace_fvar(value, id, with, depth + 1)?;
                let b2 = self.replace_fvar(body, id, with, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.replace_fvar(expr, id, with, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.replace_fvar(expr, id, with, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            _ => e.clone(),
        })
    }

    /// KR-112 + KR-901.
    fn infer_proj(
        &mut self,
        struct_name: &Name,
        idx: u64,
        scrutinee: &Expr,
        depth: u32,
        mode: InferMode,
    ) -> KResult<Expr> {
        let s_type = self.infer_core_mode(scrutinee, depth, mode)?;
        let s_type = self.whnf(&s_type, depth)?;
        let mut args: Vec<Expr> = Vec::new();
        let mut head = s_type.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return reject(
                RejectClass::InvalidProjection,
                "projection of a non-structure",
            );
        };
        if name != struct_name {
            return reject(
                RejectClass::InvalidProjection,
                "projection structure mismatch",
            );
        }
        let Some(ConstantInfo::Induct(ind)) = self.env.find(name) else {
            return reject(
                RejectClass::InvalidProjection,
                "projection of a non-inductive",
            );
        };
        if ind.ctors.len() != 1 || args.len() != (ind.num_params + ind.num_indices) as usize {
            return reject(
                RejectClass::InvalidProjection,
                "projections require a one-constructor structure with exact arity",
            );
        }
        let ctor_name = ind.ctors.first().cloned().unwrap_or_else(Name::anonymous);
        let Some(ConstantInfo::Ctor(ctor)) = self.env.find(&ctor_name) else {
            return reject(
                RejectClass::InvalidProjection,
                "structure constructor missing",
            );
        };
        let is_prop_type = {
            let s_sort = self.infer_only_core(&s_type, depth)?;
            let s_sort = self.whnf(&s_sort, depth)?;
            matches!(s_sort.node(), ExprNode::Sort { level } if level.is_equiv(&Level::zero()))
        };
        // Walk the constructor telescope: instantiate params, then peel idx fields.
        let ctor_params = ctor.base.level_params.clone();
        let levels = levels.clone();
        let mut telescope =
            self.instantiate_lparams(&ctor.base.type_.clone(), &ctor_params, &levels, depth)?;
        for arg in args.iter().take(ctor.num_params as usize) {
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return reject(RejectClass::InvalidProjection, "constructor arity mismatch");
            };
            let body = body.clone();
            telescope = self.instantiate(&body, 0, arg, depth)?;
        }
        for i in 0..idx {
            let ExprNode::ForallE {
                binder_type, body, ..
            } = telescope.node()
            else {
                return reject(
                    RejectClass::InvalidProjection,
                    "projection index out of range",
                );
            };
            if is_prop_type && !self.is_prop(&binder_type.clone(), depth)? {
                return reject(
                    RejectClass::InvalidProjection,
                    "projection would leak data out of Prop",
                );
            }
            let body = body.clone();
            let earlier = Expr::proj(struct_name.clone(), i, scrutinee.clone());
            telescope = self.instantiate(&body, 0, &earlier, depth)?;
        }
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return reject(
                RejectClass::InvalidProjection,
                "projection index out of range",
            );
        };
        let result = binder_type.clone();
        if is_prop_type && !self.is_prop(&result, depth)? {
            return reject(
                RejectClass::InvalidProjection,
                "projection would leak data out of Prop",
            );
        }
        Ok(result)
    }

    /// Publish an irreducible recursor as its own WHNF before a suspended
    /// outer recursor retries.  Without both entries, a safe definition such
    /// as `instDecidableNot p h` can unfold to the same stuck recursor on `h`
    /// on every retry and rebuild the continuation until the step budget is
    /// exhausted.
    fn cache_stuck_recursor(&mut self, stuck: Expr) -> Expr {
        self.whnf_cache.insert(
            stuck.clone(),
            stuck.clone(),
            &self.locals,
            &self.local_positions,
        );
        self.whnf_core_cache.insert(
            stuck.clone(),
            stuck.clone(),
            &self.locals,
            &self.local_positions,
        );
        stuck
    }
}

/// Bounded level rendering for rejection messages.
fn brief_level(level: &Level, fuel: usize) -> String {
    use fln_core::level::LevelView;
    if fuel == 0 {
        return "..".to_string();
    }
    match level.view() {
        LevelView::Zero => "0".to_string(),
        LevelView::Param(name) => name.to_display_string(),
        LevelView::MVar(_) => "mvar".to_string(),
        LevelView::Succ(inner) => format!("{}+1", brief_level(inner, fuel - 1)),
        LevelView::Max(a, b) => format!(
            "max({},{})",
            brief_level(a, fuel - 1),
            brief_level(b, fuel - 1)
        ),
        LevelView::IMax(a, b) => format!(
            "imax({},{})",
            brief_level(a, fuel - 1),
            brief_level(b, fuel - 1)
        ),
    }
}

/// Crate-facing bounded rendering (lib.rs admission messages).
pub(crate) fn brief_public(e: &Expr) -> String {
    brief_expr(e, 5)
}

/// Crate-facing divergence locator (admit.rs cross-check messages).
pub(crate) fn first_divergence_public(t: &Expr, s: &Expr) -> Option<String> {
    first_divergence(t, s)
}

/// Structural first-divergence locator for mismatch DIAGNOSTICS only — never
/// part of a judgment. Walks both terms in lockstep and reports the path to,
/// and both sides of, the first place the trees differ, exposing exactly the
/// differences the bounded renderer elides: metadata wrappers, binder names
/// and infos, literal values, and level shapes. Equal subtrees prune via
/// `Expr::eq`, so cost is linear in the shared prefix (bead franken_lean-irm;
/// the d4x arc's level-aware messages are the precedent).
fn first_divergence(t: &Expr, s: &Expr) -> Option<String> {
    fn level_shape(l: &Level) -> String {
        use fln_core::level::LevelView;
        match l.view() {
            LevelView::Zero => "0".to_string(),
            LevelView::Param(p) => format!("param:{}", p.to_display_string()),
            LevelView::Succ(inner) => format!("succ({})", level_shape(inner)),
            LevelView::Max(a, b) => format!("max({},{})", level_shape(a), level_shape(b)),
            LevelView::IMax(a, b) => format!("imax({},{})", level_shape(a), level_shape(b)),
            LevelView::MVar(_) => "mvar".to_string(),
        }
    }
    fn levels_diff(path: &str, l1: &[Level], l2: &[Level]) -> Option<String> {
        if l1.len() != l2.len() {
            return Some(format!("{path}: {} vs {} levels", l1.len(), l2.len()));
        }
        for (i, (a, b)) in l1.iter().zip(l2).enumerate() {
            if a != b {
                return Some(format!(
                    "{path}.level[{i}]: {} vs {}",
                    level_shape(a),
                    level_shape(b)
                ));
            }
        }
        None
    }
    fn go(t: &Expr, s: &Expr, path: String) -> Option<String> {
        if t == s {
            return None;
        }
        match (t.node(), s.node()) {
            (ExprNode::BVar { idx: i1 }, ExprNode::BVar { idx: i2 }) => {
                Some(format!("{path}: #{i1} vs #{i2}"))
            }
            (ExprNode::FVar { id: id1 }, ExprNode::FVar { id: id2 }) => Some(format!(
                "{path}: fvar {} vs {}",
                id1.0.to_display_string(),
                id2.0.to_display_string()
            )),
            (ExprNode::Sort { level: l1 }, ExprNode::Sort { level: l2 }) => Some(format!(
                "{path}: Sort {} vs {}",
                level_shape(l1),
                level_shape(l2)
            )),
            (
                ExprNode::Const {
                    name: n1,
                    levels: l1,
                },
                ExprNode::Const {
                    name: n2,
                    levels: l2,
                },
            ) => {
                if n1 != n2 {
                    Some(format!(
                        "{path}: const {} vs {}",
                        n1.to_display_string(),
                        n2.to_display_string()
                    ))
                } else {
                    levels_diff(&path, l1, l2)
                        .or_else(|| Some(format!("{path}: consts differ undetectably")))
                }
            }
            (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
                go(f1, f2, format!("{path}.fn")).or_else(|| go(a1, a2, format!("{path}.arg")))
            }
            (
                ExprNode::Lam {
                    binder_name: n1,
                    binder_type: t1,
                    body: b1,
                    binder_info: i1,
                },
                ExprNode::Lam {
                    binder_name: n2,
                    binder_type: t2,
                    body: b2,
                    binder_info: i2,
                },
            )
            | (
                ExprNode::ForallE {
                    binder_name: n1,
                    binder_type: t1,
                    body: b1,
                    binder_info: i1,
                },
                ExprNode::ForallE {
                    binder_name: n2,
                    binder_type: t2,
                    body: b2,
                    binder_info: i2,
                },
            ) => {
                if i1 != i2 {
                    return Some(format!("{path}: binder info {i1:?} vs {i2:?}"));
                }
                if n1 != n2 {
                    return Some(format!(
                        "{path}: binder name {} vs {}",
                        n1.to_display_string(),
                        n2.to_display_string()
                    ));
                }
                go(t1, t2, format!("{path}.binder_type"))
                    .or_else(|| go(b1, b2, format!("{path}.body")))
            }
            (
                ExprNode::LetE {
                    type_: t1,
                    value: v1,
                    body: b1,
                    ..
                },
                ExprNode::LetE {
                    type_: t2,
                    value: v2,
                    body: b2,
                    ..
                },
            ) => go(t1, t2, format!("{path}.let_type"))
                .or_else(|| go(v1, v2, format!("{path}.let_value")))
                .or_else(|| go(b1, b2, format!("{path}.let_body"))),
            (ExprNode::MData { expr: e1, .. }, ExprNode::MData { expr: e2, .. }) => {
                go(e1, e2, format!("{path}.mdata"))
                    .or_else(|| Some(format!("{path}: metadata payloads differ")))
            }
            (ExprNode::MData { expr, .. }, _) => go(expr, s, path.clone())
                .or_else(|| Some(format!("{path}: metadata wrapper on the left only"))),
            (_, ExprNode::MData { expr, .. }) => go(t, expr, path.clone())
                .or_else(|| Some(format!("{path}: metadata wrapper on the right only"))),
            (
                ExprNode::Proj {
                    struct_name: n1,
                    idx: i1,
                    expr: e1,
                },
                ExprNode::Proj {
                    struct_name: n2,
                    idx: i2,
                    expr: e2,
                },
            ) => {
                if n1 != n2 || i1 != i2 {
                    Some(format!(
                        "{path}: proj {}.{} vs {}.{}",
                        n1.to_display_string(),
                        i1,
                        n2.to_display_string(),
                        i2
                    ))
                } else {
                    go(e1, e2, format!("{path}.proj_expr"))
                }
            }
            (ExprNode::Lit { literal: l1 }, ExprNode::Lit { literal: l2 }) => {
                (l1 != l2).then(|| {
                    format!(
                        "{path}: literal {} vs {}",
                        brief_expr(t, 1),
                        brief_expr(s, 1)
                    )
                })
            }
            (t_node, s_node) => Some(format!(
                "{path}: node kind {} vs {}",
                node_kind_name(t_node),
                node_kind_name(s_node)
            )),
        }
    }
    go(t, s, "root".to_string())
}

fn node_kind_name(node: &ExprNode) -> &'static str {
    match node {
        ExprNode::BVar { .. } => "bvar",
        ExprNode::FVar { .. } => "fvar",
        ExprNode::MVar { .. } => "mvar",
        ExprNode::Sort { .. } => "sort",
        ExprNode::Const { .. } => "const",
        ExprNode::App { .. } => "app",
        ExprNode::Lam { .. } => "lambda",
        ExprNode::ForallE { .. } => "forall",
        ExprNode::LetE { .. } => "let",
        ExprNode::MData { .. } => "mdata",
        ExprNode::Proj { .. } => "proj",
        ExprNode::Lit { .. } => "literal",
    }
}

/// Bounded, allocation-light term rendering for rejection MESSAGES only —
/// never part of a judgment. Fuel caps both depth and total size so adversarial
/// terms cannot blow up diagnostics (FL-INV-07 discipline extends to logs).
fn brief_expr(e: &Expr, fuel: usize) -> String {
    if fuel == 0 {
        return "..".to_string();
    }
    match e.node() {
        ExprNode::BVar { idx } => format!("#{idx}"),
        ExprNode::FVar { id } => format!("fvar:{}", id.0.to_display_string()),
        ExprNode::MVar { .. } => "mvar".to_string(),
        ExprNode::Sort { level } => format!("Sort<{}>", brief_level(level, fuel)),
        ExprNode::Const { name, levels } => {
            if levels.is_empty() {
                name.to_display_string()
            } else {
                let rendered: Vec<String> = levels.iter().map(|l| brief_level(l, fuel)).collect();
                format!("{}.{{{}}}", name.to_display_string(), rendered.join(","))
            }
        }
        ExprNode::App { .. } => {
            let (head, args) = app_spine(e);
            let mut out = format!("({}", brief_expr(&head, fuel - 1));
            for arg in &args {
                out.push(' ');
                out.push_str(&brief_expr(arg, fuel - 1));
            }
            out.push(')');
            out
        }
        ExprNode::Lam { body, .. } => format!("(fun _ => {})", brief_expr(body, fuel - 1)),
        ExprNode::ForallE {
            binder_type, body, ..
        } => format!(
            "({} -> {})",
            brief_expr(binder_type, fuel - 1),
            brief_expr(body, fuel - 1)
        ),
        ExprNode::LetE { body, .. } => format!("(let _; {})", brief_expr(body, fuel - 1)),
        ExprNode::MData { expr, .. } => brief_expr(expr, fuel),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => format!(
            "({}.{} {})",
            struct_name.to_display_string(),
            idx,
            brief_expr(expr, fuel - 1)
        ),
        ExprNode::Lit {
            literal: Literal::Nat(value),
        } => {
            // Small values render exactly (triage needs to SEE 0 vs 2); giants
            // render by limb count so adversarial literals cannot blow up logs.
            match value.to_u64() {
                Some(v) => format!("lit:{v}"),
                None => format!("lit:<{} limbs>", value.limbs_le().len()),
            }
        }
        ExprNode::Lit {
            literal: Literal::Str(value),
        } => {
            let mut shown: String = value.chars().take(16).collect();
            if shown.len() < value.len() {
                shown.push('…');
            }
            format!("lit:{shown:?}")
        }
    }
}

/// Split an application spine into `(head, args-left-to-right)`.
fn app_spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args: Vec<Expr> = Vec::new();
    let mut head = e.clone();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        let next = f.clone();
        head = next;
    }
    args.reverse();
    (head, args)
}

/// Outcome of the lazy-delta loop: a decisive literal/offset verdict, or the
/// maximally-unfolded pair for the rest of the ladder.
enum LazyDelta {
    Decided(bool),
    Stuck(Expr, Expr),
}

/// `nat_lit_to_constructor` (inductive.cpp:1191): `0 ⟶ Nat.zero`,
/// `n ⟶ Nat.succ (n-1 : literal)` for `n > 0`.
fn nat_lit_to_constructor(value: &NatLit) -> Expr {
    let nat = Name::str(Name::anonymous(), "Nat");
    if value.to_u64() == Some(0) {
        return Expr::const_(Name::str(nat, "zero"), Vec::new());
    }
    Expr::app(
        Expr::const_(Name::str(nat, "succ"), Vec::new()),
        Expr::lit(Literal::Nat(nat_lit_pred(value))),
    )
}

/// The predecessor of a positive literal — a plain limb borrow walk; value
/// identity only, no bignum-arithmetic dependency.
fn nat_lit_pred(value: &NatLit) -> NatLit {
    let mut limbs = value.limbs_le().to_vec();
    for limb in limbs.iter_mut() {
        if *limb > 0 {
            *limb -= 1;
            break;
        }
        *limb = u64::MAX;
    }
    NatLit::from_limbs_le(limbs)
}

/// `string_lit_to_constructor` (inductive.cpp:1200): `"…"` ⟶
/// `String.ofList (List.cons.{0} Char (Char.ofNat (c₀ : lit)) … (List.nil.{0}
/// Char))` over the literal's Unicode code points. The pin's `g_string_mk` is
/// the constant `String.ofList` at this pin (type_checker.cpp:1213,
/// inductive.cpp:1226) — a definition, so recursor/projection consumers whnf
/// the expansion down to the real constructor.
fn string_lit_to_constructor(value: &str) -> Expr {
    let char_const = Expr::const_(Name::str(Name::anonymous(), "Char"), Vec::new());
    let list = Name::str(Name::anonymous(), "List");
    let cons = Expr::app(
        Expr::const_(Name::str(list.clone(), "cons"), vec![Level::zero()]),
        char_const.clone(),
    );
    let nil = Expr::app(
        Expr::const_(Name::str(list, "nil"), vec![Level::zero()]),
        char_const.clone(),
    );
    let char_of_nat = Expr::const_(
        Name::str(Name::str(Name::anonymous(), "Char"), "ofNat"),
        Vec::new(),
    );
    let mut spine = nil;
    for c in value.chars().rev() {
        let code = Expr::lit(Literal::Nat(NatLit::from_u64(u64::from(u32::from(c)))));
        spine = Expr::app(
            Expr::app(cons.clone(), Expr::app(char_of_nat.clone(), code)),
            spine,
        );
    }
    Expr::app(
        Expr::const_(
            Name::str(Name::str(Name::anonymous(), "String"), "ofList"),
            Vec::new(),
        ),
        spine,
    )
}

/// Is `name` exactly `<root>.<leaf>` at the top level?
fn is_name2(name: &Name, root: &str, leaf: &str) -> bool {
    if !matches!(name.leaf_view(), LeafView::Str(s) if s == leaf) {
        return false;
    }
    let parent = name.parent();
    matches!(parent.leaf_view(), LeafView::Str(s) if s == root) && parent.parent().is_anonymous()
}

/// `Nat.<op>` recognition for the KR-313 dispatch table.
fn nat_op_leaf(name: &Name) -> Option<&str> {
    let LeafView::Str(leaf) = name.leaf_view() else {
        return None;
    };
    let parent = name.parent();
    let is_nat = matches!(parent.leaf_view(), LeafView::Str(s) if s == "Nat")
        && parent.parent().is_anonymous();
    if is_nat { Some(leaf) } else { None }
}

/// `is_nat_lit_ext` (pin type_checker.cpp:569): a Nat literal, or the bare
/// constant `Nat.zero` (the pin compares whole expressions, so levels must be
/// empty), as a bignum value.
fn nat_lit_ext_value(e: &Expr) -> Option<BigNat> {
    match e.node() {
        ExprNode::Lit {
            literal: Literal::Nat(value),
        } => Some(bignat_from_literal(value)),
        ExprNode::Const { name, levels } if levels.is_empty() && is_name2(name, "Nat", "zero") => {
            Some(BigNat::zero())
        }
        _ => None,
    }
}

/// `is_nat_zero` (pin type_checker.cpp:943): `Nat.zero` or the literal `0`.
fn is_nat_zero_expr(e: &Expr) -> bool {
    match e.node() {
        ExprNode::Lit {
            literal: Literal::Nat(value),
        } => value.to_u64() == Some(0),
        ExprNode::Const { name, levels } => levels.is_empty() && is_name2(name, "Nat", "zero"),
        _ => false,
    }
}

/// `is_nat_succ` (pin type_checker.cpp:947): a positive literal peels to its
/// predecessor literal; `Nat.succ x` (exactly one argument — the outermost
/// function must be the bare constant) peels to `x`.
fn nat_succ_peel(e: &Expr) -> Option<Expr> {
    if let ExprNode::Lit {
        literal: Literal::Nat(value),
    } = e.node()
    {
        if value.to_u64() == Some(0) {
            return None;
        }
        return Some(Expr::lit(Literal::Nat(nat_lit_pred(value))));
    }
    if let ExprNode::App { f, a } = e.node()
        && let ExprNode::Const { name, levels } = f.node()
        && levels.is_empty()
        && is_name2(name, "Nat", "succ")
    {
        return Some(a.clone());
    }
    None
}

/// `Bool.true` / `Bool.false` (pin `mk_bool_true`/`mk_bool_false`).
fn bool_const_expr(value: bool) -> Expr {
    let bool_name = Name::str(Name::anonymous(), "Bool");
    Expr::const_(
        Name::str(bool_name, if value { "true" } else { "false" }),
        Vec::new(),
    )
}

/// A bignum value back onto the term plane, loss-free.
fn nat_lit_expr(value: &BigNat) -> Expr {
    Expr::lit(Literal::Nat(literal_from_bignat(value)))
}

/// Is this constant unsafe in the KR-973 sense (pin `constant_info::is_unsafe`)?
pub(crate) fn constant_is_unsafe(info: &ConstantInfo) -> bool {
    match info {
        ConstantInfo::Axiom(v) => v.is_unsafe,
        ConstantInfo::Defn(v) => v.safety == DefinitionSafety::Unsafe,
        ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => false,
        ConstantInfo::Opaque(v) => v.is_unsafe,
        ConstantInfo::Induct(v) => v.is_unsafe,
        ConstantInfo::Ctor(v) => v.is_unsafe,
        ConstantInfo::Rec(v) => v.is_unsafe,
    }
}

/// Level-parameter substitution (pure, structural).
fn substitute_level(level: &Level, params: &[Name], levels: &[Level]) -> Level {
    use fln_core::level::LevelView;
    match level.view() {
        LevelView::Zero => Level::zero(),
        LevelView::Param(name) => params
            .iter()
            .position(|p| p == name)
            .and_then(|i| levels.get(i))
            .cloned()
            .unwrap_or_else(|| level.clone()),
        LevelView::Succ(inner) => substitute_level(inner, params, levels)
            .succ()
            .unwrap_or_else(|_| level.clone()),
        LevelView::Max(a, b) => Level::try_smart_max(
            substitute_level(a, params, levels),
            substitute_level(b, params, levels),
        )
        .unwrap_or_else(|_| level.clone()),
        LevelView::IMax(a, b) => Level::try_kernel_imax(
            substitute_level(a, params, levels),
            substitute_level(b, params, levels),
        )
        .unwrap_or_else(|_| level.clone()),
        LevelView::MVar(_) => level.clone(),
    }
}

fn collect_undeclared_param(level: &Level, declared: &[Name], found: &mut Option<Name>) {
    use fln_core::level::LevelView;
    if found.is_some() || !level.has_param() {
        return;
    }
    match level.view() {
        LevelView::Param(name) => {
            if !declared.contains(name) {
                *found = Some(name.clone());
            }
        }
        LevelView::Succ(inner) => collect_undeclared_param(inner, declared, found),
        LevelView::Max(a, b) | LevelView::IMax(a, b) => {
            collect_undeclared_param(a, declared, found);
            collect_undeclared_param(b, declared, found);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration;
    use crate::admit::{compare_recursor_sets, lower_param_expr};
    use crate::capability::{Admitted, Published, admit};
    use crate::council::{Council, CouncilOutcome, convene};
    use fln_core::outcome::Outcome;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;

    /// Build an authoritative test environment through the same checked
    /// capability and explicit council path as production publication. Keeping
    /// this inside the unit module avoids giving `TypeChecker` a test-only raw
    /// admission escape hatch.
    fn publish_checked(env: &Environment, decl: Declaration) -> Environment {
        let admitted = match admit(env, decl, Budget::DEFAULT) {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(_) => unreachable!("a fixed test declaration exhausted"),
            Outcome::InternalFault(_) => unreachable!("a fixed test declaration faulted"),
        };
        assert!(
            matches!(admitted, Admitted::Accepted(_)),
            "the fixed test declaration must pass the kernel"
        );
        let checked = match convene(&Council::nobody_was_asked(), admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::Halted(_) => unreachable!("an empty council cannot object"),
            CouncilOutcome::KernelRejected { .. } => {
                unreachable!("the fixed test declaration must pass the kernel")
            }
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(published))) => {
                published.environment
            }
            Outcome::Complete(_) => unreachable!("a fresh single declaration must publish"),
            Outcome::Inconclusive(_) => unreachable!("fixed test publication exhausted"),
            Outcome::InternalFault(_) => unreachable!("fixed test publication faulted"),
        }
    }

    /// KR-202's substitution primitive: when `instantiate` consumes binder `k`,
    /// every loose bvar ABOVE `k` must shift down by one, because the binder it
    /// used to count past is gone.
    ///
    /// This is tested here, against the primitive, rather than through `check`,
    /// because the branch is unreachable from the public surface: KR-100 rejects
    /// terms with loose bvars, so in a closed term every bvar reached at depth
    /// `k` has index at most `k`. A mutation campaign confirmed that directly —
    /// dropping the `- 1` left all 93 kernel tests passing, and a panic planted
    /// in the branch was never once reached by the suite.
    ///
    /// That makes the arm defensive code inside the TCB whose correctness rested
    /// on an unstated precondition. It is one `pub(crate)` caller away from
    /// being live, and a wrong shift there silently rebinds a variable to the
    /// wrong binder — a term that still typechecks and means something else.
    #[test]
    fn instantiate_shifts_loose_bvars_down_past_the_consumed_binder() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let bv = |i: u32| Expr::bvar(i).expect("packs");
        let subst = Expr::sort(Level::zero());

        // `#0 #1` with binder 0 consumed: #0 becomes the substitute, and #1 —
        // which pointed one binder further out — must become #0.
        let open = Expr::app(bv(0), bv(1));
        // `assert!` rather than `assert_eq!`: FLN-STRUCT-030 admits exactly
        // {assert, format, matches, unreachable, vec} inside the kernel, so
        // that every expansion maps to a reviewed, LOC-counted callsite.
        assert!(
            tc.instantiate(&open, 0, &subst, 0).expect("instantiates")
                == Expr::app(subst.clone(), bv(0)),
            "a free bvar above the consumed binder must shift down by one"
        );

        // The same law one binder deeper, where `k` has advanced to 1: #0 is
        // the inner binder and is untouched, #2 shifts to #1.
        let under_binder = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            subst.clone(),
            Expr::app(bv(0), bv(2)),
            fln_core::expr::BinderInfo::Default,
        );
        let expected = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            subst.clone(),
            Expr::app(bv(0), bv(1)),
            fln_core::expr::BinderInfo::Default,
        );
        assert!(
            tc.instantiate(&under_binder, 0, &subst, 0)
                .expect("instantiates")
                == expected,
            "the shift must apply under binders with k advanced, and must not \
             disturb bvars bound inside the term"
        );

        // Bvars strictly below `k` are bound inside and must not move at all.
        let inner_bound = Expr::app(bv(0), bv(0));
        assert!(
            tc.instantiate(&inner_bound, 1, &subst, 0)
                .expect("instantiates")
                == inner_bound,
            "bvars below the consumed binder are untouched"
        );
    }

    #[test]
    fn level_substitution_uses_the_pin_smart_constructors() {
        let u = Name::str(Name::anonymous(), "u");
        let v = Name::str(Name::anonymous(), "v");
        let params = [u.clone(), v.clone()];
        let levels = [Level::zero(), Level::zero()];
        let max = Level::max(Level::param(u.clone()), Level::param(v.clone())).expect("packs");
        let imax = Level::imax(Level::param(u), Level::param(v)).expect("packs");
        let w = Name::str(Name::anonymous(), "w");
        let one_imax_w = Level::imax(Level::one(), Level::param(w.clone())).expect("packs");

        assert!(
            substitute_level(&max, &params, &levels) == Level::zero(),
            "substituting zero for both sides of max must build zero, not raw max(0,0)"
        );
        assert!(
            substitute_level(&imax, &params, &levels) == Level::zero(),
            "substituting zero for both sides of imax must build zero, not raw imax(0,0)"
        );
        assert!(
            substitute_level(&one_imax_w, &[], &[]) == Level::param(w),
            "kernel imax 1 u must be structurally u"
        );
    }

    #[test]
    fn pi_inference_uses_the_pin_smart_imax_constructor() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let proposition = Expr::sort(Level::zero());
        let dependent_proposition = Expr::forall_e(
            Name::str(Name::anonymous(), "p"),
            proposition,
            Expr::bvar(0).expect("packs"),
            fln_core::expr::BinderInfo::Default,
        );

        assert!(
            tc.infer(&dependent_proposition, 0).expect("infers") == Expr::sort(Level::zero()),
            "imax 1 0 must be structurally zero, matching the Reference smart constructor"
        );
    }

    fn closed_cache_fixture() -> (Expr, Expr, Expr) {
        let sort = Expr::sort(Level::zero());
        let binder_type = Expr::sort(Level::one());
        let identity = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            binder_type,
            Expr::bvar(0).expect("packs"),
            fln_core::expr::BinderInfo::Default,
        );
        let redex = Expr::app(identity, sort.clone());
        let pi = Expr::forall_e(
            Name::str(Name::anonymous(), "p"),
            sort.clone(),
            sort.clone(),
            fln_core::expr::BinderInfo::Default,
        );
        (pi, redex, sort)
    }

    #[test]
    fn closed_inference_whnf_and_positive_defeq_queries_reuse_only_established_results() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let (pi, redex, sort) = closed_cache_fixture();

        let inferred = tc.infer(&pi, 0).expect("first inference completes");
        let after_first_infer = tc.consumption();
        assert!(
            tc.infer(&pi, 0).expect("cached inference completes") == inferred,
            "a successful inference cache hit must preserve the exact inferred term"
        );
        let after_second_infer = tc.consumption();
        assert!(
            after_second_infer.steps_used - after_first_infer.steps_used == 2,
            "the public inference entry and KR-400 core hook still charge on a cache hit"
        );

        let reduced = tc.whnf_public(&redex, 0).expect("first whnf completes");
        assert!(
            reduced == sort,
            "the beta fixture must reduce before it can evidence the cache"
        );
        let after_first_whnf = tc.consumption();
        assert!(
            tc.whnf_public(&redex, 0).expect("cached whnf completes") == reduced,
            "a successful whnf cache hit must preserve the exact normal form"
        );
        let after_second_whnf = tc.consumption();
        assert!(
            after_second_whnf.steps_used == after_first_whnf.steps_used,
            "the full whnf cache sits before whnf-core, so a hit performs no KR-401 entry"
        );

        assert!(
            tc.def_eq_public(&redex, &sort, 0)
                .expect("first defeq completes"),
            "the beta fixture must be definitionally equal"
        );
        let after_first_defeq = tc.consumption();
        assert!(
            tc.def_eq_public(&redex, &sort, 0)
                .expect("cached defeq completes"),
            "only an established positive result may be reused"
        );
        let after_second_defeq = tc.consumption();
        assert!(
            after_second_defeq.steps_used - after_first_defeq.steps_used == 1,
            "KR-300 still charges before the positive-equivalence cache answers"
        );
    }

    #[test]
    fn infer_only_and_checking_mode_caches_are_authority_disjoint() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let undeclared = Expr::sort(Level::param(Name::str(Name::anonymous(), "u")));

        tc.infer_only(&undeclared, 0)
            .expect("infer-only deliberately skips level-parameter validation");
        assert!(
            tc.infer_only_cache.entries == 1 && tc.infer_cache.entries == 0,
            "an infer-only result must enter only the infer-only table"
        );
        assert!(
            matches!(
                tc.infer(&undeclared, 0),
                Err(Stop::Reject(RejectClass::UndefinedLevelParam, _))
            ),
            "checking mode must still enforce the obligation infer-only skipped"
        );
        assert!(
            tc.infer_cache.entries == 0,
            "a rejected checking query must not be cached"
        );
    }

    #[test]
    fn checking_and_infer_only_application_spines_are_depth_independent() {
        use fln_env::constants::{AxiomVal, ConstantVal};

        const ARITY: usize = 5_000;
        let function_name = Name::str(Name::anonymous(), "wide");
        let nat_name = Name::str(Name::anonymous(), "Nat");
        let nat = Expr::const_(nat_name.clone(), Vec::new());
        let mut function_type = nat.clone();
        for _ in 0..ARITY {
            function_type = Expr::forall_e(
                Name::anonymous(),
                nat.clone(),
                function_type,
                fln_core::expr::BinderInfo::Default,
            );
        }
        let env = publish_checked(
            &Environment::new(),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: nat_name,
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }),
        );
        let env = publish_checked(
            &env,
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: function_name.clone(),
                    level_params: Vec::new(),
                    type_: function_type,
                },
                is_unsafe: false,
            }),
        );
        let mut application = Expr::const_(function_name, Vec::new());
        let zero = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        for _ in 0..ARITY {
            application = Expr::app(application, zero.clone());
        }

        let budget = Budget::DEFAULT.narrowed(1_000_000, 32);
        let mut checking = TypeChecker::new(&env, &[], budget);
        assert!(
            checking.infer(&application, 0).expect("checking spine") == nat,
            "checking mode must validate every argument without recursive app-fn descent"
        );
        assert!(
            checking.consumption().max_depth <= budget.depth,
            "wide arity must consume loop steps, not native-stack depth"
        );

        let mut infer_only = TypeChecker::new(&env, &[], budget);
        assert!(
            infer_only
                .infer_only(&application, 0)
                .expect("infer-only spine")
                == nat,
            "infer-only must instantiate the same Π telescope"
        );
        assert!(
            infer_only.consumption().max_depth <= budget.depth,
            "the pin's flattened infer-only spine must stay inside the shallow budget"
        );
    }

    #[test]
    fn infer_only_batches_a_dependent_application_telescope() {
        use fln_env::constants::{AxiomVal, ConstantVal};

        const ARITY: usize = 512;
        let function_name = Name::str(Name::anonymous(), "dependentWide");
        // `(α₀ ... α₅₁₁ : Type) → α₀`. The final body mentions the
        // outermost binder, so eager one-at-a-time substitution must traverse
        // the whole remaining telescope after every argument.
        let outermost = u32::try_from(ARITY - 1).expect("the fixed test arity fits a bvar index");
        let mut function_type = Expr::bvar(outermost).expect("packs");
        for _ in 0..ARITY {
            function_type = Expr::forall_e(
                Name::anonymous(),
                Expr::sort(Level::one()),
                function_type,
                BinderInfo::Default,
            );
        }
        let env = publish_checked(
            &Environment::new(),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: function_name.clone(),
                    level_params: Vec::new(),
                    type_: function_type,
                },
                is_unsafe: false,
            }),
        );
        let argument = Expr::sort(Level::zero());
        let mut application = Expr::const_(function_name, Vec::new());
        for _ in 0..ARITY {
            application = Expr::app(application, argument.clone());
        }

        let budget = Budget::DEFAULT.narrowed(50_000, 1_024);
        let mut tc = TypeChecker::new(&env, &[], budget);
        assert!(
            tc.infer_only(&application, 0)
                .expect("batched dependent inference fits its linear budget")
                == argument,
            "the outermost binder must receive the first application argument"
        );
        assert!(
            tc.consumption().steps_used < budget.steps,
            "dependent infer-only substitution must stay linear in telescope arity"
        );
    }

    #[test]
    fn batched_beta_consumes_a_deep_lambda_spine_without_rewalking_the_body() {
        const ARITY: usize = 5_000;
        let domain = Expr::sort(Level::one());
        let argument = Expr::sort(Level::zero());
        let mut function = Expr::bvar((ARITY - 1) as u32).expect("packs");
        for _ in 0..ARITY {
            function = Expr::lam(
                Name::anonymous(),
                domain.clone(),
                function,
                BinderInfo::Default,
            );
        }
        let mut application = function;
        for _ in 0..ARITY {
            application = Expr::app(application, argument.clone());
        }

        let env = Environment::new();
        let budget = Budget::DEFAULT.narrowed(100_000, 32);
        let mut tc = TypeChecker::new(&env, &[], budget);
        assert!(
            tc.whnf_public(&application, 0)
                .expect("batched beta stays inside the shallow budget")
                == argument,
            "the outermost binder must receive the first application argument"
        );
        assert!(
            tc.consumption().max_depth <= budget.depth,
            "lambda arity must consume loop steps rather than native-stack depth"
        );
    }

    #[test]
    fn lambda_pi_and_let_telescopes_are_depth_independent() {
        use fln_env::constants::{AxiomVal, ConstantVal};

        const ARITY: usize = 5_000;
        let nat_name = Name::str(Name::anonymous(), "Nat");
        let nat = Expr::const_(nat_name.clone(), Vec::new());
        let zero = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        let env = publish_checked(
            &Environment::new(),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: nat_name,
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }),
        );
        let budget = Budget::DEFAULT.narrowed(1_000_000, 32);

        let mut lambda = zero.clone();
        for _ in 0..ARITY {
            lambda = Expr::lam(Name::anonymous(), nat.clone(), lambda, BinderInfo::Default);
        }
        let mut lambda_tc = TypeChecker::new(&env, &[], budget);
        let mut lambda_type = lambda_tc
            .infer(&lambda, 0)
            .expect("lambda telescope stays inside the shallow budget");
        let mut lambda_binders = 0usize;
        while let ExprNode::ForallE {
            binder_type, body, ..
        } = lambda_type.node()
        {
            assert!(
                *binder_type == nat,
                "each inferred lambda domain must be preserved"
            );
            lambda_binders += 1;
            lambda_type = body.clone();
        }
        assert!(
            lambda_binders == ARITY && lambda_type == nat,
            "lambda inference must close the complete Π telescope around the body type"
        );
        assert!(
            lambda_tc.consumption().max_depth <= budget.depth,
            "lambda telescope length must consume steps, not logical depth"
        );

        let mut pi = nat.clone();
        for _ in 0..ARITY {
            pi = Expr::forall_e(Name::anonymous(), nat.clone(), pi, BinderInfo::Default);
        }
        let mut pi_tc = TypeChecker::new(&env, &[], budget);
        assert!(
            pi_tc
                .infer(&pi, 0)
                .expect("Pi telescope stays inside the shallow budget")
                == Expr::sort(Level::one()),
            "a Nat-to-Nat Π telescope must remain in Type"
        );
        assert!(
            pi_tc.consumption().max_depth <= budget.depth,
            "Pi telescope length must consume steps, not logical depth"
        );

        let mut let_chain = zero.clone();
        for _ in 0..ARITY {
            let_chain = Expr::let_e(
                Name::anonymous(),
                nat.clone(),
                zero.clone(),
                let_chain,
                true,
            );
        }
        let mut let_tc = TypeChecker::new(&env, &[], budget);
        assert!(
            let_tc
                .infer(&let_chain, 0)
                .expect("let telescope stays inside the shallow budget")
                == nat,
            "zeta-closing a nondependent let telescope must preserve the body type"
        );
        assert!(
            let_tc.consumption().max_depth <= budget.depth,
            "let telescope length must consume steps, not logical depth"
        );
    }

    #[test]
    fn lazy_delta_compares_same_regular_head_arguments_before_unfolding() {
        use fln_core::options::KVMap;
        use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal};

        let nat_name = Name::str(Name::anonymous(), "Nat");
        let nat = Expr::const_(nat_name.clone(), Vec::new());
        let function_name = Name::str(Name::anonymous(), "expensiveRegular");
        let function_type = Expr::forall_e(
            Name::anonymous(),
            nat.clone(),
            nat.clone(),
            BinderInfo::Default,
        );

        // The definition body is intentionally deeper than the checker budget.
        // Definitional congruence of `f a` and `f b` does not require opening
        // `f`; a mutant that deletes the same-head shortcut tries to strip this
        // metadata tower and reports typed depth exhaustion.
        let mut function_value = Expr::lam(
            Name::anonymous(),
            nat.clone(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        );
        for _ in 0..128 {
            function_value = Expr::mdata(KVMap::default(), function_value);
        }

        let env = publish_checked(
            &Environment::new(),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: nat_name,
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }),
        );
        let env = publish_checked(
            &env,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: function_name.clone(),
                    level_params: Vec::new(),
                    type_: function_type,
                },
                value: function_value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![function_name.clone()],
            }),
        );
        let zero = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        let identity = Expr::lam(
            Name::anonymous(),
            nat,
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        );
        let beta_zero = Expr::app(identity, zero.clone());
        let left = Expr::app(Expr::const_(function_name.clone(), Vec::new()), beta_zero);
        let right = Expr::app(Expr::const_(function_name, Vec::new()), zero);

        let budget = Budget::DEFAULT.narrowed(10_000, 32);
        let mut tc = TypeChecker::new(&env, &[], budget);
        assert!(
            tc.def_eq_public(&left, &right, 0)
                .expect("same-head congruence stays inside the shallow budget"),
            "definitionally equal arguments must close without unfolding the regular head"
        );
        assert!(
            tc.consumption().max_depth <= budget.depth,
            "an expensive regular body must remain unopened on a positive congruence"
        );
    }

    #[test]
    fn fvar_queries_cannot_borrow_an_inference_result_after_their_scope_closes() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let id = FVarId(Name::str(Name::anonymous(), "scoped"));
        let local = Expr::fvar(id.clone());
        let type_ = Expr::sort(Level::zero());
        tc.adopt_local(id.clone(), type_.clone());

        assert!(
            tc.infer(&local, 0).expect("live local infers") == type_,
            "the live local must resolve through its current telescope"
        );
        assert!(
            tc.infer_cache.entries == 1,
            "a live local result must retain its exact dependency slice"
        );
        tc.drop_local();
        assert!(
            matches!(
                tc.infer(&local, 0),
                Err(Stop::Reject(RejectClass::UnknownFVar, _))
            ),
            "a closed scope must not receive a stale cached local type"
        );
        let replacement_type = Expr::sort(Level::one());
        tc.adopt_local(id, replacement_type.clone());
        assert!(
            tc.infer(&local, 0).expect("replacement local infers") == replacement_type,
            "reusing an fvar identifier with another binding must not hit the old type"
        );

        let mut whnf_tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let let_value = Expr::sort(Level::zero());
        let let_id = whnf_tc.fresh_fvar(Expr::sort(Level::one()), Some(let_value.clone()));
        let let_local = Expr::fvar(let_id.clone());
        assert!(
            whnf_tc
                .whnf_public(&let_local, 0)
                .expect("live let local reduces")
                == let_value,
            "the live let local must normalize to its bound value"
        );
        whnf_tc.drop_local();
        whnf_tc.adopt_local(let_id, Expr::sort(Level::one()));
        assert!(
            whnf_tc
                .whnf_public(&let_local, 0)
                .expect("replacement non-let local normalizes")
                == let_local,
            "a changed binding must not reuse the former let-local normal form"
        );
    }

    #[test]
    fn fvar_cache_dependencies_survive_unrelated_binders_but_not_rebinding() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let zero = Expr::sort(Level::zero());
        let let_id = tc.fresh_fvar(Expr::sort(Level::one()), Some(zero.clone()));
        let let_local = Expr::fvar(let_id.clone());

        assert!(
            tc.def_eq_public(&let_local, &zero, 0)
                .expect("the let local reduces to its value"),
            "the initial positive result is the fact being cached"
        );
        let after_first = tc.consumption().steps_used;
        assert!(
            tc.positive_def_eq_cache.entries == 1,
            "the fvar-bearing positive result must retain a dependency snapshot"
        );

        tc.adopt_local(
            FVarId(Name::str(Name::anonymous(), "unrelated")),
            Expr::sort(Level::zero()),
        );
        assert!(
            tc.def_eq_public(&let_local, &zero, 0)
                .expect("an unrelated binder preserves the cached fact"),
            "unrelated telescope growth must not invalidate the dependency slice"
        );
        assert!(
            tc.consumption().steps_used - after_first == 1,
            "a valid positive-equivalence hit charges only the KR-300 entry hook"
        );

        tc.drop_local();
        tc.adopt_local(let_id.clone(), Expr::sort(Level::one()));
        assert!(
            !tc.def_eq_public(&let_local, &zero, 0)
                .expect("rebinding must force an ordinary comparison"),
            "shadowing an fvar identifier with another binding must invalidate the old fact"
        );

        tc.drop_local();
        let restored_generation_steps = tc.consumption().steps_used;
        assert!(
            tc.def_eq_public(&let_local, &zero, 0)
                .expect("dropping the shadow restores the original binding"),
            "revealing a still-live prior generation must recover its cached fact"
        );
        assert!(
            tc.consumption().steps_used - restored_generation_steps == 1,
            "the restored generation must hit the original cache row"
        );

        tc.drop_local();
        tc.adopt_local(let_id, Expr::sort(Level::one()));
        assert!(
            !tc.def_eq_public(&let_local, &zero, 0)
                .expect("reusing a closed identifier must force an ordinary comparison"),
            "a new generation must not borrow the closed binding's cached fact"
        );

        let type_id = FVarId(Name::str(Name::anonymous(), "type_dependency"));
        let value_id = FVarId(Name::str(Name::anonymous(), "transitive"));
        let value_local = Expr::fvar(value_id.clone());
        tc.adopt_local(type_id.clone(), Expr::sort(Level::zero()));
        tc.adopt_local(value_id, Expr::fvar(type_id.clone()));
        tc.infer(&value_local, 0)
            .expect("the dependent local infers under its original context");
        let rows_before_shadow = tc.infer_cache.entries;
        tc.adopt_local(type_id, Expr::sort(Level::one()));
        tc.infer(&value_local, 0)
            .expect("the dependent local still infers under the shadow");
        assert!(
            tc.infer_cache.entries == rows_before_shadow,
            "changing a transitive dependency must replace the dead row with the live generation"
        );
        assert!(
            tc.infer_cache
                .buckets
                .get(&value_local.data().0)
                .is_some_and(|bucket| bucket.iter().all(|entry| {
                    dependencies_are_live(&entry.dependencies, &tc.locals, &tc.local_positions)
                })),
            "the retained row must name only the current transitive generations"
        );
    }

    #[test]
    fn dead_generations_cannot_saturate_a_live_fvar_cache_bucket() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let mut result_cache = ExprResultCache::bounded(4, 4);
        let mut defeq_cache = PositiveDefEqCache::bounded(4, 4);
        let id = FVarId(Name::str(Name::anonymous(), "rebound"));
        let local = Expr::fvar(id.clone());
        let type_ = Expr::sort(Level::zero());

        for generation in 0..5 {
            tc.adopt_local(id.clone(), type_.clone());
            result_cache.insert(
                local.clone(),
                type_.clone(),
                &tc.locals,
                &tc.local_positions,
            );
            defeq_cache.insert(
                local.clone(),
                type_.clone(),
                &tc.locals,
                &tc.local_positions,
            );
            assert!(
                result_cache.get(&local, &tc.locals, &tc.local_positions) == Some(type_.clone()),
                "generation {generation} must retain its currently live result"
            );
            assert!(
                defeq_cache.contains(&local, &type_, &tc.locals, &tc.local_positions),
                "generation {generation} must retain its currently live equality"
            );
            tc.drop_local();
        }

        assert!(
            result_cache.entries == 1
                && result_cache.local_dependency_cells == 1
                && defeq_cache.entries == 1
                && defeq_cache.local_dependency_cells == 1,
            "four dead generations must be reclaimed before the collision ceiling is applied"
        );
    }

    #[test]
    fn dependency_discovery_visits_a_shared_expression_dag_once() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let id = FVarId(Name::str(Name::anonymous(), "shared"));
        let mut shared = Expr::fvar(id.clone());
        tc.adopt_local(id.clone(), Expr::sort(Level::zero()));

        // Its expanded tree has more nodes than the per-entry ceiling, while
        // the immutable DAG contains only the leaf plus these applications.
        for _ in 0..17 {
            shared = Expr::app(shared.clone(), shared);
        }
        let mut nodes_left = TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES_PER_ENTRY;
        let dependencies =
            local_dependencies(&[&shared], &tc.locals, &tc.local_positions, &mut nodes_left)
                .expect("shared nodes are scanned by allocation, not expanded as a tree");

        assert!(
            dependencies
                == vec![LocalDependency {
                    id,
                    generation: tc.locals[0].generation.expect("live generation"),
                }],
            "the shared graph must retain its one real local dependency"
        );
        assert!(
            TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES_PER_ENTRY - nodes_left == 18,
            "the dependency walk must charge each immutable allocation exactly once"
        );
    }

    #[test]
    fn dependency_discovery_never_aliases_distinct_packed_hash_collisions() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let left_id = FVarId(Name::num_overflowing(Name::anonymous(), u64::MAX - 1));
        let right_id = FVarId(Name::num_overflowing(Name::anonymous(), u64::MAX));
        let left = Expr::fvar(left_id.clone());
        let right = Expr::fvar(right_id.clone());
        assert!(left != right, "the colliding locals must remain distinct");
        assert!(
            left.data() == right.data(),
            "overflowing numeric name components provide a real packed-data collision"
        );
        tc.adopt_local(left_id.clone(), Expr::sort(Level::zero()));
        tc.adopt_local(right_id.clone(), Expr::sort(Level::zero()));

        let application = Expr::app(left, right);
        let mut nodes_left = TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES_PER_ENTRY;
        let dependencies = local_dependencies(
            &[&application],
            &tc.locals,
            &tc.local_positions,
            &mut nodes_left,
        )
        .expect("a packed-data collision cannot suppress dependency discovery");

        assert!(dependencies.len() == 2);
        assert!(
            dependencies
                .iter()
                .any(|dependency| dependency.id == left_id)
        );
        assert!(
            dependencies
                .iter()
                .any(|dependency| dependency.id == right_id)
        );
    }

    #[test]
    fn cache_saturation_is_a_miss_and_preserves_the_uncached_verdict() {
        let env = Environment::new();
        let (pi, redex, sort) = closed_cache_fixture();

        let mut cached = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let cached_infer = cached.infer(&pi, 0).expect("cached-mode inference");
        let cached_defeq = cached
            .def_eq_public(&redex, &sort, 0)
            .expect("cached-mode defeq");

        let mut saturated = TypeChecker::new(&env, &[], Budget::DEFAULT);
        saturated.infer_cache = ExprResultCache::bounded(0, 0);
        saturated.infer_only_cache = ExprResultCache::bounded(0, 0);
        saturated.whnf_core_cache = ExprResultCache::bounded(0, 0);
        saturated.whnf_cache = ExprResultCache::bounded(0, 0);
        saturated.positive_def_eq_cache = PositiveDefEqCache::bounded(0, 0);
        saturated.instantiate_cache = InstantiateCache::bounded(0, 0);
        saturated.instantiate_lparams_cache = InstantiateLParamsCache::bounded(0, 0);
        let saturated_infer = saturated.infer(&pi, 0).expect("uncached inference");
        let saturated_defeq = saturated
            .def_eq_public(&redex, &sort, 0)
            .expect("uncached defeq");

        assert!(
            saturated_infer == cached_infer && saturated_defeq == cached_defeq,
            "a full cache may cost more work, but cannot change a completed verdict"
        );
        assert!(
            saturated.infer_cache.entries == 0
                && saturated.infer_only_cache.entries == 0
                && saturated.whnf_core_cache.entries == 0
                && saturated.whnf_cache.entries == 0
                && saturated.positive_def_eq_cache.entries == 0
                && saturated.instantiate_cache.entries == 0
                && saturated.instantiate_lparams_cache.entries == 0,
            "zero-capacity caches must remain bounded at zero"
        );

        let mut fvar_saturated = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let id = FVarId(Name::str(Name::anonymous(), "bounded"));
        let local = Expr::fvar(id.clone());
        let local_type = Expr::sort(Level::zero());
        fvar_saturated.adopt_local(id, local_type.clone());
        fvar_saturated.infer_cache.local_dependency_cells =
            TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS;
        assert!(
            fvar_saturated
                .infer(&local, 0)
                .expect("fvar inference still runs when its cache partition is full")
                == local_type,
            "fvar cache saturation must degrade to ordinary inference"
        );
        assert!(
            fvar_saturated.infer_cache.entries == 0,
            "the separate fvar ceiling must refuse another retained dependency slice"
        );

        let oversized_scan = Expr::mdata(fln_core::options::KVMap::default(), local);
        let mut one_node_left = 1;
        assert!(
            local_dependencies(
                &[&oversized_scan],
                &fvar_saturated.locals,
                &fvar_saturated.local_positions,
                &mut one_node_left,
            )
            .is_none(),
            "dependency discovery must refuse a hostile expression beyond its node ceiling"
        );

        let mut scan_refused = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let scan_id = FVarId(Name::str(Name::anonymous(), "scan_refused"));
        let scan_local = Expr::fvar(scan_id.clone());
        let scan_key = Expr::mdata(fln_core::options::KVMap::default(), scan_local);
        scan_refused.adopt_local(scan_id, Expr::sort(Level::zero()));
        scan_refused.infer_cache.local_dependency_scan_nodes =
            TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_SCAN_NODES - 1;
        scan_refused.infer_cache.insert(
            scan_key.clone(),
            scan_key.clone(),
            &scan_refused.locals,
            &scan_refused.local_positions,
        );
        assert!(
            scan_refused
                .infer_cache
                .dependency_scan_refusals
                .contains_key(&scan_key.data().0),
            "an over-limit key must retain a bounded reuse-refusal marker"
        );
        scan_refused.infer_cache.local_dependency_scan_nodes = 0;
        scan_refused.infer_cache.insert(
            scan_key.clone(),
            scan_key,
            &scan_refused.locals,
            &scan_refused.local_positions,
        );
        assert!(
            scan_refused.infer_cache.entries == 0
                && scan_refused.infer_cache.local_dependency_scan_nodes == 0,
            "a refused hash may suppress only another cache attempt, without rescanning or a row"
        );

        let mut cell_refused = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let left_id = FVarId(Name::str(Name::anonymous(), "cell_left"));
        let right_id = FVarId(Name::str(Name::anonymous(), "cell_right"));
        let left = Expr::fvar(left_id.clone());
        let right = Expr::fvar(right_id.clone());
        let pair = Expr::app(left.clone(), right.clone());
        cell_refused.adopt_local(left_id, Expr::sort(Level::zero()));
        cell_refused.adopt_local(right_id, Expr::sort(Level::zero()));
        cell_refused.infer_cache.local_dependency_cells =
            TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS - 1;
        cell_refused.infer_cache.insert(
            pair.clone(),
            pair.clone(),
            &cell_refused.locals,
            &cell_refused.local_positions,
        );
        cell_refused.positive_def_eq_cache.local_dependency_cells =
            TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS - 1;
        cell_refused.positive_def_eq_cache.insert(
            left.clone(),
            right.clone(),
            &cell_refused.locals,
            &cell_refused.local_positions,
        );
        let result_scans = cell_refused.infer_cache.local_dependency_scan_nodes;
        let defeq_scans = cell_refused
            .positive_def_eq_cache
            .local_dependency_scan_nodes;
        cell_refused.infer_cache.local_dependency_cells = 0;
        cell_refused.positive_def_eq_cache.local_dependency_cells = 0;
        cell_refused.infer_cache.insert(
            pair.clone(),
            pair,
            &cell_refused.locals,
            &cell_refused.local_positions,
        );
        cell_refused.positive_def_eq_cache.insert(
            left,
            right,
            &cell_refused.locals,
            &cell_refused.local_positions,
        );
        assert!(
            cell_refused.infer_cache.entries == 0
                && cell_refused.positive_def_eq_cache.entries == 0
                && cell_refused.infer_cache.local_dependency_scan_nodes == result_scans
                && cell_refused
                    .positive_def_eq_cache
                    .local_dependency_scan_nodes
                    == defeq_scans,
            "a dependency-cell refusal must not rescan after capacity later becomes available"
        );

        let mut refusal_full = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let full_id = FVarId(Name::str(Name::anonymous(), "refusal_full"));
        let full_local = Expr::fvar(full_id.clone());
        refusal_full.adopt_local(full_id, Expr::sort(Level::zero()));
        refusal_full.infer_cache = ExprResultCache::bounded(1, 4);
        refusal_full.positive_def_eq_cache = PositiveDefEqCache::bounded(1, 4);
        refusal_full
            .infer_cache
            .dependency_scan_refusals
            .insert(u64::MAX, ());
        refusal_full
            .positive_def_eq_cache
            .dependency_scan_refusals
            .insert((u64::MAX, u64::MAX), ());
        refusal_full.infer_cache.insert(
            full_local.clone(),
            full_local.clone(),
            &refusal_full.locals,
            &refusal_full.local_positions,
        );
        refusal_full.positive_def_eq_cache.insert(
            full_local.clone(),
            Expr::mdata(fln_core::options::KVMap::default(), full_local),
            &refusal_full.locals,
            &refusal_full.local_positions,
        );
        assert!(
            refusal_full.infer_cache.entries == 0
                && refusal_full.infer_cache.local_dependency_scan_nodes == 0
                && refusal_full.positive_def_eq_cache.entries == 0
                && refusal_full
                    .positive_def_eq_cache
                    .local_dependency_scan_nodes
                    == 0,
            "a full refusal table must stop new scans instead of retrying unrecorded keys"
        );

        let mut too_many = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let mut wide = Expr::sort(Level::zero());
        for index in 0..=TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCIES_PER_ENTRY {
            let id = FVarId(Name::num(
                Name::str(Name::anonymous(), "wide"),
                index as u64,
            ));
            let local = Expr::fvar(id.clone());
            too_many.adopt_local(id, Expr::sort(Level::zero()));
            wide = Expr::app(wide, local);
        }
        too_many.infer_cache.insert(
            wide.clone(),
            wide,
            &too_many.locals,
            &too_many.local_positions,
        );
        assert!(
            too_many.infer_cache.entries == 0,
            "a row with too many distinct dependencies must be an uncached fallback"
        );
    }

    #[test]
    fn hostile_collision_candidates_never_alias_and_saturation_stays_a_miss() {
        let env = Environment::new();
        let (pi, redex, sort) = closed_cache_fixture();
        let unrelated = Expr::sort(Level::one());

        let mut baseline = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let expected_infer = baseline.infer(&pi, 0).expect("baseline inference");
        let expected_whnf = baseline
            .whnf_public(&redex, 0)
            .expect("baseline normalization");
        let expected_defeq = baseline
            .def_eq_public(&redex, &sort, 0)
            .expect("baseline defeq");

        let mut collided = TypeChecker::new(&env, &[], Budget::DEFAULT);
        collided.infer_cache = ExprResultCache::bounded(1, 1);
        collided.infer_cache.buckets.insert(
            pi.data().0,
            vec![ExprResultCacheEntry {
                key: unrelated.clone(),
                value: unrelated.clone(),
                dependencies: Vec::new(),
            }],
        );
        collided.infer_cache.entries = 1;
        collided.whnf_cache = ExprResultCache::bounded(1, 1);
        collided.whnf_cache.buckets.insert(
            redex.data().0,
            vec![ExprResultCacheEntry {
                key: unrelated.clone(),
                value: unrelated.clone(),
                dependencies: Vec::new(),
            }],
        );
        collided.whnf_cache.entries = 1;
        collided.positive_def_eq_cache = PositiveDefEqCache::bounded(1, 1);
        collided.positive_def_eq_cache.buckets.insert(
            PositiveDefEqCache::packed_key(&redex, &sort),
            vec![PositiveDefEqCacheEntry {
                left: unrelated.clone(),
                right: pi.clone(),
                dependencies: Vec::new(),
            }],
        );
        collided.positive_def_eq_cache.entries = 1;

        // These deliberately malformed buckets model distinct structural
        // candidates landing under the same packed key. A lookup must perform
        // the structural comparison, refuse the false candidate, and then
        // degrade to uncached work because the one-row bucket is saturated.
        assert!(
            collided.infer(&pi, 0).expect("collided inference") == expected_infer,
            "a packed-key collision must not alias an unrelated inferred type"
        );
        assert!(
            collided
                .whnf_public(&redex, 0)
                .expect("collided normalization")
                == expected_whnf,
            "a packed-key collision must not alias an unrelated normal form"
        );
        assert!(
            collided
                .def_eq_public(&redex, &sort, 0)
                .expect("collided defeq")
                == expected_defeq,
            "a packed-key collision must not manufacture or hide definitional equality"
        );
        assert!(
            collided.infer_cache.entries == 1
                && collided.whnf_cache.entries == 1
                && collided.positive_def_eq_cache.entries == 1,
            "full collision buckets must stay bounded instead of growing during fallback work"
        );
    }

    #[test]
    fn one_less_step_with_cache_reuse_is_still_typed_exhaustion_and_is_never_cached() {
        let env = Environment::new();
        let (pi, _, _) = closed_cache_fixture();
        let mut baseline = TypeChecker::new(&env, &[], Budget::DEFAULT);
        baseline.infer(&pi, 0).expect("first inference");
        baseline.infer(&pi, 0).expect("cached inference");
        let exact_steps = baseline.consumption().steps_used;
        assert!(
            exact_steps > 1,
            "the fixture must consume a nontrivial budget"
        );

        let exact_budget = Budget::DEFAULT.narrowed(exact_steps, Budget::DEFAULT.depth);
        let mut exact = TypeChecker::new(&env, &[], exact_budget);
        exact.infer(&pi, 0).expect("exact first inference");
        exact.infer(&pi, 0).expect("exact cached inference");
        assert!(
            exact.consumption().steps_used == exact_steps,
            "the exact allowance must reproduce the measured cached sequence"
        );

        let short_budget =
            Budget::DEFAULT.narrowed(exact_steps.saturating_sub(1), Budget::DEFAULT.depth);
        let mut short = TypeChecker::new(&env, &[], short_budget);
        short.infer(&pi, 0).expect("first inference fits");
        assert!(
            matches!(
                short.infer(&pi, 0),
                Err(Stop::Exhausted(ExhaustionReason::Steps))
            ),
            "one less than the exact cached sequence is Inconclusive at the public boundary"
        );
        assert!(
            short.positive_def_eq_cache.entries == 0,
            "an interrupted sequence cannot manufacture a positive defeq cache row"
        );
    }

    fn empty_recursor(name: &str) -> fln_env::constants::RecursorVal {
        fln_env::constants::RecursorVal {
            base: fln_env::constants::ConstantVal {
                name: Name::str(Name::anonymous(), name),
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            all: Vec::new(),
            num_params: 0,
            num_indices: 0,
            num_motives: 0,
            num_minors: 0,
            rules: Vec::new(),
            k: false,
            is_unsafe: false,
        }
    }

    #[test]
    fn decoded_recursor_rows_are_matched_by_name_not_artifact_position() {
        let left = empty_recursor("Left.rec");
        let right = empty_recursor("Right.rec");
        let generated = [left.clone(), right.clone()];

        assert!(
            compare_recursor_sets(&generated, &[right.clone(), left]).is_ok(),
            "module row order is not block order"
        );
        assert!(matches!(
            compare_recursor_sets(&generated, &[right.clone(), right]),
            Err(Stop::Reject(RejectClass::BlockMismatch, message))
                if message.contains("Left.rec")
        ));
    }

    #[test]
    fn nested_parameter_canonicalization_distinguishes_internal_binders_from_field_locals() {
        let sort = Expr::sort(Level::zero());
        let eta_expanded_block_param = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            sort.clone(),
            Expr::app(
                Expr::bvar(2).expect("block parameter under a field local and lambda"),
                Expr::bvar(0).expect("lambda-bound argument"),
            ),
            BinderInfo::Default,
        );
        let canonical = lower_param_expr(&eta_expanded_block_param, 1, 1, 0, 0)
            .expect("an internal binder is not a loose field-local capture");
        let expected = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            sort.clone(),
            Expr::app(
                Expr::bvar(1).expect("canonical block parameter under the lambda"),
                Expr::bvar(0).expect("lambda-bound argument"),
            ),
            BinderInfo::Default,
        );
        assert!(canonical == expected);

        let captures_field_local = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            sort,
            Expr::app(
                Expr::bvar(1).expect("field local under the lambda"),
                Expr::bvar(0).expect("lambda-bound argument"),
            ),
            BinderInfo::Default,
        );
        assert!(matches!(
            lower_param_expr(&captures_field_local, 1, 1, 0, 0),
            Err(Stop::Reject(RejectClass::BlockMismatch, message))
                if message.contains("cannot contain local variables")
        ));
    }
}
