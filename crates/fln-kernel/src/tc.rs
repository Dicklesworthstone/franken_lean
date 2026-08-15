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
// are bounded. Four structural candidates per packed-data-and-telescope-length
// bucket plus four cross-scope candidates cap one lookup at twelve structural
// comparisons; 65,536 rows and 65,536 cross-scope pointers cap reuse. The scope
// partition prevents the Reference's common 32-bit hash
// collisions from crowding out useful rows, while dependency validation on the
// bounded cross-scope index retains reuse across unrelated binder churn.
// Fvar-bearing rows may retain at most 262,144
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
// Saturation normally stops admitting new rows. The WHNF-core cache is the one
// exception: proof phases can produce more than 65,536 distinct stable spines,
// so it retires a full generation as one deterministic unit before admitting
// the next row. The live row/cell bounds stay unchanged, and retiring reusable
// facts can only cause recomputation -- never manufacture a result or turn an
// interrupted computation into a completed one.
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
    position: usize,
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
        let position = *local_positions.get(&id)?;
        let local = locals.get(position)?;
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
            position,
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
            .is_some_and(|position| *position == dependency.position)
            && locals.get(dependency.position).is_some_and(|local| {
                local.id == dependency.id && local.generation == Some(dependency.generation)
            })
    })
}

fn dependencies_are_present(dependencies: &[LocalDependency], locals: &[LocalDecl]) -> bool {
    dependencies.iter().all(|dependency| {
        locals.get(dependency.position).is_some_and(|local| {
            local.id == dependency.id && local.generation == Some(dependency.generation)
        })
    })
}

struct ExprResultCacheEntry {
    key: Expr,
    value: Expr,
    dependencies: Vec<LocalDependency>,
}

type ExprResultCrossScopeEntry = (Expr, usize);

struct ExprResultCache {
    buckets: HashMap<(u64, usize), Vec<ExprResultCacheEntry>>,
    cross_scope: HashMap<u64, Vec<ExprResultCrossScopeEntry>>,
    cross_scope_entries: usize,
    dependency_scan_refusals: HashMap<(u64, usize), ()>,
    entries: usize,
    local_dependency_cells: usize,
    local_dependency_scan_nodes: usize,
    max_entries: usize,
    max_bucket_entries: usize,
    rollover_on_saturation: bool,
}

impl ExprResultCache {
    fn new() -> Self {
        Self::bounded(
            TYPE_CHECKER_CACHE_MAX_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
        )
    }

    fn rolling() -> Self {
        let mut cache = Self::new();
        cache.rollover_on_saturation = true;
        cache
    }

    fn bounded(max_entries: usize, max_bucket_entries: usize) -> Self {
        Self {
            buckets: HashMap::new(),
            cross_scope: HashMap::new(),
            cross_scope_entries: 0,
            dependency_scan_refusals: HashMap::new(),
            entries: 0,
            local_dependency_cells: 0,
            local_dependency_scan_nodes: 0,
            max_entries,
            max_bucket_entries,
            rollover_on_saturation: false,
        }
    }

    fn get(
        &self,
        key: &Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) -> Option<Expr> {
        let packed = (key.data().0, locals.len());
        if let Some(value) = self.buckets.get(&packed).and_then(|bucket| {
            bucket.iter().find_map(|entry| {
                (entry.key == *key
                    && dependencies_are_live(&entry.dependencies, locals, local_positions))
                .then(|| entry.value.clone())
            })
        }) {
            return Some(value);
        }
        for (candidate, alternate_scope) in self.cross_scope.get(&key.data().0)? {
            if candidate != key {
                continue;
            }
            if let Some(value) = self
                .buckets
                .get(&(key.data().0, *alternate_scope))
                .and_then(|bucket| {
                    bucket.iter().find_map(|entry| {
                        (entry.key == *key
                            && dependencies_are_live(&entry.dependencies, locals, local_positions))
                        .then(|| entry.value.clone())
                    })
                })
            {
                return Some(value);
            }
        }
        None
    }

    fn record_cross_scope(&mut self, key: &Expr, scope: usize) {
        let has_capacity = self.cross_scope_entries < self.max_entries;
        if let Some(bucket) = self.cross_scope.get_mut(&key.data().0) {
            if bucket
                .iter()
                .any(|(candidate, existing_scope)| candidate == key && *existing_scope == scope)
            {
                return;
            }
            let oldest_same_key = bucket.iter().position(|(candidate, _)| candidate == key);
            if has_capacity && bucket.len() < self.max_bucket_entries {
                bucket.push((key.clone(), scope));
                self.cross_scope_entries += 1;
            } else if let Some(index) = oldest_same_key {
                bucket[index] = (key.clone(), scope);
            }
        } else if has_capacity && self.max_bucket_entries > 0 {
            self.cross_scope
                .insert(key.data().0, vec![(key.clone(), scope)]);
            self.cross_scope_entries += 1;
        }
    }

    fn insert(
        &mut self,
        key: Expr,
        value: Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) {
        let packed = (key.data().0, locals.len());
        let prior_scopes = self
            .cross_scope
            .get(&key.data().0)
            .map(|bucket| {
                bucket
                    .iter()
                    .filter_map(|(candidate, scope)| (candidate == &key).then_some(*scope))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        for prior_scope in prior_scopes {
            if prior_scope == locals.len() {
                continue;
            }
            let prior_packed = (key.data().0, prior_scope);
            if let Some(bucket) = self.buckets.get_mut(&prior_packed) {
                let before = bucket.len();
                let mut removed_cells = 0_usize;
                bucket.retain(|entry| {
                    let present = dependencies_are_present(&entry.dependencies, locals);
                    if !present {
                        removed_cells += entry.dependencies.len();
                    }
                    present
                });
                self.entries -= before - bucket.len();
                self.local_dependency_cells -= removed_cells;
            }
            if self.buckets.get(&prior_packed).is_some_and(Vec::is_empty) {
                self.buckets.remove(&prior_packed);
            }
        }
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            let before = bucket.len();
            let mut removed_cells = 0_usize;
            bucket.retain(|entry| {
                let present = dependencies_are_present(&entry.dependencies, locals);
                if !present {
                    removed_cells += entry.dependencies.len();
                }
                present
            });
            self.entries -= before - bucket.len();
            self.local_dependency_cells -= removed_cells;
        }
        if self.buckets.get(&packed).is_some_and(Vec::is_empty) {
            self.buckets.remove(&packed);
        }
        if self.max_bucket_entries == 0 {
            return;
        }
        let replacement = self.buckets.get(&packed).and_then(|bucket| {
            (bucket.len() >= self.max_bucket_entries)
                .then(|| bucket.iter().position(|entry| entry.key == key))
                .flatten()
        });
        if self
            .buckets
            .get(&packed)
            .is_some_and(|bucket| bucket.len() >= self.max_bucket_entries)
            && replacement.is_none()
        {
            return;
        }
        if self.entries >= self.max_entries && replacement.is_none() {
            if !self.rollover_on_saturation || self.max_entries == 0 {
                return;
            }
            self.buckets.clear();
            self.cross_scope.clear();
            self.cross_scope_entries = 0;
            self.entries = 0;
            self.local_dependency_cells = 0;
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
        let replaced_dependency_count = replacement
            .and_then(|index| self.buckets.get(&packed)?.get(index))
            .map_or(0, |entry| entry.dependencies.len());
        if self
            .local_dependency_cells
            .saturating_sub(replaced_dependency_count)
            .checked_add(dependency_count)
            .is_none_or(|cells| cells > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS)
        {
            if self.dependency_scan_refusals.len() < self.max_entries {
                self.dependency_scan_refusals.insert(packed, ());
            }
            return;
        }
        self.record_cross_scope(&key, locals.len());
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if let Some(existing) = bucket
                .iter_mut()
                .find(|entry| entry.key == key && entry.dependencies == dependencies)
            {
                existing.value = value;
                return;
            }
            if let Some(index) = replacement {
                let Some(replaced) = bucket.get_mut(index) else {
                    return;
                };
                self.local_dependency_cells = self
                    .local_dependency_cells
                    .saturating_sub(replaced.dependencies.len())
                    .saturating_add(dependency_count);
                *replaced = ExprResultCacheEntry {
                    key,
                    value,
                    dependencies,
                };
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
    buckets: HashMap<(u64, u64, usize), Vec<PositiveDefEqCacheEntry>>,
    cross_scope: HashMap<(u64, u64), Vec<PositiveDefEqCrossScopeEntry>>,
    cross_scope_entries: usize,
    dependency_scan_refusals: HashMap<(u64, u64, usize), ()>,
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

type PositiveDefEqCrossScopeEntry = (Expr, Expr, usize);

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
            cross_scope: HashMap::new(),
            cross_scope_entries: 0,
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

    fn scoped_key(left: &Expr, right: &Expr, local_count: usize) -> (u64, u64, usize) {
        let (left, right) = Self::packed_key(left, right);
        (left, right, local_count)
    }

    fn contains(
        &self,
        left: &Expr,
        right: &Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) -> bool {
        let matches = |bucket: &Vec<PositiveDefEqCacheEntry>| {
            bucket.iter().any(|entry| {
                ((entry.left == *left && entry.right == *right)
                    || (entry.left == *right && entry.right == *left))
                    && dependencies_are_live(&entry.dependencies, locals, local_positions)
            })
        };
        if self
            .buckets
            .get(&Self::scoped_key(left, right, locals.len()))
            .is_some_and(matches)
        {
            return true;
        }
        let packed = Self::packed_key(left, right);
        let Some(candidates) = self.cross_scope.get(&packed) else {
            return false;
        };
        candidates
            .iter()
            .filter_map(|(cached_left, cached_right, scope)| {
                ((cached_left == left && cached_right == right)
                    || (cached_left == right && cached_right == left))
                    .then_some(*scope)
            })
            .any(|alternate_scope| {
                self.buckets
                    .get(&(packed.0, packed.1, alternate_scope))
                    .is_some_and(|bucket| {
                        bucket.iter().any(|entry| {
                            ((entry.left == *left && entry.right == *right)
                                || (entry.left == *right && entry.right == *left))
                                && dependencies_are_live(
                                    &entry.dependencies,
                                    locals,
                                    local_positions,
                                )
                        })
                    })
            })
    }

    fn record_cross_scope(&mut self, left: &Expr, right: &Expr, scope: usize) {
        let packed = Self::packed_key(left, right);
        let has_capacity = self.cross_scope_entries < self.max_entries;
        if let Some(bucket) = self.cross_scope.get_mut(&packed) {
            if bucket
                .iter()
                .any(|(cached_left, cached_right, existing_scope)| {
                    ((cached_left == left && cached_right == right)
                        || (cached_left == right && cached_right == left))
                        && *existing_scope == scope
                })
            {
                return;
            }
            let oldest_same_pair = bucket.iter().position(|(cached_left, cached_right, _)| {
                (cached_left == left && cached_right == right)
                    || (cached_left == right && cached_right == left)
            });
            if has_capacity && bucket.len() < self.max_bucket_entries {
                bucket.push((left.clone(), right.clone(), scope));
                self.cross_scope_entries += 1;
            } else if let Some(index) = oldest_same_pair {
                bucket[index] = (left.clone(), right.clone(), scope);
            }
        } else if has_capacity && self.max_bucket_entries > 0 {
            self.cross_scope
                .insert(packed, vec![(left.clone(), right.clone(), scope)]);
            self.cross_scope_entries += 1;
        }
    }

    fn insert(
        &mut self,
        left: Expr,
        right: Expr,
        locals: &[LocalDecl],
        local_positions: &HashMap<FVarId, usize>,
    ) {
        let packed = Self::scoped_key(&left, &right, locals.len());
        let identity = Self::packed_key(&left, &right);
        let prior_scopes = self
            .cross_scope
            .get(&identity)
            .map(|bucket| {
                bucket
                    .iter()
                    .filter_map(|(cached_left, cached_right, scope)| {
                        ((cached_left == &left && cached_right == &right)
                            || (cached_left == &right && cached_right == &left))
                            .then_some(*scope)
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        for prior_scope in prior_scopes {
            if prior_scope == locals.len() {
                continue;
            }
            let prior_packed = (identity.0, identity.1, prior_scope);
            if let Some(bucket) = self.buckets.get_mut(&prior_packed) {
                let before = bucket.len();
                let mut removed_cells = 0_usize;
                bucket.retain(|entry| {
                    let present = dependencies_are_present(&entry.dependencies, locals);
                    if !present {
                        removed_cells += entry.dependencies.len();
                    }
                    present
                });
                self.entries -= before - bucket.len();
                self.local_dependency_cells -= removed_cells;
            }
            if self.buckets.get(&prior_packed).is_some_and(Vec::is_empty) {
                self.buckets.remove(&prior_packed);
            }
        }
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            let before = bucket.len();
            let mut removed_cells = 0_usize;
            bucket.retain(|entry| {
                let present = dependencies_are_present(&entry.dependencies, locals);
                if !present {
                    removed_cells += entry.dependencies.len();
                }
                present
            });
            self.entries -= before - bucket.len();
            self.local_dependency_cells -= removed_cells;
        }
        if self.buckets.get(&packed).is_some_and(Vec::is_empty) {
            self.buckets.remove(&packed);
        }
        let replacement = self.buckets.get(&packed).and_then(|bucket| {
            (bucket.len() >= self.max_bucket_entries)
                .then(|| {
                    bucket.iter().position(|entry| {
                        (entry.left == left && entry.right == right)
                            || (entry.left == right && entry.right == left)
                    })
                })
                .flatten()
        });
        if (self.entries >= self.max_entries && replacement.is_none())
            || self.max_bucket_entries == 0
            || (self
                .buckets
                .get(&packed)
                .is_some_and(|bucket| bucket.len() >= self.max_bucket_entries)
                && replacement.is_none())
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
        let replaced_dependency_count = replacement
            .and_then(|index| self.buckets.get(&packed)?.get(index))
            .map_or(0, |entry| entry.dependencies.len());
        if self
            .local_dependency_cells
            .saturating_sub(replaced_dependency_count)
            .checked_add(dependency_count)
            .is_none_or(|cells| cells > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS)
        {
            if self.dependency_scan_refusals.len() < self.max_entries {
                self.dependency_scan_refusals.insert(packed, ());
            }
            return;
        }
        self.record_cross_scope(&left, &right, locals.len());
        if let Some(bucket) = self.buckets.get_mut(&packed) {
            if bucket.iter().any(|entry| {
                ((entry.left == left && entry.right == right)
                    || (entry.left == right && entry.right == left))
                    && entry.dependencies == dependencies
            }) {
                return;
            }
            if let Some(index) = replacement {
                let Some(replaced) = bucket.get_mut(index) else {
                    return;
                };
                self.local_dependency_cells = self
                    .local_dependency_cells
                    .saturating_sub(replaced.dependencies.len())
                    .saturating_add(dependency_count);
                *replaced = PositiveDefEqCacheEntry {
                    left,
                    right,
                    dependencies,
                };
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

struct InstantiateRevContext {
    values: Vec<Expr>,
    id: u32,
}

/// Cross-call cache for batched beta/opening substitutions. Contexts intern
/// the complete argument vector once, then all recursive source subgraphs can
/// reuse results reached from a different top-level body under that vector.
/// Full structural equality is the authority after every packed prefilter.
struct InstantiateRevContextCache {
    contexts: HashMap<(u64, usize), Vec<InstantiateRevContext>>,
    context_count: usize,
    results: HashMap<(u32, u64, u32), Vec<(Expr, Expr)>>,
    entries: usize,
    argument_cells: usize,
    max_contexts: usize,
    max_entries: usize,
    max_bucket_entries: usize,
    max_argument_cells: usize,
}

impl InstantiateRevContextCache {
    fn new() -> Self {
        Self::bounded(
            TYPE_CHECKER_CACHE_MAX_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_BUCKET_ENTRIES,
            TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCY_CELLS,
        )
    }

    fn bounded(max_entries: usize, max_bucket_entries: usize, max_argument_cells: usize) -> Self {
        Self {
            contexts: HashMap::new(),
            context_count: 0,
            results: HashMap::new(),
            entries: 0,
            argument_cells: 0,
            max_contexts: max_entries.min(4_096),
            max_entries,
            max_bucket_entries,
            max_argument_cells,
        }
    }

    fn context_key(values: &[Expr]) -> (u64, usize) {
        let hash = values
            .iter()
            .fold(0x9e37_79b9_7f4a_7c15_u64, |state, value| {
                state.rotate_left(11) ^ value.data().0.wrapping_add(0x517c_c1b7_2722_0a95)
            });
        (hash, values.len())
    }

    fn context_id(&mut self, values: &[Expr]) -> Option<u32> {
        if values.is_empty() || values.len() > TYPE_CHECKER_CACHE_MAX_LOCAL_DEPENDENCIES_PER_ENTRY {
            return None;
        }
        let key = Self::context_key(values);
        if let Some(id) = self.contexts.get(&key).and_then(|bucket| {
            bucket
                .iter()
                .find_map(|context| (context.values == values).then_some(context.id))
        }) {
            return Some(id);
        }
        if self.context_count >= self.max_contexts
            || self.max_bucket_entries == 0
            || self
                .contexts
                .get(&key)
                .is_some_and(|bucket| bucket.len() >= self.max_bucket_entries)
            || self
                .argument_cells
                .checked_add(values.len())
                .is_none_or(|cells| cells > self.max_argument_cells)
        {
            return None;
        }
        let id = u32::try_from(self.context_count).ok()?;
        self.contexts
            .entry(key)
            .or_default()
            .push(InstantiateRevContext {
                values: values.to_vec(),
                id,
            });
        self.context_count += 1;
        self.argument_cells += values.len();
        Some(id)
    }

    fn get(&self, context: u32, source: &Expr, bound: u32) -> Option<Expr> {
        self.results
            .get(&(context, source.data().0, bound))?
            .iter()
            .find_map(|(candidate, result)| (candidate == source).then(|| result.clone()))
    }

    fn insert(&mut self, context: u32, source: Expr, bound: u32, result: Expr) {
        let packed = (context, source.data().0, bound);
        if let Some(bucket) = self.results.get_mut(&packed) {
            if let Some((_, existing)) = bucket
                .iter_mut()
                .find(|(candidate, _)| candidate == &source)
            {
                *existing = result;
                return;
            }
            if self.entries >= self.max_entries || bucket.len() >= self.max_bucket_entries {
                return;
            }
            bucket.push((source, result));
            self.entries += 1;
            return;
        }
        if self.entries >= self.max_entries || self.max_bucket_entries == 0 {
            return;
        }
        self.results.insert(packed, vec![(source, result)]);
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
    /// Pinned `equiv_manager` companion for the equal-regular-head shortcut.
    /// A failed argument comparison is not a negative verdict: it only tells
    /// lazy delta to unfold this pair. Retaining that fact prevents a repeated
    /// proof-producing argument comparison from being re-run at every retry.
    regular_app_def_eq_failure_cache: PositiveDefEqCache,
    instantiate_cache: InstantiateCache,
    instantiate_rev_context_cache: InstantiateRevContextCache,
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
            whnf_core_cache: ExprResultCache::rolling(),
            whnf_cache: ExprResultCache::new(),
            positive_def_eq_cache: PositiveDefEqCache::new(),
            regular_app_def_eq_failure_cache: PositiveDefEqCache::new(),
            instantiate_cache: InstantiateCache::new(),
            instantiate_rev_context_cache: InstantiateRevContextCache::new(),
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
        // Post-order heap walk. Recursing one frame per node would abort a
        // legal deep open term before `step` could turn it into Inconclusive
        // if the host stack is smaller than Budget::depth (FL-INV-07).
        enum Op {
            Enter {
                e: Expr,
                k: u32,
                subst: Expr,
                depth: u32,
            },
            Finish {
                e: Expr,
                k: u32,
                subst: Expr,
                lifted: Option<Expr>,
            },
        }
        let lookup = |done: &HashMap<(usize, u32, usize), Expr>,
                      child: &Expr,
                      k: u32,
                      subst: &Expr|
         -> KResult<Expr> {
            done.get(&(child.allocation_identity(), k, subst.allocation_identity()))
                .cloned()
                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
        };
        let mut done: HashMap<(usize, u32, usize), Expr> = HashMap::new();
        let mut stack = vec![Op::Enter {
            e: e.clone(),
            k,
            subst: subst.clone(),
            depth,
        }];
        while let Some(op) = stack.pop() {
            match op {
                Op::Enter { e, k, subst, depth } => {
                    self.step(depth)?;
                    let key = (e.allocation_identity(), k, subst.allocation_identity());
                    if done.contains_key(&key) {
                        continue;
                    }
                    if let Some(cached) = self.instantiate_cache.get(&e, k, &subst) {
                        done.insert(key, cached);
                        continue;
                    }
                    if e.loose_bvar_range() <= k {
                        done.insert(key, e.clone());
                        continue;
                    }
                    match e.node() {
                        ExprNode::BVar { idx } => {
                            let result = if *idx == k {
                                subst.clone()
                            } else if *idx > k {
                                Expr::bvar(idx - 1).unwrap_or_else(|_| e.clone())
                            } else {
                                e.clone()
                            };
                            if result != e {
                                self.instantiate_cache.insert(
                                    e.clone(),
                                    k,
                                    subst.clone(),
                                    result.clone(),
                                );
                            }
                            done.insert(key, result);
                        }
                        ExprNode::App { f, a } => {
                            let (f, a) = (f.clone(), a.clone());
                            stack.push(Op::Finish {
                                e,
                                k,
                                subst: subst.clone(),
                                lifted: None,
                            });
                            stack.push(Op::Enter {
                                e: a,
                                k,
                                subst: subst.clone(),
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: f,
                                k,
                                subst,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::Lam { .. } | ExprNode::ForallE { .. } | ExprNode::LetE { .. } => {
                            let lifted = subst
                                .lift_loose(0, 1)
                                .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
                            let next_k = k
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let (ty, body, value) = match e.node() {
                                ExprNode::Lam {
                                    binder_type, body, ..
                                }
                                | ExprNode::ForallE {
                                    binder_type, body, ..
                                } => (Some(binder_type.clone()), body.clone(), None),
                                ExprNode::LetE {
                                    type_, value, body, ..
                                } => (Some(type_.clone()), body.clone(), Some(value.clone())),
                                _ => unreachable!("matched binder above"),
                            };
                            stack.push(Op::Finish {
                                e,
                                k,
                                subst: subst.clone(),
                                lifted: Some(lifted.clone()),
                            });
                            stack.push(Op::Enter {
                                e: body,
                                k: next_k,
                                subst: lifted,
                                depth: depth + 1,
                            });
                            if let Some(value) = value {
                                stack.push(Op::Enter {
                                    e: value,
                                    k,
                                    subst: subst.clone(),
                                    depth: depth + 1,
                                });
                            }
                            if let Some(ty) = ty {
                                stack.push(Op::Enter {
                                    e: ty,
                                    k,
                                    subst,
                                    depth: depth + 1,
                                });
                            }
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            let inner = expr.clone();
                            stack.push(Op::Finish {
                                e,
                                k,
                                subst: subst.clone(),
                                lifted: None,
                            });
                            stack.push(Op::Enter {
                                e: inner,
                                k,
                                subst,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::FVar { .. }
                        | ExprNode::MVar { .. }
                        | ExprNode::Sort { .. }
                        | ExprNode::Const { .. }
                        | ExprNode::Lit { .. } => {
                            done.insert(key, e);
                        }
                    }
                }
                Op::Finish {
                    e,
                    k,
                    subst,
                    lifted,
                } => {
                    let key = (e.allocation_identity(), k, subst.allocation_identity());
                    if done.contains_key(&key) {
                        continue;
                    }
                    let result = match e.node() {
                        ExprNode::App { f, a } => {
                            Expr::app(lookup(&done, f, k, &subst)?, lookup(&done, a, k, &subst)?)
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let lifted = lifted
                                .as_ref()
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let next_k = k
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::lam(
                                binder_name.clone(),
                                lookup(&done, binder_type, k, &subst)?,
                                lookup(&done, body, next_k, lifted)?,
                                *binder_info,
                            )
                        }
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let lifted = lifted
                                .as_ref()
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let next_k = k
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::forall_e(
                                binder_name.clone(),
                                lookup(&done, binder_type, k, &subst)?,
                                lookup(&done, body, next_k, lifted)?,
                                *binder_info,
                            )
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            let lifted = lifted
                                .as_ref()
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let next_k = k
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::let_e(
                                decl_name.clone(),
                                lookup(&done, type_, k, &subst)?,
                                lookup(&done, value, k, &subst)?,
                                lookup(&done, body, next_k, lifted)?,
                                *non_dep,
                            )
                        }
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), lookup(&done, expr, k, &subst)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, lookup(&done, expr, k, &subst)?),
                        _ => e.clone(),
                    };
                    if result != e {
                        self.instantiate_cache
                            .insert(e.clone(), k, subst.clone(), result.clone());
                    }
                    done.insert(key, result);
                }
            }
        }
        done.get(&(e.allocation_identity(), k, subst.allocation_identity()))
            .cloned()
            .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
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
        let context = self.instantiate_rev_context_cache.context_id(fvars);
        let mut cache = InstantiateRevCache::new();
        self.instantiate_rev_cached(e, fvars, bound, depth, &mut cache, context)
    }

    fn instantiate_rev_cached(
        &mut self,
        e: &Expr,
        fvars: &[Expr],
        bound: u32,
        depth: u32,
        cache: &mut InstantiateRevCache,
        context: Option<u32>,
    ) -> KResult<Expr> {
        // Post-order heap walk. Batched beta and telescope opening feed this
        // the same deep spines `instantiate` just stopped recursing on
        // (FL-INV-07). Persistent cache still stores every computed node so a
        // repeated call pays only the entry `step`.
        enum Op {
            Enter { e: Expr, bound: u32, depth: u32 },
            Finish { e: Expr, bound: u32 },
        }
        let lookup =
            |done: &HashMap<(usize, u32), Expr>, child: &Expr, bound: u32| -> KResult<Expr> {
                done.get(&(child.allocation_identity(), bound))
                    .cloned()
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
            };
        let count =
            u32::try_from(fvars.len()).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
        let mut done: HashMap<(usize, u32), Expr> = HashMap::new();
        let mut stack = vec![Op::Enter {
            e: e.clone(),
            bound,
            depth,
        }];
        while let Some(op) = stack.pop() {
            match op {
                Op::Enter { e, bound, depth } => {
                    self.step(depth)?;
                    let key = (e.allocation_identity(), bound);
                    if done.contains_key(&key) {
                        continue;
                    }
                    let cached = match context {
                        Some(context) => self.instantiate_rev_context_cache.get(context, &e, bound),
                        None => cache.get(&e, bound),
                    };
                    if let Some(cached) = cached {
                        done.insert(key, cached);
                        continue;
                    }
                    if e.loose_bvar_range() <= bound || fvars.is_empty() {
                        done.insert(key, e);
                        continue;
                    }
                    match e.node() {
                        ExprNode::BVar { idx } if *idx >= bound => {
                            let relative = *idx - bound;
                            let result = if relative < count {
                                fvars[(count - 1 - relative) as usize]
                                    .lift_loose(0, bound)
                                    .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
                            } else {
                                Expr::bvar(idx - count)
                                    .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
                            };
                            match context {
                                Some(context) => self.instantiate_rev_context_cache.insert(
                                    context,
                                    e.clone(),
                                    bound,
                                    result.clone(),
                                ),
                                None => cache.insert(e.clone(), bound, result.clone()),
                            }
                            done.insert(key, result);
                        }
                        ExprNode::BVar { .. }
                        | ExprNode::FVar { .. }
                        | ExprNode::MVar { .. }
                        | ExprNode::Sort { .. }
                        | ExprNode::Const { .. }
                        | ExprNode::Lit { .. } => {
                            match context {
                                Some(context) => self.instantiate_rev_context_cache.insert(
                                    context,
                                    e.clone(),
                                    bound,
                                    e.clone(),
                                ),
                                None => cache.insert(e.clone(), bound, e.clone()),
                            }
                            done.insert(key, e);
                        }
                        ExprNode::App { f, a } => {
                            let (f, a) = (f.clone(), a.clone());
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: a,
                                bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: f,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let (ty, body) = (binder_type.clone(), body.clone());
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: body,
                                bound: next_bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let (ty, value, body) = (type_.clone(), value.clone(), body.clone());
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: body,
                                bound: next_bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: value,
                                bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            let inner = expr.clone();
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: inner,
                                bound,
                                depth: depth + 1,
                            });
                        }
                    }
                }
                Op::Finish { e, bound } => {
                    let key = (e.allocation_identity(), bound);
                    if done.contains_key(&key) {
                        continue;
                    }
                    let result = match e.node() {
                        ExprNode::App { f, a } => {
                            Expr::app(lookup(&done, f, bound)?, lookup(&done, a, bound)?)
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::lam(
                                binder_name.clone(),
                                lookup(&done, binder_type, bound)?,
                                lookup(&done, body, next_bound)?,
                                *binder_info,
                            )
                        }
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::forall_e(
                                binder_name.clone(),
                                lookup(&done, binder_type, bound)?,
                                lookup(&done, body, next_bound)?,
                                *binder_info,
                            )
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::let_e(
                                decl_name.clone(),
                                lookup(&done, type_, bound)?,
                                lookup(&done, value, bound)?,
                                lookup(&done, body, next_bound)?,
                                *non_dep,
                            )
                        }
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), lookup(&done, expr, bound)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, lookup(&done, expr, bound)?),
                        _ => e.clone(),
                    };
                    match context {
                        Some(context) => self.instantiate_rev_context_cache.insert(
                            context,
                            e.clone(),
                            bound,
                            result.clone(),
                        ),
                        None => cache.insert(e.clone(), bound, result.clone()),
                    }
                    done.insert(key, result);
                }
            }
        }
        done.get(&(e.allocation_identity(), bound))
            .cloned()
            .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
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
        // Post-order heap walk. Recursing one frame per node would abort a
        // legal deep type with universe parameters before `step` could turn
        // it into Inconclusive if the host stack is smaller than
        // Budget::depth (FL-INV-07).
        enum Op {
            Enter { e: Expr, depth: u32 },
            Finish { e: Expr },
        }
        let lookup = |done: &HashMap<usize, Expr>, child: &Expr| -> KResult<Expr> {
            done.get(&child.allocation_identity())
                .cloned()
                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
        };
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut stack = vec![Op::Enter {
            e: e.clone(),
            depth,
        }];
        while let Some(op) = stack.pop() {
            match op {
                Op::Enter { e, depth } => {
                    self.step(depth)?;
                    let key = e.allocation_identity();
                    if done.contains_key(&key) {
                        continue;
                    }
                    if !e.has_level_param() {
                        done.insert(key, e);
                        continue;
                    }
                    if let Some(cached) = self.instantiate_lparams_cache.get(&e, params, levels) {
                        done.insert(key, cached);
                        continue;
                    }
                    match e.node() {
                        ExprNode::Sort { level } => {
                            let result = Expr::sort(substitute_level(level, params, levels));
                            if result != e {
                                self.instantiate_lparams_cache.insert(
                                    e.clone(),
                                    params,
                                    levels,
                                    result.clone(),
                                );
                            }
                            done.insert(key, result);
                        }
                        ExprNode::Const { name, levels: ls } => {
                            let result = Expr::const_(
                                name.clone(),
                                ls.iter()
                                    .map(|level| substitute_level(level, params, levels))
                                    .collect(),
                            );
                            if result != e {
                                self.instantiate_lparams_cache.insert(
                                    e.clone(),
                                    params,
                                    levels,
                                    result.clone(),
                                );
                            }
                            done.insert(key, result);
                        }
                        ExprNode::App { f, a } => {
                            let (f, a) = (f.clone(), a.clone());
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: a,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: f,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            let (ty, body) = (binder_type.clone(), body.clone());
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: body,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            let (ty, value, body) = (type_.clone(), value.clone(), body.clone());
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: body,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: value,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            let inner = expr.clone();
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: inner,
                                depth: depth + 1,
                            });
                        }
                        _ => {
                            done.insert(key, e);
                        }
                    }
                }
                Op::Finish { e } => {
                    let key = e.allocation_identity();
                    if done.contains_key(&key) {
                        continue;
                    }
                    let result = match e.node() {
                        ExprNode::App { f, a } => Expr::app(lookup(&done, f)?, lookup(&done, a)?),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            lookup(&done, binder_type)?,
                            lookup(&done, body)?,
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            lookup(&done, binder_type)?,
                            lookup(&done, body)?,
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
                            lookup(&done, type_)?,
                            lookup(&done, value)?,
                            lookup(&done, body)?,
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), lookup(&done, expr)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, lookup(&done, expr)?),
                        _ => e.clone(),
                    };
                    if result != e {
                        self.instantiate_lparams_cache.insert(
                            e.clone(),
                            params,
                            levels,
                            result.clone(),
                        );
                    }
                    done.insert(key, result);
                }
            }
        }
        done.get(&e.allocation_identity())
            .cloned()
            .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
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
        self.whnf_core_mode(e, depth, false)
    }

    /// The pin's defeq projection pre-pass uses `cheap_proj = true`: reduce a
    /// projection scrutinee without delta so `a.i =?= b.i` can compare `a` and
    /// `b` before either side opens an expensive definition. Cheap results are
    /// not mixed into the full-WHNF cache, so this mode is reserved for the
    /// matching-projection case rather than every defeq pair.
    fn whnf_core_for_defeq(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.whnf_core_mode(e, depth, true)
    }

    fn whnf_core_mode(&mut self, e: &Expr, depth: u32, cheap_proj: bool) -> KResult<Expr> {
        self.step(depth)?;
        if !cheap_proj
            && let Some(cached) = self
                .whnf_core_cache
                .get(e, &self.locals, &self.local_positions)
        {
            return Ok(cached);
        }
        // Peel mdata / zeta / let-bound fvars on the heap. The seed elaborator
        // can now emit a 400-deep let spine; recursing one frame per zeta
        // would abort the check that found it (FL-INV-07). App/proj tail
        // reductions continue the same loop.
        let mut current = e.clone();
        let mut depth = depth;
        let result = loop {
            if !cheap_proj
                && current != *e
                && let Some(cached) =
                    self.whnf_core_cache
                        .get(&current, &self.locals, &self.local_positions)
            {
                break cached;
            }
            match current.node() {
                ExprNode::MData { expr, .. } => {
                    current = expr.clone();
                    depth += 1;
                    self.step(depth)?;
                }
                ExprNode::FVar { id } => match self.find_local(id).and_then(|d| d.value.clone()) {
                    // KR-203: a let-bound fvar unfolds to its value.
                    Some(value) => {
                        current = value;
                        depth += 1;
                        self.step(depth)?;
                    }
                    None => break current.clone(),
                },
                ExprNode::LetE { value, body, .. } => {
                    // KR-203 zeta.
                    let value = value.clone();
                    let body = body.clone();
                    current = self.instantiate(&body, 0, &value, depth + 1)?;
                    depth += 1;
                    self.step(depth)?;
                }
                ExprNode::App { .. } => {
                    // Collect the spine, whnf the head, then KR-202 batched beta.
                    let (head0, args) = app_spine(&current);
                    let head = self.whnf_core_mode(&head0, depth + 1, cheap_proj)?;
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
                        let mut reduced =
                            self.instantiate_rev(&body, &args[..consumed], 0, depth + 1)?;
                        for arg in &args[consumed..] {
                            reduced = Expr::app(reduced, arg.clone());
                        }
                        current = reduced;
                        depth += 1;
                        self.step(depth)?;
                    } else if head == head0 {
                        // KR-205: the head is stable — try quotient computation, then
                        // inductive iota, on the original application.
                        match self.reduce_recursor(&current, depth + 1)? {
                            Some(reduced) => {
                                current = reduced;
                                depth += 1;
                                self.step(depth)?;
                            }
                            None => break current.clone(),
                        }
                    } else {
                        // The head changed (let-fvar zeta, mdata strip): rebuild and
                        // continue, as the pin re-enters whnf_core on the update.
                        let mut rebuilt = head;
                        for arg in args {
                            rebuilt = Expr::app(rebuilt, arg);
                        }
                        current = rebuilt;
                        depth += 1;
                        self.step(depth)?;
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
                    let scrutinee = if cheap_proj {
                        self.whnf_core_mode(expr, depth + 1, true)?
                    } else {
                        self.whnf(&expr.clone(), depth + 1)?
                    };
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
                        Some(field) => {
                            current = field;
                            depth += 1;
                            self.step(depth)?;
                        }
                        None => break Expr::proj(struct_name, idx, scrutinee),
                    }
                }
                _ => break current.clone(),
            }
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
        if !cheap_proj && (result != *e || cache_identity) {
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
                        // `BigNat::pow` panics past MAX_LIMBS. A generous
                        // step budget can pay the charge and still be unable
                        // to represent the result; that is exhaustion, not
                        // an invariant failure (FL-INV-07).
                        va.checked_pow(u32::try_from(exp).unwrap_or(u32::MAX))
                            .ok_or_else(|| {
                                self.used.steps_used = self.budget.steps.saturating_add(1);
                                Stop::Exhausted(ExhaustionReason::Steps)
                            })?
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
                // Include the left operand's limbs: `count/64 + 1` alone
                // under-charges a wide value and can pay a shift whose
                // result still exceeds the bignum limb ceiling.
                self.charge_bulk(count / 64 + 1 + limbs_a)?;
                // `BigNat::shl` panics past MAX_LIMBS. Charge can succeed
                // on a generous budget while the result is still
                // unrepresentable; that is typed exhaustion, never abort.
                match va.checked_shl(count) {
                    Some(shifted) => shifted,
                    None => {
                        self.used.steps_used = self.budget.steps.saturating_add(1);
                        return Err(Stop::Exhausted(ExhaustionReason::Steps));
                    }
                }
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
        // KR-302 binder congruence. Matching Π/λ telescopes are a heap loop
        // (`is_def_eq_binding`); one recursive frame per binder used to abort
        // on a legal 400-deep spine (FL-INV-07).
        match (t.node(), s.node()) {
            (ExprNode::Lam { .. }, ExprNode::Lam { .. })
            | (ExprNode::ForallE { .. }, ExprNode::ForallE { .. }) => {
                Ok(Some(self.is_def_eq_binding(t, s, depth)?))
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
        let cheap_projection_pair = matches!(
            (t.node(), s.node()),
            (
                ExprNode::Proj { idx: left, .. },
                ExprNode::Proj { idx: right, .. },
            ) if left == right
        );
        let tn = if cheap_projection_pair {
            self.whnf_core_for_defeq(t, depth + 1)?
        } else {
            self.whnf_core(t, depth + 1)?
        };
        let sn = if cheap_projection_pair {
            self.whnf_core_for_defeq(s, depth + 1)?
        } else {
            self.whnf_core(s, depth + 1)?
        };
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
        // lazy_delta_proj_reduction): same-index projections first compare
        // their scrutinees by lazy delta, then try constructor-field reduction
        // on both sides before the ordinary scrutinee-defeq fallback.
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
            if self.lazy_delta_proj_reduction(e1, e2, *i1, depth + 1)? {
                return Ok(true);
            }
        }
        // The cheap pre-pass deliberately leaves projection scrutinees short
        // of full WHNF. Retry both sides with the ordinary reducer only after
        // the scrutinee-level shortcut above has had its chance, exactly as at
        // the pin. A changed pair restarts the complete ladder.
        let tn_full = self.whnf_core(&tn, depth + 1)?;
        let sn_full = self.whnf_core(&sn, depth + 1)?;
        if tn_full != tn || sn_full != sn {
            return self.is_def_eq_core(&tn_full, &sn_full, depth + 1);
        }
        // KR-311 application congruence. The pin is one app per recursive
        // call (fn then arg). A 400-deep spine is now a legal WHNF residue;
        // walking it on the call stack would abort (FL-INV-07). Peel both
        // spines, charge one `step` per extra layer so Budget::depth still
        // binds, then compare head and arguments left-to-right. Failure
        // falls through to eta, same as a false conjunct at the pin.
        if matches!(
            (tn.node(), sn.node()),
            (ExprNode::App { .. }, ExprNode::App { .. })
        ) {
            let (head1, args1) = app_spine(&tn);
            let (head2, args2) = app_spine(&sn);
            if args1.len() == args2.len() {
                let mut layer = depth;
                let mut ok = true;
                for extra in 1..args1.len() {
                    layer = depth
                        .checked_add(extra as u32)
                        .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                    self.step(layer)?;
                }
                let child_depth = layer
                    .checked_add(1)
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                if !self.is_def_eq(&head1, &head2, child_depth)? {
                    ok = false;
                }
                if ok {
                    for (a1, a2) in args1.iter().zip(&args2) {
                        if !self.is_def_eq(a1, a2, child_depth)? {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    return Ok(true);
                }
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

    /// Pin `is_def_eq_binding` (type_checker.cpp:690). Matching Π/λ telescopes
    /// are a loop, not a recursive type-checker call chain. Convert can now
    /// inject a 400-deep binder spine; walking one frame per binder would
    /// abort (FL-INV-07). Peel while both sides keep the same binder kind,
    /// charge one `step` per extra layer so `Budget::depth` still binds,
    /// compare instantiated domains, then defeq the remaining bodies under
    /// the accumulated locals. A failing domain is decisive, same as the
    /// pin's early `return false`.
    fn is_def_eq_binding(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let saved_locals = self.locals.len();
        let result = (|| {
            let kind_is_lam = matches!(t.node(), ExprNode::Lam { .. });
            let mut left = t.clone();
            let mut right = s.clone();
            let mut subst: Vec<Expr> = Vec::new();
            let mut opened: u32 = 0;
            let mut layer = depth;

            loop {
                let (t_dom, t_body, s_dom, s_body) = match (left.node(), right.node()) {
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
                    ) if kind_is_lam => (t1.clone(), b1.clone(), t2.clone(), b2.clone()),
                    (
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
                    ) if !kind_is_lam => (t1.clone(), b1.clone(), t2.clone(), b2.clone()),
                    _ => break,
                };

                if opened > 0 {
                    layer = depth
                        .checked_add(opened)
                        .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                    self.step(layer)?;
                }

                let child_depth = layer
                    .checked_add(1)
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;

                // Pin skips the domain comparison when the uninstantiated
                // domains are already the same object. After the same
                // `instantiate_rev` they remain equal, so the skip is only
                // an optimization. We still instantiate the right domain
                // for the local's type.
                let instantiated_s = if t_dom != s_dom {
                    let var_t = self.instantiate_rev(&t_dom, &subst, 0, child_depth)?;
                    let var_s = self.instantiate_rev(&s_dom, &subst, 0, child_depth)?;
                    if !self.is_def_eq(&var_t, &var_s, child_depth)? {
                        return Ok(false);
                    }
                    var_s
                } else {
                    self.instantiate_rev(&s_dom, &subst, 0, child_depth)?
                };

                // Pin only allocates a local when a body mentions a loose
                // bvar; otherwise it pushes `g_dont_care`. Always allocating
                // an fvar is equivalent: a closed body ignores the substitute.
                let id = self.fresh_fvar(instantiated_s, None);
                subst.push(Expr::fvar(id));
                opened = opened
                    .checked_add(1)
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                left = t_body;
                right = s_body;
            }

            let child_depth = layer
                .checked_add(1)
                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
            let opened_left = self.instantiate_rev(&left, &subst, 0, child_depth)?;
            let opened_right = self.instantiate_rev(&right, &subst, 0, child_depth)?;
            self.is_def_eq(&opened_left, &opened_right, child_depth)
        })();
        self.truncate_locals(saved_locals);
        result
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
            // Cheap projection reduction belongs to the matching-projection
            // pre-pass. A delta-unfolded body uses ordinary cached WHNF: making
            // every retry cheap discards reusable non-projection normal forms
            // and can turn a small proof into repeated full-tree walks.
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

    /// Pinned `lazy_delta_proj_reduction`: unfold the projection scrutinees
    /// lazily. If that alone does not prove equality, reduce both constructor
    /// fields at the requested index and compare the fields; only then compare
    /// the residual scrutinees themselves.
    fn lazy_delta_proj_reduction(
        &mut self,
        t: Expr,
        s: Expr,
        idx: u64,
        depth: u32,
    ) -> KResult<bool> {
        let (t, s) = match self.lazy_delta(t, s, depth + 1)? {
            LazyDelta::Decided(true) => return Ok(true),
            LazyDelta::Decided(false) => return Ok(false),
            LazyDelta::Stuck(t, s) => (t, s),
        };
        let placeholder = Name::anonymous();
        if let (Some(t_field), Some(s_field)) = (
            self.reduce_proj(&placeholder, idx, &t),
            self.reduce_proj(&placeholder, idx, &s),
        ) {
            return self.is_def_eq(&t_field, &s_field, depth + 1);
        }
        self.is_def_eq(&t, &s, depth + 1)
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
        if self
            .regular_app_def_eq_failure_cache
            .contains(t, s, &self.locals, &self.local_positions)
        {
            return Ok(false);
        }
        for (t_arg, s_arg) in t_args.iter().zip(&s_args) {
            if !self.is_def_eq(t_arg, s_arg, depth)? {
                self.regular_app_def_eq_failure_cache.insert(
                    t.clone(),
                    s.clone(),
                    &self.locals,
                    &self.local_positions,
                );
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

    /// KR-312 (function half): `t` a lambda, `s` not — eta-expand `s` through
    /// its Π-type and retry. The pin is one expansion per recursive
    /// `is_def_eq` (`type_checker.cpp:778`). A 400-deep λ against a
    /// non-lambda is now a legal pair; composing one expansion with
    /// binder-congruence would abort (FL-INV-07). Flatten that composition:
    /// peel `t`'s λ spine against successive WHNF Πs of `s`, compare
    /// instantiated domains, apply `s` to the opened locals, then defeq the
    /// remainders. A failing domain is decisive, same as the pin.
    fn try_eta(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        if !matches!(t.node(), ExprNode::Lam { .. }) || matches!(s.node(), ExprNode::Lam { .. }) {
            return Ok(false);
        }
        let saved_locals = self.locals.len();
        let result = (|| {
            let mut remaining_t = t.clone();
            let mut remaining_s = s.clone();
            let mut subst: Vec<Expr> = Vec::new();
            let mut opened: u32 = 0;
            let mut layer = depth;

            while let ExprNode::Lam {
                binder_type: t_dom,
                body: t_body,
                ..
            } = remaining_t.node()
            {
                let (t_dom, t_body) = (t_dom.clone(), t_body.clone());

                if opened > 0 {
                    layer = depth
                        .checked_add(opened)
                        .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                    self.step(layer)?;
                }
                let child_depth = layer
                    .checked_add(1)
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;

                let s_type = match self.infer_only(&remaining_s, layer) {
                    Ok(ty) => ty,
                    Err(Stop::Reject(..)) => return Ok(false),
                    Err(stop) => return Err(stop),
                };
                let s_type = self.whnf(&s_type, layer)?;
                let ExprNode::ForallE {
                    binder_type: s_dom, ..
                } = s_type.node()
                else {
                    break;
                };
                let s_dom = s_dom.clone();

                let instantiated_t = self.instantiate_rev(&t_dom, &subst, 0, child_depth)?;
                if instantiated_t != s_dom
                    && !self.is_def_eq(&instantiated_t, &s_dom, child_depth)?
                {
                    return Ok(false);
                }

                let id = self.fresh_fvar(s_dom, None);
                let fv = Expr::fvar(id);
                subst.push(fv.clone());
                remaining_s = Expr::app(remaining_s, fv);
                remaining_t = t_body;
                opened = opened
                    .checked_add(1)
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
            }

            if opened == 0 {
                return Ok(false);
            }
            let child_depth = layer
                .checked_add(1)
                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
            let opened_t = self.instantiate_rev(&remaining_t, &subst, 0, child_depth)?;
            self.is_def_eq(&opened_t, &remaining_s, child_depth)
        })();
        self.truncate_locals(saved_locals);
        result
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
        // Peel MData on the heap. Convert can inject a 400-deep metadata
        // nest; one native frame per KR-111 used to abort the check that
        // found it (FL-INV-07). WHNF already strips these in its loop.
        let mut current = e.clone();
        let mut depth = depth;
        while let ExprNode::MData { expr, .. } = current.node() {
            current = expr.clone();
            depth = depth.saturating_add(1);
            self.step(depth)?;
        }
        let result = match current.node() {
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
            // same judgment as a heap stack so a right-nested argument tree
            // consumes steps instead of native stack (FL-INV-07).
            ExprNode::App { .. } => {
                let result = match mode {
                    InferMode::Check => self.infer_app_check(&current, depth + 1),
                    InferMode::Only => self.infer_app_only(&current, depth + 1),
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
                let result = self.infer_lambda_spine(&current, depth + 1, mode);
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
                let result = self.infer_pi_spine(&current, depth + 1, mode);
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
                let result = self.infer_let_spine(&current, depth + 1, mode);
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
            // KR-111 is the peel above. A leftover wrapper here would mean
            // the while-loop missed a node; keep a typed descent rather
            // than treating that as an invariant failure.
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
    ///
    /// Flattening the left spine does not reach an application nested inside
    /// an argument (`f (f (... a))`). Convert can inject a 400-deep nest;
    /// `infer_core` on that argument used to re-enter this function on the
    /// native stack and abort the check that found it (FL-INV-07). Nested
    /// applications become extra frames on this heap stack. Depth still
    /// grows one unit per nest, so `Budget::depth` binds the same descent.
    fn infer_app_check(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        let mut stack = vec![self.open_checked_app(e, depth, e.clone())?];
        let mut completed: Option<Expr> = None;
        while !stack.is_empty() {
            if let Some(argument_type) = completed.take() {
                self.finish_checked_app_argument(
                    stack
                        .last_mut()
                        .ok_or_else(|| Stop::Fault("application frame vanished".into()))?,
                    argument_type,
                )?;
                continue;
            }
            let frame_done = stack
                .last()
                .is_some_and(|frame| frame.idx >= frame.args.len());
            if frame_done {
                let frame = stack
                    .pop()
                    .ok_or_else(|| Stop::Fault("application frame vanished".into()))?;
                if frame.cache_key != frame.prefix {
                    self.infer_cache.insert(
                        frame.cache_key,
                        frame.function_type.clone(),
                        &self.locals,
                        &self.local_positions,
                    );
                }
                completed = Some(frame.function_type);
                continue;
            }
            let (argument, arg_depth) = {
                let frame = stack
                    .last_mut()
                    .ok_or_else(|| Stop::Fault("application frame vanished".into()))?;
                self.step(frame.depth)?;
                frame.function_type = self.whnf(&frame.function_type, frame.depth)?;
                if !matches!(frame.function_type.node(), ExprNode::ForallE { .. }) {
                    return reject(RejectClass::FunctionExpected, "function expected");
                }
                (frame.args[frame.idx].clone(), frame.depth)
            };
            if peels_to_app(&argument) {
                // Replicate `infer_core_mode`'s prefix so an App argument
                // does not re-enter this function through `infer_core`.
                self.step(arg_depth)?;
                if let Some(cached) =
                    self.infer_cache
                        .get(&argument, &self.locals, &self.local_positions)
                {
                    completed = Some(cached);
                    continue;
                }
                let mut current = argument.clone();
                let mut nested_depth = arg_depth;
                while let ExprNode::MData { expr, .. } = current.node() {
                    current = expr.clone();
                    nested_depth = nested_depth.saturating_add(1);
                    self.step(nested_depth)?;
                }
                let child = self.open_checked_app(&current, nested_depth + 1, argument)?;
                stack.push(child);
                continue;
            }
            let argument_type = self.infer_core(&argument, arg_depth)?;
            completed = Some(argument_type);
        }
        completed.ok_or_else(|| Stop::Fault("application inference finished with no result".into()))
    }

    fn open_checked_app(
        &mut self,
        e: &Expr,
        depth: u32,
        cache_key: Expr,
    ) -> KResult<CheckedAppFrame> {
        let (head, args) = app_spine(e);
        let function_type = self.infer_core(&head, depth)?;
        Ok(CheckedAppFrame {
            args,
            idx: 0,
            prefix: head,
            function_type,
            depth,
            cache_key,
        })
    }

    fn finish_checked_app_argument(
        &mut self,
        frame: &mut CheckedAppFrame,
        argument_type: Expr,
    ) -> KResult<()> {
        let ExprNode::ForallE {
            binder_type, body, ..
        } = frame.function_type.node()
        else {
            return reject(RejectClass::FunctionExpected, "function expected");
        };
        let (binder_type, body) = (binder_type.clone(), body.clone());
        let argument = frame.args[frame.idx].clone();
        if !self.is_def_eq(&argument_type, &binder_type, frame.depth)? {
            return reject(
                RejectClass::TypeMismatch,
                format!(
                    "application type mismatch: argument `{}` has type `{}` but the function expects `{}`{}",
                    brief_expr(&argument, 4),
                    brief_expr(&argument_type, 5),
                    brief_expr(&binder_type, 5),
                    match first_divergence(&argument_type, &binder_type) {
                        Some(divergence) => format!(" (first structural divergence: {divergence})"),
                        None => String::new(),
                    }
                ),
            );
        }
        frame.function_type = self.instantiate(&body, 0, &argument, frame.depth)?;
        frame.prefix = Expr::app(frame.prefix.clone(), argument);
        self.infer_cache.insert(
            frame.prefix.clone(),
            frame.function_type.clone(),
            &self.locals,
            &self.local_positions,
        );
        frame.idx += 1;
        Ok(())
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
        // Post-order heap walk. Closing a deep lambda telescope used to
        // recurse one frame per node; `step` cannot save a host stack smaller
        // than Budget::depth (FL-INV-07).
        enum Op {
            Enter { e: Expr, bound: u32, depth: u32 },
            Finish { e: Expr, bound: u32 },
        }
        let lookup =
            |done: &HashMap<(usize, u32), Expr>, child: &Expr, bound: u32| -> KResult<Expr> {
                done.get(&(child.allocation_identity(), bound))
                    .cloned()
                    .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
            };
        let mut done: HashMap<(usize, u32), Expr> = HashMap::new();
        let mut stack = vec![Op::Enter {
            e: e.clone(),
            bound,
            depth,
        }];
        while let Some(op) = stack.pop() {
            match op {
                Op::Enter { e, bound, depth } => {
                    self.step(depth)?;
                    let key = (e.allocation_identity(), bound);
                    if done.contains_key(&key) {
                        continue;
                    }
                    if !e.has_fvar() || active == 0 {
                        done.insert(key, e);
                        continue;
                    }
                    match e.node() {
                        ExprNode::FVar { id } => {
                            let result = match ordinals.get(id).copied() {
                                Some(ordinal) if ordinal < active => {
                                    let index = bound
                                        .checked_add(active - 1 - ordinal)
                                        .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                                    Expr::bvar(index)
                                        .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
                                }
                                _ => e.clone(),
                            };
                            done.insert(key, result);
                        }
                        ExprNode::App { f, a } => {
                            let (f, a) = (f.clone(), a.clone());
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: a,
                                bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: f,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let (ty, body) = (binder_type.clone(), body.clone());
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: body,
                                bound: next_bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            let (ty, value, body) = (type_.clone(), value.clone(), body.clone());
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: body,
                                bound: next_bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: value,
                                bound,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            let inner = expr.clone();
                            stack.push(Op::Finish { e, bound });
                            stack.push(Op::Enter {
                                e: inner,
                                bound,
                                depth: depth + 1,
                            });
                        }
                        _ => {
                            done.insert(key, e);
                        }
                    }
                }
                Op::Finish { e, bound } => {
                    let key = (e.allocation_identity(), bound);
                    if done.contains_key(&key) {
                        continue;
                    }
                    let result = match e.node() {
                        ExprNode::App { f, a } => {
                            Expr::app(lookup(&done, f, bound)?, lookup(&done, a, bound)?)
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::lam(
                                binder_name.clone(),
                                lookup(&done, binder_type, bound)?,
                                lookup(&done, body, next_bound)?,
                                *binder_info,
                            )
                        }
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::forall_e(
                                binder_name.clone(),
                                lookup(&done, binder_type, bound)?,
                                lookup(&done, body, next_bound)?,
                                *binder_info,
                            )
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            let next_bound = bound
                                .checked_add(1)
                                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))?;
                            Expr::let_e(
                                decl_name.clone(),
                                lookup(&done, type_, bound)?,
                                lookup(&done, value, bound)?,
                                lookup(&done, body, next_bound)?,
                                *non_dep,
                            )
                        }
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), lookup(&done, expr, bound)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, lookup(&done, expr, bound)?),
                        _ => e.clone(),
                    };
                    done.insert(key, result);
                }
            }
        }
        done.get(&(e.allocation_identity(), bound))
            .cloned()
            .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
    }

    fn replace_fvar(&mut self, e: &Expr, id: &FVarId, with: &Expr, depth: u32) -> KResult<Expr> {
        // Post-order heap walk. Zeta of a deep let body used to recurse one
        // frame per node (FL-INV-07).
        enum Op {
            Enter { e: Expr, depth: u32 },
            Finish { e: Expr },
        }
        let lookup = |done: &HashMap<usize, Expr>, child: &Expr| -> KResult<Expr> {
            done.get(&child.allocation_identity())
                .cloned()
                .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
        };
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut stack = vec![Op::Enter {
            e: e.clone(),
            depth,
        }];
        while let Some(op) = stack.pop() {
            match op {
                Op::Enter { e, depth } => {
                    self.step(depth)?;
                    let key = e.allocation_identity();
                    if done.contains_key(&key) {
                        continue;
                    }
                    if !e.has_fvar() {
                        done.insert(key, e);
                        continue;
                    }
                    match e.node() {
                        ExprNode::FVar { id: found } if found == id => {
                            done.insert(key, with.clone());
                        }
                        ExprNode::FVar { .. } => {
                            done.insert(key, e);
                        }
                        ExprNode::App { f, a } => {
                            let (f, a) = (f.clone(), a.clone());
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: a,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: f,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            let (ty, body) = (binder_type.clone(), body.clone());
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: body,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            let (ty, value, body) = (type_.clone(), value.clone(), body.clone());
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: body,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: value,
                                depth: depth + 1,
                            });
                            stack.push(Op::Enter {
                                e: ty,
                                depth: depth + 1,
                            });
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            let inner = expr.clone();
                            stack.push(Op::Finish { e });
                            stack.push(Op::Enter {
                                e: inner,
                                depth: depth + 1,
                            });
                        }
                        _ => {
                            done.insert(key, e);
                        }
                    }
                }
                Op::Finish { e } => {
                    let key = e.allocation_identity();
                    if done.contains_key(&key) {
                        continue;
                    }
                    let result = match e.node() {
                        ExprNode::App { f, a } => Expr::app(lookup(&done, f)?, lookup(&done, a)?),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            lookup(&done, binder_type)?,
                            lookup(&done, body)?,
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            lookup(&done, binder_type)?,
                            lookup(&done, body)?,
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
                            lookup(&done, type_)?,
                            lookup(&done, value)?,
                            lookup(&done, body)?,
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => {
                            Expr::mdata(data.clone(), lookup(&done, expr)?)
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, lookup(&done, expr)?),
                        _ => e.clone(),
                    };
                    done.insert(key, result);
                }
            }
        }
        done.get(&e.allocation_identity())
            .cloned()
            .ok_or(Stop::Exhausted(ExhaustionReason::Depth))
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
        // Pin `infer_proj` (`type_checker.cpp:241-265`): WHNF the remaining
        // constructor telescope before every Π peel (a parameter or field type
        // may be an abbreviation), instantiate only the inductive parameters,
        // and drop an earlier field without a leak check when later field types
        // do not mention it. Instantiating an unused non-Prop field of a Prop
        // structure is what fabricated the leak the pin never sees.
        let ctor_params = ctor.base.level_params.clone();
        let levels = levels.clone();
        let mut telescope =
            self.instantiate_lparams(&ctor.base.type_.clone(), &ctor_params, &levels, depth)?;
        for arg in args.iter().take(ind.num_params as usize) {
            telescope = self.whnf(&telescope, depth)?;
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return reject(RejectClass::InvalidProjection, "constructor arity mismatch");
            };
            let body = body.clone();
            telescope = self.instantiate(&body, 0, arg, depth)?;
        }
        for i in 0..idx {
            telescope = self.whnf(&telescope, depth)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = telescope.node()
            else {
                return reject(
                    RejectClass::InvalidProjection,
                    "projection index out of range",
                );
            };
            let (binder_type, body) = (binder_type.clone(), body.clone());
            if body.has_loose_bvars() {
                if is_prop_type && !self.is_prop(&binder_type, depth)? {
                    return reject(
                        RejectClass::InvalidProjection,
                        "projection would leak data out of Prop",
                    );
                }
                let earlier = Expr::proj(struct_name.clone(), i, scrutinee.clone());
                telescope = self.instantiate(&body, 0, &earlier, depth)?;
            } else {
                telescope = body;
            }
        }
        telescope = self.whnf(&telescope, depth)?;
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
        level_shape_fuel(l, 32)
    }
    fn level_shape_fuel(l: &Level, fuel: usize) -> String {
        use fln_core::level::LevelView;
        // Peel succ towers in a loop: `check_level` now admits 24-bit-legal
        // spines, and a recursive `succ(succ(…))` render of one would abort
        // the rejection that found them (FL-INV-07).
        let mut current = l;
        let mut offset = 0usize;
        while let LevelView::Succ(inner) = current.view() {
            offset = offset.saturating_add(1);
            current = inner;
        }
        if fuel == 0 {
            return if offset == 0 {
                "..".to_string()
            } else {
                format!("succ^{offset}(..)")
            };
        }
        let mut rendered = match current.view() {
            LevelView::Zero => "0".to_string(),
            LevelView::Param(p) => format!("param:{}", p.to_display_string()),
            LevelView::MVar(_) => "mvar".to_string(),
            LevelView::Max(a, b) => format!(
                "max({},{})",
                level_shape_fuel(a, fuel - 1),
                level_shape_fuel(b, fuel - 1)
            ),
            LevelView::IMax(a, b) => format!(
                "imax({},{})",
                level_shape_fuel(a, fuel - 1),
                level_shape_fuel(b, fuel - 1)
            ),
            LevelView::Succ(_) => unreachable!("succ towers are peeled above"),
        };
        for _ in 0..offset {
            rendered = format!("succ({rendered})");
        }
        rendered
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
    // Infer already walks app / let / binder spines on the heap. A mismatch
    // diagnostic that recursed one frame per node would abort the rejection
    // that found them (FL-INV-07). Descend the first differing child in place;
    // siblings that the recursive form only visited after `None` are tried
    // only when the earlier child is equal.
    let mut current_t = t;
    let mut current_s = s;
    let mut path = String::from("root");
    loop {
        if current_t == current_s {
            return None;
        }
        match (current_t.node(), current_s.node()) {
            (ExprNode::BVar { idx: i1 }, ExprNode::BVar { idx: i2 }) => {
                return Some(format!("{path}: #{i1} vs #{i2}"));
            }
            (ExprNode::FVar { id: id1 }, ExprNode::FVar { id: id2 }) => {
                return Some(format!(
                    "{path}: fvar {} vs {}",
                    id1.0.to_display_string(),
                    id2.0.to_display_string()
                ));
            }
            (ExprNode::Sort { level: l1 }, ExprNode::Sort { level: l2 }) => {
                return Some(format!(
                    "{path}: Sort {} vs {}",
                    level_shape(l1),
                    level_shape(l2)
                ));
            }
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
                return if n1 != n2 {
                    Some(format!(
                        "{path}: const {} vs {}",
                        n1.to_display_string(),
                        n2.to_display_string()
                    ))
                } else {
                    levels_diff(&path, l1, l2)
                        .or_else(|| Some(format!("{path}: consts differ undetectably")))
                };
            }
            (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
                if f1 != f2 {
                    current_t = f1;
                    current_s = f2;
                    path.push_str(".fn");
                    continue;
                }
                current_t = a1;
                current_s = a2;
                path.push_str(".arg");
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
                if t1 != t2 {
                    current_t = t1;
                    current_s = t2;
                    path.push_str(".binder_type");
                    continue;
                }
                current_t = b1;
                current_s = b2;
                path.push_str(".body");
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
            ) => {
                if t1 != t2 {
                    current_t = t1;
                    current_s = t2;
                    path.push_str(".let_type");
                    continue;
                }
                if v1 != v2 {
                    current_t = v1;
                    current_s = v2;
                    path.push_str(".let_value");
                    continue;
                }
                current_t = b1;
                current_s = b2;
                path.push_str(".let_body");
            }
            (ExprNode::MData { expr: e1, .. }, ExprNode::MData { expr: e2, .. }) => {
                if e1 == e2 {
                    return Some(format!("{path}: metadata payloads differ"));
                }
                current_t = e1;
                current_s = e2;
                path.push_str(".mdata");
            }
            (ExprNode::MData { expr, .. }, _) => {
                if expr == current_s {
                    return Some(format!("{path}: metadata wrapper on the left only"));
                }
                current_t = expr;
            }
            (_, ExprNode::MData { expr, .. }) => {
                if current_t == expr {
                    return Some(format!("{path}: metadata wrapper on the right only"));
                }
                current_s = expr;
            }
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
                    return Some(format!(
                        "{path}: proj {}.{} vs {}.{}",
                        n1.to_display_string(),
                        i1,
                        n2.to_display_string(),
                        i2
                    ));
                }
                current_t = e1;
                current_s = e2;
                path.push_str(".proj_expr");
            }
            (ExprNode::Lit { literal: l1 }, ExprNode::Lit { literal: l2 }) => {
                return (l1 != l2).then(|| {
                    format!(
                        "{path}: literal {} vs {}",
                        brief_expr(current_t, 1),
                        brief_expr(current_s, 1)
                    )
                });
            }
            (t_node, s_node) => {
                return Some(format!(
                    "{path}: node kind {} vs {}",
                    node_kind_name(t_node),
                    node_kind_name(s_node)
                ));
            }
        }
    }
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

/// True when stripping KR-111 wrappers leaves an application. Checking-mode
/// KR-106 trampolines those arguments onto the heap stack instead of
/// re-entering `infer_core_mode`.
fn peels_to_app(e: &Expr) -> bool {
    let mut current = e;
    while let ExprNode::MData { expr, .. } = current.node() {
        current = expr;
    }
    matches!(current.node(), ExprNode::App { .. })
}

/// One left-spine being typed by the checking-mode KR-106 heap stack.
struct CheckedAppFrame {
    args: Vec<Expr>,
    idx: usize,
    prefix: Expr,
    function_type: Expr,
    depth: u32,
    /// Original term this frame types, including any MData wrappers peeled
    /// to reach the application. Completed nested frames cache under this key.
    cache_key: Expr,
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
///
/// Iterative post-order: a 24-bit-legal succ / max / imax spine of parameters
/// is a legal universe, and a recursive walk of one blows a 2 MiB host stack
/// (FL-INV-07). Subtrees without a parameter are shared unchanged.
fn substitute_level(level: &Level, params: &[Name], levels: &[Level]) -> Level {
    use fln_core::level::LevelView;
    if !level.has_param() {
        return level.clone();
    }
    let mut done: HashMap<Level, Level> = HashMap::new();
    let mut stack = vec![(level.clone(), false)];
    while let Some((current, exit)) = stack.pop() {
        if done.contains_key(&current) {
            continue;
        }
        if !current.has_param() {
            done.insert(current.clone(), current);
            continue;
        }
        if !exit {
            stack.push((current.clone(), true));
            match current.view() {
                LevelView::Succ(inner) => {
                    if inner.has_param() && !done.contains_key(inner) {
                        stack.push((inner.clone(), false));
                    }
                }
                LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                    if b.has_param() && !done.contains_key(b) {
                        stack.push((b.clone(), false));
                    }
                    if a.has_param() && !done.contains_key(a) {
                        stack.push((a.clone(), false));
                    }
                }
                _ => {}
            }
            continue;
        }
        let substituted = match current.view() {
            LevelView::Zero => Level::zero(),
            LevelView::Param(name) => params
                .iter()
                .position(|p| p == name)
                .and_then(|i| levels.get(i))
                .cloned()
                .unwrap_or_else(|| current.clone()),
            LevelView::Succ(inner) => done
                .get(inner)
                .cloned()
                .unwrap_or_else(|| inner.clone())
                .succ()
                .unwrap_or_else(|_| current.clone()),
            LevelView::Max(a, b) => Level::try_smart_max(
                done.get(a).cloned().unwrap_or_else(|| a.clone()),
                done.get(b).cloned().unwrap_or_else(|| b.clone()),
            )
            .unwrap_or_else(|_| current.clone()),
            LevelView::IMax(a, b) => Level::try_kernel_imax(
                done.get(a).cloned().unwrap_or_else(|| a.clone()),
                done.get(b).cloned().unwrap_or_else(|| b.clone()),
            )
            .unwrap_or_else(|_| current.clone()),
            LevelView::MVar(_) => current.clone(),
        };
        done.insert(current, substituted);
    }
    done.get(level).cloned().unwrap_or_else(|| level.clone())
}

fn collect_undeclared_param(level: &Level, declared: &[Name], found: &mut Option<Name>) {
    use fln_core::level::LevelView;
    if found.is_some() || !level.has_param() {
        return;
    }
    let mut stack = vec![level.clone()];
    while let Some(current) = stack.pop() {
        if found.is_some() || !current.has_param() {
            continue;
        }
        match current.view() {
            LevelView::Param(name) => {
                if !declared.contains(name) {
                    *found = Some(name.clone());
                    return;
                }
            }
            LevelView::Succ(inner) => stack.push(inner.clone()),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                stack.push(b.clone());
                stack.push(a.clone());
            }
            _ => {}
        }
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

    /// Pin `instantiate` lifts the substitute by the binders crossed
    /// (`kernel/instantiate.cpp:29`). Without the lift, `(fun x y => x) #0`
    /// and `(fun x y => y) #0` both become `fun y => y`, so defeq would
    /// identify the first projection with the second.
    #[test]
    fn instantiate_lifts_an_open_substitute_under_binders() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let bv = |i: u32| Expr::bvar(i).expect("packs");
        let sort = Expr::sort(Level::zero());
        let name = |s: &str| Name::str(Name::anonymous(), s);
        let inner = Expr::lam(
            name("y"),
            sort.clone(),
            bv(1),
            fln_core::expr::BinderInfo::Default,
        );
        let expected = Expr::lam(
            name("y"),
            sort.clone(),
            bv(1),
            fln_core::expr::BinderInfo::Default,
        );
        assert!(
            tc.instantiate(&inner, 0, &bv(0), 0).expect("instantiates") == expected,
            "replacing #1 under a lambda with #0 must yield #1, not capture #0"
        );

        let fst = Expr::app(
            Expr::lam(
                name("x"),
                sort.clone(),
                Expr::lam(
                    name("y"),
                    sort.clone(),
                    bv(1),
                    fln_core::expr::BinderInfo::Default,
                ),
                fln_core::expr::BinderInfo::Default,
            ),
            bv(0),
        );
        let snd = Expr::app(
            Expr::lam(
                name("x"),
                sort.clone(),
                Expr::lam(
                    name("y"),
                    sort.clone(),
                    bv(0),
                    fln_core::expr::BinderInfo::Default,
                ),
                fln_core::expr::BinderInfo::Default,
            ),
            bv(0),
        );
        let fst_whnf = tc.whnf_public(&fst, 0).expect("beta fst");
        let snd_whnf = tc.whnf_public(&snd, 0).expect("beta snd");
        assert!(
            fst_whnf != snd_whnf,
            "beta of (fun x y => x) #0 must not collapse to (fun x y => y) #0"
        );
        assert!(
            fst_whnf
                == Expr::lam(
                    name("y"),
                    sort.clone(),
                    bv(1),
                    fln_core::expr::BinderInfo::Default,
                ),
            "beta must lift the argument so the first projection stays #1"
        );

        let let_open = Expr::let_e(
            name("x"),
            sort.clone(),
            bv(0),
            Expr::lam(
                name("y"),
                sort.clone(),
                bv(1),
                fln_core::expr::BinderInfo::Default,
            ),
            false,
        );
        assert!(
            tc.whnf_public(&let_open, 0).expect("zeta")
                == Expr::lam(name("y"), sort, bv(1), fln_core::expr::BinderInfo::Default,),
            "zeta must lift the let value under the body's lambda"
        );
    }

    #[test]
    fn instantiate_walks_a_deep_app_nest_without_stack_fault() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let subst = Expr::sort(Level::zero());
        let mut expr = Expr::bvar(0).expect("packs");
        for _ in 0..400 {
            expr = Expr::app(expr, Expr::bvar(1).expect("packs"));
        }
        let result = tc
            .instantiate(&expr, 0, &subst, 0)
            .expect("a 400-app open nest must not stack-fault");
        let mut current = &result;
        let mut apps = 0usize;
        while let ExprNode::App { f, a } = current.node() {
            assert!(
                matches!(a.node(), ExprNode::BVar { idx } if *idx == 0),
                "loose #1 must shift down to #0"
            );
            current = f;
            apps += 1;
        }
        assert!(apps == 400, "the app spine length is preserved");
        assert!(
            current == &subst,
            "the head #0 is replaced by the substitute"
        );
    }

    #[test]
    fn repeated_batched_instantiation_reuses_the_completed_walk() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let bvar = Expr::bvar(0).expect("packs");
        let mut body = bvar.clone();
        for _ in 0..64 {
            body = Expr::app(body, bvar.clone());
        }
        let value = Expr::sort(Level::zero());
        let values = [value];

        let first = tc
            .instantiate_rev(&body, &values, 0, 0)
            .expect("first batched substitution completes");
        let steps_after_first = tc.consumption().steps_used;
        assert!(
            steps_after_first > 1 && tc.instantiate_rev_context_cache.entries > 1,
            "the first call must perform and retain the structural walk"
        );
        let second = tc
            .instantiate_rev(&body, &values, 0, 0)
            .expect("repeated batched substitution completes");
        assert!(
            first == second,
            "cached substitution must preserve the term"
        );
        assert!(
            tc.consumption().steps_used - steps_after_first == 1,
            "a repeated batched substitution must pay only its entry hook"
        );
    }

    #[test]
    fn instantiate_rev_walks_a_deep_app_nest_without_stack_fault() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let subst = Expr::sort(Level::zero());
        let mut expr = Expr::bvar(0).expect("packs");
        for _ in 0..400 {
            expr = Expr::app(expr, Expr::bvar(1).expect("packs"));
        }
        let result = tc
            .instantiate_rev(&expr, std::slice::from_ref(&subst), 0, 0)
            .expect("a 400-app batched nest must not stack-fault");
        let mut current = &result;
        let mut apps = 0usize;
        while let ExprNode::App { f, a } = current.node() {
            assert!(
                matches!(a.node(), ExprNode::BVar { idx } if *idx == 0),
                "loose #1 must shift down by the consumed count"
            );
            current = f;
            apps += 1;
        }
        assert!(apps == 400, "the app spine length is preserved");
        assert!(
            current == &subst,
            "bvar 0 receives the last (only) substitute"
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
    fn instantiate_lparams_walks_a_deep_app_nest_without_stack_fault() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let u = Name::str(Name::anonymous(), "u");
        let sort_u = Expr::sort(Level::param(u.clone()));
        let mut expr = sort_u;
        for _ in 0..400 {
            expr = Expr::app(expr, Expr::bvar(0).expect("packs"));
        }
        let result = tc
            .instantiate_lparams(&expr, std::slice::from_ref(&u), &[Level::zero()], 0)
            .expect("a 400-app universe nest must not stack-fault");
        let mut current = &result;
        let mut apps = 0usize;
        while let ExprNode::App { f, a } = current.node() {
            assert!(
                matches!(a.node(), ExprNode::BVar { idx } if *idx == 0),
                "bvar arguments have no level params and stay shared"
            );
            current = f;
            apps += 1;
        }
        assert!(apps == 400, "the app spine length is preserved");
        assert!(
            matches!(current.node(), ExprNode::Sort { level } if *level == Level::zero()),
            "Sort u becomes Sort 0"
        );
    }

    #[test]
    fn abstract_fvar_set_walks_a_deep_app_nest_without_stack_fault() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let id = FVarId(Name::str(Name::anonymous(), "x"));
        let fvar = Expr::fvar(id.clone());
        let mut expr = fvar.clone();
        for _ in 0..400 {
            expr = Expr::app(expr, fvar.clone());
        }
        let mut ordinals = HashMap::new();
        ordinals.insert(id, 0);
        let result = tc
            .abstract_fvar_set(&expr, &ordinals, 1, 0, 0)
            .expect("a 400-app fvar nest must not stack-fault");
        let mut current = &result;
        let mut apps = 0usize;
        while let ExprNode::App { f, a } = current.node() {
            assert!(
                matches!(a.node(), ExprNode::BVar { idx } if *idx == 0),
                "the single active fvar closes to bvar 0"
            );
            current = f;
            apps += 1;
        }
        assert!(apps == 400, "the app spine length is preserved");
        assert!(
            matches!(current.node(), ExprNode::BVar { idx } if *idx == 0),
            "the head fvar closes to bvar 0"
        );
    }

    #[test]
    fn replace_fvar_walks_a_deep_app_nest_without_stack_fault() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let id = FVarId(Name::str(Name::anonymous(), "x"));
        let fvar = Expr::fvar(id.clone());
        let subst = Expr::sort(Level::zero());
        let mut expr = fvar.clone();
        for _ in 0..400 {
            expr = Expr::app(expr, fvar.clone());
        }
        let result = tc
            .replace_fvar(&expr, &id, &subst, 0)
            .expect("a 400-app fvar nest must not stack-fault");
        let mut current = &result;
        let mut apps = 0usize;
        while let ExprNode::App { f, a } = current.node() {
            assert!(a == &subst, "every fvar argument is replaced");
            current = f;
            apps += 1;
        }
        assert!(apps == 400, "the app spine length is preserved");
        assert!(current == &subst, "the head fvar is replaced");
    }

    #[test]
    fn whnf_zetas_a_deep_let_spine_without_stack_fault() {
        // The seed elaborator folds sequential lets on the heap; WHNF used to
        // zeta one LetE per recursive frame and abort the check (FL-INV-07).
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let one = Expr::lit(Literal::Nat(NatLit::from_u64(1)));
        let nat = Expr::const_(Name::str(Name::anonymous(), "Nat"), Vec::new());
        let mut expr = one.clone();
        for _ in 0..400 {
            expr = Expr::let_e(
                Name::str(Name::anonymous(), "x"),
                nat.clone(),
                one.clone(),
                expr,
                false,
            );
        }
        let result = tc
            .whnf_public(&expr, 0)
            .expect("a 400-let spine must not stack-fault");
        assert!(
            result == one,
            "zeta of unused lets around a literal is the literal"
        );
    }

    #[test]
    fn defeq_app_congruence_walks_a_deep_spine_without_stack_fault() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let arg = Expr::sort(Level::zero());
        let mut left = Expr::sort(Level::zero());
        let mut right = Expr::sort(Level::zero());
        for _ in 0..400 {
            left = Expr::app(left, arg.clone());
            right = Expr::app(right, arg.clone());
        }
        assert!(
            tc.def_eq_public(&left, &right, 0)
                .expect("a 400-app congruence must not stack-fault"),
            "identical deep app spines are defeq"
        );

        let mut other = Expr::sort(Level::one());
        for _ in 0..400 {
            other = Expr::app(other, arg.clone());
        }
        assert!(
            !tc.def_eq_public(&left, &other, 0)
                .expect("a 400-app mismatch must not stack-fault"),
            "Sort 0 and Sort 1 heads stay apart"
        );
    }

    #[test]
    fn defeq_binder_congruence_walks_a_deep_telescope_without_stack_fault() {
        // Convert can inject a 400-deep Π/λ spine; KR-302 used to open one
        // binder per recursive `is_def_eq` and abort (FL-INV-07).
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let domain = Expr::sort(Level::one());
        let name = Name::str(Name::anonymous(), "x");
        let mut left_lam = Expr::sort(Level::zero());
        let mut right_lam = Expr::sort(Level::zero());
        let mut left_pi = Expr::sort(Level::zero());
        let mut right_pi = Expr::sort(Level::zero());
        for _ in 0..400 {
            left_lam = Expr::lam(name.clone(), domain.clone(), left_lam, BinderInfo::Default);
            right_lam = Expr::lam(name.clone(), domain.clone(), right_lam, BinderInfo::Default);
            left_pi = Expr::forall_e(name.clone(), domain.clone(), left_pi, BinderInfo::Default);
            right_pi = Expr::forall_e(name.clone(), domain.clone(), right_pi, BinderInfo::Default);
        }
        assert!(
            tc.def_eq_public(&left_lam, &right_lam, 0)
                .expect("a 400-λ congruence must not stack-fault"),
            "identical deep lambda telescopes are defeq"
        );
        assert!(
            tc.def_eq_public(&left_pi, &right_pi, 0)
                .expect("a 400-Π congruence must not stack-fault"),
            "identical deep forall telescopes are defeq"
        );

        let mut other_lam = Expr::sort(Level::one());
        let mut other_pi = Expr::sort(Level::one());
        for _ in 0..400 {
            other_lam = Expr::lam(name.clone(), domain.clone(), other_lam, BinderInfo::Default);
            other_pi = Expr::forall_e(name.clone(), domain.clone(), other_pi, BinderInfo::Default);
        }
        assert!(
            !tc.def_eq_public(&left_lam, &other_lam, 0)
                .expect("a 400-λ mismatch must not stack-fault"),
            "Sort 0 and Sort 1 bodies stay apart"
        );
        assert!(
            !tc.def_eq_public(&left_pi, &other_pi, 0)
                .expect("a 400-Π mismatch must not stack-fault"),
            "Sort 0 and Sort 1 codomains stay apart"
        );

        // Innermost domain disagrees; the peel must still compare it.
        let mut left_dom = Expr::lam(
            name.clone(),
            Expr::sort(Level::zero()),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        );
        let mut right_dom = Expr::lam(
            name.clone(),
            Expr::sort(Level::one()),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        );
        for _ in 0..399 {
            left_dom = Expr::lam(name.clone(), domain.clone(), left_dom, BinderInfo::Default);
            right_dom = Expr::lam(name.clone(), domain.clone(), right_dom, BinderInfo::Default);
        }
        assert!(
            !tc.def_eq_public(&left_dom, &right_dom, 0)
                .expect("a deep domain mismatch must not stack-fault"),
            "a binder whose innermost domain differs is not defeq"
        );

        // Bodies that mention the last binder still open under one fvar.
        let mut left_bvar = Expr::bvar(0).expect("bvar 0 packs");
        let mut right_bvar = Expr::bvar(0).expect("bvar 0 packs");
        for _ in 0..400 {
            left_bvar = Expr::lam(name.clone(), domain.clone(), left_bvar, BinderInfo::Default);
            right_bvar = Expr::lam(
                name.clone(),
                domain.clone(),
                right_bvar,
                BinderInfo::Default,
            );
        }
        assert!(
            tc.def_eq_public(&left_bvar, &right_bvar, 0)
                .expect("a 400-λ identity telescope must not stack-fault"),
            "identical deep identities are defeq"
        );
    }

    #[test]
    fn defeq_function_eta_walks_a_deep_telescope_without_stack_fault() {
        // KR-312 used to expand one λ per recursive is_def_eq. Convert can
        // inject a 400-deep λ against a non-lambda; that composition aborted
        // (FL-INV-07).
        use fln_env::constants::{AxiomVal, ConstantVal};

        let name = Name::str(Name::anonymous(), "x");
        let domain = Expr::sort(Level::one());
        let f_name = Name::str(Name::anonymous(), "f");
        let mut f_type = domain.clone();
        for _ in 0..400 {
            f_type = Expr::forall_e(name.clone(), domain.clone(), f_type, BinderInfo::Default);
        }
        let env = publish_checked(
            &Environment::new(),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: f_name.clone(),
                    level_params: Vec::new(),
                    type_: f_type,
                },
                is_unsafe: false,
            }),
        );
        let f = Expr::const_(f_name, Vec::new());
        let mut expanded = f.clone();
        for i in (0..400).rev() {
            expanded = Expr::app(expanded, Expr::bvar(i).expect("bvar packs"));
        }
        for _ in 0..400 {
            expanded = Expr::lam(name.clone(), domain.clone(), expanded, BinderInfo::Default);
        }
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        assert!(
            tc.def_eq_public(&expanded, &f, 0)
                .expect("a 400-λ eta must not stack-fault"),
            "(fun x1 … x400 => f x1 … x400) ≟ f"
        );

        // Domain mismatch stays decisive: Sort 0 vs Sort 1 on the first binder.
        let g_name = Name::str(Name::anonymous(), "g");
        let g_type = Expr::forall_e(
            name.clone(),
            domain.clone(),
            domain.clone(),
            BinderInfo::Default,
        );
        let env = publish_checked(
            &env,
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: g_name.clone(),
                    level_params: Vec::new(),
                    type_: g_type,
                },
                is_unsafe: false,
            }),
        );
        let g = Expr::const_(g_name, Vec::new());
        let wrong = Expr::lam(
            name.clone(),
            Expr::sort(Level::zero()),
            Expr::app(g.clone(), Expr::bvar(0).expect("bvar packs")),
            BinderInfo::Default,
        );
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        assert!(
            !tc.def_eq_public(&wrong, &g, 0)
                .expect("eta domain mismatch must not stack-fault"),
            "eta must still compare the λ domain against the Π domain"
        );

        // Dependent two-layer: (fun (A : Sort 1) (a : A) => h A a) ≟ h
        // with h : (A : Sort 1) → A → A.
        let h_name = Name::str(Name::anonymous(), "h");
        let a_name = Name::str(Name::anonymous(), "A");
        let h_type = Expr::forall_e(
            a_name.clone(),
            domain.clone(),
            Expr::forall_e(
                name.clone(),
                Expr::bvar(0).expect("bvar packs"),
                Expr::bvar(1).expect("bvar packs"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let env = publish_checked(
            &env,
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: h_name.clone(),
                    level_params: Vec::new(),
                    type_: h_type,
                },
                is_unsafe: false,
            }),
        );
        let h = Expr::const_(h_name, Vec::new());
        let dep = Expr::lam(
            a_name,
            domain,
            Expr::lam(
                name,
                Expr::bvar(0).expect("bvar packs"),
                Expr::app(
                    Expr::app(h.clone(), Expr::bvar(1).expect("bvar packs")),
                    Expr::bvar(0).expect("bvar packs"),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        assert!(
            tc.def_eq_public(&dep, &h, 0)
                .expect("dependent two-layer eta must not stack-fault"),
            "(fun (A : Sort 1) (a : A) => h A a) ≟ h"
        );
    }

    #[test]
    fn deep_level_param_spines_do_not_stack_fault() {
        // `check_level` and `instantiate_lparams` used to recurse one frame
        // per succ / max nesting. A legal 24-bit spine is far past a 2 MiB
        // host stack (FL-INV-07). 10_000 is enough to kill the old walk and
        // small enough to build in a unit test.
        let u = Name::str(Name::anonymous(), "u");
        let mut level = Level::param(u.clone());
        for _ in 0..10_000 {
            level = level.succ().expect("10k succs pack under the 24-bit cap");
        }

        let mut expected = Level::zero();
        for _ in 0..10_000 {
            expected = expected.succ().expect("zero tower packs");
        }
        assert_eq!(
            substitute_level(&level, std::slice::from_ref(&u), &[Level::zero()]),
            expected,
            "substituting 0 for u on a deep succ spine must rebuild the offset"
        );

        let mut found = None;
        collect_undeclared_param(&level, &[], &mut found);
        assert_eq!(
            found,
            Some(u.clone()),
            "an undeclared param at the bottom of a deep succ spine must still be found"
        );
        let mut found = None;
        collect_undeclared_param(&level, std::slice::from_ref(&u), &mut found);
        assert!(
            found.is_none(),
            "a declared param at the bottom of a deep succ spine must not be reported"
        );

        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, std::slice::from_ref(&u), Budget::DEFAULT);
        let inferred = tc
            .infer(&Expr::sort(level), 0)
            .expect("inferring Sort of a deep succ spine must not stack-fault");
        assert!(
            matches!(inferred.node(), ExprNode::Sort { .. }),
            "Sort (u+10000) : Sort (u+10001)"
        );
    }

    #[test]
    fn first_divergence_renders_a_deep_succ_spine_without_stack_fault() {
        let u = Name::str(Name::anonymous(), "u");
        let v = Name::str(Name::anonymous(), "v");
        let mut left = Level::param(u);
        let mut right = Level::param(v);
        for _ in 0..10_000 {
            left = left.succ().expect("10k succs pack");
            right = right.succ().expect("10k succs pack");
        }
        let report = first_divergence(&Expr::sort(left), &Expr::sort(right))
            .expect("distinct param spines must diverge");
        assert!(
            report.contains("param:u") && report.contains("param:v"),
            "the diagnostic must still name both parameters: {report}"
        );
    }

    #[test]
    fn first_divergence_walks_deep_app_and_let_spines_without_stack_fault() {
        let zero = Expr::bvar(0).expect("packs");
        let one = Expr::bvar(1).expect("packs");
        let mut left = zero.clone();
        let mut right = one.clone();
        for _ in 0..400 {
            left = Expr::app(left, zero.clone());
            right = Expr::app(right, zero.clone());
        }
        let report = first_divergence(&left, &right).expect("deep app heads differ");
        assert!(
            report.contains("#0 vs #1") && report.contains(".fn"),
            "the difference is at the head of the fn spine: {report}"
        );

        let name = Name::str(Name::anonymous(), "x");
        let ty = Expr::sort(Level::zero());
        let val = Expr::sort(Level::zero());
        let mut left = zero;
        let mut right = one;
        for _ in 0..400 {
            left = Expr::let_e(name.clone(), ty.clone(), val.clone(), left, false);
            right = Expr::let_e(name.clone(), ty.clone(), val.clone(), right, false);
        }
        let report = first_divergence(&left, &right).expect("deep let bodies differ");
        assert!(
            report.contains("#0 vs #1") && report.contains(".let_body"),
            "the difference is at the end of the let spine: {report}"
        );

        let same = Expr::app(Expr::bvar(0).expect("packs"), Expr::bvar(1).expect("packs"));
        assert_eq!(first_divergence(&same, &same), None);
        let arg_left = Expr::app(Expr::bvar(0).expect("packs"), Expr::bvar(0).expect("packs"));
        let arg_right = Expr::app(Expr::bvar(0).expect("packs"), Expr::bvar(1).expect("packs"));
        let report = first_divergence(&arg_left, &arg_right).expect("args differ");
        assert!(
            report.contains(".arg") && report.contains("#0 vs #1"),
            "equal heads must fall through to the argument: {report}"
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
    fn whnf_core_cache_rolls_full_generations_without_widening_its_live_bound() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        assert!(tc.whnf_core_cache.rollover_on_saturation);
        assert!(
            !tc.infer_cache.rollover_on_saturation
                && !tc.infer_only_cache.rollover_on_saturation
                && !tc.whnf_cache.rollover_on_saturation,
            "only the observed phase-heavy WHNF-core cache may roll over"
        );

        let id = FVarId(Name::str(Name::anonymous(), "rolling"));
        let local = Expr::fvar(id.clone());
        tc.adopt_local(id, Expr::sort(Level::zero()));
        let keyed = |leaf: &str| {
            Expr::app(
                Expr::const_(Name::str(Name::anonymous(), leaf), Vec::new()),
                local.clone(),
            )
        };
        let first = keyed("first");
        let second = keyed("second");
        let next_phase = keyed("nextPhase");

        let mut rolling = ExprResultCache::bounded(2, 4);
        rolling.rollover_on_saturation = true;
        rolling.insert(
            first.clone(),
            first.clone(),
            &tc.locals,
            &tc.local_positions,
        );
        rolling.insert(second.clone(), second, &tc.locals, &tc.local_positions);
        assert!(rolling.entries == 2 && rolling.local_dependency_cells == 2);
        let scans_before_rollover = rolling.local_dependency_scan_nodes;
        rolling.dependency_scan_refusals.insert((u64::MAX, 0), ());

        rolling.insert(
            next_phase.clone(),
            next_phase.clone(),
            &tc.locals,
            &tc.local_positions,
        );
        assert!(
            rolling.entries == 1 && rolling.local_dependency_cells == 1,
            "retiring a generation must release both its rows and dependency cells"
        );
        assert!(
            rolling.local_dependency_scan_nodes >= scans_before_rollover
                && rolling
                    .dependency_scan_refusals
                    .contains_key(&(u64::MAX, 0)),
            "rollover must not renew either lifetime dependency-discovery allowance"
        );
        assert!(
            rolling
                .get(&first, &tc.locals, &tc.local_positions)
                .is_none(),
            "retired facts must become ordinary cache misses"
        );
        assert!(
            rolling.get(&next_phase, &tc.locals, &tc.local_positions) == Some(next_phase),
            "the first row of the next proof phase must be reusable"
        );
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
    fn infer_strips_a_deep_mdata_nest_without_stack_fault() {
        let mut term = Expr::lit(Literal::Nat(NatLit::from_u64(7)));
        for _ in 0..400 {
            term = Expr::mdata(fln_core::options::KVMap::default(), term);
        }
        let budget = Budget::DEFAULT;
        let env = Environment::new();
        let mut checking = TypeChecker::new(&env, &[], budget);
        let inferred = checking
            .infer(&term, 0)
            .expect("a 400-mdata nest must not stack-fault");
        assert!(
            matches!(
                inferred.node(),
                ExprNode::Const { name, .. } if name.to_display_string() == "Nat"
            ),
            "KR-111 must infer the inner literal, got {}",
            brief_public(&inferred)
        );
        assert!(
            checking.consumption().max_depth <= budget.depth,
            "mdata wrappers must consume loop steps, not native-stack depth"
        );
    }

    #[test]
    fn infer_checks_a_deep_right_nested_app_without_stack_fault() {
        use fln_env::constants::{AxiomVal, ConstantVal};

        const NEST: usize = 400;
        let t_name = Name::str(Name::anonymous(), "T");
        let f_name = Name::str(Name::anonymous(), "f");
        let a_name = Name::str(Name::anonymous(), "a");
        let t = Expr::const_(t_name.clone(), Vec::new());
        let env = publish_checked(
            &Environment::new(),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: t_name,
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
                    name: f_name.clone(),
                    level_params: Vec::new(),
                    type_: Expr::forall_e(
                        Name::anonymous(),
                        t.clone(),
                        t.clone(),
                        BinderInfo::Default,
                    ),
                },
                is_unsafe: false,
            }),
        );
        let env = publish_checked(
            &env,
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: a_name.clone(),
                    level_params: Vec::new(),
                    type_: t.clone(),
                },
                is_unsafe: false,
            }),
        );
        let f = Expr::const_(f_name, Vec::new());
        let mut term = Expr::const_(a_name, Vec::new());
        for _ in 0..NEST {
            term = Expr::app(f.clone(), term);
        }
        let budget = Budget::DEFAULT;
        let mut tc = TypeChecker::new(&env, &[], budget);
        let inferred = tc
            .infer(&term, 0)
            .expect("a 400-deep right-nested application must not stack-fault");
        assert!(
            inferred == t,
            "KR-106 must infer T, got {}",
            brief_public(&inferred)
        );
        assert!(
            tc.consumption().max_depth <= budget.depth,
            "right-nested applications must consume loop steps, not native-stack depth"
        );

        let mut wrapped = Expr::const_(Name::str(Name::anonymous(), "a"), Vec::new());
        for _ in 0..NEST {
            wrapped = Expr::mdata(
                fln_core::options::KVMap::default(),
                Expr::app(f.clone(), wrapped),
            );
        }
        let mut wrapped_tc = TypeChecker::new(&env, &[], budget);
        let wrapped_inferred = wrapped_tc
            .infer(&wrapped, 0)
            .expect("a 400-deep mdata-wrapped application nest must not stack-fault");
        assert!(
            wrapped_inferred == t,
            "KR-111+KR-106 must infer T through metadata, got {}",
            brief_public(&wrapped_inferred)
        );
        assert!(
            wrapped_tc.consumption().max_depth <= budget.depth,
            "mdata-wrapped right-nested applications must consume loop steps"
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
    fn lazy_delta_remembers_failed_regular_head_arguments_before_retrying() {
        use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal};

        let nat_name = Name::str(Name::anonymous(), "Nat");
        let nat = Expr::const_(nat_name.clone(), Vec::new());
        let function_name = Name::str(Name::anonymous(), "regularFailureMemo");
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
                    type_: Expr::forall_e(
                        Name::anonymous(),
                        nat.clone(),
                        nat.clone(),
                        BinderInfo::Default,
                    ),
                },
                value: Expr::lam(
                    Name::anonymous(),
                    nat,
                    Expr::bvar(0).expect("packs"),
                    BinderInfo::Default,
                ),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![function_name.clone()],
            }),
        );
        let left = Expr::app(
            Expr::const_(function_name.clone(), Vec::new()),
            Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        );
        let right = Expr::app(
            Expr::const_(function_name, Vec::new()),
            Expr::lit(Literal::Nat(NatLit::from_u64(1))),
        );
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);

        assert!(
            !tc.regular_same_head_apps_def_eq(&left, &right, 0)
                .expect("the first unequal-argument comparison completes"),
            "unequal arguments cannot close the regular-head shortcut"
        );
        assert!(
            tc.regular_app_def_eq_failure_cache.entries == 1,
            "the failed shortcut pair must be retained"
        );
        let steps_after_first = tc.consumption().steps_used;
        assert!(
            !tc.regular_same_head_apps_def_eq(&left, &right, 0)
                .expect("the repeated shortcut lookup completes"),
            "a remembered failure still means lazy delta must unfold"
        );
        assert!(
            tc.consumption().steps_used == steps_after_first,
            "a repeated failed shortcut must not re-run recursive defeq"
        );
        assert!(
            !tc.def_eq_public(&left, &right, 0)
                .expect("ordinary unfolding still decides the unequal pair"),
            "the failure memo is an optimization, never a cached rejection"
        );
    }

    #[test]
    fn lazy_delta_retains_non_projection_unfold_results() {
        use fln_env::constants::{ConstantVal, DefinitionVal};

        let sort_zero = Expr::sort(Level::zero());
        let beta_sort_zero = Expr::app(
            Expr::lam(
                Name::anonymous(),
                Expr::sort(Level::one()),
                Expr::bvar(0).expect("packs"),
                BinderInfo::Default,
            ),
            sort_zero.clone(),
        );
        let name = Name::str(Name::anonymous(), "lazyDeltaCacheSource");
        let env = publish_checked(
            &Environment::new(),
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                value: beta_sort_zero.clone(),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![name.clone()],
            }),
        );
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT.narrowed(1_000, 32));

        let outcome = tc
            .lazy_delta(Expr::const_(name, Vec::new()), sort_zero.clone(), 0)
            .expect("the regular definition unfolds and reaches the comparison term");
        assert!(
            matches!(outcome, LazyDelta::Stuck(ref left, ref right) if left == &sort_zero && right == &sort_zero),
            "delta unfolding must normalize the definition body to its comparison term"
        );
        assert_eq!(
            tc.whnf_core_cache
                .get(&beta_sort_zero, &tc.locals, &tc.local_positions),
            Some(sort_zero),
            "lazy-delta unfolding must retain the ordinary WHNF result"
        );
    }

    #[test]
    fn defeq_compares_projection_scrutinees_before_full_reduction() {
        use fln_core::options::KVMap;
        use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal};

        let nat_name = Name::str(Name::anonymous(), "Nat");
        let nat = Expr::const_(nat_name.clone(), Vec::new());
        let function_name = Name::str(Name::anonymous(), "expensiveProjectionSource");
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
            &env,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: function_name.clone(),
                    level_params: Vec::new(),
                    type_: Expr::forall_e(
                        Name::anonymous(),
                        nat.clone(),
                        nat.clone(),
                        BinderInfo::Default,
                    ),
                },
                value: function_value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![function_name.clone()],
            }),
        );
        let zero = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        let beta_zero = Expr::app(
            Expr::lam(
                Name::anonymous(),
                nat,
                Expr::bvar(0).expect("packs"),
                BinderInfo::Default,
            ),
            zero.clone(),
        );
        let source =
            |argument| Expr::app(Expr::const_(function_name.clone(), Vec::new()), argument);
        let structure_name = Name::str(Name::anonymous(), "ProjectionProbe");
        let left = Expr::proj(structure_name.clone(), 0, source(beta_zero));
        let right = Expr::proj(structure_name, 0, source(zero));
        let budget = Budget::DEFAULT.narrowed(10_000, 32);
        let mut tc = TypeChecker::new(&env, &[], budget);

        assert!(
            tc.def_eq_public(&left, &right, 0)
                .expect("cheap projection congruence stays inside the shallow budget"),
            "defeq must compare projection scrutinees before opening their regular head"
        );
        assert!(
            tc.consumption().max_depth <= budget.depth,
            "the projection pre-pass must not traverse the expensive definition body"
        );
    }

    #[test]
    fn defeq_preserves_full_whnf_cache_for_non_projection_pairs() {
        let env = Environment::new();
        let sort_zero = Expr::sort(Level::zero());
        let beta_sort_zero = Expr::app(
            Expr::lam(
                Name::anonymous(),
                Expr::sort(Level::one()),
                Expr::bvar(0).expect("packs"),
                BinderInfo::Default,
            ),
            sort_zero.clone(),
        );
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT.narrowed(1_000, 32));

        assert!(
            tc.def_eq_public(&beta_sort_zero, &sort_zero, 0)
                .expect("the non-projection beta pair completes"),
            "beta reduction must establish the ordinary defeq pair"
        );
        assert_eq!(
            tc.whnf_core_cache
                .get(&beta_sort_zero, &tc.locals, &tc.local_positions),
            Some(sort_zero),
            "ordinary defeq normalization must retain its full-WHNF result"
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
            tc.infer_cache.entries == rows_before_shadow + 1,
            "a shadowed transitive generation must remain recoverable while the live generation gets its own row"
        );
        assert!(
            tc.infer_cache
                .buckets
                .get(&(value_local.data().0, tc.locals.len()))
                .is_some_and(|bucket| bucket.iter().all(|entry| {
                    dependencies_are_live(&entry.dependencies, &tc.locals, &tc.local_positions)
                })),
            "the retained row must name only the current transitive generations"
        );

        tc.drop_local();
        tc.adopt_local(
            FVarId(Name::str(
                Name::anonymous(),
                "unrelated_after_transitive_shadow",
            )),
            zero,
        );
        let restored_transitive_steps = tc.consumption().steps_used;
        tc.infer(&value_local, 0)
            .expect("the revealed transitive generation infers");
        assert!(
            tc.consumption().steps_used - restored_transitive_steps == 2,
            "dropping a transitive shadow must reveal the original inference row across unrelated binder churn"
        );
    }

    #[test]
    fn shadowed_generation_cache_rows_reappear_after_unrelated_binder_churn() {
        let env = Environment::new();
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let id = FVarId(Name::str(Name::anonymous(), "shadowed_cache"));
        let local = Expr::fvar(id.clone());
        let zero = Expr::sort(Level::zero());
        let one = Expr::sort(Level::one());
        let function_type = Expr::forall_e(
            Name::anonymous(),
            one.clone(),
            one.clone(),
            BinderInfo::Default,
        );
        let application = Expr::app(local.clone(), zero.clone());

        tc.push_local(id.clone(), function_type.clone(), None);
        assert!(
            tc.infer(&application, 0).expect("outer application infers") == one,
            "the outer generation supplies the first reusable inference"
        );

        tc.push_local(id, function_type, None);
        assert!(
            tc.infer(&application, 0)
                .expect("shadow application infers")
                == one,
            "the shadow generation must compute its own inference"
        );

        tc.drop_local();
        tc.adopt_local(
            FVarId(Name::str(Name::anonymous(), "unrelated_after_shadow")),
            zero.clone(),
        );

        let infer_steps = tc.consumption().steps_used;
        assert!(
            tc.infer(&application, 0)
                .expect("revealed outer application infers")
                == one,
            "dropping a shadow must reveal the still-live outer generation"
        );
        assert!(
            tc.consumption().steps_used - infer_steps == 2,
            "an unrelated binder must not hide the revealed generation's inference row"
        );

        let mut defeq_tc = TypeChecker::new(&env, &[], Budget::DEFAULT);
        let let_id = FVarId(Name::str(Name::anonymous(), "shadowed_defeq"));
        let let_local = Expr::fvar(let_id.clone());
        defeq_tc.push_local(let_id.clone(), one.clone(), Some(zero.clone()));
        assert!(
            defeq_tc
                .def_eq_public(&let_local, &zero, 0)
                .expect("outer let local reduces"),
            "the outer generation supplies the first reusable equality"
        );
        defeq_tc.push_local(let_id, one, Some(zero.clone()));
        assert!(
            defeq_tc
                .def_eq_public(&let_local, &zero, 0)
                .expect("shadow let local reduces"),
            "the shadow generation must compute its own equality"
        );
        defeq_tc.drop_local();
        defeq_tc.adopt_local(
            FVarId(Name::str(Name::anonymous(), "unrelated_after_defeq_shadow")),
            zero.clone(),
        );
        let defeq_steps = defeq_tc.consumption().steps_used;
        assert!(
            defeq_tc
                .def_eq_public(&let_local, &zero, 0)
                .expect("revealed outer let local reduces"),
            "dropping a shadow must reveal the still-live outer equality"
        );
        assert!(
            defeq_tc.consumption().steps_used - defeq_steps == 1,
            "an unrelated binder must not hide the revealed generation's positive-defeq row"
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
                    position: 0,
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
                .contains_key(&(scan_key.data().0, scan_refused.locals.len())),
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
            .insert((u64::MAX, refusal_full.locals.len()), ());
        refusal_full
            .positive_def_eq_cache
            .dependency_scan_refusals
            .insert((u64::MAX, u64::MAX, refusal_full.locals.len()), ());
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
            (pi.data().0, 0),
            vec![ExprResultCacheEntry {
                key: unrelated.clone(),
                value: unrelated.clone(),
                dependencies: Vec::new(),
            }],
        );
        collided.infer_cache.entries = 1;
        collided.whnf_cache = ExprResultCache::bounded(1, 1);
        collided.whnf_cache.buckets.insert(
            (redex.data().0, 0),
            vec![ExprResultCacheEntry {
                key: unrelated.clone(),
                value: unrelated.clone(),
                dependencies: Vec::new(),
            }],
        );
        collided.whnf_cache.entries = 1;
        collided.positive_def_eq_cache = PositiveDefEqCache::bounded(1, 1);
        collided.positive_def_eq_cache.buckets.insert(
            PositiveDefEqCache::scoped_key(&redex, &sort, 0),
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
    fn packed_collision_capacity_is_partitioned_by_telescope_length() {
        let env = Environment::new();
        let (pi, redex, sort) = closed_cache_fixture();
        let unrelated = Expr::sort(Level::one());
        let mut tc = TypeChecker::new(&env, &[], Budget::DEFAULT);

        let mut result_cache = ExprResultCache::bounded(2, 1);
        result_cache.buckets.insert(
            (pi.data().0, 0),
            vec![ExprResultCacheEntry {
                key: unrelated.clone(),
                value: unrelated.clone(),
                dependencies: Vec::new(),
            }],
        );
        result_cache.entries = 1;

        let mut defeq_cache = PositiveDefEqCache::bounded(2, 1);
        defeq_cache.buckets.insert(
            PositiveDefEqCache::scoped_key(&redex, &sort, 0),
            vec![PositiveDefEqCacheEntry {
                left: unrelated,
                right: pi.clone(),
                dependencies: Vec::new(),
            }],
        );
        defeq_cache.entries = 1;

        tc.adopt_local(
            FVarId(Name::str(Name::anonymous(), "scope_partition")),
            Expr::sort(Level::zero()),
        );
        result_cache.insert(pi.clone(), sort.clone(), &tc.locals, &tc.local_positions);
        defeq_cache.insert(redex.clone(), sort.clone(), &tc.locals, &tc.local_positions);

        assert!(
            result_cache.entries == 2
                && result_cache
                    .get(&pi, &tc.locals, &tc.local_positions)
                    .is_some_and(|value| value == sort),
            "a collision in another telescope length must not consume this scope's row capacity"
        );
        assert!(
            defeq_cache.entries == 2
                && defeq_cache.contains(&redex, &sort, &tc.locals, &tc.local_positions),
            "positive-defeq collision capacity must use the same deterministic scope partition"
        );

        let mut bounded_index = ExprResultCache::bounded(1, 4);
        bounded_index.record_cross_scope(&pi, 0);
        bounded_index.record_cross_scope(&sort, 0);
        assert!(
            bounded_index.cross_scope_entries == 1 && bounded_index.cross_scope.len() == 1,
            "cross-scope acceleration must retain no more roots than the row bound"
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
