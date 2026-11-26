//! Weak head normal forms already computed under one context.
//!
//! Lazy delta, the typed conversion lane, and recursor iota ask for the weak
//! head normal form of the same terms again and again while checking one
//! declaration. In `String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three`
//! one delta step of `WellFounded.Nat.fix.go`, about 8 s, is taken 15 times,
//! from as many separate conversions. The pin keeps `m_whnf` for the life of its
//! type checker for this reason. This memo does the same for one `WhnfContext`.
//!
//! A remembered result is the result a recomputation would return, charges
//! included:
//! - reduction reads nothing but its input, the constants, the projection rules
//!   and the let-bound locals in scope. A context never changes the first three,
//!   and a clone, which shares the memo, has the same;
//! - the let-bound locals do change, as scopes open and close, and a local's name
//!   may come back bound to another value. So an entry records the bindings it
//!   was computed under and matches only the same names, in the same order,
//!   bound to structurally equal values; the fingerprint carries only the names,
//!   so the values are always compared exactly. Before this, the memo was not
//!   used at all under a let-bound local: in Mathlib's Ring.Limits five of them
//!   are in scope for all but 656 of `CommRingCat.instCreatesLimit…`'s 740,000
//!   normalizations;
//! - an entry matches only an exactly equal materialized input, under the same
//!   delta mode and the same materialization budget;
//! - reduction never branches on its budget: a smaller budget only stops it
//!   sooner. The recorded counters are therefore exactly the budget a
//!   recomputation needs, and an entry is used only when the caller's budget
//!   covers each of them. Otherwise the caller recomputes, and stops where it
//!   would have;
//! - only complete results are recorded.
use super::*;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::sync::Mutex;

/// Zero-overhead pass-through hasher for tables whose keys are already
/// 64-bit fingerprints mixed by `Fingerprinter` (never iterated for semantics).
#[derive(Default)]
pub(crate) struct IdentityU64Hasher(u64);

impl Hasher for IdentityU64Hasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut fp = Fingerprinter(self.0);
        fp.write(bytes);
        self.0 = fp.finish();
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.0 = value;
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.0 = value as u64;
    }
}

pub(crate) type PrehashedMap<V> = HashMap<u64, V, BuildHasherDefault<IdentityU64Hasher>>;
pub(crate) type FastHashMap<K, V> = HashMap<K, V, BuildHasherDefault<Fingerprinter>>;
pub(crate) type FastHashSet<K> = HashSet<K, BuildHasherDefault<Fingerprinter>>;

struct Entry {
    input: Arc<WireExpr>,
    delta_mode: DeltaMode,
    head_nat: NatReductionScope,
    materialization: TermBudget,
    /// The let-bound locals in scope when `result` was computed.
    bindings: Vec<FreeBinding>,
    result: WhnfResult,
    nat_progress: WhnfNatProgress,
    /// Whether `result`'s term is the module's own copy of a term (`WhnfInput`).
    copied: bool,
}

impl Entry {
    fn matches(
        &self,
        input: &WireExpr,
        delta_mode: DeltaMode,
        head_nat: NatReductionScope,
        materialization: TermBudget,
        bindings: &[FreeBinding],
    ) -> bool {
        self.delta_mode == delta_mode
            && self.head_nat == head_nat
            && self.materialization == materialization
            && same_bindings(&self.bindings, bindings)
            && *self.input == *input
    }
}

/// The same names in the same order, bound to structurally equal values. A
/// shared value is equal without a walk.
fn same_bindings(left: &[FreeBinding], right: &[FreeBinding]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.name == right.name
                && (Arc::ptr_eq(&left.value, &right.value) || *left.value == *right.value)
        })
}

/// Whether a bucket takes a new entry: it is not full, and holds no equal one.
fn admits(
    bucket: &[Entry],
    input: &WireExpr,
    delta_mode: DeltaMode,
    head_nat: NatReductionScope,
    materialization: TermBudget,
    bindings: &[FreeBinding],
) -> bool {
    bucket.len() < MAX_BUCKET_ENTRIES
        && !bucket
            .iter()
            .any(|entry| entry.matches(input, delta_mode, head_nat, materialization, bindings))
}

/// Reserve optional cache storage before publishing an entry. In particular,
/// a failed bucket allocation must not accumulate uncharged empty buckets.
fn try_push_bucket<T>(map: &mut PrehashedMap<Vec<T>>, key: u64, entry: T) -> bool {
    if let Some(bucket) = map.get_mut(&key) {
        if bucket.try_reserve(1).is_err() {
            return false;
        }
        bucket.push(entry);
        return true;
    }
    let mut bucket = Vec::new();
    if bucket.try_reserve_exact(1).is_err() || map.try_reserve(1).is_err() {
        return false;
    }
    bucket.push(entry);
    map.insert(key, bucket);
    true
}

/// Per-generation retention bounds: a full generation rotates into `previous`
/// and the old `previous` is dropped. These are optional cache limits, never
/// checking fuel. Count entire arenas, including levels and let-bound values,
/// even when several references share storage. The byte estimate also covers
/// payloads and spare capacities; allocator metadata and bounded table overhead
/// are additional. It is not a process RSS limit.
const MAX_ENTRIES: usize = 1 << 16;
const MAX_STORED_NODES: usize = 1 << 20;
const MAX_STORED_BYTES: usize = 128 * 1024 * 1024;

#[derive(Clone, Copy, Default)]
struct RetainedSize {
    nodes: usize,
    bytes: usize,
}

impl RetainedSize {
    fn add_term(&mut self, term: &WireExpr) {
        self.nodes = self
            .nodes
            .saturating_add(term.nodes().len())
            .saturating_add(term.levels().len());
        self.bytes = self
            .bytes
            .saturating_add(term.retained_bytes())
            .saturating_add(std::mem::size_of::<WireExpr>())
            .saturating_add(2 * std::mem::size_of::<usize>());
    }

    fn pair(left: &WireExpr, right: &WireExpr, entry_bytes: usize) -> Self {
        let mut size = Self {
            nodes: 0,
            bytes: entry_bytes,
        };
        size.add_term(left);
        size.add_term(right);
        size
    }

    fn fits(self) -> bool {
        self.nodes <= MAX_STORED_NODES && self.bytes <= MAX_STORED_BYTES
    }
}

fn entry_size(
    input: &WireExpr,
    result: &WireExpr,
    bindings: &[FreeBinding],
) -> Option<RetainedSize> {
    let mut size = RetainedSize::pair(input, result, std::mem::size_of::<Entry>());
    size.bytes = size.bytes.saturating_add(
        bindings
            .len()
            .saturating_mul(std::mem::size_of::<FreeBinding>()),
    );
    if !size.fits() {
        return None;
    }
    for binding in bindings {
        size.add_term(&binding.value);
        size.bytes = size.bytes.saturating_add(binding.name.retained_bytes());
        if !size.fits() {
            return None;
        }
    }
    Some(size)
}

/// A full bucket takes no more entries, so no input, however it collides, makes
/// a lookup compare more than this many terms.
const MAX_BUCKET_ENTRIES: usize = 8;

/// A completed KR-317 conversion and its auxiliary work. The final gate step
/// and cancellation poll are performed by the caller on both misses and hits.
#[derive(Clone, Copy)]
pub(super) struct RememberedKGate {
    pub(super) equal: bool,
    pub(super) steps: u64,
    pub(super) reductions: u64,
}

/// One remembered gate answer under the exact materialization limits used to
/// compute it. Resource-stopped or deferred conversions are not answers.
struct GateEntry {
    domain: Arc<WireExpr>,
    result: Arc<WireExpr>,
    materialization: TermBudget,
    value: RememberedKGate,
}

#[derive(Default)]
struct Table {
    /// Keyed by a fixed fingerprint, so the order of results never depends on the
    /// process; entries in a bucket are compared exactly.
    buckets: PrehashedMap<Vec<Entry>>,
    /// KR-317 gate outcomes by conversion, keyed the same way (see
    /// `WhnfMemo::recall_k_gate`). They share all retention bounds.
    k_gate: PrehashedMap<Vec<GateEntry>>,
    entries: usize,
    stored_nodes: usize,
    stored_bytes: usize,
}

#[derive(Default)]
struct MemoTables {
    current: Table,
    previous: Table,
}

#[derive(Clone, Copy)]
struct LookupKey<'a> {
    fp: u64,
    input: &'a WireExpr,
    delta_mode: DeltaMode,
    head_nat: NatReductionScope,
    bindings: &'a [FreeBinding],
}

impl Table {
    fn fits(&self, size: RetainedSize) -> bool {
        self.entries < MAX_ENTRIES
            && self.stored_nodes.saturating_add(size.nodes) <= MAX_STORED_NODES
            && self.stored_bytes.saturating_add(size.bytes) <= MAX_STORED_BYTES
    }

    fn retained(&mut self, size: RetainedSize) {
        self.entries += 1;
        self.stored_nodes = self.stored_nodes.saturating_add(size.nodes);
        self.stored_bytes = self.stored_bytes.saturating_add(size.bytes);
    }

    fn recall(&self, key: LookupKey<'_>, budget: &WhnfBudget) -> Option<(WhnfResult, bool)> {
        self.buckets
            .get(&key.fp)?
            .iter()
            .find(|entry| {
                entry.matches(
                    key.input,
                    key.delta_mode,
                    key.head_nat,
                    budget.materialization,
                    key.bindings,
                )
            })
            .filter(|entry| covers(budget, &entry.result))
            .map(|entry| (entry.result.clone(), entry.copied))
    }

    fn recall_eager_nat(
        &self,
        key: LookupKey<'_>,
        budget: &WhnfBudget,
        numeric_budget: NatBudget,
    ) -> Option<(WhnfResult, WhnfNatProgress, bool)> {
        self.buckets
            .get(&key.fp)?
            .iter()
            .find(|entry| {
                entry.matches(
                    key.input,
                    key.delta_mode,
                    key.head_nat,
                    budget.materialization,
                    key.bindings,
                )
            })
            .filter(|entry| {
                covers(budget, &entry.result)
                    && entry.nat_progress.steps <= numeric_budget.max_steps
                    && entry.nat_progress.materialized_limbs
                        <= numeric_budget.max_materialized_limbs
            })
            .map(|entry| (entry.result.clone(), entry.nat_progress, entry.copied))
    }

    fn recall_k_gate(
        &self,
        fp: u64,
        domain: &WireExpr,
        result: &WireExpr,
        materialization: TermBudget,
    ) -> Option<RememberedKGate> {
        self.k_gate
            .get(&fp)?
            .iter()
            .find(|entry| {
                entry.materialization == materialization
                    && *entry.domain == *domain
                    && *entry.result == *result
            })
            .map(|entry| entry.value)
    }
}

/// Shared by a context and its clones. It carries no meaning of its own: two
/// contexts that are otherwise equal reduce alike whatever their memos hold, so
/// every memo compares equal.
#[derive(Clone, Default)]
pub(super) struct WhnfMemo(Arc<Mutex<MemoTables>>);

impl PartialEq for WhnfMemo {
    fn eq(&self, _: &WhnfMemo) -> bool {
        true
    }
}

impl Eq for WhnfMemo {}

impl fmt::Debug for WhnfMemo {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("WhnfMemo")
    }
}

/// A fixed multiplicative hash. A fingerprint only picks a bucket, whose entries
/// are compared exactly, so it needs speed and a fixed key, not resistance to
/// chosen inputs; `MAX_BUCKET_ENTRIES` bounds what a collision can cost. Every
/// lookup hashes its whole input, which `std`'s SipHash made 6 % of a heavy
/// declaration's check. The materialization sharing table uses it for the same
/// reason (`sharing::fingerprint`).
#[derive(Default)]
pub(crate) struct Fingerprinter(u64);

impl Fingerprinter {
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl Hasher for Fingerprinter {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for word in words {
            self.add(u64::from_le_bytes(*word));
        }
        if !rest.is_empty() {
            let mut word = [0; 8];
            for (slot, byte) in word.iter_mut().zip(rest) {
                *slot = *byte;
            }
            self.add(u64::from_le_bytes(word));
        }
    }

    fn write_u8(&mut self, value: u8) {
        self.add(u64::from(value));
    }

    fn write_u32(&mut self, value: u32) {
        self.add(u64::from(value));
    }

    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    fn write_usize(&mut self, value: usize) {
        self.add(u64::try_from(value).unwrap_or(u64::MAX));
    }
}

/// The bindings enter by name only: hashing their values on every lookup would
/// cost a walk of each, and `Entry::matches` compares the values exactly anyway.
fn fingerprint(
    input: &WireExpr,
    delta_mode: DeltaMode,
    head_nat: NatReductionScope,
    materialization: TermBudget,
    bindings: &[FreeBinding],
) -> u64 {
    let mut hasher = Fingerprinter::default();
    input.hash(&mut hasher);
    delta_mode.hash(&mut hasher);
    head_nat.hash(&mut hasher);
    materialization.hash(&mut hasher);
    for binding in bindings {
        binding.name.hash(&mut hasher);
    }
    hasher.finish()
}

/// Whether `budget` lets a recomputation run to the end: every counter the
/// reducer checks stays within its limit.
fn covers(budget: &WhnfBudget, result: &WhnfResult) -> bool {
    let string = &result.string_progress;
    result.steps <= budget.max_steps
        && result.reductions <= budget.max_reductions
        && string.steps <= budget.string.max_steps
        && string.code_points <= budget.string.max_code_points
        && string.arena_nodes <= budget.string.max_arena_nodes
        && string.owned_units <= budget.string.max_owned_units
}

pub(super) struct RememberedWhnf<'a> {
    pub(super) result: &'a WhnfResult,
    pub(super) nat_progress: WhnfNatProgress,
    pub(super) copied: bool,
}

impl WhnfMemo {
    pub(super) fn recall(
        &self,
        input: &WireExpr,
        delta_mode: DeltaMode,
        head_nat: NatReductionScope,
        budget: &WhnfBudget,
        bindings: &[FreeBinding],
    ) -> Option<(WhnfResult, bool)> {
        let tables = self.0.lock().ok()?;
        let key = LookupKey {
            fp: fingerprint(
                input,
                delta_mode,
                head_nat,
                budget.materialization,
                bindings,
            ),
            input,
            delta_mode,
            head_nat,
            bindings,
        };
        tables
            .current
            .recall(key, budget)
            .or_else(|| tables.previous.recall(key, budget))
    }

    pub(super) fn recall_eager_nat(
        &self,
        input: &WireExpr,
        delta_mode: DeltaMode,
        head_nat: NatReductionScope,
        budget: &WhnfBudget,
        numeric_budget: NatBudget,
        bindings: &[FreeBinding],
    ) -> Option<(WhnfResult, WhnfNatProgress, bool)> {
        let tables = self.0.lock().ok()?;
        let key = LookupKey {
            fp: fingerprint(
                input,
                delta_mode,
                head_nat,
                budget.materialization,
                bindings,
            ),
            input,
            delta_mode,
            head_nat,
            bindings,
        };
        tables
            .current
            .recall_eager_nat(key, budget, numeric_budget)
            .or_else(|| {
                tables
                    .previous
                    .recall_eager_nat(key, budget, numeric_budget)
            })
    }

    /// Record a complete result. Results that reduced nothing are not worth a
    /// slot: recomputing them costs no more than the lookup.
    pub(super) fn remember(
        &self,
        input: Arc<WireExpr>,
        delta_mode: DeltaMode,
        head_nat: NatReductionScope,
        materialization: TermBudget,
        bindings: &[FreeBinding],
        value: RememberedWhnf<'_>,
    ) {
        if value.result.reductions == 0 && value.result.delta_reductions == 0 {
            return;
        }
        let Some(mut size) = entry_size(&input, &value.result.term, bindings) else {
            return;
        };
        let Ok(mut tables) = self.0.lock() else {
            return;
        };
        let fp = fingerprint(&input, delta_mode, head_nat, materialization, bindings);
        if tables.current.buckets.get(&fp).is_some_and(|bucket| {
            !admits(
                bucket,
                &input,
                delta_mode,
                head_nat,
                materialization,
                bindings,
            )
        }) {
            return;
        }
        // Optional retention must not turn a completed reduction into a host
        // allocation failure. Cloning FreeBinding only increments shared refs.
        let mut retained_bindings = Vec::new();
        if retained_bindings.try_reserve_exact(bindings.len()).is_err() {
            return;
        }
        size.bytes = size.bytes.saturating_add(
            retained_bindings
                .capacity()
                .saturating_sub(bindings.len())
                .saturating_mul(std::mem::size_of::<FreeBinding>()),
        );
        if !size.fits() {
            return;
        }
        if !tables.current.fits(size) {
            tables.previous = std::mem::take(&mut tables.current);
        }
        retained_bindings.extend_from_slice(bindings);
        if try_push_bucket(
            &mut tables.current.buckets,
            fp,
            Entry {
                input,
                delta_mode,
                head_nat,
                materialization,
                bindings: retained_bindings,
                result: value.result.clone(),
                nat_progress: value.nat_progress,
                copied: value.copied,
            },
        ) {
            tables.current.retained(size);
        }
    }
}

impl WhnfMemo {
    /// The completed KR-317 gate answer for this pair and materialization budget.
    /// Other conversion work limits are fixed at `K_GATE_CONVERSION_WORK`; the
    /// caller's materialization limits are not. Replay the saved charges even
    /// though no conversion is executed. In Cpop, 240 misses were 32 pairs.
    pub(super) fn recall_k_gate(
        &self,
        domain: &WireExpr,
        result: &WireExpr,
        materialization: TermBudget,
    ) -> Option<RememberedKGate> {
        let tables = self.0.lock().ok()?;
        let fp = pair_fingerprint(domain, result, materialization);
        tables
            .current
            .recall_k_gate(fp, domain, result, materialization)
            .or_else(|| {
                tables
                    .previous
                    .recall_k_gate(fp, domain, result, materialization)
            })
    }

    /// Record only a completed conversion, never a cancelled, faulted, deferred
    /// or resource-stopped attempt interpreted as a gate miss.
    pub(super) fn remember_k_gate(
        &self,
        domain: Arc<WireExpr>,
        result: Arc<WireExpr>,
        materialization: TermBudget,
        value: RememberedKGate,
    ) {
        let size = RetainedSize::pair(&domain, &result, std::mem::size_of::<GateEntry>());
        if !size.fits() {
            return;
        }
        let Ok(mut tables) = self.0.lock() else {
            return;
        };
        let fp = pair_fingerprint(&domain, &result, materialization);
        if tables.current.k_gate.get(&fp).is_some_and(|bucket| {
            bucket.len() >= MAX_BUCKET_ENTRIES
                || bucket.iter().any(|entry| {
                    entry.materialization == materialization
                        && entry.domain == domain
                        && entry.result == result
                })
        }) {
            return;
        }
        if !tables.current.fits(size) {
            tables.previous = std::mem::take(&mut tables.current);
        }
        if try_push_bucket(
            &mut tables.current.k_gate,
            fp,
            GateEntry {
                domain,
                result,
                materialization,
                value,
            },
        ) {
            tables.current.retained(size);
        }
    }
}

fn pair_fingerprint(domain: &WireExpr, result: &WireExpr, materialization: TermBudget) -> u64 {
    let mut hasher = Fingerprinter::default();
    domain.hash(&mut hasher);
    result.hash(&mut hasher);
    materialization.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::{BinderStyle, LevelNode, NamePart};

    fn name(text: &str) -> WireName {
        WireName::from_parts(vec![NamePart::Text(text.to_owned())])
    }

    fn id(index: usize) -> ExprId {
        ExprId::from_index(index).expect("small test index")
    }

    /// `(fun y : Sort 0 => y) x`: one beta step to the free local `x`.
    fn identity_at_x() -> WireExpr {
        WireExpr::from_parts(
            vec![
                ExprNode::Sort {
                    level: LevelId::ZERO,
                },
                ExprNode::Bound { index: 0 },
                ExprNode::Lambda {
                    binder_name: name("y"),
                    binder_type: id(0),
                    body: id(1),
                    style: BinderStyle::Default,
                },
                ExprNode::Free { name: name("x") },
                ExprNode::Apply {
                    function: id(2),
                    argument: id(3),
                },
            ],
            vec![LevelNode::Zero],
            id(4),
        )
    }

    fn sort_zero() -> WireExpr {
        WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: LevelId::ZERO,
            }],
            vec![LevelNode::Zero],
            ExprId::ZERO,
        )
    }

    fn normal_form(term: &WireExpr, context: &WhnfContext) -> ExprNode {
        match whnf(term, context, WhnfBudget::unlimited()) {
            WhnfOutcome::Complete(result) => result
                .term
                .node(result.term.root())
                .expect("a complete result has its root")
                .clone(),
            other => panic!("the test term must normalize: {other:?}"),
        }
    }

    fn constant(text: &str) -> WireExpr {
        WireExpr::from_parts(
            vec![ExprNode::Constant {
                name: name(text),
                levels: Vec::new(),
            }],
            Vec::new(),
            ExprId::ZERO,
        )
    }

    #[test]
    fn a_result_is_remembered_for_its_delta_mode_only() {
        use crate::environment::{
            ConstantDeclaration, ConstantEntry, ConstantSafety, DefinitionBody, DefinitionSafety,
            EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
        };
        let entry = ConstantEntry::new(
            name("link"),
            ConstantDeclaration::definition(
                Vec::new(),
                sort_zero(),
                ConstantSafety::Safe,
                DefinitionBody::new(
                    constant("target"),
                    ReducibilityHint::Regular(1),
                    DefinitionSafety::Safe,
                    Vec::new(),
                ),
            ),
        );
        let EnvironmentOutcome::Complete { environment, .. } =
            ConstantEnvironment::build(vec![entry], EnvironmentBudget::unlimited())
        else {
            panic!("the test environment must build");
        };
        let context = WhnfContext::new(Vec::new(), Vec::new(), environment);
        let link = constant("link");
        // Eager reduction unfolds `link`, and that result is remembered...
        assert_eq!(normal_form(&link, &context), constant("target").nodes()[0]);
        // ...but core reduction never unfolds, so it must still stop at `link`.
        let core = whnf_core_at_with(
            &link,
            link.root(),
            &context,
            WhnfBudget::unlimited(),
            &mut || false,
        );
        let WhnfOutcome::Complete(core) = core else {
            panic!("core reduction must complete: {core:?}");
        };
        assert_eq!(core.term, link);
    }

    #[test]
    fn a_full_bucket_takes_no_more_entries() {
        let entry = |index: usize| Entry {
            input: Arc::new(constant(&format!("c{index}"))),
            delta_mode: DeltaMode::Eager,
            head_nat: NatReductionScope::WhnfHead,
            materialization: TermBudget::unlimited(),
            bindings: Vec::new(),
            result: WhnfResult {
                term: constant("done"),
                steps: 1,
                reductions: 1,
                delta_reductions: 0,
                has_auxiliary_work: false,
                string_progress: StringExpansionProgress::default(),
            },
            nat_progress: WhnfNatProgress::default(),
            copied: false,
        };
        let admits_fresh = |bucket: &[Entry]| {
            admits(
                bucket,
                &constant("fresh"),
                DeltaMode::Eager,
                NatReductionScope::WhnfHead,
                TermBudget::unlimited(),
                &[],
            )
        };
        let mut bucket: Vec<Entry> = (1..MAX_BUCKET_ENTRIES).map(entry).collect();
        assert!(
            admits_fresh(&bucket),
            "a bucket with room takes a new input"
        );
        assert!(
            !admits(
                &bucket,
                &constant("c1"),
                DeltaMode::Eager,
                NatReductionScope::WhnfHead,
                TermBudget::unlimited(),
                &[],
            ),
            "an input already present is not added twice"
        );
        bucket.push(entry(MAX_BUCKET_ENTRIES));
        assert!(!admits_fresh(&bucket), "a full bucket takes nothing more");
    }

    #[test]
    fn a_let_bound_local_keeps_remembered_results_out() {
        let term = identity_at_x();
        let mut context = WhnfContext::default();
        // Without a binding for `x` the result is `x` itself, and it is remembered.
        assert_eq!(
            normal_form(&term, &context),
            ExprNode::Free { name: name("x") }
        );
        // With `x := Sort 0` in scope the same term must reach `Sort 0`, not the
        // result remembered without it.
        context.push_scoped_binding(FreeBinding::new(name("x"), sort_zero()));
        assert_eq!(
            normal_form(&term, &context),
            ExprNode::Sort {
                level: LevelId::ZERO
            }
        );
        assert!(context.pop_scoped_binding(&name("x")));
        assert_eq!(
            normal_form(&term, &context),
            ExprNode::Free { name: name("x") }
        );
    }

    fn remembered(context: &WhnfContext) -> usize {
        let tables = context.memo.0.lock().expect("the memo lock");
        tables.current.entries + tables.previous.entries
    }

    /// Under a let-bound local the memo is used: the result is recorded with
    /// the binding it was computed under.
    #[test]
    fn a_result_under_a_let_bound_local_is_remembered() {
        let mut context = WhnfContext::default();
        context.push_scoped_binding(FreeBinding::new(name("x"), constant("a")));
        assert_eq!(
            normal_form(&identity_at_x(), &context),
            constant("a").nodes()[0]
        );
        assert_eq!(remembered(&context), 1);
    }

    fn unused_value(label: &str, nodes: usize) -> WireExpr {
        let mut arena = vec![ExprNode::Constant {
            name: name(label),
            levels: Vec::new(),
        }];
        for index in 1..nodes {
            arena.push(ExprNode::Apply {
                function: id(index - 1),
                argument: ExprId::ZERO,
            });
        }
        WireExpr::from_parts(arena, Vec::new(), id(nodes - 1))
    }

    fn bind_unused(context: &mut WhnfContext, value: &Arc<WireExpr>, count: usize) {
        for index in 0..count {
            context.push_scoped_binding(FreeBinding::from_shared(
                name(&format!("unused{index}")),
                Arc::clone(value),
            ));
        }
    }

    /// Use shared values to cross the conservative retention bound without
    /// allocating hundreds of megabytes in a unit test. These values are not
    /// read by the reduction, but the old memo kept every one after scope exit.
    fn assert_unused_values_are_not_retained(value: WireExpr, count: usize) {
        let value = Arc::new(value);
        let weak = Arc::downgrade(&value);
        let mut context = WhnfContext::default();
        bind_unused(&mut context, &value, count);
        drop(value);
        let input = identity_at_x();
        let first = whnf(&input, &context, WhnfBudget::unlimited());
        assert!(matches!(first, WhnfOutcome::Complete(_)), "{first:?}");
        assert_eq!(remembered(&context), 0);
        assert_eq!(whnf(&input, &context, WhnfBudget::unlimited()), first);
        context.free_bindings.clear();
        assert!(
            weak.upgrade().is_none(),
            "the memo retained an expired local"
        );
        assert_eq!(
            normal_form(&input, &context),
            ExprNode::Free { name: name("x") }
        );
        assert_eq!(remembered(&context), 1, "ordinary results still cache");
    }

    #[test]
    fn unused_let_values_count_toward_the_memo_node_limit() {
        const NODES: usize = 4096;
        assert_unused_values_are_not_retained(
            unused_value("held", NODES),
            MAX_STORED_NODES / NODES + 1,
        );
    }

    #[test]
    fn unused_let_universes_count_even_when_expression_arenas_are_small() {
        const LEVELS: usize = 4096;
        let levels = vec![LevelNode::Parameter(name("u")); LEVELS];
        let level_ids = (0..LEVELS)
            .map(|index| LevelId::from_index(index).expect("small level index"))
            .collect();
        let value = WireExpr::from_parts(
            vec![ExprNode::Constant {
                name: name("held"),
                levels: level_ids,
            }],
            levels,
            ExprId::ZERO,
        );
        assert_unused_values_are_not_retained(value, MAX_STORED_NODES / LEVELS + 1);
    }

    #[test]
    fn spare_literal_capacity_counts_toward_the_memo_byte_limit() {
        const CAPACITY: usize = 1024 * 1024;
        let mut text = String::with_capacity(CAPACITY);
        text.push('x');
        let value = WireExpr::from_parts(
            vec![ExprNode::StringLiteral(text)],
            Vec::new(),
            ExprId::ZERO,
        );
        assert_unused_values_are_not_retained(value, MAX_STORED_BYTES / CAPACITY + 1);
    }

    #[test]
    fn rotation_releases_old_let_values_at_the_aggregate_limit() {
        const NODES: usize = 4096;
        let count = MAX_STORED_NODES / (2 * NODES) + 1;
        let mut context = WhnfContext::default();
        let mut oldest = None;
        for label in ["first", "second", "third"] {
            let value = Arc::new(unused_value(label, NODES));
            if oldest.is_none() {
                oldest = Some(Arc::downgrade(&value));
            }
            bind_unused(&mut context, &value, count);
            assert_eq!(
                normal_form(&identity_at_x(), &context),
                ExprNode::Free { name: name("x") }
            );
            context.free_bindings.clear();
        }
        assert!(oldest.unwrap().upgrade().is_none());
        assert_eq!(remembered(&context), 2, "only two generations survive");
        let tables = context.memo.0.lock().expect("the memo lock");
        for table in [&tables.current, &tables.previous] {
            assert!(table.stored_nodes <= MAX_STORED_NODES);
            assert!(table.stored_bytes <= MAX_STORED_BYTES);
        }
    }

    #[test]
    fn retained_results_preserve_cold_outcomes_and_tight_budget_stops() {
        let input = identity_at_x();
        let context = WhnfContext::default();
        let complete = whnf(&input, &context, WhnfBudget::unlimited());
        let WhnfOutcome::Complete(result) = &complete else {
            panic!("the control must reduce: {complete:?}");
        };
        assert_eq!(remembered(&context), 1);
        let budgets = [
            WhnfBudget::unlimited(),
            WhnfBudget::new(result.steps - 1, u64::MAX, TermBudget::unlimited()),
            WhnfBudget::new(u64::MAX, result.reductions - 1, TermBudget::unlimited()),
            WhnfBudget::new(u64::MAX, u64::MAX, TermBudget::new(0, u64::MAX)),
        ];
        for budget in budgets {
            assert_eq!(
                whnf(&input, &context, budget),
                whnf(&input, &WhnfContext::default(), budget),
                "retention must not change the verdict or its fuel accounting"
            );
        }
    }

    /// The same name bound to another value is another binding set: the result
    /// remembered under `x := a` must not answer for `x := b`, though the input
    /// and the binding names are the same.
    #[test]
    fn a_remembered_result_belongs_to_its_let_values_not_their_names() {
        let term = identity_at_x();
        let mut context = WhnfContext::default();
        context.push_scoped_binding(FreeBinding::new(name("x"), constant("a")));
        assert_eq!(normal_form(&term, &context), constant("a").nodes()[0]);
        assert!(context.pop_scoped_binding(&name("x")));
        context.push_scoped_binding(FreeBinding::new(name("x"), constant("b")));
        assert_eq!(normal_form(&term, &context), constant("b").nodes()[0]);
        // Bound to `a` again, the first result answers without a new entry.
        assert!(context.pop_scoped_binding(&name("x")));
        context.push_scoped_binding(FreeBinding::new(name("x"), constant("a")));
        assert_eq!(normal_form(&term, &context), constant("a").nodes()[0]);
        assert_eq!(remembered(&context), 2);
    }

    /// The closed type-level beta redex `(fun X : Sort 1 => X) (Sort 0)`.
    fn k_gate_beta_pair() -> (Arc<WireExpr>, Arc<WireExpr>) {
        let domain = WireExpr::from_parts(
            vec![
                ExprNode::Sort {
                    level: id_level(1),
                },
                ExprNode::Bound { index: 0 },
                ExprNode::Lambda {
                    binder_name: name("X"),
                    binder_type: id(0),
                    body: id(1),
                    style: BinderStyle::Default,
                },
                ExprNode::Sort {
                    level: LevelId::ZERO,
                },
                ExprNode::Apply {
                    function: id(2),
                    argument: id(3),
                },
            ],
            vec![LevelNode::Zero, LevelNode::Succ(LevelId::ZERO)],
            id(4),
        );
        let result = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: LevelId::ZERO,
            }],
            vec![LevelNode::Zero],
            id(0),
        );
        (Arc::new(domain), Arc::new(result))
    }

    fn id_level(index: usize) -> LevelId {
        LevelId::from_index(index).expect("small test level")
    }

    /// Run the actual conversion gate, including its outer budget check, without
    /// a whole-term WHNF entry hiding the gate cache being exercised.
    fn run_k_gate(
        context: &WhnfContext,
        domain: &Arc<WireExpr>,
        result: &Arc<WireExpr>,
        budget: WhnfBudget,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> (Result<bool, WhnfOutcome>, u64, u64) {
        let mut control = Control::new(budget);
        let prepared = match PreparedContext::prepare(context, &mut control, cancelled) {
            Ok(prepared) => prepared,
            Err(halt) => {
                return (Err(outcome(Err(halt))), control.steps, control.reductions);
            }
        };
        let mut reducer = Reducer {
            context: prepared,
            control,
            cancelled,
            unfolded_bindings: BTreeSet::new(),
            acyclic_bindings: BTreeSet::new(),
            delta_mode: DeltaMode::Eager,
            head_nat: NatReductionScope::WhnfHead,
            numeric_budget: None,
            nat_progress: WhnfNatProgress::default(),
            nat_pow_cap: None,
            delta_reductions: 0,
            discarded_reductions: 0,
            discarded_delta_reductions: 0,
            has_auxiliary_work: false,
            string_progress: StringExpansionProgress::default(),
            force_string_delta: false,
            skip_nat: false,
            facts: FastHashMap::default(),
            string_expansions: FastHashMap::default(),
            bodies: FastHashMap::default(),
            keyed_thunks: FastHashMap::default(),
            entry: None,
            copied_result: false,
        };
        let answer = match reducer.k_constructor_types_convert(domain, result, 0) {
            Ok(equal) => Ok(equal),
            Err(halt) => Err(outcome(Err(halt))),
        };
        (answer, reducer.control.steps, reducer.control.reductions)
    }

    fn remembered_gates(context: &WhnfContext) -> usize {
        let tables = context.memo.0.lock().expect("unpoisoned test memo");
        tables.current.k_gate.values().map(Vec::len).sum::<usize>()
            + tables.previous.k_gate.values().map(Vec::len).sum::<usize>()
    }

    #[test]
    fn k_gate_materialization_limits_are_isolated_in_both_orders() {
        let (domain, result) = k_gate_beta_pair();
        let unlimited = WhnfBudget::unlimited();
        let cold_full = run_k_gate(
            &WhnfContext::default(),
            &domain,
            &result,
            unlimited,
            &mut || false,
        );
        assert_eq!(cold_full.0, Ok(true));
        for materialization in [
            TermBudget::new(0, u64::MAX),
            TermBudget::new(u64::MAX, 0),
            TermBudget::unlimited().with_max_arena_nodes(0),
        ] {
            let limited = WhnfBudget::new(u64::MAX, u64::MAX, materialization);
            let context = WhnfContext::default();
            let cold_limited = run_k_gate(&context, &domain, &result, limited, &mut || false);
            assert_eq!(cold_limited.0, Ok(false));
            assert_eq!(
                remembered_gates(&context),
                0,
                "a resource stop must not become a cached negative answer"
            );
            assert_eq!(
                run_k_gate(&context, &domain, &result, unlimited, &mut || false),
                cold_full,
                "a stopped attempt must not poison the larger-budget retry"
            );
            assert_eq!(remembered_gates(&context), 1);

            let context = WhnfContext::default();
            assert_eq!(
                run_k_gate(&context, &domain, &result, unlimited, &mut || false),
                cold_full
            );
            assert_eq!(
                run_k_gate(&context, &domain, &result, limited, &mut || false),
                cold_limited,
                "a cached answer must not bypass smaller materialization limits"
            );
            assert_eq!(remembered_gates(&context), 1);
        }
    }

    #[test]
    fn k_gate_hits_replay_work_before_enforcing_the_outer_step_budget() {
        let (domain, result) = k_gate_beta_pair();
        let context = WhnfContext::default();
        let full = run_k_gate(
            &context,
            &domain,
            &result,
            WhnfBudget::unlimited(),
            &mut || false,
        );
        assert_eq!(full.0, Ok(true));
        assert!(
            full.1 > 1 && full.2 > 0,
            "the gate must perform real conversion work"
        );
        assert_eq!(
            run_k_gate(
                &context,
                &domain,
                &result,
                WhnfBudget::unlimited(),
                &mut || false,
            ),
            full,
            "a hit must replay both step and reduction charges"
        );
        let tight = WhnfBudget::new(full.1 - 1, u64::MAX, TermBudget::unlimited());
        let cold = run_k_gate(
            &WhnfContext::default(),
            &domain,
            &result,
            tight,
            &mut || false,
        );
        assert!(matches!(
            &cold.0,
            Err(WhnfOutcome::Inconclusive(WhnfStop::Resource {
                limit: WhnfLimit::Steps,
                ..
            }))
        ));
        assert_eq!(
            run_k_gate(&context, &domain, &result, tight, &mut || false),
            cold,
            "the cached gate must stop at the same limit with the same progress"
        );
        assert!(matches!(
            run_k_gate(
                &context,
                &domain,
                &result,
                WhnfBudget::unlimited(),
                &mut || true,
            )
            .0,
            Err(WhnfOutcome::Inconclusive(WhnfStop::Cancelled { .. }))
        ));
    }
}
