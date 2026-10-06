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
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Mutex;

struct Entry {
    input: Arc<WireExpr>,
    delta_mode: DeltaMode,
    materialization: TermBudget,
    /// The let-bound locals in scope when `result` was computed.
    bindings: Vec<FreeBinding>,
    result: WhnfResult,
    /// Whether `result`'s term is the module's own copy of a term (`WhnfInput`).
    copied: bool,
}

impl Entry {
    fn matches(
        &self,
        input: &WireExpr,
        delta_mode: DeltaMode,
        materialization: TermBudget,
        bindings: &[FreeBinding],
    ) -> bool {
        self.delta_mode == delta_mode
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
    materialization: TermBudget,
    bindings: &[FreeBinding],
) -> bool {
    bucket.len() < MAX_BUCKET_ENTRIES
        && !bucket
            .iter()
            .any(|entry| entry.matches(input, delta_mode, materialization, bindings))
}

/// Past either bound the memo stops growing; lookups continue. A memo lives as
/// long as its context, one declaration's check, so both bound its memory.
const MAX_ENTRIES: usize = 1 << 16;
const MAX_STORED_NODES: usize = 1 << 20;
/// A full bucket takes no more entries, so no input, however it collides, makes
/// a lookup compare more than this many terms.
const MAX_BUCKET_ENTRIES: usize = 8;

/// One remembered KR-317 gate outcome: the two types compared and whether they
/// converted.
struct GateEntry {
    domain: Arc<WireExpr>,
    result: Arc<WireExpr>,
    equal: bool,
}

#[derive(Default)]
struct Table {
    /// Keyed by a fixed fingerprint, so the order of results never depends on the
    /// process; entries in a bucket are compared exactly.
    buckets: HashMap<u64, Vec<Entry>>,
    /// KR-317 gate outcomes by conversion, keyed the same way (see
    /// `WhnfMemo::recall_k_gate`). They share the entry and node bounds.
    k_gate: HashMap<u64, Vec<GateEntry>>,
    entries: usize,
    stored_nodes: usize,
}

/// Shared by a context and its clones. It carries no meaning of its own: two
/// contexts that are otherwise equal reduce alike whatever their memos hold, so
/// every memo compares equal.
#[derive(Clone, Default)]
pub(super) struct WhnfMemo(Arc<Mutex<Table>>);

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
pub(super) struct Fingerprinter(u64);

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
    materialization: TermBudget,
    bindings: &[FreeBinding],
) -> u64 {
    let mut hasher = Fingerprinter::default();
    input.hash(&mut hasher);
    delta_mode.hash(&mut hasher);
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

impl WhnfMemo {
    pub(super) fn recall(
        &self,
        input: &WireExpr,
        delta_mode: DeltaMode,
        budget: &WhnfBudget,
        bindings: &[FreeBinding],
    ) -> Option<(WhnfResult, bool)> {
        let table = self.0.lock().ok()?;
        table
            .buckets
            .get(&fingerprint(
                input,
                delta_mode,
                budget.materialization,
                bindings,
            ))?
            .iter()
            .find(|entry| entry.matches(input, delta_mode, budget.materialization, bindings))
            .filter(|entry| covers(budget, &entry.result))
            .map(|entry| (entry.result.clone(), entry.copied))
    }

    /// Record a complete result. Results that reduced nothing are not worth a
    /// slot: recomputing them costs no more than the lookup.
    pub(super) fn remember(
        &self,
        input: Arc<WireExpr>,
        delta_mode: DeltaMode,
        materialization: TermBudget,
        bindings: &[FreeBinding],
        result: &WhnfResult,
        copied: bool,
    ) {
        if result.reductions == 0 && result.delta_reductions == 0 {
            return;
        }
        let Ok(mut table) = self.0.lock() else {
            return;
        };
        let nodes = input
            .nodes()
            .len()
            .saturating_add(result.term.nodes().len());
        if table.entries >= MAX_ENTRIES
            || table.stored_nodes.saturating_add(nodes) > MAX_STORED_NODES
        {
            return;
        }
        let bucket = table
            .buckets
            .entry(fingerprint(&input, delta_mode, materialization, bindings))
            .or_default();
        if !admits(bucket, &input, delta_mode, materialization, bindings) {
            return;
        }
        bucket.push(Entry {
            input,
            delta_mode,
            materialization,
            bindings: bindings.to_vec(),
            result: result.clone(),
            copied,
        });
        table.entries += 1;
        table.stored_nodes = table.stored_nodes.saturating_add(nodes);
    }
}

impl WhnfMemo {
    /// The KR-317 gate's conversion outcome for exactly these two types, if one
    /// was recorded. The conversion runs on the fixed `K_GATE_CONVERSION_WORK`,
    /// so, as for the results above, its outcome depends only on the pair and
    /// the context: recording it changes no answer and saves the conversion. In
    /// Cpop, 240 gate misses were 32 distinct pairs.
    pub(super) fn recall_k_gate(&self, domain: &WireExpr, result: &WireExpr) -> Option<bool> {
        let table = self.0.lock().ok()?;
        table
            .k_gate
            .get(&pair_fingerprint(domain, result))?
            .iter()
            .find(|entry| *entry.domain == *domain && *entry.result == *result)
            .map(|entry| entry.equal)
    }

    /// Record a gate outcome. Never called for a cancelled or faulted
    /// conversion, whose outcome is not a function of the pair.
    pub(super) fn remember_k_gate(
        &self,
        domain: Arc<WireExpr>,
        result: Arc<WireExpr>,
        equal: bool,
    ) {
        let Ok(mut table) = self.0.lock() else {
            return;
        };
        let nodes = domain.nodes().len().saturating_add(result.nodes().len());
        if table.entries >= MAX_ENTRIES
            || table.stored_nodes.saturating_add(nodes) > MAX_STORED_NODES
        {
            return;
        }
        let bucket = table
            .k_gate
            .entry(pair_fingerprint(&domain, &result))
            .or_default();
        if bucket.len() >= MAX_BUCKET_ENTRIES
            || bucket
                .iter()
                .any(|entry| entry.domain == domain && entry.result == result)
        {
            return;
        }
        bucket.push(GateEntry {
            domain,
            result,
            equal,
        });
        table.entries += 1;
        table.stored_nodes = table.stored_nodes.saturating_add(nodes);
    }
}

fn pair_fingerprint(domain: &WireExpr, result: &WireExpr) -> u64 {
    let mut hasher = Fingerprinter::default();
    domain.hash(&mut hasher);
    result.hash(&mut hasher);
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
            copied: false,
        };
        let admits_fresh = |bucket: &[Entry]| {
            admits(
                bucket,
                &constant("fresh"),
                DeltaMode::Eager,
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
        context.memo.0.lock().expect("the memo lock").entries
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
}
