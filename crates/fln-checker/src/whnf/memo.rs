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
//! - it is used only while the context has no let-bound locals. Reduction then
//!   reads nothing but its input, the constants and the projection rules, and a
//!   context never changes those; a clone, which shares the memo, has the same;
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
    result: WhnfResult,
}

impl Entry {
    fn matches(
        &self,
        input: &WireExpr,
        delta_mode: DeltaMode,
        materialization: TermBudget,
    ) -> bool {
        self.delta_mode == delta_mode
            && self.materialization == materialization
            && *self.input == *input
    }
}

/// Whether a bucket takes a new entry: it is not full, and holds no equal one.
fn admits(
    bucket: &[Entry],
    input: &WireExpr,
    delta_mode: DeltaMode,
    materialization: TermBudget,
) -> bool {
    bucket.len() < MAX_BUCKET_ENTRIES
        && !bucket
            .iter()
            .any(|entry| entry.matches(input, delta_mode, materialization))
}

/// Past either bound the memo stops growing; lookups continue. A memo lives as
/// long as its context, one declaration's check, so both bound its memory.
const MAX_ENTRIES: usize = 1 << 16;
const MAX_STORED_NODES: usize = 1 << 20;
/// A full bucket takes no more entries, so no input, however it collides, makes
/// a lookup compare more than this many terms.
const MAX_BUCKET_ENTRIES: usize = 8;

#[derive(Default)]
struct Table {
    /// Keyed by a fixed fingerprint, so the order of results never depends on the
    /// process; entries in a bucket are compared exactly.
    buckets: HashMap<u64, Vec<Entry>>,
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
/// declaration's check.
#[derive(Default)]
struct Fingerprinter(u64);

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

fn fingerprint(input: &WireExpr, delta_mode: DeltaMode, materialization: TermBudget) -> u64 {
    let mut hasher = Fingerprinter::default();
    input.hash(&mut hasher);
    delta_mode.hash(&mut hasher);
    materialization.hash(&mut hasher);
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
    ) -> Option<WhnfResult> {
        let table = self.0.lock().ok()?;
        table
            .buckets
            .get(&fingerprint(input, delta_mode, budget.materialization))?
            .iter()
            .find(|entry| entry.matches(input, delta_mode, budget.materialization))
            .filter(|entry| covers(budget, &entry.result))
            .map(|entry| entry.result.clone())
    }

    /// Record a complete result. Results that reduced nothing are not worth a
    /// slot: recomputing them costs no more than the lookup.
    pub(super) fn remember(
        &self,
        input: Arc<WireExpr>,
        delta_mode: DeltaMode,
        materialization: TermBudget,
        result: &WhnfResult,
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
            .entry(fingerprint(&input, delta_mode, materialization))
            .or_default();
        if !admits(bucket, &input, delta_mode, materialization) {
            return;
        }
        bucket.push(Entry {
            input,
            delta_mode,
            materialization,
            result: result.clone(),
        });
        table.entries += 1;
        table.stored_nodes = table.stored_nodes.saturating_add(nodes);
    }
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
            result: WhnfResult {
                term: constant("done"),
                steps: 1,
                reductions: 1,
                delta_reductions: 0,
                has_auxiliary_work: false,
                string_progress: StringExpansionProgress::default(),
            },
        };
        let admits_fresh = |bucket: &[Entry]| {
            admits(
                bucket,
                &constant("fresh"),
                DeltaMode::Eager,
                TermBudget::unlimited(),
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
                TermBudget::unlimited()
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
}
