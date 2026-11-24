//! A typed, sufficient KR-305 conversion lane. The untyped converter cannot
//! identify proofs under binders because it has no local type context. This
//! worklist opens matching binders hygienically and uses checker-owned typing
//! to compare proofs of the same proposition, (KR-315) values of the same
//! unit-like structure type, and (KR-312) a lambda against a function that is
//! not one, by eta-expanding the latter through its Π-type, and a structure
//! constructor application against a term that is not one, field by field, and
//! (KR-317) a K recursor stuck on a major premise that is not a constructor
//! application, by reducing it as if the major were the nullary constructor.
//! Probes explicitly disable this lane, so nested conversion never recursively
//! reenters typed inference.
use super::*;
use crate::universe::{NormalNode, level_roots_equal, normalize};
use crate::wire::WireLevel;

/// The kind of task a pair of terms was taken on as, in the lane's worklist.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Taken {
    Pair,
    Binders,
    Eta(bool),
}

#[derive(Debug)]
pub(crate) enum ProofConversionOutcome {
    Complete { equal: bool, polls: u64 },
    Halted(Box<InferenceOutcome>),
}

/// A comparand expression in `Probe::run`, shared via `Arc` for O(1) clones
/// across worklist/memo entries and tagged with `copied` so WHNF skips
/// redundant input materialization (`WhnfInput::Copied`) across lazy-delta steps.
#[derive(Clone)]
struct Term {
    expr: Arc<WireExpr>,
    copied: bool,
}

impl Term {
    fn new(expr: WireExpr) -> Self {
        Self {
            expr: Arc::new(expr),
            copied: false,
        }
    }

    fn from_whnf(expr: WireExpr, copied: bool) -> Self {
        Self {
            expr: Arc::new(expr),
            copied,
        }
    }

    fn as_whnf_input(&self) -> crate::whnf::WhnfInput<'_> {
        if self.copied {
            crate::whnf::WhnfInput::Copied(&self.expr)
        } else {
            crate::whnf::WhnfInput::Borrowed(&self.expr)
        }
    }
}

impl std::ops::Deref for Term {
    type Target = WireExpr;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

struct Probe<'a> {
    budget: InferenceBudget,
    steps: u64,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
    stop: Option<InferenceStop>,
    root_left: &'a WireExpr,
    root_right: &'a WireExpr,
    root_context: &'a InferenceContext,
    reserved: Option<BTreeSet<WireName>>,
    unreserved_nested: Vec<(WireExpr, WireExpr)>,
    next: u64,
    /// Pairs whose congruence attempt failed. Like the pin's `failed_before`,
    /// it only stops the attempt being repeated; the pair itself takes the
    /// other rules.
    incongruent: PairSet,
    /// Pairs unconditionally proven convertible in this run (`m_eqv_manager` in
    /// `type_checker.cpp`), retained even when an enclosing congruence attempt
    /// fails on a sibling argument.
    proven: PairSet,
    /// Pairs that exhausted all rules of this lane in this run (`m_failure` in
    /// `type_checker.cpp`), preventing exponential re-exploration.
    disproven: PairSet,
    /// The untyped converter's answers in this run (`PairAnswers`).
    answers: PairAnswers,
    /// Types already inferred in this run (`InferredTypes`).
    inferred: InferredTypes,
    /// The local each binder and eta task opened (`OpenedLocals`).
    opened: OpenedLocals,
}
/// The local each binder and eta task of one run opened, by the task's key.
///
/// A failed congruence attempt gives back the tasks it took, so a later
/// decomposition opens the same binder pair again. On `MvPolynomial.degrees_def`
/// (bead `fln-kiq3`) 42% of 48,000 descents repeated one already made. Each
/// opened a fresh local, which made every pair below it new to `taken`,
/// `answers` and `incongruent`, so a repeat cost as much as the first descent
/// and the run never ended.
///
/// Opening the pair again at the local it was opened at before is opening it at
/// a fresh local, so nothing the lane concludes changes: that local does not
/// occur in the pair, since it was fresh for exactly this pair; it has the type
/// the pair's binder gives it, as before; and it is reused only when the context
/// does not already hold it. A local name thus still means one thing throughout
/// the run, as `taken` and `answers` require.
#[derive(Default)]
struct OpenedLocals {
    buckets: crate::whnf::memo::PrehashedMap<Vec<(Taken, WireExpr, WireExpr, WireName)>>,
    nodes: usize,
}
impl OpenedLocals {
    /// The keys' share of memory, as for one `PairAnswers` generation. Past it
    /// new tasks open fresh locals, as before.
    const MAX_NODES: usize = 1 << 21;
    fn get(
        &self,
        fingerprint: u64,
        kind: Taken,
        left: &WireExpr,
        right: &WireExpr,
    ) -> Option<&WireName> {
        self.buckets
            .get(&fingerprint)?
            .iter()
            .find(|(k, l, r, _)| *k == kind && l == left && r == right)
            .map(|(_, _, _, name)| name)
    }
    fn insert(
        &mut self,
        fingerprint: u64,
        kind: Taken,
        left: &WireExpr,
        right: &WireExpr,
        name: WireName,
    ) {
        let nodes = left.nodes().len().saturating_add(right.nodes().len());
        if self.nodes.saturating_add(nodes) > Self::MAX_NODES
            || self.get(fingerprint, kind, left, right).is_some()
        {
            return;
        }
        self.buckets.entry(fingerprint).or_default().push((
            kind,
            left.clone(),
            right.clone(),
            name,
        ));
        self.nodes += nodes;
    }
}

/// Inferred types already obtained in one run (`m_infer_type` in the vendored
/// `type_checker.cpp`).
///
/// Every local name in one `Probe` run has a unique declaration (`root_context`
/// locals are fixed, and `OpenedLocals` binds each fresh name to one `domain`),
/// and every query runs under the same `self.budget` and `InferOnly` mode.
/// When every `Free` variable occurring in `term` is bound in `context`, the
/// inferred type is identical across contexts of this run. Stops and faults are
/// never recorded.
#[derive(Default)]
struct InferredTypes {
    current: InferredTypeTable,
    previous: InferredTypeTable,
}
#[derive(Default)]
struct InferredTypeTable {
    buckets: crate::whnf::memo::PrehashedMap<Vec<(WireExpr, Option<WireExpr>)>>,
    nodes: usize,
}
impl InferredTypeTable {
    fn get(&self, fingerprint: u64, term: &WireExpr) -> Option<Option<WireExpr>> {
        self.buckets
            .get(&fingerprint)?
            .iter()
            .find(|(stored, _)| stored == term)
            .map(|(_, answer)| answer.clone())
    }
}
impl InferredTypes {
    const MAX_GENERATION_NODES: usize = 1 << 20;
    const MAX_BUCKET: usize = 8;
    fn fingerprint(term: &WireExpr) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = crate::whnf::memo::Fingerprinter::default();
        term.hash(&mut hasher);
        hasher.finish()
    }
    fn get(&self, fingerprint: u64, term: &WireExpr) -> Option<Option<WireExpr>> {
        self.current
            .get(fingerprint, term)
            .or_else(|| self.previous.get(fingerprint, term))
    }
    fn insert(&mut self, fingerprint: u64, term: &WireExpr, answer: Option<WireExpr>) {
        let answer_nodes = answer.as_ref().map_or(0, |ty| ty.nodes().len());
        let nodes = term.nodes().len().saturating_add(answer_nodes);
        if nodes > Self::MAX_GENERATION_NODES {
            return;
        }
        if self.current.nodes.saturating_add(nodes) > Self::MAX_GENERATION_NODES {
            self.previous = std::mem::take(&mut self.current);
        }
        let bucket = self.current.buckets.entry(fingerprint).or_default();
        if bucket.len() < Self::MAX_BUCKET && !bucket.iter().any(|(stored, _)| stored == term) {
            bucket.push((term.clone(), answer));
            self.current.nodes += nodes;
        }
    }
}

fn all_free_locals_in_context(term: &WireExpr, context: &InferenceContext) -> bool {
    term.nodes().iter().all(|node| match node {
        ExprNode::Free { name } => context.local(name).is_some(),
        _ => true,
    })
}
/// A bounded two-generation set of term pairs, looked up without copying the terms.
#[derive(Default)]
pub(super) struct PairSet {
    current: PairSetTable,
    previous: PairSetTable,
}
#[derive(Default)]
struct PairSetTable {
    buckets: crate::whnf::memo::PrehashedMap<Vec<(Arc<WireExpr>, Arc<WireExpr>)>>,
    nodes: usize,
}
impl PairSetTable {
    fn contains(&self, fingerprint: u64, left: &WireExpr, right: &WireExpr) -> bool {
        !self.buckets.is_empty()
            && self
                .buckets
                .get(&fingerprint)
                .is_some_and(|pairs| pairs.iter().any(|(l, r)| **l == *left && **r == *right))
    }
}
impl PairSet {
    const MAX_GENERATION_NODES: usize = 1 << 20;
    const MAX_BUCKET: usize = 8;
    pub(super) fn fingerprint(left: &WireExpr, right: &WireExpr) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = crate::whnf::memo::Fingerprinter::default();
        left.hash(&mut hasher);
        right.hash(&mut hasher);
        hasher.finish()
    }
    fn contains(&self, left: &WireExpr, right: &WireExpr) -> bool {
        let fingerprint = Self::fingerprint(left, right);
        self.current.contains(fingerprint, left, right)
            || self.previous.contains(fingerprint, left, right)
    }
    fn insert(&mut self, left: Arc<WireExpr>, right: Arc<WireExpr>) {
        let fingerprint = Self::fingerprint(&left, &right);
        if self.current.contains(fingerprint, &left, &right)
            || self.previous.contains(fingerprint, &left, &right)
        {
            return;
        }
        let nodes = left.nodes().len().saturating_add(right.nodes().len());
        if nodes > Self::MAX_GENERATION_NODES {
            return;
        }
        if self.current.nodes.saturating_add(nodes) > Self::MAX_GENERATION_NODES {
            self.previous = std::mem::take(&mut self.current);
        }
        let bucket = self.current.buckets.entry(fingerprint).or_default();
        if bucket.len() < Self::MAX_BUCKET {
            bucket.push((left, right));
            self.current.nodes += nodes;
        }
    }
}

/// Cross-call positive conversion memo for one `InferenceEngine` run.
///
/// Records only proven `ConversionMode::Ordinary` equalities together with the
/// inference step count they required. Every local name in an `InferenceEngine`
/// run is either an immutable caller local or a monotonically fresh
/// `_fln_checker_local.<N>` that is never rebound to another value, so a pair
/// proven convertible once remains convertible throughout that run. Refusals,
/// deferrals, stops, and faults are never cached, and a hit is taken only when
/// the remaining inference step budget covers `steps_needed`.
#[derive(Default)]
pub(super) struct DomainEqualityCache {
    current: DomainEqualityTable,
    previous: DomainEqualityTable,
}
#[derive(Default)]
struct DomainEqualityTable {
    buckets: crate::whnf::memo::PrehashedMap<Vec<(WireExpr, WireExpr, u64)>>,
    nodes: usize,
}
impl DomainEqualityTable {
    fn get(&self, fingerprint: u64, left: &WireExpr, right: &WireExpr) -> Option<u64> {
        self.buckets
            .get(&fingerprint)?
            .iter()
            .find(|(l, r, _)| l == left && r == right)
            .map(|(_, _, steps)| *steps)
    }
}
impl DomainEqualityCache {
    const MAX_GENERATION_NODES: usize = 1 << 20;
    const MAX_BUCKET: usize = 8;
    pub(super) fn get(&self, fingerprint: u64, left: &WireExpr, right: &WireExpr) -> Option<u64> {
        self.current
            .get(fingerprint, left, right)
            .or_else(|| self.previous.get(fingerprint, left, right))
    }
    pub(super) fn insert(
        &mut self,
        fingerprint: u64,
        left: &WireExpr,
        right: &WireExpr,
        steps_needed: u64,
    ) {
        if self.get(fingerprint, left, right).is_some() {
            return;
        }
        let nodes = left.nodes().len().saturating_add(right.nodes().len());
        if nodes > Self::MAX_GENERATION_NODES {
            return;
        }
        if self.current.nodes.saturating_add(nodes) > Self::MAX_GENERATION_NODES {
            self.previous = std::mem::take(&mut self.current);
        }
        let bucket = self.current.buckets.entry(fingerprint).or_default();
        if bucket.len() < Self::MAX_BUCKET {
            bucket.push((left.clone(), right.clone(), steps_needed));
            self.current.nodes += nodes;
        }
    }
}
/// The untyped converter's answers already obtained in one run, by pair.
///
/// The same pairs are asked again and again: a failed congruence attempt gives
/// back the obligations it took, and the decompositions that follow re-ask
/// them. On `TensorProduct.rightComm_def` (bead
/// `fln-checker-associator-time-y8wc`), 91,603 of 107,837 untyped queries
/// repeated a pair already asked in the same run, and those queries were nearly
/// all of the declaration's time. The pin answers a repeat from its conversion
/// caches (`m_eqv_manager`, `m_failure` in the vendored `type_checker.cpp`).
///
/// An answer is reused only within the run that obtained it, for the reason
/// `taken` is: local names are fresh and bound once, so a pair of terms means
/// the same thing in every context of one run, and every query runs under the
/// same fresh conversion budget, so asking again would return the same answer.
/// A stop or a fault is never recorded: it ends the run.
///
/// Memory is bounded by generations. A pair is asked again soon after it was
/// given back, so the record keeps the recent pairs: when the current table
/// holds `MAX_GENERATION_NODES` nodes it becomes the previous one, the previous
/// one is dropped, and both are consulted. A dropped pair is simply asked again.
#[derive(Default)]
struct PairAnswers {
    current: PairTable,
    previous: PairTable,
}
#[derive(Default)]
struct PairTable {
    buckets: crate::whnf::memo::PrehashedMap<Vec<(WireExpr, WireExpr, Option<bool>)>>,
    nodes: usize,
}
impl PairTable {
    fn get(&self, fingerprint: u64, left: &WireExpr, right: &WireExpr) -> Option<Option<bool>> {
        self.buckets
            .get(&fingerprint)?
            .iter()
            .find(|(l, r, _)| l == left && r == right)
            .map(|(_, _, answer)| *answer)
    }
}
impl PairAnswers {
    /// About a hundred megabytes of terms per generation.
    const MAX_GENERATION_NODES: usize = 1 << 21;
    /// A full bucket takes no more pairs, so no collision makes a lookup
    /// compare more than this many.
    const MAX_BUCKET: usize = 8;
    fn get(&self, fingerprint: u64, left: &WireExpr, right: &WireExpr) -> Option<Option<bool>> {
        self.current
            .get(fingerprint, left, right)
            .or_else(|| self.previous.get(fingerprint, left, right))
    }
    fn insert(
        &mut self,
        fingerprint: u64,
        left: &WireExpr,
        right: &WireExpr,
        answer: Option<bool>,
    ) {
        let nodes = left.nodes().len().saturating_add(right.nodes().len());
        if nodes > Self::MAX_GENERATION_NODES {
            return;
        }
        if self.current.nodes.saturating_add(nodes) > Self::MAX_GENERATION_NODES {
            self.previous = std::mem::take(&mut self.current);
        }
        let bucket = self.current.buckets.entry(fingerprint).or_default();
        if bucket.len() < Self::MAX_BUCKET {
            bucket.push((left.clone(), right.clone(), answer));
            self.current.nodes += nodes;
        }
    }
}
/// How many stuck recursor majors and projected structures `nested_k_reduction`
/// follows down.
const MAX_NESTED_K_DEPTH: usize = 8;

/// Which steps `nested_k_reduction` may take down from a term.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reach {
    /// Recursor majors only: the eager rule, tried on every pair that gets there.
    Majors,
    /// Recursor majors and projected structures: tried whenever the spine head
    /// is a projection whose in-place chain reaches a K-like recursor
    /// (`reaches_k_recursor`), including when both sides share the same
    /// projection head. Skipping shared projection heads would strip the
    /// projection irrevocably and force equality on unrelated fields of the
    /// projected structure (`TopCat.Presheaf.generateEquivalenceOpensLe._proof_2`:
    /// `f.hom.right ≟ (eqToHom h).hom.right`). Keeping the zero-WHNF
    /// `reaches_k_recursor` guard avoids the projection-WHNF cost on BVDecide
    /// and DHashMap.
    MajorsAndProjections,
}

/// Whether a comparand's type is known to inhabit `Prop`, known not to, or
/// could not be inferred without further reduction.
enum ProofStatus {
    Proof(WireExpr),
    NotProof,
    Unknown,
}

/// Whether `term`'s spine head is a `Theorem` constant (always proof-valued
/// when fully applied, so proof irrelevance should run before congruence).
fn is_theorem_head(term: &WireExpr, context: &InferenceContext) -> bool {
    head_constant(term)
        .and_then(|name| context.constants().find(name))
        .is_some_and(|decl| decl.kind() == crate::environment::ConstantKind::Theorem)
}

/// How `nested_k_reduction` reached the next term down from the current one.
enum Descent {
    /// The recursor's major premise, at this spine position.
    Major(usize),
    /// The structure of the projection at the head of the spine.
    Projection,
}
type Result<T> = std::result::Result<T, Box<InferenceOutcome>>;
impl Probe<'_> {
    fn progress(&self) -> InferenceProgress {
        InferenceProgress {
            steps: self.steps,
            ..InferenceProgress::default()
        }
    }
    fn poll(&mut self) -> bool {
        if self.stop.is_some() {
            return true;
        }
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            self.stop = Some(InferenceStop::Cancelled {
                phase: InferencePhase::DomainComparison,
                at: 0,
                polls: self.polls,
                progress: self.progress(),
            });
        }
        self.stop.is_some()
    }
    fn tick(&mut self) -> Result<()> {
        if self.poll() {
            return self.check_stop();
        }
        self.steps = self.steps.saturating_add(1);
        if self.steps > self.budget.max_steps {
            self.stop = Some(InferenceStop::Resource {
                limit: InferenceLimit::Steps,
                allowed: self.budget.max_steps,
                observed: self.steps,
                phase: InferencePhase::DomainComparison,
                at: 0,
                progress: self.progress(),
            });
        }
        self.check_stop()
    }
    fn check_stop(&mut self) -> Result<()> {
        if let Some(stop) = self.stop.take() {
            Err(Box::new(InferenceOutcome::Inconclusive(stop)))
        } else {
            Ok(())
        }
    }
    fn fault(&self, fault: InferenceFault) -> Box<InferenceOutcome> {
        Box::new(InferenceOutcome::InternalFault {
            fault,
            progress: self.progress(),
        })
    }
    fn term(&mut self, result: TermOutcome<WireExpr>) -> Result<WireExpr> {
        self.check_stop()?;
        match result {
            TermOutcome::Complete(term) => Ok(term),
            TermOutcome::Inconclusive(stop) => Err(Box::new(InferenceOutcome::Inconclusive(
                InferenceStop::Materialization {
                    phase: InferencePhase::DomainComparison,
                    stop,
                    progress: self.progress(),
                },
            ))),
            TermOutcome::InternalFault(fault) => Err(self.fault(InferenceFault::Materialization {
                phase: InferencePhase::DomainComparison,
                fault,
            })),
        }
    }
    fn piece(&mut self, term: &WireExpr, root: ExprId) -> Result<WireExpr> {
        let budget = self.budget.materialization;
        let result = copy_compact_subterm_with(term, root, budget, &mut || self.poll());
        self.term(result)
    }
    fn open(&mut self, term: &WireExpr, body: ExprId, local: &WireExpr) -> Result<WireExpr> {
        let budget = self.budget.materialization;
        let result =
            substitute_bound_subterms_with(term, body, 0, local, local.root(), budget, &mut || {
                self.poll()
            });
        self.term(result)
    }
    fn reserve(&mut self, term: &WireExpr) -> Result<()> {
        for node in term.nodes() {
            self.tick()?;
            if let ExprNode::Free { name } = node
                && let Some(reserved) = self.reserved.as_mut()
            {
                reserved.insert(name.clone());
            }
        }
        Ok(())
    }
    /// Seed `self.reserved` lazily on the first fresh-local request, mirroring
    /// `InferenceEngine::initialize_reserved_names`. Proof-conversion calls
    /// that discharge by congruence, proof irrelevance, unit-like conversion,
    /// or WHNF without opening a binder or eta local never synthesize a fresh
    /// name and must not rescan large `let`-bound local bodies (`local.value()`)
    /// on every `compare_domain` deferral (`colimitLimitToLimitColimit_surjective`).
    fn ensure_reserved(&mut self) -> Result<()> {
        if self.reserved.is_some() {
            return Ok(());
        }
        self.reserved = Some(BTreeSet::new());
        self.reserve(self.root_left)?;
        self.reserve(self.root_right)?;
        for local in self.root_context.locals() {
            self.tick()?;
            if let Some(reserved) = self.reserved.as_mut() {
                reserved.insert(local.name().clone());
            }
            self.reserve(local.type_())?;
            if let Some(value) = local.value() {
                self.reserve(value)?;
            }
        }
        for (nested_left, nested_right) in std::mem::take(&mut self.unreserved_nested) {
            self.reserve(&nested_left)?;
            self.reserve(&nested_right)?;
        }
        Ok(())
    }
    fn local(&mut self) -> Result<(WireName, WireExpr)> {
        self.ensure_reserved()?;
        loop {
            self.tick()?;
            let name = WireName::from_parts(vec![
                NamePart::Text("_fln_proof_conversion".into()),
                NamePart::Numeric {
                    value: self.next,
                    overflowed: false,
                },
            ]);
            self.next = self
                .next
                .checked_add(1)
                .ok_or_else(|| self.fault(InferenceFault::FreshLocalIdentityExhausted))?;
            if self
                .reserved
                .as_mut()
                .is_some_and(|reserved| reserved.insert(name.clone()))
            {
                let local = self.free_local(&name)?;
                return Ok((name, local));
            }
        }
    }
    fn free_local(&self, name: &WireName) -> Result<WireExpr> {
        let root = ExprId::from_index(0)
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        Ok(WireExpr::from_parts(
            vec![ExprNode::Free { name: name.clone() }],
            vec![],
            root,
        ))
    }
    /// The local to open the binder or eta task `(kind, left, right)` at, and
    /// `context` extended by it as an assumption of type `domain`: the local the
    /// task opened before, unless `context` holds it (see `OpenedLocals`), else
    /// a fresh one.
    fn open_local(
        &mut self,
        kind: Taken,
        left: &WireExpr,
        right: &WireExpr,
        domain: WireExpr,
        context: &InferenceContext,
    ) -> Result<(WireName, WireExpr, InferenceContext)> {
        let fingerprint = PairSet::fingerprint(left, right);
        let (name, local) = match self.opened.get(fingerprint, kind, left, right) {
            Some(name) if context.local(name).is_none() => {
                let name = name.clone();
                self.tick()?;
                let local = self.free_local(&name)?;
                (name, local)
            }
            _ => {
                let (name, local) = self.local()?;
                self.opened
                    .insert(fingerprint, kind, left, right, name.clone());
                (name, local)
            }
        };
        let context = context
            .push_assumption(name.clone(), domain)
            .map_err(|_| self.fault(InferenceFault::ScopedLocalCollision { name: name.clone() }))?;
        Ok((name, local, context))
    }
    fn infer(&mut self, term: &WireExpr, context: &InferenceContext) -> Result<Option<WireExpr>> {
        let scoped = all_free_locals_in_context(term, context);
        let fingerprint = InferredTypes::fingerprint(term);
        if scoped && let Some(cached) = self.inferred.get(fingerprint, term) {
            self.tick()?;
            return Ok(cached);
        }
        let budget = self.budget;
        let mode = InferenceMode::InferOnly;
        let result =
            infer_without_proof_conversion(term, context, mode, budget, &mut || self.poll());
        self.check_stop()?;
        let answer = match result {
            InferenceOutcome::Complete(result) => Some(result.type_),
            InferenceOutcome::Refused { .. } | InferenceOutcome::Deferred { .. } => None,
            halt => return Err(Box::new(halt)),
        };
        if scoped {
            self.inferred.insert(fingerprint, term, answer.clone());
        }
        Ok(answer)
    }
    fn whnf(&mut self, term: &WireExpr, context: &InferenceContext) -> Result<Option<WireExpr>> {
        let budget = self.budget.whnf;
        let result = whnf_with(term, context.reduction(), budget, &mut || self.poll());
        self.whnf_result(result)
    }
    /// Core normalization (`DeltaMode::Disabled`, `ClosedPair`) for comparands
    /// in typed lazy delta. Returns `Ok(Some(None))` when already in `whnf_core`
    /// (zero allocation), `Ok(Some(Some(term)))` when reduced, and `Ok(None)`
    /// when WHNF refused the term.
    fn whnf_comparand_core(
        &mut self,
        term: &Term,
        context: &InferenceContext,
    ) -> Result<Option<Option<Term>>> {
        let budget = self.budget.whnf;
        let result = crate::whnf::whnf_comparand_core_of_with(
            term.as_whnf_input(),
            term.root(),
            context.reduction(),
            budget,
            &mut || self.poll(),
        );
        self.check_stop()?;
        match result {
            crate::whnf::WhnfCoreOutcome::Unchanged { .. } => Ok(Some(None)),
            crate::whnf::WhnfCoreOutcome::Complete { result, copied } => {
                Ok(Some(Some(Term::from_whnf(result.term, copied))))
            }
            crate::whnf::WhnfCoreOutcome::Refused(_) => Ok(None),
            crate::whnf::WhnfCoreOutcome::Inconclusive(stop) => Err(Box::new(
                InferenceOutcome::Inconclusive(InferenceStop::Whnf {
                    argument: 0,
                    stop: Box::new(stop),
                    progress: self.progress(),
                }),
            )),
            crate::whnf::WhnfCoreOutcome::InternalFault(fault) => {
                Err(self.fault(InferenceFault::Whnf { argument: 0, fault }))
            }
        }
    }
    /// One lazy delta step (`DeltaMode::Once`, `ClosedPair`) for comparands in
    /// typed conversion, matching the pin's `lazy_delta_reduction_step` and
    /// preserving `WhnfInput::Copied` so consecutive steps skip input recopying.
    fn whnf_comparand_delta_step(
        &mut self,
        term: &Term,
        context: &InferenceContext,
    ) -> Result<Option<Term>> {
        let budget = self.budget.whnf;
        let (result, copied) = crate::whnf::whnf_comparand_delta_step_of_with(
            term.as_whnf_input(),
            term.root(),
            context.reduction(),
            budget,
            &mut || self.poll(),
        );
        Ok(self
            .whnf_result(result)?
            .map(|reduced| Term::from_whnf(reduced, copied)))
    }
    /// Reducibility priority of `term`'s spine head (stepping through
    /// applications, metadata, and projections), and whether a projection was
    /// crossed (matching `defeq::definition_height_through` and the pin's
    /// `try_unfold_proj_app`).
    fn definition_height_through(
        &mut self,
        term: &WireExpr,
        context: &InferenceContext,
    ) -> Result<(Option<(u8, u32)>, bool)> {
        let reduction = context.reduction();
        let mut id = term.root();
        let mut through_projection = false;
        loop {
            self.tick()?;
            match term.node(id) {
                Some(ExprNode::Apply { function, .. }) => id = *function,
                Some(ExprNode::Metadata { expression, .. }) => id = *expression,
                Some(ExprNode::Projection { expression, .. }) => {
                    through_projection = true;
                    id = *expression;
                }
                Some(ExprNode::Constant { name, .. }) => {
                    let height = reduction
                        .constants()
                        .find(name)
                        .and_then(|constant| reduction.delta_body(constant))
                        .map(|definition| definition.hint().delta_priority());
                    return Ok((height, through_projection));
                }
                _ => return Ok((None, through_projection)),
            }
        }
    }
    fn whnf_result(&mut self, result: WhnfOutcome) -> Result<Option<WireExpr>> {
        self.check_stop()?;
        match result {
            WhnfOutcome::Complete(result) => Ok(Some(result.term)),
            WhnfOutcome::Refused(_) => Ok(None),
            WhnfOutcome::Inconclusive(stop) => Err(Box::new(InferenceOutcome::Inconclusive(
                InferenceStop::Whnf {
                    argument: 0,
                    stop: Box::new(stop),
                    progress: self.progress(),
                },
            ))),
            WhnfOutcome::InternalFault(fault) => {
                Err(self.fault(InferenceFault::Whnf { argument: 0, fault }))
            }
        }
    }
    fn equal(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
        context: &InferenceContext,
        record_cache: bool,
    ) -> Result<Option<bool>> {
        let fingerprint = if record_cache {
            let fp = PairSet::fingerprint(left, right);
            if let Some(answer) = self.answers.get(fp, left, right) {
                return Ok(answer);
            }
            Some(fp)
        } else {
            None
        };
        let answer = if has_nat_or_string_head(left) || has_nat_or_string_head(right) {
            let budget = self.budget.defeq;
            let result =
                def_eq_before_typed_with(left, right, context.reduction(), budget, &mut || {
                    self.poll()
                });
            self.check_stop()?;
            match result {
                DefEqOutcome::Equal(_) => Some(true),
                DefEqOutcome::NotEqual { .. } | DefEqOutcome::Refused { .. } => Some(false),
                DefEqOutcome::Deferred { .. } => None,
                DefEqOutcome::Inconclusive(stop) => {
                    return Err(Box::new(InferenceOutcome::Inconclusive(
                        InferenceStop::DefEq {
                            argument: 0,
                            stop: Box::new(stop),
                            progress: self.progress(),
                        },
                    )));
                }
                DefEqOutcome::InternalFault(fault) => {
                    return Err(self.fault(InferenceFault::DefEq { argument: 0, fault }));
                }
            }
        } else {
            // `Probe::run` owns typed lazy delta, congruence, eta, and K-reduction.
            // Running untyped `run_slow` at every intermediate lazy-delta step
            // would re-walk the remaining delta chain O(N^2) times without proof
            // irrelevance. Use quick alpha/metadata/universe equality only; a
            // literal/sort mismatch is final only at the undecomposed root pair.
            let result =
                crate::defeq::quick_def_eq_with(left, right, self.budget.defeq.quick, &mut || {
                    self.poll()
                });
            self.check_stop()?;
            match result {
                crate::defeq::QuickDefEqOutcome::Equal(_) => Some(true),
                crate::defeq::QuickDefEqOutcome::NotEqual { mismatch, .. } => {
                    let (ml, mr) = match mismatch {
                        crate::defeq::QuickDefEqMismatch::SortLevels { left, right }
                        | crate::defeq::QuickDefEqMismatch::NatLiterals { left, right }
                        | crate::defeq::QuickDefEqMismatch::StringLiterals { left, right } => {
                            (left, right)
                        }
                    };
                    if ml == left.root().index() && mr == right.root().index() {
                        Some(false)
                    } else {
                        None
                    }
                }
                crate::defeq::QuickDefEqOutcome::Deferred { .. } => None,
                crate::defeq::QuickDefEqOutcome::Inconclusive(stop) => {
                    return Err(Box::new(InferenceOutcome::Inconclusive(
                        InferenceStop::DefEq {
                            argument: 0,
                            stop: Box::new(DefEqStop::Quick(stop)),
                            progress: self.progress(),
                        },
                    )));
                }
                crate::defeq::QuickDefEqOutcome::InternalFault(fault) => {
                    return Err(self.fault(InferenceFault::DefEq {
                        argument: 0,
                        fault: crate::defeq::DefEqFault::Quick(fault),
                    }));
                }
            }
        };
        if let Some(fingerprint) = fingerprint {
            self.answers.insert(fingerprint, left, right, answer);
        }
        Ok(answer)
    }
    /// The argument pairs of two applications of one head: the same local, or
    /// the same constant at equal universe levels, applied to equally many
    /// arguments.
    fn same_head_arguments(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
    ) -> Result<Option<Vec<(ExprId, ExprId)>>> {
        let spine = |term: &WireExpr| {
            let mut arguments = Vec::new();
            let mut id = term.root();
            while let Some(ExprNode::Apply { function, argument }) = term.node(id) {
                arguments.push(*argument);
                id = *function;
            }
            arguments.reverse();
            (id, arguments)
        };
        let (left_head, left_arguments) = spine(left);
        let (right_head, right_arguments) = spine(right);
        if left_arguments.len() != right_arguments.len() {
            return Ok(None);
        }
        self.tick()?;
        if let (
            Some(ExprNode::Projection {
                structure_name: left_structure,
                index: left_index,
                expression: left_expr,
            }),
            Some(ExprNode::Projection {
                structure_name: right_structure,
                index: right_index,
                expression: right_expr,
            }),
        ) = (left.node(left_head), right.node(right_head))
            && left_structure == right_structure
            && left_index == right_index
        {
            let mut pairs = Vec::with_capacity(1 + left_arguments.len());
            pairs.push((*left_expr, *right_expr));
            pairs.extend(left_arguments.into_iter().zip(right_arguments));
            return Ok(Some(pairs));
        }
        if left_arguments.is_empty() {
            return Ok(None);
        }
        let same_head = match (left.node(left_head), right.node(right_head)) {
            (
                Some(ExprNode::Constant {
                    name: left_name,
                    levels: left_levels,
                }),
                Some(ExprNode::Constant {
                    name: right_name,
                    levels: right_levels,
                }),
            ) => {
                left_name == right_name
                    && left_levels.len() == right_levels.len()
                    && left_levels.iter().zip(right_levels).all(|(l, r)| {
                        level_roots_equal(left.levels(), *l, right.levels(), *r).unwrap_or(false)
                    })
            }
            (Some(ExprNode::Free { name: l }), Some(ExprNode::Free { name: r })) => l == r,
            _ => false,
        };
        Ok(same_head.then(|| left_arguments.into_iter().zip(right_arguments).collect()))
    }
    fn proof_status(&mut self, term: &WireExpr, context: &InferenceContext) -> Result<ProofStatus> {
        // A type constructor cannot itself be a proof. Avoid expensive failed
        // queries while descending the declaration's outer function telescope.
        if matches!(
            term.node(term.root()),
            Some(ExprNode::Sort { .. } | ExprNode::Forall { .. })
        ) {
            return Ok(ProofStatus::NotProof);
        }
        let Some(type_) = self.infer(term, context)? else {
            return Ok(ProofStatus::Unknown);
        };
        let Some(sort) = self.infer(&type_, context)? else {
            return Ok(ProofStatus::Unknown);
        };
        let Some(sort) = self.whnf(&sort, context)? else {
            return Ok(ProofStatus::Unknown);
        };
        let Some(ExprNode::Sort { level }) = sort.node(sort.root()) else {
            return Ok(ProofStatus::Unknown);
        };
        self.tick()?;
        match normalize(&WireLevel::from_parts(sort.levels().to_vec(), *level)) {
            Ok(n) if matches!(n.nodes().get(n.root().index()), Some(NormalNode::Zero)) => {
                Ok(ProofStatus::Proof(type_))
            }
            Ok(_) => Ok(ProofStatus::NotProof),
            Err(_) => Ok(ProofStatus::Unknown),
        }
    }
    /// Try KR-311 proof irrelevance (`type_checker.cpp:1117`). When either side
    /// is definitively non-`Prop` (`ProofStatus::NotProof`), clear
    /// `*check_proof`: by subject reduction, subsequent core/K/delta steps on
    /// this pair cannot turn a non-proof into a proof.
    fn try_proof_irrelevance(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
        context: &InferenceContext,
        check_proof: &mut bool,
    ) -> Result<Option<(WireExpr, WireExpr)>> {
        if !*check_proof {
            return Ok(None);
        }
        match self.proof_status(left, context)? {
            ProofStatus::Proof(lt) => match self.proof_status(right, context)? {
                ProofStatus::Proof(rt) => Ok(Some((lt, rt))),
                ProofStatus::NotProof => {
                    *check_proof = false;
                    Ok(None)
                }
                ProofStatus::Unknown => Ok(None),
            },
            ProofStatus::NotProof => {
                *check_proof = false;
                Ok(None)
            }
            ProofStatus::Unknown => Ok(None),
        }
    }
    /// KR-315, the pin's `is_def_eq_unit_like` (type_checker.cpp:1073): when
    /// `left`'s type normalizes to a non-recursive, index-free, one-constructor
    /// inductive whose constructor has no fields, the two sides are convertible
    /// exactly when their types are. Like the pin, only `left`'s type is
    /// examined. `None` means the rule does not apply.
    fn unit_like_obligation(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
        context: &InferenceContext,
    ) -> Result<Option<(WireExpr, WireExpr)>> {
        if matches!(
            left.node(left.root()),
            Some(ExprNode::Sort { .. } | ExprNode::Forall { .. })
        ) {
            return Ok(None);
        }
        let Some(left_type) = self.infer(left, context)? else {
            return Ok(None);
        };
        let Some(left_type) = self.whnf(&left_type, context)? else {
            return Ok(None);
        };
        let Some(head) = head_constant(&left_type) else {
            return Ok(None);
        };
        let constants = context.constants();
        let Some(inductive) = constants.find(head).and_then(|d| d.inductive_metadata()) else {
            return Ok(None);
        };
        let [constructor] = inductive.constructors() else {
            return Ok(None);
        };
        if inductive.num_indices() != 0 || inductive.is_recursive() {
            return Ok(None);
        }
        let Some(fields) = constants
            .find(constructor)
            .and_then(|d| d.constructor_metadata())
            .map(|c| c.num_fields())
        else {
            return Ok(None);
        };
        if fields != 0 {
            return Ok(None);
        }
        let Some(right_type) = self.infer(right, context)? else {
            return Ok(None);
        };
        Ok(Some((left_type, right_type)))
    }
    /// KR-312 structure eta, the pin's `try_eta_struct_core`
    /// (type_checker.cpp:812): when `s` is a full application of the only
    /// constructor of a non-recursive, index-free inductive and `t`'s head is
    /// not that constructor, `s ≟ t` holds exactly when their types do and
    /// every field argument of `s` converts with the matching projection of
    /// `t`. Returns those obligations as (from `s`, from `t`) pairs, types
    /// first; `None` means the rule does not apply.
    fn structure_eta(
        &mut self,
        s: &WireExpr,
        t: &WireExpr,
        context: &InferenceContext,
    ) -> Result<Option<Vec<(WireExpr, WireExpr)>>> {
        let Some(head) = head_constant(s) else {
            return Ok(None);
        };
        if head_constant(t) == Some(head) {
            return Ok(None);
        }
        let constants = context.constants();
        let Some(constructor) = constants.find(head).and_then(|d| d.constructor_metadata()) else {
            return Ok(None);
        };
        let (inductive_name, parameters, fields) = (
            constructor.inductive().clone(),
            constructor.num_parameters() as usize,
            constructor.num_fields() as usize,
        );
        let Some(inductive) = constants
            .find(&inductive_name)
            .and_then(|d| d.inductive_metadata())
        else {
            return Ok(None);
        };
        if inductive.constructors().len() != 1
            || inductive.num_indices() != 0
            || inductive.is_recursive()
        {
            return Ok(None);
        }
        let mut arguments = Vec::new();
        let mut id = s.root();
        while let Some(ExprNode::Apply { function, argument }) = s.node(id) {
            self.tick()?;
            arguments.push(*argument);
            id = *function;
        }
        arguments.reverse();
        if arguments.len() != parameters + fields {
            return Ok(None);
        }
        let Some(s_type) = self.infer(s, context)? else {
            return Ok(None);
        };
        let Some(t_type) = self.infer(t, context)? else {
            return Ok(None);
        };
        let mut obligations = vec![(s_type, t_type)];
        for (field, argument) in arguments[parameters..].iter().enumerate() {
            let argument = self.piece(s, *argument)?;
            let projection = self.project(t, &inductive_name, field as u64)?;
            obligations.push((argument, projection));
        }
        Ok(Some(obligations))
    }
    /// KR-317 in the typed lane, the pin's `to_cnstr_when_K` (inductive.h:31):
    /// a K recursor application `s` stuck on a major premise that is not a
    /// constructor application reduces as if that major were the inductive's
    /// nullary constructor, applied to the parameters of the major's type,
    /// whenever the major's type is definitionally equal to that constructor's.
    /// whnf applies the rule too, but gates it on a structural comparison with
    /// no typing, so it misses a type pair that only eta or proof irrelevance
    /// closes (`Fin.addCases_left`: `castLT (castAdd n i) h ≟ i`). Returns the
    /// (major type, constructor type) pair, which the caller must prove before
    /// using the rule, and `s` with the major replaced, which whnf's iota then
    /// reduces; `None` means the rule does not apply.
    fn k_reduction(
        &mut self,
        s: &WireExpr,
        context: &InferenceContext,
    ) -> Result<Option<((WireExpr, WireExpr), WireExpr)>> {
        let Some(head) = head_constant(s) else {
            return Ok(None);
        };
        let constants = context.constants();
        let Some(recursor) = constants.find(head).and_then(|d| d.recursor_metadata()) else {
            return Ok(None);
        };
        if !recursor.k() {
            return Ok(None);
        }
        let major_index = [
            recursor.num_parameters(),
            recursor.num_motives(),
            recursor.num_minors(),
            recursor.num_indices(),
        ]
        .into_iter()
        .map(|count| count as usize)
        .sum::<usize>();
        // The spine as (application node, argument), innermost first.
        let mut spine = Vec::new();
        let mut id = s.root();
        while let Some(ExprNode::Apply { function, argument }) = s.node(id) {
            self.tick()?;
            spine.push((id, *argument));
            id = *function;
        }
        spine.reverse();
        let Some(&(major_application, major_id)) = spine.get(major_index) else {
            return Ok(None);
        };
        let Some(ExprNode::Apply {
            function: before_major,
            ..
        }) = s.node(major_application)
        else {
            return Ok(None);
        };
        let before_major = *before_major;
        let major = self.piece(s, major_id)?;
        let Some(reduced_major) = self.whnf(&major, context)? else {
            return Ok(None);
        };
        if head_constant(&reduced_major)
            .and_then(|name| constants.find(name))
            .is_some_and(|declaration| declaration.constructor_metadata().is_some())
        {
            return Ok(None);
        }
        let Some(major_type) = self.infer(&major, context)? else {
            return Ok(None);
        };
        let Some(major_type) = self.whnf(&major_type, context)? else {
            return Ok(None);
        };
        // The major's type must be an application of the recursor's inductive.
        let mut type_arguments = Vec::new();
        let mut type_head = major_type.root();
        while let Some(ExprNode::Apply { function, argument }) = major_type.node(type_head) {
            self.tick()?;
            type_arguments.push(*argument);
            type_head = *function;
        }
        type_arguments.reverse();
        let Some(ExprNode::Constant {
            name: inductive_name,
            levels: inductive_levels,
        }) = major_type.node(type_head)
        else {
            return Ok(None);
        };
        if !recursor.mutual().contains(inductive_name) {
            return Ok(None);
        }
        let Some(inductive) = constants
            .find(inductive_name)
            .and_then(|d| d.inductive_metadata())
        else {
            return Ok(None);
        };
        let [constructor_name] = inductive.constructors() else {
            return Ok(None);
        };
        let parameters = inductive.num_parameters() as usize;
        if type_arguments.len() < parameters
            || constants
                .find(constructor_name)
                .and_then(|d| d.constructor_metadata())
                .is_none_or(|c| c.num_fields() != 0)
        {
            return Ok(None);
        }
        // The constructor applied to the major type's parameters, built by
        // extending a copy of the type's own arena.
        let mut nodes = major_type.nodes().to_vec();
        let mut constructor = push_node(
            &mut nodes,
            ExprNode::Constant {
                name: constructor_name.clone(),
                levels: inductive_levels.clone(),
            },
        )
        .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        for argument in &type_arguments[..parameters] {
            self.tick()?;
            constructor = push_node(
                &mut nodes,
                ExprNode::Apply {
                    function: constructor,
                    argument: *argument,
                },
            )
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        }
        let constructor = WireExpr::from_parts(nodes, major_type.levels().to_vec(), constructor);
        let Some(constructor_type) = self.infer(&constructor, context)? else {
            return Ok(None);
        };
        // `s` with the major replaced, built by extending a copy of `s`'s arena.
        let mut nodes = s.nodes().to_vec();
        let mut levels = s.levels().to_vec();
        let replacement = append_arena(&mut nodes, &mut levels, &constructor)
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        let mut root = push_node(
            &mut nodes,
            ExprNode::Apply {
                function: before_major,
                argument: replacement,
            },
        )
        .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        for &(_, argument) in &spine[major_index + 1..] {
            self.tick()?;
            root = push_node(
                &mut nodes,
                ExprNode::Apply {
                    function: root,
                    argument,
                },
            )
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        }
        Ok(Some((
            (major_type, constructor_type),
            WireExpr::from_parts(nodes, levels, root),
        )))
    }
    /// KR-317 below the head. The pin's `whnf` normalizes a recursor's major with
    /// K conversion available (`inductive_reduce_rec` whnfs the major, and the
    /// recursor steps inside that whnf call `to_cnstr_when_K`), so a K recursor
    /// stuck inside another recursor's major still reduces. Untyped reduction
    /// has no types for the K gate, and `k_reduction` examines only the head:
    /// `decide` on a `Rat` equality stuck as `Decidable.rec … (Eq.rec … h)`
    /// was deferred. A projection is reduced the same way: the pin's
    /// `whnf_core` reduces a projection's structure before projecting, with K
    /// available to the recursor steps there. Structure eta splits a
    /// constructor against a stuck cast into its fields against projections
    /// of the cast, `(Eq.rec … h).1`, which `k_reduction` alone cannot see
    /// (fln-4o0g: `CategoryTheory.Cat.bicategory.strict`). Follow the chain of
    /// stuck majors and projected structures down to the first K recursor
    /// `k_reduction` accepts, and rebuild the chain around it. The gate is the
    /// caller's, exactly as for `k_reduction`.
    fn nested_k_reduction(
        &mut self,
        s: &WireExpr,
        context: &InferenceContext,
        reach: Reach,
    ) -> Result<Option<((WireExpr, WireExpr), WireExpr)>> {
        let mut chain: Vec<(WireExpr, Descent)> = Vec::new();
        let mut current = s.clone();
        for _ in 0..MAX_NESTED_K_DEPTH {
            let (descent, inner) =
                if let Some((index, major)) = self.recursor_major(&current, context)? {
                    (Descent::Major(index), major)
                } else if reach == Reach::MajorsAndProjections
                    && let Some(structure) = self.projected_structure(&current)?
                {
                    (Descent::Projection, structure)
                } else {
                    return Ok(None);
                };
            let inner = self.piece(&current, inner)?;
            let Some(inner) = self.whnf(&inner, context)? else {
                return Ok(None);
            };
            chain.push((current, descent));
            if let Some((gate, reduced)) = self.k_reduction(&inner, context)? {
                let mut rebuilt = reduced;
                for (term, descent) in chain.into_iter().rev() {
                    rebuilt = match descent {
                        Descent::Major(index) => self.with_argument(&term, index, &rebuilt)?,
                        Descent::Projection => self.with_projected_structure(&term, &rebuilt)?,
                    };
                }
                return Ok(Some((gate, rebuilt)));
            }
            current = inner;
        }
        Ok(None)
    }
    /// Whether the chain below `s` reaches a K-like recursor at a spine head:
    /// through the structure of a projection head and the major of a recursor
    /// head, read in place, with no whnf and no copy. The comparands reaching
    /// the KR-317 rules are already in whnf, so a stuck cast is already at the
    /// head of its projection's structure; a chain that does not end at one
    /// cannot fire, and skipping it spares the projected structure's whnf
    /// (BVDecide's `Udiv` lemmas paid 8.7% for it without this check).
    fn reaches_k_recursor(&mut self, s: &WireExpr, context: &InferenceContext) -> Result<bool> {
        let constants = context.constants();
        let mut id = s.root();
        for _ in 0..MAX_NESTED_K_DEPTH {
            let mut arguments = Vec::new();
            let mut head = id;
            while let Some(ExprNode::Apply { function, argument }) = s.node(head) {
                self.tick()?;
                arguments.push(*argument);
                head = *function;
            }
            arguments.reverse();
            match s.node(head) {
                Some(ExprNode::Projection { expression, .. }) => id = *expression,
                Some(ExprNode::Constant { name, .. }) => {
                    let Some(recursor) = constants.find(name).and_then(|d| d.recursor_metadata())
                    else {
                        return Ok(false);
                    };
                    if recursor.k() {
                        return Ok(true);
                    }
                    let major = [
                        recursor.num_parameters(),
                        recursor.num_motives(),
                        recursor.num_minors(),
                        recursor.num_indices(),
                    ]
                    .into_iter()
                    .map(|count| count as usize)
                    .sum::<usize>();
                    let Some(&next) = arguments.get(major) else {
                        return Ok(false);
                    };
                    id = next;
                }
                _ => return Ok(false),
            }
        }
        Ok(false)
    }
    /// The structure of the projection at the head of `s`'s spine, when that
    /// head is a projection.
    fn projected_structure(&mut self, s: &WireExpr) -> Result<Option<ExprId>> {
        let mut id = s.root();
        while let Some(ExprNode::Apply { function, .. }) = s.node(id) {
            self.tick()?;
            id = *function;
        }
        Ok(match s.node(id) {
            Some(ExprNode::Projection { expression, .. }) => Some(*expression),
            _ => None,
        })
    }
    /// `s` with the structure of the projection at the head of its spine
    /// replaced by `replacement`, built by extending a copy of `s`'s arena.
    fn with_projected_structure(
        &mut self,
        s: &WireExpr,
        replacement: &WireExpr,
    ) -> Result<WireExpr> {
        let mut arguments = Vec::new();
        let mut id = s.root();
        while let Some(ExprNode::Apply { function, argument }) = s.node(id) {
            self.tick()?;
            arguments.push(*argument);
            id = *function;
        }
        let Some(ExprNode::Projection {
            structure_name,
            index,
            ..
        }) = s.node(id)
        else {
            return Err(self.fault(InferenceFault::LiteralTypeAllocation));
        };
        let (structure_name, index) = (structure_name.clone(), *index);
        let mut nodes = s.nodes().to_vec();
        let mut levels = s.levels().to_vec();
        let replacement = append_arena(&mut nodes, &mut levels, replacement)
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        let mut root = push_node(
            &mut nodes,
            ExprNode::Projection {
                structure_name,
                index,
                expression: replacement,
            },
        )
        .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        for &argument in arguments.iter().rev() {
            self.tick()?;
            root = push_node(
                &mut nodes,
                ExprNode::Apply {
                    function: root,
                    argument,
                },
            )
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        }
        Ok(WireExpr::from_parts(nodes, levels, root))
    }
    /// The position and node of `s`'s major premise, when `s`'s head is a
    /// recursor applied far enough to have one.
    fn recursor_major(
        &mut self,
        s: &WireExpr,
        context: &InferenceContext,
    ) -> Result<Option<(usize, ExprId)>> {
        let Some(head) = head_constant(s) else {
            return Ok(None);
        };
        let Some(recursor) = context
            .constants()
            .find(head)
            .and_then(|d| d.recursor_metadata())
        else {
            return Ok(None);
        };
        let index = [
            recursor.num_parameters(),
            recursor.num_motives(),
            recursor.num_minors(),
            recursor.num_indices(),
        ]
        .into_iter()
        .map(|count| count as usize)
        .sum::<usize>();
        let mut arguments = Vec::new();
        let mut id = s.root();
        while let Some(ExprNode::Apply { function, argument }) = s.node(id) {
            self.tick()?;
            arguments.push(*argument);
            id = *function;
        }
        arguments.reverse();
        Ok(arguments.get(index).map(|&major| (index, major)))
    }
    /// `s` with its argument at `index` replaced, built by extending a copy of
    /// `s`'s arena.
    fn with_argument(
        &mut self,
        s: &WireExpr,
        index: usize,
        replacement: &WireExpr,
    ) -> Result<WireExpr> {
        let mut spine = Vec::new();
        let mut id = s.root();
        while let Some(ExprNode::Apply { function, argument }) = s.node(id) {
            self.tick()?;
            spine.push((*function, *argument));
            id = *function;
        }
        spine.reverse();
        let Some(&(before, _)) = spine.get(index) else {
            return Err(self.fault(InferenceFault::LiteralTypeAllocation));
        };
        let mut nodes = s.nodes().to_vec();
        let mut levels = s.levels().to_vec();
        let replacement = append_arena(&mut nodes, &mut levels, replacement)
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        let mut root = push_node(
            &mut nodes,
            ExprNode::Apply {
                function: before,
                argument: replacement,
            },
        )
        .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        for &(_, argument) in &spine[index + 1..] {
            self.tick()?;
            root = push_node(
                &mut nodes,
                ExprNode::Apply {
                    function: root,
                    argument,
                },
            )
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        }
        Ok(WireExpr::from_parts(nodes, levels, root))
    }
    /// `term.index` of structure `name`, built by extending a copy of `term`'s
    /// own arena, so no subterm is re-copied.
    fn project(&mut self, term: &WireExpr, name: &WireName, index: u64) -> Result<WireExpr> {
        self.tick()?;
        let mut nodes = term.nodes().to_vec();
        let root = ExprId::from_index(nodes.len())
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        nodes.push(ExprNode::Projection {
            structure_name: name.clone(),
            index,
            expression: term.root(),
        });
        Ok(WireExpr::from_parts(nodes, term.levels().to_vec(), root))
    }
    /// The domain of `term`'s type when that type normalizes to a Π, which is
    /// what eta expansion through the type needs. `None` means it does not.
    fn pi_domain(
        &mut self,
        term: &WireExpr,
        context: &InferenceContext,
    ) -> Result<Option<WireExpr>> {
        let Some(type_) = self.infer(term, context)? else {
            return Ok(None);
        };
        let Some(type_) = self.whnf(&type_, context)? else {
            return Ok(None);
        };
        let Some(ExprNode::Forall { binder_type, .. }) = type_.node(type_.root()) else {
            return Ok(None);
        };
        let binder_type = *binder_type;
        Ok(Some(self.piece(&type_, binder_type)?))
    }
    /// `term x` for the fresh local `x`, built by extending a copy of `term`'s
    /// own arena, so no subterm is re-copied.
    fn apply_to_free(&mut self, term: &WireExpr, name: WireName) -> Result<WireExpr> {
        self.tick()?;
        let mut nodes = term.nodes().to_vec();
        let local = ExprId::from_index(nodes.len())
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        nodes.push(ExprNode::Free { name });
        let root = ExprId::from_index(nodes.len())
            .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
        nodes.push(ExprNode::Apply {
            function: term.root(),
            argument: local,
        });
        Ok(WireExpr::from_parts(nodes, term.levels().to_vec(), root))
    }
    /// `root_deferred`: untyped conversion has just deferred this exact root
    /// pair, so asking it again would repeat that whole search for the same
    /// answer. Only the root is skipped; every derived pair is asked as usual.
    fn run(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
        context: &InferenceContext,
        root_deferred: bool,
    ) -> Result<bool> {
        #[derive(Clone, Copy)]
        struct PairState {
            /// True until either side is inferred to have a non-Prop type.
            check_proof: bool,
            /// True for logical subgoals (`Work::Pair`), false for intermediate
            /// core/K/delta steps inside one pair's lazy-delta chain (matching
            /// `type_checker.cpp:1117-1157`: intermediate delta states do not
            /// populate `taken`, `proven`/`disproven`, or `PairAnswers`).
            record_pair: bool,
        }
        impl PairState {
            const FRESH: Self = Self {
                check_proof: true,
                record_pair: true,
            };
            const fn after_step(self) -> Self {
                Self {
                    check_proof: self.check_proof,
                    record_pair: false,
                }
            }
        }
        enum Work {
            Pair(Term, Term, InferenceContext),
            /// Intermediate core, K-reduction, or single-step lazy-delta state
            /// of an already-entered pair.
            DeltaStep(Term, Term, InferenceContext, PairState),
            /// A pair whose congruence attempt failed, taking the other rules;
            /// the flag is the root's `root_deferred`.
            Rules(Term, Term, InferenceContext, bool, PairState),
            /// Marker sitting below a pair's sub-obligations (and below any
            /// `Work::Attempt` for that pair): reaching it records the pair in
            /// `self.proven` if no unproven `taken` skip occurred beneath it;
            /// unwinding past it on `fail!()` records it in `self.disproven`.
            Established(Arc<WireExpr>, Arc<WireExpr>, u64),
            /// Every task above this one is an argument obligation of a
            /// congruence attempt on the pair, so reaching it means they all
            /// held. `trail` is the length of the taken-trail at the attempt.
            Attempt {
                left: Term,
                right: Term,
                context: InferenceContext,
                skip_untyped: bool,
                state: PairState,
                trail: usize,
            },
            Binders(Term, Term, ExprId, ExprId, WireExpr, InferenceContext),
            /// KR-312: open `lambda`'s body at a fresh local `x : domain` and
            /// compare it with `other x`, keeping the original sides.
            Eta {
                lambda: Term,
                body: ExprId,
                other: Term,
                domain: WireExpr,
                lambda_on_left: bool,
                context: InferenceContext,
            },
        }
        if !root_deferred {
            if self.reserved.is_some() {
                self.reserve(left)?;
                self.reserve(right)?;
            } else {
                self.unreserved_nested.push((left.clone(), right.clone()));
            }
        }
        let mut work = vec![Work::Pair(
            Term::new(left.clone()),
            Term::new(right.clone()),
            context.clone(),
        )];
        let mut skip_untyped = root_deferred;
        // Every task is an obligation of one conjunction: the run succeeds only
        // if each holds, and returns false at the first that does not. A task
        // already taken on therefore never needs taking on again, and the same
        // obligations recur heavily, reached from different decompositions. On
        // `Rat.ceil_add_intCast_le_ceil_add`, 1,242 distinct pairs were asked
        // 11,186 times. Local names are fresh and bound once, so a pair of
        // terms means the same thing in every context of one run. Binder and
        // eta tasks are keyed before they open a fresh local, since the pairs
        // they produce then differ in that local's name.
        let mut taken: crate::whnf::memo::FastHashSet<(Taken, Arc<WireExpr>, Arc<WireExpr>)> =
            crate::whnf::memo::FastHashSet::default();
        const MAX_TAKEN_NODES: usize = 1 << 21;
        let mut taken_nodes: usize = 0;
        let mut taken_skips: u64 = 0;
        // A congruence attempt only proposes obligations: when one fails, the
        // attempt is abandoned and the tasks it took on are not established.
        // `trail` records what was taken while an attempt is open, so that
        // abandoning it can give those tasks back.
        let mut trail: Vec<(Taken, Arc<WireExpr>, Arc<WireExpr>)> = Vec::new();
        let mut attempts = 0_usize;
        'work: while let Some(task) = work.pop() {
            // A task that does not hold fails the innermost open congruence
            // attempt, whose pair then takes the other rules; outside every
            // attempt it fails the run.
            macro_rules! fail {
                () => {{
                    let Some(marker) = work
                        .iter()
                        .rposition(|task| matches!(task, Work::Attempt { .. }))
                    else {
                        return Ok(false);
                    };
                    for abandoned in work.drain(marker + 1..) {
                        if let Work::Established(a, b, _) = abandoned {
                            self.disproven.insert(a, b);
                        }
                    }
                    if let Some(Work::Attempt {
                        left,
                        right,
                        context,
                        skip_untyped,
                        state,
                        trail: mark,
                    }) = work.pop()
                    {
                        attempts -= 1;
                        for entry in trail.drain(mark..) {
                            let entry_nodes =
                                entry.1.nodes().len().saturating_add(entry.2.nodes().len());
                            if taken.remove(&entry) {
                                taken_nodes = taken_nodes.saturating_sub(entry_nodes);
                            }
                        }
                        self.incongruent
                            .insert(Arc::clone(&left.expr), Arc::clone(&right.expr));
                        work.push(Work::Rules(left, right, context, skip_untyped, state));
                    }
                    continue 'work;
                }};
            }
            self.tick()?;
            if let Work::Pair(ref left, ref right, _) | Work::DeltaStep(ref left, ref right, ..) =
                task
            {
                if left.expr == right.expr || self.proven.contains(left, right) {
                    continue;
                }
                if self.disproven.contains(left, right) {
                    fail!();
                }
            }
            let key = match &task {
                Work::Pair(left, right, _) => Some((Taken::Pair, &left.expr, &right.expr)),
                Work::Binders(left, right, ..) => Some((Taken::Binders, &left.expr, &right.expr)),
                Work::Eta {
                    lambda,
                    other,
                    lambda_on_left,
                    ..
                } => Some((Taken::Eta(*lambda_on_left), &lambda.expr, &other.expr)),
                Work::DeltaStep(..)
                | Work::Rules(..)
                | Work::Attempt { .. }
                | Work::Established(..) => None,
            };
            if let Some((kind, a, b)) = key {
                let entry_nodes = a.nodes().len().saturating_add(b.nodes().len());
                let entry = (kind, Arc::clone(a), Arc::clone(b));
                if taken.contains(&entry) {
                    taken_skips = taken_skips.saturating_add(1);
                    continue;
                }
                if taken_nodes.saturating_add(entry_nodes) > MAX_TAKEN_NODES && attempts == 0 {
                    taken.clear();
                    taken_nodes = 0;
                }
                if taken_nodes.saturating_add(entry_nodes) <= MAX_TAKEN_NODES {
                    if attempts > 0 {
                        trail.push(entry.clone());
                    }
                    taken.insert(entry);
                    taken_nodes = taken_nodes.saturating_add(entry_nodes);
                }
            }
            let (left, right, context, try_congruence, skip, mut state) = match task {
                Work::Pair(left, right, context) => {
                    // Record an establishment marker BELOW any `Work::Attempt`
                    // or sub-obligations for this pair so proven sub-pairs
                    // survive sibling attempt rollbacks and fully failed pairs
                    // enter `self.disproven`.
                    work.push(Work::Established(
                        Arc::clone(&left.expr),
                        Arc::clone(&right.expr),
                        taken_skips,
                    ));
                    (
                        left,
                        right,
                        context,
                        true,
                        std::mem::take(&mut skip_untyped),
                        PairState::FRESH,
                    )
                }
                Work::DeltaStep(left, right, context, state) => {
                    (left, right, context, true, false, state)
                }
                Work::Rules(left, right, context, skip, state) => {
                    (left, right, context, false, skip, state)
                }
                Work::Established(a, b, start_skips) => {
                    if taken_skips == start_skips {
                        self.proven.insert(a, b);
                    }
                    continue;
                }
                Work::Attempt { .. } => {
                    attempts -= 1;
                    if attempts == 0 {
                        trail.clear();
                    }
                    continue;
                }
                Work::Binders(left, right, lb, rb, domain, context) => {
                    let (_, local, context) =
                        self.open_local(Taken::Binders, &left, &right, domain, &context)?;
                    let left = Term::new(self.open(&left, lb, &local)?);
                    let right = Term::new(self.open(&right, rb, &local)?);
                    work.push(Work::Pair(left, right, context));
                    continue;
                }
                Work::Eta {
                    lambda,
                    body,
                    other,
                    domain,
                    lambda_on_left,
                    context,
                } => {
                    let (name, local, context) = self.open_local(
                        Taken::Eta(lambda_on_left),
                        &lambda,
                        &other,
                        domain,
                        &context,
                    )?;
                    let opened = Term::new(self.open(&lambda, body, &local)?);
                    let applied = Term::new(self.apply_to_free(&other, name)?);
                    let (left, right) = if lambda_on_left {
                        (opened, applied)
                    } else {
                        (applied, opened)
                    };
                    work.push(Work::Pair(left, right, context));
                    continue;
                }
            };
            if left.expr == right.expr {
                continue;
            }
            // KR-301/KR-302: the pin's `quick_is_def_eq` sends matching
            // lambda/Pi heads directly to `is_def_eq_binding`, before lazy
            // delta. Open them in this typed worklist as well: an untyped
            // descent loses the local types needed to identify proof arguments
            // and can exhaust its budget unfolding their producers. The domain
            // obligation runs before the bodies are opened, and both remain
            // ordinary obligations of any enclosing congruence attempt.
            if let (
                Some(ExprNode::Lambda {
                    binder_type: lt,
                    body: lb,
                    ..
                }),
                Some(ExprNode::Lambda {
                    binder_type: rt,
                    body: rb,
                    ..
                }),
            )
            | (
                Some(ExprNode::Forall {
                    binder_type: lt,
                    body: lb,
                    ..
                }),
                Some(ExprNode::Forall {
                    binder_type: rt,
                    body: rb,
                    ..
                }),
            ) = (left.node(left.root()), right.node(right.root()))
            {
                let domain = self.piece(&left, *lt)?;
                let other = self.piece(&right, *rt)?;
                let (lb, rb) = (*lb, *rb);
                work.push(Work::Binders(
                    left,
                    right,
                    lb,
                    rb,
                    domain.clone(),
                    context.clone(),
                ));
                work.push(Work::Pair(Term::new(domain), Term::new(other), context));
                continue;
            }
            // If `left` is headed by a theorem constant, try proof irrelevance
            // before congruence so differing proof combinators (`Eq.trans`,
            // `congrArg`, etc.) equate their proposition types immediately
            // without comparing proof subterms.
            if state.check_proof
                && is_theorem_head(&left, &context)
                && let Some((lt, rt)) =
                    self.try_proof_irrelevance(&left, &right, &context, &mut state.check_proof)?
            {
                work.push(Work::Pair(Term::new(lt), Term::new(rt), context));
                continue;
            }
            // Congruence first, with each argument pair decided by this lane.
            // The pin tries congruence before unfolding two applications of one
            // regular definition (`lazy_delta_reduction_step`), comparing the
            // arguments with the full conversion. The untyped converter makes
            // that attempt without types, so it cannot equate proofs: a pair
            // differing only in a proof argument, such as
            // `parseFirstByte (b[0]'h₁)` against `parseFirstByte (b[0]'h₂)`,
            // unfolds on both sides until it defers, and cost
            // `utf8DecodeChar?_eq_assemble₄` its whole budget. Congruence is
            // sufficient, so a pair it cannot establish goes on to the rules
            // below unchanged.
            if try_congruence
                && let Some(arguments) = self.same_head_arguments(&left, &right)?
                && !self.incongruent.contains(&left, &right)
            {
                let mut obligations = Vec::with_capacity(arguments.len());
                for (left_argument, right_argument) in arguments {
                    obligations.push(Work::Pair(
                        Term::new(self.piece(&left, left_argument)?),
                        Term::new(self.piece(&right, right_argument)?),
                        context.clone(),
                    ));
                }
                work.push(Work::Attempt {
                    left,
                    right,
                    context,
                    skip_untyped: skip,
                    state,
                    trail: trail.len(),
                });
                attempts += 1;
                // Push in forward order so the LIFO stack compares trailing
                // arguments first (matching `type_checker.cpp:786` `is_def_eq_args`),
                // failing fast on differing value/index arguments before leading
                // typeclass instances.
                work.extend(obligations);
                continue;
            }
            // Both witnesses must independently type-check as proofs. The two
            // proposition types become a further conversion obligation; merely
            // inhabiting Prop never equates distinct propositions. This runs
            // once per logical pair before lazy delta, as the pin's
            // `is_def_eq_core` runs `is_def_eq_proof_irrel` before
            // `lazy_delta_reduction` (vendored type_checker.cpp:1117, 1121),
            // and is skipped on intermediate delta steps once either side is
            // known to have a non-Prop type.
            if let Some((lt, rt)) =
                self.try_proof_irrelevance(&left, &right, &context, &mut state.check_proof)?
            {
                work.push(Work::Pair(Term::new(lt), Term::new(rt), context));
                continue;
            }
            if !skip {
                match self.equal(&left, &right, &context, state.record_pair)? {
                    Some(true) => continue,
                    Some(false) => fail!(),
                    None => {}
                }
            }
            let Some(l_core) = self.whnf_comparand_core(&left, &context)? else {
                fail!()
            };
            let Some(r_core) = self.whnf_comparand_core(&right, &context)? else {
                fail!()
            };
            // Core beta/zeta/iota/projection reduction may expose matching
            // binders, matching heads for typed congruence, or proofs without
            // eagerly unfolding any regular definition.
            let l_changed = l_core
                .as_ref()
                .is_some_and(|reduced| reduced.expr != left.expr);
            let r_changed = r_core
                .as_ref()
                .is_some_and(|reduced| reduced.expr != right.expr);
            if l_changed || r_changed {
                let next_l = l_core.unwrap_or(left);
                let next_r = r_core.unwrap_or(right);
                work.push(Work::DeltaStep(next_l, next_r, context, state.after_step()));
                continue;
            }
            let (l, r) = (left, right);
            // KR-317: a K recursor stuck on a non-constructor major. Like the pin,
            // reduce only once the gate is established, so an unmet gate leaves
            // the pair to lazy delta, structure eta, and congruence instead of
            // failing it.
            for (s, t, s_on_left) in [(&l, &r, true), (&r, &l, false)] {
                if let Some(((major_type, constructor_type), reduced)) =
                    self.k_reduction(s, &context)?
                    && self.run(&major_type, &constructor_type, &context, false)?
                {
                    let reduced = Term::new(reduced);
                    let (a, b) = if s_on_left {
                        (reduced, t.clone())
                    } else {
                        (t.clone(), reduced)
                    };
                    work.push(Work::DeltaStep(a, b, context.clone(), state.after_step()));
                    continue 'work;
                }
            }
            // KR-317 below the head, under the same gate: see
            // `nested_k_reduction`.
            for (s, t, s_on_left) in [(&l, &r, true), (&r, &l, false)] {
                if let Some(((major_type, constructor_type), reduced)) =
                    self.nested_k_reduction(s, &context, Reach::Majors)?
                    && self.run(&major_type, &constructor_type, &context, false)?
                {
                    let reduced = Term::new(reduced);
                    let (a, b) = if s_on_left {
                        (reduced, t.clone())
                    } else {
                        (t.clone(), reduced)
                    };
                    work.push(Work::DeltaStep(a, b, context.clone(), state.after_step()));
                    continue 'work;
                }
            }
            // KR-317 through a projection (see `Reach`): reduce a K recursor
            // stuck beneath a projection before lazy delta or projection
            // congruence, as the pin's `reduce_proj` normalizes the projected
            // structure with `to_cnstr_when_K`.
            for (s, t, s_on_left) in [(&l, &r, true), (&r, &l, false)] {
                if self.projected_structure(s)?.is_none()
                    || !self.reaches_k_recursor(s, &context)?
                {
                    continue;
                }
                if let Some(((major_type, constructor_type), reduced)) =
                    self.nested_k_reduction(s, &context, Reach::MajorsAndProjections)?
                    && self.run(&major_type, &constructor_type, &context, false)?
                {
                    let reduced = Term::new(reduced);
                    let (a, b) = if s_on_left {
                        (reduced, t.clone())
                    } else {
                        (t.clone(), reduced)
                    };
                    work.push(Work::DeltaStep(a, b, context.clone(), state.after_step()));
                    continue 'work;
                }
            }
            // Pin-aligned height-ordered lazy delta (`type_checker.cpp:903-1055`):
            // unfold ONE step at the higher reducibility priority (preferring a
            // projection side over a constant side, as `try_unfold_proj_app`),
            // returning immediately via `Work::DeltaStep` so typed congruence
            // fires at every intermediate combinator layer without re-running
            // `proof_type` or polluting `taken`/`PairSet`/`PairAnswers`.
            let (mut left_height, left_proj) = self.definition_height_through(&l, &context)?;
            let (mut right_height, right_proj) = self.definition_height_through(&r, &context)?;
            let left_delta = left_height.is_some() && !left_proj;
            let right_delta = right_height.is_some() && !right_proj;
            if left_delta && !right_delta && right_proj && right_height.is_some() {
                let Some(reduced) = self.whnf_comparand_delta_step(&r, &context)? else {
                    fail!()
                };
                if reduced.expr != r.expr {
                    work.push(Work::DeltaStep(l, reduced, context, state.after_step()));
                    continue 'work;
                }
                right_height = None;
            } else if !left_delta && right_delta && left_proj && left_height.is_some() {
                let Some(reduced) = self.whnf_comparand_delta_step(&l, &context)? else {
                    fail!()
                };
                if reduced.expr != l.expr {
                    work.push(Work::DeltaStep(reduced, r, context, state.after_step()));
                    continue 'work;
                }
                left_height = None;
            }
            let (unfold_left, unfold_right) = match (left_height, right_height) {
                (Some(lh), Some(rh)) => (lh >= rh, rh >= lh),
                (Some(_), None) => (true, false),
                (None, Some(_)) => (false, true),
                (None, None) => (false, false),
            };
            if unfold_left || unfold_right {
                let mut next_l = if unfold_left {
                    let Some(reduced) = self.whnf_comparand_delta_step(&l, &context)? else {
                        fail!()
                    };
                    reduced
                } else {
                    l.clone()
                };
                let mut next_r = if unfold_right {
                    let Some(reduced) = self.whnf_comparand_delta_step(&r, &context)? else {
                        fail!()
                    };
                    reduced
                } else {
                    r.clone()
                };
                if next_l.expr == l.expr && !unfold_right && right_height.is_some() {
                    let Some(reduced) = self.whnf_comparand_delta_step(&r, &context)? else {
                        fail!()
                    };
                    next_r = reduced;
                } else if next_r.expr == r.expr && !unfold_left && left_height.is_some() {
                    let Some(reduced) = self.whnf_comparand_delta_step(&l, &context)? else {
                        fail!()
                    };
                    next_l = reduced;
                }
                if next_l.expr != l.expr || next_r.expr != r.expr {
                    work.push(Work::DeltaStep(next_l, next_r, context, state.after_step()));
                    continue 'work;
                }
            }
            // KR-315 unit-like conversion (`type_checker.cpp:1157`) runs once
            // lazy delta stops (and before non-backtracking structural
            // decomposition), avoiding `whnf(infer_type(left))` on pairs
            // settled by quick equality, congruence, or lazy delta.
            if let Some((lt, rt)) = self.unit_like_obligation(&l, &r, &context)? {
                work.push(Work::Pair(Term::new(lt), Term::new(rt), context));
                continue;
            }
            // KR-312 structure eta runs once neither side can delta-unfold
            // further (pin `type_checker.cpp:1049`): a constructor application
            // against a stuck term compares types and fields against projections.
            for (s, t, s_on_left) in [(&l, &r, true), (&r, &l, false)] {
                if let Some(obligations) = self.structure_eta(s, t, &context)? {
                    for (s_part, t_part) in obligations.into_iter().rev() {
                        let (a, b) = if s_on_left {
                            (Term::new(s_part), Term::new(t_part))
                        } else {
                            (Term::new(t_part), Term::new(s_part))
                        };
                        work.push(Work::Pair(a, b, context.clone()));
                    }
                    continue 'work;
                }
            }
            match (l.node(l.root()), r.node(r.root())) {
                (Some(ExprNode::Apply { .. }), Some(ExprNode::Apply { .. })) => {
                    // Peel all matching outer Apply layers in one shot to avoid
                    // O(n^2) prefix WireExpr materializations and `taken` clones.
                    let mut l_cursor = l.root();
                    let mut r_cursor = r.root();
                    let mut arg_pairs = Vec::new();
                    while let (
                        Some(ExprNode::Apply {
                            function: lf,
                            argument: la,
                        }),
                        Some(ExprNode::Apply {
                            function: rf,
                            argument: ra,
                        }),
                    ) = (l.node(l_cursor), r.node(r_cursor))
                    {
                        self.tick()?;
                        arg_pairs.push((*la, *ra));
                        l_cursor = *lf;
                        r_cursor = *rf;
                    }
                    // `arg_pairs` was collected outermost-first; reverse so we
                    // push arguments in forward order (0..m), causing the LIFO
                    // stack to check the heads first, then trailing arguments
                    // before leading typeclass instances.
                    arg_pairs.reverse();
                    let l_head = Term::new(self.piece(&l, l_cursor)?);
                    let r_head = Term::new(self.piece(&r, r_cursor)?);
                    for (la, ra) in arg_pairs {
                        let la = Term::new(self.piece(&l, la)?);
                        let ra = Term::new(self.piece(&r, ra)?);
                        work.push(Work::Pair(la, ra, context.clone()));
                    }
                    work.push(Work::Pair(l_head, r_head, context));
                }
                (
                    Some(ExprNode::Projection {
                        structure_name: ls,
                        index: li,
                        expression: le,
                    }),
                    Some(ExprNode::Projection {
                        structure_name: rs,
                        index: ri,
                        expression: re,
                    }),
                ) if ls == rs && li == ri => {
                    let le = Term::new(self.piece(&l, *le)?);
                    let re = Term::new(self.piece(&r, *re)?);
                    work.push(Work::Pair(le, re, context));
                }
                (Some(ExprNode::Metadata { expression: le, .. }), _) => {
                    let le = Term::new(self.piece(&l, *le)?);
                    work.push(Work::Pair(le, r, context));
                }
                (_, Some(ExprNode::Metadata { expression: re, .. })) => {
                    let re = Term::new(self.piece(&r, *re)?);
                    work.push(Work::Pair(l, re, context));
                }
                // KR-312, the pin's `try_eta_expansion_core` (type_checker.cpp:797):
                // a lambda against a non-lambda compares with the latter's eta
                // expansion through its Π-type, in either direction.
                (
                    Some(ExprNode::Lambda {
                        binder_type, body, ..
                    }),
                    _,
                ) => {
                    let (binder_type, body) = (*binder_type, *body);
                    let Some(other_domain) = self.pi_domain(&r, &context)? else {
                        fail!()
                    };
                    let domain = self.piece(&l, binder_type)?;
                    work.push(Work::Eta {
                        lambda: l,
                        body,
                        other: r,
                        domain: domain.clone(),
                        lambda_on_left: true,
                        context: context.clone(),
                    });
                    work.push(Work::Pair(
                        Term::new(domain),
                        Term::new(other_domain),
                        context,
                    ));
                }
                (
                    _,
                    Some(ExprNode::Lambda {
                        binder_type, body, ..
                    }),
                ) => {
                    let (binder_type, body) = (*binder_type, *body);
                    let Some(other_domain) = self.pi_domain(&l, &context)? else {
                        fail!()
                    };
                    let domain = self.piece(&r, binder_type)?;
                    work.push(Work::Eta {
                        lambda: r,
                        body,
                        other: l,
                        domain: domain.clone(),
                        lambda_on_left: false,
                        context: context.clone(),
                    });
                    work.push(Work::Pair(
                        Term::new(other_domain),
                        Term::new(domain),
                        context,
                    ));
                }
                _ => fail!(),
            }
        }
        Ok(true)
    }
}

/// Push `node` onto an arena under construction and return its id.
fn push_node(nodes: &mut Vec<ExprNode>, node: ExprNode) -> Option<ExprId> {
    let id = ExprId::from_index(nodes.len())?;
    nodes.push(node);
    Some(id)
}

/// Append `other`'s whole arena to one under construction, shifting every
/// reference, and return the id `other`'s root now has.
fn append_arena(
    nodes: &mut Vec<ExprNode>,
    levels: &mut Vec<LevelNode>,
    other: &WireExpr,
) -> Option<ExprId> {
    let (node_offset, level_offset) = (nodes.len(), levels.len());
    let e = |id: &ExprId| ExprId::from_index(id.index() + node_offset);
    let l = |id: &LevelId| LevelId::from_index(id.index() + level_offset);
    for level in other.levels() {
        levels.push(match level {
            LevelNode::Succ(a) => LevelNode::Succ(l(a)?),
            LevelNode::Max(a, b) => LevelNode::Max(l(a)?, l(b)?),
            LevelNode::IMax(a, b) => LevelNode::IMax(l(a)?, l(b)?),
            LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => level.clone(),
        });
    }
    for node in other.nodes() {
        nodes.push(match node {
            ExprNode::Sort { level } => ExprNode::Sort { level: l(level)? },
            ExprNode::Constant { name, levels } => ExprNode::Constant {
                name: name.clone(),
                levels: levels.iter().map(l).collect::<Option<_>>()?,
            },
            ExprNode::Apply { function, argument } => ExprNode::Apply {
                function: e(function)?,
                argument: e(argument)?,
            },
            ExprNode::Lambda {
                binder_name,
                binder_type,
                body,
                style,
            } => ExprNode::Lambda {
                binder_name: binder_name.clone(),
                binder_type: e(binder_type)?,
                body: e(body)?,
                style: *style,
            },
            ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style,
            } => ExprNode::Forall {
                binder_name: binder_name.clone(),
                binder_type: e(binder_type)?,
                body: e(body)?,
                style: *style,
            },
            ExprNode::Let {
                declaration_name,
                type_,
                value,
                body,
                non_dependent,
            } => ExprNode::Let {
                declaration_name: declaration_name.clone(),
                type_: e(type_)?,
                value: e(value)?,
                body: e(body)?,
                non_dependent: *non_dependent,
            },
            ExprNode::Metadata {
                entries,
                expression,
            } => ExprNode::Metadata {
                entries: entries.clone(),
                expression: e(expression)?,
            },
            ExprNode::Projection {
                structure_name,
                index,
                expression,
            } => ExprNode::Projection {
                structure_name: structure_name.clone(),
                index: *index,
                expression: e(expression)?,
            },
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => node.clone(),
        });
    }
    e(&other.root())
}

/// The constant at the head of `term`'s application spine, if there is one.
fn head_constant(term: &WireExpr) -> Option<&WireName> {
    let mut id = term.root();
    loop {
        match term.node(id)? {
            ExprNode::Apply { function, .. } => id = *function,
            ExprNode::Constant { name, .. } => return Some(name),
            _ => return None,
        }
    }
}

/// Whether `term` has a Nat/String literal or `Nat.*` head where untyped
/// `defeq`'s specialized numeric/string rules should run with the full budget.
fn has_nat_or_string_head(term: &WireExpr) -> bool {
    let mut id = term.root();
    loop {
        match term.node(id) {
            Some(ExprNode::Apply { function, .. }) => id = *function,
            Some(ExprNode::Metadata { expression, .. }) => id = *expression,
            Some(ExprNode::NatLiteral { .. } | ExprNode::StringLiteral(_)) => return true,
            Some(ExprNode::Constant { name, .. }) => {
                return matches!(name.parts().first(), Some(NamePart::Text(root)) if root == "Nat");
            }
            _ => return false,
        }
    }
}

/// The typed lane for a pair untyped conversion has just DEFERRED, under an
/// equivalent context: both callers reach it only on that outcome, so the root's
/// untyped query is not repeated.
pub(crate) fn proof_conversion_with(
    left: &WireExpr,
    right: &WireExpr,
    context: &InferenceContext,
    _mode: InferenceMode,
    budget: InferenceBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> ProofConversionOutcome {
    let mut probe = Probe {
        budget,
        steps: 0,
        polls: 0,
        cancelled,
        stop: None,
        root_left: left,
        root_right: right,
        root_context: context,
        reserved: None,
        unreserved_nested: Vec::new(),
        next: 0,
        incongruent: PairSet::default(),
        proven: PairSet::default(),
        disproven: PairSet::default(),
        answers: PairAnswers::default(),
        inferred: InferredTypes::default(),
        opened: OpenedLocals::default(),
    };
    match probe.run(left, right, context, true) {
        Ok(equal) => ProofConversionOutcome::Complete {
            equal,
            polls: probe.steps,
        },
        Err(halt) => ProofConversionOutcome::Halted(halt),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constant(text: &str) -> WireExpr {
        WireExpr::from_parts(
            vec![ExprNode::Constant {
                name: WireName::from_parts(vec![NamePart::Text(text.into())]),
                levels: Vec::new(),
            }],
            Vec::new(),
            ExprId::from_index(0).expect("the first expression id"),
        )
    }

    /// A recorded local belongs to exactly its task's key: the kind and both
    /// terms. The fingerprint normally separates two keys before they are
    /// compared, so each lookup here passes the SAME fingerprint, standing for
    /// a collision; only the exact comparison can then tell the keys apart. A
    /// key missing the second term would reopen an eta task at the local of
    /// another with the same lambda, and one missing the kind would open a
    /// binder pair at an eta task's local.
    #[test]
    fn an_opened_local_is_found_only_for_its_exact_key() {
        let mut opened = OpenedLocals::default();
        let (lambda, other, different) = (constant("lambda"), constant("a"), constant("b"));
        let name = WireName::from_parts(vec![NamePart::Text("x".into())]);
        let bucket = 7;
        opened.insert(bucket, Taken::Eta(false), &lambda, &other, name.clone());
        assert_eq!(
            opened.get(bucket, Taken::Eta(false), &lambda, &other),
            Some(&name)
        );
        assert_eq!(
            opened.get(bucket, Taken::Eta(false), &lambda, &different),
            None,
            "the second term is part of the key"
        );
        assert_eq!(
            opened.get(bucket, Taken::Eta(false), &different, &other),
            None,
            "the first term is part of the key"
        );
        assert_eq!(
            opened.get(bucket, Taken::Eta(true), &lambda, &other),
            None,
            "the eta side is part of the key"
        );
        assert_eq!(
            opened.get(bucket, Taken::Binders, &lambda, &other),
            None,
            "the task kind is part of the key"
        );
    }

    #[test]
    fn lazy_reservation_prevents_variable_capture_from_terms_and_let_local_values() {
        let colliding = WireName::from_parts(vec![
            NamePart::Text("_fln_proof_conversion".into()),
            NamePart::Numeric {
                value: 0,
                overflowed: false,
            },
        ]);
        let binder = WireName::from_parts(vec![NamePart::Text("x".into())]);
        let let_name = WireName::from_parts(vec![NamePart::Text("let_k".into())]);
        let sort0 = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: crate::wire::LevelId::from_index(0).expect("level 0"),
            }],
            vec![crate::wire::LevelNode::Zero],
            ExprId::from_index(0).expect("expr 0"),
        );
        let free_colliding = WireExpr::from_parts(
            vec![ExprNode::Free {
                name: colliding.clone(),
            }],
            Vec::new(),
            ExprId::from_index(0).expect("expr 0"),
        );
        // `fun x : Prop => _fln_proof_conversion.0` must NOT equal `fun x : Prop => x`.
        let lam_const_free = WireExpr::from_parts(
            vec![
                ExprNode::Sort {
                    level: crate::wire::LevelId::from_index(0).expect("level 0"),
                },
                ExprNode::Free { name: colliding },
                ExprNode::Lambda {
                    binder_name: binder.clone(),
                    binder_type: ExprId::from_index(0).expect("domain"),
                    body: ExprId::from_index(1).expect("free body"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            vec![crate::wire::LevelNode::Zero],
            ExprId::from_index(2).expect("lambda root"),
        );
        // `fun x : Prop => let_k`, where `let_k := _fln_proof_conversion.0`,
        // must ALSO NOT equal `fun x : Prop => x` after `let_k` unfolds.
        let lam_let_ref = WireExpr::from_parts(
            vec![
                ExprNode::Sort {
                    level: crate::wire::LevelId::from_index(0).expect("level 0"),
                },
                ExprNode::Free {
                    name: let_name.clone(),
                },
                ExprNode::Lambda {
                    binder_name: binder.clone(),
                    binder_type: ExprId::from_index(0).expect("domain"),
                    body: ExprId::from_index(1).expect("let body"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            vec![crate::wire::LevelNode::Zero],
            ExprId::from_index(2).expect("lambda root"),
        );
        let lam_identity = WireExpr::from_parts(
            vec![
                ExprNode::Sort {
                    level: crate::wire::LevelId::from_index(0).expect("level 0"),
                },
                ExprNode::Bound { index: 0 },
                ExprNode::Lambda {
                    binder_name: binder,
                    binder_type: ExprId::from_index(0).expect("domain"),
                    body: ExprId::from_index(1).expect("bound body"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            vec![crate::wire::LevelNode::Zero],
            ExprId::from_index(2).expect("lambda root"),
        );
        let constants = match crate::environment::ConstantEnvironment::build(
            Vec::new(),
            crate::environment::EnvironmentBudget::unlimited(),
        ) {
            crate::environment::EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("empty constant environment must build: {other:?}"),
        };
        let context = InferenceContext::new(
            vec![LocalDeclaration::definition(
                let_name,
                sort0,
                free_colliding,
            )],
            Vec::new(),
            constants,
        )
        .expect("context with let local must build");

        let direct = proof_conversion_with(
            &lam_const_free,
            &lam_identity,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
            &mut || false,
        );
        assert!(
            matches!(
                direct,
                ProofConversionOutcome::Complete { equal: false, .. }
            ),
            "direct free-name collision would capture the binder local: {direct:?}"
        );

        let via_let = proof_conversion_with(
            &lam_let_ref,
            &lam_identity,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
            &mut || false,
        );
        assert!(
            matches!(
                via_let,
                ProofConversionOutcome::Complete { equal: false, .. }
            ),
            "let-value free-name collision would capture the binder local after zeta: {via_let:?}"
        );
    }

    #[test]
    fn domain_equality_cache_separates_pairs_and_records_steps_needed() {
        let mut cache = DomainEqualityCache::default();
        let (a, b, c) = (constant("a"), constant("b"), constant("c"));
        let fp = PairSet::fingerprint(&a, &b);
        assert_eq!(cache.get(fp, &a, &b), None);
        cache.insert(fp, &a, &b, 42);
        assert_eq!(cache.get(fp, &a, &b), Some(42));
        assert_eq!(cache.get(PairSet::fingerprint(&b, &a), &b, &a), None);
        assert_eq!(cache.get(fp, &a, &c), None);
    }

    #[test]
    fn quick_subterm_literal_mismatch_does_not_reject_reducible_application() {
        use crate::environment::{
            ConstantDeclaration, ConstantEntry, ConstantKind, ConstantSafety, DefinitionBody,
            DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
        };
        let name = |s: &str| WireName::from_parts(vec![NamePart::Text(s.into())]);
        let sort_type = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: crate::wire::LevelId::from_index(1).expect("level 1"),
            }],
            vec![
                crate::wire::LevelNode::Zero,
                crate::wire::LevelNode::Succ(crate::wire::LevelId::ZERO),
            ],
            ExprId::ZERO,
        );
        let nat_to_nat = WireExpr::from_parts(
            vec![
                ExprNode::Constant {
                    name: name("Nat"),
                    levels: Vec::new(),
                },
                ExprNode::Forall {
                    binder_name: name("n"),
                    binder_type: ExprId::ZERO,
                    body: ExprId::ZERO,
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            Vec::new(),
            ExprId::from_index(1).expect("forall"),
        );
        let ignore_body = WireExpr::from_parts(
            vec![
                ExprNode::Constant {
                    name: name("Nat"),
                    levels: Vec::new(),
                },
                ExprNode::NatLiteral {
                    limbs_le: Vec::new(),
                },
                ExprNode::Lambda {
                    binder_name: name("n"),
                    binder_type: ExprId::ZERO,
                    body: ExprId::from_index(1).expect("zero"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            Vec::new(),
            ExprId::from_index(2).expect("lambda"),
        );
        let entries = vec![
            ConstantEntry::new(
                name("Nat"),
                ConstantDeclaration::header(
                    Vec::new(),
                    sort_type,
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("ignore"),
                ConstantDeclaration::definition(
                    Vec::new(),
                    nat_to_nat,
                    ConstantSafety::Safe,
                    DefinitionBody::new(
                        ignore_body,
                        ReducibilityHint::Regular(1),
                        DefinitionSafety::Safe,
                        Vec::new(),
                    ),
                ),
            ),
        ];
        let constants = match crate::environment::ConstantEnvironment::build(
            entries,
            EnvironmentBudget::unlimited(),
        ) {
            EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("environment must build: {other:?}"),
        };
        let context = InferenceContext::empty(constants);
        let app_lit = |v: u64| {
            WireExpr::from_parts(
                vec![
                    ExprNode::Constant {
                        name: name("ignore"),
                        levels: Vec::new(),
                    },
                    ExprNode::NatLiteral { limbs_le: vec![v] },
                    ExprNode::Apply {
                        function: ExprId::ZERO,
                        argument: ExprId::from_index(1).expect("lit"),
                    },
                ],
                Vec::new(),
                ExprId::from_index(2).expect("apply"),
            )
        };
        // `ignore 1 ≟ ignore 2`: quick conversion sees a subterm NatLiteral
        // mismatch beneath `ignore`, which must defer (not falsely reject) so
        // lazy delta unfolds `ignore` to `0 ≟ 0`.
        let outcome = proof_conversion_with(
            &app_lit(1),
            &app_lit(2),
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
            &mut || false,
        );
        assert!(
            matches!(
                outcome,
                ProofConversionOutcome::Complete { equal: true, .. }
            ),
            "subterm literal mismatch under reducible head must not falsely reject: {outcome:?}"
        );
    }

    #[test]
    fn typed_lazy_delta_matches_shared_head_before_unfolding_it() {
        use crate::environment::{
            ConstantDeclaration, ConstantEntry, ConstantKind, ConstantSafety, DefinitionBody,
            DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
        };
        let name = |s: &str| WireName::from_parts(vec![NamePart::Text(s.into())]);
        let sort_prop = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: crate::wire::LevelId::ZERO,
            }],
            vec![crate::wire::LevelNode::Zero],
            ExprId::ZERO,
        );
        let sort_type = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: crate::wire::LevelId::from_index(1).expect("level 1"),
            }],
            vec![
                crate::wire::LevelNode::Zero,
                crate::wire::LevelNode::Succ(crate::wire::LevelId::ZERO),
            ],
            ExprId::ZERO,
        );
        // `P : Prop`, `p1 p2 : P`, `T : Type`, `t0 : T`.
        // `shared : P -> T := fun _ => t0` (Regular height 1).
        // `wrap : P -> T := fun h => shared h` (Regular height 2).
        // Comparing `wrap p1` vs `shared p2`: lazy delta unfolds `wrap` (height 2)
        // to `shared p1`, matches shared head `shared` (height 1), and settles
        // `p1 ≟ p2` by proof irrelevance without unfolding `shared`.
        let p_const = constant("P");
        let t_const = constant("T");
        let p_to_t = WireExpr::from_parts(
            vec![
                ExprNode::Constant {
                    name: name("P"),
                    levels: Vec::new(),
                },
                ExprNode::Constant {
                    name: name("T"),
                    levels: Vec::new(),
                },
                ExprNode::Forall {
                    binder_name: name("h"),
                    binder_type: ExprId::ZERO,
                    body: ExprId::from_index(1).expect("body"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            Vec::new(),
            ExprId::from_index(2).expect("root"),
        );
        let shared_body = WireExpr::from_parts(
            vec![
                ExprNode::Constant {
                    name: name("P"),
                    levels: Vec::new(),
                },
                ExprNode::Constant {
                    name: name("T"),
                    levels: Vec::new(),
                },
                ExprNode::Constant {
                    name: name("t0"),
                    levels: Vec::new(),
                },
                ExprNode::Lambda {
                    binder_name: name("h"),
                    binder_type: ExprId::ZERO,
                    body: ExprId::from_index(2).expect("t0"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            Vec::new(),
            ExprId::from_index(3).expect("root"),
        );
        let wrap_body = WireExpr::from_parts(
            vec![
                ExprNode::Constant {
                    name: name("P"),
                    levels: Vec::new(),
                },
                ExprNode::Constant {
                    name: name("shared"),
                    levels: Vec::new(),
                },
                ExprNode::Bound { index: 0 },
                ExprNode::Apply {
                    function: ExprId::from_index(1).expect("shared"),
                    argument: ExprId::from_index(2).expect("bvar"),
                },
                ExprNode::Lambda {
                    binder_name: name("h"),
                    binder_type: ExprId::ZERO,
                    body: ExprId::from_index(3).expect("apply"),
                    style: crate::wire::BinderStyle::Default,
                },
            ],
            Vec::new(),
            ExprId::from_index(4).expect("root"),
        );
        let entries = vec![
            ConstantEntry::new(
                name("P"),
                ConstantDeclaration::header(
                    Vec::new(),
                    sort_prop,
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("p1"),
                ConstantDeclaration::header(
                    Vec::new(),
                    p_const.clone(),
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("p2"),
                ConstantDeclaration::header(
                    Vec::new(),
                    p_const,
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("T"),
                ConstantDeclaration::header(
                    Vec::new(),
                    sort_type,
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("t0"),
                ConstantDeclaration::header(
                    Vec::new(),
                    t_const,
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("shared"),
                ConstantDeclaration::definition(
                    Vec::new(),
                    p_to_t.clone(),
                    ConstantSafety::Safe,
                    DefinitionBody::new(
                        shared_body,
                        ReducibilityHint::Regular(1),
                        DefinitionSafety::Safe,
                        Vec::new(),
                    ),
                ),
            ),
            ConstantEntry::new(
                name("wrap"),
                ConstantDeclaration::definition(
                    Vec::new(),
                    p_to_t,
                    ConstantSafety::Safe,
                    DefinitionBody::new(
                        wrap_body,
                        ReducibilityHint::Regular(2),
                        DefinitionSafety::Safe,
                        Vec::new(),
                    ),
                ),
            ),
        ];
        let constants = match crate::environment::ConstantEnvironment::build(
            entries,
            EnvironmentBudget::unlimited(),
        ) {
            EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("environment must build: {other:?}"),
        };
        let context = InferenceContext::empty(constants);
        let apply = |f: &str, a: &str| {
            WireExpr::from_parts(
                vec![
                    ExprNode::Constant {
                        name: name(f),
                        levels: Vec::new(),
                    },
                    ExprNode::Constant {
                        name: name(a),
                        levels: Vec::new(),
                    },
                    ExprNode::Apply {
                        function: ExprId::ZERO,
                        argument: ExprId::from_index(1).expect("arg"),
                    },
                ],
                Vec::new(),
                ExprId::from_index(2).expect("apply"),
            )
        };
        let outcome = proof_conversion_with(
            &apply("wrap", "p1"),
            &apply("shared", "p2"),
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
            &mut || false,
        );
        assert!(
            matches!(
                outcome,
                ProofConversionOutcome::Complete { equal: true, .. }
            ),
            "height-ordered lazy delta must unfold wrap to shared and prove p1 ≟ p2: {outcome:?}"
        );
    }

    #[test]
    fn typed_lazy_delta_skips_proof_type_and_pair_set_on_intermediate_steps() {
        use crate::environment::{
            ConstantDeclaration, ConstantEntry, ConstantKind, ConstantSafety, DefinitionBody,
            DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
        };
        assert!(
            ReducibilityHint::Regular(0).delta_priority()
                > ReducibilityHint::Opaque.delta_priority()
        );
        assert!(
            ReducibilityHint::Abbrev.delta_priority()
                > ReducibilityHint::Regular(u32::MAX).delta_priority()
        );
        let name = |s: &str| WireName::from_parts(vec![NamePart::Text(s.into())]);
        let sort_type = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: crate::wire::LevelId::from_index(1).expect("level 1"),
            }],
            vec![
                crate::wire::LevelNode::Zero,
                crate::wire::LevelNode::Succ(crate::wire::LevelId::ZERO),
            ],
            ExprId::ZERO,
        );
        let t_const = constant("T");
        let mut entries = vec![
            ConstantEntry::new(
                name("T"),
                ConstantDeclaration::header(
                    Vec::new(),
                    sort_type,
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
            ConstantEntry::new(
                name("d0"),
                ConstantDeclaration::header(
                    Vec::new(),
                    t_const.clone(),
                    ConstantKind::Axiom,
                    ConstantSafety::Safe,
                ),
            ),
        ];
        // Build a 12-step regular delta chain `d12 -> d11 -> ... -> d0 : T`
        // over a non-Prop carrier `T : Type`.
        for i in 1_u32..=12 {
            let prev = format!("d{}", i - 1);
            let cur = format!("d{i}");
            entries.push(ConstantEntry::new(
                name(&cur),
                ConstantDeclaration::definition(
                    Vec::new(),
                    t_const.clone(),
                    ConstantSafety::Safe,
                    DefinitionBody::new(
                        constant(&prev),
                        ReducibilityHint::Regular(i),
                        DefinitionSafety::Safe,
                        Vec::new(),
                    ),
                ),
            ));
        }
        let constants = match crate::environment::ConstantEnvironment::build(
            entries,
            EnvironmentBudget::unlimited(),
        ) {
            EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("environment must build: {other:?}"),
        };
        let context = InferenceContext::empty(constants);
        let left = constant("d12");
        let right = constant("d0");
        let mut cancelled = || false;
        let mut probe = Probe {
            budget: InferenceBudget::unlimited(),
            steps: 0,
            polls: 0,
            cancelled: &mut cancelled,
            stop: None,
            root_left: &left,
            root_right: &right,
            root_context: &context,
            reserved: None,
            unreserved_nested: Vec::new(),
            next: 0,
            incongruent: PairSet::default(),
            proven: PairSet::default(),
            disproven: PairSet::default(),
            answers: PairAnswers::default(),
            inferred: InferredTypes::default(),
            opened: OpenedLocals::default(),
        };
        let equal = probe
            .run(&left, &right, &context, true)
            .expect("delta chain must succeed");
        assert!(equal);
        // Only the entry term `d12` and its type `T` should have been inferred;
        // intermediate delta states `d11..d1` must not re-run `proof_status`.
        assert!(
            probe.inferred.current.buckets.len() <= 3,
            "intermediate lazy-delta steps must not re-run proof_type inference: inferred_buckets={}",
            probe.inferred.current.buckets.len()
        );
        // Only the logical root pair `(d12, d0)` enters `proven`; intermediate
        // delta pairs `(d11, d0) .. (d1, d0)` must not thrash `PairSet`.
        assert!(
            probe.proven.current.buckets.len() <= 1,
            "intermediate lazy-delta steps must not populate PairSet: proven_buckets={}",
            probe.proven.current.buckets.len()
        );
        // Intermediate delta steps must not clone into `PairAnswers`.
        assert_eq!(
            probe.answers.current.buckets.len(),
            0,
            "intermediate lazy-delta steps must not populate PairAnswers"
        );
    }
}
