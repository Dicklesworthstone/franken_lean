//! A typed, sufficient KR-305 conversion lane. The untyped converter cannot
//! identify proofs under binders because it has no local type context. This
//! worklist opens matching binders hygienically and uses checker-owned typing
//! to compare proofs of the same proposition. Probes explicitly disable this
//! lane, so nested conversion never recursively reenters typed inference.
use super::*;
use crate::universe::{NormalNode, normalize};
use crate::wire::WireLevel;

pub(crate) enum ProofConversionOutcome {
    Complete { equal: bool, polls: u64 },
    Halted(Box<InferenceOutcome>),
}
struct Probe<'a> {
    budget: InferenceBudget,
    steps: u64,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
    stop: Option<InferenceStop>,
    reserved: BTreeSet<WireName>,
    next: u64,
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
            if let ExprNode::Free { name } = node {
                self.reserved.insert(name.clone());
            }
        }
        Ok(())
    }
    fn local(&mut self) -> Result<(WireName, WireExpr)> {
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
            if self.reserved.insert(name.clone()) {
                let root = ExprId::from_index(0)
                    .ok_or_else(|| self.fault(InferenceFault::LiteralTypeAllocation))?;
                return Ok((
                    name.clone(),
                    WireExpr::from_parts(vec![ExprNode::Free { name }], vec![], root),
                ));
            }
        }
    }
    fn infer(&mut self, term: &WireExpr, context: &InferenceContext) -> Result<Option<WireExpr>> {
        let budget = self.budget;
        let mode = InferenceMode::InferOnly;
        let result =
            infer_without_proof_conversion(term, context, mode, budget, &mut || self.poll());
        self.check_stop()?;
        match result {
            InferenceOutcome::Complete(result) => Ok(Some(result.type_)),
            InferenceOutcome::Refused { .. } | InferenceOutcome::Deferred { .. } => Ok(None),
            halt => Err(Box::new(halt)),
        }
    }
    fn whnf(&mut self, term: &WireExpr, context: &InferenceContext) -> Result<Option<WireExpr>> {
        let budget = self.budget.whnf;
        let result = whnf_with(term, context.reduction(), budget, &mut || self.poll());
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
    ) -> Result<Option<bool>> {
        let budget = self.budget.defeq;
        let result = def_eq_with(left, right, context.reduction(), budget, &mut || {
            self.poll()
        });
        self.check_stop()?;
        match result {
            DefEqOutcome::Equal(_) => Ok(Some(true)),
            DefEqOutcome::NotEqual { .. } | DefEqOutcome::Refused { .. } => Ok(Some(false)),
            DefEqOutcome::Deferred { .. } => Ok(None),
            DefEqOutcome::Inconclusive(stop) => Err(Box::new(InferenceOutcome::Inconclusive(
                InferenceStop::DefEq {
                    argument: 0,
                    stop: Box::new(stop),
                    progress: self.progress(),
                },
            ))),
            DefEqOutcome::InternalFault(fault) => {
                Err(self.fault(InferenceFault::DefEq { argument: 0, fault }))
            }
        }
    }
    fn proof_type(
        &mut self,
        term: &WireExpr,
        context: &InferenceContext,
    ) -> Result<Option<WireExpr>> {
        // A type constructor cannot itself be a proof. Avoid expensive failed
        // queries while descending the declaration's outer function telescope.
        if matches!(
            term.node(term.root()),
            Some(ExprNode::Sort { .. } | ExprNode::Forall { .. })
        ) {
            return Ok(None);
        }
        let Some(type_) = self.infer(term, context)? else {
            return Ok(None);
        };
        let Some(sort) = self.infer(&type_, context)? else {
            return Ok(None);
        };
        let Some(sort) = self.whnf(&sort, context)? else {
            return Ok(None);
        };
        let Some(ExprNode::Sort { level }) = sort.node(sort.root()) else {
            return Ok(None);
        };
        self.tick()?;
        let normalized = normalize(&WireLevel::from_parts(sort.levels().to_vec(), *level));
        Ok(normalized
            .ok()
            .filter(|n| matches!(n.nodes().get(n.root().index()), Some(NormalNode::Zero)))
            .map(|_| type_))
    }
    fn run(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
        context: &InferenceContext,
    ) -> Result<bool> {
        enum Work {
            Pair(WireExpr, WireExpr, InferenceContext),
            Binders(
                WireExpr,
                WireExpr,
                ExprId,
                ExprId,
                WireExpr,
                InferenceContext,
            ),
        }
        self.reserve(left)?;
        self.reserve(right)?;
        for local in context.locals() {
            self.tick()?;
            self.reserved.insert(local.name().clone());
            self.reserve(local.type_())?;
            if let Some(value) = local.value() {
                self.reserve(value)?;
            }
        }
        let mut work = vec![Work::Pair(left.clone(), right.clone(), context.clone())];
        while let Some(task) = work.pop() {
            self.tick()?;
            let (left, right, context) = match task {
                Work::Pair(left, right, context) => (left, right, context),
                Work::Binders(left, right, lb, rb, domain, context) => {
                    let (name, local) = self.local()?;
                    let mut locals = context.locals().to_vec();
                    locals.push(LocalDeclaration::assumption(name.clone(), domain));
                    let context = InferenceContext::new_with_projection_rules(
                        locals,
                        context.level_parameters().to_vec(),
                        context.projection_rules().to_vec(),
                        context.constants().clone(),
                    )
                    .map_err(|_| self.fault(InferenceFault::ScopedLocalCollision { name }))?;
                    let left = self.open(&left, lb, &local)?;
                    let right = self.open(&right, rb, &local)?;
                    work.push(Work::Pair(left, right, context));
                    continue;
                }
            };
            match self.equal(&left, &right, &context)? {
                Some(true) => continue,
                Some(false) => return Ok(false),
                None => {}
            }
            // Both witnesses must independently type-check as proofs. The two
            // proposition types become a further conversion obligation; merely
            // inhabiting Prop never equates distinct propositions.
            if let Some(lt) = self.proof_type(&left, &context)?
                && let Some(rt) = self.proof_type(&right, &context)?
            {
                work.push(Work::Pair(lt, rt, context));
                continue;
            }
            let Some(l) = self.whnf(&left, &context)? else {
                return Ok(false);
            };
            let Some(r) = self.whnf(&right, &context)? else {
                return Ok(false);
            };
            // A changed head may expose ordinary conversion or proof evidence.
            if l != left || r != right {
                work.push(Work::Pair(l, r, context));
                continue;
            }
            match (l.node(l.root()), r.node(r.root())) {
                (
                    Some(ExprNode::Apply {
                        function: lf,
                        argument: la,
                    }),
                    Some(ExprNode::Apply {
                        function: rf,
                        argument: ra,
                    }),
                ) => {
                    let lf = self.piece(&l, *lf)?;
                    let rf = self.piece(&r, *rf)?;
                    let la = self.piece(&l, *la)?;
                    let ra = self.piece(&r, *ra)?;
                    work.push(Work::Pair(la, ra, context.clone()));
                    work.push(Work::Pair(lf, rf, context));
                }
                (
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
                ) => {
                    let domain = self.piece(&l, *lt)?;
                    let other = self.piece(&r, *rt)?;
                    let lb = *lb;
                    let rb = *rb;
                    work.push(Work::Binders(l, r, lb, rb, domain.clone(), context.clone()));
                    work.push(Work::Pair(domain, other, context));
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
                    let le = self.piece(&l, *le)?;
                    let re = self.piece(&r, *re)?;
                    work.push(Work::Pair(le, re, context));
                }
                (Some(ExprNode::Metadata { expression: le, .. }), _) => {
                    let le = self.piece(&l, *le)?;
                    work.push(Work::Pair(le, r, context));
                }
                (_, Some(ExprNode::Metadata { expression: re, .. })) => {
                    let re = self.piece(&r, *re)?;
                    work.push(Work::Pair(l, re, context));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

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
        reserved: BTreeSet::new(),
        next: 0,
    };
    match probe.run(left, right, context) {
        Ok(equal) => ProofConversionOutcome::Complete {
            equal,
            polls: probe.steps,
        },
        Err(halt) => ProofConversionOutcome::Halted(halt),
    }
}
