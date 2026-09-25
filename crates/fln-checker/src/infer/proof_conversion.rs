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
            /// KR-312: open `lambda`'s body at a fresh local `x : domain` and
            /// compare it with `other x`, keeping the original sides.
            Eta {
                lambda: WireExpr,
                body: ExprId,
                other: WireExpr,
                domain: WireExpr,
                lambda_on_left: bool,
                context: InferenceContext,
            },
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
        let mut skip_untyped = root_deferred;
        'work: while let Some(task) = work.pop() {
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
                Work::Eta {
                    lambda,
                    body,
                    other,
                    domain,
                    lambda_on_left,
                    context,
                } => {
                    let (name, local) = self.local()?;
                    let mut locals = context.locals().to_vec();
                    locals.push(LocalDeclaration::assumption(name.clone(), domain));
                    let context = InferenceContext::new_with_projection_rules(
                        locals,
                        context.level_parameters().to_vec(),
                        context.projection_rules().to_vec(),
                        context.constants().clone(),
                    )
                    .map_err(|_| {
                        self.fault(InferenceFault::ScopedLocalCollision { name: name.clone() })
                    })?;
                    let opened = self.open(&lambda, body, &local)?;
                    let applied = self.apply_to_free(&other, name)?;
                    let (left, right) = if lambda_on_left {
                        (opened, applied)
                    } else {
                        (applied, opened)
                    };
                    work.push(Work::Pair(left, right, context));
                    continue;
                }
            };
            if !std::mem::take(&mut skip_untyped) {
                match self.equal(&left, &right, &context)? {
                    Some(true) => continue,
                    Some(false) => return Ok(false),
                    None => {}
                }
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
            if let Some((lt, rt)) = self.unit_like_obligation(&left, &right, &context)? {
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
            // KR-312 structure eta runs before congruence: after whnf the other
            // side's head is stuck, so `mk a b ≟ f x` could only fail on heads.
            for (s, t, s_on_left) in [(&l, &r, true), (&r, &l, false)] {
                if let Some(obligations) = self.structure_eta(s, t, &context)? {
                    for (s_part, t_part) in obligations.into_iter().rev() {
                        let (a, b) = if s_on_left {
                            (s_part, t_part)
                        } else {
                            (t_part, s_part)
                        };
                        work.push(Work::Pair(a, b, context.clone()));
                    }
                    continue 'work;
                }
            }
            // KR-317: a K recursor stuck on a non-constructor major. Like the pin,
            // reduce only once the gate is established, so an unmet gate leaves
            // the pair to congruence and the other rules instead of failing it.
            for (s, t, s_on_left) in [(&l, &r, true), (&r, &l, false)] {
                if let Some(((major_type, constructor_type), reduced)) =
                    self.k_reduction(s, &context)?
                    && self.run(&major_type, &constructor_type, &context, false)?
                {
                    let (a, b) = if s_on_left {
                        (reduced, t.clone())
                    } else {
                        (t.clone(), reduced)
                    };
                    work.push(Work::Pair(a, b, context.clone()));
                    continue 'work;
                }
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
                        return Ok(false);
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
                    work.push(Work::Pair(domain, other_domain, context));
                }
                (
                    _,
                    Some(ExprNode::Lambda {
                        binder_type, body, ..
                    }),
                ) => {
                    let (binder_type, body) = (*binder_type, *body);
                    let Some(other_domain) = self.pi_domain(&l, &context)? else {
                        return Ok(false);
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
                    work.push(Work::Pair(other_domain, domain, context));
                }
                _ => return Ok(false),
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
        reserved: BTreeSet::new(),
        next: 0,
    };
    match probe.run(left, right, context, true) {
        Ok(equal) => ProofConversionOutcome::Complete {
            equal,
            polls: probe.steps,
        },
        Err(halt) => ProofConversionOutcome::Halted(halt),
    }
}
