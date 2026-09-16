//! Transactional, bounded native instance search. Class inputs must be known
//! before search; output parameters may be inferred by the selected instance.
//! Search uses an explicit stack and never turns exhaustion into "not found".
use super::*;
use crate::instances::{InstanceRegistry, InstanceRegistryError, result_head};

mod parameters;

const MAX_SEARCH_DEPTH: usize = 128;
const MAX_CANDIDATE_ATTEMPTS: usize = 4096;

#[derive(Clone)]
enum Candidate {
    Local(FVarId),
    Global(Name),
}
struct Expansion {
    value: Expr,
    subgoals: Vec<MVarId>,
}
struct Frame {
    goal: MVarId,
    target: Expr,
    expected: Expr,
    key: Expr,
    binders: Vec<LocalDecl>,
    base: Context,
    candidates: Vec<Candidate>,
    cursor: usize,
    chosen: Option<Expansion>,
    // Successful prerequisites remain resumable until the enclosing candidate
    // completes. Arena indices keep this history flat, not recursively cloned.
    children: Vec<usize>,
    resumable: bool,
}

pub(super) fn registry_error(error: InstanceRegistryError) -> NatDefinitionElabError {
    failure(SourceInferenceError::InstanceRegistry(error))
}
pub(super) fn nonmatch(error: &NatDefinitionElabError) -> bool {
    let NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)) = error else {
        return false;
    };
    match error.as_ref() {
        UnificationError::Deferred(_)
        | UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. }) => true,
        UnificationError::AssignmentCheck { outcome, .. } => matches!(
            outcome.as_ref(),
            Outcome::Complete(Verdict::Rejected { .. })
        ),
        _ => false,
    }
}

impl Context {
    fn instance_type(&mut self, type_: &Expr) -> Result<Expr, NatDefinitionElabError> {
        // Class discovery unfolds abbreviations, but neither ordinary
        // definitions nor local type aliases. Candidate matching can still
        // use the ordinary unifier after this eligibility check.
        self.whnf_with_transparency(type_, UnificationTransparency::Abbreviations, false)
    }

    pub(super) fn instance_hole(&mut self, type_: Expr) -> Result<Expr, NatDefinitionElabError> {
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            type_,
            self.txn.lctx.clone(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        self.instance_goals.push(id.clone());
        Ok(Expr::mvar(id))
    }

    /// Same annotation rule as the supported portion of Term.ElabBinders:
    /// instance binders must end in a registered class, and non-instance
    /// parameters of parametric local instances must have forward dependencies.
    pub(super) fn validate_instance_binder(
        &mut self,
        domain: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let registry = InstanceRegistry::read(&self.txn.env).map_err(registry_error)?;
        let mut trial = self.clone();
        let mut target = domain.clone();
        let result = (|| {
            loop {
                trial.tick()?;
                target = trial.instance_type(&target)?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = target.node()
                else {
                    break;
                };
                if *binder_info != BinderInfo::InstImplicit && !body.has_loose_bvar(0) {
                    return Err(failure(SourceInferenceError::InvalidInstanceBinder));
                }
                let id = FVarId(trial.fresh_name()?);
                let next = trial.substitute(body, &Expr::fvar(id.clone()))?;
                trial.txn.lctx.add_param(
                    id.clone(),
                    id.0.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                target = next;
            }
            if result_head(&target).is_some_and(|name| registry.is_class(&name)) {
                Ok(())
            } else {
                Err(failure(SourceInferenceError::InvalidInstanceBinder))
            }
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        result
    }

    pub(super) fn resolve_instances(
        &mut self,
        final_pass: bool,
    ) -> Result<(), NatDefinitionElabError> {
        if self
            .instance_goals
            .iter()
            .all(|id| self.txn.mvars.is_assigned(id))
        {
            return Ok(());
        }
        self.flush(false)?;
        let registry = InstanceRegistry::read(&self.txn.env).map_err(registry_error)?;
        loop {
            let before = self.txn.mvars.assignments().len();
            for id in self.instance_goals.clone() {
                self.tick()?;
                if self.txn.mvars.is_assigned(&id) {
                    continue;
                }
                let mut trial = self.clone();
                let saved = trial.txn.lctx.clone();
                // An outer equation may itself need this dictionary's fields.
                // Candidate matching must solve only its own equations, not
                // demand the result of an as-yet unassigned dictionary. Retain
                // all suspended obligations and retry them after publication.
                let suspended = std::mem::take(&mut trial.equations);
                let result = trial.search_instance(id, &registry);
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                match result {
                    Ok(true) => {
                        trial.txn.lctx = saved;
                        // Resume with the now-available dictionary projections,
                        // without widening class-head matching transparency.
                        for mut equation in suspended {
                            let left = trial.whnf(&equation.sides.0)?;
                            let right = trial.whnf(&equation.sides.1)?;
                            equation.sides = (left, right);
                            trial.equations.push(equation);
                        }
                        *self = trial;
                    }
                    Ok(false) => {}
                    Err(error) => return Err(error),
                }
            }
            self.flush(false)?;
            if self.txn.mvars.assignments().len() == before {
                if final_pass && self.resolve_default_instance(&registry)? {
                    continue;
                }
                break;
            }
        }
        if final_pass
            && self
                .instance_goals
                .iter()
                .any(|id| !self.txn.mvars.is_assigned(id))
        {
            return Err(failure(SourceInferenceError::InstanceSynthesisRequired));
        }
        Ok(())
    }

    /// Defaults are tried only after ordinary synthesis reaches a fixed point.
    /// Higher priorities run across all pending goals before any lower priority.
    /// Commit just one complete result, then rerun ordinary synthesis first.
    fn resolve_default_instance(
        &mut self,
        registry: &InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        let defaults = crate::instances::defaults::read(&self.txn.env).map_err(registry_error)?;
        let mut priorities = std::collections::BTreeSet::new();
        for row in &defaults {
            priorities.insert(row.candidate.priority);
        }
        for priority in priorities.into_iter().rev() {
            for id in self.instance_goals.clone() {
                self.tick()?;
                if self.txn.mvars.is_assigned(&id) {
                    continue;
                }
                let decl = self
                    .txn
                    .mvars
                    .get_decl(&id)
                    .cloned()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                let mut probe = self.clone();
                probe.txn.lctx = decl.lctx;
                let target = probe.instance_type(&decl.type_);
                self.txn.budget.heartbeats_consumed = probe.txn.budget.heartbeats_consumed;
                let Some(class) = result_head(&target?) else {
                    continue;
                };
                for row in &defaults {
                    self.tick()?;
                    if row.candidate.priority != priority || row.class != class {
                        continue;
                    }
                    let mut trial = self.clone();
                    let saved = trial.txn.lctx.clone();
                    let suspended = std::mem::take(&mut trial.equations);
                    let result = trial.search_instance_mode(
                        id.clone(),
                        registry,
                        Some(&row.candidate.declaration),
                    );
                    self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                    if result? {
                        trial.txn.lctx = saved;
                        trial.equations.extend(suspended);
                        *self = trial;
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    /// Build a speculative frame. Unknown ordinary inputs block this goal;
    /// unknown output and semi-output parameters do not.
    fn instance_frame(
        &mut self,
        goal: MVarId,
        registry: &InstanceRegistry,
        ambient: &LocalContext,
        default: Option<&Name>,
    ) -> Result<Option<Frame>, NatDefinitionElabError> {
        let decl = self
            .txn
            .mvars
            .get_decl(&goal)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        self.txn.lctx = decl.lctx;
        let mut target = self.instance_type(&decl.type_)?;
        let mut binders = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = target.node()
        {
            self.tick()?;
            if binder_type.has_expr_mvar() || binder_type.has_level_mvar() {
                return Ok(None);
            }
            let id = FVarId(self.fresh_name()?);
            let body = self.substitute(body, &Expr::fvar(id.clone()))?;
            binders.push(
                self.txn
                    .lctx
                    .add_param(id, binder_name.clone(), binder_type.clone(), *binder_info)
                    .clone(),
            );
            target = self.instance_type(&body)?;
        }
        let Some(class) = result_head(&target).filter(|c| registry.is_class(c)) else {
            if target.has_expr_mvar() || target.has_level_mvar() {
                return Ok(None);
            }
            return Err(failure(SourceInferenceError::InvalidInstanceBinder));
        };
        let prepared = if default.is_some() {
            // Default application unifies the original goal, including known
            // outputs. Unlike ordinary synthesis, it can fix unknown inputs.
            parameters::PreparedTarget {
                target: target.clone(),
                expected: target.clone(),
                key: target,
            }
        } else {
            let Some(prepared) = self.prepare_instance_target(&target)? else {
                return Ok(None);
            };
            prepared
        };
        let mut candidates = Vec::new();
        // Lean tries the newest local instance before global registrations.
        let locals = self.txn.lctx.clone();
        for local in locals.decls().iter().rev() {
            // Target binders give candidate terms their scope, but do not
            // extend the local-instance population of this search. This also
            // holds for recursive prerequisites under those binders.
            if !ambient.contains(&local.id) || self.is_matrix_hypothesis(local) {
                continue;
            }
            let eligible = if local.binder_info == BinderInfo::InstImplicit {
                true
            } else {
                let type_ = self.instance_type(&local.type_)?;
                !matches!(type_.node(), ExprNode::ForallE { .. })
                    && result_head(&type_).is_some_and(|name| name == class)
            };
            if eligible {
                candidates.push(Candidate::Local(local.id.clone()));
            }
        }
        candidates.extend(
            registry
                .candidates(&class)
                .iter()
                .map(|row| Candidate::Global(row.declaration.clone())),
        );
        if let Some(default) = default {
            candidates = vec![Candidate::Global(default.clone())];
        }
        let resumable = prepared.expected.has_expr_mvar();
        Ok(Some(Frame {
            resumable,
            goal,
            target: prepared.target,
            expected: prepared.expected,
            key: prepared.key,
            binders,
            base: self.clone(),
            candidates,
            cursor: 0,
            chosen: None,
            children: Vec::new(),
        }))
    }

    fn expand_instance(
        &mut self,
        candidate: &Candidate,
        target: &Expr,
    ) -> Result<Option<Expansion>, NatDefinitionElabError> {
        let mut term = match candidate {
            Candidate::Local(id) => {
                let local = self
                    .txn
                    .lctx
                    .find(id)
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                Typed {
                    value: Expr::fvar(id.clone()),
                    type_: local.type_.clone(),
                }
            }
            Candidate::Global(name) => self.constant(name)?,
        };
        let mut subgoals = Vec::new();
        loop {
            self.tick()?;
            term.type_ = self.whnf(&term.type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = term.type_.node()
            else {
                break;
            };
            let body = body.clone();
            let arg = if *binder_info == BinderInfo::InstImplicit {
                let arg = self.instance_hole(binder_type.clone())?;
                let ExprNode::MVar { id } = arg.node() else {
                    unreachable!("fresh instance hole")
                };
                subgoals.push(id.clone());
                arg
            } else {
                self.hole(binder_type.clone())?
            };
            term.type_ = self.substitute(&body, &arg)?;
            term.value = Expr::app(term.value, arg);
        }
        self.constrain(&term.type_, target)?;
        self.equations
            .push(SourceEquation::selection(term.type_, target.clone()));
        self.flush(true)?;
        Ok(Some(Expansion {
            value: term.value,
            subgoals,
        }))
    }

    /// Resume the most recent successful prerequisite, descending through its
    /// own choices first. Its base retains earlier siblings but none of the
    /// abandoned branch's assignments, holes, constraints or local declarations.
    fn retry_instance_choice(
        &mut self,
        frames: &mut Vec<Frame>,
        history: &mut [Option<Frame>],
    ) -> Result<(), NatDefinitionElabError> {
        loop {
            self.tick()?;
            let Some(frame) = frames.last_mut() else {
                return Ok(());
            };
            if let Some(child) = frame.children.pop() {
                let child = history[child].take().expect("live instance choice");
                frames.push(child);
                continue;
            }
            frame.chosen = None;
            let spent = self.txn.budget.heartbeats_consumed;
            *self = frame.base.clone();
            self.txn.budget.heartbeats_consumed = spent;
            return Ok(());
        }
    }

    fn discard_instance_choices(
        &mut self,
        frame: Frame,
        history: &mut [Option<Frame>],
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = frame.children;
        while let Some(index) = pending.pop() {
            self.tick()?;
            if let Some(child) = history[index].take() {
                pending.extend(child.children);
            }
        }
        Ok(())
    }

    pub(super) fn search_instance(
        &mut self,
        root: MVarId,
        registry: &InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        self.search_instance_mode(root, registry, None)
    }

    fn search_instance_mode(
        &mut self,
        root: MVarId,
        registry: &InstanceRegistry,
        default: Option<&Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        let ambient = self
            .txn
            .mvars
            .get_decl(&root)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?
            .lctx
            .clone();
        let Some(first) = self.instance_frame(root, registry, &ambient, default)? else {
            return Ok(false);
        };
        let mut frames = vec![first];
        let mut history = Vec::new();
        let mut attempts = 0usize;
        while !frames.is_empty() {
            self.tick()?;
            let index = frames.len() - 1;
            if let Some(expansion) = &frames[index].chosen {
                let mut remaining = false;
                let mut ready = None;
                // A later prerequisite may infer the input that blocks an
                // earlier one. Rescan after each successful child, preserving
                // declaration order among ready goals. An all-blocked set is
                // a failed candidate, never permission to guess input values.
                for id in &expansion.subgoals {
                    self.tick()?;
                    if self.txn.mvars.is_assigned(id) {
                        continue;
                    }
                    remaining = true;
                    let mut trial = self.clone();
                    let child = trial.instance_frame(id.clone(), registry, &ambient, None);
                    self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                    if let Some(child) = child? {
                        *self = trial;
                        ready = Some(child);
                        break;
                    }
                    // Drop speculative output holes and opened binders from
                    // blocked preparation, but retain every charged heartbeat.
                }
                if let Some(child) = ready {
                    if frames.iter().any(|frame| frame.key == child.key) {
                        self.retry_instance_choice(&mut frames, &mut history)?;
                        continue;
                    }
                    if frames.len() >= MAX_SEARCH_DEPTH {
                        return Err(failure(SourceInferenceError::ResourceLimit));
                    }
                    frames.push(child);
                    continue;
                }
                if remaining {
                    self.retry_instance_choice(&mut frames, &mut history)?;
                    continue;
                }
                let mut value = self.instantiate(&expansion.value)?;
                let actual = self.instantiate(&frames[index].target)?;
                if value.has_expr_mvar()
                    || value.has_level_mvar()
                    || actual.has_expr_mvar()
                    || actual.has_level_mvar()
                {
                    self.retry_instance_choice(&mut frames, &mut history)?;
                    continue;
                }
                // Selection never sees existing output values. Reconcile only
                // after a complete candidate, in this goal's own local scope.
                // A mismatch ends this goal; trying a lower-priority instance
                // here would silently turn outParam into semiOutParam.
                self.txn.lctx = frames[index].base.txn.lctx.clone();
                let expected = self.instantiate(&frames[index].expected)?;
                self.equations
                    .push(SourceEquation::selection(actual, expected));
                match self.flush(true) {
                    Ok(()) => {}
                    Err(error) if nonmatch(&error) => {
                        let failed = frames.pop().expect("current instance frame");
                        self.discard_instance_choices(failed, &mut history)?;
                        if frames.is_empty() {
                            return Ok(false);
                        }
                        self.retry_instance_choice(&mut frames, &mut history)?;
                        continue;
                    }
                    Err(error) => return Err(error),
                }
                value = self.instantiate(&value)?;
                for binder in frames[index].binders.iter().rev() {
                    self.tick()?;
                    let domain = self.instantiate(&binder.type_)?;
                    value = value
                        .abstract_fvar(&binder.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    value = Expr::lam(binder.user_name.clone(), domain, value, binder.binder_info);
                }
                let id = frames[index].goal.clone();
                let class = result_head(&frames[index].target)
                    .ok_or_else(|| failure(SourceInferenceError::InvalidInstanceBinder))?;
                self.txn
                    .assign_mvar(
                        id,
                        value,
                        AssignmentJustification::InstanceSearch { class_name: class },
                    )
                    .map_err(|error| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Metavariable(error),
                        )))
                    })?;
                let complete = frames.pop().expect("completed instance frame");
                if complete.resumable
                    && let Some(parent) = frames.last_mut()
                {
                    parent.children.push(history.len());
                    history.push(Some(complete));
                } else {
                    // A ground goal has a canonical first solution. Do not
                    // enumerate alternate dictionaries for already fixed inputs.
                    self.discard_instance_choices(complete, &mut history)?;
                }
                continue;
            }
            let frame = &mut frames[index];
            let Some(candidate) = frame.candidates.get(frame.cursor).cloned() else {
                let failed = frames.pop().expect("exhausted instance frame");
                self.discard_instance_choices(failed, &mut history)?;
                if frames.is_empty() {
                    return Ok(false);
                }
                self.retry_instance_choice(&mut frames, &mut history)?;
                continue;
            };
            frame.cursor += 1;
            attempts += 1;
            if attempts > MAX_CANDIDATE_ATTEMPTS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let spent = self.txn.budget.heartbeats_consumed;
            *self = frame.base.clone();
            self.txn.budget.heartbeats_consumed = spent;
            match self.expand_instance(&candidate, &frame.target) {
                Ok(expansion) => frame.chosen = expansion,
                Err(error) if nonmatch(&error) => {}
                Err(error) => return Err(error),
            }
        }
        Ok(true)
    }
}
