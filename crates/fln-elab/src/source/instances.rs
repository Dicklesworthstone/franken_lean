//! Transactional, bounded native instance search. Class inputs must be known
//! before search; ordinary locals qualify only when their type is a class.
//! Search uses an explicit stack and never turns exhaustion into "not found".
use super::*;
use crate::instances::{InstanceRegistry, InstanceRegistryError, result_head};

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
    next: usize,
}
struct Frame {
    goal: MVarId,
    target: Expr,
    binders: Vec<LocalDecl>,
    base: Context,
    candidates: Vec<Candidate>,
    cursor: usize,
    chosen: Option<Expansion>,
}

fn registry_error(error: InstanceRegistryError) -> NatDefinitionElabError {
    failure(SourceInferenceError::InstanceRegistry(error))
}
fn nonmatch(error: &NatDefinitionElabError) -> bool {
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
                let raw = self
                    .txn
                    .mvars
                    .get_decl(&id)
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?
                    .type_
                    .clone();
                let target = self.instantiate(&raw)?;
                if target.has_expr_mvar() || target.has_level_mvar() {
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
                        for (left, right) in suspended {
                            let left = trial.whnf(&left)?;
                            let right = trial.whnf(&right)?;
                            trial.equations.push((left, right));
                        }
                        *self = trial;
                    }
                    Ok(false) => {}
                    Err(error) => return Err(error),
                }
            }
            self.flush(false)?;
            if self.txn.mvars.assignments().len() == before {
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

    fn instance_frame(
        &mut self,
        goal: MVarId,
        registry: &InstanceRegistry,
        ambient: &LocalContext,
    ) -> Result<Frame, NatDefinitionElabError> {
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
        let class = result_head(&target)
            .filter(|c| registry.is_class(c))
            .ok_or_else(|| failure(SourceInferenceError::InvalidInstanceBinder))?;
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
        Ok(Frame {
            goal,
            target,
            binders,
            base: self.clone(),
            candidates,
            cursor: 0,
            chosen: None,
        })
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
        self.equations.push((term.type_, target.clone()));
        self.flush(true)?;
        Ok(Some(Expansion {
            value: term.value,
            subgoals,
            next: 0,
        }))
    }

    fn search_instance(
        &mut self,
        root: MVarId,
        registry: &InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        let ambient = self
            .txn
            .mvars
            .get_decl(&root)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?
            .lctx
            .clone();
        let first = self.instance_frame(root, registry, &ambient)?;
        let mut frames = vec![first];
        let mut attempts = 0usize;
        while !frames.is_empty() {
            self.tick()?;
            let index = frames.len() - 1;
            if let Some(expansion) = &mut frames[index].chosen {
                while expansion.next < expansion.subgoals.len()
                    && self
                        .txn
                        .mvars
                        .is_assigned(&expansion.subgoals[expansion.next])
                {
                    expansion.next += 1;
                }
                if let Some(id) = expansion.subgoals.get(expansion.next).cloned() {
                    let ty = self
                        .txn
                        .mvars
                        .get_decl(&id)
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?
                        .type_
                        .clone();
                    let ty = self.instantiate(&ty)?;
                    if ty.has_expr_mvar()
                        || ty.has_level_mvar()
                        || frames.iter().any(|frame| frame.target == ty)
                    {
                        frames[index].chosen = None;
                        continue;
                    }
                    let child = self.instance_frame(id, registry, &ambient)?;
                    if frames.iter().any(|frame| frame.target == child.target) {
                        frames[index].chosen = None;
                        continue;
                    }
                    if frames.len() >= MAX_SEARCH_DEPTH {
                        return Err(failure(SourceInferenceError::ResourceLimit));
                    }
                    frames.push(child);
                    continue;
                }
                let mut value = self.instantiate(&expansion.value)?;
                if value.has_expr_mvar() || value.has_level_mvar() {
                    frames[index].chosen = None;
                    continue;
                }
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
                frames.pop();
                continue;
            }
            let frame = &mut frames[index];
            let Some(candidate) = frame.candidates.get(frame.cursor).cloned() else {
                frames.pop();
                if let Some(parent) = frames.last_mut() {
                    parent.chosen = None;
                    continue;
                }
                return Ok(false);
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
