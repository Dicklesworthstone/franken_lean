//! A read-only audit of the discrimination-tree filter (bead `fln-52qv`).
//!
//! For one instance goal: every global candidate of its class, whether the
//! pin's discrimination tree admits it, and whether the search's selection step
//! applies it. The filter is correct only if every candidate that applies is
//! admitted. This admits nothing and changes no environment.
use super::*;
use std::collections::BTreeSet;

/// What the search's selection step does with one candidate: the single
/// strict match of the goal against the instance's type ([`Context::expand_instance`]),
/// before any prerequisite is searched.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Selection {
    Applies,
    Fails,
    /// The step stopped without an answer, on its own fresh budget.
    Inconclusive,
}

/// One global candidate of an audited goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CandidateAudit {
    pub declaration: Name,
    /// The discrimination tree may return it for the goal.
    pub admitted: bool,
    pub selection: Selection,
}

/// Every global candidate of the goal's class, in search order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceGoalAudit {
    pub class: Name,
    pub candidates: Vec<CandidateAudit>,
}

/// Audit `goal`, a closed instance type whose leading binders the search opens,
/// against `environment`'s instances, each candidate on a fresh default budget.
/// `None` when the search would not start on it (an input is still unknown).
pub fn audit_instance_goal(
    environment: &Environment,
    goal: &Expr,
    kernel: Budget,
) -> Result<Option<InstanceGoalAudit>, NatDefinitionElabError> {
    let mut context = Context::new(environment, kernel);
    let registry = InstanceRegistry::read(environment).map_err(registry_error)?;
    let hole = context.hole(goal.clone())?;
    let ExprNode::MVar { id } = hole.node() else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let ambient = context.txn.lctx.clone();
    let Some(frame) = context.instance_frame(id.clone(), &registry, &ambient, None)? else {
        return Ok(None);
    };
    let class = result_head(&frame.target)
        .ok_or_else(|| failure(SourceInferenceError::InvalidInstanceBinder))?;
    let admitted: BTreeSet<&Name> = frame
        .candidates
        .iter()
        .filter_map(|candidate| match candidate {
            Candidate::Global(name) => Some(name),
            Candidate::Local(_) => None,
        })
        .collect();
    let mut candidates = Vec::new();
    for row in registry.candidates(&class) {
        let mut trial = frame.base.clone();
        trial.txn.budget.heartbeats_consumed = 0;
        let candidate = Candidate::Global(row.declaration.clone());
        let selection = match trial.expand_instance(&candidate, &frame.target, false, &registry) {
            Ok(Some(_)) => Selection::Applies,
            Ok(None) => Selection::Fails,
            Err(error) if nonmatch(&error) => Selection::Fails,
            Err(_) => Selection::Inconclusive,
        };
        candidates.push(CandidateAudit {
            declaration: row.declaration.clone(),
            admitted: admitted.contains(&row.declaration),
            selection,
        });
    }
    Ok(Some(InstanceGoalAudit { class, candidates }))
}
