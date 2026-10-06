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

/// What a full search of the goal selects, on its own fresh budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Choice {
    /// The selected instance's head constant, under the answer's leading lambdas.
    Instance(Name),
    /// The search completed without an answer.
    NoAnswer,
    /// The search stopped without an answer: a budget or another refusal.
    Inconclusive,
}

/// Every global candidate of the goal's class, in registry order; the global
/// candidates the search tries, in the order it tries them; and what it selects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceGoalAudit {
    pub class: Name,
    pub candidates: Vec<CandidateAudit>,
    /// The goal frame's global candidates in try order (bead `fln-vm35`).
    pub order: Vec<Name>,
    pub choice: Choice,
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
    let mut search = context.clone();
    let Some(frame) = context.instance_frame(id.clone(), &registry, &ambient, None)? else {
        return Ok(None);
    };
    search.txn.budget.heartbeats_consumed = 0;
    let choice = match search.search_instance(id.clone(), &registry) {
        Ok(SearchResult::Solved) => match search.instantiate(&hole) {
            Ok(value) => answer_head(&value).map_or(Choice::Inconclusive, Choice::Instance),
            Err(_) => Choice::Inconclusive,
        },
        Ok(SearchResult::Failed) => Choice::NoAnswer,
        Ok(SearchResult::Stuck) => Choice::Inconclusive,
        Err(error) if nonmatch(&error) => Choice::NoAnswer,
        Err(_) => Choice::Inconclusive,
    };
    let class = result_head(&frame.target)
        .ok_or_else(|| failure(SourceInferenceError::InvalidInstanceBinder))?;
    let order: Vec<Name> = frame
        .candidates
        .iter()
        .filter_map(|candidate| match candidate {
            Candidate::Global(name) => Some(name.clone()),
            Candidate::Local(_) => None,
        })
        .collect();
    let admitted: BTreeSet<&Name> = order.iter().collect();
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
    Ok(Some(InstanceGoalAudit {
        class,
        candidates,
        order,
        choice,
    }))
}

/// The head constant of an answer, under its leading lambdas and metadata.
fn answer_head(value: &Expr) -> Option<Name> {
    let mut value = value;
    while let ExprNode::Lam { body, .. } | ExprNode::MData { expr: body, .. } = value.node() {
        value = body;
    }
    while let ExprNode::App { f, .. } = value.node() {
        value = f;
    }
    match value.node() {
        ExprNode::Const { name, .. } => Some(name.clone()),
        _ => None,
    }
}
