//! Native associative normalization from the operation's checked class instances.
//!
//! The pin's AC tactic requires associativity, and additionally uses commutativity,
//! idempotence and two-sided identities when instance search supplies them. Its
//! atoms use `Expr.lt`, not simp's `acLt`. The shared AC reflection backend builds
//! each operator's checked equality; this module lifts it through exact permitted
//! occurrences and scoped binders. Traversals are iterative and charged. No
//! ordinary simp theorem or operation-specific arithmetic rule is selected.

use super::*;

mod locations;

const MAX_AC_NODES: usize = 4096;

/// A selected application argument is an occurrence, not every equal expression
/// in the target. In particular a fixed dependent index may equal a later,
/// rewritable argument. A global replacement would construct an ill-typed motive.
#[derive(Clone, Copy)]
enum Edge {
    Argument(usize),
    Function,
    Body,
    Domain,
    Inner,
}

struct Path {
    parent: Option<usize>,
    term: Expr,
    edge: Edge,
}

fn binary(term: &Expr) -> Option<(&Expr, &Expr, &Expr)> {
    let ExprNode::App { f, a: right } = term.node() else {
        return None;
    };
    let ExprNode::App { f: op, a: left } = f.node() else {
        return None;
    };
    Some((op, left, right))
}

fn named(path: &str) -> Name {
    Name::from_components(path.split('.'))
}

impl Context {
    /// Reusable AC-only normalization for the tactic and its location frontend.
    /// The optional proof has type `expression = normalized`; definitional
    /// changes need no equality witness. No ordinary simp theorem is selected.
    pub(in crate::source) fn ac_normalize_expression(
        &mut self,
        expression: &Expr,
    ) -> Result<(Expr, Option<Expr>), NatDefinitionElabError> {
        // The pin uses Simp.neutralConfig: beta/zeta/iota/projection reduction
        // must not expose additional AC operations. Ordinary simp's expression
        // loop performs those reductions, so this loop selects only AC evidence.
        let original = self.instantiate(expression)?;
        // Source type ascriptions are represented by synthetic anonymous lets.
        // The pin has no such wrapper; removing it is definitional and must not
        // expose the bodies of genuine source lets, which neutralConfig keeps.
        let original = self.without_source_ascriptions(&original)?;
        let mut current = original.clone();
        let mut proof = None;
        let mut steps = 0usize;
        loop {
            self.tick()?;
            let evidence = match self.simp_ac_evidence(&current)? {
                Some(evidence) => Some(evidence),
                None => self.simp_binder_rule(&current, &SimpRule::Ac, &[])?,
            };
            let Some(evidence) = evidence else { break };
            if steps >= MAX_SIMPLIFICATION_STEPS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            steps += 1;
            let (level, domain, _, next) = equality_target(&evidence.type_)
                .ok_or_else(|| error(TacticError::ExpectedEquality))?;
            if self.rewrite_same(&current, &next)? {
                return Err(error(TacticError::SimplificationCycle));
            }
            proof = Some(match proof {
                None => evidence.value,
                Some(previous) => app(
                    Expr::const_(named("Eq.trans"), vec![level]),
                    [
                        domain,
                        original.clone(),
                        current,
                        next.clone(),
                        previous,
                        evidence.value,
                    ],
                ),
            });
            current = next;
        }
        Ok((current, proof))
    }

    pub(in crate::source) fn ac_rfl_proof_goal(
        &mut self,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let original = self.instantiate(&goal.target)?;
        let (normalized, evidence) = self.ac_normalize_expression(&original)?;
        if let Some(evidence) = evidence {
            let evidence = Typed {
                value: evidence,
                type_: equality::equation(
                    Level::one(),
                    Expr::sort(Level::zero()),
                    original.clone(),
                    normalized,
                ),
            };
            let (child, value) =
                self.rewrite_transport(&goal, evidence, &original, false, false)?;
            // `MVarId.refl`, used by the pin's ac_rfl, only closes Eq. General
            // rfl also accepts HEq/Iff and would widen this tactic's contract.
            self.eq_refl_proof_goal(child, false)?;
            self.close_proof_goal(goal, value)
        } else {
            self.eq_refl_proof_goal(
                ProofGoal {
                    target: normalized,
                    ..goal
                },
                false,
            )
        }
    }

    fn ac_normalization_children(
        &mut self,
        term: &Expr,
    ) -> Result<Vec<(Expr, Edge)>, NatDefinitionElabError> {
        Ok(match term.node() {
            ExprNode::App { .. } => {
                let mut head = term;
                let mut args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    self.tick()?;
                    args.push(a);
                    head = f;
                }
                args.reverse();
                let policy = self.simp_application_argument_kinds(head, args.len());
                let mut children = Vec::new();
                if policy.is_none() {
                    children.push((head.clone(), Edge::Function));
                }
                for (index, arg) in args.into_iter().enumerate() {
                    self.tick()?;
                    if policy
                        .as_ref()
                        .is_none_or(|policy| policy.get(index).copied().unwrap_or(true))
                    {
                        children.push((arg.clone(), Edge::Argument(index)));
                    }
                }
                children
            }
            ExprNode::Lam { body, .. } => vec![(body.clone(), Edge::Body)],
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let mut children = Vec::new();
                if !body.has_loose_bvar(0) {
                    children.push((binder_type.clone(), Edge::Domain));
                }
                children.push((body.clone(), Edge::Body));
                children
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                vec![(expr.clone(), Edge::Inner)]
            }
            // neutralConfig does not expose a let's body by zeta reduction.
            _ => Vec::new(),
        })
    }

    fn ac_replace_child(
        &mut self,
        path: &Path,
        replacement: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        Ok(match (path.term.node(), path.edge) {
            (ExprNode::App { .. }, Edge::Argument(_) | Edge::Function) => {
                let mut head = &path.term;
                let mut args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    self.tick()?;
                    args.push(a.clone());
                    head = f;
                }
                args.reverse();
                let head = if let Edge::Argument(index) = path.edge {
                    *args
                        .get_mut(index)
                        .ok_or_else(|| failure(SourceInferenceError::Scope))? = replacement;
                    head.clone()
                } else {
                    replacement
                };
                args.into_iter().fold(head, Expr::app)
            }
            (
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    binder_info,
                    ..
                },
                Edge::Body,
            ) => Expr::lam(
                binder_name.clone(),
                binder_type.clone(),
                replacement,
                *binder_info,
            ),
            (
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                },
                Edge::Body | Edge::Domain,
            ) => {
                let (domain, body) = if matches!(path.edge, Edge::Domain) {
                    (replacement, body.clone())
                } else {
                    (binder_type.clone(), replacement)
                };
                Expr::forall_e(binder_name.clone(), domain, body, *binder_info)
            }
            (ExprNode::MData { data, .. }, Edge::Inner) => Expr::mdata(data.clone(), replacement),
            (
                ExprNode::Proj {
                    struct_name, idx, ..
                },
                Edge::Inner,
            ) => Expr::proj(struct_name.clone(), *idx, replacement),
            _ => return Err(failure(SourceInferenceError::Scope)),
        })
    }

    fn ac_lift_path(
        &mut self,
        paths: &[Path],
        mut path: Option<usize>,
        mut evidence: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        while let Some(index) = path {
            self.tick()?;
            let frame = &paths[index];
            let (_, domain, _, right) = equality_target(&evidence.type_)
                .ok_or_else(|| error(TacticError::ExpectedEquality))?;
            let marker = self.equality_local(domain.clone())?;
            let template = self.ac_replace_child(frame, Expr::fvar(marker.id.clone()))?;
            let selector = self.close_equality_binder(&marker, template, true)?;
            let result_type = self
                .known_type(&frame.term)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let sort = self
                .known_type(&result_type)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let level = self.sort_level(&Typed {
                value: result_type.clone(),
                type_: sort,
            })?;
            let selector_type = self
                .known_type(&selector)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let expected = Expr::forall_e(
                Name::anonymous(),
                domain,
                result_type.clone(),
                BinderInfo::Default,
            );
            if !self.proof_types_match(&selector_type, &expected)? {
                return Err(error(TacticError::ApplyMismatch));
            }
            let next = self.ac_replace_child(frame, right)?;
            let lifted = self.selector_congruence(&evidence, &result_type, &level, &selector)?;
            evidence = Typed {
                value: lifted.value,
                type_: equality::equation(level, result_type, frame.term.clone(), next),
            };
            path = frame.parent;
        }
        Ok(evidence)
    }

    /// A post-order AC step, lifted along its exact permitted occurrence path.
    /// The returned equality covers the WHOLE target so later Eq.rec transport
    /// cannot also replace equal expressions in fixed dependent arguments.
    pub(super) fn simp_ac_evidence(
        &mut self,
        target: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let mut work = vec![(target.clone(), None, None::<Expr>, false)];
        let mut paths = Vec::new();
        let mut nodes = 0usize;
        while let Some((term, path, parent_op, exit)) = work.pop() {
            self.tick()?;
            if term.has_loose_bvars() {
                continue;
            }
            if !exit {
                nodes += 1;
                if nodes > MAX_AC_NODES {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let op = binary(&term).map(|(op, _, _)| op.clone());
                work.push((term.clone(), path, parent_op, true));
                for (child, edge) in self.ac_normalization_children(&term)?.into_iter().rev() {
                    let index = paths.len();
                    paths.push(Path {
                        parent: path,
                        term: term.clone(),
                        edge,
                    });
                    work.push((child, Some(index), op.clone(), false));
                }
                continue;
            }
            let Some((op, _, _)) = binary(&term) else {
                continue;
            };
            if let Some(parent_op) = parent_op
                && self.proof_types_match(op, &parent_op)?
            {
                continue;
            }
            if let Some(evidence) = self.ac_operator_evidence(&term)? {
                return self.ac_lift_path(&paths, path, evidence).map(Some);
            }
        }
        Ok(None)
    }
}
