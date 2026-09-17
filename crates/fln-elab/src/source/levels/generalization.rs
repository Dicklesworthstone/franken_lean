//! Close declaration-local universe holes only after inference has finished.
//!
//! Generalization introduces rigid parameters, never an assumption or a kernel
//! shortcut. The ordinary declaration checker still validates the resulting
//! polymorphic type and value together.

use super::super::*;
use fln_core::level::LevelView;
use std::collections::HashSet;

impl Context {
    /// Header term holes remain errors even when universe holes may be solved
    /// by the body. This deliberately does not weaken query finalization.
    pub(in crate::source) fn require_resolved_terms(
        &self,
        terms: &[Expr],
    ) -> Result<(), NatDefinitionElabError> {
        let mut holes = HashSet::new();
        for term in terms {
            holes.extend(self.txn.mvars.collect_mvars(term));
        }
        if holes.is_empty() {
            Ok(())
        } else {
            Err(failure(SourceInferenceError::UnresolvedHoles {
                count: holes.len(),
            }))
        }
    }

    /// Generalize only reachable, still-unassigned universes in fully inferred
    /// declaration roots (including parameter domains). Residual constraints,
    /// missing instances, and expression holes must be resolved first.
    pub(in crate::source) fn generalize_declaration_universes(
        &mut self,
        terms: &[Expr],
    ) -> Result<(), NatDefinitionElabError> {
        self.resolve_instances(true)?;
        self.flush(true)?;
        let mut roots = Vec::with_capacity(terms.len());
        for term in terms {
            roots.push(self.instantiate(term)?);
        }
        self.require_resolved_terms(&roots)?;

        let mut reserved: HashSet<Name> = self.level_params.iter().cloned().collect();
        reserved.extend(self.source_scope.universes.iter().cloned());
        let mut pending: Vec<_> = roots.iter().rev().collect();
        let mut seen = HashSet::new();
        let mut level_seen = HashSet::new();
        let mut hole_seen = HashSet::new();
        let mut holes = Vec::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            let mut levels = Vec::new();
            match expr.node() {
                ExprNode::Sort { level } => levels.push(level),
                ExprNode::Const { levels: args, .. } => levels.extend(args.iter().rev()),
                ExprNode::App { f, a } => pending.extend([a, f]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => pending.extend([body, binder_type]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => pending.extend([body, value, type_]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
                _ => {}
            }
            while let Some(level) = levels.pop() {
                self.tick()?;
                if !level_seen.insert(std::ptr::from_ref(level)) {
                    continue;
                }
                match level.view() {
                    LevelView::Param(name) => {
                        reserved.insert(name.clone());
                    }
                    LevelView::MVar(id) => {
                        if hole_seen.insert(id.clone()) {
                            holes.push(id.clone());
                        }
                    }
                    LevelView::Succ(inner) => levels.push(inner),
                    LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                        levels.extend([right, left]);
                    }
                    LevelView::Zero => {}
                }
            }
        }

        // Stage all names before publishing any generalization assignment.
        // Source-order traversal, not hash-map iteration or allocation IDs,
        // determines their order. Reserve names from all roots before choosing
        // one, including rigid parameters seen only in the declaration body.
        let mut assignments = Vec::with_capacity(holes.len());
        let mut next = 1_u64;
        for id in holes {
            let name = loop {
                self.tick()?;
                let spelling = format!("u_{next}");
                next = next
                    .checked_add(1)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                let name = Name::from_components([spelling.as_str()]);
                if reserved.insert(name.clone()) {
                    break name;
                }
            };
            assignments.push((id, name));
        }
        for (id, name) in assignments {
            self.txn.universes.assign(id, Level::param(name.clone()));
            self.level_params.push(name);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let env = crate::seed::bootstrap_nat_environment(budget).unwrap();
        Context::new(&env, budget)
    }

    #[test]
    fn shared_holes_receive_one_parameter_across_all_roots() {
        let mut context = context();
        let hole = context.level().unwrap();
        let sort = Expr::sort(hole.clone());
        let successor = Expr::sort(hole.succ().unwrap());
        context
            .generalize_declaration_universes(&[sort.clone(), successor.clone(), sort.clone()])
            .unwrap();
        let name = Name::from_components(["u_1"]);
        assert_eq!(context.level_params, vec![name.clone()]);
        assert_eq!(
            context.instantiate(&sort).unwrap(),
            Expr::sort(Level::param(name.clone()))
        );
        assert_eq!(
            context.instantiate(&successor).unwrap(),
            Expr::sort(Level::param(name).succ().unwrap())
        );
    }

    #[test]
    fn solved_and_unreachable_universes_are_not_generalized() {
        let mut context = context();
        let solved = context.level().unwrap();
        let unreachable = context.level().unwrap();
        let LevelView::MVar(id) = solved.view() else {
            panic!("fresh universe")
        };
        context.txn.universes.assign(id.clone(), Level::one());
        let root = Expr::sort(solved);
        context
            .generalize_declaration_universes(std::slice::from_ref(&root))
            .unwrap();
        assert!(context.level_params.is_empty());
        assert_eq!(context.instantiate(&root).unwrap(), Expr::sort(Level::one()));
        let LevelView::MVar(id) = unreachable.view() else {
            panic!("fresh universe")
        };
        assert!(!context.txn.universes.is_assigned(id));
    }

    #[test]
    fn parameters_in_later_roots_cannot_be_captured() {
        let mut context = context();
        let root = Expr::sort(context.level().unwrap());
        let rigid = Expr::sort(Level::param(Name::from_components(["u_1"])));
        context
            .generalize_declaration_universes(&[root.clone(), rigid.clone()])
            .unwrap();
        assert_eq!(context.level_params, vec![Name::from_components(["u_2"])]);
        assert_eq!(context.instantiate(&rigid).unwrap(), rigid);
        assert_eq!(
            context.instantiate(&root).unwrap(),
            Expr::sort(Level::param(Name::from_components(["u_2"])))
        );
    }

    #[test]
    fn expression_holes_are_not_disguised_as_polymorphism() {
        let mut context = context();
        let hole = context.hole(nat_const()).unwrap();
        assert!(matches!(
            context.generalize_declaration_universes(&[hole]),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::UnresolvedHoles { count: 1 }
            ))
        ));
        assert!(context.level_params.is_empty());
    }
}
