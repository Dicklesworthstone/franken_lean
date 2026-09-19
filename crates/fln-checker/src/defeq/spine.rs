//! Query-local, metered redex routing for application congruence.
//!
//! A reducible head may discard arguments, so decomposition must not precede
//! reduction. Caching the demand of each immutable arena node avoids rescanning
//! an n-argument spine n times. The cache records remaining arity, not a Boolean:
//! a partial recursor can become saturated at an enclosing application. It is a
//! routing hint only; the independent reducer still validates every rule.
use super::*;

#[derive(Clone, Copy)]
pub(super) enum Demand {
    Never,
    Always,
    Constructor,
    /// Additional applications needed before an eliminator demands its major.
    Arguments(u64),
}

#[derive(Clone, Copy)]
enum PathStep {
    Apply,
    Metadata,
    Projection,
}

impl SlowControl {
    pub(super) fn spine_head_reduces(
        &mut self,
        reference: DefEqTerm,
        sources: TermSources<'_>,
        context: &WhnfContext,
        include_recursors: bool,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<bool, SlowHalt> {
        let mut current = reference;
        let mut path = Vec::new();
        let mut demand = loop {
            if let Some(demand) = self.spines.get(&current) {
                break *demand;
            }
            // Previously this entire spine walk was unmetered and quadratic.
            // Each new cache entry now consumes the shared comparison budget
            // and polls cancellation. Failed queries publish no cached state.
            self.comparison(cancelled)?;
            let term = sources.source(current)?;
            let node =
                term.node(current.root)
                    .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                        location: current.location(),
                    }))?;
            let demand = match node {
                ExprNode::Apply { function, .. } => {
                    path.push((current, PathStep::Apply));
                    current = child(current, *function)?;
                    continue;
                }
                ExprNode::Metadata { expression, .. } => {
                    path.push((current, PathStep::Metadata));
                    current = child(current, *expression)?;
                    continue;
                }
                ExprNode::Projection { expression, .. } => {
                    path.push((current, PathStep::Projection));
                    current = child(current, *expression)?;
                    continue;
                }
                ExprNode::Lambda { .. } | ExprNode::Let { .. } => Demand::Always,
                ExprNode::StringLiteral(_) => Demand::Constructor,
                ExprNode::Free { name } => {
                    let mut found = false;
                    for binding in context.free_bindings() {
                        self.comparison(cancelled)?;
                        if binding.name() == name {
                            found = true;
                            break;
                        }
                    }
                    if found { Demand::Always } else { Demand::Never }
                }
                ExprNode::Constant { name, .. } => match context.constants().find(name) {
                    Some(entry) if entry.delta_body().is_some() => Demand::Always,
                    Some(entry)
                        if entry.kind() == crate::environment::ConstantKind::Constructor =>
                    {
                        Demand::Constructor
                    }
                    Some(entry) => match entry.quotient_kind() {
                        Some(crate::environment::QuotientKind::Lift) => Demand::Arguments(6),
                        Some(crate::environment::QuotientKind::Induction) => Demand::Arguments(5),
                        _ => match entry.recursor_metadata() {
                            Some(rec) => Demand::Arguments(
                                u64::from(rec.num_parameters())
                                    + u64::from(rec.num_motives())
                                    + u64::from(rec.num_minors())
                                    + u64::from(rec.num_indices())
                                    + 1,
                            ),
                            None => Demand::Never,
                        },
                    },
                    None => Demand::Never,
                },
                _ => Demand::Never,
            };
            self.spines.insert(current, demand);
            break demand;
        };
        for (parent, step) in path.into_iter().rev() {
            // This insertion was charged on descent, but even cache completion
            // must remain cancellable for a deep spine.
            self.poll(cancelled)?;
            demand = match step {
                PathStep::Apply => match demand {
                    Demand::Arguments(remaining) => Demand::Arguments(remaining.saturating_sub(1)),
                    other => other,
                },
                PathStep::Metadata => demand,
                PathStep::Projection => match demand {
                    Demand::Always | Demand::Constructor => Demand::Always,
                    Demand::Arguments(0) => Demand::Arguments(0),
                    _ => Demand::Never,
                },
            };
            self.spines.insert(parent, demand);
        }
        Ok(matches!(demand, Demand::Always)
            || (include_recursors && matches!(demand, Demand::Arguments(0))))
    }
}
