//! Exact free-local metadata for immutable, universe-free syntax DAGs.
//! Universe-bearing expressions keep the parent's ordered two-phase traversal.
//! This is syntax analysis only: assignments and local definitions are not read.
use super::*;
use std::sync::Arc;

// Small transient constraints cost less to scan directly. This only selects
// an optional optimization; every ineligible shape uses the original walk.
const MIN_DEPTH: u8 = 24;
const MAX_ENTRIES: usize = 16_384;
const MAX_IDENTITIES: usize = 65_536;

// Pin every allocation used as a key; equal hashes never identify expressions.
type Entry = (Expr, Arc<[FVarId]>);

#[derive(Default)]
pub(super) struct Cache {
    entries: HashMap<usize, Entry>,
    identities: usize,
}

impl Cache {
    pub(super) fn scan(
        &mut self,
        root: &Expr,
        meter: &mut Meter<'_>,
    ) -> Result<Option<HashSet<FVarId>>, UnificationError> {
        if root.approx_depth() < MIN_DEPTH
            || !root.has_fvar()
            || root.has_expr_mvar()
            || root.has_level_param()
            || root.has_level_mvar()
            || matches!(root.node(), ExprNode::FVar { .. })
        {
            return Ok(None);
        }
        if self.entries.len() >= MAX_ENTRIES || self.identities >= MAX_IDENTITIES {
            return Ok(None);
        }
        let mut staged: HashMap<usize, Entry> = HashMap::new();
        let mut identities = 0usize;
        let mut pending = vec![(root.clone(), false)];
        while let Some((expr, exit)) = pending.pop() {
            meter.node()?;
            let key = expr.allocation_identity();
            if self.entries.contains_key(&key) || staged.contains_key(&key) {
                continue;
            }
            let empty = !expr.has_fvar() && !expr.has_expr_mvar() && !expr.has_loose_bvars();
            if !exit && !empty {
                pending.push((expr.clone(), true));
                for child in children(&expr).into_iter().rev().flatten() {
                    pending.push((child.clone(), false));
                }
                continue;
            }
            let mut found = Vec::new();
            let mut seen = HashSet::new();
            if let ExprNode::FVar { id } = expr.node() {
                meter.node()?;
                found.push(id.clone());
            } else if !empty {
                for child in children(&expr).into_iter().flatten() {
                    meter.tick()?;
                    let (_, locals) = staged
                        .get(&child.allocation_identity())
                        .or_else(|| self.entries.get(&child.allocation_identity()))
                        .ok_or(UnificationError::ExpressionScope)?;
                    for local in locals.iter() {
                        meter.node()?;
                        if seen.insert(local.clone()) {
                            found.push(local.clone());
                        }
                    }
                }
            }
            if self.entries.len() + staged.len() >= MAX_ENTRIES
                || self.identities + identities + found.len() > MAX_IDENTITIES
            {
                // Capacity exhaustion only declines caching. The ordinary
                // traversal still runs, and this attempt refunds no work.
                return Ok(None);
            }
            identities += found.len();
            staged.insert(key, (expr, found.into()));
        }
        let (_, locals) = staged
            .get(&root.allocation_identity())
            .or_else(|| self.entries.get(&root.allocation_identity()))
            .ok_or(UnificationError::ExpressionScope)?;
        let mut result = HashSet::new();
        for local in locals.iter() {
            meter.node()?;
            result.insert(local.clone());
        }
        // Pay for publication before mutating the cache. Cancellation or a
        // work stop exposes neither partial metadata nor unpinned identities.
        for _ in 0..staged.len() {
            meter.tick()?;
        }
        self.entries.extend(staged);
        self.identities += identities;
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests;
