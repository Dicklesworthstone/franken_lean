//! Exact free-local and universe-parameter metadata for immutable, hole-free syntax DAGs.
//! Metavariable-bearing expressions keep the parent's ordered two-phase traversal.
//! This is syntax analysis only: assignments and local definitions are not read.
use super::*;
use std::sync::Arc;

// Small transient constraints cost less to scan directly. This only selects
// an optional optimization; every ineligible shape uses the original walk.
const MIN_DEPTH: u8 = 24;
const MAX_ENTRIES: usize = 16_384;
const MAX_IDENTITIES: usize = 65_536;

// Pin every allocation used as a key; equal hashes never identify expressions.
type Entry = (Expr, Arc<[FVarId]>, Arc<[Name]>);

#[derive(Default)]
pub(super) struct Cache {
    entries: HashMap<usize, Entry>,
    identities: usize,
}

fn collect_level_params(
    roots: &[&Level],
    seen_params: &mut HashSet<Name>,
    found_params: &mut Vec<Name>,
    meter: &mut Meter<'_>,
) -> Result<(), UnificationError> {
    let mut seen_levels = HashSet::new();
    let mut pending: Vec<&Level> = roots.iter().rev().copied().collect();
    while let Some(level) = pending.pop() {
        if !seen_levels.insert(std::ptr::from_ref(level)) {
            continue;
        }
        meter.node()?;
        if !level.has_param() {
            continue;
        }
        match level.view() {
            LevelView::Param(name) if seen_params.insert(name.clone()) => {
                found_params.push(name.clone());
            }
            LevelView::Succ(inner) => pending.push(inner),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            _ => {}
        }
    }
    Ok(())
}

impl Cache {
    #[cfg(test)]
    pub(super) fn scan(
        &mut self,
        root: &Expr,
        meter: &mut Meter<'_>,
    ) -> Result<Option<HashSet<FVarId>>, UnificationError> {
        if root.has_level_param() || !root.has_fvar() {
            return Ok(None);
        }
        Ok(self.scan_facts(root, meter)?.map(|facts| facts.fvars))
    }

    pub(super) fn scan_facts(
        &mut self,
        root: &Expr,
        meter: &mut Meter<'_>,
    ) -> Result<Option<Facts>, UnificationError> {
        if root.approx_depth() < MIN_DEPTH
            || !root.has_fvar()
            || root.has_expr_mvar()
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
            let empty = !expr.has_fvar()
                && !expr.has_expr_mvar()
                && !expr.has_level_param()
                && !expr.has_loose_bvars();
            if !exit && !empty {
                pending.push((expr.clone(), true));
                for child in children(&expr).into_iter().rev().flatten() {
                    pending.push((child.clone(), false));
                }
                continue;
            }
            let mut found = Vec::new();
            let mut seen = HashSet::new();
            let mut found_params = Vec::new();
            let mut seen_params = HashSet::new();
            match expr.node() {
                ExprNode::FVar { id } => {
                    meter.node()?;
                    found.push(id.clone());
                }
                ExprNode::Sort { level } if expr.has_level_param() => {
                    collect_level_params(&[level], &mut seen_params, &mut found_params, meter)?;
                }
                ExprNode::Const { levels, .. } if expr.has_level_param() => {
                    let level_refs: Vec<&Level> = levels.iter().collect();
                    collect_level_params(&level_refs, &mut seen_params, &mut found_params, meter)?;
                }
                _ if !empty => {
                    for child in children(&expr).into_iter().flatten() {
                        meter.tick()?;
                        let (_, locals, params) = staged
                            .get(&child.allocation_identity())
                            .or_else(|| self.entries.get(&child.allocation_identity()))
                            .ok_or(UnificationError::ExpressionScope)?;
                        for local in locals.iter() {
                            meter.node()?;
                            if seen.insert(local.clone()) {
                                found.push(local.clone());
                            }
                        }
                        for param in params.iter() {
                            meter.node()?;
                            if seen_params.insert(param.clone()) {
                                found_params.push(param.clone());
                            }
                        }
                    }
                }
                _ => {}
            }
            let entry_identities = found.len() + found_params.len();
            if self.entries.len() + staged.len() >= MAX_ENTRIES
                || self.identities + identities + entry_identities > MAX_IDENTITIES
            {
                // Capacity exhaustion only declines caching. The ordinary
                // traversal still runs, and this attempt refunds no work.
                return Ok(None);
            }
            identities += entry_identities;
            staged.insert(key, (expr, found.into(), found_params.into()));
        }
        let (_, locals, params) = staged
            .get(&root.allocation_identity())
            .or_else(|| self.entries.get(&root.allocation_identity()))
            .ok_or(UnificationError::ExpressionScope)?;
        let mut fvars = HashSet::new();
        for local in locals.iter() {
            meter.node()?;
            fvars.insert(local.clone());
        }
        let mut out_params = Vec::with_capacity(params.len());
        for param in params.iter() {
            meter.node()?;
            out_params.push(param.clone());
        }
        // Pay for publication before mutating the cache. Cancellation or a
        // work stop exposes neither partial metadata nor unpinned identities.
        for _ in 0..staged.len() {
            meter.tick()?;
        }
        self.entries.extend(staged);
        self.identities += identities;
        Ok(Some(Facts {
            fvars,
            params: out_params,
            uvars: Vec::new(),
        }))
    }
}

#[cfg(test)]
mod tests;
