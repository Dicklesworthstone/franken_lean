//! Lexical lifetimes for quoted `local macro_rules` without snapshotting globals.
//!
//! Lean.ScopedEnvExtension adds global entries to every scope, but local entries
//! only to the current one. Mark each clause instead of restoring an old map:
//! global registrations made inside a section must survive its closing `end`.
use super::*;
use std::borrow::Cow;

type Depths = Vec<Option<usize>>;

impl FileGrammar {
    pub(super) fn prepended_rule_depths(
        &self,
        kind: &Name,
        previous: usize,
        added: usize,
        local: bool,
    ) -> Result<Option<Depths>, &'static str> {
        let older = self.local_rule_depths.get(kind);
        if !local && older.is_none() {
            return Ok(None);
        }
        if older.is_some_and(|depths| depths.len() != previous) {
            return Err("native macro locality does not match its clause chain");
        }
        let mut depths = vec![local.then_some(self.scopes.len()); added];
        match older {
            Some(older) => depths.extend(older.iter().copied()),
            None => depths.resize(added + previous, None),
        }
        Ok(Some(depths))
    }

    /// Imports are inserted after this file's own prefix, not ahead of it.
    /// Prepare the matching metadata before import_native changes any state.
    pub(super) fn imported_rule_depths(
        &self,
        kind: &Name,
        previous: usize,
        own: usize,
        added: usize,
    ) -> Result<Option<Depths>, &'static str> {
        let Some(depths) = self.local_rule_depths.get(kind) else {
            return Ok(None);
        };
        if depths.len() != previous || own > previous {
            return Err("native macro locality does not match its import prefix");
        }
        let mut result = depths[..own].to_vec();
        result.resize(own + added, None);
        result.extend_from_slice(&depths[own..]);
        Ok(Some(result))
    }

    /// Local clauses at file scope are still local: strip them even when no
    /// explicit `end` has occurred. Imports and global clauses keep their order.
    pub(super) fn exportable_rule<'a>(
        &self,
        kind: &Name,
        rule: &'a NotationRule,
    ) -> Result<Option<Cow<'a, NotationRule>>, &'static str> {
        let Some(depths) = self.local_rule_depths.get(kind) else {
            return Ok(Some(Cow::Borrowed(rule)));
        };
        if depths.len() != rule.cases().count() {
            return Err("native macro locality does not match its exported chain");
        }
        Ok(selected(rule, depths, |depth| depth.is_none()).map(Cow::Owned))
    }

    /// Already-built grammars retain their Arc snapshot. Only subsequent
    /// commands see the expired locals, including after a cached scope reentry.
    pub(super) fn expire_local_rules(&mut self) {
        let depth = self.scopes.len();
        let old = std::mem::take(&mut self.local_rule_depths);
        for (kind, depths) in old {
            let Some(rule) = self.rules.get(&kind) else {
                continue;
            };
            if depths.len() != rule.cases().count() {
                self.native_export_refusal = Some("native macro locality lost its clause chain");
                Arc::make_mut(&mut self.rules).remove(&kind);
                self.generation += 1;
                continue;
            }
            if !depths.iter().any(|d| d.is_some_and(|d| d > depth)) {
                self.local_rule_depths.insert(kind, depths);
                continue;
            }
            let keep = |d: &Option<usize>| d.is_none_or(|d| d <= depth);
            let remaining = selected(rule, &depths, keep);
            if let Some(scopes) = self.rule_scopes.get_mut(&kind) {
                if scopes.len() != depths.len() {
                    self.native_export_refusal =
                        Some("native scoped macro metadata lost its clause chain");
                    Arc::make_mut(&mut self.rules).remove(&kind);
                    self.generation += 1;
                    continue;
                }
                *scopes = scopes
                    .iter()
                    .zip(&depths)
                    .filter(|(_, depth)| keep(depth))
                    .map(|(scope, _)| scope.clone())
                    .collect();
            }
            let retained: Depths = depths.into_iter().filter(keep).collect();
            let rules = Arc::make_mut(&mut self.rules);
            match remaining {
                Some(rule) => {
                    rules.insert(kind.clone(), Arc::new(rule));
                }
                None => {
                    rules.remove(&kind);
                }
            }
            if retained.iter().any(Option::is_some) {
                self.local_rule_depths.insert(kind, retained);
            }
            self.generation += 1;
        }
    }
}

fn selected(
    rule: &NotationRule,
    depths: &[Option<usize>],
    keep: impl Fn(&Option<usize>) -> bool,
) -> Option<NotationRule> {
    let mut cases = rule
        .cases()
        .zip(depths)
        .filter(|(_, depth)| keep(depth))
        .map(|(rule, _)| modules::flat_case(rule));
    let mut head = cases.next()?;
    head.fallbacks = cases.collect();
    Some(head)
}

#[cfg(test)]
mod tests;
