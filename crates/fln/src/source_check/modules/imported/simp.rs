//! Replay the supported default simp entries from council-checked artifacts.
//! The foreign proof is already oriented. Never replace it by its erase origin,
//! infer authority from its rfl flag, or execute a Reference initializer.
use super::*;
use fln_elab::source::scope::simp::{self as native, ImportedSimpRule, SimpSetError};

pub(super) struct Replay<'a> {
    pub checked: &'a CheckedOleanSet,
    pub origin: &'a Environment,
    pub order: &'a [usize],
    pub limits: &'a SourceOleanImportLimits,
    pub cancellation: Option<&'a dyn CancellationProbe>,
}

impl Replay<'_> {
    pub(super) fn activate(
        &self,
        env: &Environment,
        rows: Vec<metadata::SimpEntry>,
        reports: &mut [SourceMetadataReport],
        journals: &mut BTreeMap<Name, (Environment, Environment)>,
    ) -> Result<Outcome<Environment>> {
        macro_rules! cancelled {
            () => {
                if self
                    .cancellation
                    .is_some_and(CancellationProbe::is_cancelled)
                {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "source-olean/simp",
                    )));
                }
            };
        }
        cancelled!();
        let expected = reports.iter().try_fold(0usize, |sum, report| {
            sum.checked_add(report.simps)
                .ok_or(SourceOleanImportError::Limit("simp entry inventory"))
        })?;
        if expected != rows.len() || self.order.len() != reports.len() {
            return Err(SourceOleanImportError::Internal(
                "decoded simp entries escaped their module inventory",
            ));
        }
        let mut scopes = ScopeIndex::new(self.checked, &rows, self.limits.metadata.max_objects)?;
        cancelled!();
        let mut rows = rows.into_iter();
        let mut operations = Vec::new();
        operations
            .try_reserve(expected)
            .map_err(|_| SourceOleanImportError::Limit("simp operation allocation"))?;
        for (&index, report) in self.order.iter().zip(reports) {
            cancelled!();
            if report.simps == 0 {
                continue;
            }
            let reachable = scopes.closure(index)?;
            let start = operations.len();
            for _ in 0..report.simps {
                cancelled!();
                let row = rows.next().ok_or(SourceOleanImportError::Internal(
                    "simp count changed during replay",
                ))?;
                scopes.spend(1)?;
                scopes.authorize_entry(self.origin, env, &reachable, &report.module, &row)?;
                let (operation, deferred) = select(env, &report.module, &row)?;
                report.deferred_simps += usize::from(deferred);
                if let Some(operation) = operation {
                    report.activated_simps += usize::from(!deferred);
                    operations.push(operation);
                }
            }
            if report.deferred_simps != 0 {
                report.uninterpreted.push(extension_name());
            }
            let (_, after) =
                journals
                    .get_mut(&report.module)
                    .ok_or(SourceOleanImportError::Internal(
                        "simp module lost its metadata snapshots",
                    ))?;
            // Only the appended suffix is replayed by ImportContexts. Record
            // every operation, including redundant registrations and erasures,
            // so intervening source modules do not change what a suffix means.
            // The class/instance registrar never reads this independent journal.
            *after = native::import_rules(after, &operations[start..])
                .map_err(|error| registry_error(&report.module, error))?;
        }
        if rows.next().is_some() {
            return Err(SourceOleanImportError::Internal("unconsumed simp entries"));
        }
        cancelled!();
        // Replay the ordered union once, without restarting the kept class and
        // instance activation for every module. Readback validates the existing
        // native journal even when the new closure contains no simp entries.
        let next = native::import_rules(env, &operations)
            .map_err(|error| registry_error(&extension_name(), error))?;
        cancelled!();
        Ok(Outcome::Complete(next))
    }
}

fn extension_name() -> Name {
    Name::from_components(metadata::SIMP_EXTENSION.split('.'))
}

fn origin_of(row: &metadata::SimpEntry) -> &Name {
    match &row.kind {
        metadata::SimpKind::Theorem(theorem) => &theorem.origin,
        metadata::SimpKind::Unfold(name)
        | metadata::SimpKind::UnfoldTheorems {
            declaration: name, ..
        } => name,
    }
}

/// Supported entries are global, forward, post-phase, non-permutation rules.
/// Compact constants omit all universes; explicit constants must be generic,
/// never specialized or reordered applications of the declaration's universes.
fn candidate(env: &Environment, row: &metadata::SimpEntry) -> Option<ImportedSimpRule> {
    if row.scope.is_some() {
        return None;
    }
    match &row.kind {
        metadata::SimpKind::Theorem(theorem)
            if theorem.post && !theorem.origin_reverse && !theorem.permutation =>
        {
            let ExprNode::Const { name, levels } = theorem.proof.node() else {
                return None;
            };
            let info = env.find(name)?.constant_val();
            let compact = levels.is_empty() && theorem.level_params.is_empty();
            let expanded = levels.len() == info.level_params.len()
                && theorem.level_params.len() == info.level_params.len()
                && levels
                    .iter()
                    .zip(&theorem.level_params)
                    .all(|(level, name)| *level == Level::param(name.clone()));
            if !compact && !expanded {
                return None;
            }
            Some(ImportedSimpRule::Proof {
                origin: theorem.origin.clone(),
                proof: name.clone(),
                priority: theorem.priority,
            })
        }
        metadata::SimpKind::Unfold(declaration) => Some(ImportedSimpRule::Unfold {
            declaration: declaration.clone(),
        }),
        metadata::SimpKind::UnfoldTheorems {
            declaration,
            theorems,
        } => Some(ImportedSimpRule::UnfoldTheorems {
            declaration: declaration.clone(),
            theorems: theorems.clone(),
        }),
        _ => None,
    }
}

fn select(
    env: &Environment,
    module: &Name,
    row: &metadata::SimpEntry,
) -> Result<(Option<ImportedSimpRule>, bool)> {
    if !env.contains(origin_of(row)) {
        return Err(registry_error(
            module,
            SimpSetError::UnknownDeclaration(origin_of(row).clone()),
        ));
    }
    if let metadata::SimpKind::Theorem(theorem) = &row.kind
        && let ExprNode::Const { name, .. } = theorem.proof.node()
        && !env.contains(name)
    {
        return Err(registry_error(
            module,
            SimpSetError::UnknownDeclaration(name.clone()),
        ));
    }
    if let metadata::SimpKind::UnfoldTheorems { theorems, .. } = &row.kind {
        for theorem in theorems {
            if !env.contains(theorem) {
                return Err(registry_error(
                    module,
                    SimpSetError::UnknownDeclaration(theorem.clone()),
                ));
            }
        }
    }
    if let Some(operation) = candidate(env, row) {
        match operation.validate(env) {
            Ok(()) => return Ok((Some(operation), false)),
            Err(SimpSetError::UnsupportedDeclaration(_)) => {}
            Err(error) => return Err(registry_error(module, error)),
        }
    }
    // A deferred global origin must not leave a stale forward selection active.
    // In particular an imported reverse rule withdraws its earlier converse.
    // Scoped entries are dormant and must not erase any global registration.
    let erase = row.scope.is_none().then(|| ImportedSimpRule::Erase {
        declaration: origin_of(row).clone(),
    });
    if let Some(operation) = &erase {
        operation
            .validate(env)
            .map_err(|error| registry_error(module, error))?;
    }
    Ok((erase, true))
}

fn registry_error(module: &Name, error: SimpSetError) -> SourceOleanImportError {
    let (declaration, reason) = match error {
        SimpSetError::Limit => return SourceOleanImportError::Limit("native simp journal"),
        SimpSetError::Malformed => (extension_name(), "malformed native simp journal"),
        SimpSetError::UnknownDeclaration(name) => (name, "simp names no admitted declaration"),
        SimpSetError::UnsupportedDeclaration(name) => (name, "unsupported native simp declaration"),
    };
    SourceOleanImportError::Metadata {
        module: module.clone(),
        declaration,
        reason,
    }
}

/// Index only names actually referenced by simp metadata. A root's sibling is
/// not in its import world merely because the council checked both together.
struct ScopeIndex {
    parents: Vec<Vec<usize>>,
    owners: BTreeMap<Name, Vec<usize>>,
    /// Each module's import closure, itself included, computed once from its
    /// parents' closures. A fresh walk per simp module made the pinned Std
    /// closure (965 modules) charge 1,210,820 work units, quadratic in modules.
    closures: Vec<Option<Reach>>,
    work_left: u64,
}

/// A set of module indices, one bit per module of the checked set.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Reach(Vec<u64>);

impl Reach {
    fn contains(&self, index: usize) -> bool {
        self.0
            .get(index / 64)
            .is_some_and(|word| word & (1 << (index % 64)) != 0)
    }
}

impl ScopeIndex {
    fn new(
        checked: &CheckedOleanSet,
        rows: &[metadata::SimpEntry],
        work_left: u64,
    ) -> Result<Self> {
        let mut result = Self {
            parents: Vec::new(),
            owners: BTreeMap::new(),
            closures: Vec::new(),
            work_left,
        };
        if rows.is_empty() {
            return Ok(result);
        }
        for row in rows {
            result.spend(1)?;
            result.owners.entry(origin_of(row).clone()).or_default();
            if let metadata::SimpKind::Theorem(theorem) = &row.kind
                && let ExprNode::Const { name, .. } = theorem.proof.node()
            {
                result.owners.entry(name.clone()).or_default();
            }
            if let metadata::SimpKind::UnfoldTheorems { theorems, .. } = &row.kind {
                for theorem in theorems {
                    result.spend(1)?;
                    result.owners.entry(theorem.clone()).or_default();
                }
            }
        }
        result.spend(checked.modules.len() as u64)?;
        let indices: BTreeMap<_, _> = checked
            .modules
            .iter()
            .enumerate()
            .map(|(index, module)| (&module.name, index))
            .collect();
        for (index, module) in checked.modules.iter().enumerate() {
            let mut parents = Vec::new();
            for import in &module.decoded.module.imports {
                result.spend(1)?;
                parents.push(*indices.get(&import.module).ok_or(
                    SourceOleanImportError::Internal("simp import graph is incomplete"),
                )?);
            }
            result.parents.push(parents);
            for constant in &module.decoded.constants {
                result.spend(1)?;
                if let Some(owners) = result.owners.get_mut(constant.name()) {
                    owners.push(index);
                }
            }
        }
        Ok(result)
    }

    fn spend(&mut self, amount: u64) -> Result<()> {
        self.work_left = self
            .work_left
            .checked_sub(amount)
            .ok_or(SourceOleanImportError::Limit("simp import-closure work"))?;
        Ok(())
    }

    /// The import closure of `module`, itself included. A module's closure is
    /// the union of its parents' closures, so each module is expanded once
    /// however many simp modules import it. Work is charged before every
    /// allocation and covers each word stored, so the budget bounds memory too.
    fn closure(&mut self, module: usize) -> Result<Reach> {
        const OUTSIDE: SourceOleanImportError =
            SourceOleanImportError::Internal("simp module index is outside its graph");
        const CYCLIC: SourceOleanImportError =
            SourceOleanImportError::Internal("simp import graph is cyclic");
        let modules = self.parents.len();
        let words = modules.div_ceil(64);
        if self.closures.len() < modules {
            self.closures
                .try_reserve_exact(modules - self.closures.len())
                .map_err(|_| SourceOleanImportError::Limit("simp import-closure allocation"))?;
            self.closures.resize(modules, None);
        }
        // Postorder over modules not yet closed. Popping a module that is still
        // open, or closing one whose parent is not closed, means a cycle.
        let mut open = BTreeSet::new();
        let mut pending = vec![(module, false)];
        while let Some((index, expanded)) = pending.pop() {
            if self.closures.get(index).ok_or(OUTSIDE)?.is_some() {
                continue;
            }
            let count = self.parents[index].len();
            if !expanded {
                if !open.insert(index) {
                    return Err(CYCLIC);
                }
                self.spend(1 + count as u64)?;
                pending
                    .try_reserve(count + 1)
                    .map_err(|_| SourceOleanImportError::Limit("simp import-closure allocation"))?;
                pending.push((index, true));
                for &parent in &self.parents[index] {
                    if self.closures.get(parent).ok_or(OUTSIDE)?.is_none() {
                        pending.push((parent, false));
                    }
                }
                continue;
            }
            self.spend(words as u64 * (count as u64 + 1))?;
            let mut reach = Vec::new();
            reach
                .try_reserve_exact(words)
                .map_err(|_| SourceOleanImportError::Limit("simp import-closure allocation"))?;
            reach.resize(words, 0u64);
            reach[index / 64] |= 1 << (index % 64);
            for &parent in &self.parents[index] {
                let Some(Reach(bits)) = &self.closures[parent] else {
                    return Err(CYCLIC);
                };
                for (word, bits) in reach.iter_mut().zip(bits) {
                    *word |= bits;
                }
            }
            self.closures[index] = Some(Reach(reach));
        }
        self.spend(words as u64)?;
        self.closures.get(module).cloned().flatten().ok_or(OUTSIDE)
    }

    fn authorize(
        &mut self,
        origin: &Environment,
        active: &Environment,
        reachable: &Reach,
        module: &Name,
        name: &Name,
    ) -> Result<()> {
        self.spend(1)?;
        let actual = active.find(name).ok_or_else(|| {
            registry_error(module, SimpSetError::UnknownDeclaration(name.clone()))
        })?;
        if origin.find(name) == Some(actual) {
            return Ok(());
        }
        let allowed = if let Some(owners) = self.owners.get(name) {
            let count = owners.len();
            let allowed = owners.iter().any(|&index| reachable.contains(index));
            self.spend(count as u64)?;
            allowed
        } else {
            false
        };
        if !allowed {
            return Err(SourceOleanImportError::Metadata {
                module: module.clone(),
                declaration: name.clone(),
                reason: "simp declaration is outside this module's checked import closure",
            });
        }
        Ok(())
    }

    fn authorize_entry(
        &mut self,
        origin: &Environment,
        active: &Environment,
        reachable: &Reach,
        module: &Name,
        row: &metadata::SimpEntry,
    ) -> Result<()> {
        self.authorize(origin, active, reachable, module, origin_of(row))?;
        match &row.kind {
            metadata::SimpKind::Theorem(theorem) => {
                if let ExprNode::Const { name, .. } = theorem.proof.node() {
                    self.authorize(origin, active, reachable, module, name)?;
                }
            }
            metadata::SimpKind::UnfoldTheorems { theorems, .. } => {
                for theorem in theorems {
                    self.authorize(origin, active, reachable, module, theorem)?;
                }
            }
            metadata::SimpKind::Unfold(_) => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
