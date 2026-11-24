//! Bind each explicit trigger to the recording module's checked dependency
//! closure. Admitting several roots together never makes them mutual imports.
use super::*;

pub(super) struct Scopes<'a> {
    indices: BTreeMap<&'a Name, usize>,
    owners: BTreeMap<Name, Vec<(usize, &'a ConstantInfo)>>,
    work_left: u64,
}

fn tick(remaining: &mut u64) -> Result<()> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or(SourceOleanImportError::Limit(
            "grind-pattern import-closure work",
        ))?;
    Ok(())
}

fn names(row: &metadata::GrindPatternEntry, remaining: &mut u64) -> Result<BTreeSet<Name>> {
    let mut result = BTreeSet::new();
    tick(remaining)?;
    result.insert(row.declaration.clone());
    for symbol in &row.symbols {
        tick(remaining)?;
        result.insert(symbol.clone());
    }
    let wildcard = Name::from_components(["[grind_dontcare]"]);
    let mut seen = HashSet::new();
    let mut pending = vec![(&row.proof, false)];
    for pattern in &row.patterns {
        tick(remaining)?;
        pending
            .try_reserve(1)
            .map_err(|_| SourceOleanImportError::Limit("grind-pattern dependency allocation"))?;
        pending.push((pattern, true));
    }
    while let Some((expression, pattern)) = pending.pop() {
        tick(remaining)?;
        seen.try_reserve(1)
            .map_err(|_| SourceOleanImportError::Limit("grind-pattern dependency allocation"))?;
        if !seen.insert((expression.allocation_identity(), pattern)) {
            continue;
        }
        pending
            .try_reserve(3)
            .map_err(|_| SourceOleanImportError::Limit("grind-pattern dependency allocation"))?;
        match expression.node() {
            ExprNode::Const { name, levels } => {
                // This reserved symbol is metadata syntax, never a declaration
                // or proof. Its position and type are checked by import_captured.
                if !(pattern && *name == wildcard && levels.is_empty()) {
                    result.insert(name.clone());
                }
            }
            ExprNode::App { f, a } => pending.extend([(f, pattern), (a, pattern)]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.extend([(binder_type, pattern), (body, pattern)]);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.extend([(type_, pattern), (value, pattern), (body, pattern)]);
            }
            ExprNode::MData { expr, .. } => pending.push((expr, pattern)),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                result.insert(struct_name.clone());
                pending.push((expr, pattern));
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(result)
}

impl<'a> Scopes<'a> {
    pub(super) fn new(
        checked: &'a CheckedOleanSet,
        rows: &[Option<metadata::GrindPatternEntry>],
        work_left: u64,
    ) -> Result<Self> {
        let mut result = Self {
            indices: BTreeMap::new(),
            owners: BTreeMap::new(),
            work_left,
        };
        for row in rows.iter().flatten() {
            for name in names(row, &mut result.work_left)? {
                result.owners.entry(name).or_default();
            }
        }
        if result.owners.is_empty() {
            return Ok(result);
        }
        for (index, module) in checked.modules.iter().enumerate() {
            tick(&mut result.work_left)?;
            result.indices.insert(&module.name, index);
            for constant in &module.decoded.constants {
                tick(&mut result.work_left)?;
                if let Some(owners) = result.owners.get_mut(constant.name()) {
                    owners.try_reserve(1).map_err(|_| {
                        SourceOleanImportError::Limit("grind-pattern ownership allocation")
                    })?;
                    owners.push((index, constant));
                }
            }
        }
        Ok(result)
    }

    pub(super) fn validate_row(
        &mut self,
        checked: &CheckedOleanSet,
        origin: &Environment,
        active: &Environment,
        module: usize,
        row: &metadata::GrindPatternEntry,
    ) -> Result<()> {
        for declaration in names(row, &mut self.work_left)? {
            self.validate(checked, origin, active, module, &declaration)?;
        }
        Ok(())
    }

    fn validate(
        &mut self,
        checked: &CheckedOleanSet,
        origin: &Environment,
        active: &Environment,
        module: usize,
        declaration: &Name,
    ) -> Result<()> {
        tick(&mut self.work_left)?;
        let error = |reason| SourceOleanImportError::Metadata {
            module: checked.modules[module].name.clone(),
            declaration: declaration.clone(),
            reason,
        };
        let target = active
            .find(declaration)
            .ok_or_else(|| error("a grind-pattern entry names no admitted declaration"))?;
        if origin.find(declaration) == Some(target) {
            return Ok(());
        }
        let mut pending = vec![module];
        let mut seen = HashSet::new();
        while let Some(index) = pending.pop() {
            tick(&mut self.work_left)?;
            seen.try_reserve(1).map_err(|_| {
                SourceOleanImportError::Limit("grind-pattern import-closure allocation")
            })?;
            if !seen.insert(index) {
                continue;
            }
            if self.owners.get(declaration).is_some_and(|owners| {
                owners
                    .iter()
                    .any(|(owner, constant)| *owner == index && *constant == target)
            }) {
                return Ok(());
            }
            for import in &checked.modules[index].decoded.module.imports {
                tick(&mut self.work_left)?;
                let dependency = self.indices.get(&import.module).copied().ok_or(
                    SourceOleanImportError::Internal("grind-pattern import graph is incomplete"),
                )?;
                pending.try_reserve(1).map_err(|_| {
                    SourceOleanImportError::Limit("grind-pattern import-closure allocation")
                })?;
                pending.push(dependency);
            }
        }
        Err(error(
            "a grind-pattern entry is outside this module's checked import closure",
        ))
    }
}

pub(super) fn error(
    module: &Name,
    error: fln_elab::NatDefinitionElabError,
) -> SourceOleanImportError {
    SourceOleanImportError::Grind {
        module: module.clone(),
        error,
    }
}
