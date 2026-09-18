use super::*;

pub(super) struct Plan {
    pub(super) headers: Vec<SourceHeader>,
    pub(super) order: Vec<usize>,
    pub(super) entry: usize,
    dependencies: Vec<Vec<usize>>,
}
impl Plan {
    pub(super) fn new(
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        meter: &mut Meter,
    ) -> Result<Self, SourceModuleCheckError> {
        if modules.is_empty() {
            return Err(SourceModuleCheckError::EmptyInput);
        }
        if modules.len() > meter.limits.max_modules {
            return Err(SourceModuleCheckError::Limit { resource: "modules", limit: meter.limits.max_modules });
        }
        let mut by_name = BTreeMap::new();
        let mut total_bytes = 0usize;
        for (index, module) in modules.iter().enumerate() {
            validate_name(module.name, meter)?;
            if by_name.insert(module.name.clone(), index).is_some() {
                return Err(SourceModuleCheckError::DuplicateModule(module.name.clone()));
            }
            total_bytes = total_bytes.checked_add(module.source.len())
                .filter(|n| *n <= meter.limits.source.max_bytes)
                .ok_or(SourceModuleCheckError::Limit { resource: "source bytes", limit: meter.limits.source.max_bytes })?;
        }
        validate_name(entry, meter)?;
        let entry = by_name.get(entry).copied().ok_or_else(|| SourceModuleCheckError::MissingModule {
            importer: entry.clone(), module: entry.clone(),
        })?;
        let mut headers = Vec::new();
        let mut dependencies = Vec::new();
        let mut imports = 0usize;
        for module in modules {
            meter.work(1)?;
            let header = parse_source_header(module.source).map_err(|error| SourceModuleCheckError::Header {
                module: module.name.clone(), error,
            })?;
            imports = imports.checked_add(header.imports.len()).filter(|n| *n <= meter.limits.max_imports)
                .ok_or(SourceModuleCheckError::Limit { resource: "imports", limit: meter.limits.max_imports })?;
            let mut direct = Vec::new();
            for name in &header.imports {
                validate_name(name, meter)?;
                direct.push(by_name.get(name).copied().ok_or_else(|| SourceModuleCheckError::MissingModule {
                    importer: module.name.clone(), module: name.clone(),
                })?);
            }
            headers.push(header);
            dependencies.push(direct);
        }
        let order = postorder(entry, &dependencies, modules, meter)?;
        if order.len() != modules.len() {
            let reached: std::collections::BTreeSet<_> = order.iter().copied().collect();
            let missing = by_name.iter().find_map(|(name, &index)| {
                (!reached.contains(&index)).then_some(name)
            }).expect("unreachable module");
            return Err(SourceModuleCheckError::UnreachableModule(missing.clone()));
        }
        Ok(Self { headers, order, entry, dependencies })
    }

    pub(super) fn dependencies_of(
        &self,
        module: usize,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
    ) -> Result<Vec<usize>, SourceModuleCheckError> {
        let mut order = postorder(module, &self.dependencies, modules, meter)?;
        let last = order.pop();
        debug_assert_eq!(last, Some(module));
        Ok(order)
    }
}

fn validate_name(name: &Name, meter: &mut Meter) -> Result<(), SourceModuleCheckError> {
    let mut cursor = name.clone();
    let mut depth = 0usize;
    let mut bytes = 0usize;
    while !cursor.is_anonymous() {
        meter.work(1)?;
        depth += 1;
        if depth > meter.limits.max_name_depth {
            return Err(SourceModuleCheckError::Limit { resource: "module name depth", limit: meter.limits.max_name_depth });
        }
        match cursor.leaf_view() {
            LeafView::Str(component) if !component.is_empty() => {
                bytes = bytes.checked_add(component.len()).filter(|n| *n <= meter.limits.source.max_bytes)
                    .ok_or(SourceModuleCheckError::Limit { resource: "module name bytes", limit: meter.limits.source.max_bytes })?;
            }
            _ => return Err(SourceModuleCheckError::InvalidName(name.clone())),
        }
        cursor = cursor.parent();
    }
    if depth == 0 {
        return Err(SourceModuleCheckError::InvalidName(name.clone()));
    }
    Ok(())
}

/// Iterative DFS preserves direct-import order without recursive host stack use.
fn postorder(
    root: usize,
    dependencies: &[Vec<usize>],
    modules: &[SourceModuleInput<'_>],
    meter: &mut Meter,
) -> Result<Vec<usize>, SourceModuleCheckError> {
    meter.work(modules.len())?;
    let mut colors = vec![0u8; modules.len()];
    let mut stack = vec![(root, 0usize)];
    let mut order = Vec::new();
    colors[root] = 1;
    while let Some((module, cursor)) = stack.last_mut() {
        meter.work(1)?;
        if let Some(&dependency) = dependencies[*module].get(*cursor) {
            *cursor += 1;
            match colors[dependency] {
                0 => {
                    colors[dependency] = 1;
                    stack.push((dependency, 0));
                }
                1 => return Err(SourceModuleCheckError::Cycle(modules[dependency].name.clone())),
                _ => {}
            }
        } else {
            colors[*module] = 2;
            order.push(*module);
            stack.pop();
        }
    }
    Ok(order)
}
