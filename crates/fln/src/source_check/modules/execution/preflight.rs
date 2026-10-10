//! Parse native source imports under their exact preceding grammar exports.
//! This is a syntax pass only: quotation references are checked later in each
//! module's admitted declaration world, and no preflight result is published.
use super::*;
use crate::source_check::grammar::{Resolution, SourceGrammar};
use fln_parse::command_scope::ScopeCommand;
use fln_parse::extensions::NativeSyntaxModule;
use std::collections::BTreeSet;

pub(super) fn check(
    modules: &[SourceModuleInput<'_>],
    limits: SourceModuleCheckLimits,
    implicit_init: bool,
) -> Result<(), SourceModuleCheckError> {
    if modules.len() > limits.max_modules {
        return Err(SourceModuleCheckError::Limit {
            resource: "modules",
            limit: limits.max_modules,
        });
    }
    let mut meter = Meter {
        work: 0,
        bytes: 0,
        limits,
    };
    let mut by_name = BTreeMap::new();
    let mut bytes = 0usize;
    let mut imports = 0usize;
    let mut headers = Vec::new();
    for (index, module) in modules.iter().enumerate() {
        graph::validate_name(module.name, &mut meter)?;
        if by_name.insert(module.name.clone(), index).is_some() {
            return Err(SourceModuleCheckError::DuplicateModule(module.name.clone()));
        }
        bytes = bytes
            .checked_add(module.source.len())
            .filter(|bytes| *bytes <= limits.source.max_bytes)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "source bytes",
                limit: limits.source.max_bytes,
            })?;
        let mut header =
            parse_source_header(module.source).map_err(|error| SourceModuleCheckError::Header {
                module: module.name.clone(),
                error,
            })?;
        validate_source_header(module.name, &header)?;
        if (implicit_init || header.module_system) && !header.prelude {
            header.imports.insert(0, Name::from_components(["Init"]));
        }
        imports = imports
            .checked_add(header.imports.len())
            .filter(|imports| *imports <= limits.max_imports)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "imports",
                limit: limits.max_imports,
            })?;
        for import in &header.imports {
            graph::validate_name(import, &mut meter)?;
        }
        headers.push(header);
    }
    // Artifact imports do not supply native quoted templates. Their existence
    // and receipt authority are validated by the real execution graph.
    let dependencies: Vec<Vec<usize>> = headers
        .iter()
        .map(|header| {
            header
                .imports
                .iter()
                .filter_map(|name| by_name.get(name).copied())
                .collect()
        })
        .collect();
    let mut completed = BTreeMap::<usize, NativeSyntaxModule>::new();
    let mut count = 0usize;
    for root in 0..modules.len() {
        let order = graph::postorder(root, &dependencies, modules, &mut meter)?;
        for index in order {
            if completed.contains_key(&index) {
                continue;
            }
            let module = modules[index];
            let header = &headers[index];
            let mut grammar = SourceGrammar::for_module(Some(module.name), header.module_system);
            let mut seen = BTreeSet::new();
            for &dependency in &dependencies[index] {
                for predecessor in graph::postorder(dependency, &dependencies, modules, &mut meter)?
                {
                    if seen.insert(predecessor) {
                        grammar
                            .import_native(&completed[&predecessor])
                            .map_err(|error| source_error(module.name, error))?;
                    }
                }
            }
            let commands = grammar.enter(|| super::commands(module.name, module.source, header))?;
            for (command, (at, source)) in commands.into_iter().enumerate() {
                count = count
                    .checked_add(1)
                    .filter(|count| *count <= limits.source.max_commands)
                    .ok_or(SourceModuleCheckError::Limit {
                        resource: "source commands",
                        limit: limits.source.max_commands,
                    })?;
                check_command(module.name, command, at, source, &mut grammar, &mut meter)?;
            }
            completed.insert(
                index,
                grammar
                    .export_native()
                    .map_err(|error| source_error(module.name, error))?,
            );
        }
    }
    Ok(())
}

fn check_command(
    module: &Name,
    index: usize,
    at: fln_parse::BytePos,
    source: &[u8],
    grammar: &mut SourceGrammar,
    meter: &mut Meter,
) -> Result<(), SourceModuleCheckError> {
    use crate::source_check::{SourceStep, in_steps};
    let mut queue = std::collections::VecDeque::from([SourceStep::Command((at, source))]);
    while let Some(step) = queue.pop_front() {
        meter.work(1)?;
        let (at, source) = match step {
            SourceStep::Scope(_, scope) => {
                grammar.observe(&scope);
                continue;
            }
            SourceStep::Command(command) => command,
        };
        let control = grammar
            .enter(|| fln_parse::command_scope::parse(source))
            .map_err(|error| parse_error(module, index, at, error))?;
        let temporary = match control {
            Some(ScopeCommand::OpenIn {
                names,
                scoped,
                body,
            }) => Some((
                if scoped {
                    ScopeCommand::OpenScoped(names)
                } else {
                    ScopeCommand::Open(names)
                },
                body,
            )),
            Some(ScopeCommand::SetOptionIn { name, value, body }) => {
                Some((ScopeCommand::SetOption { name, value }, body))
            }
            Some(ScopeCommand::GuardMsgs { body, .. }) => {
                queue.push_front(SourceStep::Command((
                    fln_parse::BytePos(at.0 + body),
                    &source[body..],
                )));
                continue;
            }
            Some(scope) => {
                grammar.observe(&scope);
                continue;
            }
            None => None,
        };
        if let Some((scope, body)) = temporary {
            for step in in_steps(at, source, scope, body).into_iter().rev() {
                queue.push_front(step);
            }
            continue;
        }
        if grammar
            .declare(source, |_| Resolution::Unchecked)
            .map_err(|error| {
                source_error(
                    module,
                    EngineExecutionError::BatchCommand {
                        index,
                        at: Some(at),
                        error: Box::new(error),
                    },
                )
            })?
        {
            continue;
        }
        grammar
            .enter(|| {
                if fln_parse::command_scope::mutual::parse(source)?.is_none() {
                    fln_parse::parse_source_command(source)?;
                }
                Ok(())
            })
            .map_err(|error| parse_error(module, index, at, error))?;
    }
    Ok(())
}
