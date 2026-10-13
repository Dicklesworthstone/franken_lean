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
                // The scope parser locates a balanced specification but does not
                // validate its contents. Do that before admitting any external
                // imports, in the same grammar and original coordinate system.
                // This is syntax only: capture capabilities and message matching
                // remain decisions of execution and the presentation's judge.
                grammar
                    .enter(|| fln_parse::command_scope::guard_spec::parse(source, body))
                    .map_err(|error| parse_error(module, index, at, error))?;
                queue.push_front(SourceStep::Command((
                    fln_parse::BytePos(at.0 + body),
                    &source[body..],
                )));
                continue;
            }
            Some(ScopeCommand::In { head, body }) => {
                for step in crate::source_check::in_command_steps(at, source, head, body)
                    .into_iter()
                    .rev()
                {
                    queue.push_front(step);
                }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn preflight(source: &str, implicit_init: bool) -> Result<(), SourceModuleCheckError> {
        let name = Name::from_components(["Main"]);
        let input = SourceModuleInput {
            name: &name,
            source: source.as_bytes(),
        };
        let admission =
            crate::EngineAdmissionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024));
        check(
            &[input],
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
            implicit_init,
        )
    }

    #[test]
    fn guard_preflight_rejects_malformed_policies_before_import_admission() {
        for implicit_init in [false, true] {
            for spec in [
                "whitespace := invalidGuardMode",
                "ordering := invalidGuardMode",
                "substring := invalidGuardMode",
                "positions := invalidGuardMode",
                "drop invalidGuardMode",
                "unknownGuardOption := true",
                "whitespace := exact, whitespace := invalidGuardMode",
                "info,",
            ] {
                let source = format!(
                    "import UnavailableGuardDependency\n#guard_msgs ({spec}) in\n#check 1\n"
                );
                let error = preflight(&source, implicit_init).unwrap_err();
                assert!(matches!(
                    error,
                    SourceModuleCheckError::Source {
                        error: SourceCheckError::Command { .. },
                        ..
                    }
                ));
            }
        }
    }

    #[test]
    fn guard_preflight_is_syntax_only_not_a_message_judge() {
        for spec in [
            "",
            "info",
            "drop info",
            "pass error, drop all",
            "positions := true",
            "drop error",
            "ordering := sorted, substring := true, whitespace := lax",
        ] {
            let source = format!(
                "prelude\n/-- intentionally not the generated message -/\n\
                 #guard_msgs ({spec}) in\n#check 1\n"
            );
            preflight(&source, false).unwrap();
        }
        preflight("prelude\n#guard_msgs in\n#check 1\n", false).unwrap();
    }

    #[test]
    fn guard_preflight_retains_original_offsets_inside_temporary_wrappers() {
        let source = concat!(
            "prelude\r\n",
            "set_option pp.universes true in\r\n",
            "/-- Unicode λ before the error -/\r\n",
            "#guard_msgs (whitespace := invalidGuardMode) in\r\n",
            "#check 1\r\n",
        );
        let error = preflight(source, false).unwrap_err();
        let SourceModuleCheckError::Source {
            error: SourceCheckError::Command { error, .. },
            ..
        } = error
        else {
            panic!("expected a positioned command parse error: {error:?}");
        };
        assert_eq!(
            error.primary_source_offset(),
            Some(fln_parse::BytePos(source.find("invalidGuardMode").unwrap()))
        );
    }

    #[test]
    fn guard_preflight_validates_nested_headers_and_still_checks_the_body() {
        let source = concat!(
            "prelude\n#guard_msgs in\n",
            "#guard_msgs (positions := invalidGuardMode) in\n#check 1\n",
        );
        assert!(preflight(source, false).is_err());
        assert!(preflight("prelude\n#guard_msgs (drop info) in\n#check (\n", false).is_err());
        // Nested guards may be refused by execution, but well-formed syntax is
        // not an execution-capability failure in this pre-import pass.
        preflight(
            "prelude\n#guard_msgs in\n#guard_msgs (drop info) in\n#check 1\n",
            false,
        )
        .unwrap();
    }
}
