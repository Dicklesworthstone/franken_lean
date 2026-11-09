//! Document outlines join explicit parser names to the checked source snapshot.
//! Generated declarations and anonymous instances have no invented source name.
use super::super::grammar::{Resolution, SourceGrammar};
use super::*;
use fln_parse::command_scope::ScopeCommand;
use fln_syntax::tree::Syntax;
use std::ops::Range;

/// Bounds for enumerating an outline, in addition to ordinary module checking.
#[derive(Debug, Clone, Copy)]
pub struct DocumentSymbolLimits {
    pub max_source_bytes: usize,
    pub max_modules: usize,
    pub max_commands: usize,
    pub max_syntax_nodes: usize,
}
impl Default for DocumentSymbolLimits {
    fn default() -> Self {
        Self {
            max_source_bytes: 1024 * 1024,
            max_modules: 256,
            max_commands: 4096,
            max_syntax_nodes: 100_000,
        }
    }
}

/// An explicitly named, admitted declaration in the requested source module.
/// Both ranges use the original UTF-8 bytes. The name is qualified for a flat
/// outline, with module-private implementation prefixes removed for display.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDocumentSymbol {
    pub name: Name,
    pub range: Range<usize>,
    pub selection_range: Range<usize>,
}

impl SourceModuleSession {
    /// List explicit declarations from the current checked document, excluding
    /// imports, local binders and generated helpers. Failure never returns a
    /// partial outline or an outline cached for different source bytes.
    pub fn document_symbols(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
    ) -> Result<Outcome<Vec<SourceDocumentSymbol>>, SourceModuleCheckError> {
        self.document_symbols_with_limits(inputs, entry, DocumentSymbolLimits::default())
    }

    pub fn document_symbols_with_limits(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        limits: DocumentSymbolLimits,
    ) -> Result<Outcome<Vec<SourceDocumentSymbol>>, SourceModuleCheckError> {
        if inputs.len() > limits.max_modules {
            return Err(limit("document symbol modules", limits.max_modules));
        }
        let mut bytes = 0usize;
        for input in inputs {
            bytes = bytes
                .checked_add(input.source.len())
                .filter(|n| *n <= limits.max_source_bytes)
                .ok_or_else(|| limit("document symbol source bytes", limits.max_source_bytes))?;
        }
        let checked = match self.check(inputs, entry)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let input_index = inputs
            .iter()
            .position(|input| input.name == entry)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: entry.clone(),
            })?;
        let input = &inputs[input_index];
        let header = modules::parse_source_header(input.source).map_err(|error| {
            SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            }
        })?;
        // Start from the checked import world, not the final file's journal:
        // local syntax can expire and later syntax must not change an earlier
        // declaration's parse. The exact full source was admitted above.
        let mut prefix_inputs = inputs.to_vec();
        prefix_inputs[input_index].source = &input.source[..header.body_start.0];
        let prefix = match self.check(&prefix_inputs, entry)? {
            Outcome::Complete(prefix) => prefix,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut grammar = SourceGrammar::for_engine(
            &prefix.checked.checked.engine,
            Some(entry),
            header.module_system,
        )
        .map_err(|error| source_error(entry, 0, 0, error.to_string()))?;
        let commands = grammar
            .enter(|| fln_parse::command_scope::partition(&input.source[header.body_start.0..]))
            .map_err(|error| SourceModuleCheckError::Header {
                module: entry.clone(),
                error: error.with_original_offset(header.body_start),
            })?;
        if commands.len() > limits.max_commands {
            return Err(limit("document symbol commands", limits.max_commands));
        }
        let environment = checked.checked.checked.engine.environment();
        let mut scopes = super::super::scopes::Scopes::default();
        scopes.current.source_module = Some(entry.clone());
        scopes.current.private_module = header.module_system.then(|| entry.clone());
        let mut symbols = Vec::new();
        let mut work = limits.max_syntax_nodes;
        let mut queue: std::collections::VecDeque<_> = commands
            .into_iter()
            .map(|(start, command)| {
                SourceStep::Command((fln_parse::BytePos(header.body_start.0 + start.0), command))
            })
            .collect();
        let mut index = 0;
        while let Some(step) = queue.pop_front() {
            let (start, command) = match step {
                SourceStep::Command(command) => {
                    if index >= limits.max_commands {
                        return Err(limit("document symbol commands", limits.max_commands));
                    }
                    command
                }
                SourceStep::Scope(start, control) => {
                    observe_scope(&mut scopes, &mut grammar, control, entry, index, start.0)?;
                    continue;
                }
            };
            let base = start.0;
            let control = grammar
                .enter(|| fln_parse::command_scope::parse(command))
                .map_err(|error| SourceModuleCheckError::Header {
                    module: entry.clone(),
                    error: error.with_original_offset(start),
                })?;
            if let Some(control) = control {
                let steps = match control {
                    ScopeCommand::OpenIn {
                        names,
                        scoped,
                        body,
                    } => Some(in_steps(
                        start,
                        command,
                        if scoped {
                            ScopeCommand::OpenScoped(names)
                        } else {
                            ScopeCommand::Open(names)
                        },
                        body,
                    )),
                    ScopeCommand::SetOptionIn { name, value, body } => Some(in_steps(
                        start,
                        command,
                        ScopeCommand::SetOption { name, value },
                        body,
                    )),
                    ScopeCommand::In { head, body } => {
                        Some(in_command_steps(start, command, head, body))
                    }
                    control => {
                        observe_scope(&mut scopes, &mut grammar, control, entry, index, base)?;
                        None
                    }
                };
                if let Some(steps) = steps {
                    for step in steps.into_iter().rev() {
                        queue.push_front(step);
                    }
                }
                index += 1;
                continue;
            }
            // Parsing needs the same lexical grammar, but no expansion or
            // admission is performed here. The checked pass already resolved
            // and validated these templates in their exact definition worlds.
            if grammar
                .declare(command, |_| Resolution::Unchecked)
                .map_err(|error| source_error(entry, index, base, error.to_string()))?
            {
                index += 1;
                continue;
            }
            let parse_error =
                |error: fln_parse::DefinitionParseError| SourceModuleCheckError::Header {
                    module: entry.clone(),
                    error: error.with_original_offset(fln_parse::BytePos(base)),
                };
            let mut add_symbol = |syntax: &Syntax, view: &fln_syntax::view::SourceView| {
                let Some((name, selection)) = explicit_name(syntax) else {
                    return Ok(());
                };
                let scope = scopes
                    .current
                    .for_declaration(syntax)
                    .map_err(|error| source_error(entry, index, base, error.to_string()))?;
                let absolute = scope
                    .declaration_name(name)
                    .map_err(|error| source_error(entry, index, base, error.to_string()))?;
                if !environment.contains(&absolute) {
                    return Ok(());
                }
                let range = syntax_range(syntax, &mut work, limits.max_syntax_nodes)?;
                let map = |range: Range<usize>| {
                    // A half-open endpoint follows the last included byte.
                    // Mapping a normalized LF directly lands inside CRLF.
                    base + view.to_original(fln_parse::BytePos(range.start)).0
                        ..base + view.to_original(fln_parse::BytePos(range.end - 1)).0 + 1
                };
                let Some(range) = range else { return Ok(()) };
                symbols.push(SourceDocumentSymbol {
                    name: scope.user_name(&absolute),
                    range: map(range),
                    selection_range: map(selection),
                });
                Ok::<(), SourceModuleCheckError>(())
            };
            if let Some(members) = grammar
                .enter(|| fln_parse::command_scope::mutual::parse(command))
                .map_err(parse_error)?
            {
                // The ordinary mutual parser preserves each member's positions
                // in the normalized group's coordinate system.
                let original = fln_syntax::source::SourceText::from_utf8(command)
                    .map_err(|error| source_error(entry, index, base, error.to_string()))?;
                let view = fln_syntax::view::SourceView::of(&original);
                for member in &members {
                    add_symbol(member, &view)?;
                }
            } else {
                let parsed = grammar
                    .enter(|| fln_parse::parse_source_command(command))
                    .map_err(parse_error)?;
                add_symbol(parsed.syntax(), parsed.source_view())?;
            }
            index += 1;
        }
        Ok(Outcome::Complete(symbols))
    }
}

fn observe_scope(
    scopes: &mut super::super::scopes::Scopes,
    grammar: &mut SourceGrammar,
    control: ScopeCommand,
    module: &Name,
    command: usize,
    offset: usize,
) -> Result<(), SourceModuleCheckError> {
    grammar.observe(&control);
    if matches!(
        control,
        ScopeCommand::Namespace(_)
            | ScopeCommand::Section(_)
            | ScopeCommand::SectionWithModifiers { .. }
            | ScopeCommand::End(_)
    ) {
        scopes
            .check_limits(&control)
            .map_err(|(resource, bound)| limit(resource, bound))?;
        scopes
            .apply(control)
            .map_err(|message| source_error(module, command, offset, message))?;
    }
    Ok(())
}

fn limit(resource: &'static str, limit: usize) -> SourceModuleCheckError {
    SourceModuleCheckError::Limit { resource, limit }
}

fn source_error(
    module: &Name,
    command: usize,
    offset: usize,
    message: String,
) -> SourceModuleCheckError {
    SourceModuleCheckError::Source {
        module: module.clone(),
        error: SourceCheckError::Scope {
            file: 0,
            command,
            offset,
            message,
        },
    }
}

fn explicit_name(syntax: &Syntax) -> Option<(&Name, Range<usize>)> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    if kind != &Name::from_components(["Lean", "Parser", "Command", "declaration"]) {
        return None;
    }
    let Syntax::Node { kind, args, .. } = args.get(1)? else {
        return None;
    };
    if ![
        "definition",
        "theorem",
        "abbrev",
        "opaque",
        "axiom",
        "inductive",
        "structure",
        "instance",
    ]
    .iter()
    .any(|leaf| kind == &Name::from_components(["Lean", "Parser", "Command", leaf]))
    {
        return None;
    }
    let id = if kind == &Name::from_components(["Lean", "Parser", "Command", "instance"]) {
        let Syntax::Node { args, .. } = args.get(3)? else {
            return None;
        };
        args.first()?
    } else {
        args.get(1)?
    };
    let Syntax::Node { kind, args, .. } = id else {
        return None;
    };
    if kind != &Name::from_components(["Lean", "Parser", "Command", "declId"]) {
        return None;
    }
    let Syntax::Ident { val, info, .. } = args.first()? else {
        return None;
    };
    Some((val, info.pos(true)?.0..info.end_pos(true)?.0))
}

fn syntax_range(
    syntax: &Syntax,
    work: &mut usize,
    limit_: usize,
) -> Result<Option<Range<usize>>, SourceModuleCheckError> {
    let mut pending = vec![syntax];
    let mut start = usize::MAX;
    let mut end = 0;
    while let Some(syntax) = pending.pop() {
        *work = work
            .checked_sub(1)
            .ok_or_else(|| limit("document symbol syntax", limit_))?;
        if let Some(pos) = syntax.info().pos(true) {
            start = start.min(pos.0);
        }
        if let Some(pos) = syntax.info().end_pos(true) {
            end = end.max(pos.0);
        }
        if let Syntax::Node { args, .. } = syntax {
            pending.extend(args);
        }
    }
    Ok((start < end).then_some(start..end))
}
