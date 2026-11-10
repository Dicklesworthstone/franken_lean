//! Document outlines join explicit parser names to the checked source snapshot.
//! Generated helpers and anonymous instances have no invented source name.
use super::super::grammar::{Resolution, SourceGrammar};
use super::*;
use fln_elab::records::imported::ImportedStructures;
use fln_env::constants::ConstantInfo;
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

/// The admitted identity is separate from the user-facing outline name: private
/// declarations must still join the elaborator's exact constant, not its label.
pub(super) struct SourceDeclarationOrigin {
    pub name: Name,
    pub symbol: SourceDocumentSymbol,
}

pub(super) struct SourceOriginBudget {
    limits: DocumentSymbolLimits,
    commands_left: usize,
    syntax_left: usize,
}

impl SourceOriginBudget {
    pub fn new(limits: DocumentSymbolLimits) -> Self {
        Self {
            limits,
            commands_left: limits.max_commands,
            syntax_left: limits.max_syntax_nodes,
        }
    }
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
        let source = inputs
            .iter()
            .find(|input| input.name == entry)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: entry.clone(),
            })?
            .source;
        self.declaration_origins(
            inputs,
            entry,
            source,
            checked.checked.checked.engine.environment(),
            &mut SourceOriginBudget::new(limits),
        )
        .map(|outcome| {
            outcome
                .map_complete(|origins| origins.into_iter().map(|origin| origin.symbol).collect())
        })
    }

    /// Enumerate only bytes already admitted in `environment`. Navigation passes
    /// its checked command prefix; outlines pass the fully checked document.
    /// Shared counters bound the entire import closure and nested `in` commands.
    pub(super) fn declaration_origins(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        source: &[u8],
        environment: &Environment,
        budget: &mut SourceOriginBudget,
    ) -> Result<Outcome<Vec<SourceDeclarationOrigin>>, SourceModuleCheckError> {
        let mut prefix_inputs = source_closure(inputs, entry)?;
        let input_index = prefix_inputs
            .iter()
            .position(|input| input.name == entry)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: entry.clone(),
            })?;
        let header = modules::parse_source_header(source).map_err(|error| {
            SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            }
        })?;
        // Start from the checked import world, not the final file's journal:
        // local syntax can expire and later syntax must not change an earlier
        // declaration's parse. The caller already checked these exact bytes.
        prefix_inputs[input_index].source = &source[..header.body_start.0];
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
            .enter(|| fln_parse::command_scope::partition(&source[header.body_start.0..]))
            .map_err(|error| SourceModuleCheckError::Header {
                module: entry.clone(),
                error: error.with_original_offset(header.body_start),
            })?;
        if commands.len() > budget.commands_left {
            return Err(limit(
                "document symbol commands",
                budget.limits.max_commands,
            ));
        }
        let structures = ImportedStructures::read(environment).map_err(|error| {
            if error == fln_elab::records::RecordError::ResourceLimit {
                // Preserve the registry's typed resource stop. Its independent
                // bounds are not the caller's syntax-node budget, and exhausting
                // them is no evidence that the checked source is invalid.
                SourceModuleCheckError::Source {
                    module: entry.clone(),
                    error: SourceCheckError::Command {
                        file: 0,
                        command: 0,
                        offset: 0,
                        error: Box::new(EngineExecutionError::Frontend(
                            DefinitionFrontendError::Elaborate(
                                fln_elab::NatDefinitionElabError::Inference(
                                    fln_elab::source::SourceInferenceError::Record(error),
                                ),
                            ),
                        )),
                    },
                }
            } else {
                SourceModuleCheckError::Extension {
                    module: entry.clone(),
                    extension: fln_elab::records::imported::export::journal_name(),
                    reason: "invalid checked structure metadata while locating declarations",
                }
            }
        })?;
        let mut scopes = super::super::scopes::Scopes::default();
        scopes.current.source_module = Some(entry.clone());
        scopes.current.private_module = header.module_system.then(|| entry.clone());
        let mut symbols = Vec::new();
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
                    budget.commands_left =
                        budget.commands_left.checked_sub(1).ok_or_else(|| {
                            limit("document symbol commands", budget.limits.max_commands)
                        })?;
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
                let map = |range: Range<usize>| {
                    // A half-open endpoint follows the last included byte.
                    // Mapping a normalized LF directly lands inside CRLF.
                    base + view.to_original(fln_parse::BytePos(range.start)).0
                        ..base + view.to_original(fln_parse::BytePos(range.end - 1)).0 + 1
                };
                let mut origins = vec![(absolute.clone(), syntax, selection)];
                origins.extend(explicit_children(
                    syntax,
                    &absolute,
                    environment,
                    &structures,
                    budget,
                )?);
                for (name, syntax, selection) in origins {
                    let Some(range) = syntax_range(
                        syntax,
                        &mut budget.syntax_left,
                        budget.limits.max_syntax_nodes,
                    )?
                    else {
                        continue;
                    };
                    let range = map(range);
                    let selection_range = map(selection);
                    if range.end > source.len()
                        || selection_range.start < range.start
                        || selection_range.end > range.end
                        || selection_range.is_empty()
                    {
                        return Err(source_error(
                            entry,
                            index,
                            base,
                            "declaration origin is outside its source range".into(),
                        ));
                    }
                    symbols.push(SourceDeclarationOrigin {
                        symbol: SourceDocumentSymbol {
                            name: scope.user_name(&name),
                            range,
                            selection_range,
                        },
                        name,
                    });
                }
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

/// A location pass may inspect a dependency of the requested document. Its
/// grammar must be checked against that dependency's own import closure, not
/// the document and its unrelated sibling imports. The outer admission already
/// validated this finite source graph; this walk only selects its exact subset.
fn source_closure<'a>(
    inputs: &[SourceModuleInput<'a>],
    entry: &Name,
) -> Result<Vec<SourceModuleInput<'a>>, SourceModuleCheckError> {
    let by_name: std::collections::BTreeMap<_, _> = inputs
        .iter()
        .map(|input| (input.name.clone(), *input))
        .collect();
    let mut visited = std::collections::BTreeSet::new();
    let mut pending = vec![entry.clone()];
    while let Some(module) = pending.pop() {
        if !visited.insert(module.clone()) {
            continue;
        }
        let input = by_name
            .get(&module)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: module.clone(),
            })?;
        let mut header = modules::parse_source_header(input.source).map_err(|error| {
            SourceModuleCheckError::Header {
                module: module.clone(),
                error,
            }
        })?;
        if header.module_system && !header.prelude {
            header.imports.push(Name::from_components(["Init"]));
        }
        // An absent source edge can be supplied by a checked .olean context.
        // The ordinary checker below remains responsible for validating it.
        pending.extend(
            header
                .imports
                .into_iter()
                .filter(|import| by_name.contains_key(import)),
        );
    }
    Ok(inputs
        .iter()
        .filter(|input| visited.contains(input.name))
        .copied()
        .collect())
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
    identifier(args.first()?)
}

fn identifier(syntax: &Syntax) -> Option<(&Name, Range<usize>)> {
    let Syntax::Ident { val, info, .. } = syntax else {
        return None;
    };
    let range = info.pos(true)?.0..info.end_pos(true)?.0;
    (!range.is_empty()).then_some((val, range))
}

fn node_args<'a>(syntax: &'a Syntax, leaf: &str) -> Option<&'a [Syntax]> {
    match syntax {
        Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["Lean", "Parser", "Command", leaf]) =>
        {
            Some(args)
        }
        _ => None,
    }
}

fn null_args(syntax: &Syntax) -> Option<&[Syntax]> {
    match syntax {
        Syntax::Node { kind, args, .. } if kind == &Name::from_components(["null"]) => Some(args),
        _ => None,
    }
}

/// Constructor and projection names are admitted children of the exact owner.
/// Only their authored identifiers receive origins: generated recursors, the
/// default `mk`, inherited projections and default overrides do not.
fn explicit_children<'a>(
    syntax: &'a Syntax,
    owner: &Name,
    environment: &Environment,
    structures: &ImportedStructures,
    budget: &mut SourceOriginBudget,
) -> Result<Vec<(Name, &'a Syntax, Range<usize>)>, SourceModuleCheckError> {
    let mut origins = Vec::new();
    let Some(command) = node_args(syntax, "declaration").and_then(|args| args.get(1)) else {
        return Ok(origins);
    };
    let constructor = |ident: &Syntax| {
        let (name, selection) = identifier(ident)?;
        let name = owner.append_core(name);
        matches!(environment.find(&name), Some(ConstantInfo::Ctor(ctor)) if &ctor.induct == owner)
            .then_some((name, selection))
    };
    if let Some(constructors) = node_args(command, "inductive")
        .and_then(|args| args.get(4))
        .and_then(null_args)
    {
        for syntax in constructors {
            if let Some((name, selection)) = node_args(syntax, "ctor")
                .and_then(|args| args.get(3))
                .and_then(constructor)
            {
                origins.push((name, syntax, selection));
            }
        }
        return Ok(origins);
    }
    let Some(body) = node_args(command, "structure")
        .and_then(|args| args.get(4))
        .and_then(null_args)
    else {
        return Ok(origins);
    };
    let Some(structure) = structures.get(owner) else {
        return Ok(origins);
    };
    if let Some(syntax) = body
        .get(1)
        .and_then(null_args)
        .and_then(|args| args.first())
        && let Some((name, selection)) = node_args(syntax, "structCtor")
            .and_then(|args| args.get(1))
            .and_then(constructor)
    {
        origins.push((name, syntax, selection));
    }
    let Some(fields) = body
        .get(2)
        .and_then(|syntax| node_args(syntax, "structFields"))
        .and_then(|args| args.first())
        .and_then(null_args)
    else {
        return Ok(origins);
    };
    // An inherited field can be mentioned again to override its default. That
    // does not redeclare its projection, even when a copied parent gives the
    // child a physical field with the same name.
    let mut inherited = std::collections::BTreeSet::new();
    let mut visited = std::collections::BTreeSet::new();
    let mut parents: Vec<_> = structure
        .parents
        .iter()
        .map(|parent| &parent.name)
        .collect();
    while let Some(parent) = parents.pop() {
        budget.syntax_left = budget
            .syntax_left
            .checked_sub(1)
            .ok_or_else(|| limit("document symbol syntax", budget.limits.max_syntax_nodes))?;
        if !visited.insert(parent) {
            continue;
        }
        if let Some(parent) = structures.get(parent) {
            inherited.extend(parent.fields.iter().map(|field| &field.name));
            parents.extend(parent.parents.iter().map(|parent| &parent.name));
        }
    }
    for syntax in fields {
        let names = if let Some(args) = node_args(syntax, "structSimpleBinder") {
            args.get(1).map(std::slice::from_ref)
        } else {
            [
                "structExplicitBinder",
                "structImplicitBinder",
                "structInstBinder",
            ]
            .iter()
            .find_map(|leaf| node_args(syntax, leaf))
            .and_then(|args| args.get(2))
            .and_then(null_args)
        };
        for ident in names.unwrap_or_default() {
            let Some((name, selection)) = identifier(ident) else {
                continue;
            };
            if inherited.contains(name) {
                continue;
            }
            let projection = owner.append_core(name);
            if structure.fields.iter().any(|field| {
                &field.name == name && field.projection == projection && field.subobject.is_none()
            }) && environment.contains(&projection)
            {
                origins.push((projection, syntax, selection));
            }
        }
    }
    Ok(origins)
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
