//! Navigation is a join between a real elaborator observation and checked source.
//! Textual spelling alone never selects a declaration, and an unfinished command
//! cannot manufacture a location for an unchecked or stale declaration.
use super::*;
use fln_core::expr::ExprNode;
use fln_parse::command_scope::ScopeCommand;
use fln_syntax::tree::Syntax;
use std::ops::Range;

/// Independent bounds for the source-location pass. Inspection also remains
/// subject to the session's original source, import and checking budgets.
#[derive(Debug, Clone, Copy)]
pub struct DefinitionLookupLimits {
    pub max_source_bytes: usize,
    pub max_modules: usize,
    pub max_commands: usize,
    pub max_head_steps: usize,
}
impl Default for DefinitionLookupLimits {
    fn default() -> Self {
        Self {
            max_source_bytes: 1024 * 1024,
            max_modules: 256,
            max_commands: 4096,
            max_head_steps: 100_000,
        }
    }
}

/// The explicit source identifier of an already checked definition or theorem.
/// `range` is in the ORIGINAL UTF-8 bytes of `module`, not normalized parser text.
/// This metadata confers no admission authority on the command at the cursor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDefinition {
    pub name: Name,
    pub module: Name,
    pub range: Range<usize>,
}

impl SourceModuleSession {
    /// Locate an elaborator-resolved global in the exact checked source closure.
    /// Locals, seed constants, generated declarations and unsupported source
    /// declaration shapes return `None`, never a same-spelled global substitute.
    pub fn definition(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        offset: usize,
    ) -> Result<Outcome<Option<SourceDefinition>>, SourceModuleCheckError> {
        self.definition_with_limits(inputs, entry, offset, DefinitionLookupLimits::default())
    }

    pub fn definition_with_limits(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        offset: usize,
        limits: DefinitionLookupLimits,
    ) -> Result<Outcome<Option<SourceDefinition>>, SourceModuleCheckError> {
        if inputs.len() > limits.max_modules {
            return Err(limit("definition modules", limits.max_modules));
        }
        let mut bytes = 0usize;
        for input in inputs {
            bytes = bytes
                .checked_add(input.source.len())
                .filter(|n| *n <= limits.max_source_bytes)
                .ok_or_else(|| limit("definition source bytes", limits.max_source_bytes))?;
        }
        let inspected = match self.inspect(inputs, entry, offset, ObservationKind::Term)? {
            Outcome::Complete(inspected) => inspected,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let Some(SourceObservation::Term { expression, .. }) = &inspected.observation else {
            return Ok(Outcome::Complete(None));
        };
        let Some(target) = constant_head(expression, limits.max_head_steps)? else {
            return Ok(Outcome::Complete(None));
        };
        let environment = inspected.prefix.checked.checked.engine.environment();
        if !environment.contains(target) {
            return Ok(Outcome::Complete(None));
        }
        let mut found = None;
        let mut visited = 0usize;
        for module in &inspected.prefix.checked.module_order {
            let input = inputs
                .iter()
                .find(|input| input.name == module)
                .ok_or_else(|| SourceModuleCheckError::MissingModule {
                    importer: entry.clone(),
                    module: module.clone(),
                })?;
            let header = modules::parse_source_header(input.source).map_err(|error| {
                SourceModuleCheckError::Header {
                    module: module.clone(),
                    error,
                }
            })?;
            let commands = fln_parse::command_scope::partition(
                &input.source[header.body_start.0..],
            )
            .map_err(|error| SourceModuleCheckError::Header {
                module: module.clone(),
                error: error.with_original_offset(header.body_start),
            })?;
            // Inspection checked only the current command's prefix, NOT its
            // body or later commands. Never search those unchecked bytes.
            let count = if module == entry {
                commands
                    .iter()
                    .rposition(|(start, _)| header.body_start.0 + start.0 <= offset)
                    .unwrap_or(0)
            } else {
                commands.len()
            };
            // Only namespace/section lifetimes affect a declaration's absolute
            // name. Other controls already passed the ordinary checker and must
            // not be executed again (including variable/attribute journals).
            let mut scopes = super::super::scopes::Scopes::default();
            for (command_index, (start, command)) in commands.iter().take(count).enumerate() {
                visited = visited
                    .checked_add(1)
                    .filter(|n| *n <= limits.max_commands)
                    .ok_or_else(|| limit("definition commands", limits.max_commands))?;
                let base = header.body_start.0 + start.0;
                let control = fln_parse::command_scope::parse(command).map_err(|error| {
                    SourceModuleCheckError::Header {
                        module: module.clone(),
                        error: error.with_original_offset(fln_parse::BytePos(base)),
                    }
                })?;
                if let Some(control) = control {
                    if matches!(
                        control,
                        ScopeCommand::Namespace(_)
                            | ScopeCommand::Section(_)
                            | ScopeCommand::End(_)
                    ) {
                        scopes
                            .check_limits(&control)
                            .map_err(|(resource, size)| limit(resource, size))?;
                        scopes.apply(control).map_err(|message| {
                            source_error(module, command_index, base, message)
                        })?;
                    }
                    continue;
                }
                let parsed = fln_parse::parse_definition(command).map_err(|error| {
                    SourceModuleCheckError::Header {
                        module: module.clone(),
                        error: error.with_original_offset(fln_parse::BytePos(base)),
                    }
                })?;
                let Some((name, range)) = explicit_name(parsed.syntax()) else {
                    continue;
                };
                let absolute = scopes.current.declaration_name(name).map_err(|error| {
                    source_error(module, command_index, base, error.to_string())
                })?;
                if &absolute != target {
                    continue;
                }
                let range = base
                    + parsed
                        .source_view()
                        .to_original(fln_parse::BytePos(range.start))
                        .0
                    ..base
                        + parsed
                            .source_view()
                            .to_original(fln_parse::BytePos(range.end))
                            .0;
                let text = std::str::from_utf8(input.source).map_err(|_| {
                    source_error(
                        module,
                        command_index,
                        base,
                        "definition source is not UTF-8".into(),
                    )
                })?;
                if range.is_empty() || text.get(range.clone()).is_none() || found.is_some() {
                    return Err(source_error(
                        module,
                        command_index,
                        base,
                        "definition location is invalid or ambiguous".into(),
                    ));
                }
                found = Some(SourceDefinition {
                    name: absolute,
                    module: module.clone(),
                    range,
                });
            }
        }
        Ok(Outcome::Complete(found))
    }
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

/// Strip only elaborator-inserted application/metadata wrappers. Reducing or
/// unfolding here would navigate to a dependency of the selected declaration.
fn constant_head(
    expression: &Expr,
    max_steps: usize,
) -> Result<Option<&Name>, SourceModuleCheckError> {
    let mut current = expression;
    for _ in 0..max_steps {
        match current.node() {
            ExprNode::Const { name, .. } => return Ok(Some(name)),
            ExprNode::App { f, .. } => current = f,
            ExprNode::MData { expr, .. } => current = expr,
            _ => return Ok(None),
        }
    }
    Err(limit("definition expression head", max_steps))
}

/// Inspect only the declaration header, never identifiers inside a body, local
/// helper, quotation or example. More generated shapes require explicit origins.
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
    if !["definition", "theorem", "abbrev", "opaque"]
        .iter()
        .any(|name| kind == &Name::from_components(["Lean", "Parser", "Command", *name]))
    {
        return None;
    }
    let Syntax::Node { kind, args, .. } = args.get(1)? else {
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
