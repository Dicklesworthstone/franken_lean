//! Navigation is a join between a real elaborator observation and checked source.
//! Textual spelling alone never selects a declaration, and an unfinished command
//! cannot manufacture a location for an unchecked or stale declaration.
use super::*;
use fln_core::expr::ExprNode;
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

/// The explicit source identifier of an already checked declaration, constructor
/// or structure field.
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
    /// Locals, seed constants, generated helpers and unsupported source
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
        let mut budget = symbols::SourceOriginBudget::new(DocumentSymbolLimits {
            max_source_bytes: limits.max_source_bytes,
            max_modules: limits.max_modules,
            max_commands: limits.max_commands,
            ..DocumentSymbolLimits::default()
        });
        for module in &inspected.prefix.checked.module_order {
            let input = inputs
                .iter()
                .find(|input| input.name == module)
                .ok_or_else(|| SourceModuleCheckError::MissingModule {
                    importer: entry.clone(),
                    module: module.clone(),
                })?;
            // Inspection checked only the current command's prefix, NOT its
            // body or later commands. Never search those unchecked bytes.
            let source = if module == entry {
                let header = modules::parse_source_header(input.source).map_err(|error| {
                    SourceModuleCheckError::Header {
                        module: module.clone(),
                        error,
                    }
                })?;
                let commands =
                    fln_parse::command_scope::partition(&input.source[header.body_start.0..])
                        .map_err(|error| SourceModuleCheckError::Header {
                            module: module.clone(),
                            error: error.with_original_offset(header.body_start),
                        })?;
                let end = commands
                    .iter()
                    .rev()
                    .find(|(start, _)| header.body_start.0 + start.0 <= offset)
                    .map_or(header.body_start.0, |(start, _)| {
                        header.body_start.0 + start.0
                    });
                &input.source[..end]
            } else {
                input.source
            };
            let origins = match self
                .declaration_origins(inputs, module, source, environment, &mut budget)
                .map_err(|error| match error {
                    SourceModuleCheckError::Limit {
                        resource: "document symbol commands",
                        limit: bound,
                    } => limit("definition commands", bound),
                    SourceModuleCheckError::Limit {
                        resource: "document symbol syntax",
                        limit: bound,
                    } => limit("definition source syntax", bound),
                    error => error,
                })? {
                Outcome::Complete(origins) => origins,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            for origin in origins {
                if &origin.name != target {
                    continue;
                }
                let range = origin.symbol.selection_range;
                let text = std::str::from_utf8(input.source).map_err(|_| {
                    source_error(
                        module,
                        0,
                        range.start,
                        "definition source is not UTF-8".into(),
                    )
                })?;
                if range.is_empty() || text.get(range.clone()).is_none() || found.is_some() {
                    return Err(source_error(
                        module,
                        0,
                        range.start,
                        "definition location is invalid or ambiguous".into(),
                    ));
                }
                found = Some(SourceDefinition {
                    name: origin.name,
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
