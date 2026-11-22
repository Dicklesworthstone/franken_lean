//! Native `.ilean` metadata from checked source and actual identifier resolution.
//! Original source bytes own positions; imported checked entries own module names.
use super::symbols::{SourceOriginBudget, source_error};
use super::*;
use crate::{Ilean, IleanDeclInfo, IleanImport, IleanLocation, IleanRefIdent, IleanRefInfo};
use fln_parse::command_scope::ScopeCommand;
use fln_syntax::tree::Syntax;
use std::collections::BTreeMap;
use std::ops::Range;

// Preserve all three outcomes through the independent metadata passes.
macro_rules! complete {
    ($value:expr) => {
        match $value {
            Outcome::Complete(value) => value,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
    };
}

/// Independent metadata bounds in addition to the session's checking budget.
#[derive(Debug, Clone, Copy)]
pub struct SourceIleanLimits {
    pub source: DocumentSymbolLimits,
    pub max_references: usize,
    pub max_imported_declarations: usize,
    /// Aggregate rendered names, including repeated parent declaration strings.
    pub max_name_bytes: usize,
}

impl Default for SourceIleanLimits {
    fn default() -> Self {
        Self {
            source: DocumentSymbolLimits::default(),
            max_references: 100_000,
            max_imported_declarations: 1_000_000,
            max_name_bytes: 16 * 1024 * 1024,
        }
    }
}

impl SourceModuleSession {
    /// Produce the pin's editor metadata for a successfully checked source module.
    /// This is an explicit, bounded native declaration path. Unsupported reference
    /// forms are capability failures, never successful artifacts with missing refs.
    /// Use `from_lean_imports` for the ordinary Lean frontend's implicit Init policy.
    pub fn ilean(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        limits: SourceIleanLimits,
    ) -> Result<Outcome<Ilean>, SourceModuleCheckError> {
        if inputs.len() > limits.source.max_modules {
            return Err(limit("ilean modules", limits.source.max_modules));
        }
        let mut bytes = 0usize;
        for input in inputs {
            bytes = bytes
                .checked_add(input.source.len())
                .filter(|bytes| *bytes <= limits.source.max_source_bytes)
                .ok_or_else(|| limit("ilean source bytes", limits.source.max_source_bytes))?;
        }
        let source_index = inputs
            .iter()
            .position(|input| input.name == entry)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: entry.clone(),
            })?;
        let source = inputs[source_index].source;
        let text = std::str::from_utf8(source)
            .map_err(|error| source_error(entry, 0, 0, error.to_string()))?;
        let header = modules::parse_source_header(source).map_err(|error| {
            SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            }
        })?;
        let checked = complete!(self.check(inputs, entry)?);
        let environment = checked.checked.checked.engine.environment();
        let mut origin_budget = SourceOriginBudget::new(limits.source);
        let mut owners = self.imported_declaration_owners(limits.max_imported_declarations)?;
        let mut positions = Positions::new(text, limits.source.max_source_bytes.saturating_mul(4));
        let mut own_origins = Vec::new();
        for module in &checked.checked.module_order {
            let Some(input) = inputs.iter().find(|input| input.name == module) else {
                continue;
            };
            let origins = complete!(self.declaration_origins(
                inputs,
                module,
                input.source,
                environment,
                &mut origin_budget,
            )?);
            for origin in &origins {
                owners.insert(origin.name.clone(), module.clone());
            }
            if module == entry {
                own_origins = origins;
            }
        }
        let mut names = NameBudget::new(entry, limits.max_name_bytes);
        let mut result = Ilean {
            version: crate::ILEAN_VERSION,
            module: names.render(entry)?,
            direct_imports: header
                .import_specs
                .iter()
                .map(|import| {
                    Ok(IleanImport {
                        module: names.render(&import.module)?,
                        is_private: header.module_system && import.public_at.is_none(),
                        is_all: import.all_at.is_some(),
                        is_meta: import.meta_at.is_some(),
                    })
                })
                .collect::<Result<_, SourceModuleCheckError>>()?,
            references: BTreeMap::new(),
            decls: BTreeMap::new(),
        };
        let commands = fln_parse::command_scope::partition(&source[header.body_start.0..])
            .map_err(|error| SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            })?;
        if commands.len() > limits.source.max_commands {
            return Err(limit("ilean commands", limits.source.max_commands));
        }
        let mut prefix_inputs = inputs.to_vec();
        let mut syntax_left = limits.source.max_syntax_nodes;
        let mut references_left = limits.max_references;
        for (index, (start, command)) in commands.into_iter().enumerate() {
            let base = header.body_start.0 + start.0;
            if let Some(control) = fln_parse::command_scope::parse(command).map_err(|error| {
                SourceModuleCheckError::Header {
                    module: entry.clone(),
                    error,
                }
            })? {
                if matches!(
                    control,
                    ScopeCommand::Namespace(_)
                        | ScopeCommand::Section(_)
                        | ScopeCommand::SectionWithModifiers { .. }
                        | ScopeCommand::End(_)
                        | ScopeCommand::Open(_)
                        | ScopeCommand::OpenScoped(_)
                        | ScopeCommand::Universe(_)
                        | ScopeCommand::Trivia
                ) {
                    continue;
                }
                return Err(unsupported(
                    entry,
                    index,
                    base,
                    ".ilean references for this source scope command",
                ));
            }
            prefix_inputs[source_index].source = &source[..base];
            let prefix = complete!(self.check(&prefix_inputs, entry)?);
            let grammar = super::super::grammar::SourceGrammar::for_engine(
                &prefix.checked.checked.engine,
                Some(entry),
                header.module_system,
            )
            .map_err(|error| source_error(entry, index, base, error.to_string()))?;
            let parsed = grammar
                .enter(|| fln_parse::parse_source_command(command))
                .map_err(|error| SourceModuleCheckError::Header {
                    module: entry.clone(),
                    error,
                })?;
            if parsed.kind() != crate::SourceCommandKind::Definition
                || !supported_syntax(
                    parsed.syntax(),
                    &mut syntax_left,
                    limits.source.max_syntax_nodes,
                )?
            {
                return Err(unsupported(
                    entry,
                    index,
                    base,
                    ".ilean references for this declaration or term syntax",
                ));
            }
            let Some(origin) = own_origins.iter().find(|origin| {
                origin.symbol.selection_range.start >= base
                    && origin.symbol.selection_range.end <= base + command.len()
            }) else {
                return Err(unsupported(
                    entry,
                    index,
                    base,
                    ".ilean references for anonymous or generated declarations",
                ));
            };
            let mut scope = prefix
                .checked
                .checked
                .scope
                .for_declaration(parsed.syntax())
                .map_err(|error| source_error(entry, index, base, error.to_string()))?;
            let private_scope = scope.clone();
            let private_environment = prefix.checked.checked.engine.environment();
            let environment = if scope.exports_declaration() {
                scope.instance_scopes = prefix
                    .checked
                    .public_scope
                    .as_ref()
                    .ok_or_else(|| {
                        source_error(entry, index, base, "missing checked public scope".into())
                    })?
                    .instance_scopes
                    .clone();
                prefix.checked.public_environment.as_ref().ok_or_else(|| {
                    source_error(
                        entry,
                        index,
                        base,
                        "missing checked public environment".into(),
                    )
                })?
            } else {
                private_environment
            };
            let needs_worlds = scope.exports_declaration()
                && (fln_elab::source::is_theorem(parsed.syntax())
                    || fln_elab::source::is_instance(parsed.syntax())
                    || (!scope.expose_definitions
                        && fln_elab::source::is_definition_body(parsed.syntax())));
            let collected = if needs_worlds {
                fln_elab::source::inspect::public_declaration_references(
                    parsed.syntax(),
                    &fln_elab::source::TheoremWorlds {
                        public: environment,
                        private: private_environment,
                        public_scope: &scope,
                        private_scope: &private_scope,
                    },
                    self.inspection_kernel_budget(),
                    references_left,
                )
            } else {
                fln_elab::source::inspect::declaration_references(
                    parsed.syntax(),
                    environment,
                    self.inspection_kernel_budget(),
                    &scope,
                    references_left,
                )
            };
            let collected = source_records::elaboration_outcome(collected).map_err(|error| {
                SourceModuleCheckError::Source {
                    module: entry.clone(),
                    error: SourceCheckError::Command {
                        file: 0,
                        command: index,
                        offset: base,
                        error: Box::new(error),
                    },
                }
            })?;
            let Some(mut references) = complete!(collected) else {
                return Err(unsupported(
                    entry,
                    index,
                    base,
                    ".ilean references for field notation or recursive local references",
                ));
            };
            references.sort_by_key(|reference| (reference.range.start, reference.range.end));
            references.dedup_by(|right, left| right.name == left.name && right.range == left.range);
            references_left = references_left
                .checked_sub(references.len() + 1)
                .ok_or_else(|| limit("ilean references", limits.max_references))?;
            let is_axiom = matches!(parsed.syntax(), Syntax::Node { args, .. }
                if args.get(1).and_then(Syntax::kind)
                    == Some(&Name::from_components(["Lean", "Parser", "Command", "axiom"])));
            let parent = names.render(&origin.name)?;
            let definition_parent = if is_axiom {
                Some(names.copy(&parent)?)
            } else {
                None
            };
            let definition = location(
                &mut positions,
                origin.symbol.selection_range.clone(),
                definition_parent,
                entry,
            )?;
            result.references.insert(
                IleanRefIdent::Const {
                    module: names.copy(&result.module)?,
                    name: names.copy(&parent)?,
                },
                IleanRefInfo {
                    definition: Some(definition),
                    usages: Vec::new(),
                },
            );
            if is_axiom || !references.is_empty() {
                let range = location(&mut positions, origin.symbol.range.clone(), None, entry)?;
                let selection = location(
                    &mut positions,
                    origin.symbol.selection_range.clone(),
                    None,
                    entry,
                )?;
                result.decls.insert(
                    names.copy(&parent)?,
                    IleanDeclInfo {
                        range_start_line: range.start_line,
                        range_start_character: range.start_character,
                        range_end_line: range.end_line,
                        range_end_character: range.end_character,
                        selection_start_line: selection.start_line,
                        selection_start_character: selection.start_character,
                        selection_end_line: selection.end_line,
                        selection_end_character: selection.end_character,
                    },
                );
            }
            for reference in references {
                let owner = if let Some(owner) = owners.get(&reference.name) {
                    owner.clone()
                } else {
                    return Err(unsupported(
                        entry,
                        index,
                        base,
                        ".ilean ownership for seed constants or generated source declarations",
                    ));
                };
                let view = parsed.source_view();
                let range = base
                    + view
                        .to_original(fln_parse::BytePos(reference.range.start))
                        .0
                    ..base
                        + view
                            .to_original(fln_parse::BytePos(reference.range.end - 1))
                            .0
                        + 1;
                let usage = location(&mut positions, range, Some(names.copy(&parent)?), entry)?;
                result
                    .references
                    .entry(IleanRefIdent::Const {
                        module: names.render(&owner)?,
                        name: names.render(&reference.name)?,
                    })
                    .or_insert_with(|| IleanRefInfo {
                        definition: None,
                        usages: Vec::new(),
                    })
                    .usages
                    .push(usage);
            }
        }
        Ok(Outcome::Complete(result))
    }
}

fn limit(resource: &'static str, limit: usize) -> SourceModuleCheckError {
    SourceModuleCheckError::Limit { resource, limit }
}

struct NameBudget {
    module: Name,
    left: usize,
    limit: usize,
}

impl NameBudget {
    fn new(module: &Name, limit: usize) -> Self {
        Self {
            module: module.clone(),
            left: limit,
            limit,
        }
    }

    fn render(&mut self, name: &Name) -> Result<String, SourceModuleCheckError> {
        use fln_core::name::identifier::{NameRenderError, to_identifier_string};
        let text = to_identifier_string(name, self.left).map_err(|error| match error {
            NameRenderError::ByteBudgetExceeded { .. } => limit("ilean name bytes", self.limit),
            NameRenderError::OverflowedComponent => unsupported(
                &self.module,
                0,
                0,
                ".ilean names with overflowed numeric components",
            ),
        })?;
        self.left -= text.len();
        Ok(text)
    }

    fn copy(&mut self, text: &str) -> Result<String, SourceModuleCheckError> {
        self.left = self
            .left
            .checked_sub(text.len())
            .ok_or_else(|| limit("ilean name bytes", self.limit))?;
        Ok(text.to_owned())
    }
}

fn unsupported(
    module: &Name,
    command: usize,
    offset: usize,
    feature: &'static str,
) -> SourceModuleCheckError {
    SourceModuleCheckError::Source {
        module: module.clone(),
        error: SourceCheckError::Command {
            file: 0,
            command,
            offset,
            error: Box::new(EngineExecutionError::NotImplemented { feature }),
        },
    }
}

struct Positions<'a> {
    text: &'a str,
    lines: Vec<usize>,
    known: BTreeMap<usize, (u64, u64)>,
    left: usize,
    limit: usize,
}

impl<'a> Positions<'a> {
    fn new(text: &'a str, limit: usize) -> Self {
        let lines = std::iter::once(0)
            .chain(
                text.bytes()
                    .enumerate()
                    .filter_map(|(at, byte)| (byte == b'\n').then_some(at + 1)),
            )
            .collect();
        Self {
            text,
            lines,
            known: BTreeMap::new(),
            left: limit,
            limit,
        }
    }

    fn at(&mut self, offset: usize) -> Result<(u64, u64), SourceModuleCheckError> {
        if let Some(position) = self.known.get(&offset) {
            return Ok(*position);
        }
        let line = self.lines.partition_point(|start| *start <= offset) - 1;
        let start = self.lines[line];
        let (from, column) = self
            .known
            .range(start..=offset)
            .next_back()
            .map_or((start, 0), |(at, (_, column))| (*at, *column));
        self.left = self
            .left
            .checked_sub(offset - from)
            .ok_or_else(|| limit("ilean position bytes", self.limit))?;
        let position = (
            line as u64,
            column + self.text[from..offset].encode_utf16().count() as u64,
        );
        self.known.insert(offset, position);
        Ok(position)
    }
}

fn location(
    positions: &mut Positions<'_>,
    range: Range<usize>,
    parent_decl: Option<String>,
    module: &Name,
) -> Result<IleanLocation, SourceModuleCheckError> {
    let text = positions.text;
    if range.start > range.end
        || range.end > text.len()
        || !text.is_char_boundary(range.start)
        || !text.is_char_boundary(range.end)
    {
        return Err(source_error(
            module,
            0,
            range.start,
            "invalid original source reference range".into(),
        ));
    }
    let (start_line, start_character) = positions.at(range.start)?;
    let (end_line, end_character) = positions.at(range.end)?;
    Ok(IleanLocation {
        start_line,
        start_character,
        end_line,
        end_character,
        parent_decl,
    })
}

// These forms resolve their original global identifiers through the atom door,
// including terms elaborated by the checked proof driver. Tactic-selected lemmas,
// backtracking controls, patterns, record fields, nested declarations and user
// macros need their own source observations before they can join this artifact.
fn supported_syntax(
    syntax: &Syntax,
    left: &mut usize,
    limit_: usize,
) -> Result<bool, SourceModuleCheckError> {
    let mut pending = vec![syntax];
    while let Some(node) = pending.pop() {
        *left = left
            .checked_sub(1)
            .ok_or_else(|| limit("ilean syntax nodes", limit_))?;
        if let Syntax::Node { kind, args, .. } = node {
            let kind = kind.to_display_string();
            let allowed = kind == "null"
                || kind.is_empty()
                || matches!(kind.as_str(), "num" | "str" | "char" | "scientific")
                || kind
                    .strip_prefix("Lean.Parser.Command.")
                    .is_some_and(|kind| {
                        matches!(
                            kind,
                            "declaration"
                                | "declModifiers"
                                | "definition"
                                | "theorem"
                                | "abbrev"
                                | "opaque"
                                | "axiom"
                                | "declId"
                                | "declSig"
                                | "optDeclSig"
                                | "declValSimple"
                                | "visibility"
                                | "noncomputable"
                                | "unsafe"
                                | "private"
                                | "public"
                                | "protected"
                        )
                    })
                || kind.strip_prefix("Lean.Parser.Term.").is_some_and(|kind| {
                    matches!(
                        kind,
                        "app"
                            | "paren"
                            | "explicit"
                            | "explicitUniv"
                            | "type"
                            | "sort"
                            | "prop"
                            | "fun"
                            | "basicFun"
                            | "forall"
                            | "arrow"
                            | "typeSpec"
                            | "typeAscription"
                            | "binderIdent"
                            | "explicitBinder"
                            | "implicitBinder"
                            | "strictImplicitBinder"
                            | "instBinder"
                            | "simpleBinder"
                            | "hole"
                            | "syntheticHole"
                            | "let"
                            | "letDecl"
                            | "letIdDecl"
                            | "letDeclId"
                            | "letType"
                            | "letVal"
                            | "optType"
                            | "quotedName"
                            | "byTactic"
                    )
                })
                || kind
                    .strip_prefix("Lean.Parser.Tactic.")
                    .is_some_and(|kind| {
                        matches!(
                            kind,
                            "tacticSeq"
                                | "tacticSeq1Indented"
                                | "tacticSeqBracketed"
                                | "paren"
                                | "exact"
                                | "apply"
                                | "refine"
                                | "intro"
                                | "intros"
                                | "assumption"
                        )
                    })
                || kind.strip_prefix("Lean.Parser.Level.").is_some()
                || kind == "Lean.Parser.Termination.suffix"
                || matches!(
                    kind.as_str(),
                    "term_+_" | "term_-_" | "term_*_" | "term_=_" | "term_≠_"
                );
            if !allowed {
                return Ok(false);
            }
            pending.extend(args.iter().rev());
        }
    }
    Ok(true)
}
