//! Syntax-based semantic highlighting from the pin's original parser trees.
//! Identifier spellings never stand in for elaborator resolution. In particular,
//! global constants and unresolved locals do not become guessed variable tokens.
use super::super::grammar::{Resolution, SourceGrammar};
use super::symbols::{observe_scope, source_closure, source_error};
use super::*;
use fln_parse::command_scope::ScopeCommand;
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;
use std::ops::Range;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticTokenKind {
    Keyword,
    Property,
    SorryLike,
}

/// Original UTF-8 source bytes, never normalized parser coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSemanticToken {
    pub range: Range<usize>,
    pub kind: SemanticTokenKind,
}

#[derive(Debug, Clone, Copy)]
pub struct SemanticTokenLimits {
    pub max_source_bytes: usize,
    pub max_modules: usize,
    pub max_commands: usize,
    pub max_syntax_nodes: usize,
    pub max_tokens: usize,
}

impl Default for SemanticTokenLimits {
    fn default() -> Self {
        Self {
            max_source_bytes: 1024 * 1024,
            max_modules: 256,
            max_commands: 4096,
            max_syntax_nodes: 100_000,
            max_tokens: 32_768,
        }
    }
}

fn limit(resource: &'static str, limit: usize) -> SourceModuleCheckError {
    SourceModuleCheckError::Limit { resource, limit }
}

impl SourceModuleSession {
    /// Highlight the exact checked document with its import and lexical grammar.
    /// This syntax slice covers keywords, tactic sorry-like atoms and named field
    /// projections. It does not claim elaboration-based local-variable coverage.
    pub fn semantic_tokens(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
    ) -> Result<Outcome<Vec<SourceSemanticToken>>, SourceModuleCheckError> {
        self.semantic_tokens_with_limits(inputs, entry, SemanticTokenLimits::default())
    }

    pub fn semantic_tokens_with_limits(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        limits: SemanticTokenLimits,
    ) -> Result<Outcome<Vec<SourceSemanticToken>>, SourceModuleCheckError> {
        if inputs.len() > limits.max_modules {
            return Err(limit("semantic token modules", limits.max_modules));
        }
        let mut bytes = 0usize;
        for input in inputs {
            bytes = bytes
                .checked_add(input.source.len())
                .filter(|size| *size <= limits.max_source_bytes)
                .ok_or_else(|| limit("semantic token source bytes", limits.max_source_bytes))?;
        }
        match self.check(inputs, entry)? {
            Outcome::Complete(_) => {}
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(reason) => return Ok(Outcome::InternalFault(reason)),
        }
        let mut prefix_inputs = source_closure(inputs, entry)?;
        let input_index = prefix_inputs
            .iter()
            .position(|input| input.name == entry)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: entry.clone(),
            })?;
        let source = prefix_inputs[input_index].source;
        let parse_error = |error| SourceModuleCheckError::Header {
            module: entry.clone(),
            error,
        };
        let header = modules::parse_source_header(source).map_err(parse_error)?;
        prefix_inputs[input_index].source = &source[..header.body_start.0];
        let prefix = match self.check(&prefix_inputs, entry)? {
            Outcome::Complete(prefix) => prefix,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(reason) => return Ok(Outcome::InternalFault(reason)),
        };
        let mut grammar = SourceGrammar::for_engine(
            &prefix.checked.checked.engine,
            Some(entry),
            header.module_system,
        )
        .map_err(|error| source_error(entry, 0, 0, error.to_string()))?;
        let commands = grammar
            .enter(|| fln_parse::command_scope::partition(&source[header.body_start.0..]))
            .map_err(|error| parse_error(error.with_original_offset(header.body_start)))?;
        let mut collector = Collector {
            limits,
            nodes_left: limits.max_syntax_nodes,
            tokens: Vec::new(),
        };
        let original = fln_syntax::source::SourceText::from_utf8(source)
            .map_err(|error| source_error(entry, 0, 0, error.to_string()))?;
        let view = SourceView::of(&original);
        collector.collect(
            &fln_parse::command_scope::imports::parse_source_header_syntax(source)
                .map_err(parse_error)?,
            &view,
            0,
        )?;
        let mut scopes = super::super::scopes::Scopes::default();
        let mut queue: std::collections::VecDeque<_> = commands
            .into_iter()
            .map(|(start, command)| {
                SourceStep::Command(
                    (fln_parse::BytePos(header.body_start.0 + start.0), command),
                    true,
                )
            })
            .collect();
        let mut commands_left = limits.max_commands;
        while let Some(step) = queue.pop_front() {
            let index = limits.max_commands - commands_left;
            let (start, command) = match step {
                SourceStep::Scope(start, control) => {
                    observe_scope(&mut scopes, &mut grammar, control, entry, index, start.0)?;
                    continue;
                }
                SourceStep::Command(command, _) => {
                    commands_left = commands_left
                        .checked_sub(1)
                        .ok_or_else(|| limit("semantic token commands", limits.max_commands))?;
                    command
                }
            };
            let control = grammar
                .enter(|| fln_parse::command_scope::parse(command))
                .map_err(|error| parse_error(error.with_original_offset(start)))?;
            let original = fln_syntax::source::SourceText::from_utf8(command)
                .map_err(|error| source_error(entry, index, start.0, error.to_string()))?;
            let view = SourceView::of(&original);
            if let Some(control) = control {
                if let Some(syntax) = grammar
                    .enter(|| fln_parse::command_scope::trees::head_tree(command))
                    .map_err(|error| parse_error(error.with_original_offset(start)))?
                {
                    collector.collect(&syntax, &view, start.0)?;
                } else if !matches!(control, ScopeCommand::Trivia) {
                    return Err(source_error(
                        entry,
                        index,
                        start.0,
                        "scope command has no native highlighting syntax".into(),
                    ));
                }
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
                        observe_scope(&mut scopes, &mut grammar, control, entry, index, start.0)?;
                        None
                    }
                };
                if let Some(steps) = steps {
                    for step in steps.into_iter().rev() {
                        queue.push_front(step);
                    }
                }
                continue;
            }
            if let Some(syntax) = grammar
                .enter(|| fln_parse::command_scope::mutual::tree(command))
                .map_err(|error| parse_error(error.with_original_offset(start)))?
            {
                collector.collect(&syntax, &view, start.0)?;
            } else {
                let parsed = grammar
                    .enter(|| fln_parse::parse_source_command(command))
                    .map_err(|error| parse_error(error.with_original_offset(start)))?;
                collector.collect(parsed.syntax(), parsed.source_view(), start.0)?;
            }
            grammar
                .declare(command, |_| Resolution::Unchecked)
                .map_err(|error| source_error(entry, index, start.0, error.to_string()))?;
        }
        collector
            .tokens
            .sort_by_key(|token| (token.range.start, token.range.end));
        collector.tokens.dedup();
        Ok(Outcome::Complete(collector.tokens))
    }
}

struct Collector {
    limits: SemanticTokenLimits,
    nodes_left: usize,
    tokens: Vec<SourceSemanticToken>,
}

impl Collector {
    fn collect(
        &mut self,
        syntax: &Syntax,
        view: &SourceView,
        base: usize,
    ) -> Result<(), SourceModuleCheckError> {
        // Same syntax decisions as SemanticHighlighting.lean at the pin. Work
        // is iterative and charged across the entire document, including scopes.
        // Compare names directly: rendering a long custom kind at every node
        // would multiply work beyond the syntax-node budget.
        let no_highlight = [
            Name::from_components(["Lean", "Parser", "Term", "sorry"]),
            Name::from_components(["Lean", "Parser", "Term", "type"]),
            Name::from_components(["Lean", "Parser", "Term", "prop"]),
            Name::from_components(["antiquotName"]),
            Name::from_components(["Lean", "Parser", "Command", "plainDocComment"]),
            Name::from_components(["Lean", "Parser", "Command", "docComment"]),
            Name::from_components(["Lean", "Parser", "Command", "moduleDoc"]),
        ];
        let choice = Name::from_components(["choice"]);
        let projections = [
            Name::from_components(["Lean", "Parser", "Term", "proj"]),
            Name::from_components(["Lean", "Parser", "Term", "pipeProj"]),
        ];
        let mut pending = vec![(syntax, None)];
        while let Some((syntax, forced_kind)) = pending.pop() {
            self.nodes_left = self.nodes_left.checked_sub(1).ok_or_else(|| {
                limit("semantic token syntax nodes", self.limits.max_syntax_nodes)
            })?;
            match syntax {
                Syntax::Node { kind, args, .. } => {
                    if no_highlight.contains(kind) {
                        continue;
                    }
                    if kind == &choice {
                        if let Some(first) = args.first() {
                            pending.push((first, None));
                        }
                    } else if projections.contains(kind)
                        && args.len() == 3
                        && matches!(args[2], Syntax::Ident { .. })
                    {
                        pending.push((&args[2], Some(SemanticTokenKind::Property)));
                        pending.push((&args[0], None));
                    } else {
                        pending.extend(args.iter().rev().map(|child| (child, None)));
                    }
                }
                Syntax::Atom { val, .. } => {
                    let first = val.strip_prefix('#').unwrap_or(val).chars().next();
                    if first.is_some_and(fln_syntax::token::is_id_first) {
                        let kind = if matches!(val.as_str(), "sorry" | "admit" | "stop" | "#exit") {
                            SemanticTokenKind::SorryLike
                        } else {
                            SemanticTokenKind::Keyword
                        };
                        self.add(syntax, kind, view, base)?;
                    }
                }
                Syntax::Ident { .. } => {
                    if let Some(kind) = forced_kind {
                        self.add(syntax, kind, view, base)?;
                    }
                }
                Syntax::Missing => {}
            }
        }
        Ok(())
    }

    fn add(
        &mut self,
        syntax: &Syntax,
        kind: SemanticTokenKind,
        view: &SourceView,
        base: usize,
    ) -> Result<(), SourceModuleCheckError> {
        let (Some(start), Some(end)) = (syntax.info().pos(true), syntax.info().end_pos(true)) else {
            return Ok(());
        };
        if start.0 >= end.0 {
            return Ok(());
        }
        if self.tokens.len() >= self.limits.max_tokens {
            return Err(limit("semantic token count", self.limits.max_tokens));
        }
        self.tokens.push(SourceSemanticToken {
            range: base + view.to_original(start).0
                ..base + view.to_original(fln_parse::BytePos(end.0 - 1)).0 + 1,
            kind,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect(
        source: &str,
        limits: SemanticTokenLimits,
    ) -> Result<Vec<SourceSemanticToken>, SourceModuleCheckError> {
        let syntax = fln_parse::command_scope::trees::command_tree(source.as_bytes()).unwrap();
        let original = fln_syntax::source::SourceText::from_utf8(source.as_bytes()).unwrap();
        let mut collector = Collector {
            limits,
            nodes_left: limits.max_syntax_nodes,
            tokens: Vec::new(),
        };
        collector.collect(&syntax, &SourceView::of(&original), 0)?;
        Ok(collector.tokens)
    }

    #[test]
    fn syntax_tokens_do_not_guess_identifiers_comments_strings_or_sort_keywords() {
        let source = "/-- by def sorry -/\r\ndef «by» (x : Type) : Type := x";
        let tokens = collect(source, SemanticTokenLimits::default()).unwrap();
        assert_eq!(
            tokens,
            vec![SourceSemanticToken {
                range: source.find("\r\ndef").unwrap() + 2..source.find("\r\ndef").unwrap() + 5,
                kind: SemanticTokenKind::Keyword,
            }]
        );
        let source = "def message : String := \"def by sorry\"";
        let tokens = collect(source, SemanticTokenLimits::default()).unwrap();
        assert_eq!(tokens.len(), 1);
        assert_eq!(&source[tokens[0].range.clone()], "def");
    }

    #[test]
    fn limits_fail_without_a_partial_token_product() {
        let source = "def value : Nat := by exact 1";
        let limits = SemanticTokenLimits {
            max_tokens: 1,
            ..SemanticTokenLimits::default()
        };
        assert!(matches!(
            collect(source, limits),
            Err(SourceModuleCheckError::Limit {
                resource: "semantic token count",
                ..
            })
        ));
        let limits = SemanticTokenLimits {
            max_syntax_nodes: 1,
            ..SemanticTokenLimits::default()
        };
        assert!(matches!(
            collect(source, limits),
            Err(SourceModuleCheckError::Limit {
                resource: "semantic token syntax nodes",
                ..
            })
        ));
    }
}
