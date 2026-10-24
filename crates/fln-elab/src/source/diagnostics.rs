//! The pin's panic/assert/unreachable expansions, with the original source site.
//! These produce ordinary applications. Inhabited synthesis and kernel admission
//! remain the same checks as for a written panicWithPosWithDecl application.
use super::*;
use fln_syntax::source::{ByteSpan, SourceInfo};

pub(super) fn is_diagnostic(syntax: &Syntax) -> bool {
    ["panic", "assert", "doAssert", "unreachable"]
        .iter()
        .any(|kind| syntax.kind() == Some(&parser_kind(&["Term", kind])))
}

fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}
fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}
fn root(name: &str) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        val: Name::from_components(std::iter::once("_root_").chain(name.split('.'))),
        preresolved: Vec::new(),
    }
}
fn app(head: Syntax, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", "app"]), vec![head, null(args)])
}
fn string(value: &str) -> Syntax {
    // Lean accepts literal Unicode, and exactly these short string escapes.
    let mut quoted = String::from("\"");
    for c in value.chars() {
        match c {
            '\\' => quoted.push_str("\\\\"),
            '"' => quoted.push_str("\\\""),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            c => quoted.push(c),
        }
    }
    quoted.push('"');
    Syntax::node(Name::from_components(["str"]), vec![atom(&quoted)])
}
fn number(value: usize) -> Syntax {
    Syntax::node(
        Name::from_components(["num"]),
        vec![atom(&value.to_string())],
    )
}

pub(super) fn assertion(condition: Syntax, body: Syntax, panic: Syntax) -> Syntax {
    Syntax::node(
        Name::from_components(["termIfThenElse"]),
        vec![
            atom("if"),
            condition,
            atom("then"),
            body,
            atom("else"),
            panic,
        ],
    )
}

impl Context {
    fn panic_application(
        &mut self,
        keyword: &Syntax,
        message: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let site = self.source_scope.source_site.as_ref().ok_or(
            NatDefinitionElabError::UnexpectedSyntax {
                expected: "original source location for panic!",
            },
        )?;
        let local = keyword
            .info()
            .pos(false)
            .ok_or(failure(SourceInferenceError::Scope))?;
        let at = site
            .syntax_offset(local)
            .ok_or(failure(SourceInferenceError::Scope))?;
        let position = site
            .view
            .normalized()
            .position_of(at)
            .ok_or(failure(SourceInferenceError::Scope))?;
        let module = self.source_scope.source_module.as_ref().map_or_else(
            || Name::anonymous().to_display_string(),
            Name::to_display_string,
        );
        let mut arguments = vec![string(&module)];
        let function = match &self.diagnostic_declaration {
            Some(name) => {
                arguments.push(string(&name.to_display_string()));
                "panicWithPosWithDecl"
            }
            None => "panicWithPos",
        };
        arguments.extend([
            number(position.line + 1),
            number(position.scalar_column),
            message,
        ]);
        Ok(app(root(function), arguments))
    }

    /// `Syntax.reprint` at macro expansion, before the pin's `updateLeading`.
    /// Our lossless parser redistributes trivia between neighboring leaves, so
    /// restore the condition's outer boundaries: no preceding leading trivia,
    /// and all whitespace/comments after its final token. Interior attachment
    /// boundaries already concatenate to the same bytes. Generated leaves use
    /// the pin's separating spaces.
    fn diagnostic_reprint(&mut self, syntax: &Syntax) -> Result<String, NatDefinitionElabError> {
        let mut pending = vec![syntax];
        let mut leaves = Vec::new();
        let mut text = String::new();
        while let Some(node) = pending.pop() {
            self.tick()?;
            match node {
                Syntax::Node { args, .. } => pending.extend(args.iter().rev()),
                Syntax::Missing => {}
                Syntax::Atom { .. } | Syntax::Ident { .. } => leaves.push(node),
            }
        }
        for (index, node) in leaves.iter().enumerate() {
            match node {
                Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                    if let SourceInfo::Original {
                        leading,
                        pos,
                        trailing,
                        end_pos,
                    } = info
                    {
                        let site = self
                            .source_scope
                            .source_site
                            .as_ref()
                            .ok_or(failure(SourceInferenceError::Scope))?;
                        let start = site
                            .syntax_offset(if index == 0 { *pos } else { leading.start() })
                            .ok_or(failure(SourceInferenceError::Scope))?;
                        let mut end = site
                            .syntax_offset(if index + 1 == leaves.len() {
                                *end_pos
                            } else {
                                trailing.end()
                            })
                            .ok_or(failure(SourceInferenceError::Scope))?;
                        if index + 1 == leaves.len() {
                            // Start before any block comment, since the parser's
                            // nice-trivia split can fall inside a multiline one.
                            end = fln_syntax::trivia::scan_trivia(site.view.normalized(), end)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                        }
                        let span = ByteSpan::new(start, end)
                            .ok_or(failure(SourceInferenceError::Scope))?;
                        text.push_str(
                            site.view
                                .normalized()
                                .span_str(span)
                                .ok_or(failure(SourceInferenceError::Scope))?,
                        );
                    } else {
                        text.push(' ');
                        match node {
                            Syntax::Atom { val, .. } => text.push_str(val),
                            Syntax::Ident { val, .. } => text.push_str(&val.to_display_string()),
                            _ => unreachable!(),
                        }
                        text.push(' ');
                    }
                }
                _ => unreachable!("only leaves are collected"),
            }
        }
        // The Reference parser reads crlfToLf(source); its reprint retains
        // comments and spacing from that normalized view, not the raw CR bytes.
        Ok(text.replace("\r\n", "\n"))
    }

    pub(super) fn expand_diagnostic_node(
        &mut self,
        mut node: Syntax,
        original: &Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if pattern || !is_diagnostic(&node) {
            return Ok(node);
        }
        let Syntax::Node { kind, args, .. } = &mut node else {
            unreachable!()
        };
        if *kind == parser_kind(&["Term", "panic"]) && args.len() == 2 {
            let message = args.pop().expect("panic message");
            return self.panic_application(&args[0], message);
        }
        if *kind == parser_kind(&["Term", "unreachable"]) && args.len() == 1 {
            return self.panic_application(&args[0], string("unreachable code has been reached"));
        }
        let statement = *kind == parser_kind(&["Term", "doAssert"]);
        if (*kind == parser_kind(&["Term", "assert"]) && args.len() == 4)
            || (statement && args.len() == 2)
        {
            let source = expect_node(
                original,
                kind,
                args.len(),
                "assert condition and continuation",
            )?;
            // The pin expands `"assertion violation: " ++ code`. Preserve the
            // ordinary dictionary search, including local HAppend instances.
            let message = app(
                root("HAppend.hAppend"),
                vec![
                    string("assertion violation: "),
                    string(&self.diagnostic_reprint(&source[1])?),
                ],
            );
            let body = if statement {
                None
            } else {
                let body = args.pop().expect("assert continuation");
                args.pop();
                Some(body)
            };
            let condition = args.pop().expect("assert condition");
            let panic = self.panic_application(&args[0], message)?;
            return Ok(match body {
                Some(body) => assertion(condition, body, panic),
                None => Syntax::node(
                    parser_kind(&["Term", "nativeDoAssert"]),
                    vec![condition, panic],
                ),
            });
        }
        Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "panic, assert, or unreachable term",
        })
    }
}
