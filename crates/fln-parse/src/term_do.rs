//! Sequential do notation on the ordinary, nonrecursive term-frame stack.
//!
//! Every statement owns its original leaves. Immutable named lets, named
//! monadic binds, actions and terminal returns support both indentation and
//! explicit braces. Single-collection, immutable for loops reuse the same
//! frame stack; mutable, pattern and nonlocal control-flow forms still refuse.
use super::*;
use term_locals::word;

pub(super) struct Prefix {
    keyword: usize,
    baseline: usize,
    braces: Option<(usize, Option<usize>)>,
    items: Vec<Syntax>,
    statement: Statement,
    annotation: Option<Syntax>,
    collection: Option<Syntax>,
    phase: Phase,
}
#[derive(Clone, Copy)]
enum Statement {
    Action,
    Return(usize),
    For {
        keyword: usize,
        name: usize,
        in_at: usize,
        position: BytePos,
    },
    Binding {
        keyword: usize,
        name: usize,
        colon: Option<usize>,
        assignment: Option<usize>,
    },
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Annotation,
    Collection,
    Value,
    Done,
}

fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::ScalarValue,
    }
}
fn atom(leaves: &Leaves, at: usize, text: &str) -> Result<Syntax, NatDefinitionParseError> {
    Ok(Syntax::Atom {
        info: leaves.leaf(at)?.info(),
        val: text.to_owned(),
    })
}
fn column(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    let pos = tokens[at].extent.start();
    pos.0
        - view
            .normalized()
            .line_start(view.normalized().line_of(pos))
            .expect("token line")
            .0
}
fn newline(view: &SourceView, tokens: &[LexedToken], at: usize) -> bool {
    at > 0
        && view.normalized().line_of(tokens[at].extent.start())
            > view.normalized().line_of(tokens[at - 1].extent.end())
}
fn closing(tokens: &[LexedToken], at: usize) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind),
        Some(TokenKind::Symbol(s)) if matches!(s.as_str(), ")" | "]" | "}" | "⦄" | ","))
}

impl Prefix {
    pub(super) fn start(
        view: &SourceView,
        tokens: &[LexedToken],
        keyword: usize,
        cursor: &mut usize,
        end: usize,
    ) -> Result<Self, NatDefinitionParseError> {
        let braces = if word(tokens, *cursor, "{") {
            let open = *cursor;
            *cursor += 1;
            Some((open, None))
        } else {
            None
        };
        if *cursor >= end {
            return Err(refuse(view, tokens, *cursor));
        }
        let mut p = Self {
            keyword,
            baseline: column(view, tokens, *cursor),
            braces,
            items: Vec::new(),
            statement: Statement::Action,
            annotation: None,
            collection: None,
            phase: Phase::Value,
        };
        p.begin(view, tokens, cursor, end)?;
        Ok(p)
    }
    fn begin(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        cursor: &mut usize,
        end: usize,
    ) -> Result<(), NatDefinitionParseError> {
        if *cursor >= end || closing(tokens, *cursor) {
            return Err(refuse(view, tokens, *cursor));
        }
        self.annotation = None;
        self.collection = None;
        self.phase = Phase::Value;
        let at = *cursor;
        if word(tokens, at, "let") {
            let name = at + 1;
            if name >= end
                || !matches!(tokens[name].kind, TokenKind::Ident(_))
                || word(tokens, name, "mut")
                || word(tokens, name, "rec")
            {
                return Err(refuse(view, tokens, name));
            }
            let marker = at + 2;
            if marker >= end {
                return Err(refuse(view, tokens, marker));
            }
            let (colon, assignment) = if word(tokens, marker, ":") {
                self.phase = Phase::Annotation;
                (Some(marker), None)
            } else if word(tokens, marker, ":=")
                || word(tokens, marker, "←")
                || word(tokens, marker, "<-")
            {
                (None, Some(marker))
            } else {
                return Err(refuse(view, tokens, marker));
            };
            self.statement = Statement::Binding {
                keyword: at,
                name,
                colon,
                assignment,
            };
            *cursor = marker + 1;
        } else if word(tokens, at, "for") {
            let name = at + 1;
            let in_at = at + 2;
            if in_at >= end
                || !matches!(&tokens[name].kind, TokenKind::Ident(name)
                    if !name.is_anonymous() && name.parent().is_anonymous())
                || !word(tokens, in_at, "in")
            {
                return Err(refuse(view, tokens, name));
            }
            self.statement = Statement::For {
                keyword: at,
                name,
                in_at,
                position: original_position(view, tokens, at),
            };
            self.phase = Phase::Collection;
            *cursor = in_at + 1;
        } else if word(tokens, at, "return") {
            self.statement = Statement::Return(at);
            *cursor += 1;
        } else {
            // These belong to doElem, not ordinary term application. In
            // particular, parsing an if as a term would lose early-return scope.
            for unsupported in [
                "if", "match", "while", "repeat", "unless", "try", "break", "continue", "have",
                "let_expr",
            ] {
                if word(tokens, at, unsupported) {
                    return Err(refuse(view, tokens, at));
                }
            }
            self.statement = Statement::Action;
        }
        if *cursor >= end {
            return Err(refuse(view, tokens, *cursor));
        }
        Ok(())
    }
    pub(super) fn done(&self) -> bool {
        self.phase == Phase::Done
    }
    pub(super) fn closes_header(&self, tokens: &[LexedToken], at: usize) -> bool {
        match self.phase {
            Phase::Annotation => {
                word(tokens, at, ":=") || word(tokens, at, "←") || word(tokens, at, "<-")
            }
            Phase::Value => word(tokens, at, ";"),
            Phase::Collection => word(tokens, at, "do"),
            Phase::Done => false,
        }
    }
    fn item(
        &mut self,
        leaves: &Leaves,
        value: Syntax,
        semi: Option<usize>,
    ) -> Result<(), NatDefinitionParseError> {
        let element = match self.statement {
            Statement::Action => Syntax::node(parser_kind(&["Term", "doExpr"]), vec![value]),
            Statement::Return(at) => Syntax::node(
                parser_kind(&["Term", "doReturn"]),
                vec![atom(leaves, at, "return")?, null_node(vec![value])],
            ),
            Statement::For {
                keyword,
                name,
                in_at,
                position,
            } => {
                // The loop's `do` introduces a doSeq, not a new return scope.
                // Reuse the nested parser frame, then remove only its wrapper.
                let mut value = value;
                let Syntax::Node { kind, args, .. } = &mut value else {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: position,
                        expected: NatDefinitionExpectation::ScalarValue,
                    });
                };
                if *kind != parser_kind(&["Term", "do"]) || args.len() != 2 {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: position,
                        expected: NatDefinitionExpectation::ScalarValue,
                    });
                }
                let sequence = args.pop().expect("checked do sequence");
                let do_keyword = args.pop().expect("checked do keyword");
                let collection =
                    self.collection
                        .take()
                        .ok_or(NatDefinitionParseError::OutsideSeedGrammar {
                            at: position,
                            expected: NatDefinitionExpectation::ScalarValue,
                        })?;
                let declaration = Syntax::node(
                    parser_kind(&["Term", "doForDecl"]),
                    vec![
                        null_node(vec![]),
                        leaves.leaf(name)?,
                        atom(leaves, in_at, "in")?,
                        collection,
                    ],
                );
                Syntax::node(
                    parser_kind(&["Term", "doFor"]),
                    vec![
                        atom(leaves, keyword, "for")?,
                        null_node(vec![declaration]),
                        do_keyword,
                        sequence,
                    ],
                )
            }
            Statement::Binding {
                keyword,
                name,
                colon,
                assignment,
            } => {
                let assignment = assignment.expect("completed do binding header");
                let annotation = match (colon, self.annotation.take()) {
                    (Some(colon), Some(type_)) => null_node(vec![Syntax::node(
                        parser_kind(&["Term", "typeSpec"]),
                        vec![leaves.leaf(colon)?, type_],
                    )]),
                    (None, None) => null_node(vec![]),
                    _ => unreachable!("checked do annotation"),
                };
                let pure =
                    matches!(&leaves.leaf(assignment)?, Syntax::Atom { val, .. } if val == ":=");
                let config =
                    Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null_node(vec![])]);
                if pure {
                    let declaration = Syntax::node(
                        parser_kind(&["Term", "letIdDecl"]),
                        vec![
                            Syntax::node(parser_kind(&["Term", "letId"]), vec![leaves.leaf(name)?]),
                            null_node(vec![]),
                            annotation,
                            leaves.leaf(assignment)?,
                            value,
                        ],
                    );
                    Syntax::node(
                        parser_kind(&["Term", "doLet"]),
                        vec![
                            leaves.leaf(keyword)?,
                            null_node(vec![]),
                            config,
                            Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]),
                        ],
                    )
                } else {
                    let declaration = Syntax::node(
                        parser_kind(&["Term", "doIdDecl"]),
                        vec![
                            leaves.leaf(name)?,
                            annotation,
                            leaves.leaf(assignment)?,
                            Syntax::node(parser_kind(&["Term", "doExpr"]), vec![value]),
                        ],
                    );
                    Syntax::node(
                        parser_kind(&["Term", "doLetArrow"]),
                        vec![
                            leaves.leaf(keyword)?,
                            null_node(vec![]),
                            config,
                            declaration,
                        ],
                    )
                }
            }
        };
        self.items.push(Syntax::node(
            parser_kind(&["Term", "doSeqItem"]),
            vec![
                element,
                null_node(
                    semi.map(|at| leaves.leaf(at))
                        .transpose()?
                        .into_iter()
                        .collect(),
                ),
            ],
        ));
        Ok(())
    }
    pub(super) fn finish_header(
        mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        expression: Syntax,
        end: usize,
    ) -> Result<(Self, usize), NatDefinitionParseError> {
        if self.phase == Phase::Collection {
            if !word(tokens, at, "do") || at + 1 >= end {
                return Err(refuse(view, tokens, at));
            }
            let Statement::For { keyword, .. } = self.statement else {
                return Err(refuse(view, tokens, at));
            };
            if !word(tokens, at + 1, "{")
                && newline(view, tokens, at + 1)
                && column(view, tokens, at + 1) <= column(view, tokens, keyword)
            {
                return Err(refuse(view, tokens, at + 1));
            }
            self.collection = Some(expression);
            self.phase = Phase::Value;
            // Let the ordinary parser consume this original `do` token and
            // its entire sequence on a child heap frame.
            return Ok((self, at));
        }
        if self.phase == Phase::Annotation {
            self.annotation = Some(expression);
            let Statement::Binding { assignment, .. } = &mut self.statement else {
                unreachable!("binding annotation")
            };
            *assignment = Some(at);
            self.phase = Phase::Value;
            return Ok((self, at + 1));
        }
        if self.phase != Phase::Value {
            return Err(refuse(view, tokens, at));
        }
        let semi = word(tokens, at, ";").then_some(at);
        let mut next = at + usize::from(semi.is_some());
        let terminal = matches!(self.statement, Statement::Return(_));
        let binding = matches!(self.statement, Statement::Binding { .. });
        self.item(leaves, expression, semi)?;
        if let Some((_, close)) = &mut self.braces {
            if next < end && word(tokens, next, "}") {
                if binding {
                    return Err(refuse(view, tokens, next));
                }
                *close = Some(next);
                self.phase = Phase::Done;
                return Ok((self, next + 1));
            }
            if next >= end || closing(tokens, next) {
                return Err(refuse(view, tokens, next));
            }
        } else if next >= end
            || closing(tokens, next)
            || (newline(view, tokens, next) && column(view, tokens, next) < self.baseline)
        {
            if binding {
                return Err(refuse(view, tokens, next));
            }
            self.phase = Phase::Done;
            return Ok((self, next));
        }
        if terminal {
            return Err(refuse(view, tokens, next));
        }
        self.begin(view, tokens, &mut next, end)?;
        Ok((self, next))
    }
    pub(super) fn finish(
        mut self,
        leaves: &Leaves,
        value: Syntax,
    ) -> Result<(Syntax, usize), NatDefinitionParseError> {
        if self.braces.is_some_and(|(_, close)| close.is_none()) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: BytePos(0),
                expected: NatDefinitionExpectation::ClosingParenthesis,
            });
        }
        if self.phase != Phase::Done {
            if self.phase != Phase::Value || matches!(self.statement, Statement::Binding { .. }) {
                return Err(NatDefinitionParseError::OutsideSeedGrammar {
                    at: BytePos(0),
                    expected: NatDefinitionExpectation::ScalarValue,
                });
            }
            self.item(leaves, value, None)?;
        }
        let sequence = if let Some((open, Some(close))) = self.braces {
            Syntax::node(
                parser_kind(&["Term", "doSeqBracketed"]),
                vec![
                    leaves.leaf(open)?,
                    null_node(self.items),
                    leaves.leaf(close)?,
                ],
            )
        } else {
            Syntax::node(
                parser_kind(&["Term", "doSeqIndent"]),
                vec![null_node(self.items)],
            )
        };
        Ok((
            Syntax::node(
                parser_kind(&["Term", "do"]),
                vec![atom(leaves, self.keyword, "do")?, sequence],
            ),
            self.keyword,
        ))
    }
}

/// Only body prefixes may close before the next do statement. Parentheses,
/// annotations and records retain their own layout and delimiters. Explicit
/// braces, unlike indentation, cannot be closed by an offside token.
pub(super) fn layout(
    view: &SourceView,
    tokens: &[LexedToken],
    frames: &[BoundedTermFrame],
    at: usize,
) -> Option<bool> {
    if frames
        .last()
        .is_some_and(|f| matches!(&f.prefix, Some(term_locals::Prefix::Do(p)) if p.done()))
    {
        return Some(true);
    }
    if frames
        .last()
        .is_none_or(|f| f.application.is_empty() && f.operands.is_empty())
    {
        return None;
    }
    for frame in frames.iter().rev() {
        if frame.negation.is_some() {
            continue;
        }
        match frame.prefix.as_ref()? {
            term_locals::Prefix::Do(p)
                if !matches!(p.phase, Phase::Annotation | Phase::Collection) =>
            {
                if p.braces.is_some() && word(tokens, at, "}") {
                    return Some(false);
                }
                if !newline(view, tokens, at) || word(tokens, at, ";") || closing(tokens, at) {
                    return None;
                }
                let col = column(view, tokens, at);
                return (col <= p.baseline).then_some(p.braces.is_none() && col < p.baseline);
            }
            p if p.body() => {}
            _ => return None,
        }
    }
    None
}

#[cfg(test)]
mod for_tests {
    use super::*;

    fn kinds(syntax: &Syntax, leaf: &str) -> usize {
        let expected = parser_kind(&["Term", leaf]);
        let mut work = vec![syntax];
        let mut count = 0;
        while let Some(syntax) = work.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                count += usize::from(kind == &expected);
                work.extend(args);
            }
        }
        count
    }

    #[test]
    fn for_body_is_a_sequence_not_a_nested_return_scope() {
        let source = "def walk : Nat := do\n  for x in xs do\n    visit x\n  return 7";
        let parsed = parse_definition(source.as_ref()).expect("immutable loop syntax");
        assert_eq!(kinds(&parsed.syntax, "do"), 1);
        assert_eq!(kinds(&parsed.syntax, "doFor"), 1);
        assert_eq!(kinds(&parsed.syntax, "doForDecl"), 1);
        assert_eq!(kinds(&parsed.syntax, "doReturn"), 1);
    }

    #[test]
    fn nested_loops_and_explicit_do_keep_distinct_scopes() {
        let source = "def walk : Nat := do\n  for x in xs do\n    for y in ys do\n      visit (do { return x }) y\n  return 7";
        let parsed = parse_definition(source.as_ref()).expect("nested loops");
        assert_eq!(kinds(&parsed.syntax, "doFor"), 2);
        assert_eq!(kinds(&parsed.syntax, "do"), 2);
        assert_eq!(kinds(&parsed.syntax, "doReturn"), 2);
    }

    #[test]
    fn braced_loops_retain_the_outer_continuation() {
        let source = "def walk : Nat := do { for x in xs do { visit x }; after; return 7 }";
        let parsed = parse_definition(source.as_ref()).expect("braced loop");
        assert_eq!(kinds(&parsed.syntax, "doFor"), 1);
        assert_eq!(kinds(&parsed.syntax, "doSeqBracketed"), 2);
        assert_eq!(kinds(&parsed.syntax, "doExpr"), 2);
        assert_eq!(kinds(&parsed.syntax, "doReturn"), 1);
    }

    #[test]
    fn collection_parentheses_protect_a_nested_do_from_the_header_delimiter() {
        let source =
            "def walk : Nat := do { for x in (do { return xs }) do { visit x }; return 7 }";
        let parsed = parse_definition(source.as_ref()).expect("parenthesized collection");
        assert_eq!(kinds(&parsed.syntax, "do"), 2);
        assert_eq!(kinds(&parsed.syntax, "doFor"), 1);
    }

    #[test]
    fn crlf_comments_and_a_non_bmp_binder_do_not_change_loop_structure() {
        let source = "def walk : Nat := do\r\n  for «𝒙» in xs /- collection -/ do\r\n    visit «𝒙» -- one action\r\n  return 7";
        let parsed = parse_definition(source.as_ref()).expect("original source coordinates");
        assert_eq!(kinds(&parsed.syntax, "doFor"), 1);
        assert_eq!(kinds(&parsed.syntax, "do"), 1);
    }

    #[test]
    fn malformed_or_unsupported_loop_headers_never_become_actions() {
        for source in [
            "def walk : Nat := do { for x xs do { visit x }; return 7 }",
            "def walk : Nat := do { for x in xs; return 7 }",
            "def walk : Nat := do { for x in xs do {}; return 7 }",
            "def walk : Nat := do { for (x, y) in xs do { visit x }; return 7 }",
            "def walk : Nat := do { for h : x in xs do { visit x }; return 7 }",
            "def walk : Nat := do { for x in xs, y in ys do { visit x }; return 7 }",
            "def walk : Nat := do { for x in xs do { break }; return 7 }",
            "def walk : Nat := do { for x in xs do { continue }; return 7 }",
            "def walk : Nat := do { for x in xs do { let mut y := x; visit y }; return 7 }",
        ] {
            assert!(parse_definition(source.as_ref()).is_err(), "{source}");
        }
    }

    #[test]
    fn missing_indented_body_does_not_consume_the_enclosing_continuation() {
        let source = "def walk : Nat := do\r\n  for x in xs do\r\n  return 7";
        let error = parse_definition(source.as_ref()).expect_err("missing loop body");
        assert_eq!(
            error.primary_offset(),
            Some(BytePos(source.find("return").unwrap()))
        );
    }
}
