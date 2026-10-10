//! Sequential do notation on the ordinary, nonrecursive term-frame stack.
//!
//! Every statement owns its original leaves. Immutable named and pattern lets,
//! monadic binds, actions and terminal returns support both indentation and
//! explicit braces. Single-collection, immutable for loops reuse the same
//! frame stack, including terminal break/continue. Mutable bindings, pattern
//! iteration and nonlocal returns from loops remain separate elaboration work.
use super::*;
use term_locals::word;
mod conditional;
mod fallback;

pub(super) struct Prefix {
    keyword: usize,
    sequence_only: bool,
    baseline: usize,
    braces: Option<(usize, Option<usize>)>,
    items: Vec<Syntax>,
    statement: Statement,
    annotation: Option<Syntax>,
    collection: Option<Syntax>,
    pattern: Option<Syntax>,
    /// A local function's binders (`let f {n : Nat} (x : Nat) := …`), read where its header ends.
    binders: Option<Vec<Syntax>>,
    phase: Phase,
}
#[derive(Clone, Copy)]
enum Statement {
    Action,
    Try {
        position: BytePos,
    },
    Conditional {
        position: BytePos,
    },
    Match {
        position: BytePos,
    },
    Return(usize),
    Unless {
        keyword: usize,
        position: BytePos,
    },
    /// `"while " (ident " : ")? termBeforeDo " do " doSeq` (`Term.doWhile`, `Init/While.lean`),
    /// its condition a `doIfProp`: the keyword and the evidence name, if any.
    While {
        keyword: usize,
        name: Option<usize>,
        position: BytePos,
    },
    Jump {
        keyword: usize,
        is_break: bool,
        position: BytePos,
    },
    For {
        keyword: usize,
        name: usize,
        witness: Option<usize>,
        in_at: usize,
        position: BytePos,
    },
    Binding {
        keyword: usize,
        name: usize,
        colon: Option<usize>,
        assignment: Option<usize>,
        /// `let mut x …`: the `mut`, the `doLet`/`doLetArrow` slot the elaborator refuses.
        mutable: Option<usize>,
        /// `x := e` / `x ← e` (`doReassign`, `doReassignArrow`): `keyword` is the name.
        reassign: bool,
        /// `let rec`'s `rec` (`doLetRec`).
        recursive: Option<usize>,
    },
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Pattern,
    /// A `for`'s bracketed binder, a term up to its `in`.
    ForBinder,
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
/// The bracket closing the one opened at `open`, before `end`.
fn closing_bracket(tokens: &[LexedToken], open: usize, end: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (at, token) in tokens.iter().enumerate().take(end).skip(open) {
        if let TokenKind::Symbol(s) = &token.kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        return Some(at);
                    }
                }
                _ => {}
            }
        }
    }
    None
}
fn closing(tokens: &[LexedToken], at: usize) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind),
        Some(TokenKind::Symbol(s)) if matches!(s.as_str(), ")" | "]" | "}" | "⦄" | "⟩" | ","))
}

// A bare `do` in do-element position shares the surrounding control scope.
// Parenthesized terms retain their wrapper and therefore remain doExpr terms.
fn do_element(mut value: Syntax) -> Syntax {
    if let Syntax::Node { kind, .. } = &mut value
        && kind == &parser_kind(&["Term", "do"])
    {
        *kind = parser_kind(&["Term", "doNested"]);
        value
    } else {
        arrow_element(value)
    }
}

/// A `doIf` or `doMatch` the planner read right after a `←` (`leftArrow doElemParser`) is already
/// a do element; any other term is a `doExpr`.
pub(super) fn arrow_element(value: Syntax) -> Syntax {
    if value.kind() == Some(&parser_kind(&["Term", "doIf"]))
        || value.kind() == Some(&parser_kind(&["Term", "doMatch"]))
    {
        value
    } else {
        Syntax::node(parser_kind(&["Term", "doExpr"]), vec![value])
    }
}

fn is_failure_value(syntax: &Syntax) -> bool {
    syntax.kind() == Some(&parser_kind(&["Term", "nativeDoFailureValue"]))
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
            sequence_only: false,
            baseline: column(view, tokens, *cursor),
            braces,
            items: Vec::new(),
            statement: Statement::Action,
            annotation: None,
            collection: None,
            pattern: None,
            binders: None,
            phase: Phase::Value,
        };
        p.begin(view, tokens, cursor, end)?;
        Ok(p)
    }
    /// Parse a branch directly as a sequence, carrying the original leaves.
    /// There is no inserted `do` token and no new source return scope.
    pub(super) fn branch(
        view: &SourceView,
        tokens: &[LexedToken],
        cursor: &mut usize,
        end: usize,
    ) -> Result<Self, NatDefinitionParseError> {
        let mut prefix = Self::start(view, tokens, *cursor, cursor, end)?;
        prefix.sequence_only = true;
        Ok(prefix)
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
        self.pattern = None;
        self.binders = None;
        self.phase = Phase::Value;
        let at = *cursor;
        // `doHave := "have" letConfig letDecl`: `doLet`'s declaration, with no `mut` and no arrow.
        let have = word(tokens, at, "have");
        if word(tokens, at, "let") || have {
            let mutable = (!have && word(tokens, at + 1, "mut")).then_some(at + 1);
            // `doLetRec := group("let " "rec ") letRecDecls`: one declaration here.
            let recursive =
                (!have && mutable.is_none() && word(tokens, at + 1, "rec")).then_some(at + 1);
            let name = at + 1 + usize::from(mutable.is_some()) + usize::from(recursive.is_some());
            if name >= end || word(tokens, name, "mut") || word(tokens, name, "rec") {
                return Err(refuse(view, tokens, name));
            }
            // `have : T := v` binds `this` (`letId`'s `hygieneInfo`): the binding's name is then
            // the keyword itself.
            let anonymous = have && (word(tokens, name, ":") || word(tokens, name, ":="));
            let (name, marker) = if anonymous {
                (at, name)
            } else {
                (name, name + 1)
            };
            let named = anonymous
                || (matches!(tokens[name].kind, TokenKind::Ident(_))
                    && (word(tokens, marker, ":")
                        || word(tokens, marker, ":=")
                        || (!have && (word(tokens, marker, "←") || word(tokens, marker, "<-")))));
            if !named {
                // `let mut` binds a name here; a mutable pattern is not read.
                if mutable.is_some() {
                    return Err(refuse(view, tokens, name));
                }
                // Parse the complete pattern on the ordinary heap term frame.
                // Parentheses keep inner delimiters out of this header phase.
                self.statement = Statement::Binding {
                    keyword: at,
                    name,
                    colon: None,
                    assignment: None,
                    mutable: None,
                    reassign: false,
                    recursive,
                };
                self.phase = Phase::Pattern;
                *cursor = name;
                return Ok(());
            }
            if recursive.is_some() && (word(tokens, marker, "←") || word(tokens, marker, "<-")) {
                return Err(refuse(view, tokens, marker));
            }
            let (colon, assignment) = if word(tokens, marker, ":") {
                self.phase = Phase::Annotation;
                (Some(marker), None)
            } else {
                (None, Some(marker))
            };
            self.statement = Statement::Binding {
                keyword: at,
                name,
                colon,
                assignment,
                mutable,
                reassign: false,
                recursive,
            };
            *cursor = marker + 1;
        } else if word(tokens, at, "for")
            && (word(tokens, at + 1, "⟨") || word(tokens, at + 1, "("))
        {
            // `doForDecl := (atomic(ident " : "))? termParser " in " …`: a bracketed binder is a
            // pattern, read as a term up to its `in` (`for ⟨a, b⟩ in l do`).
            self.statement = Statement::For {
                keyword: at,
                name: at + 1,
                witness: None,
                in_at: at + 1,
                position: original_position(view, tokens, at),
            };
            self.phase = Phase::ForBinder;
            *cursor = at + 1;
        } else if word(tokens, at, "for") {
            let mut name = at + 1;
            let witness = if word(tokens, name + 1, ":") {
                if !matches!(tokens.get(name).map(|token| &token.kind),
                    Some(TokenKind::Ident(name))
                        if !name.is_anonymous() && name.parent().is_anonymous())
                {
                    return Err(refuse(view, tokens, name));
                }
                let witness = name;
                name += 2;
                Some(witness)
            } else {
                None
            };
            let in_at = name + 1;
            if in_at >= end
                || !(matches!(&tokens[name].kind, TokenKind::Ident(name)
                    if !name.is_anonymous() && name.parent().is_anonymous())
                    || word(tokens, name, "_"))
                || !word(tokens, in_at, "in")
            {
                return Err(refuse(view, tokens, name));
            }
            self.statement = Statement::For {
                keyword: at,
                name,
                witness,
                in_at,
                position: original_position(view, tokens, at),
            };
            self.phase = Phase::Collection;
            *cursor = in_at + 1;
        } else if word(tokens, at, "unless") {
            self.statement = Statement::Unless {
                keyword: at,
                position: original_position(view, tokens, at),
            };
            self.phase = Phase::Collection;
            *cursor = at + 1;
        } else if word(tokens, at, "while") {
            let name = (matches!(
                tokens.get(at + 1).map(|t| &t.kind),
                Some(TokenKind::Ident(_))
            ) && word(tokens, at + 2, ":"))
            .then_some(at + 1);
            self.statement = Statement::While {
                keyword: at,
                name,
                position: original_position(view, tokens, at),
            };
            self.phase = Phase::Collection;
            *cursor = at + 1 + if name.is_some() { 2 } else { 0 };
        } else if word(tokens, at, "match") {
            self.statement = Statement::Match {
                position: original_position(view, tokens, at),
            };
        } else if word(tokens, at, "try") {
            self.statement = Statement::Try {
                position: original_position(view, tokens, at),
            };
        } else if word(tokens, at, "if") {
            // The compound planner owns the explicit-else conditional. Its
            // branches are reclassified as do elements after that single parse.
            self.statement = Statement::Conditional {
                position: original_position(view, tokens, at),
            };
        } else if word(tokens, at, "break") || word(tokens, at, "continue") {
            // Leave the keyword on the ordinary term frame (the driver pushes its
            // leaf: see `jump_keyword`). `item` requires that frame to contain
            // exactly this original leaf, so a jump cannot swallow an argument,
            // ascription or trailing expression.
            self.statement = Statement::Jump {
                keyword: at,
                is_break: word(tokens, at, "break"),
                position: original_position(view, tokens, at),
            };
        } else if word(tokens, at, "return") {
            self.statement = Statement::Return(at);
            *cursor += 1;
        } else if matches!(&tokens[at].kind, TokenKind::Ident(_))
            && at + 1 < end
            && (word(tokens, at + 1, ":=")
                || word(tokens, at + 1, "←")
                || word(tokens, at + 1, "<-"))
        {
            // `doReassign := letIdDeclNoBinders`, `doReassignArrow := doIdDecl`: a mutable
            // variable's update, which the elaborator refuses.
            self.statement = Statement::Binding {
                keyword: at,
                name: at,
                colon: None,
                assignment: Some(at + 1),
                mutable: None,
                reassign: true,
                recursive: None,
            };
            *cursor = at + 2;
        } else if (word(tokens, at, "(") || word(tokens, at, "⟨"))
            && closing_bracket(tokens, at, end).is_some_and(|close| {
                word(tokens, close + 1, ":=")
                    || word(tokens, close + 1, "←")
                    || word(tokens, close + 1, "<-")
            })
        {
            // `doReassign := letIdDeclNoBinders <|> letPatDecl` and `doReassignArrow := doIdDecl
            // <|> doPatDecl`: a pattern's update (`(a, b) := e`), its pattern read on the heap
            // frame up to the assignment, as a `let` pattern is.
            self.statement = Statement::Binding {
                keyword: at,
                name: at,
                colon: None,
                assignment: None,
                mutable: None,
                reassign: true,
                recursive: None,
            };
            self.phase = Phase::Pattern;
        } else {
            // These belong to doElem, not ordinary term application. Unsupported
            // control forms must not be laundered into calls to user declarations.
            for unsupported in ["repeat", "catch", "finally", "let_expr"] {
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
    /// The token index of the `break`/`continue` this element is, if it is a jump. Both are
    /// builtin tokens at the pin (`doBreak`, `doContinue`), so the ordinary term frame cannot
    /// read them as an identifier leaf; the driver hands the keyword to the frame itself.
    pub(super) fn jump_keyword(&self) -> Option<usize> {
        match self.statement {
            Statement::Jump { keyword, .. } => Some(keyword),
            _ => None,
        }
    }
    pub(super) fn closes_header(&self, tokens: &[LexedToken], at: usize) -> bool {
        match self.phase {
            Phase::Pattern => {
                word(tokens, at, ":")
                    || word(tokens, at, ":=")
                    || word(tokens, at, "←")
                    || word(tokens, at, "<-")
            }
            Phase::Annotation => {
                word(tokens, at, ":=") || word(tokens, at, "←") || word(tokens, at, "<-")
            }
            Phase::ForBinder => word(tokens, at, "in"),
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
            Statement::Binding { .. } if is_failure_value(&value) => {
                self.failure_binding(leaves, value)?
            }
            Statement::Binding { .. } => self.binding_element(leaves, value)?,
            _ => self.nonbinding_element(leaves, value)?,
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
    // Dispatch before allocating the independent constructor frames. Refutable
    // bindings already sit inside a bounded compound-term parser invocation.
    #[inline(never)]
    fn nonbinding_element(
        &mut self,
        leaves: &Leaves,
        value: Syntax,
    ) -> Result<Syntax, NatDefinitionParseError> {
        Ok(match self.statement {
            Statement::Action => do_element(value),
            Statement::Try { position } => {
                if !matches!(&value, Syntax::Node {kind, args, ..}
                    if kind == &parser_kind(&["Term", "doTry"]) && args.len() == 4)
                {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: position,
                        expected: NatDefinitionExpectation::ScalarValue,
                    });
                }
                value
            }
            Statement::Conditional { position } => conditional::element(value, position)?,
            Statement::Match { position } => {
                if !matches!(&value, Syntax::Node { kind, args, .. }
                        if kind == &parser_kind(&["Term", "doMatch"]) && args.len() == 7)
                {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: position,
                        expected: NatDefinitionExpectation::MatchAlternative,
                    });
                }
                value
            }
            Statement::Return(at) => Syntax::node(
                parser_kind(&["Term", "doReturn"]),
                vec![atom(leaves, at, "return")?, null_node(vec![value])],
            ),
            Statement::Jump {
                keyword,
                is_break,
                position,
            } => {
                if value != leaves.leaf(keyword)? {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: position,
                        expected: NatDefinitionExpectation::EndOfCommand,
                    });
                }
                Syntax::node(
                    parser_kind(&["Term", if is_break { "doBreak" } else { "doContinue" }]),
                    vec![atom(
                        leaves,
                        keyword,
                        if is_break { "break" } else { "continue" },
                    )?],
                )
            }
            Statement::Unless { keyword, position } => {
                // The body is a doSeq in the surrounding return/loop scope,
                // not a nested do expression with independent control flow.
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
                let sequence = args.pop().expect("checked unless body");
                let do_keyword = args.pop().expect("checked unless do keyword");
                let condition =
                    self.collection
                        .take()
                        .ok_or(NatDefinitionParseError::OutsideSeedGrammar {
                            at: position,
                            expected: NatDefinitionExpectation::ScalarValue,
                        })?;
                Syntax::node(
                    parser_kind(&["Term", "doUnless"]),
                    vec![
                        atom(leaves, keyword, "unless")?,
                        condition,
                        do_keyword,
                        sequence,
                    ],
                )
            }
            Statement::While {
                keyword,
                name,
                position,
            } => {
                // As `unless`: the body is a doSeq of the surrounding scope.
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
                let sequence = args.pop().expect("checked while body");
                let do_keyword = args.pop().expect("checked while do keyword");
                let condition =
                    self.collection
                        .take()
                        .ok_or(NatDefinitionParseError::OutsideSeedGrammar {
                            at: position,
                            expected: NatDefinitionExpectation::ScalarValue,
                        })?;
                let binding = match name {
                    Some(at) => null_node(vec![leaves.leaf(at)?, leaves.leaf(at + 1)?]),
                    None => null_node(vec![]),
                };
                Syntax::node(
                    parser_kind(&["Term", "doWhile"]),
                    vec![
                        atom(leaves, keyword, "while")?,
                        Syntax::node(parser_kind(&["Term", "doIfProp"]), vec![binding, condition]),
                        do_keyword,
                        sequence,
                    ],
                )
            }
            Statement::For {
                keyword,
                name,
                witness,
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
                let witness = match witness {
                    Some(at) => null_node(vec![leaves.leaf(at)?, leaves.leaf(at + 1)?]),
                    None => null_node(vec![]),
                };
                let name = match self.pattern.take() {
                    Some(pattern) => pattern,
                    None => match leaves.leaf(name)? {
                        hole @ Syntax::Atom { .. } if matches!(&hole, Syntax::Atom { val, .. } if val == "_") => {
                            Syntax::node(parser_kind(&["Term", "hole"]), vec![hole])
                        }
                        name => name,
                    },
                };
                let declaration = Syntax::node(
                    parser_kind(&["Term", "doForDecl"]),
                    vec![witness, name, atom(leaves, in_at, "in")?, collection],
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
            Statement::Binding { .. } => unreachable!("bindings have a separate frame"),
        })
    }
    // Keep binding-construction temporaries off the shared statement frame.
    // A long do block still uses heap frames, including in an unoptimized build
    // with the same small native stack contract as the ordinary term parser.
    #[inline(never)]
    fn binding_element(
        &mut self,
        leaves: &Leaves,
        value: Syntax,
    ) -> Result<Syntax, NatDefinitionParseError> {
        let Statement::Binding {
            keyword,
            name,
            colon,
            assignment,
            mutable,
            reassign,
            recursive,
        } = self.statement
        else {
            unreachable!("binding element is dispatched only for a binding")
        };
        let mutable = match mutable {
            Some(at) => null_node(vec![atom(leaves, at, "mut")?]),
            None => null_node(vec![]),
        };
        let assignment = assignment.expect("completed do binding header");
        let annotation = match (colon, self.annotation.take()) {
            (Some(colon), Some(type_)) => null_node(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![leaves.leaf(colon)?, type_],
            )]),
            (None, None) => null_node(vec![]),
            _ => unreachable!("checked do annotation"),
        };
        let pure = matches!(&leaves.leaf(assignment)?, Syntax::Atom { val, .. } if val == ":=");
        if reassign && let Some(pattern) = self.pattern.take() {
            return Ok(if pure {
                Syntax::node(
                    parser_kind(&["Term", "doReassign"]),
                    vec![Syntax::node(
                        parser_kind(&["Term", "letPatDecl"]),
                        vec![
                            pattern,
                            null_node(vec![]),
                            annotation,
                            leaves.leaf(assignment)?,
                            value,
                        ],
                    )],
                )
            } else {
                Syntax::node(
                    parser_kind(&["Term", "doReassignArrow"]),
                    vec![Syntax::node(
                        parser_kind(&["Term", "doPatDecl"]),
                        vec![
                            pattern,
                            annotation,
                            leaves.leaf(assignment)?,
                            do_element(value),
                            null_node(vec![]),
                        ],
                    )],
                )
            });
        }
        if reassign {
            return Ok(if pure {
                Syntax::node(
                    parser_kind(&["Term", "doReassign"]),
                    vec![Syntax::node(
                        parser_kind(&["Term", "letIdDeclNoBinders"]),
                        vec![
                            Syntax::node(parser_kind(&["Term", "letId"]), vec![leaves.leaf(name)?]),
                            null_node(vec![]),
                            null_node(vec![]),
                            leaves.leaf(assignment)?,
                            value,
                        ],
                    )],
                )
            } else {
                Syntax::node(
                    parser_kind(&["Term", "doReassignArrow"]),
                    vec![Syntax::node(
                        parser_kind(&["Term", "doIdDecl"]),
                        vec![
                            leaves.leaf(name)?,
                            null_node(vec![]),
                            leaves.leaf(assignment)?,
                            do_element(value),
                        ],
                    )],
                )
            });
        }
        let config = Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null_node(vec![])]);
        // `finish_header` refuses an arrow after `have`.
        let have = matches!(&leaves.leaf(keyword)?, Syntax::Atom { val, .. } if val == "have");
        Ok(if pure {
            let (kind, binder, binders) = if let Some(binders) = self.binders.take() {
                (
                    "letIdDecl",
                    Syntax::node(parser_kind(&["Term", "letId"]), vec![leaves.leaf(name)?]),
                    null_node(binders),
                )
            } else if let Some(pattern) = self.pattern.take() {
                if pattern.kind() == Some(&parser_kind(&["Term", "hole"])) {
                    // Unlike doIdDecl, the pin's letId accepts `_` binders.
                    (
                        "letIdDecl",
                        Syntax::node(parser_kind(&["Term", "letId"]), vec![pattern]),
                        null_node(vec![]),
                    )
                } else if let Some((function, parameters)) = local_function(&pattern) {
                    // `let f x y := e` is `letIdDecl` with the names as its binders.
                    (
                        "letIdDecl",
                        Syntax::node(parser_kind(&["Term", "letId"]), vec![function]),
                        null_node(parameters),
                    )
                } else {
                    ("letPatDecl", pattern, null_node(vec![]))
                }
            } else {
                let binder = if have && name == keyword {
                    crate::hygiene_info_following(&leaves.leaf(keyword)?)
                } else {
                    leaves.leaf(name)?
                };
                (
                    "letIdDecl",
                    Syntax::node(parser_kind(&["Term", "letId"]), vec![binder]),
                    null_node(vec![]),
                )
            };
            let declaration = Syntax::node(
                parser_kind(&["Term", kind]),
                vec![binder, binders, annotation, leaves.leaf(assignment)?, value],
            );
            let declaration = Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]);
            if have {
                Syntax::node(
                    parser_kind(&["Term", "doHave"]),
                    vec![leaves.leaf(keyword)?, config, declaration],
                )
            } else if let Some(rec) = recursive {
                // `doLetRec := group("let " "rec ") letRecDecls`, `letRecDecl := (docComment)?
                // (attributes)? letDecl Termination.suffix`.
                let declaration = Syntax::node(
                    parser_kind(&["Term", "letRecDecl"]),
                    vec![
                        null_node(vec![]),
                        null_node(vec![]),
                        declaration,
                        crate::empty_termination_suffix(),
                    ],
                );
                Syntax::node(
                    parser_kind(&["Term", "doLetRec"]),
                    vec![
                        Syntax::node(
                            Name::from_components(["group"]),
                            vec![leaves.leaf(keyword)?, atom(leaves, rec, "rec")?],
                        ),
                        Syntax::node(
                            parser_kind(&["Term", "letRecDecls"]),
                            vec![null_node(vec![declaration])],
                        ),
                    ],
                )
            } else {
                Syntax::node(
                    parser_kind(&["Term", "doLet"]),
                    vec![leaves.leaf(keyword)?, mutable, config, declaration],
                )
            }
        } else {
            // `doIdDecl` takes no binders: an arrow reads the header as `doPatDecl`'s term.
            self.binders = None;
            let action = do_element(value);
            let declaration = if let Some(pattern) = self.pattern.take() {
                Syntax::node(
                    parser_kind(&["Term", "doPatDecl"]),
                    vec![
                        pattern,
                        annotation,
                        leaves.leaf(assignment)?,
                        action,
                        null_node(vec![]),
                    ],
                )
            } else {
                Syntax::node(
                    parser_kind(&["Term", "doIdDecl"]),
                    vec![
                        leaves.leaf(name)?,
                        annotation,
                        leaves.leaf(assignment)?,
                        action,
                    ],
                )
            };
            Syntax::node(
                parser_kind(&["Term", "doLetArrow"]),
                vec![leaves.leaf(keyword)?, mutable, config, declaration],
            )
        })
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
        // `doHave` binds with `:=` only.
        if (word(tokens, at, "←") || word(tokens, at, "<-"))
            && matches!(self.statement, Statement::Binding { keyword, reassign: false, recursive, .. }
                if word(tokens, keyword, "have") || recursive.is_some())
        {
            return Err(refuse(view, tokens, at));
        }
        if self.phase == Phase::ForBinder {
            let Statement::For { in_at, .. } = &mut self.statement else {
                return Err(refuse(view, tokens, at));
            };
            if at + 1 >= end || !word(tokens, at, "in") {
                return Err(refuse(view, tokens, at));
            }
            *in_at = at;
            self.pattern = Some(expression);
            self.phase = Phase::Collection;
            return Ok((self, at + 1));
        }
        if self.phase == Phase::Pattern {
            if at + 1 >= end
                || !(word(tokens, at, ":")
                    || word(tokens, at, ":=")
                    || word(tokens, at, "←")
                    || word(tokens, at, "<-"))
            {
                return Err(refuse(view, tokens, at));
            }
            let Statement::Binding {
                name,
                colon,
                assignment,
                mutable,
                reassign,
                ..
            } = &mut self.statement
            else {
                return Err(refuse(view, tokens, at));
            };
            // `letIdDecl := atomic(letIdLhs " := ") term` comes before `letPatDecl`: a name and
            // binders up to the `:` or `:=` (`letIdLhs := binderIdent letIdBinder* optType`) are a
            // local function, its binders read as a declaration's are, not a pattern applying the
            // name to a structure instance (`let f {n : Nat} (x : Nat) : T := e`).
            let binders = (matches!(tokens[*name].kind, TokenKind::Ident(_))
                && mutable.is_none()
                && !*reassign
                && !word(tokens, at, "←")
                && !word(tokens, at, "<-"))
            .then(|| crate::signature_binders(view, tokens, *name + 1, DefinitionGrammar::Scalar))
            .and_then(Result::ok)
            .filter(|(groups, after)| !groups.is_empty() && *after == at);
            // The pattern stays: a failure branch (`doLetElse`) or an arrow (`doPatDecl`) reads
            // the same header as a term.
            if let Some((groups, _)) = binders {
                self.binders = Some(crate::bounded_binder_syntax(
                    leaves,
                    view,
                    tokens,
                    groups,
                    DefinitionGrammar::Scalar,
                )?);
            }
            self.pattern = Some(expression);
            if word(tokens, at, ":") {
                *colon = Some(at);
                self.phase = Phase::Annotation;
            } else {
                *assignment = Some(at);
                self.phase = Phase::Value;
            }
            return Ok((self, at + 1));
        }
        if self.phase == Phase::Collection {
            if !word(tokens, at, "do") || at + 1 >= end {
                return Err(refuse(view, tokens, at));
            }
            let keyword = match self.statement {
                Statement::For { keyword, .. }
                | Statement::Unless { keyword, .. }
                | Statement::While { keyword, .. } => keyword,
                _ => return Err(refuse(view, tokens, at)),
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
            if at + 1 >= end
                || !(word(tokens, at, ":=") || word(tokens, at, "←") || word(tokens, at, "<-"))
            {
                return Err(refuse(view, tokens, at));
            }
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
        let terminal = matches!(
            self.statement,
            Statement::Return(_) | Statement::Jump { .. }
        );
        // A binding needs a continuation; a reassignment is a complete statement.
        let binding = matches!(
            self.statement,
            Statement::Binding {
                reassign: false,
                ..
            }
        ) && !is_failure_value(&expression);
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
            if self.phase != Phase::Value
                || (matches!(
                    self.statement,
                    Statement::Binding {
                        reassign: false,
                        ..
                    }
                ) && !is_failure_value(&value))
            {
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
        if self.sequence_only {
            return Ok((sequence, self.keyword));
        }
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
                if !matches!(
                    p.phase,
                    Phase::Pattern | Phase::ForBinder | Phase::Annotation | Phase::Collection
                ) =>
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

/// An application of a name to names or holes, `f x _`, read as a local function's head and its
/// binders (`letIdDecl`'s `letId` and `binderIdent*`).
fn local_function(pattern: &Syntax) -> Option<(Syntax, Vec<Syntax>)> {
    let Syntax::Node { kind, args, .. } = pattern else {
        return None;
    };
    if kind != &parser_kind(&["Term", "app"]) {
        return None;
    }
    let [
        function @ Syntax::Ident { .. },
        Syntax::Node {
            args: parameters, ..
        },
    ] = args.as_slice()
    else {
        return None;
    };
    parameters
        .iter()
        .all(|parameter| {
            matches!(parameter, Syntax::Ident { .. })
                || parameter.kind() == Some(&parser_kind(&["Term", "hole"]))
        })
        .then(|| (function.clone(), parameters.clone()))
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
    fn bare_nested_elements_and_parenthesized_terms_have_different_kinds() {
        for (body, ordinary, nested) in [
            ("let n ← do { return 1 }; return n", 1, 1),
            ("let n ← (do { return 1 }); return n", 2, 0),
            ("do { return 1 }", 1, 1),
        ] {
            let source = format!("def value : Nat := do {{ {body} }}");
            let parsed = parse_definition(source.as_bytes()).expect("nested do syntax");
            assert_eq!(kinds(&parsed.syntax, "do"), ordinary, "{source}");
            assert_eq!(kinds(&parsed.syntax, "doNested"), nested, "{source}");
        }
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
            "def walk : Nat := do { for h : : x in xs do { visit x }; return 7 }",
            "def walk : Nat := do { for x in xs, y in ys do { visit x }; return 7 }",
            "def walk : Nat := do { for x in xs do { break 1 }; return 7 }",
            "def walk : Nat := do { for x in xs do { continue action }; return 7 }",
        ] {
            assert!(parse_definition(source.as_ref()).is_err(), "{source}");
        }
        // A pattern binder is `doForDecl`'s term: the pin parses it (and fails in elaboration,
        // 2026-10-09).
        assert!(
            parse_definition(
                "def walk : Nat := do { for (x, y) in xs do { visit x }; return 7 }".as_ref()
            )
            .is_ok()
        );
        // A mutable binding in a loop body is the pin's syntax; the elaborator refuses it.
        assert!(
            parse_definition(
                "def walk : Nat := do { for x in xs do { let mut y := x; visit y }; return 7 }"
                    .as_ref()
            )
            .is_ok()
        );
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

#[cfg(test)]
mod control_tests {
    use super::*;

    fn count(syntax: &Syntax, label: &str) -> usize {
        let kind = parser_kind(&["Term", label]);
        let mut pending = vec![syntax];
        let mut result = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node {
                kind: found, args, ..
            } = syntax
            {
                result += usize::from(found == &kind);
                pending.extend(args);
            }
        }
        result
    }

    #[test]
    fn control_keywords_retain_original_leaves_and_enclosing_continuations() {
        for (keyword, kind) in [("break", "doBreak"), ("continue", "doContinue")] {
            for source in [
                format!(
                    "def run : Nat := do {{ for x in xs do {{ visit x; {keyword} }}; return 7 }}"
                ),
                format!(
                    "def run : Nat := do\r\n  for «𝒙» in xs do\r\n    visit «𝒙»\r\n    {keyword} -- control\r\n  return 7"
                ),
            ] {
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(count(parsed.syntax(), kind), 1);
                assert_eq!(count(parsed.syntax(), "doReturn"), 1);
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
                assert_eq!(
                    parsed.reconstruct_normalized().unwrap(),
                    parsed.source_view().normalized().as_bytes()
                );
            }
        }
    }

    #[test]
    fn escaped_control_names_are_ordinary_actions_not_jumps() {
        let source = "def run : Nat := do { «break»; «continue»; return 7 }";
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(count(parsed.syntax(), "doExpr"), 2);
        assert_eq!(count(parsed.syntax(), "doBreak"), 0);
        assert_eq!(count(parsed.syntax(), "doContinue"), 0);
    }

    #[test]
    fn terminal_controls_cannot_hide_unreachable_or_malformed_source() {
        for body in [
            "break; missing",
            "continue; missing",
            "break 1",
            "continue true",
            "break : Nat",
        ] {
            let source = format!("def run : Nat := do {{ for x in xs do {{ {body} }}; return 7 }}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod membership_tests;

#[cfg(test)]
mod unless_tests;
