//! List literals and anonymous constructors share the ordinary term parser's
//! explicit frame stack.
//!
//! The pin's `term[_]` (`[a, b]`) and `Term.anonymousCtor` (`⟨a, b⟩`) trees retain
//! brackets, commas (including an optional trailing comma: `sepBy … (allowTrailingSep
//! := true)` in both), comments and source positions. Constructor expansion belongs
//! to elaboration, not to this source-preserving parser.
use super::*;

mod patterns;
pub(super) use patterns::pattern;

#[derive(Default)]
pub(super) struct Lists {
    active: Vec<List>,
}

struct List {
    open: usize,
    bracket: Bracket,
    elements_and_separators: Vec<Syntax>,
    /// The indexed term of a [`Bracket::Index`], with where it starts.
    base: Option<(Syntax, usize)>,
    /// A [`Bracket::Subtype`]'s binder, optional type and `//`.
    subtype: Option<Subtype>,
}

struct Subtype {
    name: usize,
    colon: Option<usize>,
    separator: Option<usize>,
    type_: Option<Syntax>,
}

/// Which comma-separated bracket a [`List`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Bracket {
    /// `[a, b]`: `term[_]` (`Init/Data/List/Notation.lean`).
    List,
    /// `⟨a, b⟩`: `Lean.Parser.Term.anonymousCtor` (`Lean/Parser/Term.lean`).
    AnonymousCtor,
    /// `xs[i]`: `syntax:max term noWs "[" withoutPosition(term) "]" : term`
    /// (`Init/GetElem.lean`), one element and no separators.
    Index,
    /// `(a, b)`: `Lean.Parser.Term.tuple`, `"(" optional (term ", " sepBy1 term ", "
    /// (allowTrailingSep := true)) ")"` (`Lean/Parser/Term.lean`). Opened at its first comma.
    Tuple,
    /// `#[a, b]`: `syntax (name := «term#[_,]») "#[" withoutPosition(term,*,?) "]"`
    /// (`Init/Data/Array/Basic.lean`), a list literal's shape.
    Array,
    /// `#v[a, b]`: `Vector.«term#v[_,]»` (`Init/Data/Vector/Basic.lean`), the array literal's
    /// shape.
    Vector,
    /// `{x // p}` and `{x : T // p}`: `«term{_:_//_}»` (`Init/Core.lean`), the type ended by
    /// `//` and the predicate by `}`.
    Subtype,
}

impl Bracket {
    fn close(self) -> &'static str {
        match self {
            Bracket::List | Bracket::Index | Bracket::Array | Bracket::Vector => "]",
            Bracket::AnonymousCtor => "⟩",
            Bracket::Tuple => ")",
            Bracket::Subtype => "}",
        }
    }
    fn kind(self) -> Name {
        match self {
            Bracket::List => list_kind(),
            Bracket::Array => Name::from_components(["term#[_,]"]),
            Bracket::Vector => Name::from_components(["Vector", "term#v[_,]"]),
            Bracket::Subtype => Name::from_components(["term{_:_//_}"]),
            Bracket::AnonymousCtor => parser_kind(&["Term", "anonymousCtor"]),
            Bracket::Index => Name::from_components(["term__[_]"]),
            Bracket::Tuple => parser_kind(&["Term", "tuple"]),
        }
    }
}

fn frame(open: usize) -> BoundedTermFrame {
    BoundedTermFrame {
        record: None,
        ascription: None,
        open: Some(open),
        prefix: None,
        negation: None,
        application: Vec::new(),
        operands: Vec::new(),
        operators: Vec::new(),
    }
}

pub(super) fn list_kind() -> Name {
    Name::from_components(["term[_]"])
}

/// Whether the tokens at `left` and `right` touch: the pin's `noWs`.
fn touching(tokens: &[LexedToken], left: usize, right: usize) -> bool {
    tokens[left].extent.end() == tokens[right].extent.start()
}

impl Lists {
    pub(super) fn open(&mut self, frames: &mut Vec<BoundedTermFrame>, at: usize, bracket: Bracket) {
        self.active.push(List {
            open: at,
            bracket,
            elements_and_separators: Vec::new(),
            base: None,
            subtype: None,
        });
        frames.push(frame(at));
    }

    /// The first top-level comma of a plain parenthesized term makes it a tuple: its first
    /// element is finished, and the rest are read as the tuple's own separated elements.
    pub(super) fn open_tuple(
        &mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        frames: &mut Vec<BoundedTermFrame>,
        at: usize,
    ) -> Result<bool, NatDefinitionParseError> {
        let plain = frames.len() >= 2
            && frames.last().is_some_and(|frame| {
                frame.open.is_some_and(|open| {
                    matches!(&tokens[open].kind, TokenKind::Symbol(s) if s == "(")
                        && !self.active.last().is_some_and(|list| list.open == open)
                }) && frame.record.is_none()
                    && frame.ascription.is_none()
                    && frame.prefix.is_none()
                    && frame.negation.is_none()
                    && !(frame.application.is_empty()
                        && frame.operands.is_empty()
                        && frame.operators.is_empty())
            });
        if !plain {
            return Ok(false);
        }
        let current = frames.pop().expect("validated parenthesized frame");
        let open = current.open.expect("validated parenthesis");
        let first = finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
        self.active.push(List {
            open,
            bracket: Bracket::Tuple,
            elements_and_separators: vec![first, leaves.leaf(at)?],
            base: None,
            subtype: None,
        });
        frames.push(frame(open));
        Ok(true)
    }

    /// A `[` touching the term just read indexes it rather than opening a list argument: the
    /// pin's trailing `noWs "["` at maximal precedence takes only the last argument, so
    /// `f a[i]` is `f (a[i])`. Returns whether it did.
    pub(super) fn open_index(
        &mut self,
        tokens: &[LexedToken],
        frames: &mut Vec<BoundedTermFrame>,
        at: usize,
    ) -> bool {
        if at == 0 || !touching(tokens, at - 1, at) {
            return false;
        }
        let Some(base) = frames.last_mut().and_then(|frame| frame.application.pop()) else {
            return false;
        };
        self.active.push(List {
            open: at,
            bracket: Bracket::Index,
            elements_and_separators: Vec::new(),
            base: Some(base),
            subtype: None,
        });
        frames.push(frame(at));
        true
    }

    /// Whether `symbol` is a delimiter of the innermost open bracket: `,` or its own close;
    /// for a subtype, its `//` while the type is open, and its `}`.
    pub(super) fn delimits(&self, symbol: &str) -> bool {
        self.active.last().is_some_and(|list| match &list.subtype {
            Some(subtype) => symbol == "}" || (symbol == "//" && subtype.separator.is_none()),
            None => {
                symbol == ","
                    || symbol == list.bracket.close()
                    || (list.bracket == Bracket::Index && symbol == "]'")
            }
        })
    }

    /// A subtype's `//` (ending its type) or `}` (ending its predicate and the subtype).
    fn subtype_delimiter(
        &mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        frames: &mut Vec<BoundedTermFrame>,
        at: usize,
        symbol: &str,
    ) -> Result<usize, NatDefinitionParseError> {
        let refusal = || NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, at),
            expected: NatDefinitionExpectation::ScalarValue,
        };
        let current = frames.pop().expect("validated subtype frame");
        if current.ascription.is_some()
            || (current.application.is_empty()
                && current.operands.is_empty()
                && current.operators.is_empty())
        {
            return Err(refusal());
        }
        let term = finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
        let list = self.active.last_mut().expect("validated active subtype");
        let subtype = list.subtype.as_mut().expect("validated subtype state");
        if symbol == "//" && subtype.separator.is_none() {
            subtype.type_ = Some(term);
            subtype.separator = Some(at);
            frames.push(frame(list.open));
            return Ok(at + 1);
        }
        if symbol != "}" {
            return Err(refusal());
        }
        let list = self.active.pop().expect("completed subtype");
        let subtype = list.subtype.expect("subtype state");
        let type_ = match (subtype.colon, subtype.type_) {
            (Some(colon), Some(type_)) => null_node(vec![leaves.leaf(colon)?, type_]),
            (None, None) => null_node(Vec::new()),
            _ => return Err(refusal()),
        };
        let syntax = Syntax::node(
            list.bracket.kind(),
            vec![
                leaves.leaf(list.open)?,
                leaves.leaf(subtype.name)?,
                type_,
                leaves.leaf(subtype.separator.expect("a subtype's //"))?,
                term,
                leaves.leaf(at)?,
            ],
        );
        frames
            .last_mut()
            .expect("subtype has an enclosing term frame")
            .application
            .push((syntax, list.open));
        Ok(at + 1)
    }

    /// `{x // p}` or `{x : T // p}` at the `{` at `at`: opens the subtype and returns where its
    /// first term starts, or `None` for any other brace (a structure instance's).
    pub(super) fn open_subtype(
        &mut self,
        tokens: &[LexedToken],
        frames: &mut Vec<BoundedTermFrame>,
        at: usize,
    ) -> Option<usize> {
        let symbol = |i: usize, text: &str| matches!(tokens.get(i).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
        if !matches!(
            tokens.get(at + 1).map(|t| &t.kind),
            Some(TokenKind::Ident(_))
        ) {
            return None;
        }
        let subtype = if symbol(at + 2, "//") {
            Subtype {
                name: at + 1,
                colon: None,
                separator: Some(at + 2),
                type_: None,
            }
        } else if symbol(at + 2, ":") {
            // A `//` at this brace's own depth, before its `}`.
            let mut depth = 0usize;
            let mut separated = false;
            for token in tokens.iter().skip(at + 3) {
                let TokenKind::Symbol(s) = &token.kind else {
                    continue;
                };
                match crate::canonical_bracket(s.as_str()) {
                    "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                    "}" if depth == 0 => break,
                    ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                    "//" if depth == 0 => {
                        separated = true;
                        break;
                    }
                    _ => {}
                }
            }
            if !separated {
                return None;
            }
            Subtype {
                name: at + 1,
                colon: Some(at + 2),
                separator: None,
                type_: None,
            }
        } else {
            return None;
        };
        self.active.push(List {
            open: at,
            bracket: Bracket::Subtype,
            elements_and_separators: Vec::new(),
            base: None,
            subtype: Some(subtype),
        });
        frames.push(frame(at));
        Some(at + 3)
    }

    /// A list does not own commas or closing delimiters inside a record,
    /// parenthesis, or binder header nested in its current element.
    pub(super) fn current(&self, frames: &[BoundedTermFrame]) -> bool {
        self.active.last().is_some_and(|list| {
            frames.last().is_some_and(|frame| {
                frame.open == Some(list.open)
                    && frame.record.is_none()
                    && frame.prefix.is_none()
                    && frame.negation.is_none()
            })
        })
    }

    pub(super) fn delimiter(
        &mut self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        frames: &mut Vec<BoundedTermFrame>,
        at: usize,
        limit: usize,
    ) -> Result<usize, NatDefinitionParseError> {
        let refusal = || NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, at),
            expected: NatDefinitionExpectation::ScalarValue,
        };
        if !self.current(frames) || frames.len() < 2 {
            return Err(refusal());
        }
        let Some(TokenKind::Symbol(symbol)) = tokens.get(at).map(|token| &token.kind) else {
            return Err(refusal());
        };
        let close = self
            .active
            .last()
            .expect("validated active list")
            .bracket
            .close();
        if self
            .active
            .last()
            .is_some_and(|list| list.subtype.is_some())
        {
            return self.subtype_delimiter(leaves, view, tokens, frames, at, symbol);
        }
        let proved = symbol == "]'"
            && self
                .active
                .last()
                .is_some_and(|list| list.bracket == Bracket::Index);
        if symbol != "," && symbol != close && !proved {
            return Err(refusal());
        }
        let current = frames.pop().expect("validated list element frame");
        if current.ascription.is_some() {
            return Err(refusal());
        }
        let empty = current.application.is_empty()
            && current.operands.is_empty()
            && current.operators.is_empty();
        let list = self.active.last_mut().expect("validated active list");
        // An index holds exactly one term: no separator, and nothing empty.
        if list.bracket == Bracket::Index && (symbol == "," || empty) {
            return Err(refusal());
        }
        if empty {
            // [] and [a,] are valid; [,], [a,,b] and [a,,] are not (and so for ⟨⟩).
            // Every noninitial empty frame follows exactly one consumed comma.
            if symbol != close {
                return Err(refusal());
            }
        } else {
            let element =
                finish_bounded_frame(view, tokens, current, DefinitionGrammar::Scalar, at)?;
            list.elements_and_separators.push(element);
        }
        if symbol == "," {
            list.elements_and_separators.push(leaves.leaf(at)?);
            frames.push(frame(list.open));
            return Ok(at + 1);
        }
        let mut list = self.active.pop().expect("completed list");
        let mut next = at + 1;
        let (syntax, start) = match list.base.take() {
            Some((base, start)) if proved => {
                // `syntax:max term noWs "[" withoutPosition(term) "]'" term:max : term`
                // (`Init/GetElem.lean`): the proof is one argument-level term.
                let index = list.elements_and_separators.pop().expect("one index term");
                let (proof, end) = index_proof(leaves, view, tokens, next, limit)?;
                next = end;
                (
                    Syntax::node(
                        Name::from_components(["term__[_]'_"]),
                        vec![
                            base,
                            leaves.leaf(list.open)?,
                            index,
                            leaves.leaf(at)?,
                            proof,
                        ],
                    ),
                    start,
                )
            }
            Some((base, start)) => {
                let index = list.elements_and_separators.pop().expect("one index term");
                let suffix = (next < limit && touching(tokens, at, next))
                    .then(|| match &tokens[next].kind {
                        TokenKind::Symbol(s) if s == "!" || s == "?" => Some(s.as_str()),
                        _ => None,
                    })
                    .flatten();
                let syntax = match suffix {
                    // `macro:max x:term noWs "[" i:term "]" noWs "?" : term` and `"!"`
                    // (`Init/GetElem.lean`): each `noWs` is an empty `group` in the pin's tree.
                    Some(mark) => {
                        let group = || Syntax::node(Name::from_components(["group"]), Vec::new());
                        let syntax = Syntax::node(
                            Name::from_components([format!("term__[_]_{mark}").as_str()]),
                            vec![
                                base,
                                group(),
                                leaves.leaf(list.open)?,
                                index,
                                leaves.leaf(at)?,
                                group(),
                                leaves.leaf(next)?,
                            ],
                        );
                        next += 1;
                        syntax
                    }
                    None => Syntax::node(
                        list.bracket.kind(),
                        vec![base, leaves.leaf(list.open)?, index, leaves.leaf(at)?],
                    ),
                };
                (syntax, start)
            }
            None if list.bracket == Bracket::Tuple => {
                // `[e "," [es,*]]`, with at least one term after the first comma.
                let mut elements = list.elements_and_separators;
                if elements.len() < 3 {
                    return Err(refusal());
                }
                let rest = elements.split_off(2);
                elements.push(null_node(rest));
                (
                    Syntax::node(
                        list.bracket.kind(),
                        vec![
                            hygienic_lparen(leaves.leaf(list.open)?),
                            null_node(elements),
                            leaves.leaf(at)?,
                        ],
                    ),
                    list.open,
                )
            }
            None => (
                Syntax::node(
                    list.bracket.kind(),
                    vec![
                        leaves.leaf(list.open)?,
                        null_node(list.elements_and_separators),
                        leaves.leaf(at)?,
                    ],
                ),
                list.open,
            ),
        };
        frames
            .last_mut()
            .expect("list has an enclosing term frame")
            .application
            .push((syntax, start));
        Ok(next)
    }
}

/// The `term:max` after `]'`: a name, `_`, or one parenthesized or anonymous-constructor group,
/// and the token after it.
#[inline(never)]
fn index_proof(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    at: usize,
    limit: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let refusal = || NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::ScalarValue,
    };
    let end = match tokens
        .get(at)
        .filter(|_| at < limit)
        .map(|token| &token.kind)
    {
        Some(TokenKind::Ident(_)) => at + 1,
        Some(TokenKind::Symbol(s)) if s == "_" => at + 1,
        Some(TokenKind::Symbol(s)) if matches!(canonical_bracket(s), "(" | "⟨") => {
            let mut depth = 0usize;
            let mut close = None;
            for (index, token) in tokens.iter().enumerate().take(limit).skip(at) {
                if let TokenKind::Symbol(s) = &token.kind {
                    match canonical_bracket(s) {
                        "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                        ")" | "]" | "}" | "⦄" | "⟩" => {
                            depth = depth.checked_sub(1).ok_or_else(refusal)?;
                            if depth == 0 {
                                close = Some(index);
                                break;
                            }
                        }
                        _ => {}
                    }
                }
            }
            close.ok_or_else(refusal)? + 1
        }
        _ => return Err(refusal()),
    };
    // The proof is `term:max`: projections touching it (`(h).1`, `h.out`) are its own.
    let touching =
        |left: usize, right: usize| tokens[left].extent.end() == tokens[right].extent.start();
    let mut end = end;
    while end + 1 < limit
        && matches!(&tokens[end].kind, TokenKind::Symbol(s) if s == ".")
        && touching(end - 1, end)
        && touching(end, end + 1)
        && matches!(
            &tokens[end + 1].kind,
            TokenKind::Ident(_) | TokenKind::Literal(LiteralKind::Nat)
        )
    {
        end += 2;
    }
    let proof = nested_term(leaves, view, tokens, at..end)?;
    Ok((proof, end))
}
