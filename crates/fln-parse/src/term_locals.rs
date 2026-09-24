//! Local bindings, opaque assertions and result types on ordinary heap frames.
//!
//! The pin's `let`/`have`/`show` nodes retain every original token. A nested binding
//! never recursively invokes the term parser: its annotation, value and body
//! are separate phases on the same stack used for lambda telescopes.
use super::*;

pub(super) enum Prefix {
    Binders(Box<term_binders::Prefix>),
    Assertion(Box<Assertion>),
    Do(Box<term_do::Prefix>),
}
impl From<term_binders::Prefix> for Prefix {
    fn from(value: term_binders::Prefix) -> Self {
        Self::Binders(Box::new(value))
    }
}

pub(super) struct Assertion {
    keyword: usize,
    name: Option<usize>,
    colon: Option<usize>,
    annotation: Option<Syntax>,
    assignment: Option<usize>,
    value: Option<Syntax>,
    separator: Option<usize>,
    form: Form,
    phase: Phase,
    proof_intro: Option<usize>,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    Let,
    Have,
    Show,
    Suffices,
}
#[derive(Clone, Copy)]
enum Phase {
    Annotation,
    Value,
    Body,
}
// These are contextual term keywords, not new globally reserved identifiers.
// Length excludes guillemet-escaped names such as `«have»` from keyword matches.
pub(super) fn word(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    tokens.get(at).is_some_and(|t| match &t.kind {
        TokenKind::Symbol(s) => s == text,
        TokenKind::Ident(name) => {
            name == &Name::from_components([text])
                && t.extent.end().0 - t.extent.start().0 == text.len()
        }
        _ => false,
    })
}
fn atom(leaves: &Leaves, at: usize, text: &str) -> Result<Syntax, NatDefinitionParseError> {
    Ok(Syntax::Atom {
        info: leaves.leaf(at)?.info(),
        val: text.to_string(),
    })
}
fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::ScalarValue,
    }
}
fn column(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    let source = view.normalized();
    let pos = tokens[at].extent.start();
    pos.0
        - source
            .line_start(source.line_of(pos))
            .expect("token line")
            .0
}
fn newline(view: &SourceView, tokens: &[LexedToken], at: usize) -> bool {
    at > 0
        && view.normalized().line_of(tokens[at].extent.start())
            > view.normalized().line_of(tokens[at - 1].extent.end())
}

// A group, binder annotation, or record blocks an outer layout boundary. Only
// completed prefix bodies can be closed to reach the waiting local witness.
fn pending_value(frames: &[BoundedTermFrame]) -> Option<usize> {
    for frame in frames.iter().rev() {
        if frame.negation.is_some() {
            continue;
        }
        match frame.prefix.as_ref()? {
            Prefix::Assertion(p) if matches!(p.phase, Phase::Value) => return Some(p.keyword),
            prefix if prefix.body() => {}
            _ => return None,
        }
    }
    None
}
pub(super) fn layout_boundary(
    view: &SourceView,
    tokens: &[LexedToken],
    frames: &[BoundedTermFrame],
    at: usize,
) -> bool {
    if !newline(view, tokens, at) || word(tokens, at, ";") {
        return false;
    }
    // A first witness token on the next line cannot terminate an empty value.
    if frames
        .last()
        .is_none_or(|f| f.application.is_empty() && f.operands.is_empty())
    {
        return false;
    }
    pending_value(frames)
        .is_some_and(|keyword| column(view, tokens, at) <= column(view, tokens, keyword))
}

/// Bound a tactic-valued assertion before handing it to the independent proof
/// planner. Its own nested declarations and branches remain in the same slice.
pub(super) fn proof_limit(
    view: &SourceView,
    tokens: &[LexedToken],
    frames: &[BoundedTermFrame],
    by: usize,
    end: usize,
) -> usize {
    let Some(keyword) = pending_value(frames) else {
        return end;
    };
    if by + 1 >= end {
        return end;
    }
    let mut baseline = column(view, tokens, keyword);
    let first = by + 1;
    if newline(view, tokens, first) && column(view, tokens, first) <= baseline {
        // An inline declaration can place `have ... := by` far to the right.
        // Its first indented tactic establishes the proof's actual baseline.
        baseline = column(view, tokens, first).saturating_sub(1);
    }
    let mut depth = 0usize;
    for at in first..end {
        if at > first
            && depth == 0
            && newline(view, tokens, at)
            && column(view, tokens, at) <= baseline
        {
            return at;
        }
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match s.as_str() {
                "(" | "[" | "{" | ".{" | "⦃" => depth += 1,
                ")" | "]" | "}" | "⦄" if depth == 0 => return at,
                ")" | "]" | "}" | "⦄" => depth -= 1,
                _ => {}
            }
        }
    }
    end
}
fn separator(leaves: &Leaves, at: Option<usize>) -> Result<Syntax, NatDefinitionParseError> {
    Ok(at.map_or_else(|| Ok(null_node(vec![])), |at| leaves.leaf(at))?)
}
fn primed_proof(mut proof: Syntax) -> Syntax {
    if let Syntax::Node { kind, .. } = &mut proof {
        *kind = parser_kind(&["Term", "byTactic'"]);
    }
    proof
}

impl Prefix {
    pub(super) fn assertion(
        view: &SourceView,
        tokens: &[LexedToken],
        keyword: usize,
        cursor: &mut usize,
        end: usize,
    ) -> Result<Self, NatDefinitionParseError> {
        let form = if word(tokens, keyword, "let") {
            Form::Let
        } else if word(tokens, keyword, "show") {
            Form::Show
        } else if word(tokens, keyword, "suffices") {
            Form::Suffices
        } else {
            Form::Have
        };
        let mut assertion = Assertion {
            keyword,
            name: None,
            colon: None,
            annotation: None,
            assignment: None,
            value: None,
            separator: None,
            form,
            phase: Phase::Annotation,
            proof_intro: None,
        };
        if form == Form::Suffices {
            // The pin makes only `identifier :` optional; without it the next
            // expression is the complete proposition, not a declaration name.
            if *cursor + 1 < end
                && matches!(&tokens[*cursor].kind, TokenKind::Ident(_))
                && word(tokens, *cursor + 1, ":")
            {
                assertion.name = Some(*cursor);
                assertion.colon = Some(*cursor + 1);
                *cursor += 2;
            }
        } else if matches!(form, Form::Have | Form::Let) {
            if *cursor < end && matches!(&tokens[*cursor].kind, TokenKind::Ident(_)) {
                assertion.name = Some(*cursor);
                *cursor += 1;
            }
            if form == Form::Let && assertion.name.is_none() {
                return Err(refuse(view, tokens, *cursor));
            }
            if *cursor < end && word(tokens, *cursor, ":") {
                assertion.colon = Some(*cursor);
                *cursor += 1;
            } else if *cursor < end && word(tokens, *cursor, ":=") {
                assertion.assignment = Some(*cursor);
                assertion.phase = Phase::Value;
                *cursor += 1;
            } else {
                return Err(refuse(view, tokens, *cursor));
            }
        }
        if *cursor >= end {
            return Err(refuse(view, tokens, *cursor));
        }
        Ok(Self::Assertion(Box::new(assertion)))
    }

    pub(super) fn body(&self) -> bool {
        match self {
            Self::Do(_) => false,
            Self::Binders(p) => p.body(),
            Self::Assertion(p) => matches!(p.phase, Phase::Body),
        }
    }
    pub(super) fn closes_header(&self, tokens: &[LexedToken], at: usize) -> bool {
        match self {
            Self::Do(p) => p.closes_header(tokens, at),
            Self::Binders(p) => p.closes_header(tokens, at),
            Self::Assertion(p) => match p.phase {
                Phase::Annotation if !matches!(p.form, Form::Have | Form::Let) => {
                    word(tokens, at, "from") || word(tokens, at, "by")
                }
                Phase::Annotation => word(tokens, at, ":="),
                Phase::Value => word(tokens, at, ";"),
                Phase::Body => false,
            },
        }
    }
    pub(super) fn finish_header(
        self,
        leaves: &Leaves,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        expression: Syntax,
        end: usize,
    ) -> Result<(Self, usize), NatDefinitionParseError> {
        let mut p = match self {
            Self::Do(p) => {
                return p
                    .finish_header(leaves, view, tokens, at, expression, end)
                    .map(|(p, next)| (Self::Do(Box::new(p)), next));
            }
            Self::Binders(p) => {
                return p
                    .finish_header(leaves, view, tokens, at, expression, end)
                    .map(|(p, next)| (Self::Binders(Box::new(p)), next));
            }
            Self::Assertion(p) => p,
        };
        let mut next = at + 1;
        match p.phase {
            Phase::Annotation => {
                p.annotation = Some(expression);
                if !matches!(p.form, Form::Have | Form::Let) {
                    p.proof_intro = Some(at);
                    p.phase = if p.form == Form::Show {
                        Phase::Body
                    } else {
                        Phase::Value
                    };
                    // `by` owns its original token and remains a complete term.
                    if word(tokens, at, "by") {
                        next = at;
                    }
                } else {
                    p.assignment = Some(at);
                    p.phase = Phase::Value;
                }
            }
            Phase::Value => {
                p.value = Some(expression);
                if word(tokens, at, ";") {
                    p.separator = Some(at);
                } else {
                    // The pin's semicolonOrLinebreak pushes an empty null node.
                    // This token belongs to the continuation, not a fake atom.
                    p.separator = None;
                    next = at;
                }
                p.phase = Phase::Body;
            }
            Phase::Body => return Err(refuse(view, tokens, at)),
        }
        if next >= end {
            return Err(refuse(view, tokens, next));
        }
        Ok((Self::Assertion(p), next))
    }
    pub(super) fn finish(
        self,
        leaves: &Leaves,
        body: Syntax,
    ) -> Result<(Syntax, usize), NatDefinitionParseError> {
        let p = match self {
            Self::Do(p) => return p.finish(leaves, body),
            Self::Binders(p) => return p.finish(leaves, body),
            Self::Assertion(p) => p,
        };
        let syntax = if p.form == Form::Show {
            let separator = p.proof_intro.expect("show proof introducer");
            let rhs = if body.kind() == Some(&parser_kind(&["Term", "byTactic"]))
                && matches!(&leaves.leaf(separator)?, Syntax::Atom { val, .. } if val == "by")
            {
                primed_proof(body)
            } else {
                Syntax::node(
                    parser_kind(&["Term", "fromTerm"]),
                    vec![atom(leaves, separator, "from")?, body],
                )
            };
            Syntax::node(
                parser_kind(&["Term", "show"]),
                vec![
                    atom(leaves, p.keyword, "show")?,
                    p.annotation.expect("show annotation"),
                    rhs,
                ],
            )
        } else if p.form == Form::Suffices {
            let binder = match p.name {
                Some(at) => null_node(vec![
                    leaves.leaf(at)?,
                    leaves.leaf(p.colon.expect("suffices colon"))?,
                ]),
                None => Syntax::node(
                    Name::from_components(["hygieneInfo"]),
                    vec![hygiene_ident()],
                ),
            };
            let intro = p.proof_intro.expect("suffices proof introducer");
            let proof = p.value.expect("suffices continuation");
            let rhs = if proof.kind() == Some(&parser_kind(&["Term", "byTactic"]))
                && matches!(&leaves.leaf(intro)?, Syntax::Atom { val, .. } if val == "by")
            {
                primed_proof(proof)
            } else {
                Syntax::node(
                    parser_kind(&["Term", "fromTerm"]),
                    vec![atom(leaves, intro, "from")?, proof],
                )
            };
            Syntax::node(
                parser_kind(&["Term", "suffices"]),
                vec![
                    atom(leaves, p.keyword, "suffices")?,
                    Syntax::node(
                        parser_kind(&["Term", "sufficesDecl"]),
                        vec![binder, p.annotation.expect("suffices proposition"), rhs],
                    ),
                    separator(leaves, p.separator)?,
                    body,
                ],
            )
        } else {
            let separator = separator(leaves, p.separator)?;
            let name = match p.name {
                Some(at) => leaves.leaf(at)?,
                None => Syntax::node(
                    Name::from_components(["hygieneInfo"]),
                    vec![hygiene_ident()],
                ),
            };
            let annotation = match (p.colon, p.annotation) {
                (Some(colon), Some(type_)) => null_node(vec![Syntax::node(
                    parser_kind(&["Term", "typeSpec"]),
                    vec![leaves.leaf(colon)?, type_],
                )]),
                (None, None) => null_node(vec![]),
                _ => unreachable!("assertion annotation phases"),
            };
            let declaration = Syntax::node(
                parser_kind(&["Term", "letIdDecl"]),
                vec![
                    Syntax::node(parser_kind(&["Term", "letId"]), vec![name]),
                    null_node(vec![]),
                    annotation,
                    leaves.leaf(p.assignment.expect("have assignment"))?,
                    p.value.expect("have value"),
                ],
            );
            let keyword = if p.form == Form::Let { "let" } else { "have" };
            Syntax::node(
                parser_kind(&["Term", keyword]),
                vec![
                    atom(leaves, p.keyword, keyword)?,
                    Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null_node(vec![])]),
                    Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]),
                    separator,
                    body,
                ],
            )
        };
        Ok((syntax, p.keyword))
    }
}
