//! Opaque local assertions and explicit result types on the ordinary heap frames.
//!
//! The pin's `have`/`show` nodes retain every original token. A nested assertion
//! never recursively invokes the term parser: its annotation, value and body
//! are separate phases on the same stack used for lambda telescopes.
use super::*;

pub(super) enum Prefix {
    Binders(Box<term_binders::Prefix>),
    Assertion(Box<Assertion>),
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
impl Prefix {
    pub(super) fn assertion(
        view: &SourceView,
        tokens: &[LexedToken],
        keyword: usize,
        cursor: &mut usize,
        end: usize,
    ) -> Result<Self, NatDefinitionParseError> {
        let form = if word(tokens, keyword, "show") {
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
        } else if form == Form::Have {
            if *cursor < end && matches!(&tokens[*cursor].kind, TokenKind::Ident(_)) {
                assertion.name = Some(*cursor);
                *cursor += 1;
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
            Self::Binders(p) => p.body(),
            Self::Assertion(p) => matches!(p.phase, Phase::Body),
        }
    }
    pub(super) fn closes_header(&self, tokens: &[LexedToken], at: usize) -> bool {
        match self {
            Self::Binders(p) => p.closes_header(tokens, at),
            Self::Assertion(p) => match p.phase {
                Phase::Annotation if p.form != Form::Have => {
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
        let Self::Assertion(mut p) = self else {
            let Self::Binders(p) = self else {
                unreachable!("prefix variants")
            };
            return p
                .finish_header(leaves, view, tokens, at, expression, end)
                .map(|(p, next)| (Self::Binders(Box::new(p)), next));
        };
        let mut next = at + 1;
        match p.phase {
            Phase::Annotation => {
                p.annotation = Some(expression);
                if p.form != Form::Have {
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
                p.separator = Some(at);
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
        let Self::Assertion(p) = self else {
            let Self::Binders(p) = self else {
                unreachable!("prefix variants")
            };
            return p.finish(leaves, body);
        };
        let syntax = if p.form == Form::Show {
            let separator = p.proof_intro.expect("show proof introducer");
            let rhs = if body.kind() == Some(&parser_kind(&["Term", "byTactic"]))
                && matches!(&leaves.leaf(separator)?, Syntax::Atom { val, .. } if val == "by")
            {
                body
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
                proof
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
                    leaves.leaf(p.separator.expect("suffices separator"))?,
                    body,
                ],
            )
        } else {
            let separator = p.separator.expect("have separator");
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
            Syntax::node(
                parser_kind(&["Term", "have"]),
                vec![
                    atom(leaves, p.keyword, "have")?,
                    Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null_node(vec![])]),
                    Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]),
                    leaves.leaf(separator)?,
                    body,
                ],
            )
        };
        Ok((syntax, p.keyword))
    }
}
