//! Syntax quotations and their antiquotations, as the pin's trees (bead
//! `fln-pin-syntax-corpus-7b5b`).
//!
//! ```text
//! Term.quot      := "`(" term ")"                          (Lean/Parser/Command.lean)
//! Tactic.quot    := "`(tactic| " tactic ")"                 (default+1, Lean/Parser/Term.lean)
//! Tactic.quotSeq := "`(tactic| " Tactic.seq1 ")"            seq1 := sepBy1 tactic "; "
//! conv.quot      := "`(conv| " conv ")"                     (inside a `Term.quot` node)
//! dynamicQuot    := "`(" ident "|" … ")"                    (read for term, prec and prio)
//! antiquot       := "$"* "$" (ident <|> "_" <|> antiquotNestedExpr) (":" name)?
//! ```
//!
//! An antiquotation's kind is the parser it stands in for (`mkAntiquot`, Lean/Parser/Basic.lean):
//! a category's is `<cat>.pseudo.antiquot` (`term.pseudo.antiquot` for a term operand,
//! `tactic.pseudo.antiquot` for a tactic, `Lean.Parser.Term.funBinder.pseudo.antiquot` for a
//! `fun` binder), a node's `<kind>.antiquot` (`Lean.Parser.Tactic.tacticSeq.antiquot` where a
//! whole tactic sequence is one), and a named one the parser its name selects (`$x:ident` is
//! `ident.antiquot`). Its children: the `$`, the escaping `$`s (none read here), the expression,
//! and the `antiquotName` node or nothing. Antiquotations are read only inside a quotation; a
//! splice (`$xs,*`, `$[…]?`, `$x*`) and an escaped `$$x` are refused.
use super::*;
use std::ops::Range;

thread_local! {
    /// How many quotations enclose the term being read (`incQuotDepth`), less the nested
    /// antiquotation expressions between (`decQuotDepth`).
    static DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Quotations nest only this deep; deeper is refused rather than recursed into.
const MAX_DEPTH: usize = 16;

struct Depth(isize);

impl Depth {
    fn shift(by: isize) -> Depth {
        DEPTH.with(|depth| depth.set(depth.get().saturating_add_signed(by)));
        Depth(by)
    }
}

impl Drop for Depth {
    fn drop(&mut self) {
        DEPTH.with(|depth| depth.set(depth.get().saturating_add_signed(-self.0)));
    }
}

/// Whether the term or tactic being read is inside a quotation, where `$` starts an
/// antiquotation.
pub(crate) fn inside() -> bool {
    DEPTH.with(|depth| depth.get() > 0)
}

fn text(tokens: &[LexedToken], at: usize) -> Option<&str> {
    match &tokens.get(at)?.kind {
        TokenKind::Symbol(symbol) => Some(symbol.as_str()),
        _ => None,
    }
}

fn touching(tokens: &[LexedToken], left: usize, right: usize) -> bool {
    match (tokens.get(left), tokens.get(right)) {
        (Some(left), Some(right)) => left.extent.end() == right.extent.start(),
        _ => false,
    }
}

fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::ScalarValue,
    }
}

/// Whether `symbol` opens a quotation.
pub(crate) fn opens(symbol: &str) -> bool {
    matches!(symbol, "`(" | "`(tactic|" | "`(conv|")
}

/// The `)` that closes the group opened at `open` (a `(` or a quotation), before `end`.
fn closing(tokens: &[LexedToken], open: usize, end: usize) -> Option<usize> {
    let mut depth = 0_usize;
    for at in open..end {
        match text(tokens, at) {
            Some("(") => depth += 1,
            Some(symbol) if opens(symbol) => depth += 1,
            Some(")") => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(at);
                }
            }
            _ => {}
        }
    }
    None
}

/// The quotation at `start`, if one opens there: its tree and the token after its `)`.
pub(crate) fn quotation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
) -> Result<Option<(Syntax, usize)>, NatDefinitionParseError> {
    let Some(open) = text(tokens, start).filter(|symbol| opens(symbol)) else {
        return Ok(None);
    };
    let close = closing(tokens, start, end).ok_or_else(|| refuse(view, tokens, start))?;
    if close == start + 1 || DEPTH.with(|depth| depth.get()) >= MAX_DEPTH {
        return Err(refuse(view, tokens, start));
    }
    let _inside = Depth::shift(1);
    let inner = start + 1..close;
    let dynamic = open == "`("
        && close > start + 3
        && matches!(tokens[start + 1].kind, TokenKind::Ident(_))
        && text(tokens, start + 2) == Some("|");
    let syntax = if dynamic {
        dynamic_quotation(leaves, view, tokens, start, close)?
    } else if open == "`(" {
        Syntax::node(
            parser_kind(&["Term", "quot"]),
            vec![
                leaves.leaf(start)?,
                nested_term(leaves, view, tokens, inner)?,
                leaves.leaf(close)?,
            ],
        )
    } else if open == "`(conv|" {
        // `conv.quot := "`(conv|" conv ")"`, one conv tactic, as the term the pin reads it as: a
        // `Term.quot` around the category's quotation.
        Syntax::node(
            parser_kind(&["Term", "quot"]),
            vec![Syntax::node(
                Name::from_components(["conv", "quot"]),
                vec![
                    leaves.leaf(start)?,
                    proofs::conv_quoted(leaves, view, tokens, inner)?,
                    leaves.leaf(close)?,
                ],
            )],
        )
    } else {
        tactic_quotation(leaves, view, tokens, start, inner, close)?
    };
    Ok(Some((syntax, close + 1)))
}

/// `Term.dynamicQuot := "`(" ident "|" … ")"`, a quotation of the category or parser `ident`
/// names, read for `term` and for the numerals of `prec` and `prio` (`(prec| 1024)`, and
/// `$n:num` in their place); any other is refused.
fn dynamic_quotation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    close: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let category = view
        .normalized()
        .span_str(tokens[start + 1].extent)
        .unwrap_or_default();
    let inner = start + 3..close;
    let body = match category {
        "term" => nested_term(leaves, view, tokens, inner)?,
        "prec" | "prio"
            if inner.len() == 1
                && matches!(
                    tokens[inner.start].kind,
                    TokenKind::Literal(LiteralKind::Nat)
                ) =>
        {
            Syntax::node(
                Name::str(Name::anonymous(), "num"),
                vec![leaves.leaf(inner.start)?],
            )
        }
        "prec" | "prio" if inner.len() == 4 && text(tokens, inner.start + 2) == Some(":") => {
            match antiquotation(leaves, view, tokens, inner.start, inner.end, Position::Term)? {
                Some((antiquotation, next))
                    if next == inner.end
                        && antiquotation.kind()
                            == Some(&Name::from_components(["num", "antiquot"])) =>
                {
                    antiquotation
                }
                _ => return Err(refuse(view, tokens, inner.start)),
            }
        }
        _ => return Err(refuse(view, tokens, start + 1)),
    };
    Ok(Syntax::node(
        parser_kind(&["Term", "dynamicQuot"]),
        vec![
            leaves.leaf(start)?,
            leaves.leaf(start + 1)?,
            leaves.leaf(start + 2)?,
            body,
            leaves.leaf(close)?,
        ],
    ))
}

/// `Tactic.quot` when one tactic reads the whole quotation (it wins the tie at default+1),
/// otherwise `Tactic.quotSeq` over `seq1`: tactics separated by `;`. The contents are read as a
/// tactic sequence is, so a tactic that takes a sequence takes the `;`s after it
/// (`with_reducible apply f; assumption` is one tactic); a line break between two tactics is no
/// separator of `seq1`, and is refused.
fn tactic_quotation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    inner: Range<usize>,
    close: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let open = leaves.leaf(start)?;
    let close_atom = leaves.leaf(close)?;
    let quot = |tactic: Syntax| {
        Syntax::node(
            parser_kind(&["Tactic", "quot"]),
            vec![open.clone(), tactic, close_atom.clone()],
        )
    };
    if let Some((antiquotation, next)) = antiquotation(
        leaves,
        view,
        tokens,
        inner.start,
        inner.end,
        Position::Tactic,
    )? && next == inner.end
    {
        return Ok(quot(antiquotation));
    }
    let sequence = proofs::tactic_seq(leaves, view, tokens, inner.clone())?;
    // `{ tacs }` is one tactic (`nestedTactic`), the quotation's.
    if let Syntax::Node { args, .. } = &sequence
        && let [bracketed @ Syntax::Node { kind, .. }] = args.as_slice()
        && kind == &parser_kind(&["Tactic", "tacticSeqBracketed"])
    {
        return Ok(quot(bracketed.clone()));
    }
    let rows = match &sequence {
        Syntax::Node { args, .. } => match args.as_slice() {
            [Syntax::Node { args, .. }] => match args.as_slice() {
                [Syntax::Node { args: rows, .. }] => rows.clone(),
                _ => return Err(refuse(view, tokens, inner.start)),
            },
            _ => return Err(refuse(view, tokens, inner.start)),
        },
        _ => return Err(refuse(view, tokens, inner.start)),
    };
    if let [tactic] = rows.as_slice() {
        return Ok(quot(tactic.clone()));
    }
    let separated =
        rows.len() % 2 == 1
            && rows.iter().skip(1).step_by(2).all(
                |separator| matches!(separator, Syntax::Atom { val, .. } if val.as_str() == ";"),
            );
    if !separated {
        return Err(refuse(view, tokens, inner.start));
    }
    Ok(Syntax::node(
        parser_kind(&["Tactic", "quotSeq"]),
        vec![
            open,
            Syntax::node(parser_kind(&["Tactic", "seq1"]), vec![null_node(rows)]),
            close_atom,
        ],
    ))
}

/// Where an antiquotation stands, which decides its kind when it has no name.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Position {
    Term,
    Tactic,
    TacticSeq,
    FunBinder,
    ConvSeq,
    OptConfig,
    RwRuleSeq,
}

/// The antiquotation at `start` inside a quotation, ending by `end`: its tree and the token after
/// it. `None` outside a quotation or where no `$` starts one.
pub(crate) fn antiquotation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
    position: Position,
) -> Result<Option<(Syntax, usize)>, NatDefinitionParseError> {
    if !inside() || text(tokens, start) != Some("$") || start + 1 >= end {
        return Ok(None);
    }
    if !touching(tokens, start, start + 1) || text(tokens, start + 1) == Some("$") {
        return Err(refuse(view, tokens, start));
    }
    let (expression, mut next) = match &tokens[start + 1].kind {
        TokenKind::Ident(_) => (leaves.leaf(start + 1)?, start + 2),
        TokenKind::Symbol(symbol) if symbol == "_" => (leaves.leaf(start + 1)?, start + 2),
        TokenKind::Symbol(symbol) if symbol == "(" => {
            let close =
                closing(tokens, start + 1, end).ok_or_else(|| refuse(view, tokens, start + 1))?;
            // `decQuotDepth`: the nested expression is ordinary syntax again.
            let _outside = Depth::shift(-1);
            let term = nested_term(leaves, view, tokens, start + 2..close)?;
            (
                Syntax::node(
                    Name::from_components(["antiquotNestedExpr"]),
                    vec![leaves.leaf(start + 1)?, term, leaves.leaf(close)?],
                ),
                close + 1,
            )
        }
        _ => return Err(refuse(view, tokens, start + 1)),
    };
    // `(":" name)?`, touching the expression and each other.
    let named = next + 1 < end
        && text(tokens, next) == Some(":")
        && touching(tokens, next - 1, next)
        && touching(tokens, next, next + 1)
        && matches!(tokens[next + 1].kind, TokenKind::Ident(_));
    let (kind, name) = if named {
        let spelled = view
            .normalized()
            .span_str(tokens[next + 1].extent)
            .unwrap_or_default();
        let kind = match (position, spelled) {
            (Position::Term, "term") => Name::from_components(["term", "pseudo", "antiquot"]),
            (Position::Tactic, "tactic") => Name::from_components(["tactic", "pseudo", "antiquot"]),
            (Position::OptConfig, "optConfig") => {
                Name::from_components(["Lean", "Parser", "Tactic", "optConfig", "antiquot"])
            }
            (Position::Term, "ident" | "num" | "str") => {
                Name::from_components([spelled, "antiquot"])
            }
            _ => return Err(refuse(view, tokens, next + 1)),
        };
        let name = Syntax::node(
            Name::from_components(["antiquotName"]),
            vec![
                leaves.leaf(next)?,
                Syntax::Atom {
                    info: leaves.leaf(next + 1)?.info(),
                    val: spelled.into(),
                },
            ],
        );
        next += 2;
        (kind, name)
    } else {
        let kind = match position {
            Position::Term => Name::from_components(["term", "pseudo", "antiquot"]),
            Position::Tactic => Name::from_components(["tactic", "pseudo", "antiquot"]),
            Position::TacticSeq => {
                Name::from_components(["Lean", "Parser", "Tactic", "tacticSeq", "antiquot"])
            }
            Position::FunBinder => {
                Name::from_components(["Lean", "Parser", "Term", "funBinder", "pseudo", "antiquot"])
            }
            Position::ConvSeq => {
                Name::from_components(["Lean", "Parser", "Tactic", "Conv", "convSeq", "antiquot"])
            }
            Position::OptConfig => {
                Name::from_components(["Lean", "Parser", "Tactic", "optConfig", "antiquot"])
            }
            Position::RwRuleSeq => {
                Name::from_components(["Lean", "Parser", "Tactic", "rwRuleSeq", "antiquot"])
            }
        };
        (kind, null_node(Vec::new()))
    };
    // A splice suffix (`$xs*`, `$xs,*`, `$x?`) is not read: refuse rather than misread it as an
    // operator.
    let splice = match text(tokens, next) {
        Some("*" | "?" | ",*" | ",+") => true,
        Some(",") => {
            touching(tokens, next, next + 1) && matches!(text(tokens, next + 1), Some("*" | "+"))
        }
        _ => false,
    };
    if next < end && touching(tokens, next - 1, next) && splice {
        return Err(refuse(view, tokens, next));
    }
    Ok(Some((
        Syntax::node(
            kind,
            vec![leaves.leaf(start)?, null_node(Vec::new()), expression, name],
        ),
        next,
    )))
}
