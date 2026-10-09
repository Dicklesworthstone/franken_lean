//! `obtain`, `rcases`, `rintro` and `ext` with their `rcases` patterns (`Init/RCases.lean`):
//! - `rcasesPat`: a name (`one`), `_` (`ignore`), `-` (`clear`), `⟨p, …⟩` (`tuple`) or `(p)`
//!   (`paren`);
//! - `rcasesPatMed`: patterns separated by `|`;
//! - `rcasesPatLo`: a `Med` with an optional `: T`.
//!
//! Patterns nest through brackets only, at most [`PATTERN_NESTING`] deep; deeper ones are
//! refused rather than recursed into on a small host stack.
use super::*;

const PATTERN_NESTING: usize = 16;

fn is(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}

/// The top-level occurrences of `separator` in `range`.
fn split(tokens: &[LexedToken], range: Range<usize>, separator: &str) -> Vec<usize> {
    let mut depth = 0usize;
    let mut found = Vec::new();
    for at in range {
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                _ if depth == 0 && s == separator => found.push(at),
                _ => {}
            }
        }
    }
    found
}

fn kind(name: &[&str]) -> Name {
    let mut components = vec!["Tactic"];
    components.extend_from_slice(name);
    parser_kind(&components)
}

struct Patterns<'a> {
    leaves: &'a Leaves,
    view: &'a SourceView,
    tokens: &'a [LexedToken],
}

impl Patterns<'_> {
    fn refuse(&self, at: usize) -> NatDefinitionParseError {
        refusal(self.view, self.tokens, at)
    }

    /// `rintroPat.one` units, each a name, `_`, `-` or a `⟨…⟩` tuple.
    fn rintro_units(&self, range: Range<usize>) -> Result<Vec<Syntax>, NatDefinitionParseError> {
        let mut units = Vec::new();
        let mut at = range.start;
        while at < range.end {
            let end = if is(self.tokens, at, "⟨") {
                matching(self.tokens, at)
                    .filter(|&close| close < range.end)
                    .ok_or_else(|| self.refuse(at))?
                    + 1
            } else {
                at + 1
            };
            units.push(Syntax::node(
                kind(&["rintroPat", "one"]),
                vec![self.pat(at..end, 0)?],
            ));
            at = end;
        }
        Ok(units)
    }

    /// `rcasesPatLo`: a `Med`, then an optional top-level `: T`.
    fn lo(&self, range: Range<usize>, depth: usize) -> Result<Syntax, NatDefinitionParseError> {
        let colon = split(self.tokens, range.clone(), ":").first().copied();
        let (pattern, type_) = match colon {
            Some(colon) if colon + 1 < range.end => (
                range.start..colon,
                null_node(vec![
                    self.leaves.leaf(colon)?,
                    bounded_term(
                        self.leaves,
                        self.view,
                        self.tokens,
                        colon + 1..range.end,
                        DefinitionGrammar::Scalar,
                    )?,
                ]),
            ),
            Some(colon) => return Err(self.refuse(colon)),
            None => (range, null_node(Vec::new())),
        };
        Ok(Syntax::node(
            kind(&["rcasesPatLo"]),
            vec![self.med(pattern, depth)?, type_],
        ))
    }

    /// `rcasesPatMed`: patterns separated by top-level `|`.
    fn med(&self, range: Range<usize>, depth: usize) -> Result<Syntax, NatDefinitionParseError> {
        let mut parts = Vec::new();
        let mut start = range.start;
        for bar in split(self.tokens, range.clone(), "|")
            .into_iter()
            .chain(std::iter::once(range.end))
        {
            parts.push(self.pat(start..bar, depth)?);
            if bar < range.end {
                parts.push(self.leaves.leaf(bar)?);
            }
            start = bar + 1;
        }
        Ok(Syntax::node(
            kind(&["rcasesPatMed"]),
            vec![null_node(parts)],
        ))
    }

    /// One `rcasesPat`.
    fn pat(&self, range: Range<usize>, depth: usize) -> Result<Syntax, NatDefinitionParseError> {
        if range.is_empty() {
            return Err(self.refuse(range.start));
        }
        if depth >= PATTERN_NESTING {
            return Err(self.refuse(range.start));
        }
        let first = range.start;
        if range.len() == 1 {
            return Ok(match &self.tokens[first].kind {
                TokenKind::Ident(_) => {
                    Syntax::node(kind(&["rcasesPat", "one"]), vec![self.leaves.leaf(first)?])
                }
                TokenKind::Symbol(s) if s == "_" => Syntax::node(
                    kind(&["rcasesPat", "ignore"]),
                    vec![self.leaves.leaf(first)?],
                ),
                TokenKind::Symbol(s) if s == "-" => Syntax::node(
                    kind(&["rcasesPat", "clear"]),
                    vec![self.leaves.leaf(first)?],
                ),
                _ => return Err(self.refuse(first)),
            });
        }
        let last = range.end - 1;
        let closes = |open: &str, close: &str| {
            is(self.tokens, first, open)
                && is(self.tokens, last, close)
                && split(self.tokens, first + 1..last, close).is_empty()
                && matching(self.tokens, first) == Some(last)
        };
        if closes("⟨", "⟩") {
            let inner = first + 1..last;
            let mut elements = Vec::new();
            if !inner.is_empty() {
                let mut start = inner.start;
                for comma in split(self.tokens, inner.clone(), ",")
                    .into_iter()
                    .chain(std::iter::once(inner.end))
                {
                    elements.push(self.lo(start..comma, depth + 1)?);
                    if comma < inner.end {
                        elements.push(self.leaves.leaf(comma)?);
                    }
                    start = comma + 1;
                }
            }
            return Ok(Syntax::node(
                kind(&["rcasesPat", "tuple"]),
                vec![
                    self.leaves.leaf(first)?,
                    null_node(elements),
                    self.leaves.leaf(last)?,
                ],
            ));
        }
        if closes("(", ")") {
            return Ok(Syntax::node(
                kind(&["rcasesPat", "paren"]),
                vec![
                    self.leaves.leaf(first)?,
                    self.lo(first + 1..last, depth + 1)?,
                    self.leaves.leaf(last)?,
                ],
            ));
        }
        Err(self.refuse(first))
    }
}

/// The token closing the bracket opened at `open`.
fn matching(tokens: &[LexedToken], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (at, token) in tokens.iter().enumerate().skip(open) {
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

/// `obtain`, `rcases` or `rintro` at `range.start`, its keyword already an atom.
#[inline(never)]
pub(super) fn tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: &str,
    atom: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let patterns = Patterns {
        leaves,
        view,
        tokens,
    };
    let body = range.start + 1..range.end;
    match keyword {
        // `"obtain" (ppSpace rcasesPatMed)? (" : " term)? (" := " term,+)?`
        "obtain" => {
            let assign = split(tokens, body.clone(), ":=").first().copied();
            let head = body.start..assign.unwrap_or(body.end);
            let value = match assign {
                Some(assign) => {
                    let values = assign + 1..body.end;
                    if values.is_empty() {
                        return Err(refusal(view, tokens, assign));
                    }
                    let mut terms = Vec::new();
                    let mut start = values.start;
                    for comma in split(tokens, values.clone(), ",")
                        .into_iter()
                        .chain(std::iter::once(values.end))
                    {
                        terms.push(bounded_term(
                            leaves,
                            view,
                            tokens,
                            start..comma,
                            DefinitionGrammar::Scalar,
                        )?);
                        if comma < values.end {
                            terms.push(leaves.leaf(comma)?);
                        }
                        start = comma + 1;
                    }
                    null_node(vec![leaves.leaf(assign)?, null_node(terms)])
                }
                None => null_node(Vec::new()),
            };
            let colon = split(tokens, head.clone(), ":").first().copied();
            let (pattern, type_) = match colon {
                Some(colon) => (
                    head.start..colon,
                    null_node(vec![
                        leaves.leaf(colon)?,
                        bounded_term(
                            leaves,
                            view,
                            tokens,
                            colon + 1..head.end,
                            DefinitionGrammar::Scalar,
                        )?,
                    ]),
                ),
                None => (head, null_node(Vec::new())),
            };
            let pattern = if pattern.is_empty() {
                null_node(Vec::new())
            } else {
                null_node(vec![patterns.med(pattern, 0)?])
            };
            Ok(Syntax::node(
                kind(&["obtain"]),
                vec![atom, pattern, type_, value],
            ))
        }
        // `"rcases" elimTarget,* (" with " rcasesPatLo)?`
        "rcases" => {
            let with = split(tokens, body.clone(), "with").first().copied();
            let targets_range = body.start..with.unwrap_or(body.end);
            if targets_range.is_empty() {
                return Err(refusal(view, tokens, body.start));
            }
            let mut targets = Vec::new();
            let mut start = targets_range.start;
            for comma in split(tokens, targets_range.clone(), ",")
                .into_iter()
                .chain(std::iter::once(targets_range.end))
            {
                let named = comma > start + 2
                    && matches!(&tokens[start].kind, TokenKind::Ident(_))
                    && is(tokens, start + 1, ":");
                // `elimTarget := atomic(binderIdent " : ")? term`, as `cases`'s.
                let binder = if named {
                    null_node(vec![
                        Syntax::node(
                            Name::from_components(["Lean", "binderIdent"]),
                            vec![leaves.leaf(start)?],
                        ),
                        leaves.leaf(start + 1)?,
                    ])
                } else {
                    null_node(Vec::new())
                };
                let term_start = if named { start + 2 } else { start };
                targets.push(Syntax::node(
                    kind(&["elimTarget"]),
                    vec![
                        binder,
                        bounded_term(
                            leaves,
                            view,
                            tokens,
                            term_start..comma,
                            DefinitionGrammar::Scalar,
                        )?,
                    ],
                ));
                if comma < targets_range.end {
                    targets.push(leaves.leaf(comma)?);
                }
                start = comma + 1;
            }
            let with = match with {
                Some(with) => {
                    if with + 1 >= body.end {
                        return Err(refusal(view, tokens, with));
                    }
                    null_node(vec![
                        atom_at(leaves, with, "with")?,
                        patterns.lo(with + 1..body.end, 0)?,
                    ])
                }
                None => null_node(Vec::new()),
            };
            Ok(Syntax::node(
                kind(&["rcases"]),
                vec![atom, null_node(targets), with],
            ))
        }
        // `syntax (name := ext) "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic`
        // (`Init/Ext.lean`).
        "ext" => {
            let colon = split(tokens, body.clone(), ":").first().copied();
            let units = patterns.rintro_units(body.start..colon.unwrap_or(body.end))?;
            let depth = match colon {
                Some(colon)
                    if colon + 2 == body.end
                        && matches!(
                            &tokens[colon + 1].kind,
                            TokenKind::Literal(LiteralKind::Nat)
                        ) =>
                {
                    null_node(vec![
                        leaves.leaf(colon)?,
                        Syntax::node(
                            Name::str(Name::anonymous(), "num"),
                            vec![leaves.leaf(colon + 1)?],
                        ),
                    ])
                }
                Some(colon) => return Err(refusal(view, tokens, colon)),
                None => null_node(Vec::new()),
            };
            Ok(Syntax::node(
                Name::from_components(["Lean", "Elab", "Tactic", "Ext", "ext"]),
                vec![atom, null_node(units), depth],
            ))
        }
        // `syntax "ext1" (colGt ppSpace rintroPat)* : tactic` (`Init/Ext.lean`).
        "ext1" => {
            let units = patterns.rintro_units(body.clone())?;
            Ok(Syntax::node(
                Name::from_components(["Lean", "Elab", "Tactic", "Ext", "tacticExt1___"]),
                vec![atom, null_node(units)],
            ))
        }
        // `"rintro" (ppSpace colGt rintroPat)+ (" : " term)?`; only `rintroPat.one`.
        "rintro" => {
            let colon = split(tokens, body.clone(), ":").first().copied();
            let units = patterns.rintro_units(body.start..colon.unwrap_or(body.end))?;
            if units.is_empty() {
                return Err(refusal(view, tokens, body.start));
            }
            let type_ = match colon {
                Some(colon) => null_node(vec![
                    leaves.leaf(colon)?,
                    bounded_term(
                        leaves,
                        view,
                        tokens,
                        colon + 1..body.end,
                        DefinitionGrammar::Scalar,
                    )?,
                ]),
                None => null_node(Vec::new()),
            };
            Ok(Syntax::node(
                kind(&["rintro"]),
                vec![atom, null_node(units), type_],
            ))
        }
        _ => Err(refusal(view, tokens, range.start)),
    }
}

/// The keyword-like token at `at` as the atom `text` (`with` is a symbol, an atom already).
fn atom_at(leaves: &Leaves, at: usize, text: &str) -> Result<Syntax, NatDefinitionParseError> {
    let leaf = leaves.leaf(at)?;
    Ok(Syntax::Atom {
        info: leaf.info(),
        val: text.to_string(),
    })
}
