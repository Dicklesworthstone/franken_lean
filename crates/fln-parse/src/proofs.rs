//! Bounded native proof scripts, preserving real token leaves and separators.
//!
//! The lane accepts flat intro/exact/assumption/apply sequences. Parentheses
//! and lambdas in tactic arguments use the ordinary term driver. Nested `by`
//! blocks are explicitly outside this lane, so this call into the term driver
//! cannot become a recursive host-stack traversal over source-controlled depth.

use super::*;
use std::ops::Range;
mod elimination;

fn refusal(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::Tactic,
    }
}

pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    by: usize,
    limit: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let mut depth = 0_usize;
    let mut end = by + 1;
    while end < limit {
        match &tokens[end].kind {
            TokenKind::Symbol(symbol) if symbol == "by" => return Err(refusal(view, tokens, end)),
            TokenKind::Symbol(symbol) if symbol == "(" || symbol == "[" => depth += 1,
            TokenKind::Symbol(symbol) if symbol == ")" || symbol == "]" => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            TokenKind::Symbol(symbol) if symbol == "," && depth == 0 => break,
            _ => {}
        }
        end += 1;
    }
    if depth != 0 {
        return Err(refusal(view, tokens, end));
    }
    let first = by + 1;
    if first == end {
        return Err(refusal(view, tokens, first));
    }
    let source = view.normalized();
    let first_line = source.line_of(tokens[first].extent.start());
    let first_column = tokens[first].extent.start().0
        - source.line_start(first_line).expect("token line exists").0;
    let by_line = source.line_of(tokens[by].extent.start());
    let by_column =
        tokens[by].extent.start().0 - source.line_start(by_line).expect("by line exists").0;
    if first_line != by_line && first_column <= by_column {
        // For declaration bodies Lean compares indentation with the declaration
        // baseline, not the inline `by` column. Accept the common indented body
        // but reject a first tactic at the beginning of a fresh line.
        if first_column == 0 {
            return Err(refusal(view, tokens, first));
        }
    }
    let sequence = elimination::sequence(leaves, view, tokens, first..end)?;
    Ok((
        Syntax::node(
            parser_kind(&["Term", "byTactic"]),
            vec![leaves.leaf(by)?, sequence],
        ),
        end,
    ))
}

fn tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let keyword = match &tokens[start].kind {
        TokenKind::Ident(name) => [
            "intro",
            "exact",
            "assumption",
            "apply",
            "rfl",
            "rw",
            "rewrite",
            "simp",
            "subst",
        ]
        .into_iter()
        .find(|word| name == &Name::from_components([*word]))
        .ok_or_else(|| refusal(view, tokens, start))?,
        _ => return Err(refusal(view, tokens, start)),
    };
    // Tactic words are contextual: `def apply ...` must stay a legal identifier.
    // The selected tactic production gives its keyword an atom leaf.
    let leaf = leaves.leaf(start)?;
    let mut args = vec![Syntax::Atom {
        info: leaf.info(),
        val: keyword.to_string(),
    }];
    if keyword == "simp" {
        return simplify(leaves, view, tokens, range, args.remove(0));
    }
    if keyword == "rw" || keyword == "rewrite" {
        return rewrite(leaves, view, tokens, range, args.remove(0), keyword == "rw");
    }
    match keyword {
        "intro" => {
            let mut names = Vec::new();
            for index in start + 1..range.end {
                if matches!(&tokens[index].kind, TokenKind::Ident(_)) {
                    names.push(leaves.leaf(index)?);
                } else if matches!(&tokens[index].kind, TokenKind::Symbol(symbol) if symbol == "_")
                {
                    names.push(Syntax::node(
                        parser_kind(&["Term", "hole"]),
                        vec![leaves.leaf(index)?],
                    ));
                } else {
                    return Err(refusal(view, tokens, index));
                }
            }
            args.push(null_node(names));
        }
        "subst"
            if range.end == start + 2 && matches!(&tokens[start + 1].kind, TokenKind::Ident(_)) =>
        {
            args.push(leaves.leaf(start + 1)?);
        }
        "assumption" | "rfl" if range.end == start + 1 => {}
        "exact" | "apply" if range.end > start + 1 => args.push(bounded_term(
            leaves,
            view,
            tokens,
            start + 1..range.end,
            DefinitionGrammar::Scalar,
        )?),
        _ => return Err(refusal(view, tokens, start)),
    }
    Ok(Syntax::node(parser_kind(&["Tactic", keyword]), args))
}

fn rewrite(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
    close: bool,
) -> Result<Syntax, NatDefinitionParseError> {
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    if range.len() < 4 || !is(range.start + 1, "[") || !is(range.end - 1, "]") {
        return Err(refusal(view, tokens, range.start));
    }
    let mut rows = Vec::new();
    let mut start = range.start + 2;
    let mut depth = 0_usize;
    for at in (range.start + 2)..range.end {
        let end = at == range.end - 1;
        if end || (depth == 0 && is(at, ",")) {
            if at == start {
                if end && !rows.is_empty() {
                    break;
                }
                return Err(refusal(view, tokens, at));
            }
            let reverse = is(start, "←") || is(start, "<-");
            let term_start = start + usize::from(reverse);
            let direction = if reverse {
                null_node(vec![leaves.leaf(start)?])
            } else {
                null_node(Vec::new())
            };
            let term = bounded_term(
                leaves,
                view,
                tokens,
                term_start..at,
                DefinitionGrammar::Scalar,
            )?;
            rows.push(Syntax::node(
                parser_kind(&["Tactic", "rwRule"]),
                vec![direction, term],
            ));
            if !end {
                rows.push(leaves.leaf(at)?);
            }
            start = at + 1;
        } else if is(at, "(") {
            depth += 1;
        } else if is(at, ")") {
            depth = depth
                .checked_sub(1)
                .ok_or_else(|| refusal(view, tokens, at))?;
        }
    }
    if depth != 0 {
        return Err(refusal(view, tokens, range.end));
    }
    let rules = Syntax::node(
        parser_kind(&["Tactic", "rwRuleSeq"]),
        vec![
            leaves.leaf(range.start + 1)?,
            null_node(rows),
            leaves.leaf(range.end - 1)?,
        ],
    );
    Ok(Syntax::node(
        parser_kind(&["Tactic", if close { "rwSeq" } else { "rewriteSeq" }]),
        vec![keyword, null_node(Vec::new()), rules, null_node(Vec::new())],
    ))
}

/// Explicit-set simplification. Plain `simp` needs an attribute registry and
/// is refused rather than silently pretending its default simp set is empty.
fn simplify(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let only = range.start + 1;
    if !matches!(tokens.get(only).map(|t| &t.kind), Some(TokenKind::Ident(name)) if name == &Name::from_components(["only"]))
    {
        return Err(refusal(view, tokens, only));
    }
    let only_leaf = leaves.leaf(only)?;
    let only = null_node(vec![Syntax::Atom {
        info: only_leaf.info(),
        val: "only".to_string(),
    }]);
    let open = range.start + 2;
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    let arguments = if open == range.end {
        null_node(Vec::new())
    } else {
        if range.end < open + 2 || !is(open, "[") || !is(range.end - 1, "]") {
            return Err(refusal(view, tokens, open));
        }
        let mut rows = Vec::new();
        let mut start = open + 1;
        let mut depth = 0_usize;
        for at in open + 1..range.end {
            let end = at == range.end - 1;
            if end || depth == 0 && is(at, ",") {
                if at == start {
                    if end && (start == open + 1 || !rows.is_empty()) {
                        break;
                    }
                    return Err(refusal(view, tokens, at));
                }
                let reverse = is(start, "←") || is(start, "<-");
                let direction = if reverse {
                    null_node(vec![leaves.leaf(start)?])
                } else {
                    null_node(Vec::new())
                };
                let term = bounded_term(
                    leaves,
                    view,
                    tokens,
                    start + usize::from(reverse)..at,
                    DefinitionGrammar::Scalar,
                )?;
                rows.push(Syntax::node(
                    parser_kind(&["Tactic", "simpLemma"]),
                    vec![null_node(Vec::new()), direction, term],
                ));
                if !end {
                    rows.push(leaves.leaf(at)?);
                }
                start = at + 1;
            } else if is(at, "(") {
                depth += 1;
            } else if is(at, ")") {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| refusal(view, tokens, at))?;
            }
        }
        if depth != 0 {
            return Err(refusal(view, tokens, range.end));
        }
        null_node(vec![
            leaves.leaf(open)?,
            null_node(rows),
            leaves.leaf(range.end - 1)?,
        ])
    };
    Ok(Syntax::node(
        parser_kind(&["Tactic", "simp"]),
        vec![
            keyword,
            null_node(Vec::new()),
            null_node(Vec::new()),
            only,
            arguments,
            null_node(Vec::new()),
        ],
    ))
}

#[cfg(test)]
mod simp_tests {
    use super::*;

    #[test]
    fn simp_only_accepts_empty_ordered_reverse_and_multiline_rule_lists() {
        for source in [
            "theorem t (x : Nat) : x = x := by simp only []",
            "theorem t (x : Nat) : x = x := by simp only",
            "theorem t (x : Nat) : x = x := by simp only [h, <- k,]",
            "theorem t (x : Nat) : x = x := by\n  simp only [h,\n    <- k]\n  exact p",
        ] {
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            let mut pending = vec![&parsed.syntax];
            let mut found = false;
            while let Some(syntax) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = syntax {
                    if kind == &parser_kind(&["Tactic", "simp"]) {
                        assert_eq!(args.len(), 6);
                        assert!(
                            matches!(&args[3], Syntax::Node { args, .. } if matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "only"))
                        );
                        found = true;
                    }
                    pending.extend(args);
                }
            }
            assert!(found);
        }
    }

    #[test]
    fn unsupported_simp_features_are_not_silently_ignored() {
        for tail in [
            "simp",
            "subst",
            "simp [h]",
            "simp only [h] at h",
            "simp only [*]",
            "simp only [,h]",
            "simp only [h,,k]",
            "simp only [<-]",
            "simp only [h] garbage",
            "simp only [by rfl]",
        ] {
            let source = format!("theorem t (x : Nat) : x = x := by {tail}");
            assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
        }
        assert!(parse_definition(b"def simp (only : Nat) := only").is_ok());
    }
}

#[cfg(test)]
mod equality_tests {
    use super::*;
    #[test]
    fn substitution_is_contextual_and_requires_a_single_local_name() {
        assert!(parse_definition(b"def subst (x : Nat) := x").is_ok());
        for tail in ["subst h", "subst x"] {
            assert!(
                parse_source_command(
                    format!("theorem t (x y : Nat) (h : x = y) : x = y := by {tail}; rfl")
                        .as_bytes()
                )
                .is_ok()
            );
        }
        for tail in [
            "subst",
            "subst 2",
            "subst (h)",
            "subst h at x",
            "subst h, x",
        ] {
            assert!(
                parse_source_command(
                    format!("theorem t (x : Nat) : x = x := by {tail}").as_bytes()
                )
                .is_err(),
                "{tail}"
            );
        }
    }
}
