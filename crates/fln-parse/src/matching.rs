//! Constructor match syntax planned on a heap stack before term parsing.
//!
//! Each nested match is consumed once, inside out. This avoids recursive calls
//! to the term parser and preserves original leaves, including comments/CRLF.
//! The bounded lane has one discriminant and flat constructor patterns. Nested
//! matches may be parenthesized or separated by strictly indented alternatives.
use super::*;
use std::collections::{HashMap, HashSet};
use std::ops::Range;

pub(super) type Splices = HashMap<usize, (usize, Syntax)>;
struct Alternative {
    pipe: usize,
    arrow: Option<usize>,
    end: usize,
}
struct MatchPlan {
    start: usize,
    depth: usize,
    with: Option<usize>,
    alternatives: Vec<Alternative>,
    end: usize,
}
fn is_symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|token| &token.kind), Some(TokenKind::Symbol(s)) if s == text)
}
fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::MatchAlternative,
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
fn later_line(view: &SourceView, tokens: &[LexedToken], a: usize, b: usize) -> bool {
    view.normalized().line_of(tokens[a].extent.start())
        > view.normalized().line_of(tokens[b].extent.start())
}
fn close(
    view: &SourceView,
    tokens: &[LexedToken],
    active: &mut Vec<MatchPlan>,
    done: &mut Vec<MatchPlan>,
    end: usize,
) -> Result<(), NatDefinitionParseError> {
    let mut plan = active.pop().expect("active match");
    let last = plan
        .alternatives
        .last_mut()
        .ok_or_else(|| refuse(view, tokens, end))?;
    if plan.with.is_none() || last.arrow.is_none_or(|arrow| arrow + 1 >= end) {
        return Err(refuse(view, tokens, end));
    }
    last.end = end;
    plan.end = end;
    done.push(plan);
    Ok(())
}
fn plan(
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Vec<MatchPlan>, NatDefinitionParseError> {
    let mut delimiters = Vec::new();
    let mut active: Vec<MatchPlan> = Vec::new();
    let mut lets = Vec::new();
    let mut done = Vec::new();
    for at in range.clone() {
        let TokenKind::Symbol(symbol) = &tokens[at].kind else {
            continue;
        };
        let depth = delimiters.len();
        match symbol.as_str() {
            "match" => active.push(MatchPlan {
                start: at,
                depth,
                with: None,
                alternatives: Vec::new(),
                end: range.end,
            }),
            "let" => lets.push((depth, active.len())),
            ";" => {
                // A let's separator ends matches in its VALUE, not the outer
                // match whose branch contains the let and its continuation.
                let enclosing = if lets.last().is_some_and(|(d, _)| *d == depth) {
                    lets.pop().expect("let at current depth").1
                } else {
                    0
                };
                while active.len() > enclosing && active.last().is_some_and(|p| p.depth == depth) {
                    close(view, tokens, &mut active, &mut done, at)?;
                }
            }
            "(" => delimiters.push(")"),
            "{" => delimiters.push("}"),
            "[" => delimiters.push("]"),
            "⦃" => delimiters.push("⦄"),
            ":" if lets
                .last()
                .is_some_and(|(d, enclosing)| *d == depth && active.len() <= *enclosing) => {}
            ")" | "}" | "]" | "⦄" | "," | ":" => {
                while active.last().is_some_and(|p| p.depth == depth) {
                    close(view, tokens, &mut active, &mut done, at)?;
                }
                if matches!(symbol.as_str(), ")" | "}" | "]" | "⦄")
                    && delimiters.pop() != Some(symbol.as_str())
                {
                    return Err(refuse(view, tokens, at));
                }
            }
            "with"
                if active
                    .last()
                    .is_some_and(|p| p.depth == depth && p.with.is_none()) =>
            {
                let current = active.last_mut().expect("matching depth");
                if at == current.start + 1 || !is_symbol(tokens, at + 1, "|") {
                    return Err(refuse(view, tokens, at));
                }
                current.with = Some(at);
            }
            "|" => {
                while let Some(current) = active.last() {
                    let Some(first) = current.alternatives.first() else {
                        break;
                    };
                    if current.depth == depth
                        && later_line(view, tokens, at, first.pipe)
                        && column(view, tokens, at) < column(view, tokens, first.pipe)
                    {
                        close(view, tokens, &mut active, &mut done, at)?;
                    } else {
                        break;
                    }
                }
                let current = active.last_mut().ok_or_else(|| refuse(view, tokens, at))?;
                if current.depth != depth || current.with.is_none() {
                    return Err(refuse(view, tokens, at));
                }
                if let Some(first) = current.alternatives.first()
                    && later_line(view, tokens, at, first.pipe)
                    && column(view, tokens, at) != column(view, tokens, first.pipe)
                {
                    return Err(refuse(view, tokens, at));
                }
                if let Some(last) = current.alternatives.last_mut() {
                    if last.arrow.is_none_or(|arrow| arrow + 1 >= at) {
                        return Err(refuse(view, tokens, at));
                    }
                    last.end = at;
                }
                current.alternatives.push(Alternative {
                    pipe: at,
                    arrow: None,
                    end: range.end,
                });
            }
            "=>" | "↦" if active.last().is_some_and(|p| p.depth == depth) => {
                if let Some(alt) = active.last_mut().and_then(|p| p.alternatives.last_mut())
                    && alt.arrow.is_none()
                {
                    alt.arrow = Some(at);
                }
            }
            _ => {}
        }
    }
    while !active.is_empty() {
        close(view, tokens, &mut active, &mut done, range.end)?;
    }
    if !delimiters.is_empty() {
        return Err(refuse(view, tokens, range.end));
    }
    // Descendants start later. Ownership moves into their parent rather than
    // cloning a growing Syntax tree once per enclosing match.
    done.sort_by_key(|p| std::cmp::Reverse(p.start));
    Ok(done)
}
fn pattern(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut cursor = range.start;
    let dot = is_symbol(tokens, cursor, ".");
    if dot {
        cursor += 1;
    }
    if cursor >= range.end {
        return Err(refuse(view, tokens, cursor));
    }
    let head = if is_symbol(tokens, cursor, "_") && !dot {
        Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(cursor)?])
    } else if matches!(tokens[cursor].kind, TokenKind::Ident(_)) {
        if dot {
            // dotIdent is the Reference's expected-type-driven constructor head.
            Syntax::node(
                parser_kind(&["Term", "dotIdent"]),
                vec![leaves.leaf(range.start)?, leaves.leaf(cursor)?],
            )
        } else {
            leaves.leaf(cursor)?
        }
    } else {
        return Err(refuse(view, tokens, cursor));
    };
    cursor += 1;
    let mut arguments = Vec::new();
    while cursor < range.end {
        arguments.push(if is_symbol(tokens, cursor, "_") {
            Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(cursor)?])
        } else if matches!(tokens[cursor].kind, TokenKind::Ident(_)) {
            leaves.leaf(cursor)?
        } else {
            return Err(refuse(view, tokens, cursor));
        });
        cursor += 1;
    }
    Ok(if arguments.is_empty() {
        head
    } else {
        Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![head, null_node(arguments)],
        )
    })
}

/// Parse a branch's leading let telescope without recursively parsing its
/// nested matches. Already-built child matches move out of the shared splice map.
fn branch_value(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let bounded = &tokens[..range.end];
    let (bindings, body_start) = bounded_let_bindings(view, bounded, range.start)?;
    let mut value = bounded_term_spliced(
        leaves,
        view,
        tokens,
        body_start..range.end,
        grammar,
        splices,
        updates,
    )?;
    for binding in bindings.into_iter().rev() {
        let local_value = bounded_term_spliced(
            leaves,
            view,
            tokens,
            binding.value,
            grammar,
            splices,
            updates,
        )?;
        let annotation = match binding.explicit_type {
            Some((colon, type_range)) => null_node(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![
                    leaves.leaf(colon)?,
                    bounded_term_spliced(
                        leaves, view, tokens, type_range, grammar, splices, updates,
                    )?,
                ],
            )]),
            None => null_node(vec![]),
        };
        let declaration = Syntax::node(
            parser_kind(&["Term", "letIdDecl"]),
            vec![
                Syntax::node(
                    parser_kind(&["Term", "letId"]),
                    vec![leaves.leaf(binding.name)?],
                ),
                null_node(vec![]),
                annotation,
                leaves.leaf(binding.assignment)?,
                local_value,
            ],
        );
        value = Syntax::node(
            parser_kind(&["Term", "let"]),
            vec![
                leaves.leaf(binding.keyword)?,
                Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null_node(vec![])]),
                Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]),
                leaves.leaf(binding.separator)?,
                value,
            ],
        );
    }
    Ok(value)
}

pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut splices = Splices::new();
    let updates: HashSet<_> = record_terms::update_openers(tokens, range.clone());
    if grammar == DefinitionGrammar::Scalar
        && range.clone().any(|at| is_symbol(tokens, at, "match"))
    {
        for plan in plan(view, tokens, range.clone())? {
            let with = plan.with.expect("validated match header");
            let discriminator = bounded_term_spliced(
                leaves,
                view,
                tokens,
                plan.start + 1..with,
                grammar,
                &mut splices,
                &updates,
            )?;
            let mut alternatives = Vec::new();
            for alt in plan.alternatives {
                let arrow = alt.arrow.expect("validated alternative");
                let pat = pattern(leaves, view, tokens, alt.pipe + 1..arrow)?;
                let rhs = branch_value(
                    leaves,
                    view,
                    tokens,
                    arrow + 1..alt.end,
                    grammar,
                    &mut splices,
                    &updates,
                )?;
                alternatives.push(Syntax::node(
                    parser_kind(&["Term", "matchAlt"]),
                    vec![
                        leaves.leaf(alt.pipe)?,
                        null_node(vec![null_node(vec![pat])]),
                        leaves.leaf(arrow)?,
                        rhs,
                    ],
                ));
            }
            let syntax = Syntax::node(
                parser_kind(&["Term", "match"]),
                vec![
                    leaves.leaf(plan.start)?,
                    null_node(vec![]),
                    null_node(vec![]),
                    null_node(vec![Syntax::node(
                        parser_kind(&["Term", "matchDiscr"]),
                        vec![null_node(vec![]), discriminator],
                    )]),
                    leaves.leaf(with)?,
                    Syntax::node(
                        parser_kind(&["Term", "matchAlts"]),
                        vec![null_node(alternatives)],
                    ),
                ],
            );
            splices.insert(plan.start, (plan.end, syntax));
        }
    }
    let result =
        bounded_term_spliced(leaves, view, tokens, range, grammar, &mut splices, &updates)?;
    if !splices.is_empty() {
        return Err(refuse(view, tokens, 0));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn matches_preserve_all_original_token_leaves() {
        for text in [
            "def f (b : Bool) : Nat := match b with | true => 1 | false => 0",
            "def f (b : Bool) : Nat := match b with | true => let x : Nat := 7; x | false => 0",
            "def f (b : Bool) : Nat := let x := match b with | true => let y := 1; y | false => 2; x",
            "theorem self (b : Bool) : b = b := by exact (match b with | true => rfl | false => rfl)",
            "-- hello\r\ndef f (b : Bool) : Nat := match b with\r\n  | true => 1 -- branch\r\n  | false => 0\r\n",
            "def f (b : Bool) : Nat := (match b with | true => 1 | false => 0) + 2",
            "def f (b : Bool) : Box Nat := { value := match b with | true => 1 | false => 0 }",
            "def f (b : Bool) : Nat := match b with\n  | true => match b with\n    | true => 1\n    | false => 2\n  | false => 0",
            "def f (m : Maybe Nat) : Nat := match m with | .none => 0 | .some x => x",
        ] {
            let parsed = parse_definition(text.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                text.replace("\r\n", "\n").as_bytes()
            );
        }
    }
    #[test]
    fn missing_patterns_bodies_and_ambiguous_indentation_refuse() {
        for text in [
            "def f := match b with",
            "def f := match b with | => 1",
            "def f := match b with | true =>",
            "def f := match b with | true 1",
            "def f := match b, c with | true => 1",
            "def f := match b with | true => 1\n  | false => 0",
            "def f := match b with | .some (x : Nat) => x",
        ] {
            assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
        }
    }
    #[test]
    fn deeply_nested_matches_parse_without_host_recursion() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let text = format!(
                    "def f := {}0{}",
                    "(match b with | true => ".repeat(3000),
                    " | false => 1)".repeat(3000)
                );
                let parsed = parse_definition(text.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), text.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
