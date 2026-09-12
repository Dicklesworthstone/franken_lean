//! Constructor match syntax planned on a heap stack before term parsing.
//!
//! Each nested match is consumed once, inside out. This avoids recursive calls
//! to the term parser and preserves original leaves, including comments/CRLF.
//! Discriminants and pattern columns retain their comma leaves. Parenthesized
//! constructor patterns and nested matches are both planned without host recursion.
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
    equations: bool,
) -> Result<Vec<MatchPlan>, NatDefinitionParseError> {
    let mut delimiters = Vec::new();
    let mut active: Vec<MatchPlan> = if equations {
        vec![MatchPlan {
            start: range.start,
            depth: 0,
            with: Some(range.start),
            alternatives: Vec::new(),
            end: range.end,
        }]
    } else {
        Vec::new()
    };
    let mut lets = Vec::new();
    let mut done = Vec::new();
    for at in range.clone() {
        let TokenKind::Symbol(symbol) = &tokens[at].kind else {
            continue;
        };
        let depth = delimiters.len();
        let proof_body = active.last().is_some_and(|p| {
            p.depth == depth
                && p.alternatives.last().is_some_and(|alt| {
                    alt.arrow
                        .is_some_and(|arrow| is_symbol(tokens, arrow + 1, "by") && at > arrow + 1)
                })
        });
        match symbol.as_str() {
            "match" => active.push(MatchPlan {
                start: at,
                depth,
                with: None,
                alternatives: Vec::new(),
                end: range.end,
            }),
            "let" => lets.push((depth, active.len())),
            ";" | ":" if proof_body => {}
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
                // Commas before `with`, or before a row's arrow, separate
                // columns of this match rather than terminate its branch body.
                if symbol == ","
                    && active.last().is_some_and(|p| {
                        p.depth == depth
                            && (p.with.is_none()
                                || p.alternatives.last().is_some_and(|a| a.arrow.is_none()))
                    })
                {
                    continue;
                }
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
                // Indented tactic alternatives belong to the proof parser,
                // not the surrounding expression match. Keep their leaves in
                // the original branch range for that parser to validate.
                if proof_body
                    && active
                        .last()
                        .and_then(|p| p.alternatives.first())
                        .is_some_and(|first| {
                            later_line(view, tokens, at, first.pipe)
                                && column(view, tokens, at) > column(view, tokens, first.pipe)
                        })
                {
                    continue;
                }
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
    enum Task {
        Parse(Range<usize>),
        Group(usize, usize),
        Application(usize),
    }
    let mut pairs = HashMap::new();
    let mut opens = Vec::new();
    for at in range.clone() {
        if is_symbol(tokens, at, "(") {
            opens.push(at);
        } else if is_symbol(tokens, at, ")") {
            let open = opens.pop().ok_or_else(|| refuse(view, tokens, at))?;
            pairs.insert(open, at);
        }
    }
    if !opens.is_empty() {
        return Err(refuse(view, tokens, range.end));
    }
    let mut tasks = vec![Task::Parse(range)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Group(open, close) => {
                let inner = values.pop().expect("planned pattern group");
                values.push(Syntax::node(
                    parser_kind(&["Term", "paren"]),
                    vec![
                        hygienic_lparen(leaves.leaf(open)?),
                        inner,
                        leaves.leaf(close)?,
                    ],
                ));
            }
            Task::Application(start) => {
                let arguments = values.split_off(start + 1);
                let head = values.pop().expect("planned constructor head");
                values.push(Syntax::node(
                    parser_kind(&["Term", "app"]),
                    vec![head, null_node(arguments)],
                ));
            }
            Task::Parse(range) => {
                if range.is_empty() {
                    return Err(refuse(view, tokens, range.start));
                }
                if is_symbol(tokens, range.start, "(") {
                    let close = pairs[&range.start];
                    if close + 1 != range.end {
                        return Err(refuse(view, tokens, close + 1));
                    }
                    tasks.push(Task::Group(range.start, close));
                    tasks.push(Task::Parse(range.start + 1..close));
                    continue;
                }
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
                let start = values.len();
                values.push(head);
                let mut arguments = Vec::new();
                while cursor < range.end {
                    let begin = cursor;
                    if is_symbol(tokens, cursor, "(") {
                        cursor = pairs[&cursor] + 1;
                    } else if is_symbol(tokens, cursor, ".") {
                        cursor += 2;
                    } else {
                        cursor += 1;
                    }
                    if cursor > range.end {
                        return Err(refuse(view, tokens, begin));
                    }
                    arguments.push(begin..cursor);
                }
                if !arguments.is_empty() {
                    tasks.push(Task::Application(start));
                    tasks.extend(arguments.into_iter().rev().map(Task::Parse));
                }
            }
        }
    }
    Ok(values.pop().expect("one complete pattern"))
}

/// The separators are returned as indices so reconstruction keeps their exact
/// original source attachment, including comments and CRLF whitespace.
fn columns(tokens: &[LexedToken], range: Range<usize>) -> Vec<(Range<usize>, Option<usize>)> {
    let mut depth = 0usize;
    let mut start = range.start;
    let mut result = Vec::new();
    for at in range.clone() {
        if let TokenKind::Symbol(symbol) = &tokens[at].kind {
            match symbol.as_str() {
                "(" | "{" | "[" | "⦃" => depth += 1,
                ")" | "}" | "]" | "⦄" => depth = depth.saturating_sub(1),
                "," if depth == 0 => {
                    result.push((start..at, Some(at)));
                    start = at + 1;
                }
                _ => {}
            }
        }
    }
    result.push((start..range.end, None));
    result
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
    parse_planned(leaves, view, tokens, range, grammar, false)
}

/// Declaration equations own their original pipes, patterns and bodies. The
/// enclosing plan shares the same heap stack and scope rules as nested matches.
/// No synthetic `match` text is lexed and no original token is discarded.
pub(super) fn declaration_equations(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
) -> Result<Syntax, NatDefinitionParseError> {
    if grammar != DefinitionGrammar::Scalar || !is_symbol(tokens, range.start, "|") {
        return Err(refuse(view, tokens, range.start));
    }
    parse_planned(leaves, view, tokens, range, grammar, true)
}

fn parse_planned(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
    equations: bool,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut splices = Splices::new();
    let updates: HashSet<_> = record_terms::update_openers(tokens, range.clone());
    if grammar == DefinitionGrammar::Scalar
        && (equations || range.clone().any(|at| is_symbol(tokens, at, "match")))
    {
        for plan in plan(view, tokens, range.clone(), equations)? {
            let with = plan.with.expect("validated match header");
            let equation_root = equations && plan.start == range.start;
            let mut discriminators = Vec::new();
            let discriminant_columns = if equation_root {
                Vec::new()
            } else {
                columns(tokens, plan.start + 1..with)
            };
            let arity = if equation_root {
                let first = plan.alternatives.first().expect("validated equation row");
                columns(
                    tokens,
                    first.pipe + 1..first.arrow.expect("validated arrow"),
                )
                .len()
            } else {
                discriminant_columns.len()
            };
            for (range, comma) in discriminant_columns {
                let discriminator = bounded_term_spliced(
                    leaves,
                    view,
                    tokens,
                    range,
                    grammar,
                    &mut splices,
                    &updates,
                )?;
                discriminators.push(Syntax::node(
                    parser_kind(&["Term", "matchDiscr"]),
                    vec![null_node(vec![]), discriminator],
                ));
                if let Some(comma) = comma {
                    discriminators.push(leaves.leaf(comma)?);
                }
            }
            let mut alternatives = Vec::new();
            for alt in plan.alternatives {
                let arrow = alt.arrow.expect("validated alternative");
                let pattern_columns = columns(tokens, alt.pipe + 1..arrow);
                if pattern_columns.len() != arity {
                    return Err(refuse(view, tokens, alt.pipe));
                }
                let mut patterns = Vec::new();
                for (range, comma) in pattern_columns {
                    patterns.push(pattern(leaves, view, tokens, range)?);
                    if let Some(comma) = comma {
                        patterns.push(leaves.leaf(comma)?);
                    }
                }
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
                        null_node(vec![null_node(patterns)]),
                        leaves.leaf(arrow)?,
                        rhs,
                    ],
                ));
            }
            let alternatives = Syntax::node(
                parser_kind(&["Term", "matchAlts"]),
                vec![null_node(alternatives)],
            );
            if equation_root {
                if !splices.is_empty() {
                    return Err(refuse(view, tokens, range.start));
                }
                return Ok(alternatives);
            }
            let syntax = Syntax::node(
                parser_kind(&["Term", "match"]),
                vec![
                    leaves.leaf(plan.start)?,
                    null_node(vec![]),
                    null_node(vec![]),
                    null_node(discriminators),
                    leaves.leaf(with)?,
                    alternatives,
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

#[cfg(test)]
mod matrix_tests {
    use super::*;
    #[test]
    fn column_and_nested_pattern_tokens_round_trip_losslessly() {
        for text in [
            "def f (a b : Bool) : Nat := match a /- col -/, b with | true, _ => 1 | _, _ => 2",
            "def f (x : T) : Nat := match x with | .some (.some n) => n | .some .none => 0 | .none => 0",
            "-- hi\r\ndef f (a b : Bool) : Nat := match a, b with\r\n  | true, _ => by\r\n    have h : Nat := 7\r\n    exact h\r\n  | false, _ => 0\r\n",
            "def f (a b : Bool) : Nat := match a, b with\n  | true, _ => by\n    cases b with\n    | true => exact 1\n    | false => exact 2\n  | false, _ => 0",
        ] {
            let parsed =
                parse_definition(text.as_bytes()).unwrap_or_else(|e| panic!("{text}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                text.replace("\r\n", "\n").as_bytes()
            );
        }
    }
    #[test]
    fn malformed_matrices_never_drop_a_column_or_group() {
        for pattern in [
            "",
            ", true",
            "true,",
            "true,,false",
            "(.some x",
            ".some ()",
            ".some (x : Nat)",
            ".some (x, y)",
        ] {
            let text = format!("def bad (a b : Bool) := match a, b with | {pattern} => 0");
            assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
        }
        assert!(parse_definition(b"def bad := match a, b with | true, false, true => 0").is_err());
    }
    #[test]
    fn deeply_nested_pattern_groups_fit_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let text = format!(
                    "def f (x : T) : Nat := match x with | {}n{} => n",
                    "(.some ".repeat(2000),
                    ")".repeat(2000)
                );
                let parsed = parse_definition(text.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod equation_tests {
    use super::*;
    #[test]
    fn equations_retain_original_leaves_including_nested_proofs() {
        for source in [
            "def f : Bool -> Nat | true => 1 | false => 0",
            "def f (x : Nat) : Bool -> Nat\r\n | true => x -- first\r\n | false => let y := x; y\r\n",
            "def f : Bool -> Nat\n | true => match false with\n   | true => 1\n   | false => 2\n | false => 0",
            "theorem t : forall b : Bool, b = b\n | true => by\n   have h : true = true := rfl\n   exact h\n | false => by rfl",
            "def f : Maybe (Maybe Nat) -> Nat | .none => 0 | .some (.some n) => n | .some .none => 1",
        ] {
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
    }
    #[test]
    fn equation_syntax_never_ignores_missing_or_extra_tokens() {
        for source in [
            "def f : Bool -> Nat | true 1",
            "def f : Bool -> Nat | true =>",
            "def f : Bool -> Nat | true => 1 | false =>",
            "def f : Bool -> Nat | true => 1 | false, true => 2",
            "def f : Bool -> Nat | true => 1 := 2",
            "def f : Bool -> Nat | true => 1\n   | false => 2",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        assert!(parse_nat_definition(b"def f : Nat -> Nat | n => n").is_err());
    }
}

#[cfg(test)]
mod equation_depth_tests {
    use super::*;
    #[test]
    fn nested_rhs_matches_in_equations_use_a_heap_plan() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut source = String::from("def nested : Bool -> Nat\n | true => ");
                for _ in 0..300 {
                    source.push_str("(match true with | true => ");
                }
                source.push('1');
                for _ in 0..300 {
                    source.push_str(" | false => 0)");
                }
                source.push_str("\n | false => 2\n");
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
                assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn result_type_match_is_not_confused_with_declaration_equations() {
        let source = b"def value : match true with | true => Nat | false => Nat := 7";
        let parsed = parse_definition(source).unwrap();
        assert_eq!(parsed.reconstruct_original(), source);
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source);
    }
}
