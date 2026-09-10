//! Heap-planned tactic sequences with scoped `cases` and `induction` alternatives.
//! Each alternative retains its original leaves and owns a complete tactic
//! sequence. Nested eliminations are parsed without recursing on the host stack.
use super::*;

struct Alternative {
    pipe: usize,
    arrow: usize,
    body: Range<usize>,
}
struct Elimination {
    start: usize,
    target: usize,
    generalizing: Option<Range<usize>>,
    with: Option<usize>,
    alternatives: Vec<Alternative>,
    end: usize,
}
enum Plan {
    Plain(Range<usize>),
    Eliminate(Elimination),
}
enum Task {
    Sequence(Range<usize>),
    Plain(Range<usize>),
    Eliminate(Elimination),
    FinishSequence(Vec<Option<usize>>),
    FinishElimination(Elimination),
}
fn word(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(name)) if name == &Name::from_components([text]))
}
fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}
fn column(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    let pos = tokens[at].extent.start();
    let source = view.normalized();
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
fn delimiter_depth(token: &LexedToken, depth: &mut usize) {
    if let TokenKind::Symbol(s) = &token.kind {
        match s.as_str() {
            "(" | "[" | "{" | "⦃" => *depth += 1,
            ")" | "]" | "}" | "⦄" => *depth = depth.saturating_sub(1),
            _ => {}
        }
    }
}
fn plain_end(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
    baseline: usize,
) -> usize {
    let mut depth = 0;
    for at in start..end {
        if depth == 0
            && (symbol(tokens, at, ";")
                || at > start && newline(view, tokens, at) && column(view, tokens, at) <= baseline)
        {
            return at;
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    end
}
fn plan_elimination(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
    baseline: usize,
) -> Result<Elimination, NatDefinitionParseError> {
    let target = start + 1;
    let header_limit = plain_end(view, tokens, start, limit, baseline);
    if target >= header_limit || !matches!(&tokens[target].kind, TokenKind::Ident(_)) {
        return Err(refusal(view, tokens, target));
    }
    let mut at = target + 1;
    let generalizing = if at < header_limit && word(tokens, at, "generalizing") {
        if !word(tokens, start, "induction") {
            return Err(refusal(view, tokens, at));
        }
        let begin = at;
        at += 1;
        while at < header_limit && matches!(&tokens[at].kind, TokenKind::Ident(_)) {
            at += 1;
        }
        if at == begin + 1 {
            return Err(refusal(view, tokens, at));
        }
        Some(begin..at)
    } else {
        None
    };
    let mut result = Elimination {
        start,
        target,
        generalizing,
        with: None,
        alternatives: Vec::new(),
        end: at,
    };
    if at == header_limit {
        return Ok(result);
    }
    if !symbol(tokens, at, "with") || at + 1 >= limit || !symbol(tokens, at + 1, "|") {
        return Err(refusal(view, tokens, at));
    }
    result.with = Some(at);
    let first = at + 1;
    let pipe_column = column(view, tokens, first);
    let mut pipes = Vec::new();
    let mut depth = 0;
    let mut end = limit;
    for at in first..limit {
        let fresh_line = newline(view, tokens, at);
        if depth == 0
            && at > first
            && fresh_line
            && column(view, tokens, at) <= pipe_column
            && !(column(view, tokens, at) == pipe_column && symbol(tokens, at, "|"))
        {
            end = at;
            break;
        }
        if depth == 0
            && symbol(tokens, at, "|")
            && (at == first || !fresh_line || column(view, tokens, at) == pipe_column)
        {
            // An inline nested elimination must be parenthesized; multiline
            // nesting uses a strictly deeper alternative indentation.
            pipes.push(at);
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    for (index, pipe) in pipes.iter().copied().enumerate() {
        let stop = pipes.get(index + 1).copied().unwrap_or(end);
        if pipe + 1 >= stop || !matches!(&tokens[pipe + 1].kind, TokenKind::Ident(_)) {
            return Err(refusal(view, tokens, pipe + 1));
        }
        let mut arrow = pipe + 2;
        while arrow < stop
            && (matches!(&tokens[arrow].kind, TokenKind::Ident(_)) || symbol(tokens, arrow, "_"))
        {
            arrow += 1;
        }
        if arrow + 1 >= stop || !(symbol(tokens, arrow, "=>") || symbol(tokens, arrow, "↦")) {
            return Err(refusal(view, tokens, arrow));
        }
        result.alternatives.push(Alternative {
            pipe,
            arrow,
            body: arrow + 1..stop,
        });
    }
    result.end = end;
    Ok(result)
}
fn split(
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<(Vec<Plan>, Vec<Option<usize>>), NatDefinitionParseError> {
    if range.is_empty() {
        return Err(refusal(view, tokens, range.start));
    }
    let baseline = column(view, tokens, range.start);
    let mut cursor = range.start;
    let mut plans = Vec::new();
    let mut separators = Vec::new();
    while cursor < range.end {
        let (plan, end) = if word(tokens, cursor, "cases") || word(tokens, cursor, "induction") {
            let plan = plan_elimination(view, tokens, cursor, range.end, baseline)?;
            let end = plan.end;
            (Plan::Eliminate(plan), end)
        } else {
            let end = plain_end(view, tokens, cursor, range.end, baseline);
            if end == cursor {
                return Err(refusal(view, tokens, cursor));
            }
            (Plan::Plain(cursor..end), end)
        };
        plans.push(plan);
        cursor = end;
        if cursor < range.end && symbol(tokens, cursor, ";") {
            separators.push(Some(cursor));
            cursor += 1;
        } else {
            separators.push(None);
            if cursor < range.end && column(view, tokens, cursor) != baseline {
                return Err(refusal(view, tokens, cursor));
            }
        }
    }
    Ok((plans, separators))
}
fn atom(leaves: &Leaves, at: usize, text: &str) -> Result<Syntax, NatDefinitionParseError> {
    Ok(Syntax::Atom {
        info: leaves.leaf(at)?.info(),
        val: text.to_string(),
    })
}
pub(super) fn sequence(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut tasks = vec![Task::Sequence(range)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Sequence(range) => {
                let (plans, separators) = split(view, tokens, range)?;
                tasks.push(Task::FinishSequence(separators));
                tasks.extend(plans.into_iter().rev().map(|plan| match plan {
                    Plan::Plain(range) => Task::Plain(range),
                    Plan::Eliminate(plan) => Task::Eliminate(plan),
                }));
            }
            Task::Plain(range) => values.push(tactic(leaves, view, tokens, range)?),
            Task::Eliminate(plan) => {
                let bodies: Vec<_> = plan
                    .alternatives
                    .iter()
                    .map(|alt| alt.body.clone())
                    .collect();
                tasks.push(Task::FinishElimination(plan));
                tasks.extend(bodies.into_iter().rev().map(Task::Sequence));
            }
            Task::FinishSequence(separators) => {
                let count = separators.len();
                let children = values.split_off(values.len() - count);
                let mut rows = Vec::new();
                for (index, (child, separator)) in children.into_iter().zip(separators).enumerate()
                {
                    rows.push(child);
                    if let Some(separator) = separator {
                        rows.push(leaves.leaf(separator)?);
                    } else if index + 1 < count {
                        rows.push(Syntax::Missing);
                    }
                }
                values.push(Syntax::node(
                    parser_kind(&["Tactic", "tacticSeq"]),
                    vec![Syntax::node(
                        parser_kind(&["Tactic", "tacticSeq1Indented"]),
                        vec![null_node(rows)],
                    )],
                ));
            }
            Task::FinishElimination(plan) => {
                let children = values.split_off(values.len() - plan.alternatives.len());
                let mut alts = Vec::new();
                for (alt, body) in plan.alternatives.into_iter().zip(children) {
                    let names = (alt.pipe + 2..alt.arrow)
                        .map(|at| leaves.leaf(at))
                        .collect::<Result<Vec<_>, _>>()?;
                    alts.push(Syntax::node(
                        parser_kind(&["Tactic", "inductionAlt"]),
                        vec![
                            leaves.leaf(alt.pipe)?,
                            leaves.leaf(alt.pipe + 1)?,
                            null_node(names),
                            leaves.leaf(alt.arrow)?,
                            body,
                        ],
                    ));
                }
                let generalizing = if let Some(range) = plan.generalizing {
                    let mut fields = vec![atom(leaves, range.start, "generalizing")?];
                    fields.extend(
                        (range.start + 1..range.end)
                            .map(|at| leaves.leaf(at))
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    null_node(fields)
                } else {
                    null_node(Vec::new())
                };
                let keyword = if word(tokens, plan.start, "cases") {
                    "cases"
                } else {
                    "induction"
                };
                values.push(Syntax::node(
                    parser_kind(&["Tactic", keyword]),
                    vec![
                        atom(leaves, plan.start, keyword)?,
                        leaves.leaf(plan.target)?,
                        generalizing,
                        null_node(
                            plan.with
                                .map(|at| leaves.leaf(at))
                                .transpose()?
                                .into_iter()
                                .collect(),
                        ),
                        null_node(alts),
                    ],
                ));
            }
        }
    }
    Ok(values.pop().expect("root tactic sequence"))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scoped_elimination_syntax_preserves_every_original_leaf() {
        for source in [
            "-- proof\r\ntheorem self (n : Nat) : n = n := by\r\n  induction n with\r\n  | zero => rfl -- base\r\n  | succ k ih => rfl\r\n",
            "theorem self (n acc : Nat) : n = n := by induction n generalizing acc with | zero => rfl | succ k _ => rfl",
            "theorem self (a b : Bool) : a = a := by\n  cases a with\n  | false =>\n    cases b with\n    | false => rfl\n    | true => rfl\n  | true => rfl",
            "def cases (n : Nat) : Nat := n",
            "def induction (n : Nat) : Nat := n",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
    }
    #[test]
    fn malformed_eliminations_never_drop_a_branch_or_unrecognized_modifier() {
        for source in [
            "theorem t := by cases",
            "theorem t := by cases (f x)",
            "theorem t := by cases n with",
            "theorem t := by cases n with | zero =>",
            "theorem t := by induction n generalizing with | zero => rfl",
            "theorem t := by cases n generalizing h",
            "theorem t := by induction n using fake with | zero => rfl",
            "theorem t := by cases n with | zero => rfl\n | succ k => rfl",
            "theorem t := by cases n with | zero 2 => rfl",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn nested_tactic_alternatives_use_heap_frames() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let depth = 400;
                let mut source = String::from("theorem t (b : Bool) : b = b := by\n");
                for level in 0..depth {
                    let indent = "  ".repeat(level + 1);
                    source.push_str(&format!("{indent}cases b with\n{indent}| false =>\n"));
                }
                source.push_str(&format!("{}rfl\n", "  ".repeat(depth + 1)));
                for level in (0..depth).rev() {
                    source.push_str(&format!("{}| true => rfl\n", "  ".repeat(level + 1)));
                }
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
