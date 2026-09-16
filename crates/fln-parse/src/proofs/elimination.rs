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
struct Binding {
    start: usize,
    name: Option<usize>,
    annotation: Option<(usize, Range<usize>)>,
    assign: usize,
    value: Range<usize>,
    by: Option<usize>,
    end: usize,
    opaque: bool,
}
struct Control {
    start: usize,
    body: Range<usize>,
    end: usize,
    keyword: &'static str,
    kind: &'static str,
    baseline: usize,
}
struct Chain {
    left: Range<usize>,
    separator: usize,
    right: Range<usize>,
}
struct Choice {
    start: usize,
    branches: Vec<(usize, Range<usize>)>,
    end: usize,
}
enum Plan {
    Choice(Choice),
    Chain(Chain),
    Group(Range<usize>),
    Control(Control),
    Plain(Range<usize>),
    Bind(Binding),
    Eliminate(Elimination),
}
enum Task {
    Choice(Choice),
    FinishChoice(Choice),
    Chain(Chain),
    FinishChain(usize),
    Group(Range<usize>),
    FinishGroup(usize, usize),
    Control(Control),
    FinishControl(Control),
    Sequence(Range<usize>, Option<usize>),
    Plain(Range<usize>),
    Eliminate(Elimination),
    FinishSequence(Vec<Option<usize>>),
    FinishElimination(Elimination),
    Bind(Binding),
    FinishBinding(Binding),
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
            "(" | "[" | "{" | ".{" | "⦃" => *depth += 1,
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
    let mut nested_lets = 0usize;
    for at in start..end {
        if depth == 0 && at > start && symbol(tokens, at, "let") {
            nested_lets += 1;
        }
        if depth == 0 && symbol(tokens, at, ";") && nested_lets > 0 {
            nested_lets -= 1;
            continue;
        }
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
fn control_word(tokens: &[LexedToken], at: usize) -> Option<(&'static str, &'static str)> {
    if symbol(tokens, at, "·") {
        Some(("·", "cdot"))
    } else if word(tokens, at, "focus") {
        Some(("focus", "focus"))
    } else if word(tokens, at, "all_goals") {
        Some(("all_goals", "allGoals"))
    } else if word(tokens, at, "try") {
        Some(("try", "try"))
    } else if word(tokens, at, "repeat") {
        Some(("repeat", "repeat"))
    } else {
        None
    }
}
fn plan_choice(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
    baseline: usize,
) -> Result<Choice, NatDefinitionParseError> {
    let first = start + 1;
    if first >= limit || !symbol(tokens, first, "|") {
        return Err(refusal(view, tokens, first));
    }
    let pipe_column = column(view, tokens, first);
    let mut pipes = vec![first];
    let mut depth = 0;
    let mut term_pipes = false;
    let mut end = limit;
    for at in first + 1..limit {
        if depth == 0 {
            let fresh = newline(view, tokens, at);
            if fresh
                && column(view, tokens, at) <= baseline
                && !(symbol(tokens, at, "|") && column(view, tokens, at) == pipe_column)
            {
                end = at;
                break;
            }
            let source = view.normalized();
            let line_start = source
                .line_start(source.line_of(tokens[at].extent.start()))
                .expect("choice line")
                .0;
            let line_indent = source.as_bytes()[line_start..tokens[at].extent.start().0]
                .iter()
                .take_while(|&&b| b == b' ' || b == b'\t')
                .count();
            if symbol(tokens, at, "|")
                && (fresh && column(view, tokens, at) == pipe_column
                    || !fresh && line_indent <= pipe_column && !term_pipes)
            {
                pipes.push(at);
                term_pipes = false;
            } else if symbol(tokens, at, "match")
                || symbol(tokens, at, "with")
                || ((symbol(tokens, at, "fun") || symbol(tokens, at, "λ"))
                    && symbol(tokens, at + 1, "|"))
            {
                // The expression/scoped-elimination planner owns its pipes.
                // An outer pipe at this block's indentation resumes the choice.
                term_pipes = true;
            }
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    if depth != 0 {
        return Err(refusal(view, tokens, end));
    }
    let mut branches = Vec::with_capacity(pipes.len());
    for (index, pipe) in pipes.iter().copied().enumerate() {
        let stop = pipes.get(index + 1).copied().unwrap_or(end);
        if pipe + 1 == stop {
            return Err(refusal(view, tokens, pipe));
        }
        branches.push((pipe, pipe + 1..stop));
    }
    Ok(Choice {
        start,
        branches,
        end,
    })
}
fn plan_control(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
    baseline: usize,
    keyword: &'static str,
    kind: &'static str,
) -> Result<Control, NatDefinitionParseError> {
    let body = start + 1;
    let mut depth = 0;
    let mut end = limit;
    for at in body..limit {
        if depth == 0 && newline(view, tokens, at) && column(view, tokens, at) <= baseline {
            end = at;
            break;
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    if body == end || depth != 0 {
        return Err(refusal(view, tokens, body));
    }
    let mut body_baseline = column(view, tokens, body);
    if !newline(view, tokens, body) {
        let mut depth = 0;
        for at in body..end {
            if depth == 0 && newline(view, tokens, at) {
                body_baseline = body_baseline.min(column(view, tokens, at));
            }
            delimiter_depth(&tokens[at], &mut depth);
        }
    }
    Ok(Control {
        start,
        body: body..end,
        end,
        keyword,
        kind,
        baseline: body_baseline,
    })
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
    let mut in_body = false;
    let mut nested_pipes = false;
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
            && (at == first
                || !fresh_line && !nested_pipes
                || fresh_line && column(view, tokens, at) == pipe_column)
        {
            // A nested choice owns its inline pipes. The next constructor
            // alternative resumes at the original pipe indentation.
            pipes.push(at);
            in_body = false;
            nested_pipes = false;
        } else if depth == 0 {
            if symbol(tokens, at, "=>") || symbol(tokens, at, "↦") {
                in_body = true;
            } else if in_body
                && (word(tokens, at, "first")
                    || symbol(tokens, at, "match")
                    || ((symbol(tokens, at, "fun") || symbol(tokens, at, "λ"))
                        && symbol(tokens, at + 1, "|")))
            {
                nested_pipes = true;
            }
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
fn plan_binding(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
    baseline: usize,
) -> Result<Binding, NatDefinitionParseError> {
    let opaque = word(tokens, start, "have");
    let preliminary_end = plain_end(view, tokens, start, limit, baseline);
    let mut cursor = start + 1;
    let name = if cursor < preliminary_end && matches!(&tokens[cursor].kind, TokenKind::Ident(_)) {
        let at = cursor;
        cursor += 1;
        Some(at)
    } else {
        None
    };
    if !opaque && name.is_none() {
        return Err(refusal(view, tokens, cursor));
    }
    let colon = if symbol(tokens, cursor, ":") {
        let at = cursor;
        cursor += 1;
        Some(at)
    } else {
        None
    };
    let type_start = cursor;
    let mut depth = 0;
    while cursor < preliminary_end {
        if depth == 0 && symbol(tokens, cursor, ":=") {
            break;
        }
        if colon.is_none() {
            return Err(refusal(view, tokens, cursor));
        }
        delimiter_depth(&tokens[cursor], &mut depth);
        cursor += 1;
    }
    if cursor + 1 >= preliminary_end
        || depth != 0
        || !symbol(tokens, cursor, ":=")
        || colon.is_some() && type_start == cursor
    {
        return Err(refusal(view, tokens, cursor));
    }
    let assign = cursor;
    let by = symbol(tokens, assign + 1, "by").then_some(assign + 1);
    let end = if by.is_some() {
        // Semicolons inside the nested proof belong to that proof. A new line
        // at the enclosing sequence's indentation closes it, not a guessed
        // tactic count. Bracket delimiters are still respected.
        let mut depth = 0;
        let mut end = limit;
        for at in assign + 2..limit {
            if depth == 0 && newline(view, tokens, at) && column(view, tokens, at) <= baseline {
                end = at;
                break;
            }
            delimiter_depth(&tokens[at], &mut depth);
        }
        end
    } else {
        preliminary_end
    };
    let value = assign + 1 + usize::from(by.is_some())..end;
    if value.is_empty() {
        return Err(refusal(view, tokens, value.start));
    }
    Ok(Binding {
        start,
        name,
        annotation: colon.map(|at| (at, type_start..assign)),
        assign,
        value,
        by,
        end,
        opaque,
    })
}

fn binding_term(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if let Some(at) = range.clone().find(|&at| symbol(tokens, at, "by")) {
        return Err(refusal(view, tokens, at));
    }
    bounded_term(leaves, view, tokens, range, DefinitionGrammar::Scalar)
}

fn finish_binding(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: Binding,
    value: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let keyword = if plan.opaque { "have" } else { "let" };
    let name = null_node(
        plan.name
            .map(|at| leaves.leaf(at))
            .transpose()?
            .into_iter()
            .collect(),
    );
    let annotation = match plan.annotation {
        Some((colon, range)) => null_node(vec![Syntax::node(
            parser_kind(&["Term", "typeSpec"]),
            vec![
                leaves.leaf(colon)?,
                binding_term(leaves, view, tokens, range)?,
            ],
        )]),
        None => null_node(Vec::new()),
    };
    let value = match plan.by {
        Some(at) => Syntax::node(
            parser_kind(&["Term", "byTactic"]),
            vec![leaves.leaf(at)?, value],
        ),
        None => value,
    };
    Ok(Syntax::node(
        parser_kind(&["Tactic", keyword]),
        vec![
            atom(leaves, plan.start, keyword)?,
            name,
            annotation,
            leaves.leaf(plan.assign)?,
            value,
        ],
    ))
}

/// Sequence-level combinators cannot capture operators inside term arguments,
/// local proof values, or constructor alternatives. Those own their subranges.
fn chain_at(tokens: &[LexedToken], range: Range<usize>) -> Option<usize> {
    let mut depth = 0;
    for at in range {
        if depth == 0 {
            if symbol(tokens, at, "<;>") {
                return Some(at);
            }
            if symbol(tokens, at, ":=") || symbol(tokens, at, "with") {
                return None;
            }
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    None
}

fn split(
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    baseline: Option<usize>,
) -> Result<(Vec<Plan>, Vec<Option<usize>>), NatDefinitionParseError> {
    if range.is_empty() {
        return Err(refusal(view, tokens, range.start));
    }
    let baseline = baseline.unwrap_or_else(|| column(view, tokens, range.start));
    let mut cursor = range.start;
    let mut plans = Vec::new();
    let mut separators = Vec::new();
    while cursor < range.end {
        let (plan, end) = if word(tokens, cursor, "first") {
            let plan = plan_choice(view, tokens, cursor, range.end, baseline)?;
            let end = plan.end;
            (Plan::Choice(plan), end)
        } else if let Some((keyword, kind)) = control_word(tokens, cursor) {
            let plan = plan_control(view, tokens, cursor, range.end, baseline, keyword, kind)?;
            let end = plan.end;
            (Plan::Control(plan), end)
        } else if let Some(separator) = chain_at(
            tokens,
            cursor..plain_end(view, tokens, cursor, range.end, baseline),
        ) {
            let end = plain_end(view, tokens, cursor, range.end, baseline);
            if separator == cursor || separator + 1 == end {
                return Err(refusal(view, tokens, separator));
            }
            (
                Plan::Chain(Chain {
                    left: cursor..separator,
                    separator,
                    right: separator + 1..end,
                }),
                end,
            )
        } else if symbol(tokens, cursor, "(") {
            let end = plain_end(view, tokens, cursor, range.end, baseline);
            if end <= cursor + 2 || !symbol(tokens, end - 1, ")") {
                return Err(refusal(view, tokens, cursor));
            }
            let mut depth = 0;
            for at in cursor..end {
                delimiter_depth(&tokens[at], &mut depth);
                if depth == 0 && at != end - 1 {
                    return Err(refusal(view, tokens, at));
                }
            }
            if depth != 0 {
                return Err(refusal(view, tokens, end));
            }
            (Plan::Group(cursor..end), end)
        } else if word(tokens, cursor, "have") || symbol(tokens, cursor, "let") {
            let plan = plan_binding(view, tokens, cursor, range.end, baseline)?;
            let end = plan.end;
            (Plan::Bind(plan), end)
        } else if word(tokens, cursor, "cases") || word(tokens, cursor, "induction") {
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
    let mut tasks = vec![Task::Sequence(range, None)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Sequence(range, baseline) => {
                let (plans, separators) = split(view, tokens, range, baseline)?;
                tasks.push(Task::FinishSequence(separators));
                tasks.extend(plans.into_iter().rev().map(|plan| match plan {
                    Plan::Choice(plan) => Task::Choice(plan),
                    Plan::Chain(plan) => Task::Chain(plan),
                    Plan::Group(range) => Task::Group(range),
                    Plan::Plain(range) => Task::Plain(range),
                    Plan::Control(plan) => Task::Control(plan),
                    Plan::Bind(plan) => Task::Bind(plan),
                    Plan::Eliminate(plan) => Task::Eliminate(plan),
                }));
            }
            Task::Choice(plan) => {
                let ranges: Vec<_> = plan
                    .branches
                    .iter()
                    .map(|(_, range)| range.clone())
                    .collect();
                tasks.push(Task::FinishChoice(plan));
                tasks.extend(
                    ranges
                        .into_iter()
                        .rev()
                        .map(|range| Task::Sequence(range, None)),
                );
            }
            Task::FinishChoice(plan) => {
                let bodies = values.split_off(values.len() - plan.branches.len());
                let mut branches = Vec::with_capacity(bodies.len() * 2);
                for ((pipe, _), body) in plan.branches.into_iter().zip(bodies) {
                    branches.push(leaves.leaf(pipe)?);
                    branches.push(body);
                }
                values.push(Syntax::node(
                    parser_kind(&["Tactic", "first"]),
                    vec![atom(leaves, plan.start, "first")?, null_node(branches)],
                ));
            }
            Task::Chain(plan) => {
                tasks.push(Task::FinishChain(plan.separator));
                tasks.push(Task::Sequence(plan.right, None));
                tasks.push(Task::Sequence(plan.left, None));
            }
            Task::FinishChain(separator) => {
                let right = values.pop().expect("sequenced tactic right operand");
                let left = values.pop().expect("sequenced tactic left operand");
                values.push(Syntax::node(
                    parser_kind(&["Tactic", "andThen"]),
                    vec![left, leaves.leaf(separator)?, right],
                ));
            }
            Task::Group(range) => {
                tasks.push(Task::FinishGroup(range.start, range.end - 1));
                tasks.push(Task::Sequence(range.start + 1..range.end - 1, None));
            }
            Task::FinishGroup(open, close) => {
                let body = values.pop().expect("parenthesized tactic sequence");
                values.push(Syntax::node(
                    parser_kind(&["Tactic", "paren"]),
                    vec![leaves.leaf(open)?, body, leaves.leaf(close)?],
                ));
            }
            Task::Control(plan) => {
                let body = plan.body.clone();
                let baseline = plan.baseline;
                tasks.push(Task::FinishControl(plan));
                tasks.push(Task::Sequence(body, Some(baseline)));
            }
            Task::FinishControl(plan) => {
                let body = values.pop().expect("scoped tactic sequence");
                values.push(Syntax::node(
                    parser_kind(&["Tactic", plan.kind]),
                    vec![atom(leaves, plan.start, plan.keyword)?, body],
                ));
            }
            Task::Plain(range) => values.push(tactic(leaves, view, tokens, range)?),
            Task::Bind(plan) => {
                if plan.by.is_some() {
                    let range = plan.value.clone();
                    tasks.push(Task::FinishBinding(plan));
                    tasks.push(Task::Sequence(range, None));
                } else {
                    let value = binding_term(leaves, view, tokens, plan.value.clone())?;
                    values.push(finish_binding(leaves, view, tokens, plan, value)?);
                }
            }
            Task::FinishBinding(plan) => {
                let value = values.pop().expect("nested local proof sequence");
                values.push(finish_binding(leaves, view, tokens, plan, value)?);
            }
            Task::Eliminate(plan) => {
                let bodies: Vec<_> = plan
                    .alternatives
                    .iter()
                    .map(|alt| alt.body.clone())
                    .collect();
                tasks.push(Task::FinishElimination(plan));
                tasks.extend(
                    bodies
                        .into_iter()
                        .rev()
                        .map(|range| Task::Sequence(range, None)),
                );
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

#[cfg(test)]
mod goal_control_tests {
    use super::*;
    #[test]
    fn goal_scopes_preserve_original_leaves_and_statement_boundaries() {
        for source in [
            "-- scope\r\ntheorem t : 0 = 0 := by\r\n  · have h : 0 = 0 := by rfl -- inner\r\n    exact h\r\n",
            "theorem t : 0 = 0 := by\n  focus\n    all_goals rfl",
            "theorem t : 0 = 0 := by\n  focus intro n\n  rfl",
            "def focus (all_goals : Nat) : Nat := all_goals",
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
    fn missing_and_misindented_goal_scope_bodies_refuse() {
        for body in [
            "·",
            "focus",
            "all_goals",
            "·\n  rfl",
            "focus\n  rfl",
            "all_goals\n  rfl",
            "· ; rfl",
            "focus unknownTactic",
        ] {
            let source = format!("theorem t : 0 = 0 := by\n  {body}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn deeply_nested_goal_scopes_are_heap_planned() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut source = String::from("theorem t : 0 = 0 := by\n");
                for level in 0..500 {
                    source.push_str(&" ".repeat(level + 2));
                    source.push_str("focus\n");
                }
                source.push_str(&" ".repeat(502));
                source.push_str("rfl\n");
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod sequencing_tests {
    use super::*;
    #[test]
    fn tactic_sequencing_preserves_original_parentheses_and_operator_leaves() {
        for source in [
            "theorem t : 0 = 0 := by constructor <;> rfl",
            "theorem t : 0 = 0 := by\r\n  constructor <;> (intro x; rfl) -- trailing\r\n",
            "theorem t : 0 = 0 := by\n  all_goals constructor <;> (have h := p; exact h)",
            "theorem t : 0 = 0 := by\n  cases b with\n  | false => constructor <;> rfl\n  | true => constructor <;> rfl",
            "theorem t : 0 = 0 := by ((constructor; rfl); rfl)",
            "theorem t : 0 = 0 := by\n  have local : P := by\n    constructor <;> rfl\n  exact local",
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
    fn missing_sequencing_operands_and_malformed_groups_refuse() {
        for body in [
            "<;> rfl",
            "rfl <;>",
            "rfl <;> <;> rfl",
            "()",
            "(rfl) rfl",
            "(rfl",
            "rfl)",
            "constructor <;> ()",
        ] {
            let source = format!("theorem bad : 0 = 0 := by {body}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn deep_sequencing_and_parentheses_use_the_heap_plan() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                for body in [
                    format!("{}rfl{}", "(".repeat(1000), ")".repeat(1000)),
                    format!("{}rfl", "rfl <;> ".repeat(1000)),
                ] {
                    let source = format!("theorem t : 0 = 0 := by {body}");
                    let parsed = parse_definition(source.as_bytes()).unwrap();
                    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod backtracking_tests {
    use super::*;

    #[test]
    fn choice_and_try_preserve_leaf_positions_and_nested_pipe_ownership() {
        for source in [
            "theorem t : 0 = 0 := by first | fail \"no\" | rfl",
            "theorem t : 0 = 0 := by\r\n  first /- alternatives -/\r\n  | have h : 0 = 0 := by\r\n      first | fail | rfl\r\n    exact h\r\n  | rfl -- other\r\n",
            "theorem t : 0 = 0 := by\n  first\n  | have fn : Bool -> Nat := fun | true => 1 | false => 2\n    rfl\n  | fail",
            "theorem t : 0 = 0 := by\n  first\n  | cases b with\n    | false => first | fail | rfl\n    | true => rfl\n  | rfl",
            "theorem t : 0 = 0 := by try (intro x; fail); first | fail | skip",
        ] {
            let parsed = parse_definition(source.as_bytes())
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
    }

    #[test]
    fn incomplete_choices_and_try_bodies_refuse_without_discarding_tokens() {
        for body in [
            "first",
            "first rfl",
            "first |",
            "first | | rfl",
            "first | rfl |",
            "try",
            "try ()",
            "skip x",
            "fail 7",
        ] {
            let source = format!("theorem t : 0 = 0 := by {body}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn deeply_nested_choices_and_try_use_heap_parser_frames() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                for opener in ["try (", "first | fail | ("] {
                    let source = format!(
                        "theorem t : 0 = 0 := by {}rfl{}",
                        opener.repeat(1000),
                        ")".repeat(1000)
                    );
                    let parsed = parse_definition(source.as_bytes()).unwrap();
                    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod repetition_tests {
    use super::*;
    #[test]
    fn repetition_preserves_nested_choices_and_statement_boundaries() {
        for source in [
            "theorem t : 0 = 0 := by repeat (first | fail | rfl)",
            "theorem t : 0 = 0 := by\r\n  repeat /- loop -/\r\n    first\r\n    | intro x\r\n    | rfl\r\n  skip\r\n",
            "theorem t : 0 = 0 := by\n  constructor <;> repeat (intro x; rfl)",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
        for source in ["theorem t := by repeat", "theorem t := by repeat ()"] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn nested_repetition_uses_heap_parser_frames() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let source = format!(
                    "theorem t : 0 = 0 := by {}fail{}",
                    "repeat (".repeat(1000),
                    ")".repeat(1000)
                );
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
