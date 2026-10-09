//! Heap-planned tactic sequences with scoped `cases` and `induction` alternatives.
//! Each alternative retains its original leaves and owns a complete tactic
//! sequence. Nested eliminations are parsed without recursing on the host stack.
use super::*;
mod calc;

struct Alternative {
    /// Each `inductionAltLHS`: its `|` and the end of its names (`| zero | succ m => t`).
    lhs: Vec<(usize, usize)>,
    /// `=>`, absent when the alternative only names its goal's locals (`| succ m ih`) and the
    /// enclosing sequence goes on (`(" => " …)?`, `Init/Tactics.lean`).
    arrow: Option<usize>,
    body: Range<usize>,
}
struct Elimination {
    start: usize,
    /// The tactic `match`: `target` holds its discriminants, and each alternative's left-hand
    /// side is its patterns, up to the `=>`.
    matching: bool,
    target: Range<usize>,
    equation: Option<usize>,
    /// `using r`: from the `using` token to the end of its eliminator term.
    using: Option<Range<usize>>,
    generalizing: Option<Range<usize>>,
    with: Option<usize>,
    /// `with tac | …`: the tactic run on every goal before the alternatives.
    pre_tactic: Option<Range<usize>>,
    alternatives: Vec<Alternative>,
    end: usize,
}
struct Binding {
    start: usize,
    name: Option<usize>,
    /// `letPatDecl`'s pattern (`have ⟨k, hk⟩ := h`, `let (a, b) := p`), in place of a name.
    pattern: Option<Range<usize>>,
    annotation: Option<(usize, Range<usize>)>,
    assign: usize,
    value: Range<usize>,
    by: Option<usize>,
    end: usize,
    opaque: bool,
    /// `replace`: a `have` that replaces the hypothesis it names (`Init/Tactics.lean`).
    replace: bool,
    /// `letI`/`haveI`: `let`/`have` whose value is inlined (`tacticLetI__`, `tacticHaveI__`).
    inline: bool,
}
struct Control {
    start: usize,
    body: Range<usize>,
    end: usize,
    keyword: &'static str,
    kind: &'static str,
    baseline: usize,
    /// `next`'s binder names and its `=>`.
    names: Range<usize>,
    arrow: Option<usize>,
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
/// The tactic `if` (`tacIfThenElse`, `tacDepIfThenElse` with `h :`): its condition and its two
/// branches' sequences.
struct Conditional {
    start: usize,
    /// `h :`: the name and the colon.
    binder: Option<(usize, usize)>,
    condition: Range<usize>,
    then_at: usize,
    else_at: usize,
    yes: Range<usize>,
    no: Range<usize>,
    end: usize,
}
enum Plan {
    If(Conditional),
    Calc(calc::Calculation, Option<usize>),
    Choice(Choice),
    Chain(Chain),
    Group(Range<usize>),
    Control(Control),
    Plain(Range<usize>),
    Bind(Binding),
    Eliminate(Elimination),
    /// `open … in tacs`: the `open`, the `in`, and the end of the sequence after it.
    Open(usize, usize, usize),
}
enum Task {
    If(Conditional),
    FinishIf(Conditional),
    Calc(calc::Calculation),
    StartCalcTactic(calc::Calculation, Option<usize>),
    FinishCalc(calc::Calculation),
    CalcTactic(Option<usize>),
    CalcProof(Range<usize>),
    By(usize),
    Choice(Choice),
    FinishChoice(Choice),
    Chain(Chain),
    FinishChain(usize),
    Group(Range<usize>),
    FinishGroup(usize, usize),
    Open(usize, usize, usize),
    FinishOpen(usize, usize),
    Control(Control),
    FinishControl(Control),
    Sequence(Range<usize>, Option<usize>),
    Plain(Range<usize>),
    Eliminate(Elimination),
    /// The separators after each item, and whether the sequence keeps a trailing one.
    FinishSequence(Vec<Option<usize>>, bool),
    FinishElimination(Elimination),
    Bind(Binding),
    FinishBinding(Binding),
}
/// A tactic word. Some are tokens at the pin (`try`, `repeat`, `have`, `using`,
/// `generalizing`) and the rest identifiers (`cases`, `exact`), so both forms are accepted.
fn word(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    crate::term_locals::word(tokens, at, text)
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
        match crate::canonical_bracket(s.as_str()) {
            "(" | "[" | "{" | ".{" | "⦃" | "⟨" => *depth += 1,
            ")" | "]" | "}" | "⦄" | "⟩" => *depth = depth.saturating_sub(1),
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
    // A `by` outside brackets opens a tactic sequence that takes the `;`s after it
    // (`exact f <| by simp; rfl`): only a line back at `baseline` ends the tactic.
    let mut nested_by = false;
    for at in start..end {
        if depth == 0 && at > start && symbol(tokens, at, "let") {
            nested_lets += 1;
        }
        if depth == 0 && at > start && symbol(tokens, at, "by") {
            nested_by = true;
        }
        if depth == 0 && symbol(tokens, at, ";") && (nested_lets > 0 || nested_by) {
            nested_lets = nested_lets.saturating_sub(1);
            continue;
        }
        // `t <;> u` is one tactic across a line break on either side of its `<;>`.
        let continued = symbol(tokens, at, "<;>") || at > 0 && symbol(tokens, at - 1, "<;>");
        if depth == 0
            && (symbol(tokens, at, ";")
                || at > start
                    && !continued
                    && newline(view, tokens, at)
                    && column(view, tokens, at) <= baseline)
        {
            return at;
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    end
}
/// Where the tactic at `start` ends when its `;`s are its own: at the first line, outside
/// brackets, that returns to `baseline`.
fn block_end(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
    baseline: usize,
) -> usize {
    let mut depth = 0;
    for at in start..end {
        if depth == 0
            && at > start
            && newline(view, tokens, at)
            && column(view, tokens, at) <= baseline
        {
            return at;
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    end
}
fn control_word(tokens: &[LexedToken], at: usize) -> Option<(&'static str, &'static str)> {
    // `cdotTk := unicode("· ", ". ")`: the ASCII dot is the same focus.
    if symbol(tokens, at, "·") {
        Some(("·", "cdot"))
    } else if symbol(tokens, at, ".") {
        Some((".", "cdot"))
    } else if word(tokens, at, "focus") {
        Some(("focus", "focus"))
    } else if word(tokens, at, "all_goals") {
        Some(("all_goals", "allGoals"))
    } else if word(tokens, at, "try") {
        // `macro "try " t:tacticSeq : tactic` (`Init/Tactics.lean`), whose kind is `tacticTry_`.
        Some(("try", "tacticTry_"))
    } else if word(tokens, at, "repeat") {
        // `syntax "repeat " tacticSeq : tactic` (`Init/Tactics.lean`): its kind is `tacticRepeat_`.
        Some(("repeat", "tacticRepeat_"))
    } else if word(tokens, at, "repeat'") {
        Some(("repeat'", "repeat'"))
    } else if word(tokens, at, "next") {
        Some(("next", "tacticNext_=>_"))
    } else if word(tokens, at, "case") {
        Some(("case", "case"))
    } else if word(tokens, at, "case'") {
        Some(("case'", "case'"))
    } else {
        None
    }
}
/// `case`'s `sepBy1(caseArg, " | ")`: each `caseArg` is `binderIdent (ppSpace binderIdent)*`.
fn case_args(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    names: Range<usize>,
    binder: impl Fn(usize) -> Result<Syntax, NatDefinitionParseError>,
) -> Result<Vec<Syntax>, NatDefinitionParseError> {
    let mut args = Vec::new();
    let mut start = names.start;
    for bar in (names.start..names.end)
        .filter(|&at| symbol(tokens, at, "|"))
        .chain(std::iter::once(names.end))
    {
        if bar == start {
            return Err(refusal(view, tokens, bar));
        }
        args.push(Syntax::node(
            parser_kind(&["Tactic", "caseArg"]),
            vec![
                binder(start)?,
                null_node(
                    (start + 1..bar)
                        .map(&binder)
                        .collect::<Result<Vec<_>, _>>()?,
                ),
            ],
        ));
        if bar < names.end {
            args.push(leaves.leaf(bar)?);
        }
        start = bar + 1;
    }
    Ok(args)
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
    // `macro "next " args:(ppSpace binderIdent)* " => " tac:tacticSeq : tactic`
    // (`Init/Tactics.lean`): the names, then the body after `=>`. `case` is
    // `"case " sepBy1(caseArg, " | ") " => " tacticSeq`, each `caseArg` a tag and its names.
    let case = keyword == "case" || keyword == "case'";
    let (names, arrow) = if keyword == "next" || case {
        let mut at = start + 1;
        while at < limit
            && (matches!(&tokens[at].kind, TokenKind::Ident(_))
                || symbol(tokens, at, "_")
                || case && symbol(tokens, at, "|"))
        {
            at += 1;
        }
        if !symbol(tokens, at, "=>") || case && at == start + 1 {
            return Err(refusal(view, tokens, at));
        }
        (start + 1..at, Some(at))
    } else {
        (start + 1..start + 1, None)
    };
    let body = arrow.map_or(start + 1, |arrow| arrow + 1);
    // A body on its own line is a `tacticSeq` positioned at its first token (`sepByIndent`'s
    // `withPosition`): it runs while lines start at that column, even the enclosing sequence's
    // (`· case zero =>⏎    simp`), and ends at the first line left of it.
    // `·` alone takes `tacticSeqIndentGt`: a body at the enclosing column is not its own (the
    // pin reads `·⏎  rfl` as an empty focus and a sibling `rfl`).
    let own_line = body < limit && newline(view, tokens, body) && !matches!(keyword, "·" | ".");
    let floor = if own_line {
        column(view, tokens, body)
    } else {
        baseline + 1
    };
    let mut depth = 0;
    let mut end = limit;
    for at in body..limit {
        // An own-line body's first token is at `floor`; any other body's first token on a new
        // line at the enclosing column ends it empty (`·⏎  rfl`).
        if depth == 0
            && (at > body || !own_line)
            && newline(view, tokens, at)
            && column(view, tokens, at) < floor
        {
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
        names,
        arrow,
    })
}
fn plan_elimination(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
    baseline: usize,
) -> Result<Elimination, NatDefinitionParseError> {
    let mut target = start + 1;
    let matching = word(tokens, start, "match");
    // `fun_induction f x` and `fun_cases f x` (`Init/Tactics.lean`): one term, the
    // function's application; `generalizing` (for `fun_induction`) and alternatives as
    // `induction`'s.
    let functional = word(tokens, start, "fun_induction") || word(tokens, start, "fun_cases");
    let header_limit = plain_end(view, tokens, start, limit, baseline);
    let equation =
        if !matching && !functional && target + 1 < header_limit && symbol(tokens, target + 1, ":")
        {
            if !matches!(&tokens[target].kind, TokenKind::Ident(_)) && !symbol(tokens, target, "_")
            {
                return Err(refusal(view, tokens, target));
            }
            let name = target;
            target += 2;
            Some(name)
        } else {
            None
        };
    let mut at = target;
    let mut depth = 0;
    while at < header_limit {
        if depth == 0
            && (symbol(tokens, at, "with")
                || !matching
                    && at > target
                    && (word(tokens, at, "generalizing")
                        || !functional && word(tokens, at, "using")))
        {
            break;
        }
        delimiter_depth(&tokens[at], &mut depth);
        at += 1;
    }
    if target == at || depth != 0 {
        return Err(refusal(view, tokens, target));
    }
    let target = target..at;
    // `(" using " term)?`, before `generalizing` (`Init/Tactics.lean`).
    let using = if at < header_limit && word(tokens, at, "using") {
        let keyword = at;
        let mut depth = 0;
        at += 1;
        while at < header_limit
            && !(depth == 0 && (symbol(tokens, at, "with") || word(tokens, at, "generalizing")))
        {
            delimiter_depth(&tokens[at], &mut depth);
            at += 1;
        }
        if at == keyword + 1 || depth != 0 {
            return Err(refusal(view, tokens, keyword + 1));
        }
        Some(keyword..at)
    } else {
        None
    };
    let generalizing = if at < header_limit && word(tokens, at, "generalizing") {
        if !word(tokens, start, "induction") && !word(tokens, start, "fun_induction") {
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
        matching,
        target,
        equation,
        using,
        generalizing,
        with: None,
        pre_tactic: None,
        alternatives: Vec::new(),
        end: at,
    };
    if at == header_limit && !matching {
        return Ok(result);
    }
    if !symbol(tokens, at, "with") || at + 1 >= limit {
        return Err(refusal(view, tokens, at));
    }
    result.with = Some(at);
    // `inductionAlts := " with" (ppSpace colGt tactic)? withPosition((colGe inductionAlt)+)`.
    let first = if symbol(tokens, at + 1, "|") {
        at + 1
    } else {
        // The pre-tactic is one tactic (`ppSpace colGt tactic`): an alternative's `|` comes within
        // it or where it ends; with none, the alternatives are absent (`induction l with simp_all`).
        let tactic_end = plain_end(view, tokens, at + 1, limit, baseline);
        let mut depth = 0;
        let mut pipe = None;
        for index in at + 1..limit {
            if index >= tactic_end && !(index == tactic_end && symbol(tokens, index, "|")) {
                break;
            }
            if depth == 0 && symbol(tokens, index, "|") {
                pipe = Some(index);
                break;
            }
            if word(tokens, index, "first") {
                break;
            }
            delimiter_depth(&tokens[index], &mut depth);
        }
        let Some(pipe) = pipe else {
            if tactic_end == at + 1 {
                return Err(refusal(view, tokens, at + 1));
            }
            result.pre_tactic = Some(at + 1..tactic_end);
            result.end = tactic_end;
            return Ok(result);
        };
        result.pre_tactic = Some(at + 1..pipe);
        pipe
    };
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
                    || symbol(tokens, at, "with")
                    || symbol(tokens, at, "match")
                    || ((symbol(tokens, at, "fun") || symbol(tokens, at, "λ"))
                        && symbol(tokens, at + 1, "|")))
            {
                nested_pipes = true;
            }
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    let mut lhs = Vec::new();
    for (index, pipe) in pipes.iter().copied().enumerate() {
        let stop = pipes.get(index + 1).copied().unwrap_or(end);
        if matching {
            let mut depth = 0;
            let mut arrow = None;
            for at in pipe + 1..stop {
                if depth == 0 && (symbol(tokens, at, "=>") || symbol(tokens, at, "↦")) {
                    arrow = Some(at);
                    break;
                }
                delimiter_depth(&tokens[at], &mut depth);
            }
            let Some(arrow) = arrow.filter(|&arrow| arrow > pipe + 1 && arrow + 1 < stop) else {
                return Err(refusal(view, tokens, pipe + 1));
            };
            result.alternatives.push(Alternative {
                lhs: vec![(pipe, arrow)],
                arrow: Some(arrow),
                body: arrow + 1..stop,
            });
            continue;
        }
        // `inductionAltLHS := "| " (("@"? ident) <|> hole) (ident <|> hole)*`.
        if pipe + 1 >= stop
            || !(matches!(&tokens[pipe + 1].kind, TokenKind::Ident(_))
                || symbol(tokens, pipe + 1, "_"))
        {
            return Err(refusal(view, tokens, pipe + 1));
        }
        let mut arrow = pipe + 2;
        while arrow < stop
            && (matches!(&tokens[arrow].kind, TokenKind::Ident(_)) || symbol(tokens, arrow, "_"))
        {
            arrow += 1;
        }
        lhs.push((pipe, arrow));
        if arrow == stop {
            // Shares the next alternative's body or, last, has none.
            if index + 1 == pipes.len() {
                result.alternatives.push(Alternative {
                    lhs: std::mem::take(&mut lhs),
                    arrow: None,
                    body: stop..stop,
                });
            }
            continue;
        }
        if arrow + 1 >= stop || !(symbol(tokens, arrow, "=>") || symbol(tokens, arrow, "↦")) {
            return Err(refusal(view, tokens, arrow));
        }
        result.alternatives.push(Alternative {
            lhs: std::mem::take(&mut lhs),
            arrow: Some(arrow),
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
    let replace = word(tokens, start, "replace");
    let inline = word(tokens, start, "letI") || word(tokens, start, "haveI");
    let opaque = replace || word(tokens, start, "have") || word(tokens, start, "haveI");
    let preliminary_end = plain_end(view, tokens, start, limit, baseline);
    let mut cursor = start + 1;
    let name = if cursor < preliminary_end && matches!(&tokens[cursor].kind, TokenKind::Ident(_)) {
        let at = cursor;
        cursor += 1;
        Some(at)
    } else {
        None
    };
    // `letPatDecl := term optType " := " term`: a bracketed pattern in place of the name, an
    // anonymous constructor or a tuple. A parenthesis without a comma is the anonymous `have`'s
    // binder (`have (x : T) : P := v` is `letIdDecl`'s), which is not read here.
    let pattern = if name.is_none() && !replace && !inline {
        let open = cursor;
        let mut depth = 0;
        let mut close = None;
        let mut comma = false;
        for (at, token) in tokens.iter().enumerate().take(preliminary_end).skip(open) {
            delimiter_depth(token, &mut depth);
            if depth == 1 && symbol(tokens, at, ",") {
                comma = true;
            }
            if depth == 0 {
                close = Some(at);
                break;
            }
        }
        match close {
            Some(close)
                if symbol(tokens, open, "⟨") || (symbol(tokens, open, "(") && comma) =>
            {
                cursor = close + 1;
                Some(open..close + 1)
            }
            _ => None,
        }
    } else {
        None
    };
    // An anonymous `letI : C := v` names its instance as `have` does (`hygieneInfo`).
    if !opaque && !inline && name.is_none() && pattern.is_none() {
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
        pattern,
        annotation: colon.map(|at| (at, type_start..assign)),
        assign,
        value,
        by,
        end,
        opaque,
        replace,
        inline,
    })
}

fn binding_term(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    // A proof inside the value (`f (by omega)`) is the term parser's, bounded as every proof
    // in a tactic term is (`PROOF_NESTING`); a `calc` there is not read.
    if let Some(at) = range.clone().find(|&at| symbol(tokens, at, "calc")) {
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
    let keyword = match (plan.replace, plan.opaque, plan.inline) {
        (true, _, _) => "replace",
        (false, true, true) => "haveI",
        (false, true, false) => "have",
        (false, false, true) => "letI",
        (false, false, false) => "let",
    };
    let keyword_atom = atom(leaves, plan.start, keyword)?;
    // An anonymous `have` names its `letId` with the hygiene identifier (`hygieneInfo`).
    let name = match plan.name {
        Some(at) => leaves.leaf(at)?,
        None => crate::hygiene_info_following(&keyword_atom),
    };
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
    // `macro "have" c:letConfig d:letDecl : tactic` and `let` likewise (`Init/Tactics.lean`):
    // the term forms' `letConfig` and `letDecl`.
    let declaration = match plan.pattern.clone() {
        Some(range) => Syntax::node(
            parser_kind(&["Term", "letPatDecl"]),
            vec![
                binding_term(leaves, view, tokens, range)?,
                null_node(Vec::new()),
                annotation,
                leaves.leaf(plan.assign)?,
                value,
            ],
        ),
        None => Syntax::node(
            parser_kind(&["Term", "letIdDecl"]),
            vec![
                Syntax::node(parser_kind(&["Term", "letId"]), vec![name]),
                null_node(Vec::new()),
                annotation,
                leaves.leaf(plan.assign)?,
                value,
            ],
        ),
    };
    let declaration = Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]);
    // `syntax "replace" haveDecl : tactic`: no configuration slot.
    if plan.replace {
        return Ok(Syntax::node(
            parser_kind(&["Tactic", "replace"]),
            vec![keyword_atom, declaration],
        ));
    }
    Ok(Syntax::node(
        parser_kind(&[
            "Tactic",
            match keyword {
                "have" => "tacticHave__",
                "haveI" => "tacticHaveI__",
                "letI" => "tacticLetI__",
                _ => "tacticLet__",
            },
        ]),
        vec![
            keyword_atom,
            Syntax::node(
                parser_kind(&["Term", "letConfig"]),
                vec![null_node(Vec::new())],
            ),
            declaration,
        ],
    ))
}

/// A scoped control tactic (`·`, `focus`, `next`, `case`, …) around its body. Out of line, as
/// the task loop's frame is live under every nested parse on small host stacks
/// (`nested_expression_splits_stay_on_the_heap_on_a_small_stack`).
#[inline(never)]
fn finish_control(
    leaves: &Leaves,
    tokens: &[LexedToken],
    view: &SourceView,
    plan: Control,
    body: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let keyword = atom(leaves, plan.start, plan.keyword)?;
    Ok(if plan.kind == "cdot" {
        // `syntax cdotTk := unicode("· ", ". ")` and `syntax (name := cdot) cdotTk
        // tacticSeqIndentGt : tactic`, in namespace `Lean` (`Init/NotationExtra.lean`).
        Syntax::node(
            Name::from_components(["Lean", "cdot"]),
            vec![
                Syntax::node(Name::from_components(["Lean", "cdotTk"]), vec![keyword]),
                body,
            ],
        )
    } else if let Some(arrow) = plan.arrow {
        // `next`: each name a `Lean.binderIdent`, then `=>` and the body.
        let binder = |at: usize| {
            let name = leaves.leaf(at)?;
            let name = if symbol(tokens, at, "_") {
                Syntax::node(parser_kind(&["Term", "hole"]), vec![name])
            } else {
                name
            };
            Ok::<_, NatDefinitionParseError>(Syntax::node(
                Name::from_components(["Lean", "binderIdent"]),
                vec![name],
            ))
        };
        let names = if plan.keyword != "next" {
            case_args(leaves, view, tokens, plan.names.clone(), binder)?
        } else {
            plan.names
                .clone()
                .map(binder)
                .collect::<Result<Vec<_>, NatDefinitionParseError>>()?
        };
        Syntax::node(
            parser_kind(&["Tactic", plan.kind]),
            vec![keyword, null_node(names), leaves.leaf(arrow)?, body],
        )
    } else {
        Syntax::node(parser_kind(&["Tactic", plan.kind]), vec![keyword, body])
    })
}

/// The tactic `if c then … else …` from `start`: the `then` at depth 0, the `else` that is not
/// a nested `if`'s, and the end of the `else` branch where a line returns to `baseline`.
fn plan_if(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
    baseline: usize,
) -> Result<Conditional, NatDefinitionParseError> {
    let binder = (start + 2 < limit
        && (matches!(&tokens[start + 1].kind, TokenKind::Ident(_))
            || symbol(tokens, start + 1, "_"))
        && symbol(tokens, start + 2, ":"))
    .then_some((start + 1, start + 2));
    let condition_start = binder.map_or(start + 1, |(_, colon)| colon + 1);
    let mut depth = 0;
    let mut then_at = None;
    let mut else_at = None;
    let mut nested = 0usize;
    for at in condition_start..limit {
        if depth == 0 {
            if then_at.is_none() && symbol(tokens, at, "then") {
                then_at = Some(at);
            } else if then_at.is_some() && symbol(tokens, at, "if") {
                nested += 1;
            } else if then_at.is_some() && symbol(tokens, at, "else") {
                if nested == 0 {
                    else_at = Some(at);
                    break;
                }
                nested -= 1;
            }
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    let (Some(then_at), Some(else_at)) = (then_at, else_at) else {
        return Err(refusal(view, tokens, start));
    };
    // The `else` branch is a tactic sequence: it takes the `;`s after it.
    let end = block_end(view, tokens, else_at, limit, baseline);
    if then_at == condition_start || else_at == then_at + 1 || end == else_at + 1 {
        return Err(refusal(view, tokens, then_at));
    }
    Ok(Conditional {
        start,
        binder,
        condition: condition_start..then_at,
        then_at,
        else_at,
        yes: then_at + 1..else_at,
        no: else_at + 1..end,
        end,
    })
}

/// `tacIfThenElse := "if " term " then " tacticSeq " else " tacticSeq` and `tacDepIfThenElse`
/// with `binderIdent " : "` after `if` (`Init/Tactics.lean`).
#[inline(never)]
fn finish_if(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: Conditional,
    yes: Syntax,
    no: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let condition = binding_term(leaves, view, tokens, plan.condition)?;
    let mut parts = vec![leaves.leaf(plan.start)?];
    let kind = match plan.binder {
        Some((name, colon)) => {
            let leaf = leaves.leaf(name)?;
            let name = if symbol(tokens, name, "_") {
                Syntax::node(parser_kind(&["Term", "hole"]), vec![leaf])
            } else {
                leaf
            };
            parts.push(Syntax::node(
                Name::from_components(["Lean", "binderIdent"]),
                vec![name],
            ));
            parts.push(leaves.leaf(colon)?);
            "tacDepIfThenElse"
        }
        None => "tacIfThenElse",
    };
    parts.extend([
        condition,
        leaves.leaf(plan.then_at)?,
        yes,
        leaves.leaf(plan.else_at)?,
        no,
    ]);
    Ok(Syntax::node(parser_kind(&["Tactic", kind]), parts))
}

/// `items` split at its top-level commas: each item's range, and the comma after it.
fn comma_items(tokens: &[LexedToken], items: Range<usize>) -> Vec<(Range<usize>, Option<usize>)> {
    let mut parts = Vec::new();
    let mut start = items.start;
    let mut depth = 0;
    for at in items.clone() {
        if depth == 0 && symbol(tokens, at, ",") {
            parts.push((start..at, Some(at)));
            start = at + 1;
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    parts.push((start..items.end, None));
    parts
}

/// `("generalizing" (ppSpace colGt term:max)+)?`: the keyword, then the names.
fn generalized(
    leaves: &Leaves,
    generalizing: Option<Range<usize>>,
) -> Result<Syntax, NatDefinitionParseError> {
    Ok(match generalizing {
        Some(range) => null_node(vec![
            atom(leaves, range.start, "generalizing")?,
            null_node(
                (range.start + 1..range.end)
                    .map(|at| leaves.leaf(at))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        ]),
        None => null_node(Vec::new()),
    })
}

/// The tactic `match` (`Lean/Parser/Tactic.lean`): `"match" generalizingParam? motive?
/// sepBy1(matchDiscr, ", ") " with " matchAlts(tacticSeq)`, without the two optional slots. A
/// discriminant may be named (`h : e`); each row's patterns are terms. Out of line: the patterns
/// are bounded term parses.
#[inline(never)]
fn finish_match(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: Elimination,
    children: Vec<Syntax>,
) -> Result<Syntax, NatDefinitionParseError> {
    let with = plan
        .with
        .ok_or_else(|| refusal(view, tokens, plan.target.end))?;
    let mut discriminants = Vec::new();
    for (range, comma) in comma_items(tokens, plan.target.clone()) {
        if range.is_empty() {
            return Err(refusal(view, tokens, range.start));
        }
        let named = range.len() > 2
            && matches!(&tokens[range.start].kind, TokenKind::Ident(_))
            && symbol(tokens, range.start + 1, ":");
        let (name, term) = if named {
            (
                null_node(vec![
                    leaves.leaf(range.start)?,
                    leaves.leaf(range.start + 1)?,
                ]),
                range.start + 2..range.end,
            )
        } else {
            (null_node(Vec::new()), range)
        };
        discriminants.push(Syntax::node(
            parser_kind(&["Term", "matchDiscr"]),
            vec![name, binding_term(leaves, view, tokens, term)?],
        ));
        if let Some(comma) = comma {
            discriminants.push(leaves.leaf(comma)?);
        }
    }
    let mut alternatives = Vec::new();
    for (alt, body) in plan.alternatives.into_iter().zip(children) {
        let (pipe, arrow) = alt.lhs[0];
        let mut patterns = Vec::new();
        for (range, comma) in comma_items(tokens, pipe + 1..arrow) {
            if range.is_empty() {
                return Err(refusal(view, tokens, range.start));
            }
            patterns.push(binding_term(leaves, view, tokens, range)?);
            if let Some(comma) = comma {
                patterns.push(leaves.leaf(comma)?);
            }
        }
        alternatives.push(Syntax::node(
            parser_kind(&["Term", "matchAlt"]),
            vec![
                leaves.leaf(pipe)?,
                null_node(vec![null_node(patterns)]),
                leaves.leaf(arrow)?,
                body,
            ],
        ));
    }
    Ok(Syntax::node(
        parser_kind(&["Tactic", "match"]),
        vec![
            atom(leaves, plan.start, "match")?,
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(discriminants),
            atom(leaves, with, "with")?,
            Syntax::node(
                parser_kind(&["Term", "matchAlts"]),
                vec![null_node(alternatives)],
            ),
        ],
    ))
}

/// Sequence-level combinators cannot capture operators inside term arguments,
/// local proof values, or constructor alternatives. Those own their subranges.
/// One `cases`/`induction` tactic from its plan and its alternatives' bodies. Out of line: the
/// task loop's frame stays live while nested terms are parsed on small host stacks
/// (`deeply_grouped_generalization_uses_a_small_stack`), and every arm of it shares that frame.
#[inline(never)]
fn finish_elimination(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: Elimination,
    children: Vec<Syntax>,
) -> Result<Syntax, NatDefinitionParseError> {
    if plan.matching {
        return finish_match(leaves, view, tokens, plan, children);
    }
    // The pin's trees (`Init/Tactics.lean`): `cases`/`induction` take a list of
    // `elimTarget`s, then `using`, (for `induction`) `generalizing`, and the
    // `inductionAlts`; an alternative is `inductionAltLHS+` and its `=> body`.
    let binder = |at: usize| -> Result<Syntax, NatDefinitionParseError> {
        let leaf = leaves.leaf(at)?;
        Ok(if symbol(tokens, at, "_") {
            Syntax::node(parser_kind(&["Term", "hole"]), vec![leaf])
        } else {
            leaf
        })
    };
    let mut alts = Vec::new();
    let mut children = children.into_iter();
    // `with tac`: one tactic, read as a sequence (it may be `try …`) of exactly one.
    let pre_tactic = match plan.pre_tactic.clone() {
        Some(range) => {
            let sequence = children.next().expect("the with tactic");
            let single = match &sequence {
                Syntax::Node { args, .. } => match args.first() {
                    Some(Syntax::Node { args: indented, .. }) => match indented.first() {
                        Some(Syntax::Node { args: items, .. }) if items.len() == 1 => {
                            Some(items[0].clone())
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            Some(single.ok_or_else(|| refusal(view, tokens, range.start))?)
        }
        None => None,
    };
    for alt in plan.alternatives {
        let mut lhs = Vec::new();
        for (pipe, names_end) in alt.lhs {
            let names = (pipe + 2..names_end)
                .map(binder)
                .collect::<Result<Vec<_>, _>>()?;
            let name = if symbol(tokens, pipe + 1, "_") {
                Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(pipe + 1)?])
            } else {
                Syntax::node(
                    Name::from_components(["group"]),
                    vec![null_node(Vec::new()), leaves.leaf(pipe + 1)?],
                )
            };
            lhs.push(Syntax::node(
                parser_kind(&["Tactic", "inductionAltLHS"]),
                vec![leaves.leaf(pipe)?, name, null_node(names)],
            ));
        }
        let rhs = match alt.arrow {
            Some(arrow) => vec![
                leaves.leaf(arrow)?,
                children.next().expect("alternative body"),
            ],
            None => Vec::new(),
        };
        alts.push(Syntax::node(
            parser_kind(&["Tactic", "inductionAlt"]),
            vec![null_node(lhs), null_node(rhs)],
        ));
    }
    let alternatives = match plan.with {
        Some(at) => null_node(vec![Syntax::node(
            parser_kind(&["Tactic", "inductionAlts"]),
            vec![
                leaves.leaf(at)?,
                null_node(pre_tactic.into_iter().collect()),
                null_node(alts),
            ],
        )]),
        None => null_node(Vec::new()),
    };
    if word(tokens, plan.start, "fun_induction") || word(tokens, plan.start, "fun_cases") {
        let induction = word(tokens, plan.start, "fun_induction");
        let (keyword, kind) = if induction {
            ("fun_induction", "funInduction")
        } else {
            ("fun_cases", "funCases")
        };
        let mut parts = vec![
            atom(leaves, plan.start, keyword)?,
            binding_term(leaves, view, tokens, plan.target)?,
        ];
        if induction {
            parts.push(generalized(leaves, plan.generalizing)?);
        } else if plan.generalizing.is_some() {
            return Err(refusal(view, tokens, plan.start));
        }
        parts.push(alternatives);
        return Ok(Syntax::node(parser_kind(&["Tactic", kind]), parts));
    }
    let keyword = if word(tokens, plan.start, "cases") {
        "cases"
    } else {
        "induction"
    };
    // `sepBy1(elimTarget, ", ")`, `elimTarget := atomic(binderIdent " : ")? term`: the first
    // target's name was read with the plan.
    let mut targets = Vec::new();
    for (index, (range, comma)) in comma_items(tokens, plan.target.clone())
        .into_iter()
        .enumerate()
    {
        if range.is_empty() {
            return Err(refusal(view, tokens, range.start));
        }
        let (equation, term) = if index == 0 {
            (plan.equation, range)
        } else if range.len() > 2
            && (matches!(&tokens[range.start].kind, TokenKind::Ident(_))
                || symbol(tokens, range.start, "_"))
            && symbol(tokens, range.start + 1, ":")
        {
            (Some(range.start), range.start + 2..range.end)
        } else {
            (None, range)
        };
        targets.push(Syntax::node(
            parser_kind(&["Tactic", "elimTarget"]),
            vec![
                match equation {
                    Some(at) => null_node(vec![
                        Syntax::node(
                            Name::from_components(["Lean", "binderIdent"]),
                            vec![binder(at)?],
                        ),
                        leaves.leaf(at + 1)?,
                    ]),
                    None => null_node(Vec::new()),
                },
                binding_term(leaves, view, tokens, term)?,
            ],
        ));
        if let Some(comma) = comma {
            targets.push(leaves.leaf(comma)?);
        }
    }
    let using = match plan.using {
        Some(range) => null_node(vec![
            atom(leaves, range.start, "using")?,
            binding_term(leaves, view, tokens, range.start + 1..range.end)?,
        ]),
        None => null_node(Vec::new()),
    };
    let mut parts = vec![
        atom(leaves, plan.start, keyword)?,
        null_node(targets),
        using,
    ];
    if keyword == "induction" {
        parts.push(generalized(leaves, plan.generalizing)?);
    } else if plan.generalizing.is_some() {
        return Err(refusal(view, tokens, plan.start));
    }
    parts.push(alternatives);
    Ok(Syntax::node(parser_kind(&["Tactic", keyword]), parts))
}

/// A sequence of exactly one tactic as that tactic (`<;>`'s operands are `tactic`s); any other
/// syntax is returned unchanged.
fn single_tactic(syntax: Syntax) -> Syntax {
    let unwrap = |syntax: &Syntax, kind: &str| match syntax {
        Syntax::Node {
            kind: found, args, ..
        } if found == &parser_kind(&["Tactic", kind]) && args.len() == 1 => Some(args[0].clone()),
        _ => None,
    };
    let Some(indented) = unwrap(&syntax, "tacticSeq") else {
        return syntax;
    };
    let Some(items) = unwrap(&indented, "tacticSeq1Indented") else {
        return syntax;
    };
    match &items {
        Syntax::Node { args, .. } if args.len() == 1 => args[0].clone(),
        _ => syntax,
    }
}

/// The last top-level `<;>`: `macro:1 x:tactic " <;> " y:tactic:2` (`Init/Tactics.lean`) takes
/// its right operand at precedence 2, so `a <;> b <;> c` nests to the left. A right operand that
/// takes a `tacticSeq` (`try`, `first`, `all_goals`, …) takes everything after it, `;`s and
/// `<;>`s included, so the first `<;>` before one is the chain's.
fn chain_at(tokens: &[LexedToken], range: Range<usize>) -> Option<usize> {
    let mut depth = 0;
    let mut last = None;
    // `rcases … with pat` has a pattern after `with`, not alternatives holding tactics.
    let pattern_with = word(tokens, range.start, "rcases");
    // `conv … => convSeq`: a `<;>` after the `=>` is the conv sequence's (`conv_<;>_`).
    let conv = word(tokens, range.start, "conv");
    for at in range {
        if depth == 0 && conv && symbol(tokens, at, "=>") {
            return last;
        }
        if depth == 0 {
            if symbol(tokens, at, "<;>") {
                if sequence_operand(tokens, at + 1) {
                    return Some(at);
                }
                last = Some(at);
            }
            // A `by` owns the `<;>`s after it (`suffices h : t by … split <;> simp`).
            if symbol(tokens, at, ":=")
                || symbol(tokens, at, "by")
                || (symbol(tokens, at, "with") && !pattern_with)
            {
                return last;
            }
        }
        delimiter_depth(&tokens[at], &mut depth);
    }
    last
}

/// Whether the tactic at `at` takes a `tacticSeq` (or `conv`'s `convSeq`) after its head.
fn sequence_operand(tokens: &[LexedToken], at: usize) -> bool {
    word(tokens, at, "first") || word(tokens, at, "conv") || control_word(tokens, at).is_some()
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
            let operand = separator + 1;
            let end = if word(tokens, operand, "first") {
                plan_choice(view, tokens, operand, range.end, baseline)?.end
            } else if let Some((keyword, kind)) = control_word(tokens, operand) {
                plan_control(view, tokens, operand, range.end, baseline, keyword, kind)?.end
            } else if word(tokens, operand, "conv") {
                block_end(view, tokens, operand, range.end, baseline)
            } else {
                plain_end(view, tokens, cursor, range.end, baseline)
            };
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
        } else if symbol(tokens, cursor, "calc")
            || word(tokens, cursor, "exact") && symbol(tokens, cursor + 1, "calc")
        {
            let exact = word(tokens, cursor, "exact").then_some(cursor);
            let plan = calc::plan(
                view,
                tokens,
                cursor + usize::from(exact.is_some()),
                range.end,
            )?;
            let end = plan.end;
            (Plan::Calc(plan, exact), end)
        } else if word(tokens, cursor, "have")
            || word(tokens, cursor, "replace")
            || word(tokens, cursor, "letI")
            || word(tokens, cursor, "haveI")
            || symbol(tokens, cursor, "let")
        {
            let plan = plan_binding(view, tokens, cursor, range.end, baseline)?;
            let end = plan.end;
            (Plan::Bind(plan), end)
        } else if symbol(tokens, cursor, "if") {
            let plan = plan_if(view, tokens, cursor, range.end, baseline)?;
            let end = plan.end;
            (Plan::If(plan), end)
        } else if word(tokens, cursor, "cases")
            || word(tokens, cursor, "induction")
            || word(tokens, cursor, "match")
            || word(tokens, cursor, "fun_induction")
            || word(tokens, cursor, "fun_cases")
        {
            let plan = plan_elimination(view, tokens, cursor, range.end, baseline)?;
            let end = plan.end;
            (Plan::Eliminate(plan), end)
        } else if symbol(tokens, cursor, "open") {
            // `"open " openDecl withOpenDecl(" in " tacticSeq)` (`Lean/Parser/Command.lean`): the
            // declaration up to its `in`, then a sequence that runs as `conv`'s, to the line back
            // at `baseline`.
            let header = block_end(view, tokens, cursor, range.end, baseline);
            let Some(in_at) = (cursor + 1..header).find(|&at| symbol(tokens, at, "in")) else {
                return Err(refusal(view, tokens, cursor));
            };
            // A sequence on its own line is positioned at its first token, as a `case` body.
            let body = in_at + 1;
            let end = if body < range.end && newline(view, tokens, body) {
                let floor = column(view, tokens, body);
                let mut depth = 0;
                let mut end = range.end;
                for at in body..range.end {
                    if depth == 0
                        && at > body
                        && newline(view, tokens, at)
                        && column(view, tokens, at) < floor
                    {
                        end = at;
                        break;
                    }
                    delimiter_depth(&tokens[at], &mut depth);
                }
                end
            } else {
                header
            };
            if body >= end {
                return Err(refusal(view, tokens, in_at));
            }
            (Plan::Open(cursor, in_at, end), end)
        } else if word(tokens, cursor, "conv") {
            // `conv … => convSeq` takes the `;`s after it: it ends where a line returns to
            // `baseline`.
            let end = block_end(view, tokens, cursor, range.end, baseline);
            (Plan::Plain(cursor..end), end)
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
    run(leaves, view, tokens, Task::Sequence(range, None))
}

pub(crate) fn calculation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    limit: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let plan = calc::plan(view, tokens, start, limit)?;
    let end = plan.end;
    Ok((run(leaves, view, tokens, Task::Calc(plan))?, end))
}

fn run(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    root: Task,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut tasks = vec![root];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            // A plain tactic parses its terms from this loop's own small frame; every other task
            // is one `step`, whose temporaries are not live while a tactic's terms are parsed.
            Task::Plain(range) => values.push(tactic(leaves, view, tokens, range)?),
            task => step(leaves, view, tokens, task, &mut tasks, &mut values)?,
        }
    }
    Ok(values.pop().expect("root tactic sequence"))
}

/// One task of [`run`]'s work loop: it pushes the tasks it needs or the value it makes.
#[inline(never)]
fn step(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    task: Task,
    tasks: &mut Vec<Task>,
    values: &mut Vec<Syntax>,
) -> Result<(), NatDefinitionParseError> {
    match task {
        Task::Sequence(range, baseline) => {
            // `sepByIndent tactic "; " (allowTrailingSep := true)`: a termination hint on a later
            // line at the items' column passes the separator's `checkColEq`, pushing an empty
            // separator that no item follows.
            let trailing = range.end < tokens.len()
                && range.start < range.end
                && (symbol(tokens, range.end, "termination_by")
                    || symbol(tokens, range.end, "decreasing_by"))
                && view.normalized().line_of(tokens[range.end].extent.start())
                    > view.normalized().line_of(tokens[range.end - 1].extent.end())
                && column(view, tokens, range.end) == column(view, tokens, range.start);
            let (plans, separators) = split(view, tokens, range, baseline)?;
            tasks.push(Task::FinishSequence(separators, trailing));
            tasks.extend(plans.into_iter().rev().map(|plan| match plan {
                Plan::If(plan) => Task::If(plan),
                Plan::Calc(plan, exact) => Task::StartCalcTactic(plan, exact),
                Plan::Choice(plan) => Task::Choice(plan),
                Plan::Chain(plan) => Task::Chain(plan),
                Plan::Group(range) => Task::Group(range),
                Plan::Plain(range) => Task::Plain(range),
                Plan::Control(plan) => Task::Control(plan),
                Plan::Bind(plan) => Task::Bind(plan),
                Plan::Eliminate(plan) => Task::Eliminate(plan),
                Plan::Open(open, in_at, end) => Task::Open(open, in_at, end),
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
        Task::Chain(plan) => {
            tasks.push(Task::FinishChain(plan.separator));
            tasks.push(Task::Sequence(plan.right, None));
            tasks.push(Task::Sequence(plan.left, None));
        }
        Task::Open(open, in_at, end) => {
            tasks.push(Task::FinishOpen(open, in_at));
            tasks.push(Task::Sequence(in_at + 1..end, None));
        }
        Task::Group(range) => {
            tasks.push(Task::FinishGroup(range.start, range.end - 1));
            tasks.push(Task::Sequence(range.start + 1..range.end - 1, None));
        }
        Task::Control(plan) => {
            let body = plan.body.clone();
            let baseline = plan.baseline;
            tasks.push(Task::FinishControl(plan));
            tasks.push(Task::Sequence(body, Some(baseline)));
        }
        Task::FinishControl(plan) => {
            let body = values.pop().expect("scoped tactic sequence");
            values.push(finish_control(leaves, tokens, view, plan, body)?);
        }
        Task::Plain(range) => values.push(tactic(leaves, view, tokens, range)?),
        Task::Bind(plan) => {
            if plan.by.is_some() {
                let range = plan.value.clone();
                tasks.push(Task::FinishBinding(plan));
                tasks.push(Task::Sequence(range, None));
            } else if symbol(tokens, plan.value.start, "calc") {
                let range = plan.value.clone();
                tasks.push(Task::FinishBinding(plan));
                tasks.push(Task::CalcProof(range));
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
                .filter(|alt| alt.arrow.is_some())
                .map(|alt| alt.body.clone())
                .collect();
            let pre_tactic = plan.pre_tactic.clone();
            tasks.push(Task::FinishElimination(plan));
            tasks.extend(
                bodies
                    .into_iter()
                    .rev()
                    .map(|range| Task::Sequence(range, None)),
            );
            // `with tac`'s tactic is read first, so its value precedes the bodies'.
            if let Some(range) = pre_tactic {
                tasks.push(Task::Sequence(range, None));
            }
        }
        Task::If(plan) => {
            let (yes, no) = (plan.yes.clone(), plan.no.clone());
            tasks.push(Task::FinishIf(plan));
            tasks.push(Task::Sequence(no, None));
            tasks.push(Task::Sequence(yes, None));
        }
        Task::FinishIf(plan) => {
            let no = values.pop().expect("else branch sequence");
            let yes = values.pop().expect("then branch sequence");
            values.push(finish_if(leaves, view, tokens, plan, yes, no)?);
        }
        Task::FinishElimination(plan) => {
            let bodies = plan
                .alternatives
                .iter()
                .filter(|alt| alt.arrow.is_some())
                .count()
                + usize::from(plan.pre_tactic.is_some());
            let children = values.split_off(values.len() - bodies);
            values.push(finish_elimination(leaves, view, tokens, plan, children)?);
        }
        task @ (Task::FinishChoice(_)
        | Task::FinishChain(_)
        | Task::FinishOpen(..)
        | Task::FinishGroup(..)
        | Task::CalcTactic(_)
        | Task::By(_)
        | Task::FinishSequence(..)) => finish_syntax(leaves, view, tokens, task, values)?,
        task @ (Task::StartCalcTactic(..)
        | Task::Calc(_)
        | Task::CalcProof(_)
        | Task::FinishCalc(_)) => calc_step(leaves, view, tokens, task, tasks, values)?,
    }
    Ok(())
}

/// [`step`]'s tasks that build a node from finished values, in a frame of their own: their
/// temporaries are not live while another task parses a tactic's terms.
#[inline(never)]
fn finish_syntax(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    task: Task,
    values: &mut Vec<Syntax>,
) -> Result<(), NatDefinitionParseError> {
    match task {
        Task::FinishChoice(plan) => {
            // `"first " withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+)`: each
            // alternative is a `group` of its `|` and its sequence.
            let bodies = values.split_off(values.len() - plan.branches.len());
            let mut branches = Vec::with_capacity(bodies.len());
            for ((pipe, _), body) in plan.branches.into_iter().zip(bodies) {
                branches.push(Syntax::node(
                    Name::str(Name::anonymous(), "group"),
                    vec![leaves.leaf(pipe)?, body],
                ));
            }
            values.push(Syntax::node(
                parser_kind(&["Tactic", "first"]),
                vec![atom(leaves, plan.start, "first")?, null_node(branches)],
            ));
        }
        Task::FinishChain(separator) => {
            // Each operand is one `tactic` at the pin, not a sequence.
            let right = single_tactic(values.pop().expect("sequenced tactic right operand"));
            let left = single_tactic(values.pop().expect("sequenced tactic left operand"));
            // `macro:1 x:tactic tk:" <;> " y:tactic:2 : tactic` (`Init/Tactics.lean`).
            values.push(Syntax::node(
                parser_kind(&["Tactic", "tactic_<;>_"]),
                vec![left, leaves.leaf(separator)?, right],
            ));
        }
        Task::FinishOpen(open, in_at) => {
            let body = values.pop().expect("the sequence after open … in");
            let declaration =
                crate::command_scope::trees::open_declaration(leaves, tokens, open + 1, in_at)?
                    .ok_or_else(|| refusal(view, tokens, open + 1))?;
            values.push(Syntax::node(
                parser_kind(&["Tactic", "open"]),
                vec![
                    atom(leaves, open, "open")?,
                    declaration,
                    atom(leaves, in_at, "in")?,
                    body,
                ],
            ));
        }
        Task::FinishGroup(open, close) => {
            let body = values.pop().expect("parenthesized tactic sequence");
            values.push(Syntax::node(
                parser_kind(&["Tactic", "paren"]),
                vec![leaves.leaf(open)?, body, leaves.leaf(close)?],
            ));
        }
        Task::CalcTactic(exact) => {
            let term = values.pop().expect("calculation term");
            values.push(if let Some(at) = exact {
                Syntax::node(
                    parser_kind(&["Tactic", "exact"]),
                    vec![atom(leaves, at, "exact")?, term],
                )
            } else {
                // `Lean.calcTactic`: the term's keyword and steps, as a tactic.
                match &term {
                    Syntax::Node { args, .. } => Syntax::node(
                        Name::from_components(["Lean", "calcTactic"]),
                        args.clone(),
                    ),
                    _ => term,
                }
            });
        }
        Task::By(at) => {
            let body = values.pop().expect("calculation step proof");
            values.push(Syntax::node(
                parser_kind(&["Term", "byTactic"]),
                vec![leaves.leaf(at)?, body],
            ));
        }
        Task::FinishSequence(separators, trailing) => {
            let count = separators.len();
            let children = values.split_off(values.len() - count);
            let mut rows = Vec::new();
            for (index, (child, separator)) in children.into_iter().zip(separators).enumerate()
            {
                rows.push(child);
                if let Some(separator) = separator {
                    rows.push(leaves.leaf(separator)?);
                } else if index + 1 < count || trailing {
                    // A line break: `sepByIndent`'s `checkColEq >> pushNone` (`Parser/Extra.lean`).
                    rows.push(null_node(Vec::new()));
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
        // `step` routes only the tasks above here.
        _ => return Err(refusal(view, tokens, tokens.len().saturating_sub(1))),
    }
    Ok(())
}

/// [`step`]'s calculation tasks, in a frame of their own.
#[inline(never)]
fn calc_step(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    task: Task,
    tasks: &mut Vec<Task>,
    values: &mut Vec<Syntax>,
) -> Result<(), NatDefinitionParseError> {
    match task {
        Task::StartCalcTactic(plan, exact) => {
            tasks.push(Task::CalcTactic(exact));
            tasks.push(Task::Calc(plan));
        }
        Task::Calc(plan) => {
            let proofs: Vec<_> = plan.steps.iter().map(|step| step.proof.clone()).collect();
            tasks.push(Task::FinishCalc(plan));
            tasks.extend(proofs.into_iter().rev().map(Task::CalcProof));
        }
        Task::CalcProof(range) => {
            if symbol(tokens, range.start, "by") {
                tasks.push(Task::By(range.start));
                tasks.push(Task::Sequence(range.start + 1..range.end, None));
            } else if symbol(tokens, range.start, "calc") {
                let plan = calc::plan(view, tokens, range.start, range.end)?;
                if plan.end != range.end {
                    return Err(refusal(view, tokens, plan.end));
                }
                tasks.push(Task::Calc(plan));
            } else {
                values.push(binding_term(leaves, view, tokens, range)?);
            }
        }
        Task::FinishCalc(plan) => {
            // `"calc" calcSteps`, `calcSteps := calcFirstStep calcStep*`,
            // `calcFirstStep := term (" := " term)?`, `calcStep := term " := " term`
            // (`Lean/Parser/Term.lean`, kinds in namespace `Lean`).
            let lean = |kind: &str| Name::from_components(["Lean", kind]);
            let proofs = values.split_off(values.len() - plan.steps.len());
            let mut first = None;
            let mut steps = Vec::new();
            for (step, proof) in plan.steps.into_iter().zip(proofs) {
                let relation = binding_term(leaves, view, tokens, step.relation)?;
                let assign = leaves.leaf(step.assign)?;
                if first.is_none() {
                    first = Some(Syntax::node(
                        lean("calcFirstStep"),
                        vec![relation, null_node(vec![assign, proof])],
                    ));
                } else {
                    steps.push(Syntax::node(
                        lean("calcStep"),
                        vec![relation, assign, proof],
                    ));
                }
            }
            let first = first.ok_or_else(|| refusal(view, tokens, plan.start))?;
            values.push(Syntax::node(
                lean("calc"),
                vec![
                    leaves.leaf(plan.start)?,
                    Syntax::node(lean("calcSteps"), vec![first, null_node(steps)]),
                ],
            ));
        }
        // `step` routes only the tasks above here.
        _ => return Err(refusal(view, tokens, tokens.len().saturating_sub(1))),
    }
    Ok(())
}


#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn expression_discriminants_and_equations_preserve_original_tokens() {
        for source in [
            "theorem t : 0 = 0 := by cases (f x) with | false => rfl | true => rfl",
            "-- header\r\ntheorem t : 0 = 0 := by\r\n  cases h : f /- input -/ x with\r\n  | false => rfl\r\n  | true => rfl\r\n",
            "theorem t : 0 = 0 := by induction h : (f x) generalizing y with | zero => rfl | succ n ih => exact ih y",
            "theorem t : 0 = 0 := by cases _ : (f x)",
            "theorem t : 0 = 0 := by cases «equation name» : (f «argument name») with | false => rfl | true => rfl",
            "theorem t : 0 = 0 := by cases (match b with | .false => false | .true => true) with | false => rfl | true => rfl",
            // `generalizing` is a keyword at the pin; a local of that name is escaped.
            "theorem t («generalizing» : Bool) : 0 = 0 := by cases «generalizing» with | false => rfl | true => rfl",
            "theorem t : 0 = 0 := by cases h : f n with\n  | false =>\n    cases h : g n with | false => rfl | true => rfl\n  | true => rfl",
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
    fn malformed_expression_targets_are_refused_before_elaboration() {
        for target in [
            "",
            "h :",
            "2 : f x",
            "h : (f x",
            "h : (calc 0 = 0 := by rfl)",
        ] {
            let source = format!("theorem t : 0 = 0 := by cases {target}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        // A proof nested in the target is a term the pin parses (it fails in elaboration: the
        // major premise is not inductive), bounded as any proof in a tactic term.
        assert!(
            parse_definition(b"theorem t : 0 = 0 := by cases (by cases b)").is_ok(),
            "a nested proof target"
        );
        // `(" using " ident)?` is the pin's eliminator slot: the target is `f x`, and the
        // elaborator, not the parser, refuses an eliminator it does not have.
        assert!(parse_definition(b"theorem t : 0 = 0 := by cases f x using fake").is_ok());
        // `elimTarget,+`: two targets are the pin's syntax; the elaborator reads one and refuses
        // the rest (`several_elimination_targets_are_refused_not_misread`, `crates/fln`).
        assert!(parse_definition(b"theorem t : 0 = 0 := by cases f x, g x").is_ok());
    }

    #[test]
    fn nested_expression_splits_stay_on_the_heap_on_a_small_stack() {
        std::thread::Builder::new()
            .name("nested_expression_splits_stay_on_the_heap_on_a_small_stack".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                let depth = 300;
                let mut source =
                    String::from("theorem t (f : Nat -> Bool) (n : Nat) : f n = f n := by\n");
                for level in 0..depth {
                    let indent = "  ".repeat(level + 1);
                    source.push_str(&format!(
                        "{indent}cases h : (f n) with\n{indent}| false =>\n"
                    ));
                }
                source.push_str(&format!("{}rfl\n", "  ".repeat(depth + 1)));
                for level in (0..depth).rev() {
                    source.push_str(&format!("{}| true => rfl\n", "  ".repeat(level + 1)));
                }
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }

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
            "theorem t := by cases h : with | zero => rfl",
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
            .name("nested_tactic_alternatives_use_heap_frames".to_string())
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
            "· ; rfl",
            "focus unknownTactic",
        ] {
            let source = format!("theorem t : 0 = 0 := by\n  {body}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        // `focus`, `all_goals` and `try` take a `tacticSeq` positioned at its first token, so a
        // body on its own line at the enclosing column is theirs, as at the pin; `·` takes
        // `tacticSeqIndentGt`, so its body there is empty (refused above).
        for body in ["focus\n  rfl", "all_goals\n  rfl", "try\n  rfl"] {
            let source = format!("theorem t : 0 = 0 := by\n  {body}");
            assert!(parse_definition(source.as_bytes()).is_ok(), "{source}");
        }
    }
    #[test]
    fn deeply_nested_goal_scopes_are_heap_planned() {
        std::thread::Builder::new()
            .name("deeply_nested_goal_scopes_are_heap_planned".to_string())
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
            "theorem t : 0 = 0 := by\n  have loc : P := by\n    constructor <;> rfl\n  exact loc",
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
            .name("deep_sequencing_and_parentheses_use_the_heap_plan".to_string())
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
            .name("deeply_nested_choices_and_try_use_heap_parser_frames".to_string())
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
            .name("nested_repetition_uses_heap_parser_frames".to_string())
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
