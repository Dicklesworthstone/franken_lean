//! Refutable do-bind ranges on the shared, nonrecursive compound planner.
//!
//! The failure sequence and optional success continuation retain the pin's
//! separate layout anchors. Only the value is spliced: the ordinary do frame
//! still owns and validates the original pattern, annotation and assignment.
use super::*;

pub(super) struct FallbackPlan {
    pub(super) start: usize,
    depth: usize,
    assignment: usize,
    pipe: usize,
    otherwise_end: Option<usize>,
    continuation: Option<usize>,
    end: usize,
}

pub(super) fn candidate(
    tokens: &[LexedToken],
    at: usize,
    depth: usize,
    local: Option<&(usize, usize, usize, usize, bool)>,
    matches: usize,
) -> Option<(usize, usize)> {
    if !is_symbol(tokens, at, "|") {
        return None;
    }
    let &(local_depth, enclosing, _, start, statement) = local?;
    if !statement || depth != local_depth || matches > enclosing {
        return None;
    }
    let mut nested = 0usize;
    for index in start + 1..at {
        if ["(", "{", ".{", "[", "⦃"]
            .iter()
            .any(|t| is_symbol(tokens, index, t))
        {
            nested += 1;
        } else if [")", "}", "]", "⦄"]
            .iter()
            .any(|t| is_symbol(tokens, index, t))
        {
            nested = nested.checked_sub(1)?;
        } else if nested == 0
            && [":=", "←", "<-"]
                .iter()
                .any(|t| is_symbol(tokens, index, t))
        {
            return (index + 1 < at).then_some((start, index));
        }
    }
    None
}

pub(super) fn open(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    assignment: usize,
    pipe: usize,
    depth: usize,
    end: usize,
) -> Result<FallbackPlan, NatDefinitionParseError> {
    if pipe + 1 >= end || column(view, tokens, pipe) < column(view, tokens, start) {
        return Err(refuse(view, tokens, pipe));
    }
    // The pinned production is doSeqIndent, not doSeqBracketed.
    if is_symbol(tokens, pipe + 1, "{") {
        return Err(refuse(view, tokens, pipe + 1));
    }
    Ok(FallbackPlan {
        start,
        depth,
        assignment,
        pipe,
        otherwise_end: None,
        continuation: None,
        end,
    })
}

pub(super) fn advance(
    view: &SourceView,
    tokens: &[LexedToken],
    at: usize,
    depth: usize,
    scopes: &mut DoScopes,
    active: &mut Vec<FallbackPlan>,
    done: &mut Vec<Plan>,
) -> Result<(), NatDefinitionParseError> {
    while active.last().is_some_and(|p| scopes.ended(p.start)) {
        let p = active.last_mut().expect("ended fallback");
        scopes.closed(p.start);
        if p.otherwise_end.is_none() {
            p.otherwise_end = Some(at);
            if depth == p.depth
                && ![")", "]", "}", "⦄", ",", "|", "else"]
                    .iter()
                    .any(|t| is_symbol(tokens, at, t))
                && column(view, tokens, at) >= column(view, tokens, p.start)
            {
                p.continuation = Some(at);
                scopes.open_at(view, tokens, p.pipe, at, depth, Some(p.start), p.end)?;
                break;
            }
        }
        let mut p = active.pop().expect("completed fallback");
        p.end = at;
        done.push(Plan::Fallback(p));
    }
    Ok(())
}

pub(super) fn finish(active: &mut Vec<FallbackPlan>, done: &mut Vec<Plan>, end: usize) {
    while let Some(mut p) = active.pop() {
        p.end = end;
        done.push(Plan::Fallback(p));
    }
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    p: FallbackPlan,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<(), NatDefinitionParseError> {
    let value = branch_value(
        leaves,
        view,
        tokens,
        p.assignment + 1..p.pipe,
        grammar,
        splices,
        updates,
    )?;
    let otherwise = bounded_do_sequence_spliced(
        leaves,
        view,
        tokens,
        p.pipe + 1..p.otherwise_end.unwrap_or(p.end),
        grammar,
        splices,
        updates,
    )?;
    let continuation = match p.continuation {
        Some(start) => null_node(vec![bounded_do_sequence_spliced(
            leaves,
            view,
            tokens,
            start..p.end,
            grammar,
            splices,
            updates,
        )?]),
        None => null_node(vec![]),
    };
    let value = Syntax::node(
        parser_kind(&["Term", "nativeDoFailureValue"]),
        vec![value, leaves.leaf(p.pipe)?, otherwise, continuation],
    );
    splices.insert(p.assignment + 1, (p.end, value));
    Ok(())
}
