//! Constructor match syntax planned on a heap stack before term parsing.
//!
//! Each nested match is consumed once, inside out. This avoids recursive calls
//! to the term parser and preserves original leaves, including comments/CRLF.
//! Discriminants and pattern columns retain their comma leaves. Parenthesized
//! constructor patterns and nested matches are both planned without host recursion.
use super::*;
use std::collections::{HashMap, HashSet};
use std::ops::Range;
mod do_scopes;
mod exceptions;
mod fallback;
mod if_let;
use do_scopes::DoScopes;

pub(super) type Splices = HashMap<usize, (usize, Syntax)>;
struct Alternative {
    pipe: usize,
    /// `| p | q => e`: the pipes after the first, each separating a group of patterns that
    /// shares the right-hand side (`matchAlt`'s `sepBy1 (sepBy1 term ", ") " | "`).
    shared: Vec<usize>,
    arrow: Option<usize>,
    /// The first `by` or `do` at the alternative's depth after its `=>`: its sequence takes every
    /// `;` after it (`=> calc … := by skip; rfl`, `=> do f x; loop i`).
    by_at: Option<usize>,
    end: usize,
}
struct ConditionalPlan {
    statement: bool,
    start: usize,
    depth: usize,
    baseline: usize,
    pattern_assignment: Option<usize>,
    then_at: Option<usize>,
    else_at: Option<usize>,
    end: usize,
}
enum Plan {
    Match(MatchPlan),
    Conditional(ConditionalPlan),
    Fallback(fallback::FallbackPlan),
    Try(exceptions::TryPlan),
}
impl Plan {
    fn start(&self) -> usize {
        match self {
            Self::Match(p) => p.start,
            Self::Conditional(p) => p.start,
            Self::Fallback(p) => p.start,
            Self::Try(p) => p.start,
        }
    }
}
struct MatchPlan {
    statement: bool,
    function: bool,
    catch: bool,
    baseline: usize,
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
/// The bracket closing the one opened at `open` (a compound opener such as `` `(tactic| `` too),
/// before `end`.
fn bracket_close(tokens: &[LexedToken], open: usize, end: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (at, token) in tokens.iter().enumerate().take(end).skip(open) {
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
fn later_line(view: &SourceView, tokens: &[LexedToken], a: usize, b: usize) -> bool {
    view.normalized().line_of(tokens[a].extent.start())
        > view.normalized().line_of(tokens[b].extent.start())
}
fn close(
    view: &SourceView,
    tokens: &[LexedToken],
    active: &mut Vec<MatchPlan>,
    done: &mut Vec<Plan>,
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
    done.push(Plan::Match(plan));
    Ok(())
}
fn close_conditional(
    view: &SourceView,
    tokens: &[LexedToken],
    active: &mut Vec<ConditionalPlan>,
    done: &mut Vec<Plan>,
    end: usize,
) -> Result<(), NatDefinitionParseError> {
    let mut conditional = active.pop().expect("active conditional");
    if conditional
        .then_at
        .is_none_or(|at| at <= conditional.start + 1)
        || match conditional.else_at {
            Some(at) => at <= conditional.then_at.expect("validated then") + 1 || at + 1 >= end,
            None => !conditional.statement || conditional.then_at.is_none_or(|at| at + 1 >= end),
        }
    {
        return Err(refuse(view, tokens, end));
    }
    conditional.end = end;
    done.push(Plan::Conditional(conditional));
    Ok(())
}

fn plan(
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    equations: bool,
) -> Result<Vec<Plan>, NatDefinitionParseError> {
    let mut delimiters = Vec::new();
    let mut active: Vec<MatchPlan> = if equations {
        vec![MatchPlan {
            statement: false,
            function: false,
            catch: false,
            baseline: 0,
            start: range.start,
            depth: 0,
            with: Some(range.start),
            alternatives: Vec::new(),
            end: range.end,
        }]
    } else {
        Vec::new()
    };
    let mut conditionals: Vec<ConditionalPlan> = Vec::new();
    let mut lets = Vec::new();
    let mut fallbacks = Vec::new();
    let mut tries = exceptions::Planner::default();
    let mut done = Vec::new();
    let mut do_scopes = DoScopes::default();
    let mut pending_matches: Option<(usize, usize)> = None;
    // A `by` block inside brackets that is no row's proof (`⟨by intro h; induction l with | …, x⟩`)
    // is the proof parser's whole: its tactics' `|`s, `with`s and `match`es are not this plan's.
    let mut proof_end = 0;
    // Per bracket depth, the binders (`∃ h : p, q`, `∀ x, p`, `Σ x, β x`) whose comma is still to
    // come: that comma is the binder's own, not one that ends an alternative's body.
    let mut binder_commas: Vec<usize> = Vec::new();
    for at in range.clone() {
        if at < proof_end {
            continue;
        }
        let depth = delimiters.len();
        let failure = fallback::candidate(tokens, at, depth, lets.last(), active.len());
        do_scopes.before(
            view,
            tokens,
            at,
            depth,
            &conditionals,
            &active,
            failure.is_some(),
        );
        tries.before(
            view,
            tokens,
            at,
            depth,
            &mut do_scopes,
            &mut active,
            &mut done,
            range.end,
        )?;
        fallback::advance(
            view,
            tokens,
            at,
            depth,
            &mut do_scopes,
            &mut fallbacks,
            &mut done,
        )?;
        while conditionals.last().is_some_and(|p| {
            p.statement
                && do_scopes.ended(p.start)
                && !(is_symbol(tokens, at, "else")
                    && p.else_at.is_none()
                    && DoScopes::accepts_else(view, tokens, at, p))
        }) {
            do_scopes.closed(conditionals.last().expect("ended conditional").start);
            close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
        }
        // A do-match ends when its final arm leaves the do-sequence scope.
        // A following pipe still belongs to the match planner, which resolves
        // nested arm indentation before assigning it to an enclosing match.
        while active
            .last()
            .is_some_and(|p| p.statement && do_scopes.ended(p.start) && !is_symbol(tokens, at, "|"))
        {
            do_scopes.closed(active.last().expect("ended do match").start);
            close(view, tokens, &mut active, &mut done, at)?;
        }
        let statement = do_scopes
            .statement_at(view, tokens, at, depth)
            .or_else(|| do_scopes.arrow_element(view, tokens, at, depth));
        if term_locals::word(tokens, at, "do") {
            do_scopes.open(view, tokens, at, depth, None, range.end)?;
        }
        // The value of an offside local declaration has ended. Close only
        // compound expressions opened in that value; its containing branch
        // continues with the next local declaration or result expression.
        while lets.last().is_some_and(|&(depth, _, _, keyword, _)| {
            failure.is_none()
                && depth == delimiters.len()
                && local_line_break(view, tokens, keyword, keyword, at)
        }) {
            let (_, enclosing, enclosing_conditionals, _, _) =
                lets.pop().expect("offside local declaration");
            while conditionals.len() > enclosing_conditionals
                && conditionals
                    .last()
                    .is_some_and(|p| p.depth == delimiters.len())
            {
                close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
            }
            while active.len() > enclosing
                && active.last().is_some_and(|p| p.depth == delimiters.len())
            {
                close(view, tokens, &mut active, &mut done, at)?;
            }
        }
        // A completed conditional in a local value ends at the next outer
        // statement. Nested conditionals share this heap plan with matches.
        while conditionals.last().is_some_and(|p| {
            p.depth == delimiters.len()
                && ((!p.statement
                    && p.else_at.is_some()
                    && later_line(view, tokens, at, p.start)
                    && column(view, tokens, at) <= p.baseline
                    && !is_symbol(tokens, at, "else"))
                    || (p.statement
                        && do_scopes.ended(p.start)
                        && !(is_symbol(tokens, at, "else")
                            && p.else_at.is_none()
                            && DoScopes::accepts_else(view, tokens, at, p))))
        }) {
            close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
        }
        // A function used in a tactic-local value must stop at the next outer
        // statement, not consume it as the final branch's application argument.
        // Use the enclosing line's indentation, not the inline `fun` column.
        while active.last().is_some_and(|p| {
            p.function
                && p.depth == delimiters.len()
                && later_line(view, tokens, at, p.start)
                && column(view, tokens, at) <= p.baseline
                && !is_symbol(tokens, at, "|")
                && p.alternatives.last().is_some_and(|alt| alt.arrow.is_some())
        }) {
            close(view, tokens, &mut active, &mut done, at)?;
        }
        let TokenKind::Symbol(symbol) = &tokens[at].kind else {
            continue;
        };
        // A quotation is read whole, as a `by` block is: a tactic quotation's `first` pipes
        // (`(tactic|⏎  first⏎  | exact …)`) are not this plan's, and a term quotation's `match`
        // or `if` (`(if $c then …)`) is planned by the quotation's own term.
        if crate::quotations::opens(symbol)
            && let Some(close) = bracket_close(tokens, at, range.end)
        {
            proof_end = close + 1;
            continue;
        }
        let depth = delimiters.len();
        if matches!(
            symbol.as_str(),
            "∃" | "∃!" | "∀" | "forall" | "exists" | "Σ" | "Σ'"
        ) {
            if binder_commas.len() <= depth {
                binder_commas.resize(depth + 1, 0);
            }
            binder_commas[depth] += 1;
        }
        let proof_body = active.last().is_some_and(|p| {
            p.depth == depth
                && p.alternatives.last().is_some_and(|alt| {
                    alt.arrow
                        .is_some_and(|arrow| is_symbol(tokens, arrow + 1, "by") && at > arrow + 1)
                        || alt.by_at.is_some_and(|by| at > by)
                })
        });
        // A row's tactic proof (`=> by …`), as opposed to its `do` block, which also owns `;`s.
        let tactic_body = active.last().is_some_and(|p| {
            p.depth == depth
                && p.alternatives.last().is_some_and(|alt| {
                    alt.arrow
                        .is_some_and(|arrow| is_symbol(tokens, arrow + 1, "by") && at > arrow + 1)
                        || alt
                            .by_at
                            .is_some_and(|by| at > by && is_symbol(tokens, by, "by"))
                })
        });
        let mut statement_separator = false;
        // A compound symbol acts as the bracket it contains (`]'` in `xs[i]'h` closes `[`).
        match crate::canonical_bracket(symbol.as_str()) {
            // In a row's proof (`| 0 => by simp; try omega`), and outside every `do` block (a
            // quotation's `(tactic| …; try omega)`), `try` is the tactic's.
            "try" if tactic_body || statement.is_none() => {}
            "try" => {
                let baseline = statement.ok_or_else(|| refuse(view, tokens, at))?;
                tries.open(view, tokens, at, depth, baseline, &mut do_scopes, range.end)?;
            }
            ":" if tries.in_header(at) => {}
            // `bif c then a else b` is a term, never a `do` statement's conditional.
            "bif" if statement.is_some() => return Err(refuse(view, tokens, at)),
            "if" | "bif" => conditionals.push(ConditionalPlan {
                statement: statement.is_some(),
                start: at,
                depth,
                baseline: statement.unwrap_or_else(|| {
                    let source = view.normalized();
                    let begin = source
                        .line_start(source.line_of(tokens[at].extent.start()))
                        .expect("conditional line")
                        .0;
                    source.as_bytes()[begin..tokens[at].extent.start().0]
                        .iter()
                        .take_while(|&&b| b == b' ' || b == b'\t')
                        .count()
                }),
                pattern_assignment: None,
                then_at: None,
                else_at: None,
                end: range.end,
            }),
            "then" | "else" => {
                let target = conditionals
                    .iter()
                    .rposition(|p| {
                        p.depth == depth
                            && if symbol == "then" {
                                p.then_at.is_none()
                            } else {
                                p.then_at.is_some()
                                    && p.else_at.is_none()
                                    && DoScopes::accepts_else(view, tokens, at, p)
                            }
                    })
                    .ok_or_else(|| refuse(view, tokens, at))?;
                while conditionals.len() > target + 1 {
                    close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
                }
                let current = &mut conditionals[target];
                while active
                    .last()
                    .is_some_and(|p| p.start > current.start && p.depth == depth)
                {
                    close(view, tokens, &mut active, &mut done, at)?;
                }
                if symbol == "then" {
                    if at == current.start + 1 {
                        return Err(refuse(view, tokens, at));
                    }
                    current.then_at = Some(at);
                } else {
                    if current.then_at == Some(at - 1) {
                        return Err(refuse(view, tokens, at));
                    }
                    current.else_at = Some(at);
                }
                if current.statement {
                    if at + 1 < range.end
                        && !is_symbol(tokens, at + 1, "{")
                        && later_line(view, tokens, at + 1, at)
                        && column(view, tokens, at + 1) <= current.baseline
                    {
                        return Err(refuse(view, tokens, at + 1));
                    }
                    do_scopes.open(view, tokens, at, depth, Some(current.start), range.end)?;
                }
            }
            "match" => active.push(MatchPlan {
                catch: false,
                statement: statement.is_some(),
                function: false,
                baseline: statement.unwrap_or(0),
                start: at,
                depth,
                with: None,
                alternatives: Vec::new(),
                end: range.end,
            }),
            "fun" | "λ" if is_symbol(tokens, at + 1, "|") => active.push(MatchPlan {
                catch: false,
                statement: false,
                function: true,
                baseline: {
                    let source = view.normalized();
                    let begin = source
                        .line_start(source.line_of(tokens[at].extent.start()))
                        .expect("function line")
                        .0;
                    source.as_bytes()[begin..tokens[at].extent.start().0]
                        .iter()
                        .take_while(|&&byte| byte == b' ' || byte == b'\t')
                        .count()
                },
                start: at,
                depth,
                with: Some(at),
                alternatives: Vec::new(),
                end: range.end,
            }),
            "let"
                if conditionals
                    .last()
                    .is_some_and(|p| p.depth == depth && p.start + 1 == at) =>
            {
                // A pattern-test header is not a term-local let telescope.
                // Its binding ends at `then`, not at a later branch semicolon.
            }
            // A term `if let` binds with `:=` only (`termIfLet`); a statement may bind with `←`.
            ":=" | "←" | "<-"
                if conditionals.last().is_some_and(|p| {
                    (p.statement || is_symbol(tokens, at, ":="))
                        && p.depth == depth
                        && p.then_at.is_none()
                        && p.pattern_assignment.is_none()
                        && is_symbol(tokens, p.start + 1, "let")
                }) =>
            {
                conditionals
                    .last_mut()
                    .expect("pattern condition")
                    .pattern_assignment = Some(at);
            }
            // `have k : T := v` annotates like `let`: its `:` does not end the branch.
            "let" | "have" | "letI" | "haveI" | "suffices" => lets.push((
                depth,
                active.len(),
                conditionals.len(),
                at,
                statement.is_some(),
            )),
            // A `do` owns the `;`s after it as a `by` does (`=> do f x; loop i`).
            "by" if depth > 0
                && statement.is_none()
                && active.last().is_none_or(|p| p.depth != depth)
                && conditionals.last().is_none_or(|p| p.depth != depth) =>
            {
                proof_end = proofs::block_extent(view, tokens, at, range.end)?;
            }
            "by" | "do" => {
                if let Some(current) = active.last_mut()
                    && current.depth == depth
                    && let Some(alt) = current.alternatives.last_mut()
                    && alt.arrow.is_some_and(|arrow| at > arrow)
                    && alt.by_at.is_none()
                {
                    alt.by_at = Some(at);
                }
            }
            ";" | ":" if proof_body => {}
            ";" => {
                // A let's separator ends matches in its VALUE, not the outer
                // match whose branch contains the let and its continuation.
                let (enclosing, enclosing_conditionals) =
                    if lets.last().is_some_and(|(d, _, _, _, _)| *d == depth) {
                        let (_, matches, conditionals, _, is_statement) =
                            lets.pop().expect("let at current depth");
                        statement_separator = is_statement;
                        (matches, conditionals)
                    } else {
                        statement_separator = true;
                        (0, 0)
                    };
                while conditionals.len() > enclosing_conditionals
                    && conditionals
                        .last()
                        .is_some_and(|p| p.depth == depth && !p.statement)
                {
                    close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
                }
                while active.len() > enclosing
                    && active
                        .last()
                        .is_some_and(|p| p.depth == depth && !p.statement)
                {
                    close(view, tokens, &mut active, &mut done, at)?;
                }
            }
            // A syntax quotation closes with `)` (`quotations`).
            "(" | "`(" | "`(tactic|" | "`(conv|" => delimiters.push(")"),
            "{" | ".{" => delimiters.push("}"),
            "[" => delimiters.push("]"),
            "⦃" => delimiters.push("⦄"),
            "⟨" => delimiters.push("⟩"),
            ":" if active.last().is_some_and(|p| {
                p.depth == depth
                    && p.with.is_none()
                    && (at == p.start + 2 || at >= 2 && is_symbol(tokens, at - 2, ","))
                    && (matches!(tokens[at - 1].kind, TokenKind::Ident(_))
                        || is_symbol(tokens, at - 1, "_"))
            }) => {}
            ":" if conditionals.last().is_some_and(|p| {
                p.depth == depth
                    && p.then_at.is_none()
                    && at == p.start + 2
                    && (matches!(tokens[p.start + 1].kind, TokenKind::Ident(_))
                        || is_symbol(tokens, p.start + 1, "_"))
            }) => {}
            ":" if lets.last().is_some_and(|(d, enclosing, _, _, _)| {
                *d == depth && active.len() <= *enclosing
            }) => {}
            ")" | "}" | "]" | "⦄" | "⟩" | "," | ":" => {
                // The binder's own comma, and its type's `:` before it (`∃ h : p, q`).
                if binder_commas.get(depth).is_some_and(|&open| open > 0) {
                    if symbol == "," {
                        binder_commas[depth] -= 1;
                        continue;
                    }
                    if symbol == ":" {
                        continue;
                    }
                }
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
                // A comma before the conditional's `then` is its condition's own (`if ∃ i, p i
                // then …`): an `if` cannot end before its `then`.
                if symbol == ","
                    && conditionals
                        .last()
                        .is_some_and(|p| p.depth == depth && p.then_at.is_none())
                {
                    continue;
                }
                while conditionals
                    .last()
                    .is_some_and(|p| p.depth == depth && (symbol != ":" || !p.statement))
                {
                    close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
                }
                while active
                    .last()
                    .is_some_and(|p| p.depth == depth && (symbol != ":" || !p.statement))
                {
                    close(view, tokens, &mut active, &mut done, at)?;
                }
                if matches!(
                    crate::canonical_bracket(symbol.as_str()),
                    ")" | "}" | "]" | "⦄" | "⟩"
                ) && delimiters.pop() != Some(crate::canonical_bracket(symbol.as_str()))
                {
                    return Err(refuse(view, tokens, at));
                }
                // A binder inside the brackets ended with them.
                binder_commas.truncate(delimiters.len() + 1);
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
            // `e matches p | q`: the `|`s on the `matches` line at its depth are its own.
            "matches" => pending_matches = Some((depth, at)),
            "|" if pending_matches
                .is_some_and(|(d, start)| d == depth && !later_line(view, tokens, at, start)) => {}
            "|" => {
                while conditionals.last().is_some_and(|p| {
                    p.depth == depth
                        && active.last().is_none_or(|m| m.start < p.start)
                        && failure.is_none_or(|(start, _)| p.start > start)
                }) {
                    close_conditional(view, tokens, &mut conditionals, &mut done, at)?;
                }
                if let Some((start, assignment)) = failure {
                    lets.pop();
                    let p = fallback::open(view, tokens, start, assignment, at, depth, range.end)?;
                    do_scopes.open(view, tokens, at, depth, Some(start), range.end)?;
                    fallbacks.push(p);
                    continue;
                }
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
                let Some(current) = active.last_mut() else {
                    return Err(refuse(view, tokens, at));
                };
                if current.depth != depth || current.with.is_none() {
                    return Err(refuse(view, tokens, at));
                }
                // A later line's alternative starts at the first one's column; a pipe inside the
                // line (`| ofNat _, succ _ | -[_+1], 0 => …`) separates that row's groups.
                if let Some(first) = current.alternatives.first()
                    && later_line(view, tokens, at, first.pipe)
                    && (at == 0 || later_line(view, tokens, at, at - 1))
                    && column(view, tokens, at) != column(view, tokens, first.pipe)
                {
                    return Err(refuse(view, tokens, at));
                }
                // Before the `=>`, a pipe starts another group of the same alternative.
                let shared = current
                    .alternatives
                    .last()
                    .is_some_and(|last| last.arrow.is_none());
                if let Some(last) = current.alternatives.last_mut() {
                    if shared {
                        if at == last.shared.last().copied().unwrap_or(last.pipe) + 1 {
                            return Err(refuse(view, tokens, at));
                        }
                        last.shared.push(at);
                    } else {
                        if last.arrow.is_some_and(|arrow| arrow + 1 >= at) {
                            return Err(refuse(view, tokens, at));
                        }
                        last.end = at;
                    }
                }
                if !shared {
                    // The preceding arm ended at this pipe, but the match has
                    // not ended: retain it while scanning the next pattern/header.
                    do_scopes.closed(current.start);
                    current.alternatives.push(Alternative {
                        pipe: at,
                        shared: Vec::new(),
                        arrow: None,
                        by_at: None,
                        end: range.end,
                    });
                }
            }
            "=>" | "↦" if active.last().is_some_and(|p| p.depth == depth) => {
                let current = active.last_mut().expect("matching depth");
                if let Some(alt) = current.alternatives.last_mut()
                    && alt.arrow.is_none()
                {
                    alt.arrow = Some(at);
                    if current.statement {
                        if at + 1 < range.end
                            && !is_symbol(tokens, at + 1, "{")
                            && later_line(view, tokens, at + 1, at)
                            && column(view, tokens, at + 1) < column(view, tokens, alt.pipe)
                        {
                            return Err(refuse(view, tokens, at + 1));
                        }
                        do_scopes.open(view, tokens, at, depth, Some(current.start), range.end)?;
                    }
                }
            }
            _ => {}
        }
        do_scopes.after(tokens, at, depth, statement_separator);
    }
    while !conditionals.is_empty() {
        close_conditional(view, tokens, &mut conditionals, &mut done, range.end)?;
    }
    while !active.is_empty() {
        close(view, tokens, &mut active, &mut done, range.end)?;
    }
    fallback::finish(&mut fallbacks, &mut done, range.end);
    tries.finish(&mut done, range.end);
    if !delimiters.is_empty() {
        return Err(refuse(view, tokens, range.end));
    }
    // An inner match always starts later. Build it first and splice it once
    // into its parent's body, never by recursively invoking the parser.
    done.sort_by_key(|p| std::cmp::Reverse(p.start()));
    Ok(done)
}
/// Whether `range` is a list pattern at its own top level: a `[` or a `::` outside every bracket
/// (`[a, b]`, `x :: l`, and `some [x]`, which the list reader takes whole). List syntax nested in
/// an anonymous constructor or a tuple (`⟨[]⟩`, `(x, [y])`) is the nested pattern's.
fn list_pattern(tokens: &[LexedToken], range: Range<usize>) -> bool {
    let mut depth = 0usize;
    for at in range {
        match &tokens[at].kind {
            TokenKind::Symbol(symbol) if depth == 0 && matches!(symbol.as_str(), "[" | "::") => {
                return true;
            }
            TokenKind::Symbol(symbol)
                if matches!(symbol.as_str(), "(" | "[" | "{" | "⟨" | "#[") =>
            {
                depth += 1;
            }
            TokenKind::Symbol(symbol) if matches!(symbol.as_str(), ")" | "]" | "}" | "⟩") => {
                depth = depth.saturating_sub(1);
            }
            _ => {}
        }
    }
    false
}

fn pattern(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    // A syntax quotation (`macro_rules | `(f $x) => …`) is a term, read whole.
    if let Some((quotation, next)) =
        crate::quotations::quotation(leaves, view, tokens, range.start, range.end)?
    {
        if next != range.end {
            return Err(refuse(view, tokens, next));
        }
        return Ok(quotation);
    }
    // `x@p` around a list pattern (`l@(x :: _)`): the name, then the pattern it names.
    if range.len() >= 3
        && matches!(tokens[range.start].kind, TokenKind::Ident(_))
        && is_symbol(tokens, range.start + 1, "@")
        && tokens[range.start].extent.end() == tokens[range.start + 1].extent.start()
        && tokens[range.start + 1].extent.end() == tokens[range.start + 2].extent.start()
        && range
            .clone()
            .any(|at| is_symbol(tokens, at, "[") || is_symbol(tokens, at, "::"))
    {
        let named = collections::pattern(leaves, view, tokens, range.start + 2..range.end)?;
        return Ok(Syntax::node(
            parser_kind(&["Term", "namedPattern"]),
            vec![
                leaves.leaf(range.start)?,
                leaves.leaf(range.start + 1)?,
                null_node(Vec::new()),
                named,
            ],
        ));
    }
    if list_pattern(tokens, range.clone()) {
        return collections::pattern(leaves, view, tokens, range);
    }
    enum Task {
        Parse(Range<usize>),
        Group(usize, usize),
        Application(usize),
        /// `p + k` with a numeral `k`: the pin's Nat offset pattern (`«term_+_»`), at the
        /// `+` and the numeral.
        Offset(usize, usize),
        /// `⟨p, …⟩` (`Term.anonymousCtor`): the brackets, the separating commas, and the
        /// number of element patterns on the value stack.
        Anonymous(usize, usize, Vec<usize>, usize),
        /// `(p, q, …)` (`Term.tuple`, `[p "," [q "," …]]`): as [`Task::Anonymous`].
        Tuple(usize, usize, Vec<usize>, usize),
        /// `x@p` (`Term.namedPattern`): the name and the `@`.
        Named(usize, usize),
        /// `(p : T)` (`Term.typeAscription`): the brackets and the colon; the type is a term.
        Ascription(usize, usize, usize),
        /// `..` as an application's last argument (`Term.ellipsis`): every remaining explicit
        /// argument a hole.
        Ellipsis(usize),
    }
    let mut pairs = HashMap::new();
    let mut opens = Vec::new();
    for at in range.clone() {
        if is_symbol(tokens, at, "(") || is_symbol(tokens, at, "⟨") {
            opens.push(at);
        } else if is_symbol(tokens, at, ")") || is_symbol(tokens, at, "⟩") {
            let open = opens.pop().ok_or_else(|| refuse(view, tokens, at))?;
            if is_symbol(tokens, open, "(") != is_symbol(tokens, at, ")") {
                return Err(refuse(view, tokens, at));
            }
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
            Task::Ascription(open, colon, close) => {
                let pattern = values.pop().expect("planned ascribed pattern");
                let type_ = bounded_term(
                    leaves,
                    view,
                    tokens,
                    colon + 1..close,
                    DefinitionGrammar::Scalar,
                )?;
                values.push(Syntax::node(
                    parser_kind(&["Term", "typeAscription"]),
                    vec![
                        hygienic_lparen(leaves.leaf(open)?),
                        pattern,
                        leaves.leaf(colon)?,
                        null_node(vec![type_]),
                        leaves.leaf(close)?,
                    ],
                ));
            }
            Task::Named(name, at) => {
                let pattern = values.pop().expect("planned named pattern");
                values.push(Syntax::node(
                    parser_kind(&["Term", "namedPattern"]),
                    vec![
                        leaves.leaf(name)?,
                        leaves.leaf(at)?,
                        null_node(Vec::new()),
                        pattern,
                    ],
                ));
            }
            Task::Offset(plus, literal) => {
                let base = values.pop().expect("planned offset base");
                values.push(Syntax::node(
                    Name::str(Name::anonymous(), "term_+_"),
                    vec![
                        base,
                        leaves.leaf(plus)?,
                        bounded_term_leaf(
                            leaves,
                            view,
                            tokens,
                            literal,
                            DefinitionGrammar::Scalar,
                        )?,
                    ],
                ));
            }
            Task::Anonymous(open, close, commas, count) => {
                let elements = values.split_off(values.len() - count);
                let mut items = Vec::with_capacity(elements.len() * 2);
                for (index, element) in elements.into_iter().enumerate() {
                    if index > 0 {
                        items.push(leaves.leaf(commas[index - 1])?);
                    }
                    items.push(element);
                }
                values.push(Syntax::node(
                    parser_kind(&["Term", "anonymousCtor"]),
                    vec![leaves.leaf(open)?, null_node(items), leaves.leaf(close)?],
                ));
            }
            Task::Tuple(open, close, commas, count) => {
                let mut elements = values.split_off(values.len() - count).into_iter();
                let first = elements.next().expect("a tuple's first element");
                let mut rest = Vec::with_capacity(count * 2);
                for (index, element) in elements.enumerate() {
                    if index > 0 {
                        rest.push(leaves.leaf(commas[index])?);
                    }
                    rest.push(element);
                }
                values.push(Syntax::node(
                    parser_kind(&["Term", "tuple"]),
                    vec![
                        hygienic_lparen(leaves.leaf(open)?),
                        null_node(vec![first, leaves.leaf(commas[0])?, null_node(rest)]),
                        leaves.leaf(close)?,
                    ],
                ));
            }
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
            Task::Ellipsis(at) => {
                values.push(Syntax::node(
                    parser_kind(&["Term", "ellipsis"]),
                    vec![leaves.leaf(at)?],
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
                // A list pattern inside another (`⟨[]⟩`, `⟨a :: l⟩`, `(x, [y])`).
                if list_pattern(tokens, range.clone()) {
                    values.push(collections::pattern(leaves, view, tokens, range)?);
                    continue;
                }
                // `namedPattern := ident noWs "@" noWs (ident ":")? term:max`: the name touches
                // the `@`, which touches one atomic pattern ending the range (`l@(x :: _)`).
                let touching = |left: usize, right: usize| {
                    tokens[left].extent.end() == tokens[right].extent.start()
                };
                if range.len() >= 3
                    && matches!(tokens[range.start].kind, TokenKind::Ident(_))
                    && is_symbol(tokens, range.start + 1, "@")
                    && touching(range.start, range.start + 1)
                    && touching(range.start + 1, range.start + 2)
                    && (range.len() == 3
                        || pairs.get(&(range.start + 2)) == Some(&(range.end - 1))
                        || (range.len() == 4
                            && is_symbol(tokens, range.start + 2, ".")
                            && touching(range.start + 2, range.start + 3)))
                {
                    tasks.push(Task::Named(range.start, range.start + 1));
                    tasks.push(Task::Parse(range.start + 2..range.end));
                    continue;
                }
                // `+` binds looser than application, so a trailing `+ k` outside every
                // parenthesis splits the pattern: `n + 2`, `(succ n) + 1`.
                if range.len() >= 3
                    && is_symbol(tokens, range.end - 2, "+")
                    && matches!(
                        tokens[range.end - 1].kind,
                        TokenKind::Literal(LiteralKind::Nat)
                    )
                    && !range.clone().any(|at| {
                        at < range.end - 2
                            && (is_symbol(tokens, at, "+")
                                || pairs.get(&at).is_some_and(|close| *close > range.end - 2))
                    })
                {
                    tasks.push(Task::Offset(range.end - 2, range.end - 1));
                    tasks.push(Task::Parse(range.start..range.end - 2));
                    continue;
                }
                if is_symbol(tokens, range.start, "⟨") {
                    let close = pairs[&range.start];
                    if close + 1 != range.end {
                        return Err(refuse(view, tokens, close + 1));
                    }
                    let inner = range.start + 1..close;
                    let elements = if inner.is_empty() {
                        Vec::new()
                    } else {
                        columns(tokens, inner)
                    };
                    let commas = elements.iter().filter_map(|(_, comma)| *comma).collect();
                    tasks.push(Task::Anonymous(range.start, close, commas, elements.len()));
                    tasks.extend(
                        elements
                            .into_iter()
                            .rev()
                            .map(|(range, _)| Task::Parse(range)),
                    );
                    continue;
                }
                if is_symbol(tokens, range.start, "(") {
                    let close = pairs[&range.start];
                    if close + 1 != range.end {
                        return Err(refuse(view, tokens, close + 1));
                    }
                    let inner = range.start + 1..close;
                    let elements = if inner.is_empty() {
                        Vec::new()
                    } else {
                        columns(tokens, inner.clone())
                    };
                    if elements.len() > 1 {
                        if elements.iter().any(|(range, _)| range.is_empty()) {
                            return Err(refuse(view, tokens, range.start));
                        }
                        let commas = elements.iter().filter_map(|(_, comma)| *comma).collect();
                        tasks.push(Task::Tuple(range.start, close, commas, elements.len()));
                        tasks.extend(
                            elements
                                .into_iter()
                                .rev()
                                .map(|(range, _)| Task::Parse(range)),
                        );
                        continue;
                    }
                    // `(p : T)`: a colon outside the inner brackets ascribes the pattern.
                    let mut depth = 0usize;
                    let colon = inner.clone().find(|&at| {
                        if let TokenKind::Symbol(s) = &tokens[at].kind {
                            match crate::canonical_bracket(s.as_str()) {
                                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                                ":" if depth == 0 => return true,
                                _ => {}
                            }
                        }
                        false
                    });
                    if let Some(colon) = colon {
                        if colon == inner.start || colon + 1 == close {
                            return Err(refuse(view, tokens, colon));
                        }
                        tasks.push(Task::Ascription(range.start, colon, close));
                        tasks.push(Task::Parse(inner.start..colon));
                        continue;
                    }
                    tasks.push(Task::Group(range.start, close));
                    tasks.push(Task::Parse(inner));
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
                } else if !dot
                    && matches!(
                        tokens[cursor].kind,
                        TokenKind::Literal(LiteralKind::Nat | LiteralKind::Str)
                    )
                {
                    if cursor + 1 != range.end {
                        return Err(refuse(view, tokens, cursor + 1));
                    }
                    bounded_term_leaf(leaves, view, tokens, cursor, DefinitionGrammar::Scalar)?
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
                } else if let Some((notation, end)) = (!dot)
                    .then(|| {
                        crate::extensions::leading_term(leaves, view, tokens, cursor, range.end)
                    })
                    .flatten()
                {
                    // An atom-like notation of the entered grammar (`-[n+1]` under `open Int`).
                    cursor = end - 1;
                    notation
                } else {
                    return Err(refuse(view, tokens, cursor));
                };
                cursor += 1;
                let start = values.len();
                values.push(head);
                let mut arguments = Vec::new();
                let mut ellipsis = None;
                while cursor < range.end {
                    let begin = cursor;
                    // `f a ..`: only the last argument may be the ellipsis.
                    if is_symbol(tokens, cursor, "..") {
                        if cursor + 1 != range.end {
                            return Err(refuse(view, tokens, cursor));
                        }
                        ellipsis = Some(cursor);
                        break;
                    }
                    // `x@p` as an argument (`.inner _ l@(.inner ..)`): the name, a touching `@` and
                    // the atomic pattern touching it are one argument.
                    let touches = |left: usize, right: usize| {
                        right < range.end
                            && tokens[left].extent.end() == tokens[right].extent.start()
                    };
                    if matches!(tokens[cursor].kind, TokenKind::Ident(_))
                        && is_symbol(tokens, cursor + 1, "@")
                        && touches(cursor, cursor + 1)
                        && touches(cursor + 1, cursor + 2)
                    {
                        cursor += 2;
                    }
                    if is_symbol(tokens, cursor, "(") || is_symbol(tokens, cursor, "⟨") {
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
                if !arguments.is_empty() || ellipsis.is_some() {
                    tasks.push(Task::Application(start));
                    tasks.extend(ellipsis.map(Task::Ellipsis));
                    tasks.extend(arguments.into_iter().rev().map(Task::Parse));
                }
            }
        }
    }
    Ok(values.pop().expect("one complete pattern"))
}

/// The else-if clauses an `else` followed by an `if` makes: when the `else` branch is exactly one
/// `doIf` statement, its condition and sequence become the first clause and its own clauses and
/// `else` follow; otherwise the branch is kept as written.
fn else_if_clauses(else_atom: Syntax, otherwise: Syntax) -> (Vec<Syntax>, Syntax) {
    fn args(syntax: &Syntax) -> &[Syntax] {
        match syntax {
            Syntax::Node { args, .. } => args,
            _ => &[],
        }
    }
    let nested = match args(&otherwise) {
        [_, sequence] if sequence.kind() == Some(&parser_kind(&["Term", "doSeqIndent"])) => {
            match args(sequence) {
                [items] => match args(items) {
                    [item] => match args(item) {
                        [element, semi]
                            if args(semi).is_empty()
                                && element.kind() == Some(&parser_kind(&["Term", "doIf"]))
                                && args(element).len() == 6 =>
                        {
                            Some(args(element).to_vec())
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    };
    let Some(parts) = nested else {
        return (Vec::new(), otherwise);
    };
    let mut clauses = vec![Syntax::node(
        Name::from_components(["group"]),
        vec![
            Syntax::node(
                Name::from_components(["group"]),
                vec![else_atom, parts[0].clone()],
            ),
            parts[1].clone(),
            parts[2].clone(),
            parts[3].clone(),
        ],
    )];
    clauses.extend(args(&parts[4]).iter().cloned());
    (clauses, parts[5].clone())
}

/// The separators are returned as indices so reconstruction keeps their exact
/// original source attachment, including comments and CRLF whitespace.
fn columns(tokens: &[LexedToken], range: Range<usize>) -> Vec<(Range<usize>, Option<usize>)> {
    let mut depth = 0usize;
    let mut start = range.start;
    let mut result = Vec::new();
    for at in range.clone() {
        if let TokenKind::Symbol(symbol) = &tokens[at].kind {
            match crate::canonical_bracket(symbol.as_str()) {
                "(" | "{" | ".{" | "[" | "⦃" | "⟨" => depth += 1,
                ")" | "}" | "]" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
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
    let mut head = range.start;
    while head < range.end && is_symbol(tokens, head, "(") {
        head += 1;
    }
    if is_symbol(tokens, head, "let") {
        let_values(leaves, view, tokens, range, grammar, splices, updates)
    } else {
        bounded_term_spliced(leaves, view, tokens, range, grammar, splices, updates)
    }
}

// Keep construction temporaries off the ordinary-term parser's small stack.
#[inline(never)]
fn let_values(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    enum Task {
        Value(Range<usize>),
        Close(Vec<LetBindingTokens>),
        Parentheses(usize, usize, usize),
    }
    let mut tasks = vec![Task::Value(range)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Value(range) => {
                let mut head = range.start;
                while head < range.end && is_symbol(tokens, head, "(") {
                    head += 1;
                }
                let wrappers = head - range.start;
                if wrappers > 0 && is_symbol(tokens, head, "let") {
                    // Strip complete outer wrappers in one pass, not one
                    // rescan per parenthesis. Infix/application surroundings
                    // stay with the ordinary term parser.
                    let end = range.end.saturating_sub(wrappers);
                    let mut depth = wrappers;
                    let mut enclosed = head < end;
                    for at in head..end {
                        if is_symbol(tokens, at, "(") {
                            depth += 1;
                        }
                        if is_symbol(tokens, at, ")") {
                            depth = depth.saturating_sub(1);
                        }
                        enclosed &= depth >= wrappers;
                    }
                    enclosed &=
                        depth == wrappers && (end..range.end).all(|at| is_symbol(tokens, at, ")"));
                    if enclosed {
                        tasks.push(Task::Parentheses(range.start, range.end, wrappers));
                        tasks.push(Task::Value(head..end));
                        continue;
                    }
                }
                let (bindings, body_start) =
                    bounded_let_bindings(view, &tokens[..range.end], range.start)?;
                if bindings.is_empty() {
                    values.push(bounded_term_spliced(
                        leaves, view, tokens, range, grammar, splices, updates,
                    )?);
                    continue;
                }
                if grammar == DefinitionGrammar::NatOnly
                    && bindings
                        .iter()
                        .any(|b| b.recursive.is_some() || !b.parameters.is_empty())
                {
                    return Err(refuse(view, tokens, range.start));
                }
                let bodies = bindings.iter().map(|b| b.value.clone()).collect::<Vec<_>>();
                tasks.push(Task::Close(bindings));
                tasks.push(Task::Value(body_start..range.end));
                tasks.extend(bodies.into_iter().rev().map(Task::Value));
            }
            Task::Close(bindings) => {
                let mut value = values.pop().expect("let continuation follows its values");
                for binding in bindings.into_iter().rev() {
                    let local_value = values.pop().expect("let value precedes its continuation");
                    // A binding by equations, or with a termination hint, is not read here.
                    if binding.equations || binding.termination.is_some() {
                        return Err(refuse(view, tokens, binding.name));
                    }
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
                    // The binder parser owns these domains and their child
                    // matches; leave every value/continuation splice untouched.
                    for parameter in &binding.parameters {
                        splices.retain(|start, _| !parameter.type_range.contains(start));
                    }
                    let parameters =
                        bounded_binder_syntax(leaves, view, tokens, binding.parameters, grammar)?;
                    let declaration = match binding.pattern {
                        // `letPatDecl := term pushNone optType " := " term` (`let ⟨a, b⟩ := p`).
                        Some(pattern) => Syntax::node(
                            parser_kind(&["Term", "letPatDecl"]),
                            vec![
                                bounded_term_spliced(
                                    leaves, view, tokens, pattern, grammar, splices, updates,
                                )?,
                                null_node(vec![]),
                                annotation,
                                leaves.leaf(binding.assignment)?,
                                local_value,
                            ],
                        ),
                        None => Syntax::node(
                            parser_kind(&["Term", "letIdDecl"]),
                            vec![
                                Syntax::node(
                                    parser_kind(&["Term", "letId"]),
                                    vec![leaves.leaf(binding.name)?],
                                ),
                                null_node(parameters),
                                annotation,
                                leaves.leaf(binding.assignment)?,
                                local_value,
                            ],
                        ),
                    };
                    // The binding's attributes, never dropped: the elaborator refuses them.
                    let attributes = match binding.attributes {
                        Some(at) => crate::command_scope::attributes::inline_syntax(
                            view, leaves, tokens, at,
                        )?,
                        None => null_node(vec![]),
                    };
                    value = local_binding_syntax(
                        leaves,
                        binding.keyword,
                        binding.recursive,
                        attributes,
                        declaration,
                        crate::empty_termination_suffix(),
                        binding.separator,
                        value,
                    )?;
                }
                values.push(value);
            }
            Task::Parentheses(start, end, count) => {
                let mut value = values.pop().expect("parenthesized local term");
                for offset in (0..count).rev() {
                    value = Syntax::node(
                        parser_kind(&["Term", "paren"]),
                        vec![
                            hygienic_lparen(leaves.leaf(start + offset)?),
                            value,
                            leaves.leaf(end - 1 - offset)?,
                        ],
                    );
                }
                values.push(value);
            }
        }
    }
    if values.len() != 1 {
        return Err(refuse(view, tokens, 0));
    }
    Ok(values.pop().expect("one local value"))
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

// Keep match construction's temporaries off the ordinary-term call stack:
// tactic arguments reenter this dispatcher while their enclosing term is live.
fn parse_planned(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
    equations: bool,
) -> Result<Syntax, NatDefinitionParseError> {
    if grammar == DefinitionGrammar::Scalar && is_symbol(tokens, range.start, "by") {
        let (proof, end) = proofs::parse(leaves, view, tokens, range.start, range.end)?;
        if end != range.end {
            return Err(refuse(view, tokens, end));
        }
        return Ok(proof);
    }
    // Tactic blocks own their pipes; their bounded arguments reenter here. A bare
    // pipe needs the planner only as a refutable do binding's failure branch, so it
    // counts only in a range that opens a `do`: `have n := 0; by first | a | b`
    // keeps its tactic alternatives for the proof parser.
    let opens_do = range.clone().any(|at| term_locals::word(tokens, at, "do"));
    if grammar == DefinitionGrammar::Scalar
        && !is_symbol(tokens, range.start, "by")
        && !is_symbol(tokens, range.start, "calc")
        && (equations
            || range.clone().any(|at| {
                is_symbol(tokens, at, "if")
                    || is_symbol(tokens, at, "bif")
                    || is_symbol(tokens, at, "match")
                    || is_symbol(tokens, at, "try")
                    || (opens_do && is_symbol(tokens, at, "|"))
                    || ((is_symbol(tokens, at, "fun") || is_symbol(tokens, at, "λ"))
                        && is_symbol(tokens, at + 1, "|"))
            }))
    {
        return parse_compound(leaves, view, tokens, range, grammar, equations);
    }
    let mut splices = Splices::new();
    let updates = record_terms::update_openers(tokens, range.clone());
    branch_value(leaves, view, tokens, range, grammar, &mut splices, &updates)
}

// Do not retain both match and conditional construction temporaries while a
// child range is parsed. Nesting is on the plan/work stacks; the native stack
// footprint is independent of the number and shape of source branches.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn build_conditional(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: ConditionalPlan,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<(), NatDefinitionParseError> {
    let then_at = plan.then_at.expect("planned then");
    if is_symbol(tokens, plan.start, "bif") {
        return build_bool_conditional(
            leaves, view, tokens, plan, grammar, splices, updates, then_at,
        );
    }

    let pattern_test = is_symbol(tokens, plan.start + 1, "let");
    let named = !pattern_test && is_symbol(tokens, plan.start + 2, ":");
    let binding = if named {
        null_node(vec![
            leaves.leaf(plan.start + 1)?,
            leaves.leaf(plan.start + 2)?,
        ])
    } else {
        null_node(vec![])
    };
    let condition = if pattern_test && !plan.statement {
        // Read with the branches below (`termIfLet`).
        Syntax::Missing
    } else if pattern_test {
        if_let::condition(leaves, view, tokens, &plan, grammar, splices, updates)?
    } else {
        let begin = plan.start + if named { 3 } else { 1 };
        let predicate = branch_value(
            leaves,
            view,
            tokens,
            begin..then_at,
            grammar,
            splices,
            updates,
        )?;
        if plan.statement {
            Syntax::node(
                parser_kind(&["Term", "doIfProp"]),
                vec![binding.clone(), predicate],
            )
        } else {
            predicate
        }
    };
    if plan.statement {
        let yes = bounded_do_sequence_spliced(
            leaves,
            view,
            tokens,
            then_at + 1..plan.else_at.unwrap_or(plan.end),
            grammar,
            splices,
            updates,
        )?;
        let otherwise = match plan.else_at {
            Some(else_at) => null_node(vec![
                leaves.leaf(else_at)?,
                bounded_do_sequence_spliced(
                    leaves,
                    view,
                    tokens,
                    else_at + 1..plan.end,
                    grammar,
                    splices,
                    updates,
                )?,
            ]),
            None => null_node(vec![]),
        };
        let syntax = statement_conditional(
            leaves, view, tokens, &plan, then_at, condition, yes, otherwise,
        )?;
        splices.insert(plan.start, (plan.end, syntax));
        return Ok(());
    }
    let else_at = plan.else_at.expect("ordinary conditional requires else");
    let yes = branch_value(
        leaves,
        view,
        tokens,
        then_at + 1..else_at,
        grammar,
        splices,
        updates,
    )?;
    let no = branch_value(
        leaves,
        view,
        tokens,
        else_at + 1..plan.end,
        grammar,
        splices,
        updates,
    )?;
    let syntax = term_conditional(
        leaves, view, tokens, &plan, grammar, splices, updates, condition, yes, no,
    )?;
    splices.insert(plan.start, (plan.end, syntax));
    Ok(())
}

/// A statement `if`'s `doIf` node, built once its child ranges are parsed so that their
/// construction temporaries are not live while a child range is parsed.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn statement_conditional(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: &ConditionalPlan,
    then_at: usize,
    condition: Syntax,
    yes: Syntax,
    otherwise: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    // `elseIf := atomic(group(withPosition("else " checkLineEq " if ")))`: an `if` right after
    // the `else` on its line, alone in its branch, is an else-if clause of this `if`, its own
    // clauses and `else` becoming this one's. On the next line it stays a nested `if`.
    let (else_ifs, otherwise) = match plan.else_at {
        Some(else_at)
            if is_symbol(tokens, else_at + 1, "if")
                && !later_line(view, tokens, else_at + 1, else_at) =>
        {
            else_if_clauses(leaves.leaf(else_at)?, otherwise)
        }
        _ => (Vec::new(), otherwise),
    };
    Ok(Syntax::node(
        parser_kind(&["Term", "doIf"]),
        vec![
            leaves.leaf(plan.start)?,
            condition,
            leaves.leaf(then_at)?,
            yes,
            null_node(else_ifs),
            otherwise,
        ],
    ))
}

/// A term `if`'s node, built once both branches are parsed (`termIfLet` reads its pattern and
/// value here).
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn term_conditional(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: &ConditionalPlan,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
    condition: Syntax,
    yes: Syntax,
    no: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    // The pin's `if` notations (`Init/Prelude.lean`): `termIfThenElse` and, with evidence
    // `if h : c`, `termDepIfThenElse`, whose name is a `binderIdent`; `if let p := e` is
    // `termIfLet` (`Init/Notation.lean`).
    let pattern_test = is_symbol(tokens, plan.start + 1, "let");
    let named = !pattern_test && is_symbol(tokens, plan.start + 2, ":");
    let then_at = plan.then_at.expect("planned then");
    let else_at = plan.else_at.expect("ordinary conditional requires else");
    Ok(if pattern_test {
        let (pattern, assignment, value) =
            if_let::term_parts(leaves, view, tokens, plan, grammar, splices, updates)?;
        Syntax::node(
            Name::from_components(["termIfLet"]),
            vec![
                leaves.leaf(plan.start)?,
                leaves.leaf(plan.start + 1)?,
                pattern,
                assignment,
                value,
                leaves.leaf(then_at)?,
                yes,
                leaves.leaf(else_at)?,
                no,
            ],
        )
    } else if named {
        Syntax::node(
            Name::from_components(["termDepIfThenElse"]),
            vec![
                leaves.leaf(plan.start)?,
                // `binderIdent := ident <|> hole`: `_` is the hole.
                Syntax::node(
                    Name::from_components(["Lean", "binderIdent"]),
                    vec![match leaves.leaf(plan.start + 1)? {
                        hole @ Syntax::Atom { .. } => {
                            Syntax::node(parser_kind(&["Term", "hole"]), vec![hole])
                        }
                        name => name,
                    }],
                ),
                leaves.leaf(plan.start + 2)?,
                condition,
                leaves.leaf(then_at)?,
                yes,
                leaves.leaf(else_at)?,
                no,
            ],
        )
    } else {
        Syntax::node(
            Name::from_components(["termIfThenElse"]),
            vec![
                leaves.leaf(plan.start)?,
                condition,
                leaves.leaf(then_at)?,
                yes,
                leaves.leaf(else_at)?,
                no,
            ],
        )
    })
}

/// `bif c then a else b` (`boolIfThenElse`, `Init/Notation.lean`, which expands to `cond c a b`):
/// no evidence binding and always an `else`.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn build_bool_conditional(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: ConditionalPlan,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
    then_at: usize,
) -> Result<(), NatDefinitionParseError> {
    let Some(else_at) = plan.else_at else {
        return Err(refuse(view, tokens, plan.end));
    };
    let mut parts = vec![leaves.leaf(plan.start)?];
    for (range, separator) in [
        (plan.start + 1..then_at, Some(then_at)),
        (then_at + 1..else_at, Some(else_at)),
        (else_at + 1..plan.end, None),
    ] {
        parts.push(branch_value(
            leaves, view, tokens, range, grammar, splices, updates,
        )?);
        if let Some(separator) = separator {
            parts.push(leaves.leaf(separator)?);
        }
    }
    splices.insert(
        plan.start,
        (
            plan.end,
            Syntax::node(Name::from_components(["boolIfThenElse"]), parts),
        ),
    );
    Ok(())
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn build_match(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
    equations: bool,
    plan: MatchPlan,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<Option<Syntax>, NatDefinitionParseError> {
    let with = plan.with.expect("validated match header");
    let equation_root = equations && plan.start == range.start;
    let mut discriminators = Vec::new();
    let discriminant_columns = if equation_root || plan.function || plan.catch {
        Vec::new()
    } else {
        columns(tokens, plan.start + 1..with)
    };
    let arity = if plan.catch {
        1
    } else if equation_root || plan.function {
        let first = plan.alternatives.first().expect("validated equation row");
        let first_group_end = first
            .shared
            .first()
            .copied()
            .unwrap_or_else(|| first.arrow.expect("validated arrow"));
        columns(tokens, first.pipe + 1..first_group_end).len()
    } else {
        discriminant_columns.len()
    };
    // Inside a quotation, the pin reads an antiquotation with no kind straight after `match`
    // (`match $c with`) as the optional `(generalizing := …)` parameter's, and then misses the
    // discriminant: a parse error there, so a refusal here. `$c:term` is a discriminant.
    if let Some((first, _)) = discriminant_columns.first()
        && crate::quotations::inside()
        && is_symbol(tokens, first.start, "$")
        && !(first.start + 3 < first.end && is_symbol(tokens, first.start + 2, ":"))
    {
        return Err(refuse(view, tokens, first.start));
    }
    for (mut range, comma) in discriminant_columns {
        // Preserve the pinned optional binderIdent-colon production instead
        // of misreading `h : e` as a term ascription. Parenthesized
        // ascriptions start with `(` and remain ordinary discriminants.
        let binding = if range.start + 1 < range.end && is_symbol(tokens, range.start + 1, ":") {
            let binder = leaves.leaf(range.start)?;
            if !matches!(&binder, Syntax::Ident { .. })
                && !matches!(&binder, Syntax::Atom { val, .. } if val == "_")
            {
                return Err(refuse(view, tokens, range.start));
            }
            let colon = leaves.leaf(range.start + 1)?;
            range.start += 2;
            if range.is_empty() {
                return Err(refuse(view, tokens, range.start - 1));
            }
            null_node(vec![binder, colon])
        } else {
            null_node(vec![])
        };
        let monadic = plan.statement
            && (is_symbol(tokens, range.start, "←") || is_symbol(tokens, range.start, "<-"));
        let discriminator = if monadic {
            // General mixed nested actions need a separate evaluation-order
            // planner. This bounded path owns one top-level action only.
            if arity != 1 || range.start + 1 >= range.end {
                return Err(refuse(view, tokens, range.start));
            }
            let arrow = leaves.leaf(range.start)?;
            let action = bounded_term_spliced(
                leaves,
                view,
                tokens,
                range.start + 1..range.end,
                grammar,
                splices,
                updates,
            )?;
            Syntax::node(
                parser_kind(&["Term", "nestedAction"]),
                vec![
                    arrow,
                    Syntax::node(parser_kind(&["Term", "doExpr"]), vec![action]),
                ],
            )
        } else {
            bounded_term_spliced(leaves, view, tokens, range, grammar, splices, updates)?
        };
        discriminators.push(Syntax::node(
            parser_kind(&["Term", "matchDiscr"]),
            vec![binding, discriminator],
        ));
        if let Some(comma) = comma {
            discriminators.push(leaves.leaf(comma)?);
        }
    }
    let mut alternatives = Vec::new();
    for alt in plan.alternatives {
        let arrow = alt.arrow.expect("validated alternative");
        let mut groups = Vec::new();
        let mut group_start = alt.pipe + 1;
        for separator in alt.shared.iter().copied().chain(std::iter::once(arrow)) {
            let pattern_columns = columns(tokens, group_start..separator);
            if pattern_columns.len() != arity {
                return Err(refuse(view, tokens, group_start - 1));
            }
            let mut patterns = Vec::new();
            for (range, comma) in pattern_columns {
                patterns.push(pattern(leaves, view, tokens, range)?);
                if let Some(comma) = comma {
                    patterns.push(leaves.leaf(comma)?);
                }
            }
            if !groups.is_empty() {
                groups.push(leaves.leaf(group_start - 1)?);
            }
            groups.push(null_node(patterns));
            group_start = separator + 1;
        }
        let rhs = if plan.statement {
            bounded_do_sequence_spliced(
                leaves,
                view,
                tokens,
                arrow + 1..alt.end,
                grammar,
                splices,
                updates,
            )?
        } else {
            branch_value(
                leaves,
                view,
                tokens,
                arrow + 1..alt.end,
                grammar,
                splices,
                updates,
            )?
        };
        alternatives.push(Syntax::node(
            parser_kind(&["Term", "matchAlt"]),
            vec![
                leaves.leaf(alt.pipe)?,
                null_node(groups),
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
        // The rows reach the end of the definition: tokens after a row the planner closed early
        // are refused, never dropped.
        if plan.end != range.end {
            return Err(refuse(view, tokens, plan.end));
        }
        if !splices.is_empty() {
            return Err(refuse(view, tokens, range.start));
        }
        return Ok(Some(alternatives));
    }
    let syntax = if plan.catch {
        Syntax::node(
            parser_kind(&["Term", "doCatchMatch"]),
            vec![leaves.leaf(plan.start)?, alternatives],
        )
    } else if plan.function {
        Syntax::node(
            parser_kind(&["Term", "fun"]),
            vec![leaves.leaf(plan.start)?, alternatives],
        )
    } else if plan.statement {
        Syntax::node(
            parser_kind(&["Term", "doMatch"]),
            vec![
                leaves.leaf(plan.start)?,
                null_node(vec![]), // optional dependent parameter
                null_node(vec![]), // optional generalizing parameter
                null_node(vec![]), // optional motive
                null_node(discriminators),
                leaves.leaf(with)?,
                alternatives,
            ],
        )
    } else {
        Syntax::node(
            parser_kind(&["Term", "match"]),
            vec![
                leaves.leaf(plan.start)?,
                null_node(vec![]),
                null_node(vec![]),
                null_node(discriminators),
                leaves.leaf(with)?,
                alternatives,
            ],
        )
    };
    splices.insert(plan.start, (plan.end, syntax));
    Ok(None)
}

fn parse_compound(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    grammar: DefinitionGrammar,
    equations: bool,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut splices = Splices::new();
    let updates: HashSet<_> = record_terms::update_openers(tokens, range.clone());
    for planned in plan(view, tokens, range.clone(), equations)? {
        match planned {
            Plan::Try(plan) => {
                exceptions::build(leaves, view, tokens, plan, grammar, &mut splices, &updates)?;
            }
            Plan::Fallback(plan) => {
                fallback::build(leaves, view, tokens, plan, grammar, &mut splices, &updates)?;
            }
            Plan::Conditional(plan) => {
                build_conditional(leaves, view, tokens, plan, grammar, &mut splices, &updates)?;
            }
            Plan::Match(plan) => {
                if let Some(equations) = build_match(
                    leaves,
                    view,
                    tokens,
                    range.clone(),
                    grammar,
                    equations,
                    plan,
                    &mut splices,
                    &updates,
                )? {
                    return Ok(equations);
                }
            }
        }
    }
    let result = branch_value(leaves, view, tokens, range, grammar, &mut splices, &updates)?;
    if !splices.is_empty() {
        return Err(refuse(view, tokens, 0));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn equation_rows_never_drop_the_tokens_after_a_closed_row() {
        // A `;` closes a row whose value is not a proof; what follows is refused (the pin
        // reports an unexpected token there), never dropped.
        assert!(
            parse_definition("def g1 : Nat → Nat\n  | 0 => 0; 1\n  | _ => 1".as_bytes()).is_err()
        );
        // After a `by` anywhere in the row, the `;` is the tactic sequence's.
        let source = "def cs3 : Nat → Nat\n  | 0 => 0\n  | n + 1 =>\n    calc\n      n + 1 = n + 1 := by skip; rfl\n";
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
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
        ] {
            assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
        }
        // An ascribed pattern is the pin's `Term.typeAscription`.
        assert!(parse_definition(b"def f := match b with | .some (x : Nat) => x").is_ok());
    }
    #[test]
    fn deeply_nested_matches_parse_without_host_recursion() {
        std::thread::Builder::new()
            .name("deeply_nested_matches_parse_without_host_recursion".to_string())
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
            .name("deeply_nested_pattern_groups_fit_a_small_stack".to_string())
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
            .name("nested_rhs_matches_in_equations_use_a_heap_plan".to_string())
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

#[cfg(test)]
mod pattern_function_tests {
    use super::*;
    #[test]
    fn original_function_pipes_comments_and_scopes_round_trip() {
        for source in [
            "def f : Bool -> Nat := fun | true => 7 | false => 9",
            "def f : Bool -> Nat := λ | true => 7 | false => 9",
            "def f : Nat := apply (fun | .none => 0 | .some x => x) value",
            "def f : Bool -> Bool -> Nat := fun | true, _ => 1 | _, _ => 0",
            "-- before\r\ndef f : Bool -> Nat := fun\r\n | true /- pattern -/ => 7 -- result\r\n | false => 9\r\n",
            "def f : Bool -> Nat := fun\n | true => by\n   have h : Nat := 7\n   exact h\n | false => 0",
            "def f : Bool -> Nat\n | true => (fun | true => 1 | false => 2) true\n | false => 0",
            "def f : Nat := let g : Bool -> Nat := fun | true => 1 | false => 0; g true",
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
    fn malformed_function_equations_cannot_drop_leaves() {
        for source in [
            "def f := fun |",
            "def f := fun | true =>",
            "def f := fun | true 7",
            "def f := fun | => 1",
            "def f := fun | true => 1 | false, true => 2",
            "def f := (fun | true => 1 | false => 2",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn nested_pattern_functions_use_a_heap_plan() {
        std::thread::Builder::new()
            .name("nested_pattern_functions_use_a_heap_plan".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                let source = format!(
                    "def f := {}0{}",
                    "(fun | true => ".repeat(1000),
                    " | false => 1)".repeat(1000)
                );
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod literal_pattern_tests {
    use super::*;
    #[test]
    fn literal_tokens_keep_original_spelling_and_trivia() {
        for source in [
            "def f : Nat -> Nat | 0x10 => 1 | _ => 2",
            "-- before\r\ndef f : Nat -> Nat\r\n  | 0 /- zero -/ => 7\r\n  | .succ n => n\r\n",
            r##"def f : String -> Nat | r#"\x61"# => 1 | "a" => 2 | _ => 3"##,
            "def f : Nat := (fun | 1, true => 7 | _, _ => 9) 1 true",
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
    fn literals_cannot_be_applied_as_pattern_constructors() {
        for source in [
            "def f : Nat -> Nat | 0 x => 1 | _ => 2",
            "def f : Nat -> Nat | .0 => 1 | _ => 2",
            "def f : String -> Nat | \"a\" x => 1 | _ => 2",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn grouped_literal_patterns_are_heap_parsed() {
        std::thread::Builder::new()
            .name("grouped_literal_patterns_are_heap_parsed".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
            let source = format!("def f : Nat -> Nat | {}340282366920938463463374607431768211456{} => 7 | _ => 9", "(".repeat(1000), ")".repeat(1000));
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        }).unwrap().join().unwrap();
    }
}

#[cfg(test)]
mod conditional_tests {
    use super::*;
    #[test]
    fn named_proposition_conditions_preserve_evidence_and_branch_boundaries() {
        for source in [
            "def f (p : Prop) [Decidable p] : Nat := if /- evidence -/ h : p then 1 else 2",
            "theorem f (p : Prop) [Decidable p] (hp : p) : p :=\r\n  if h : p then h else hp\r\n",
            "theorem f (p : Prop) [Decidable p] (hp : p) : p := by\n  refine if h : p then ?_ else ?_\n  · exact h\n  · exact hp\n",
        ] {
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn conditionals_roundtrip_comments_and_statement_boundaries() {
        for source in [
            "def f (b : Bool) : Nat := if /- condition -/ b then 1 else 2",
            "def f (b : Bool) : Nat :=\r\n  if b then\r\n    1\r\n  else\r\n    2\r\n",
            "def f : Nat := by\n let n := if true then 1 else 2\n exact n\n",
            "def f : Nat := if true then let n := 1; n else let n := 2; n",
            "def f : Nat := if true then match false with | true => 1 | false => 2 else 3",
            "def f : Nat := if h : true then 1 else 2",
        ] {
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn malformed_conditional_boundaries_refuse() {
        for body in [
            "if then 1 else 2",
            "if true then else 2",
            "if true then 1 else",
            "if true then 1",
            "if true else 1",
            "if true then 1 else 2 else 3",
            "if true then if false then 1 else 2",
        ] {
            let source = format!("def f : Nat := {body}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
    #[test]
    fn deeply_nested_conditionals_use_heap_plans() {
        std::thread::Builder::new()
            .name("deeply_nested_conditionals_use_heap_plans".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                let source = format!(
                    "def f : Nat := {}0{}",
                    "if true then ".repeat(1000),
                    " else 1".repeat(1000)
                );
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
