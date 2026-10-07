//! Exception regions on the compound parser's heap plan. Each body is an
//! ordinary do sequence, and every original keyword, binder and delimiter is
//! retained in the pinned Parser.Do tree. No synthesized source is re-lexed.
use super::*;

struct Catch {
    keyword: usize,
    pattern: bool,
    binder: usize,
    colon: Option<usize>,
    arrow: usize,
    end: usize,
}

pub(super) struct TryPlan {
    pub(super) start: usize,
    depth: usize,
    baseline: usize,
    body_end: usize,
    catches: Vec<Catch>,
    finally: Option<(usize, usize)>,
    end: usize,
}

impl TryPlan {
    /// Pattern handlers let the match planner own their arm scopes. Named
    /// handlers and protected/finalizer sequences are owned by the try itself.
    fn body_owner(&self) -> usize {
        if self.finally.is_none()
            && let Some(catch) = self.catches.last()
            && catch.pattern
        {
            catch.keyword
        } else {
            self.start
        }
    }
    fn close_body(&mut self, end: usize) {
        if let Some((_, finish)) = &mut self.finally {
            *finish = end;
        } else if let Some(handler) = self.catches.last_mut() {
            handler.end = end;
        } else {
            self.body_end = end;
        }
        self.end = end;
    }
    fn accepts(&self, view: &SourceView, tokens: &[LexedToken], at: usize, depth: usize) -> bool {
        self.depth == depth
            && self.finally.is_none()
            && (!later_line(view, tokens, at, self.start)
                || column(view, tokens, at) >= self.baseline)
    }
}

#[derive(Default)]
pub(super) struct Planner {
    active: Vec<TryPlan>,
}

impl Planner {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn open(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        depth: usize,
        baseline: usize,
        scopes: &mut DoScopes,
        end: usize,
    ) -> Result<(), NatDefinitionParseError> {
        check_body(view, tokens, at, at + 1, baseline, end)?;
        scopes.open(view, tokens, at, depth, Some(at), end)?;
        self.active.push(TryPlan {
            start: at,
            depth,
            baseline,
            body_end: end,
            catches: Vec::new(),
            finally: None,
            end,
        });
        Ok(())
    }

    pub(super) fn in_header(&self, at: usize) -> bool {
        self.active
            .last()
            .and_then(|p| p.catches.last())
            .is_some_and(|c| !c.pattern && at > c.keyword && at < c.arrow)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn before(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        depth: usize,
        scopes: &mut DoScopes,
        matches: &mut Vec<MatchPlan>,
        done: &mut Vec<Plan>,
        end: usize,
    ) -> Result<(), NatDefinitionParseError> {
        let catch = is_symbol(tokens, at, "catch");
        let finally = is_symbol(tokens, at, "finally");
        while self.active.last().is_some_and(|p| {
            scopes.ended(p.body_owner())
                && !(is_symbol(tokens, at, "|")
                    && matches
                        .iter()
                        .rev()
                        .find(|m| m.start == p.body_owner())
                        .is_some_and(|m| {
                            m.catch
                                && m.depth == depth
                                && m.alternatives.first().is_none_or(|first| {
                                    !later_line(view, tokens, at, first.pipe)
                                        || column(view, tokens, at)
                                            >= column(view, tokens, first.pipe)
                                })
                        }))
                && !((catch || finally) && p.accepts(view, tokens, at, depth))
        }) {
            let mut p = self.active.pop().expect("ended exception region");
            scopes.closed(p.start);
            p.close_body(at);
            done.push(Plan::Try(p));
        }
        if !catch && !finally {
            return Ok(());
        }
        let Some(p) = self.active.last_mut() else {
            return Err(refuse(view, tokens, at));
        };
        if !p.accepts(view, tokens, at, depth) || !scopes.end_exception_body(p.body_owner()) {
            return Err(refuse(view, tokens, at));
        }
        p.close_body(at);
        // A new clause ends matches in the previous clause, not a match that
        // contains this try. Close these before opening a catch-pattern match.
        while matches
            .last()
            .is_some_and(|m| m.start > p.start && m.depth == depth)
        {
            scopes.closed(matches.last().expect("completed clause match").start);
            close(view, tokens, matches, done, at)?;
        }
        if catch && is_symbol(tokens, at + 1, "|") {
            p.catches.push(Catch {
                keyword: at,
                pattern: true,
                binder: at + 1,
                colon: None,
                arrow: at,
                end,
            });
            matches.push(MatchPlan {
                statement: true,
                function: false,
                catch: true,
                baseline: p.baseline,
                start: at,
                depth,
                with: Some(at),
                alternatives: Vec::new(),
                end,
            });
            return Ok(());
        }
        let (introducer, body) = if catch {
            let binder = at + 1;
            if binder >= end
                || !(matches!(&tokens[binder].kind, TokenKind::Ident(name)
                if !name.is_anonymous() && name.parent().is_anonymous())
                    || is_symbol(tokens, binder, "_"))
            {
                return Err(refuse(view, tokens, binder));
            }
            let colon = is_symbol(tokens, binder + 1, ":").then_some(binder + 1);
            let mut arrow = binder + 1 + usize::from(colon.is_some());
            let begin = arrow;
            let mut delimiters = Vec::new();
            while arrow < end {
                if delimiters.is_empty()
                    && (is_symbol(tokens, arrow, "=>") || is_symbol(tokens, arrow, "↦"))
                {
                    break;
                }
                if colon.is_none() {
                    return Err(refuse(view, tokens, arrow));
                }
                if let TokenKind::Symbol(symbol) = &tokens[arrow].kind {
                    match symbol.as_str() {
                        "(" => delimiters.push(")"),
                        "[" => delimiters.push("]"),
                        "{" | ".{" => delimiters.push("}"),
                        "⦃" => delimiters.push("⦄"),
                        ")" | "]" | "}" | "⦄" => {
                            if delimiters.pop() != Some(symbol.as_str()) {
                                return Err(refuse(view, tokens, arrow));
                            }
                        }
                        ";" | "catch" | "finally" if delimiters.is_empty() => {
                            return Err(refuse(view, tokens, arrow));
                        }
                        _ => {}
                    }
                }
                arrow += 1;
            }
            if arrow >= end || colon.is_some() && arrow == begin {
                return Err(refuse(view, tokens, arrow));
            }
            p.catches.push(Catch {
                keyword: at,
                pattern: false,
                binder,
                colon,
                arrow,
                end,
            });
            (arrow, arrow + 1)
        } else {
            p.finally = Some((at, end));
            (at, at + 1)
        };
        check_body(view, tokens, at, body, p.baseline, end)?;
        scopes.open_at(view, tokens, introducer, body, depth, Some(p.start), end)?;
        Ok(())
    }

    pub(super) fn finish(&mut self, done: &mut Vec<Plan>, end: usize) {
        while let Some(mut p) = self.active.pop() {
            p.close_body(end);
            done.push(Plan::Try(p));
        }
    }
}

fn check_body(
    view: &SourceView,
    tokens: &[LexedToken],
    keyword: usize,
    body: usize,
    baseline: usize,
    end: usize,
) -> Result<(), NatDefinitionParseError> {
    if body >= end
        || (!is_symbol(tokens, body, "{")
            && later_line(view, tokens, body, keyword)
            && column(view, tokens, body) <= baseline)
    {
        return Err(refuse(view, tokens, body));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    p: TryPlan,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<(), NatDefinitionParseError> {
    let body = bounded_do_sequence_spliced(
        leaves,
        view,
        tokens,
        p.start + 1..p.body_end,
        grammar,
        splices,
        updates,
    )?;
    let mut catches = Vec::new();
    for c in p.catches {
        if c.pattern {
            let (end, handler) = splices
                .remove(&c.keyword)
                .ok_or_else(|| refuse(view, tokens, c.keyword))?;
            if end != c.end || handler.kind() != Some(&parser_kind(&["Term", "doCatchMatch"])) {
                return Err(refuse(view, tokens, c.keyword));
            }
            catches.push(handler);
            continue;
        }
        let annotation = if let Some(colon) = c.colon {
            null_node(vec![
                leaves.leaf(colon)?,
                branch_value(
                    leaves,
                    view,
                    tokens,
                    colon + 1..c.arrow,
                    grammar,
                    splices,
                    updates,
                )?,
            ])
        } else {
            null_node(vec![])
        };
        let binder = if is_symbol(tokens, c.binder, "_") {
            Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(c.binder)?])
        } else {
            leaves.leaf(c.binder)?
        };
        catches.push(Syntax::node(
            parser_kind(&["Term", "doCatch"]),
            vec![
                leaves.leaf(c.keyword)?,
                binder,
                annotation,
                leaves.leaf(c.arrow)?,
                bounded_do_sequence_spliced(
                    leaves,
                    view,
                    tokens,
                    c.arrow + 1..c.end,
                    grammar,
                    splices,
                    updates,
                )?,
            ],
        ));
    }
    let finally = match p.finally {
        None => null_node(vec![]),
        Some((at, end)) => null_node(vec![Syntax::node(
            parser_kind(&["Term", "doFinally"]),
            vec![
                leaves.leaf(at)?,
                bounded_do_sequence_spliced(
                    leaves,
                    view,
                    tokens,
                    at + 1..end,
                    grammar,
                    splices,
                    updates,
                )?,
            ],
        )]),
    };
    splices.insert(
        p.start,
        (
            p.end,
            Syntax::node(
                parser_kind(&["Term", "doTry"]),
                vec![leaves.leaf(p.start)?, body, null_node(catches), finally],
            ),
        ),
    );
    Ok(())
}
