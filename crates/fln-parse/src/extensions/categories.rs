//! Native source-category Pratt parsing. The descriptors, not a hard-coded DSL,
//! determine leading/trailing nodes, operand precedences and syntax kinds.
//! Anchors: Parser.Basic.prattParser/longestMatchFn and Parser.Extension.categoryParserFnImpl.
use super::*;

#[derive(Default)]
struct Work {
    nesting: usize,
    steps: usize,
    exhausted: bool,
}
thread_local! {
    static WORK: RefCell<Work> = RefCell::new(Work::default());
}
struct EnteredCategory;
impl EnteredCategory {
    fn enter() -> Option<Self> {
        WORK.with(|work| {
            let mut work = work.borrow_mut();
            if work.nesting == 0 {
                *work = Work::default();
            }
            if work.nesting >= MAX_DESCR_DEPTH || work.exhausted {
                work.exhausted = true;
                return None;
            }
            work.nesting += 1;
            Some(Self)
        })
    }
}
impl Drop for EnteredCategory {
    fn drop(&mut self) {
        WORK.with(|work| work.borrow_mut().nesting -= 1);
    }
}
/// All candidate descriptors share one work budget, including reentry through
/// builtin term parsing. Exhaustion poisons the entire choice, not just the
/// expensive candidate: otherwise an unexamined longer parse could be missed.
pub(super) fn stop() {
    WORK.with(|work| {
        let mut work = work.borrow_mut();
        if work.nesting != 0 {
            work.exhausted = true;
        }
    });
}

pub(super) fn tick() -> bool {
    WORK.with(|work| {
        let mut work = work.borrow_mut();
        if work.nesting == 0 {
            return true;
        }
        if work.steps >= MAX_TEMPLATE_NODES {
            work.exhausted = true;
        } else {
            work.steps += 1;
        }
        !work.exhausted
    })
}

struct Candidate {
    syntax: Syntax,
    next: usize,
    precedence: u32,
    priority: u32,
    tied: bool,
}
impl Candidate {
    fn retain(best: &mut Option<Self>, candidate: Self) {
        match best {
            Some(previous)
                if (previous.next, previous.priority) > (candidate.next, candidate.priority) => {}
            Some(previous)
                if (previous.next, previous.priority) == (candidate.next, candidate.priority) =>
            {
                previous.tied = true;
            }
            _ => *best = Some(candidate),
        }
    }
}

impl Run<'_> {
    pub(super) fn category(
        &self,
        category: &Name,
        precedence: u32,
        at: usize,
        end: usize,
        follow: &Follow,
        depth: usize,
    ) -> Parsed {
        if depth > MAX_DESCR_DEPTH {
            stop();
            return None;
        }
        if at >= end {
            return None;
        }
        let _entered = EnteredCategory::enter()?;
        let grammar = active()?;
        if !grammar.source_categories.contains(category) {
            return None;
        }
        let declarations = grammar
            .category_decls
            .get(category)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let mut best = crate::quotations::antiquotation(
            self.leaves,
            self.view,
            self.tokens,
            at,
            end,
            crate::quotations::Position::Category(category.clone()),
        )
        .ok()
        .flatten()
        .map(|(syntax, next)| Candidate {
            syntax,
            next,
            precedence: MAX_PREC,
            priority: DEFAULT_PRIORITY,
            tied: false,
        });
        if best.is_none() {
            for &index in declarations {
                let declaration = &grammar.decls[index];
                if !tick() {
                    return None;
                }
                if !declaration.leading || declaration.category.as_ref() != Some(category) {
                    continue;
                }
                let Descr::Node { prec, .. } = &declaration.descr else {
                    continue;
                };
                if *prec < precedence {
                    continue;
                }
                let starts = heads(&declaration.descr, 0);
                if !starts.is_empty() && !self.text(at).is_some_and(|head| starts.contains(&head)) {
                    continue;
                }
                if let Some((items, next)) =
                    self.parse(&declaration.descr, at, end, follow, depth + 1)
                    && next > at
                    && let [syntax] = items.as_slice()
                {
                    Candidate::retain(
                        &mut best,
                        Candidate {
                            syntax: syntax.clone(),
                            next,
                            precedence: *prec,
                            priority: declaration.priority,
                            tied: false,
                        },
                    );
                }
            }
        }
        let mut current = best?;
        if current.tied {
            return None;
        }
        loop {
            let mut best = None;
            for &index in declarations {
                let declaration = &grammar.decls[index];
                if !tick() {
                    return None;
                }
                if declaration.leading || declaration.category.as_ref() != Some(category) {
                    continue;
                }
                let Descr::TrailingNode {
                    kind,
                    prec,
                    lhs_prec,
                    body,
                } = &declaration.descr
                else {
                    continue;
                };
                if *prec < precedence || current.precedence < *lhs_prec {
                    continue;
                }
                let starts = heads(body, 0);
                if !starts.is_empty()
                    && !self
                        .text(current.next)
                        .is_some_and(|head| starts.contains(&head))
                {
                    continue;
                }
                if let Some((items, next)) = self.parse(body, current.next, end, follow, depth + 1)
                    && next > current.next
                {
                    let args = std::iter::once(current.syntax.clone())
                        .chain(items)
                        .collect();
                    Candidate::retain(
                        &mut best,
                        Candidate {
                            syntax: Syntax::node(kind.clone(), args),
                            next,
                            precedence: *prec,
                            priority: declaration.priority,
                            tied: false,
                        },
                    );
                }
            }
            match best {
                Some(next) if !next.tied => current = next,
                Some(_) => return None,
                None => break,
            }
        }
        // A failing recursive candidate cannot reset or hide the shared budget.
        if WORK.with(|work| work.borrow().exhausted) {
            return None;
        }
        Some((vec![current.syntax], current.next))
    }
}

/// The generated quotation token uses the category's string suffix. Refuse a
/// suffix collision rather than choosing a namespace by map iteration order.
pub(crate) fn category_for_quotation(symbol: &str) -> Option<Name> {
    let suffix = symbol.strip_prefix("`(")?.strip_suffix('|')?;
    let grammar = active()?;
    let mut matches = grammar
        .source_categories
        .iter()
        .filter(|category| matches!(category.leaf_view(), LeafView::Str(name) if name == suffix));
    let category = matches.next()?.clone();
    if matches.next().is_some() {
        None
    } else {
        Some(category)
    }
}

pub(crate) fn parse_category_quotation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    category: &Name,
) -> Option<Syntax> {
    let run = Run {
        leaves,
        view,
        tokens,
    };
    let (items, next) = run.category(category, 0, range.start, range.end, &Follow::End, 0)?;
    let [syntax] = items.as_slice() else {
        return None;
    };
    (next == range.end).then(|| syntax.clone())
}
