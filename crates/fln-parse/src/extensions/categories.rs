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

/// Keep builtin command reentry in the same work and depth allowance as
/// descriptor categories. An exhausted candidate cannot become a fallback.
pub(super) fn bounded<T>(parse: impl FnOnce() -> Option<T>) -> Option<T> {
    let _entered = EnteredCategory::enter()?;
    let result = parse()?;
    if WORK.with(|work| work.borrow().exhausted) {
        None
    } else {
        Some(result)
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

/// Every trailing reading owns its left operand. Charge the whole copy before
/// allocating it: repeated ambiguous operators otherwise double the previous
/// choice tree while visiting only a constant number of parser descriptions.
fn clone_operand(syntax: &Syntax) -> Option<Syntax> {
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if !tick() {
            return None;
        }
        if let Syntax::Node { args, .. } = syntax {
            pending.extend(args);
        }
    }
    Some(syntax.clone())
}

/// Run reports successful endpoints, but not failed parser positions. A failed
/// same-head candidate may have consumed farther than a success and therefore
/// win at the pin. Do not introduce a newly accepted choice without knowing
/// that every competing candidate was scored. Check nested choices too, and
/// failures of trailing parsers after an earlier leading choice.
fn check_choice_progress(syntax: &Syntax, failed_candidate: bool) -> Option<()> {
    if !failed_candidate {
        return Some(());
    }
    let choice = Name::from_components(["choice"]);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if !tick() {
            return None;
        }
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == choice {
                return None;
            }
            pending.extend(args);
        }
    }
    Some(())
}

struct Candidate {
    readings: Vec<Syntax>,
    next: usize,
    precedence: u32,
    priority: u32,
}
impl Candidate {
    fn retain(best: &mut Option<Self>, candidate: Self) {
        match best {
            Some(previous)
                if (previous.next, previous.priority) > (candidate.next, candidate.priority) => {}
            Some(previous)
                if (previous.next, previous.priority) == (candidate.next, candidate.priority) =>
            {
                // `longestMatchStep` retains every equally successful reading.
                // A following operator must be legal for all of them, so the
                // choice inherits the minimum precedence, as at the pin.
                previous.readings.extend(candidate.readings);
                previous.precedence = previous.precedence.min(candidate.precedence);
            }
            _ => *best = Some(candidate),
        }
    }

    fn into_syntax(mut self) -> Syntax {
        if self.readings.len() == 1 {
            self.readings
                .pop()
                .expect("a successful parser has a reading")
        } else {
            Syntax::node(Name::from_components(["choice"]), self.readings)
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
            readings: vec![syntax],
            next,
            precedence: MAX_PREC,
            priority: DEFAULT_PRIORITY,
        });
        // Keep earlier failures visible if a later trailing parser adds a choice.
        let mut failed_candidate = false;
        if best.is_none() {
            // The pin conses parser registrations onto its tables. Equal
            // readings therefore occur newest first, including local/scoped
            // registrations and productions replayed from imports.
            for &index in declarations.iter().rev() {
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
                if let Some((mut items, next)) =
                    self.parse(&declaration.descr, at, end, follow, depth + 1)
                    && next > at
                    && items.len() == 1
                {
                    Candidate::retain(
                        &mut best,
                        Candidate {
                            readings: vec![items.pop().expect("one parser reading")],
                            next,
                            precedence: *prec,
                            priority: declaration.priority,
                        },
                    );
                } else {
                    failed_candidate = true;
                }
            }
        }
        let current = best?;
        let mut next = current.next;
        let mut current_precedence = current.precedence;
        let mut syntax = current.into_syntax();
        check_choice_progress(&syntax, failed_candidate)?;
        loop {
            let mut best = None;
            for &index in declarations.iter().rev() {
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
                if *prec < precedence || current_precedence < *lhs_prec {
                    continue;
                }
                let starts = heads(body, 0);
                if !starts.is_empty() && !self.text(next).is_some_and(|head| starts.contains(&head))
                {
                    continue;
                }
                if let Some((items, parsed_end)) = self.parse(body, next, end, follow, depth + 1)
                    && parsed_end > next
                {
                    let args = std::iter::once(clone_operand(&syntax)?)
                        .chain(items)
                        .collect();
                    Candidate::retain(
                        &mut best,
                        Candidate {
                            readings: vec![Syntax::node(kind.clone(), args)],
                            next: parsed_end,
                            precedence: *prec,
                            priority: declaration.priority,
                        },
                    );
                } else {
                    failed_candidate = true;
                }
            }
            let Some(candidate) = best else {
                check_choice_progress(&syntax, failed_candidate)?;
                break;
            };
            next = candidate.next;
            current_precedence = candidate.precedence;
            syntax = candidate.into_syntax();
            check_choice_progress(&syntax, failed_candidate)?;
        }
        // A failing recursive candidate cannot reset or hide the shared budget.
        if WORK.with(|work| work.borrow().exhausted) {
            return None;
        }
        Some((vec![syntax], next))
    }
}

/// The generated quotation token uses the category's string suffix. Refuse a
/// suffix collision rather than choosing a namespace by map iteration order.
pub(crate) fn category_for_quotation(symbol: &str) -> Option<Name> {
    let suffix = symbol.strip_prefix("`(")?.strip_suffix('|')?;
    let grammar = active()?;
    let mut matches = grammar
        .source_quotation_categories
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
