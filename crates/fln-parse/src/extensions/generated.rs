//! Production bridge for registered builtin parser aliases that the bounded
//! token parser cannot interpret. Whole descriptors and competing declarations
//! run together, so ordinary backtracking follows Lean's combinators. Resource
//! stops and recovered errors cannot be hidden by a successful alternative.
use super::*;
use crate::DefinitionParseError;
use crate::builtin_interpreter::{
    DEFAULT_STEP_BUDGET, ParserFailure, ParserInput, ParserResourceLimit,
    reference_builtin_interpreter,
};

const MAX_ALIAS_STEPS: usize = DEFAULT_STEP_BUDGET;

struct Work {
    nesting: usize,
    remaining: usize,
    error: Option<DefinitionParseError>,
    mismatch: Option<DefinitionParseError>,
    positions: Vec<Option<usize>>,
}

impl Default for Work {
    fn default() -> Self {
        Self {
            nesting: 0,
            remaining: MAX_ALIAS_STEPS,
            error: None,
            mismatch: None,
            positions: Vec::new(),
        }
    }
}

thread_local! {
    static WORK: RefCell<Work> = RefCell::new(Work::default());
}

struct Entered;
impl Drop for Entered {
    fn drop(&mut self) {
        WORK.with(|work| work.borrow_mut().nesting -= 1);
    }
}

/// Keep exhaustion and recovered diagnostics sticky through the hand parser's
/// alternatives. A successful cheap candidate cannot hide an incomplete run.
pub(crate) fn with_parse_errors<T>(
    parse: impl FnOnce() -> Result<T, DefinitionParseError>,
) -> Result<T, DefinitionParseError> {
    WORK.with(|work| {
        let mut work = work.borrow_mut();
        if work.nesting == 0 {
            *work = Work::default();
        }
        work.nesting += 1;
    });
    let _entered = Entered;
    let result = parse();
    match WORK.with(|work| work.borrow().error.clone()) {
        Some(error) => Err(error),
        None => match result {
            Err(error) => Err(WORK
                .with(|work| work.borrow().mismatch.clone())
                .unwrap_or(error)),
            success => success,
        },
    }
}

struct Position;
impl Drop for Position {
    fn drop(&mut self) {
        WORK.with(|work| {
            work.borrow_mut().positions.pop();
        });
    }
}

pub(super) fn with_position<T>(position: Option<usize>, parse: impl FnOnce() -> T) -> T {
    WORK.with(|work| work.borrow_mut().positions.push(position));
    let _position = Position;
    parse()
}

pub(super) fn remaining_steps() -> usize {
    WORK.with(|work| {
        let work = work.borrow();
        if work.nesting > 0 {
            work.remaining
        } else {
            DEFAULT_STEP_BUDGET
        }
    })
}

pub(super) fn charge_steps(steps: usize) {
    WORK.with(|work| {
        let mut work = work.borrow_mut();
        if work.nesting > 0 {
            work.remaining = work.remaining.saturating_sub(steps);
        }
    });
}

#[cfg(test)]
pub(crate) fn with_step_budget<T>(budget: usize, parse: impl FnOnce() -> T) -> T {
    let saved = WORK.with(|work| {
        let mut work = work.borrow_mut();
        let prev = (work.nesting, work.remaining);
        work.nesting += 1;
        work.remaining = budget;
        prev
    });
    struct Restore(usize, usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            WORK.with(|work| {
                let mut work = work.borrow_mut();
                work.nesting = self.0;
                work.remaining = self.1;
            });
        }
    }
    let _restore = Restore(saved.0, saved.1);
    parse()
}

fn refuse(run: &Run<'_>, at: usize, error: ParserFailure) -> Parsed {
    WORK.with(|work| {
        let mut work = work.borrow_mut();
        if matches!(error, ParserFailure::Syntax { .. }) {
            work.mismatch = Some(DefinitionParseError::GeneratedParser {
                at: run.view.to_original(BytePos(at)),
                error,
            });
            return;
        }
        if work.error.is_none() {
            work.error = Some(DefinitionParseError::GeneratedParser {
                at: run.view.to_original(BytePos(at)),
                error,
            });
        }
    });
    if WORK.with(|work| work.borrow().error.is_some()) {
        categories::stop();
    }
    None
}

/// A rich alias transfers its enclosing descriptor to the generated engine.
/// Keeping `atomic`, `orelse` and repetitions inside that execution is essential:
/// interpreting only the leaf alias would lose consumed-error/backtrack state.
pub(super) fn needs(descr: &Descr) -> bool {
    let mut pending = vec![descr];
    while let Some(descr) = pending.pop() {
        match descr {
            Descr::Const(name) => {
                if simple(name).is_some_and(|alias| {
                    extension_census()
                        .aliases
                        .get(&alias)
                        .is_some_and(|info| info.arity == 0)
                        && !no_input(&alias)
                        && !matches!(
                            alias.as_str(),
                            "ident"
                                | "num"
                                | "str"
                                | "char"
                                | "scientific"
                                | "name"
                                | "hole"
                                | "tacticSeq"
                                | "noWs"
                                | "hygieneInfo"
                                | "ws"
                                | "linebreak"
                        )
                }) {
                    return true;
                }
            }
            Descr::Unary(_, body)
            | Descr::Node { body, .. }
            | Descr::TrailingNode { body, .. }
            | Descr::NodeWithAntiquot(_, _, body) => pending.push(body),
            Descr::Binary(_, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Descr::SepBy { item, parser, .. } => {
                pending.push(item);
                pending.push(parser);
            }
            _ => {}
        }
    }
    false
}

enum Request<'a> {
    Description(&'a Descr),
    Candidates(&'a [usize]),
}

pub(super) fn description(run: &Run<'_>, descr: &Descr, at: usize, end: usize) -> Parsed {
    read(run, Request::Description(descr), at, end, 0)
}

/// A quoted builtin slot may capture a whole signature/sequence, not just a
/// leaf inside it. Reuse the registered alias's own antiquotation combinator,
/// including its longest-match handling of typed captures and repetitions.
pub(crate) fn quoted_builtin_operand(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    alias: &str,
    at: usize,
    end: usize,
) -> Option<(Syntax, usize)> {
    if !crate::quotations::inside() || extension_census().aliases.get(alias)?.arity != 0 {
        return None;
    }
    let run = Run {
        leaves,
        view,
        tokens,
    };
    let descr = Descr::Const(Name::from_components([alias]));
    let (mut items, next) = description(&run, &descr, at, end)?;
    (items.len() == 1)
        .then(|| items.pop().map(|syntax| (syntax, next)))
        .flatten()
}

/// `None` means this set stays on the existing parser. Once selected, an error
/// from the generated engine is never retried by that other implementation.
pub(super) fn candidates(
    run: &Run<'_>,
    indices: &[usize],
    at: usize,
    end: usize,
    minimum: u32,
) -> Option<Parsed> {
    let grammar = active()?;
    if !indices
        .iter()
        .any(|&index| needs(&grammar.decls[index].descr))
    {
        return None;
    }
    Some(read(run, Request::Candidates(indices), at, end, minimum))
}

fn read(run: &Run<'_>, request: Request<'_>, at: usize, end: usize, minimum: u32) -> Parsed {
    let census = extension_census();
    let grammar = active()?;
    let start = run.tokens.get(at)?.extent.start().0;
    if WORK.with(|work| work.borrow().error.is_some()) {
        return None;
    }
    let interpreter = grammar.generated_interpreter(reference_builtin_interpreter());
    let interpreter = match interpreter {
        Ok(interpreter) => interpreter,
        Err(error) => return refuse(run, start, ParserFailure::Description(error)),
    };
    // Retain the full prefix so columns and byte offsets remain those of the
    // command. The endpoint excludes the next enclosing operand/delimiter.
    let limit = run
        .tokens
        .get(end)
        .map_or(run.view.normalized().len_bytes(), |token| {
            token.extent.start().0
        });
    let source = SourceText::from_utf8(&run.view.normalized().as_bytes()[..limit]).ok()?;
    let (remaining, saved_pos) = WORK.with(|work| {
        let work = work.borrow();
        (
            work.remaining,
            work.positions
                .last()
                .copied()
                .unwrap_or_else(|| run.tokens.first().map(|token| token.extent.start().0)),
        )
    });
    if remaining == 0 {
        return refuse(
            run,
            start,
            ParserFailure::Resource(ParserResourceLimit::Steps),
        );
    }
    let input = ParserInput {
        source: &source,
        start,
        saved_pos,
        quot_depth: crate::quotations::depth(),
        precedence: minimum,
        max_steps: remaining,
        verso_docs: grammar.docs.verso(false),
        verso_module_docs: grammar.docs.verso(true),
    };
    let parsed = match request {
        Request::Description(descr) => {
            interpreter.run_description(descr, &census.alias_declarations, input)
        }
        Request::Candidates(indices) => {
            let mut indices = indices.to_vec();
            indices.sort_unstable();
            let declarations: Vec<_> = indices
                .into_iter()
                .map(|index| grammar.decls[index].as_ref())
                .collect();
            interpreter.run_candidates(&declarations, input)
        }
    };
    WORK.with(|work| {
        let mut work = work.borrow_mut();
        work.remaining = work.remaining.saturating_sub(parsed.steps);
    });
    let mut syntax = match parsed.result {
        Ok(syntax) => syntax,
        Err((position, error)) => return refuse(run, position, error),
    };
    let next = run
        .tokens
        .partition_point(|token| token.extent.start().0 < parsed.next);
    if next > end
        || next < at
        || parsed.next > limit
        || next > at && run.tokens[next - 1].extent.end().0 > parsed.next
    {
        return refuse(run, parsed.next, ParserFailure::Boundary);
    }
    // Shared tokens retain their established trivia ownership. Generated
    // subtoken leaves (raw comments, interpolation and hygiene nodes) retain
    // the exact spans emitted by their builtin combinator.
    let mut pending: Vec<_> = syntax.iter_mut().collect();
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Node { args, .. } => pending.extend(args.iter_mut()),
            Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                let SourceInfo::Original { pos, end_pos, .. } = info else {
                    continue;
                };
                let index = run
                    .tokens
                    .partition_point(|token| token.extent.start() < *pos);
                if let Some(token) = run.tokens.get(index)
                    && token.extent.start() == *pos
                    && token.extent.end() == *end_pos
                    && let Ok(leaf) = run.leaves.leaf(index)
                {
                    *info = leaf.info();
                }
            }
            Syntax::Missing => {}
        }
    }
    Some((syntax, next))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exhausted_alias_budget_cannot_succeed_through_optional() {
        let mut file = FileGrammar::new(false, &[], None)
            .unwrap()
            .own_syntax_only();
        let declaration = crate::parse_source_command(
            b"syntax \"budgeted \" optional(bracketedBinder) \" done\" : command",
        )
        .unwrap();
        file.declare(declaration.syntax()).unwrap();
        let result = with_parse_errors(|| {
            WORK.with(|work| work.borrow_mut().remaining = 0);
            with_grammar(&file.grammar(), || {
                crate::parse_source_command(b"budgeted (n : Nat) done")
            })
        });
        assert!(matches!(
            result,
            Err(DefinitionParseError::GeneratedParser {
                error: ParserFailure::Resource(ParserResourceLimit::Steps),
                ..
            })
        ));
    }

    #[test]
    fn public_generated_entry_points_keep_depth_and_step_stops_sticky() {
        let interpreter = reference_builtin_interpreter();
        let depth = crate::builtin_interpreter::DEFAULT_MAX_DEPTH + 2;
        let nested = format!("{}Nat{}", "(".repeat(depth), ")".repeat(depth));
        let term = SourceText::from_utf8(nested.as_bytes()).unwrap();
        let error = interpreter
            .parse_category("term", &term, MAX_ALIAS_STEPS)
            .unwrap_err();
        assert!(error.unexpected.contains("depth"));
        let module = SourceText::from_utf8(format!("def deep := {nested}").as_bytes()).unwrap();
        let parsed = interpreter.parse_module(&module, MAX_ALIAS_STEPS);
        assert!(parsed.budget_exhausted);
        assert!(
            parsed
                .errors
                .iter()
                .any(|error| error.unexpected.contains("depth"))
        );
        let tiny = SourceText::from_utf8(b"Nat").unwrap();
        assert!(interpreter.parse_category("term", &tiny, 0).is_err());
    }
}
