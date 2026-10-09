//! Layout context for statement conditionals in the shared compound plan.
//!
//! This only assigns ranges and grammar categories. The ordinary do frame
//! parser still validates every statement, header and original source leaf.
//! Parentheses/records protect nested expressions; a branch is a doSeq, not a
//! fresh do expression (in particular it must not acquire a return scope).
use super::*;

struct Sequence {
    introducer: usize,
    first: usize,
    depth: usize,
    baseline: usize,
    braced: bool,
    owner: Option<usize>,
    ready: bool,
}

#[derive(Default)]
pub(super) struct DoScopes {
    sequences: Vec<Sequence>,
    ended: HashSet<usize>,
}

impl DoScopes {
    pub(super) fn open(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        introducer: usize,
        depth: usize,
        owner: Option<usize>,
        end: usize,
    ) -> Result<(), NatDefinitionParseError> {
        self.open_at(view, tokens, introducer, introducer + 1, depth, owner, end)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn open_at(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        introducer: usize,
        start: usize,
        depth: usize,
        owner: Option<usize>,
        end: usize,
    ) -> Result<(), NatDefinitionParseError> {
        let braced = is_symbol(tokens, start, "{");
        let first = start + usize::from(braced);
        if first >= end {
            return Err(refuse(view, tokens, start));
        }
        if let Some(owner) = owner {
            self.ended.remove(&owner);
        }
        self.sequences.push(Sequence {
            introducer,
            first,
            depth: depth + usize::from(braced),
            baseline: column(view, tokens, first),
            braced,
            owner,
            ready: true,
        });
        Ok(())
    }

    fn pop(&mut self) {
        if let Some(owner) = self.sequences.pop().and_then(|sequence| sequence.owner) {
            self.ended.insert(owner);
        }
    }

    /// An else on a later line may not jump rightward into a more deeply
    /// indented statement conditional. Inline else keeps nearest-if binding.
    pub(super) fn accepts_else(
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        p: &ConditionalPlan,
    ) -> bool {
        !p.statement
            || !later_line(view, tokens, at, p.start)
            || column(view, tokens, at) >= p.baseline
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn before(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        depth: usize,
        conditionals: &[ConditionalPlan],
        matches: &[MatchPlan],
        failure: bool,
    ) {
        let else_target = is_symbol(tokens, at, "else")
            .then(|| {
                conditionals
                    .iter()
                    .rev()
                    .find(|p| {
                        p.depth == depth
                            && p.then_at.is_some()
                            && p.else_at.is_none()
                            && Self::accepts_else(view, tokens, at, p)
                    })
                    .map(|p| p.start)
            })
            .flatten();
        let match_target = (is_symbol(tokens, at, "|") && !failure)
            .then(|| {
                matches
                    .iter()
                    .rev()
                    .find(|p| p.depth == depth)
                    .map(|p| p.start)
            })
            .flatten();
        while self.sequences.last().is_some_and(|s| {
            at >= s.first
                && !s.braced
                && s.depth == depth
                && ([")", "]", "}", "⦄", "⟩", ","]
                    .iter()
                    .any(|t| is_symbol(tokens, at, t))
                    || (later_line(view, tokens, at, s.first)
                        && column(view, tokens, at) < s.baseline)
                    || else_target.is_some_and(|target| target < s.introducer)
                    || match_target.is_some_and(|target| target < s.introducer))
        }) {
            self.pop();
        }
    }

    pub(super) fn statement_at(
        &mut self,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        depth: usize,
    ) -> Option<usize> {
        let s = self.sequences.last_mut()?;
        if s.depth != depth || at < s.first {
            return None;
        }
        let start = s.ready
            || (at > s.first
                && later_line(view, tokens, at, at - 1)
                && column(view, tokens, at) <= s.baseline);
        s.ready = false;
        start.then(|| {
            // `else if` resets the nested conditional's layout anchor to else,
            // as the pin's dedicated elseIf production does.
            if at == s.first
                && is_symbol(tokens, s.introducer, "else")
                && !later_line(view, tokens, at, s.introducer)
            {
                column(view, tokens, s.introducer)
            } else {
                column(view, tokens, at)
            }
        })
    }

    /// `leftArrow doElemParser` (`doIdDecl`, `doPatDecl`, `nestedAction`): an `if` or `match` right
    /// after a `←` is a do element, not a term. `doIf`'s `withPositionAfterLinebreak` anchors it at
    /// its own column after a line break, and otherwise at the enclosing sequence's position, which
    /// a bracket's `withoutPosition` clears.
    pub(super) fn arrow_element(
        &self,
        view: &SourceView,
        tokens: &[LexedToken],
        at: usize,
        depth: usize,
    ) -> Option<usize> {
        if at == 0
            || !(is_symbol(tokens, at - 1, "←") || is_symbol(tokens, at - 1, "<-"))
            || !(is_symbol(tokens, at, "if") || is_symbol(tokens, at, "match"))
        {
            return None;
        }
        if later_line(view, tokens, at, at - 1) {
            return Some(column(view, tokens, at));
        }
        Some(
            self.sequences
                .last()
                .filter(|s| s.depth == depth)
                .map_or(0, |s| s.baseline),
        )
    }

    pub(super) fn after(
        &mut self,
        tokens: &[LexedToken],
        at: usize,
        depth: usize,
        statement_separator: bool,
    ) {
        if let Some(s) = self.sequences.last_mut()
            && at >= s.first
            && s.depth == depth
        {
            if s.braced && is_symbol(tokens, at, "}") {
                self.pop();
            } else if statement_separator {
                s.ready = true;
            }
        }
    }

    /// A catch/finally delimiter ends the preceding exception body and any
    /// unbraced statement branches nested inside it. Braces keep their own
    /// delimiter discipline and cannot be silently crossed.
    pub(super) fn end_exception_body(&mut self, start: usize) -> bool {
        while self.sequences.last().is_some_and(|s| s.introducer >= start) {
            if self.sequences.last().is_some_and(|s| s.braced) {
                return false;
            }
            self.pop();
        }
        true
    }

    pub(super) fn ended(&self, start: usize) -> bool {
        self.ended.contains(&start)
    }
    pub(super) fn closed(&mut self, start: usize) {
        self.ended.remove(&start);
    }
}
