//! The Pratt loop: leading production, then the trailing loop (plan §9; bead fln-ffam).
//!
//! Every rule here is transcribed from `Lean/Parser/Basic.lean` at the pinned tag, and the two
//! error-discarding rules were additionally **observed by running the pinned `lean` binary** —
//! see [`trailing_loop`]. That distinction matters and is kept explicit throughout: a rule
//! transcribed from source is a reading, a rule observed from the running Reference is evidence,
//! and a rule I reasoned to is neither.
//!
//! ## Why a from-scratch comparison cannot establish this slice
//!
//! Discarding an error is **invisible in the happy path**. It shows up only as a diagnostic that
//! never appears, or one that appears twice — and both of those look identical whether my
//! implementation discards correctly, discards too much, or discards nothing at all, so long as
//! whatever I compare against does the same. A differential proves agreement, never correctness.
//! So the oracle for this slice is the pin, and where the pin could not be consulted the module
//! says so rather than implying otherwise.
//!
//! ## The shape (`prattParser`, `Basic.lean:1969`)
//!
//! ```text
//! prattParser kind tables behavior antiquot =
//!   let s := leadingParser ...
//!   if s.hasError then s else trailingLoop tables c s
//! ```
//!
//! A leading production runs once; then trailing productions chain for as long as they apply. A
//! leading failure aborts — the trailing loop is not entered — which is why a broken leading
//! position yields exactly one diagnostic rather than one per trailing attempt.

use crate::state::{ParseError, ParserState, Production, longest_match, make_result};
use fln_core::name::Name;
use fln_syntax::source::BytePos;
use fln_syntax::tree::Syntax;

/// What a table lookup found at the current position.
///
/// A lookup can *fail to peek a token at all* — which is a different thing from finding no
/// applicable production, and the trailing loop treats the two differently. Collapsing them into
/// an empty list would erase rule 1 before it could be applied.
pub enum Lookup<'a> {
    /// The productions indexed under the token here, possibly empty.
    Productions(Vec<&'a Production>),
    /// The token itself could not be lexed. `indexed` propagates this through `peekToken`.
    TokenError(ParseError),
}

/// The grammar the loop drives.
///
/// A trait rather than a concrete table so this slice does not depend on how productions are
/// indexed — that is slice C's business (`indexed` and `LeadingIdentBehavior`). The loop's rules
/// are independent of the lookup strategy, and keeping them apart means neither slice has to be
/// re-verified when the other changes.
pub trait Grammar {
    /// The category name, used in the "expected ..." diagnostic.
    fn kind(&self) -> Name;

    /// Productions applicable at a leading position.
    fn leading_at(&self, state: &ParserState) -> Lookup<'_>;

    /// Productions applicable at a trailing position.
    fn trailing_at(&self, state: &ParserState) -> Lookup<'_>;

    /// Consume one token, returning its text.
    ///
    /// Used only on the no-applicable-production path, where upstream consumes the offending
    /// token before reporting it (see [`leading_parser`]).
    fn consume_token(&self, state: &mut ParserState) -> Result<String, ParseError>;
}

/// `prattParser` (`Basic.lean:1969`): one leading production, then the trailing loop.
pub fn pratt_parser(grammar: &dyn Grammar, state: &mut ParserState) {
    leading_parser(grammar, state);
    if state.has_error() {
        return;
    }
    trailing_loop(grammar, state);
}

/// `leadingParserAux` (`Basic.lean:1908`).
///
/// The part worth transcribing rather than inventing is the empty-productions branch. Upstream's
/// own comment: "if there are no applicable parsers, consume the leading token and flag it as
/// unexpected at this position". **Consume, then flag** — the token is eaten even though nothing
/// could parse it.
///
/// That ordering is not tidiness, it is what keeps input accounting total: a parser that reported
/// without consuming would be asked to parse the same position again and would report again,
/// forever. Observed against the pin: `#check @@@` reports at end of input rather than looping or
/// reporting at the `@`, because the `@` was consumed and the scan moved on.
pub fn leading_parser(grammar: &dyn Grammar, state: &mut ParserState) {
    let mark = state.stack_size();
    let productions = match grammar.leading_at(state) {
        Lookup::TokenError(error) => {
            // Upstream: `if s.hasError then return s`. A leading position that cannot even be
            // tokenized is a real error — unlike the trailing case, it is not discarded.
            state.set_error(error);
            return;
        }
        Lookup::Productions(productions) => productions,
    };

    if productions.is_empty() {
        let at = state.pos();
        match grammar.consume_token(state) {
            Ok(token) => state.set_error(ParseError::with_expected(
                format!("unexpected token '{token}'"),
                [kind_text(grammar)],
                at,
                true,
            )),
            // No token to consume: end of input, which upstream reports through `tokenFn`'s own
            // EOI error rather than as an unexpected token.
            Err(error) => state.set_error(error),
        }
        return;
    }

    longest_match(state, None, &productions);
    make_result(state, mark);
}

/// `trailingLoop` (`Basic.lean:1928`) — and the two discard rules.
///
/// ## Rule 1: a token error from the lookup is discarded and the loop breaks
///
/// Upstream, verbatim: "Discard token parse errors and break the trailing loop instead. The error
/// will be flagged when the next leading position is parsed, unless the token is in fact valid
/// there (e.g. EOI at command level, no-longer forbidden token)."
///
/// **Observed against the pinned binary.** `def f : Nat := 1` followed by nothing produces
/// **zero** diagnostics. At the trailing position after `1` the lookup peeks and hits end of
/// input, which is a token error; if it were reported, that file would carry an "unexpected end
/// of input" error. It does not. And `def f : Nat := 1` followed by `@@@` produces exactly one
/// error, `unexpected token '@'; expected command`, positioned at the *next leading position* —
/// which is the pin's stated reason made visible.
///
/// ## Rule 2: a *non-consuming* error is discarded and `left` is restored
///
/// Upstream, verbatim: "Discard non-consuming parse errors and break the trailing loop instead,
/// restoring `left`. This is necessary for fallback parsers like `app` that pretend to be always
/// applicable."
///
/// **Observed against the pinned binary.** `#check 1 = 2 = 3` — `=` is `infix:50`, so its
/// arguments sit at 51 and the second `=` runs `checkLhsPrec 51` against an `lhsPrec` of 50. That
/// check is an epsilon parser: it fails having consumed nothing. The observed result is a single
/// error, `unexpected token '='; expected command`, at the leftover `=`. So the precedence failure
/// produced **no diagnostic of its own** and `1 = 2` was returned intact for the command level to
/// find the leftover. Reproduced with `1 < 2 < 3` and with a user `infix:50 " ## "`.
///
/// A consequence worth recording: `checkPrec`'s message — "unexpected token at this precedence
/// level; consider parenthesizing the term" — is **discarded** in exactly these cases. I could
/// not get it to surface in any probe, and it appears nowhere in the pin's source except its own
/// definition. I am not claiming it is unreachable; I am recording that I did not observe it
/// reaching a user, which is a weaker and honest statement.
///
/// ## The termination guard is OURS, not the pin's
///
/// Upstream's `trailingLoop` is a `partial def` that recurses unconditionally on success. A
/// trailing production that succeeded while consuming nothing would loop forever there; upstream
/// tolerates that because well-formed grammars do not contain one. The guard below is a
/// divergence I am adding deliberately, flagged as such: a hung parser is a worse failure than a
/// rejected grammar, and this converts one into the other.
pub fn trailing_loop(grammar: &dyn Grammar, state: &mut ParserState) {
    loop {
        let mark = state.stack_size();
        let start = state.pos();

        let productions = match grammar.trailing_at(state) {
            // RULE 1. Discard and break, restoring the position.
            Lookup::TokenError(_) => {
                state.restore(mark, start);
                return;
            }
            Lookup::Productions(productions) => productions,
        };

        if productions.is_empty() {
            // "no available trailing parser" — not an error, just the end of the chain.
            return;
        }

        let Some(left) = state.pop() else {
            // The loop is only entered with a left operand on the stack. Refusing rather than
            // indexing keeps the function total if a caller ever drives it wrongly.
            state.set_error(ParseError::new("trailing loop with no left operand", start));
            return;
        };

        longest_match(state, Some(left.clone()), &productions);

        if state.has_error() {
            if state.pos() == start {
                // RULE 2. Non-consuming failure: discard, restore `left`, break. Upstream's
                // `s.restore (iniSz - 1) iniPos |>.pushSyntax left`.
                state.restore(mark.saturating_sub(1), start);
                state.push(left);
                return;
            }
            // Consuming failure: a real error, propagated.
            return;
        }

        if state.pos() == start {
            // OUR guard, not the pin's — see the function docs. Nothing consumed and no error
            // means the chain cannot advance, so stop rather than recurse forever.
            return;
        }
    }
}

fn kind_text(grammar: &dyn Grammar) -> String {
    grammar.kind().to_display_string()
}

/// The syntax a completed parse produced, if it produced exactly one node.
pub fn result_of(state: &ParserState) -> Option<&Syntax> {
    state.back()
}

/// Where a parse stopped.
pub fn stopped_at(state: &ParserState) -> BytePos {
    state.pos()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::Prec;
    use fln_syntax::source::{ByteSpan, SourceInfo};
    use std::cell::RefCell;

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn atom(text: &str, from: usize, to: usize) -> Syntax {
        Syntax::atom(
            SourceInfo::Original {
                leading: ByteSpan::empty_at(BytePos(from)),
                pos: BytePos(from),
                trailing: ByteSpan::empty_at(BytePos(to)),
                end_pos: BytePos(to),
            },
            text,
        )
    }

    /// How a scripted lookup should behave at each call.
    enum Step {
        /// Hand out the productions at these indices.
        Give(Vec<usize>),
        /// No applicable production — the end of a chain.
        Empty,
        /// The token could not be lexed (rule 1's trigger).
        TokenError,
    }

    /// A scripted grammar: the loop's rules are about *what it does with* lookup answers, so the
    /// answers are scripted rather than derived from a real table. That keeps this slice's tests
    /// independent of slice C's indexing, and it lets a token error be produced on demand — which
    /// a real table would only do on input the lexer refuses.
    struct Scripted {
        productions: Vec<Production>,
        leading: RefCell<Vec<Step>>,
        trailing: RefCell<Vec<Step>>,
        /// Tokens `consume_token` hands out, in order.
        tokens: RefCell<Vec<String>>,
    }

    impl Scripted {
        fn new(productions: Vec<Production>, leading: Vec<Step>, trailing: Vec<Step>) -> Scripted {
            Scripted {
                productions,
                leading: RefCell::new(leading),
                trailing: RefCell::new(trailing),
                tokens: RefCell::new(vec!["?".to_string()]),
            }
        }

        fn answer(&self, script: &RefCell<Vec<Step>>) -> Lookup<'_> {
            let mut script = script.borrow_mut();
            let step = if script.is_empty() {
                Step::Empty
            } else {
                script.remove(0)
            };
            match step {
                Step::Give(indices) => Lookup::Productions(
                    indices
                        .into_iter()
                        .map(|index| &self.productions[index])
                        .collect(),
                ),
                Step::Empty => Lookup::Productions(Vec::new()),
                Step::TokenError => {
                    Lookup::TokenError(ParseError::new("could not lex a token", BytePos(0)))
                }
            }
        }
    }

    impl Grammar for Scripted {
        fn kind(&self) -> Name {
            name("term")
        }

        fn leading_at(&self, _state: &ParserState) -> Lookup<'_> {
            self.answer(&self.leading)
        }

        fn trailing_at(&self, _state: &ParserState) -> Lookup<'_> {
            self.answer(&self.trailing)
        }

        fn consume_token(&self, state: &mut ParserState) -> Result<String, ParseError> {
            let mut tokens = self.tokens.borrow_mut();
            if tokens.is_empty() {
                return Err(ParseError::new("unexpected end of input", state.pos()));
            }
            let token = tokens.remove(0);
            state.set_pos(BytePos(state.pos().0 + token.len()));
            Ok(token)
        }
    }

    /// A leading production that consumes to `end` and pushes one atom.
    fn leading(label: &str, end: usize) -> Production {
        let text = label.to_string();
        Production::new(name(label), 0, move |state| {
            let from = state.pos().0;
            state.set_pos(BytePos(end));
            state.push(atom(&text, from, end));
        })
    }

    /// A trailing production that folds `left` into a node and consumes to `end`.
    fn trailing(label: &str, end: usize) -> Production {
        let kind = name(label);
        Production::new(kind.clone(), 0, move |state| {
            let left = state.pop().unwrap_or(Syntax::Missing);
            state.set_pos(BytePos(end));
            state.push(Syntax::node(kind.clone(), vec![left]));
        })
    }

    /// A trailing production that fails WITHOUT consuming — rule 2's trigger, and the shape a
    /// precedence check has, since `checkLhsPrec` is an epsilon parser.
    fn declines(label: &str) -> Production {
        Production::new(name(label), 0, move |state| {
            let at = state.pos();
            state.set_error(ParseError::new(crate::state::PREC_MESSAGE, at));
        })
    }

    /// A trailing production that consumes and then fails — a real error.
    fn breaks(label: &str, end: usize) -> Production {
        Production::new(name(label), 0, move |state| {
            state.set_pos(BytePos(end));
            state.set_error(ParseError::consuming("malformed", BytePos(end)));
        })
    }

    fn describe(node: Option<&Syntax>) -> String {
        match node {
            Some(Syntax::Atom { val, .. }) => format!("atom {val}"),
            Some(Syntax::Node { kind, args, .. }) => {
                format!("node {}[{}]", kind.to_display_string(), args.len())
            }
            Some(Syntax::Ident { .. }) => "ident".to_string(),
            Some(Syntax::Missing) => "missing".to_string(),
            None => "nothing".to_string(),
        }
    }

    /// **RULE 1**, mirroring the pin observation: a token error at a trailing position is
    /// discarded, the loop breaks, and the completed term survives with NO diagnostic.
    ///
    /// The pin equivalent is `def f : Nat := 1` with nothing after it, which produces zero
    /// diagnostics even though the trailing lookup hits end of input.
    #[test]
    fn a_token_error_at_a_trailing_position_is_discarded_and_leaves_no_diagnostic() {
        let grammar = Scripted::new(
            vec![leading("one", 1)],
            vec![Step::Give(vec![0])],
            vec![Step::TokenError],
        );
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);

        assert!(
            !state.has_error(),
            "a trailing token error must not become a diagnostic: {:?}",
            state.error()
        );
        assert_eq!(
            describe(state.back()),
            "atom one",
            "the term survives intact"
        );
        assert_eq!(
            state.pos(),
            BytePos(1),
            "the position is restored, not advanced"
        );
        assert_eq!(state.stack_size(), 1);
    }

    /// The same token error at a LEADING position is a real error, not discarded. The asymmetry is
    /// upstream's and it is the whole reason rule 1 needs stating: `leadingParserAux` returns the
    /// error, `trailingLoop` throws it away.
    #[test]
    fn a_token_error_at_a_leading_position_is_reported() {
        let grammar = Scripted::new(vec![leading("one", 1)], vec![Step::TokenError], vec![]);
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);
        assert!(
            state.has_error(),
            "a leading token error must be reported, unlike a trailing one"
        );
    }

    /// **RULE 2**, mirroring the pin observation: a trailing production that fails WITHOUT
    /// consuming is discarded, `left` is restored, and there is no diagnostic.
    ///
    /// The pin equivalent is `#check 1 = 2 = 3`, where the second `=` fails `checkLhsPrec` without
    /// consuming: the observed output is one error at the leftover `=` from the COMMAND level, and
    /// nothing from the precedence check itself.
    #[test]
    fn a_non_consuming_trailing_failure_is_discarded_and_restores_the_left_operand() {
        let grammar = Scripted::new(
            vec![leading("lhs", 3), declines("prec")],
            vec![Step::Give(vec![0])],
            vec![Step::Give(vec![1])],
        );
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);

        assert!(
            !state.has_error(),
            "a non-consuming trailing failure must not become a diagnostic: {:?}",
            state.error()
        );
        assert_eq!(
            describe(state.back()),
            "atom lhs",
            "the left operand is restored exactly, not replaced by a partial node"
        );
        assert_eq!(state.stack_size(), 1, "and there is exactly one node");
        assert_eq!(
            state.pos(),
            BytePos(3),
            "the position is where the term ended"
        );
    }

    /// A trailing production that CONSUMED before failing is a real error and propagates. This is
    /// the direction that distinguishes rule 2 from "discard every trailing error", which would
    /// swallow genuine malformed input.
    #[test]
    fn a_consuming_trailing_failure_is_a_real_error() {
        let grammar = Scripted::new(
            vec![leading("lhs", 3), breaks("bad", 9)],
            vec![Step::Give(vec![0])],
            vec![Step::Give(vec![1])],
        );
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);

        assert!(
            state.has_error(),
            "a trailing failure that consumed input must be reported"
        );
        assert_eq!(state.error().expect("error").message(), "malformed");
        assert!(
            state.pos().0 > 3,
            "and the position reflects what it consumed"
        );
    }

    /// The trailing chain runs as long as productions apply, folding left-associatively.
    #[test]
    fn the_trailing_chain_folds_repeatedly_while_productions_apply() {
        let grammar = Scripted::new(
            vec![leading("a", 1), trailing("op", 3), trailing("op", 5)],
            vec![Step::Give(vec![0])],
            vec![Step::Give(vec![1]), Step::Give(vec![2]), Step::Empty],
        );
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);

        assert!(!state.has_error());
        assert_eq!(state.stack_size(), 1, "the chain leaves one node");
        assert_eq!(
            describe(state.back()),
            "node op[1]",
            "folded, not accumulated"
        );
        assert_eq!(
            state.pos(),
            BytePos(5),
            "and it consumed through both steps"
        );
    }

    /// No applicable leading production: the token is CONSUMED and then flagged.
    ///
    /// Consume-then-flag is upstream's order and it is what keeps accounting total — a parser that
    /// flagged without consuming would be asked the same position again forever. The message shape
    /// mirrors the pin's observed `unexpected token '+'; expected term`.
    #[test]
    fn no_applicable_leading_production_consumes_the_token_then_flags_it() {
        let grammar = Scripted::new(vec![], vec![Step::Empty], vec![]);
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);

        let error = state.error().expect("an unexpected-token error");
        assert_eq!(
            error.message(),
            "unexpected token '?'; expected term",
            "the message names the token and the category, as the pin's does"
        );
        assert!(
            error.consumed,
            "the token was consumed before being flagged"
        );
        assert_eq!(
            state.pos(),
            BytePos(1),
            "consume-then-flag: the position advanced past the offending token"
        );
    }

    /// With no token left to consume, the refusal is end-of-input rather than a fabricated
    /// unexpected token.
    #[test]
    fn no_applicable_production_at_end_of_input_reports_end_of_input() {
        let grammar = Scripted::new(vec![], vec![Step::Empty], vec![]);
        grammar.tokens.borrow_mut().clear();
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);
        assert_eq!(
            state.error().expect("error").message(),
            "unexpected end of input"
        );
    }

    /// A leading failure aborts before the trailing loop, so one broken position yields ONE
    /// diagnostic rather than one per trailing attempt. Asserted by scripting a trailing lookup
    /// that would panic if it were consulted.
    #[test]
    fn a_leading_failure_does_not_enter_the_trailing_loop() {
        struct Exploding;
        impl Grammar for Exploding {
            fn kind(&self) -> Name {
                name("term")
            }
            fn leading_at(&self, _state: &ParserState) -> Lookup<'_> {
                Lookup::TokenError(ParseError::new("bad token", BytePos(0)))
            }
            fn trailing_at(&self, _state: &ParserState) -> Lookup<'_> {
                // Reaching here would mean the trailing loop ran after a leading failure. An
                // empty answer would hide that, so this returns a marker the test can detect.
                Lookup::TokenError(ParseError::new("TRAILING WAS CONSULTED", BytePos(0)))
            }
            fn consume_token(&self, _state: &mut ParserState) -> Result<String, ParseError> {
                Ok("x".to_string())
            }
        }
        let mut state = ParserState::new(0);
        pratt_parser(&Exploding, &mut state);
        assert_eq!(
            state.error().expect("error").message(),
            "bad token",
            "the leading error must survive; if the trailing loop had run it would have \
             overwritten or discarded it"
        );
    }

    /// **Termination.** A trailing production that succeeds without consuming stops the chain
    /// rather than looping forever.
    ///
    /// This guard is OURS, not the pin's: upstream's `trailingLoop` recurses unconditionally on
    /// success and would loop here. Flagged as a deliberate divergence because a hung parser is a
    /// worse failure than a rejected grammar.
    #[test]
    fn a_trailing_production_that_consumes_nothing_stops_the_chain() {
        let stall = Production::new(name("stall"), 0, |state| {
            let left = state.pop().unwrap_or(Syntax::Missing);
            state.push(Syntax::node(name("stall"), vec![left]));
        });
        let grammar = Scripted::new(
            vec![leading("a", 1), stall],
            vec![Step::Give(vec![0])],
            // An unbounded supply of the stalling production: without the guard this never ends.
            vec![
                Step::Give(vec![1]),
                Step::Give(vec![1]),
                Step::Give(vec![1]),
            ],
        );
        let mut state = ParserState::new(0);
        pratt_parser(&grammar, &mut state);
        assert!(!state.has_error(), "stopping is not an error");
        assert_eq!(state.pos(), BytePos(1), "the position never advanced");
    }

    /// The context precedence reaches the productions, so a production can consult it. Asserted
    /// because the loop must not reset it: `prattParser` is entered *from* `categoryParser`, which
    /// is what set it.
    #[test]
    fn the_context_precedence_survives_the_loop() {
        let observed = RefCell::new(Vec::new());
        {
            let probe = Production::new(name("probe"), 0, |state| {
                state.set_pos(BytePos(1));
                state.push(atom("p", 0, 1));
            });
            let grammar = Scripted::new(vec![probe], vec![Step::Give(vec![0])], vec![Step::Empty]);
            let mut state = ParserState::new(65 as Prec);
            pratt_parser(&grammar, &mut state);
            observed.borrow_mut().push(state.prec());
        }
        assert_eq!(
            observed.borrow().as_slice(),
            &[65],
            "the loop must not reset the context precedence it was entered with"
        );
    }
}
