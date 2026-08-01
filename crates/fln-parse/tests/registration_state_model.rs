//! `registration_state_model` — add / scope / restore / shadow as an explicit state machine
//! (bead fln-okfb).
//!
//! ## The model, and why it is written down separately
//!
//! The registry's behaviour is a state machine over (productions, scope stack, epoch). Writing it
//! out independently and checking the registry against it is only worth something if the model is
//! derived from the **pin's observed behaviour** rather than from reading the registry — otherwise
//! the model is a transcription of the implementation and agreeing with it proves nothing. That is
//! the trap this whole bead exists under.
//!
//! So every transition below cites the observation it comes from, all taken by running
//! `~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`:
//!
//! ```text
//! ADD          `syntax "myfoo" : term` then `#check myfoo`  -> accepted
//!              the same file with `#check` first            -> Unknown identifier 'myfoo'
//! SHADOW       two `notation "dup"` then `#eval dup`        -> error: Ambiguous term
//! SCOPE        `local notation` used inside `section`       -> accepted
//! RESTORE      the same, used after `end`                   -> Unknown identifier
//! NESTED       n1 in A, n2 in B; after `end B`: n1 ok, n2   -> Unknown identifier 'n2'
//! UNSCOPED     plain `notation` inside a section, after end -> accepted
//! ```
//!
//! ## What this suite does NOT establish
//!
//! It compares the registry against a model of the *same* seven observations. It cannot show that
//! the observations are the whole law — only that the registry implements the part of the law that
//! was observed. Anything the pin does that I did not think to probe is outside both sides equally.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::registry::{
    GrammarComponent, MemoAdvanceBudget, MemoKey, MemoLookup, ParseDependencies, ParseMemo,
    ParseProduct, ParserPosition, RegisterError, Registry,
};
use fln_parse::state::{ParserDescriptor, Production};
use fln_syntax::source::BytePos;

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn production(label: &str) -> Production {
    Production::new(name(label), 0, |_state| {})
}

fn stable_production(label: &str) -> Production {
    let kind = name(label);
    Production::described(
        kind.clone(),
        0,
        ParserDescriptor::stable(kind, 1, b"registration-state-model".to_vec()),
        |_state| {},
    )
}

/// The model: an independent account of what should be live, kept as a plain list so it shares no
/// code with the registry's tables.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct Model {
    /// (token, kind, scope-depth-or-none), in registration order — additive, never replacing.
    live: Vec<(Name, Name, Option<usize>)>,
    depth: usize,
}

impl Model {
    /// ADD and SHADOW: append, never replace. From the `Ambiguous term` observation.
    fn add(&mut self, token: &str, kind: &str, scoped: bool) {
        let scope = scoped.then_some(self.depth);
        self.live.push((name(token), name(kind), scope));
    }

    fn push_scope(&mut self) {
        self.depth += 1;
    }

    /// RESTORE and NESTED: drop exactly the closing scope's entries.
    fn pop_scope(&mut self) {
        let dying = self.depth;
        self.live.retain(|(_, _, scope)| *scope != Some(dying));
        self.depth -= 1;
    }

    fn kinds(&self, grammar_key: &Name) -> Vec<Name> {
        self.live
            .iter()
            .filter(|(key, _, _)| key.cmp(grammar_key).is_eq())
            .map(|(_, kind, _)| kind.clone())
            .collect()
    }
}

/// One scripted operation, applied to both the model and the registry.
#[derive(Debug, Clone)]
enum Op {
    Add {
        token: &'static str,
        kind: &'static str,
        scoped: bool,
    },
    PushScope,
    PopScope,
}

fn apply(ops: &[Op]) -> (Registry, Model, Name) {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    let mut model = Model::default();

    for op in ops {
        match op {
            Op::Add {
                token,
                kind,
                scoped,
            } => {
                registry
                    .add_leading(&term, name(token), production(kind), *scoped)
                    .expect("registers");
                model.add(token, kind, *scoped);
            }
            Op::PushScope => {
                registry.push_scope();
                model.push_scope();
            }
            Op::PopScope => {
                registry.pop_scope().expect("pops");
                model.pop_scope();
            }
        }
    }
    (registry, model, term)
}

fn agree(ops: &[Op], tokens: &[&str], context: &str) {
    let (registry, model, term) = apply(ops);
    let epoch = registry.epoch();
    for token in tokens {
        let token = name(token);
        assert_eq!(
            registry.kinds_at(&term, &token, epoch),
            model.kinds(&token),
            "{context}: registry and model disagree on {token:?} after {ops:?}"
        );
    }
}

/// **ADD and SHADOW.** Registrations accumulate; a second under one token does not replace.
#[test]
fn adding_accumulates_and_never_replaces() {
    agree(
        &[
            Op::Add {
                token: "dup",
                kind: "first",
                scoped: false,
            },
            Op::Add {
                token: "dup",
                kind: "second",
                scoped: false,
            },
            Op::Add {
                token: "other",
                kind: "third",
                scoped: false,
            },
        ],
        &["dup", "other"],
        "add/shadow",
    );
    // And directly, so the law is legible without reading the model.
    let (registry, _, term) = apply(&[
        Op::Add {
            token: "dup",
            kind: "first",
            scoped: false,
        },
        Op::Add {
            token: "dup",
            kind: "second",
            scoped: false,
        },
    ]);
    assert_eq!(
        registry.kinds_at(&term, &name("dup"), registry.epoch()),
        vec![name("first"), name("second")],
        "the pin gives `Ambiguous term` for two notations under one token, which is only possible \
         if both are live"
    );
}

/// **SCOPE, RESTORE, NESTED, UNSCOPED** — the four scope observations, as one sequence.
#[test]
fn scopes_restore_exactly_their_own_registrations() {
    agree(
        &[
            Op::Add {
                token: "g",
                kind: "global",
                scoped: false,
            },
            Op::PushScope,
            Op::Add {
                token: "a",
                kind: "outer",
                scoped: true,
            },
            Op::Add {
                token: "u",
                kind: "unscopedInside",
                scoped: false,
            },
            Op::PushScope,
            Op::Add {
                token: "b",
                kind: "inner",
                scoped: true,
            },
            Op::PopScope,
            Op::PopScope,
        ],
        &["g", "a", "b", "u"],
        "scope/restore/nested/unscoped",
    );
}

/// The model and the registry agree over every sequence a small operation alphabet generates —
/// a bounded exhaustive sweep rather than a sampled one, since the alphabet is small enough.
#[test]
fn the_model_and_the_registry_agree_over_every_short_sequence() {
    let alphabet = [
        Op::Add {
            token: "x",
            kind: "k1",
            scoped: false,
        },
        Op::Add {
            token: "x",
            kind: "k2",
            scoped: true,
        },
        Op::Add {
            token: "y",
            kind: "k3",
            scoped: true,
        },
        Op::PushScope,
    ];
    let mut checked = 0usize;

    // Every sequence of length <= 4, with PopScope inserted only where a scope is open, so the
    // sweep never generates a state the registry would refuse.
    fn walk(
        alphabet: &[Op],
        prefix: &mut Vec<Op>,
        depth: usize,
        remaining: usize,
        checked: &mut usize,
    ) {
        if remaining == 0 {
            let tokens = ["x", "y"];
            agree(prefix, &tokens, "sweep");
            *checked += 1;
            return;
        }
        for op in alphabet {
            prefix.push(op.clone());
            let next_depth = if matches!(op, Op::PushScope) {
                depth + 1
            } else {
                depth
            };
            walk(alphabet, prefix, next_depth, remaining - 1, checked);
            prefix.pop();
        }
        if depth > 0 {
            prefix.push(Op::PopScope);
            walk(alphabet, prefix, depth - 1, remaining - 1, checked);
            prefix.pop();
        }
    }

    for length in 1..=5 {
        walk(&alphabet, &mut Vec::new(), 0, length, &mut checked);
    }
    assert!(checked > 500, "only {checked} sequences swept");
}

/// **The model can fail.** A last-wins model must disagree with the registry, or the sweep above is
/// comparing two copies of the same mistake.
///
/// This is the assertion that makes the model independent rather than a transcription: it shows that
/// a *different* model produces a *different* answer, so agreement carries information.
#[test]
fn a_last_wins_model_disagrees_with_the_registry() {
    let ops = [
        Op::Add {
            token: "dup",
            kind: "first",
            scoped: false,
        },
        Op::Add {
            token: "dup",
            kind: "second",
            scoped: false,
        },
    ];
    let (registry, additive, term) = apply(&ops);

    // The wrong model: replace on collision.
    let mut last_wins: Vec<(Name, Name)> = Vec::new();
    for op in &ops {
        if let Op::Add { token, kind, .. } = op {
            let grammar_key = name(token);
            last_wins.retain(|(existing, _)| existing.cmp(&grammar_key).is_ne());
            last_wins.push((grammar_key, name(kind)));
        }
    }
    let wrong: Vec<Name> = last_wins.iter().map(|(_, kind)| kind.clone()).collect();

    assert_eq!(
        additive.kinds(&name("dup")),
        vec![name("first"), name("second")]
    );
    assert_eq!(wrong, vec![name("second")]);
    assert_ne!(
        registry.kinds_at(&term, &name("dup"), registry.epoch()),
        wrong,
        "a last-wins model must disagree with the registry — otherwise the model is a \
         transcription of the implementation and agreeing with it proves nothing"
    );
}

/// States the registry refuses are refused, not silently accepted: closing an unopened scope, and
/// registering into an undeclared category.
#[test]
fn the_registry_refuses_unreachable_operations() {
    let mut registry = Registry::new();
    let before = registry.epoch();
    assert_eq!(registry.pop_scope(), Err(RegisterError::NoScopeOpen));
    assert_eq!(
        registry.add_leading(&name("nope"), name("t"), production("p"), false),
        Err(RegisterError::UnknownCategory { name: name("nope") })
    );
    assert_eq!(registry.epoch(), before, "refusals are inert");
}

#[derive(Debug, Clone, Copy)]
enum EpochEdit {
    AddX,
    AddY,
    PushScope,
    AddScopedX,
    PopScope,
    SetOption,
}

fn memoized_and_fresh_agree(edits: &[EpochEdit]) -> usize {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category_at(BytePos(0), term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    let mut memo = ParseMemo::<Vec<Name>>::new();
    let queries = [
        (BytePos(5), name("x")),
        (BytePos(6), name("y")),
        (BytePos(15), name("x")),
        (BytePos(16), name("y")),
        (BytePos(25), name("x")),
        (BytePos(26), name("y")),
        (BytePos(35), name("x")),
        (BytePos(36), name("y")),
        (BytePos(45), name("x")),
        (BytePos(46), name("y")),
    ];
    let mut comparisons = 0usize;

    let check_all =
        |registry: &Registry, memo: &mut ParseMemo<Vec<Name>>, comparisons: &mut usize| {
            for (position, token) in &queries {
                let epoch = registry.epoch_at_position(*position);
                let identity = registry
                    .identity_at(epoch)
                    .expect("the timeline only names retained epochs")
                    .clone();
                let key = MemoKey {
                    position: *position,
                    category: term.clone(),
                    precedence: 0,
                    epoch,
                };
                let fresh = registry.kinds_at(&term, token, epoch);
                match memo.lookup(&key, &identity).expect("identity matches") {
                    MemoLookup::Hit(product) => {
                        assert_eq!(
                            product.value(),
                            &fresh,
                            "memoized and fresh reads diverged at {position:?} for {token:?} \
                         after {edits:?}"
                        );
                    }
                    MemoLookup::Miss | MemoLookup::CollisionMiss => {
                        memo.insert(
                            key,
                            &identity,
                            ParseProduct::new(
                                epoch,
                                ParseDependencies::from_components([GrammarComponent::Syntax {
                                    category: term.clone(),
                                    token: token.clone(),
                                    position: ParserPosition::Leading,
                                }]),
                                fresh,
                            ),
                        )
                        .expect("memo insert");
                    }
                }
                *comparisons += 1;
            }
        };
    check_all(&registry, &mut memo, &mut comparisons);

    for (index, edit) in edits.iter().enumerate() {
        let activation = BytePos(10 + index * 10);
        let before = registry.epoch();
        let before_identity = registry.identity().clone();
        match edit {
            EpochEdit::AddX => {
                registry
                    .add_leading_at(
                        activation,
                        &term,
                        name("x"),
                        stable_production(&format!("x{index}")),
                        false,
                    )
                    .expect("adds x");
            }
            EpochEdit::AddY => {
                registry
                    .add_leading_at(
                        activation,
                        &term,
                        name("y"),
                        stable_production(&format!("y{index}")),
                        false,
                    )
                    .expect("adds y");
            }
            EpochEdit::PushScope => {
                registry.push_scope_at(activation);
            }
            EpochEdit::AddScopedX => {
                registry
                    .add_leading_at(
                        activation,
                        &term,
                        name("x"),
                        stable_production(&format!("local{index}")),
                        true,
                    )
                    .expect("adds scoped x");
            }
            EpochEdit::PopScope => {
                registry.pop_scope_at(activation).expect("pops");
            }
            EpochEdit::SetOption => {
                registry.set_option_at(activation, name("parser.mode"), format!("v{index}"));
            }
        }
        let transition = registry
            .last_transition()
            .expect("each edit emits a transition")
            .clone();
        assert_eq!(transition.before, before);
        let after_identity = registry.identity().clone();
        memo.advance(
            &transition,
            &before_identity,
            &after_identity,
            MemoAdvanceBudget::generous(),
            None,
        )
        .into_complete()
        .expect("a generous memo transition completes")
        .expect("memo transition");
        check_all(&registry, &mut memo, &mut comparisons);
    }
    comparisons
}

/// Bounded exhaustive property: memoized registry reads equal cold reads after every valid short
/// edit sequence, including activation boundaries and scope restoration.
#[test]
fn memoized_parse_equals_fresh_parse_over_generated_epoch_respecting_edits() {
    fn walk(
        prefix: &mut Vec<EpochEdit>,
        depth: usize,
        remaining: usize,
        cases: &mut usize,
        comparisons: &mut usize,
    ) {
        if remaining == 0 {
            *comparisons += memoized_and_fresh_agree(prefix);
            *cases += 1;
            return;
        }
        for edit in [
            EpochEdit::AddX,
            EpochEdit::AddY,
            EpochEdit::PushScope,
            EpochEdit::SetOption,
        ] {
            prefix.push(edit);
            walk(
                prefix,
                depth + usize::from(matches!(edit, EpochEdit::PushScope)),
                remaining - 1,
                cases,
                comparisons,
            );
            prefix.pop();
        }
        if depth > 0 {
            for edit in [EpochEdit::AddScopedX, EpochEdit::PopScope] {
                prefix.push(edit);
                walk(
                    prefix,
                    depth - usize::from(matches!(edit, EpochEdit::PopScope)),
                    remaining - 1,
                    cases,
                    comparisons,
                );
                prefix.pop();
            }
        }
    }

    let mut cases = 0usize;
    let mut comparisons = 0usize;
    for length in 1..=4 {
        walk(&mut Vec::new(), 0, length, &mut cases, &mut comparisons);
    }
    assert!(cases > 400, "only {cases} edit sequences checked");
    assert!(
        comparisons > 10_000,
        "only {comparisons} memo/fresh comparisons checked"
    );
}
