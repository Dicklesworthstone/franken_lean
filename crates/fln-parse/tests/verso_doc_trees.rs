//! Verso doc comments against the pinned Reference (bead `fln-pin-syntax-corpus-7b5b`;
//! `fln_parse`'s `verso`): where `doc.verso` is set, a doc comment's body is a Verso document.
//!
//! `fixtures/verso_docs.pin-syntax` is the pin's lossless capture of `fixtures/verso_docs.lean`,
//! taken from `leanprover/lean4:v4.32.0` on 2026-10-09:
//!
//! ```text
//! T=~/.elan/toolchains/leanprover--lean4---v4.32.0
//! $T/bin/lean --run scripts/extract/dump_command_syntax.lean verso_docs.lean "$T" --lossless
//! ```
//!
//! Every command is parsed as frontier A parses an Init file (the file's grammar, scope commands
//! advancing it) and compared with the pin's tree leaf by leaf, file positions included. The file
//! holds paragraphs, lists, a header, a code block, a quote, links, an image, math, role
//! arguments and a block command; three bodies the pin cannot parse (an unclosed link, and the
//! emphasis inside `**…**`, whose empty opener makes the pin's `many` fail), which are its
//! `parseFailure`; an indented field doc; and the option's scoping: `end` restores it, and
//! `set_option … in` leaves the doc after it plain, since the pin parses that command before the
//! option is set.

#![forbid(unsafe_code)]

use fln_parse::command_scope::{self, imports::parse_source_header};
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::pin_syntax;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;

const SOURCE: &str = include_str!("fixtures/verso_docs.lean");
const PIN: &str = include_str!("fixtures/verso_docs.pin-syntax");

fn first_position(root: &Syntax) -> Option<usize> {
    let mut stack = vec![root];
    while let Some(syntax) = stack.pop() {
        match syntax {
            Syntax::Atom {
                info: SourceInfo::Original { pos, .. },
                ..
            }
            | Syntax::Ident {
                info: SourceInfo::Original { pos, .. },
                ..
            } => return Some(pos.0),
            Syntax::Node { args, .. } => stack.extend(args.iter().rev()),
            _ => {}
        }
    }
    None
}

fn span(info: &SourceInfo, offset: usize) -> Option<(usize, usize)> {
    match info {
        SourceInfo::Original { pos, end_pos, .. } => Some((pos.0 + offset, end_pos.0 + offset)),
        _ => None,
    }
}

/// The first place the trees part: a different node, atom or name, or a leaf elsewhere. `ours`
/// holds positions in the command's bytes, which start at `offset`.
fn difference(pin: &Syntax, ours: &Syntax, offset: usize) -> Option<String> {
    let mut stack = vec![(pin, ours)];
    while let Some((pin, ours)) = stack.pop() {
        let placed = match (pin, ours) {
            (Syntax::Missing, Syntax::Missing) => true,
            (Syntax::Atom { info: a, val: x }, Syntax::Atom { info: b, val: y }) if x == y => {
                span(a, 0) == span(b, offset)
            }
            (
                Syntax::Ident {
                    info: a, val: x, ..
                },
                Syntax::Ident {
                    info: b, val: y, ..
                },
            ) if x == y => span(a, 0) == span(b, offset),
            (
                Syntax::Node {
                    kind: k, args: xs, ..
                },
                Syntax::Node {
                    kind: l, args: ys, ..
                },
            ) if k == l && xs.len() == ys.len() => {
                stack.extend(xs.iter().zip(ys).rev());
                true
            }
            _ => false,
        };
        if !placed {
            return Some(format!("pin {pin:?}\nours {ours:?}"));
        }
    }
    None
}

#[test]
fn verso_doc_comments_produce_the_pins_trees_and_positions() {
    let trees = pin_syntax::read(PIN, SOURCE.as_bytes()).expect("the capture decodes");
    let header = parse_source_header(SOURCE.as_bytes()).expect("no header");
    let body_start = header.body_start.0;
    let mut grammar = FileGrammar::new(false, &[], None).expect("Init");
    let parts = with_grammar(&grammar.grammar(), || {
        command_scope::partition(&SOURCE.as_bytes()[body_start..])
    })
    .expect("the file partitions");
    let commands: Vec<&Syntax> = trees
        .commands
        .iter()
        .filter(|tree| !matches!(tree, Syntax::Node { kind, .. } if kind.to_display_string() == "Lean.Parser.Command.eoi"))
        .collect();
    assert_eq!(commands.len(), 15);
    let mut verso = 0;
    for pin in commands {
        let start = first_position(pin).expect("a positioned command");
        let bytes = parts
            .iter()
            .find(|(offset, _)| offset.0 + body_start == start)
            .map(|(_, bytes)| *bytes)
            .unwrap_or_else(|| panic!("no command starts at {start}"));
        let text = String::from_utf8_lossy(bytes).into_owned();
        let current = grammar.grammar();
        let ours = match with_grammar(&current, || command_scope::parse(bytes)) {
            Ok(Some(scope)) => {
                let tree = with_grammar(&current, || command_scope::trees::tree(bytes));
                grammar.apply(&scope);
                tree.unwrap_or_else(|error| panic!("{text}: {error:?}"))
                    .unwrap_or_else(|| panic!("{text}: no tree"))
            }
            _ => with_grammar(&current, || parse_source_command(bytes))
                .unwrap_or_else(|error| panic!("{text}: {error:?}"))
                .syntax()
                .clone(),
        };
        if let Some(difference) = difference(pin, &ours, start) {
            panic!("{text}\n{difference}");
        }
        verso += format!("{ours:?}").matches("versoCommentBody").count();
    }
    // Of the file's 11 docs, the 2 the scope leaves plain (`a6`, `a7`) are the only plain ones.
    assert_eq!(verso, 9);
}

/// A body holding a block this port does not read (a directive) keeps the plain body: one atom
/// from after the opener's whitespace through `-/`, which is what the parser built before Verso.
#[test]
fn a_body_holding_an_unread_block_keeps_the_plain_body() {
    let source = "set_option doc.verso true\n/--\n:::note\nBody.\n:::\n-/\ndef d : Nat := 1\n";
    let mut grammar = FileGrammar::new(false, &[], None).expect("Init");
    let parts = with_grammar(&grammar.grammar(), || {
        command_scope::partition(source.as_bytes())
    })
    .expect("the file partitions");
    let [(_, option), (_, declaration)] = parts.as_slice() else {
        panic!("two commands: {parts:?}");
    };
    let scope = with_grammar(&grammar.grammar(), || command_scope::parse(option))
        .expect("set_option")
        .expect("a scope command");
    grammar.apply(&scope);
    let parsed = with_grammar(&grammar.grammar(), || parse_source_command(declaration))
        .expect("the declaration parses");
    let rendered = format!("{:?}", parsed.syntax());
    assert!(!rendered.contains("versoCommentBody"), "{rendered}");
    assert!(
        rendered.contains(":::note\\nBody.\\n:::\\n-/"),
        "{rendered}"
    );
}
