//! Whole-command parse trees against the pinned Reference (bead `franken_lean-z8j.1.10`,
//! stage 2: builtin parsers producing the pin's node kinds).
//!
//! Each row is a complete command and the tree the pinned frontend produced for it, captured
//! with `scripts/extract/dump_command_syntax.lean` from `leanprover/lean4:v4.32.0` (commit
//! `8c9756b28d64dab099da31a4c09229a9e6a2ef35`) on 2026-10-05:
//!
//! ```text
//! T=~/.elan/toolchains/leanprover--lean4---v4.32.0
//! $T/bin/lean --run scripts/extract/dump_command_syntax.lean FILE.lean "$T"
//! ```
//!
//! The capture is `Syntax.toString`, with runs of whitespace collapsed to one space. There is no
//! update mode: a row changes only by re-running the capture and reviewing the difference.
//!
//! The comparison is exact over node kinds, child order, null nodes, atom spellings and
//! identifier names, through [`render`], which prints FrankenLean's tree in the same vocabulary.
//! It excludes source positions and trivia. The tree on our side is the one the check-source
//! engine elaborates: `parse_definition`'s.

#![forbid(unsafe_code)]

use fln_parse::{DefinitionParseError, NatDefinitionParseError, parse_definition};
use fln_syntax::source::BytePos;
use fln_syntax::tree::Syntax;

/// A command the pin accepts, and its tree.
struct Accepted {
    source: &'static str,
    tree: &'static str,
}

/// A command the pin refuses, the pin's message, and the byte of the token it names.
struct Refused {
    source: &'static str,
    message: &'static str,
    at: usize,
}

/// Declaration modifiers, `declModifiers` slots 2..6 (`Lean/Parser/Command.lean:114`).
const MODIFIERS: &[Accepted] = &[
    Accepted {
        source: "protected def bar : Nat := 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) (Command.definition "def" (Command.declId `bar []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private def a : Nat := 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.definition "def" (Command.declId `a []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "noncomputable def b : Nat := 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [(Command.noncomputable "noncomputable")] [] []) (Command.definition "def" (Command.declId `b []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "2") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private protected noncomputable unsafe partial def c (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [(Command.protected "protected")] [(Command.noncomputable "noncomputable")] [(Command.unsafe "unsafe")] [(Command.partial "partial")]) (Command.definition "def" (Command.declId `c []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[simp] protected theorem d : 1 = 1 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] []))] "]")] [] [(Command.protected "protected")] [] [] []) (Command.theorem "theorem" (Command.declId `d []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (num "1") "=" (num "1")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "protected theorem e : 2 = 2 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) (Command.theorem "theorem" (Command.declId `e []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (num "2") "=" (num "2")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "nonrec def f : Nat := 3",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] [(Command.nonrec "nonrec")]) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "3") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "public def g : Nat := 4",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.public "public")] [] [] [] []) (Command.definition "def" (Command.declId `g []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "4") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private\ndef h : Nat := 5",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.definition "def" (Command.declId `h []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "5") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "unsafe def i : Nat := 6",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [(Command.unsafe "unsafe")] []) (Command.definition "def" (Command.declId `i []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "6") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private example : 1 = 1 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.example "example" (Command.optDeclSig [] [(Term.typeSpec ":" («term_=_» (num "1") "=" (num "1")))]) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
];

/// `instance` without a name (`optional declId`): the elaborator generates the name.
const ANONYMOUS_INSTANCES: &[Accepted] = &[
    Accepted {
        source: "instance : Inhabited Nat := Inhabited.mk 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(num "0")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "instance (priority := 50) : Inhabited Nat := Inhabited.mk 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [(Command.namedPrio "(" "priority" ":=" (num "50") ")")] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(num "0")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "instance {α : Type} [Inhabited α] : Inhabited (List α) := Inhabited.mk []",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [])] "}") (Term.instBinder "[" [] (Term.app `Inhabited [`α]) "]")] (Term.typeSpec ":" (Term.app `Inhabited [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `List [`α]) ")")]))) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(«term[_]» "[" [] "]")]) (Termination.suffix [] []) [])))"#,
    },
];

/// `⟨a, b, …⟩`: `Term.anonymousCtor`, `"⟨" >> sepBy termParser ", " (allowTrailingSep := true)
/// >> "⟩"` (`Lean/Parser/Term.lean:216`), alone, nested, with a trailing comma, as a do-`let`
/// pattern, and inside a list. The Point rows were captured after
/// `structure Point where x : Nat y : Nat`, and the do row after
/// `structure P where a : Nat b : Nat`.
const ANONYMOUS_CONSTRUCTORS: &[Accepted] = &[
    Accepted {
        source: "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [`hp "," `hq] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def u : Unit := ⟨⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `u []) (Command.optDeclSig [] [(Term.typeSpec ":" `Unit)]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [] "⟩") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "instance : Add P := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Add [`P]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.anonymousCtor "⟨" [(«term_+_» `a.x "+" `b.x) "," («term_+_» `a.y "+" `b.y)] "⟩")))] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def p : Point := ⟨1, 2,⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p []) (Command.optDeclSig [] [(Term.typeSpec ":" `Point)]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "1") "," (num "2") ","] "⟩") (Termination.suffix [] []) []) []))"#,
    },
    // A `⟨…⟩` pattern before a do-`let`'s `|` fallback: the fallback scanner
    // (`matching/fallback.rs`) must count `⟨` as an opener, or `⟩` underflows its depth and
    // the alternative is refused at the `|`.
    Accepted {
        source: "def f (p : Option P) : Option Nat := do\n  let some ⟨a, b⟩ := p | none\n  pure (a + b)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" (Term.app `Option [`P])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetElse "let" [] (Term.letConfig []) (Term.app `some [(Term.anonymousCtor "⟨" [`a "," `b] "⟩")]) ":=" `p "|" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `none) [])]) [(Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `a "+" `b) ")")])) [])])]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def k : List Point := [⟨1, 2⟩, ⟨3, 4⟩]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `k []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `List [`Point]))]) (Command.declValSimple ":=" («term[_]» "[" [(Term.anonymousCtor "⟨" [(num "1") "," (num "2")] "⟩") "," (Term.anonymousCtor "⟨" [(num "3") "," (num "4")] "⟩")] "]") (Termination.suffix [] []) []) []))"#,
    },
];

/// Malformed `⟨…⟩`, refused at the pin's token. Captured as above (the pin's columns count
/// code points; `at` is the byte offset in `source`).
const ANONYMOUS_CONSTRUCTOR_REFUSALS: &[Refused] = &[
    Refused {
        source: "def p : Point := ⟨1,, 2⟩",
        message: "4:20: error: unexpected token ','; expected '⟩'",
        at: 22,
    },
    Refused {
        source: "def p : Point := ⟨,⟩",
        message: "4:18: error: unexpected token ','; expected '⟩'",
        at: 20,
    },
];

/// Modifiers out of the pin's order: the pin stops at the first one it cannot place.
const MODIFIER_REFUSALS: &[Refused] = &[
    Refused {
        source: "protected private def j : Nat := 7",
        message: "1:9: error: unexpected token 'private'; expected 'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'structure' or 'theorem'",
        at: 10,
    },
    Refused {
        source: "unsafe protected def k : Nat := 8",
        message: "1:6: error: unexpected token 'protected'; expected 'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'structure' or 'theorem'",
        at: 7,
    },
];

/// FrankenLean's tree in the pin's `Syntax.toString` vocabulary, on one line.
fn render(syntax: &Syntax, out: &mut String) {
    match syntax {
        Syntax::Missing => out.push_str("<missing>"),
        Syntax::Atom { val, .. } => out.push_str(&format!("{:?}", val.as_str())),
        Syntax::Ident { val, .. } => {
            out.push('`');
            out.push_str(&val.to_display_string());
        }
        Syntax::Node { kind, args, .. } => {
            let display = kind.to_display_string();
            if display == "null" {
                out.push('[');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    render(arg, out);
                }
                out.push(']');
                return;
            }
            let shown = display.strip_prefix("Lean.Parser.").unwrap_or(&display);
            let plain = shown.split('.').all(|part| {
                !part.is_empty()
                    && part
                        .chars()
                        .all(|c| c.is_alphanumeric() || matches!(c, '_' | '!' | '?' | '\''))
            });
            out.push('(');
            if plain {
                out.push_str(shown);
            } else {
                out.push('«');
                out.push_str(shown);
                out.push('»');
            }
            for arg in args {
                out.push(' ');
                render(arg, out);
            }
            out.push(')');
        }
    }
}

fn rendered(source: &str) -> Result<String, DefinitionParseError> {
    let parsed = parse_definition(source.as_bytes())?;
    let mut out = String::new();
    render(parsed.syntax(), &mut out);
    Ok(out)
}

#[test]
fn declaration_modifiers_produce_the_pins_trees() {
    for row in MODIFIERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn anonymous_instances_produce_the_pins_trees() {
    for row in ANONYMOUS_INSTANCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn anonymous_constructors_produce_the_pins_trees() {
    for row in ANONYMOUS_CONSTRUCTORS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn modifiers_out_of_order_are_refused_at_the_pins_token() {
    refusals_agree(MODIFIER_REFUSALS);
}

#[test]
fn malformed_anonymous_constructors_are_refused_at_the_pins_token() {
    refusals_agree(ANONYMOUS_CONSTRUCTOR_REFUSALS);
}

fn refusals_agree(rows: &[Refused]) {
    for row in rows {
        // The pin reports the end of the preceding token; the token it names comes next.
        let named = row
            .message
            .split('\'')
            .nth(1)
            .expect("the message names a token");
        assert_eq!(
            &row.source[row.at..row.at + named.len()],
            named,
            "{}",
            row.source
        );
        match parse_definition(row.source.as_bytes()) {
            Err(NatDefinitionParseError::OutsideSeedGrammar { at, .. }) => {
                assert_eq!(at, BytePos(row.at), "{}", row.source);
            }
            other => panic!(
                "{}: the pin refuses ({}), got {other:?}",
                row.source, row.message
            ),
        }
    }
}

/// The renderer is not vacuous: a tree with a modifier moved to another slot renders
/// differently from the pin's row, so the fixture can tell the slots apart.
#[test]
fn a_misplaced_modifier_does_not_render_as_the_pins_tree() {
    let pin = MODIFIERS[0].tree;
    let moved = pin.replacen(
        r#"[] [] [] [(Command.protected "protected")] [] [] []"#,
        r#"[] [] [(Command.protected "protected")] [] [] [] []"#,
        1,
    );
    assert_ne!(moved, pin);
    assert_ne!(rendered(MODIFIERS[0].source).unwrap(), moved);
}
