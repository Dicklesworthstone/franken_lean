//! Syntax extensions in the production parser (`fln_parse::extensions`; bead
//! `franken_lean-z8j.1.10`, stages 3 and 4).
//!
//! Pin-free: the census is read as checked in, and every expectation below is a census row or a
//! pin tree kind captured from it. What the pin's own files do with these declarations is
//! measured by frontier A (`tests/pin_syntax_frontier.rs`), which also checks every declaration
//! the translator registers for an Init or Std file against that module's census row.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::command_scope::{self, ScopeCommand};
use fln_parse::extensions::{
    Descr, ExtensionCensus, FileGrammar, extension_census, rendered_name, with_grammar,
};
use fln_parse::parse_source_command;
use fln_parse::reference_tokens::GRAMMAR_CENSUS;
use fln_syntax::tree::Syntax;

fn name(text: &str) -> Name {
    rendered_name(text).expect("a rendered name")
}

fn kinds(syntax: &Syntax) -> Vec<Name> {
    let mut out = Vec::new();
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            out.push(kind.clone());
            pending.extend(args.iter().rev());
        }
    }
    out
}

/// A file's grammar after these scope and syntax commands, each parsed as the frontier parses it.
fn grammar_after(imports: &[&str], commands: &[&str]) -> FileGrammar {
    let imports: Vec<Name> = imports.iter().map(|module| name(module)).collect();
    let mut grammar =
        FileGrammar::new(false, &imports, Some(name("Test.Extensions"))).expect("census modules");
    for command in commands {
        let current = grammar.grammar();
        match with_grammar(&current, || command_scope::parse(command.as_bytes())) {
            Ok(Some(scope)) => grammar.apply(&scope),
            Ok(None) => {
                let parsed = with_grammar(&current, || parse_source_command(command.as_bytes()))
                    .unwrap_or_else(|error| panic!("{command}: {error:?}"));
                grammar
                    .declare(parsed.syntax())
                    .unwrap_or_else(|reason| panic!("{command}: {reason}"));
            }
            Err(error) => panic!("{command}: {error:?}"),
        }
    }
    grammar
}

#[test]
fn the_census_descriptions_parse_and_count() {
    let census = extension_census();
    assert_eq!(
        census.decls().len(),
        957,
        "every Init/Std syntax declaration has its description"
    );
    let wf = census
        .decls()
        .iter()
        .find(|decl| decl.decl == name("Std.DTreeMap.Internal.Impl.tacticWf_trivial"))
        .expect("the census row");
    assert_eq!(wf.scope, Some(name("Std.DTreeMap.Internal.Impl")));
    assert_eq!(
        wf.descr,
        Descr::parse(
            r#"(node "Std.DTreeMap.Internal.Impl.tacticWf_trivial" 1024 (nonReservedSymbol "wf_trivial" false))"#
        )
        .expect("a description")
    );
}

#[test]
fn malformed_descriptions_and_censuses_are_refused() {
    for text in [
        "",
        "(symbol)",
        r#"(symbol "a""#,
        r#"(symbol "a") extra"#,
        r#"(frobnicate "a")"#,
        r#"(cat "term" x)"#,
        r#"(nonReservedSymbol "a" maybe)"#,
    ] {
        assert!(Descr::parse(text).is_err(), "{text:?} must be refused");
    }
    // A description row dropped without its count is refused, never a smaller table.
    let first = GRAMMAR_CENSUS
        .lines()
        .find(|line| line.starts_with("syntax-descr\t"))
        .expect("a description row");
    let truncated = GRAMMAR_CENSUS.replacen(&format!("{first}\n"), "", 1);
    assert!(ExtensionCensus::parse(&truncated).is_err());
}

#[test]
fn scoped_notation_is_active_exactly_where_its_namespace_is() {
    let imports = ["Std.Data.DHashMap.Basic"];
    let outside = grammar_after(&imports, &[]);
    assert!(
        !outside.grammar().table().contains("~m"),
        "scoped: not active by import alone"
    );
    let inside = grammar_after(&imports, &["namespace Std.DHashMap"]);
    assert!(
        inside.grammar().table().contains("~m"),
        "namespace activates it"
    );
    let closed = grammar_after(&imports, &["namespace Std.DHashMap", "end Std.DHashMap"]);
    assert!(
        !closed.grammar().table().contains("~m"),
        "`end` restores the activation"
    );
    let opened = grammar_after(&imports, &["open Std.DHashMap"]);
    assert!(
        opened.grammar().table().contains("~m"),
        "`open` activates it"
    );
    let relative = grammar_after(&imports, &["namespace Std", "open DHashMap"]);
    assert!(
        relative.grammar().table().contains("~m"),
        "`open` resolves against the current namespace"
    );
    let sectioned = grammar_after(&imports, &["section", "open Std.DHashMap", "end"]);
    assert!(
        !sectioned.grammar().table().contains("~m"),
        "a section's `open` ends with it"
    );
    // `open … in` for the one command.
    let base = grammar_after(&imports, &[]);
    assert!(
        base.grammar_opening(&[name("Std.DHashMap")])
            .table()
            .contains("~m")
    );
    // Not imported: never active.
    let elsewhere = grammar_after(&["Init.Data.List.Basic"], &["namespace Std.DHashMap"]);
    assert!(!elsewhere.grammar().table().contains("~m"));
}

#[test]
fn an_imported_scoped_infix_parses_as_its_declared_kind() {
    let source = "theorem t (m₁ m₂ : Nat) (h : m₁ ~m m₂) : True := trivial";
    // Production, with no grammar entered, refuses the notation it does not have.
    assert!(parse_source_command(source.as_bytes()).is_err());
    let grammar = grammar_after(&["Std.Data.DHashMap.Basic"], &["namespace Std.DHashMap"]);
    let parsed = with_grammar(&grammar.grammar(), || {
        parse_source_command(source.as_bytes())
    })
    .expect("the active notation parses");
    assert!(
        kinds(parsed.syntax()).contains(&name("Std.DHashMap.«term_~m_»")),
        "{:?}",
        kinds(parsed.syntax())
    );
}

#[test]
fn an_imported_global_infix_parses_and_a_scoped_one_needs_its_namespace() {
    // `List.«term_<+_»` is `scoped infixl:50 " <+ "` (Init/Data/List/Basic.lean).
    let source = "theorem t (l₁ l₂ : List Nat) (h : l₁ <+ l₂) : True := trivial";
    let closed = grammar_after(&["Init.Data.List.Basic"], &[]);
    assert!(
        with_grammar(&closed.grammar(), || parse_source_command(
            source.as_bytes()
        ))
        .is_err()
    );
    let open = grammar_after(&["Init.Data.List.Basic"], &["open List"]);
    let parsed = with_grammar(&open.grammar(), || parse_source_command(source.as_bytes()))
        .expect("parses under `open List`");
    assert!(kinds(parsed.syntax()).contains(&name("List.«term_<+_»")));
}

#[test]
fn a_file_declared_tactic_matches_its_census_row_and_parses() {
    // The declaration `Std/Data/DTreeMap/Internal/Lemmas.lean` makes, in its namespace.
    let grammar = grammar_after(
        &["Init"],
        &[
            "namespace Std.DTreeMap.Internal.Impl",
            "scoped syntax \"simp_to_model\" (\" [\" (ident,*) \"]\")? (\"using\" term)? : tactic",
            "scoped syntax \"wf_trivial\" : tactic",
        ],
    );
    let census = extension_census();
    for declared in grammar.declared() {
        let row = census
            .decls()
            .iter()
            .find(|decl| decl.decl == declared.decl)
            .unwrap_or_else(|| panic!("no census row named {}", declared.decl.to_display_string()));
        assert_eq!(row.descr, declared.descr);
        assert_eq!(row.scope, declared.scope);
        assert_eq!(row.priority, declared.priority);
        assert_eq!(row.category, declared.category);
    }
    assert_eq!(grammar.declared().len(), 2);
    let source = "theorem t : True := by\n  simp_to_model [insert, isEmpty] using List.isEmpty_insertEntry\n";
    let parsed = with_grammar(&grammar.grammar(), || {
        parse_source_command(source.as_bytes())
    })
    .expect("the declared tactic parses");
    assert!(kinds(parsed.syntax()).contains(&name(
        "Std.DTreeMap.Internal.Impl.«tacticSimp_to_model[_]Using_»"
    )));
    // Outside its namespace the scoped tactic is gone.
    let mut closed = grammar_after(&["Init"], &[]);
    closed.apply(&ScopeCommand::Namespace(name("Other")));
    assert!(
        with_grammar(&closed.grammar(), || parse_source_command(
            source.as_bytes()
        ))
        .is_err()
    );
}

#[test]
fn infix_notation_names_and_precedences_follow_the_pin() {
    // `infixl:50 " ~ " => Perm` in namespace `List` is the census row `List.«term_~_»`, so
    // with `Init` imported the name is taken and a declaration there gets the next fresh one,
    // as `elabSyntax`'s loop gives it; in a namespace where it is free it is the base name.
    let taken = grammar_after(&["Init"], &["namespace List", "infixl:50 \" ~ \" => Perm"]);
    assert_eq!(taken.declared()[0].decl, name("List.«term_~__1»"));
    let grammar = grammar_after(
        &["Init"],
        &[
            "namespace Test",
            "infixl:50 \" ~ \" => Perm",
            "infixr:67 \" ::: \" => foo",
            "infixl:50 \" ~ \" => Perm",
        ],
    );
    let declared: Vec<_> = grammar.declared().iter().collect();
    assert_eq!(declared[0].decl, name("Test.«term_~_»"));
    assert_eq!(
        declared[0].descr,
        Descr::parse(
            r#"(trailingNode "Test.«term_~_»" 50 50 (binary "andthen" (symbol " ~ ") (cat "term" 51)))"#
        )
        .expect("a description")
    );
    assert_eq!(
        declared[1].descr,
        Descr::parse(
            r#"(trailingNode "Test.«term_:::_»" 67 68 (binary "andthen" (symbol " ::: ") (cat "term" 67)))"#
        )
        .expect("a description")
    );
    assert_eq!(declared[2].decl, name("Test.«term_~__1»"));
}

#[test]
fn two_active_infix_notations_are_the_pins_choice_most_recent_first() {
    // `namespace Std.DTreeMap.Raw` activates `Std.DTreeMap`, then `Std.DTreeMap.Raw`: both `~m`
    // read the input, and the pin's tree (captured with `scripts/extract/dump_command_syntax.lean`
    // on 2026-10-09) is `(choice (Std.DTreeMap.Raw.«term_~m_» …) (Std.DTreeMap.«term_~m_» …))`.
    let grammar = grammar_after(
        &["Std.Data.DTreeMap.Raw.Basic"],
        &["namespace Std.DTreeMap.Raw"],
    );
    let source = "theorem t (t₁ t₂ : Nat) (h : t₁ ~m t₂) : True := trivial";
    let parsed = with_grammar(&grammar.grammar(), || {
        parse_source_command(source.as_bytes())
    })
    .expect("parses");
    let found = kinds(parsed.syntax());
    let choice = found
        .iter()
        .position(|kind| *kind == name("choice"))
        .expect("a choice node");
    assert_eq!(
        found[choice + 1..choice + 3],
        [
            name("Std.DTreeMap.Raw.«term_~m_»"),
            name("Std.DTreeMap.«term_~m_»")
        ]
    );
}

#[test]
fn an_atom_like_notation_is_an_operand_an_application_head_and_a_pattern() {
    // `notation "-[" n "+1]" => negSucc n`, scoped in `Int` (Init/Data/Int/Basic.lean).
    let int = grammar_after(&["Init.Data.Int.Basic"], &["open Int"]);
    for source in [
        "def f : Int → Nat\n  | -[n+1] => n\n  | _ => 0\n",
        "theorem g (n : Nat) : f -[n+1] = n := rfl\n",
    ] {
        let parsed = with_grammar(&int.grammar(), || parse_source_command(source.as_bytes()))
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            kinds(parsed.syntax()).contains(&name("Int.«term-[_+1]»")),
            "{source}"
        );
    }
    // `syntax "wp⟦" term (":" term)? "⟧" : term` at `max`: an application's head (`wp⟦x⟧ Q`).
    let wp = grammar_after(&["Std.Do.WP.Basic"], &["open Std.Do"]);
    let source = "theorem t (x : Nat) : wp⟦x⟧ Q = Q := rfl";
    let parsed =
        with_grammar(&wp.grammar(), || parse_source_command(source.as_bytes())).expect("parses");
    let found = kinds(parsed.syntax());
    assert!(found.contains(&name("Lean.Parser.Term.app")));
    assert!(found.contains(&name("Std.Do.«termWp⟦_:_⟧»")));
    // Without the namespace the notation is not there.
    let closed = grammar_after(&["Std.Do.WP.Basic"], &[]);
    assert!(
        with_grammar(&closed.grammar(), || parse_source_command(
            source.as_bytes()
        ))
        .is_err()
    );
}

#[test]
fn a_declared_category_takes_its_syntax_and_its_quotation_token() {
    let grammar = grammar_after(
        &["Init"],
        &[
            "declare_syntax_cat widget (behavior := both)",
            "syntax \"knob\" ident : widget",
        ],
    );
    assert!(grammar.grammar().table().contains("`(widget|"));
    let [declared] = grammar.declared() else {
        panic!("one declaration");
    };
    assert_eq!(declared.category, Some(name("widget")));
    // `both`: the first atom is non-reserved, so `knob` does not become a keyword.
    assert_eq!(
        declared.descr,
        Descr::parse(
            r#"(node "widgetKnob_" 1022 (binary "andthen" (nonReservedSymbol "knob" false) (const "ident")))"#
        )
        .expect("a description")
    );
    assert!(!grammar.grammar().table().contains("knob"));
}

#[test]
fn a_leading_command_the_partition_does_not_recognise_stays_its_own() {
    // `Init/Data/List/Lemmas.lean`: `grind_annotated "…"` right after the header, then
    // `public section`, which is a command of its own at the pin.
    let body = "grind_annotated \"2025-01-24\"\n\npublic section\n";
    let parts = command_scope::partition(body.as_bytes()).expect("partitions");
    let starts: Vec<usize> = parts.iter().map(|(start, _)| start.0).collect();
    assert_eq!(starts, vec![0, body.find("public").expect("section")]);
    // Leading trivia stays with the first command.
    let commented = "-- note\ndef x := 1\n";
    let parts = command_scope::partition(commented.as_bytes()).expect("partitions");
    assert_eq!(parts.len(), 1);
}

#[test]
fn rendered_names_read_numeric_components_and_escapes() {
    let private = name("_private.Std.Time.0.termInt32");
    assert_eq!(
        private,
        Name::num(Name::from_components(["_private", "Std", "Time"]), 0)
            .append_core(&Name::from_components(["termInt32"]))
    );
    // An escaped component that reads as digits is a string.
    assert_eq!(name("«0»"), Name::from_components(["0"]));
    assert_eq!(
        name("A.«term_~m_»"),
        Name::from_components(["A", "term_~m_"])
    );
    assert!(rendered_name("A..B").is_none());
    assert!(rendered_name("«open").is_none());
}

#[test]
fn interpolated_strings_are_chunks_around_terms() {
    // `syntax "s!" interpolatedStr(term) : term` (`termS!_`); the tree is the pin's
    // `(termS!_ "s!" (interpolatedStrKind (interpolatedStrLitKind "\"a{") x
    // (interpolatedStrLitKind "}b{") (term_+_ …) (interpolatedStrLitKind "}\"")))`.
    let grammar = grammar_after(&["Init"], &[]);
    let parse = |source: &str| {
        with_grammar(&grammar.grammar(), || {
            parse_source_command(source.as_bytes())
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    };
    let parsed = parse("def f (x : Nat) : String := s!\"a{x}b{x + 1}\"");
    let found = kinds(parsed.syntax());
    let chunks = found
        .iter()
        .filter(|kind| **kind == name("interpolatedStrLitKind"))
        .count();
    assert_eq!(chunks, 3);
    assert!(found.contains(&name("termS!_")));
    assert!(found.contains(&name("term_+_")));
    // A string inside a hole, holding a `}`, is the hole's own token.
    let nested = parse("def k (x : String) : String := s!\"q{x ++ \"}\"}r\"");
    assert!(kinds(nested.syntax()).contains(&name("term_++_")));
    // No hole: one chunk.
    let plain = parse("def g : String := s!\"plain\"");
    assert_eq!(
        kinds(plain.syntax())
            .iter()
            .filter(|kind| **kind == name("interpolatedStrLitKind"))
            .count(),
        1
    );
    // Without a grammar the string is one literal and `s!` is not read.
    assert!(parse_source_command("def g : String := s!\"a{1}\"".as_bytes()).is_err());
}

#[test]
fn empty_and_abbreviated_braces_are_the_pins_choice_with_init_notation() {
    let grammar = grammar_after(&["Init"], &[]);
    let parse = |source: &str| {
        with_grammar(&grammar.grammar(), || {
            parse_source_command(source.as_bytes())
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    };
    for (source, notation) in [
        ("def e : Nat := f {}", "term{}"),
        ("def e : Nat := f {a, b}", "term{_}"),
    ] {
        let found = kinds(parse(source).syntax());
        let choice = found
            .iter()
            .position(|kind| *kind == name("choice"))
            .unwrap_or_else(|| panic!("{source}: no choice"));
        assert_eq!(
            found[choice + 1],
            Name::from_components([notation]),
            "{source}"
        );
        assert!(found[choice + 1..].contains(&name("Lean.Parser.Term.structInst")));
    }
    // A field with a value or a source is only a structure instance.
    for source in [
        "def e : Nat := f {a := 1}",
        "def e : Nat := f {s with a := 1}",
    ] {
        assert!(
            !kinds(parse(source).syntax()).contains(&name("choice")),
            "{source}"
        );
    }
    // Without the notation (no grammar entered) there is no second reading.
    let plain = parse_source_command("def e : Nat := f {}".as_bytes()).expect("parses");
    assert!(!kinds(plain.syntax()).contains(&name("choice")));
}

/// An attribute the census declares by `syntax … : attr` is read by that declaration where the
/// file imports it (`@[bv_normalize]` under `Std.Tactic.BVDecide.Syntax`), and as `Attr.simple`
/// where it does not: `Init.Prelude`'s `@[simp]` comes before `Init.Tactics` declares `simp`.
/// Without a grammar, and under one that enters only the file's own syntax, the hand reader's
/// trees stand.
#[test]
fn a_census_attribute_is_read_by_its_declaration_only_where_imported() {
    let parse = |grammar: &FileGrammar, source: &str| {
        with_grammar(&grammar.grammar(), || {
            parse_source_command(source.as_bytes())
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    };
    let bv = grammar_after(&["Std.Tactic.BVDecide.Syntax"], &[]);
    let found = kinds(parse(&bv, "@[bv_normalize] theorem t : True := trivial").syntax());
    assert!(
        found.contains(&name("Lean.Parser.bv_normalize")),
        "{found:?}"
    );
    let simp = "@[simp] theorem t : True := trivial";
    let prelude = FileGrammar::new(true, &[], Some(name("Test.Extensions"))).expect("prelude");
    let found = kinds(parse(&prelude, simp).syntax());
    assert!(
        found.contains(&name("Lean.Parser.Attr.simple")),
        "{found:?}"
    );
    assert!(!found.contains(&name("Lean.Parser.Attr.simp")), "{found:?}");
    let init = grammar_after(&["Init"], &[]);
    assert!(kinds(parse(&init, simp).syntax()).contains(&name("Lean.Parser.Attr.simp")));
    let own = FileGrammar::new(true, &[], Some(name("Test.Extensions")))
        .expect("prelude")
        .own_syntax_only();
    assert!(kinds(parse(&own, simp).syntax()).contains(&name("Lean.Parser.Attr.simp")));
    let plain = parse_source_command(simp.as_bytes()).expect("parses");
    assert!(kinds(plain.syntax()).contains(&name("Lean.Parser.Attr.simp")));
}

/// The production paths enter only the file's own syntax (`FileGrammar::own_syntax_only`): Init's
/// collection notations are not entered, so `{}` stays the structure instance their elaborator
/// reads, while the file's own notation parses, its token lexing over Init's table.
#[test]
fn own_syntax_only_enters_the_files_declarations_and_not_the_imports() {
    let mut grammar = FileGrammar::new(false, &[], Some(name("Test.Extensions")))
        .expect("Init")
        .own_syntax_only();
    let declaration = "notation \"⟪\" n \"⟫\" => Nat.add n n";
    let parsed = with_grammar(&grammar.grammar(), || {
        parse_source_command(declaration.as_bytes())
    })
    .expect("the declaration parses");
    let declared = grammar
        .declare(parsed.syntax())
        .expect("translates")
        .expect("declares");
    let parse = |source: &str| {
        with_grammar(&grammar.grammar(), || {
            parse_source_command(source.as_bytes())
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    };
    for source in ["def e : Nat := f {}", "def e : Nat := f {a, b}"] {
        let found = kinds(parse(source).syntax());
        assert!(!found.contains(&name("choice")), "{source}");
        assert!(
            found.contains(&name("Lean.Parser.Term.structInst")),
            "{source}"
        );
    }
    assert!(kinds(parse("def e : Nat := ⟪1⟫").syntax()).contains(&declared.decl));
}

/// The `lean` door's partition (`partition_source_module`) leaves a token the file declares later
/// to the command that holds it, as `command_scope::partition` does: that command's parse decides,
/// with the grammar in effect there. Nothing is declared in the import header, so an unknown
/// token there still refuses the source.
#[test]
fn a_module_partition_leaves_an_undeclared_token_to_its_command() {
    let source = "notation \"⟪\" n \"⟫\" => n\n#eval ⟪21⟫\n";
    let partitioned = fln_parse::partition_source_module(source.as_bytes()).expect("partitions");
    assert_eq!(partitioned.commands.len(), 2);
    assert!(partitioned.commands[1].1.starts_with(b"#eval"));
    assert!(fln_parse::partition_source_module(b"import Init \xe2\x9f\xaa\ndef x := 1\n").is_err());
    // An unterminated string runs past its command: still the whole source's refusal.
    assert!(fln_parse::partition_source_module(b"def x := 1\ndef s := \"open\n").is_err());
}

#[test]
fn a_prefix_notation_starts_an_operand_and_the_same_symbol_is_infix_after_one() {
    // `Std.Do.«term⊢ₛ_»` is `node 25 (andthen (symbol "⊢ₛ ") (cat term 25))`, and
    // `Std.Do.«term_⊢ₛ_»` the infix on the same symbol (Std/Do/SPred/Notation.lean).
    let grammar = grammar_after(&["Std.Do.SPred.Notation"], &["open Std.Do"]);
    let source = "theorem t (P Q : Prop) : (⊢ₛ P → Q) ↔ (P ⊢ₛ Q) := rfl";
    let parsed = with_grammar(&grammar.grammar(), || {
        parse_source_command(source.as_bytes())
    })
    .expect("parses");
    let found = kinds(parsed.syntax());
    assert!(found.contains(&name("Std.Do.«term⊢ₛ_»")));
    assert!(found.contains(&name("Std.Do.«term_⊢ₛ_»")));
    // The prefix's operand is read at 25: the arrow (`infixr:25`) is inside it.
    let prefix = found
        .iter()
        .position(|kind| *kind == name("Std.Do.«term⊢ₛ_»"))
        .expect("the prefix node");
    assert_eq!(found[prefix + 1], name("Lean.Parser.Term.arrow"));
}

/// `prefix:max "√" => f` is `notation:max "√" arg:max` (`expandMixfix`): its operand is one
/// argument, and the node, at `max`, heads an application (`√x y` is `(√x) y` at the pin).
#[test]
fn a_max_prefix_notation_takes_one_argument() {
    let grammar = grammar_after(&["Init"], &["prefix:max \"√\" => Nat.succ"]);
    let parse = |source: &str| {
        with_grammar(&grammar.grammar(), || {
            parse_source_command(source.as_bytes())
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    };
    let prefix = grammar.declared()[0].decl.clone();
    let found = kinds(parse("def e (f : Nat → Nat) (x : Nat) : Nat := f (√x)").syntax());
    assert!(found.contains(&prefix), "{found:?}");
    // A literal is one argument too.
    assert!(kinds(parse("def e : Nat := √2").syntax()).contains(&prefix));
    let found = kinds(parse("def e (x : Nat) : Nat := √(x + 1)").syntax());
    let at = found
        .iter()
        .position(|kind| *kind == prefix)
        .expect("the prefix node");
    assert_eq!(found[at + 1], name("Lean.Parser.Term.paren"));
    // `√g x`: the application's head is the prefix node over `g` alone.
    let found = kinds(parse("def e (g : Nat → Nat) (x : Nat) : Nat := √g x").syntax());
    let app = found
        .iter()
        .position(|kind| *kind == name("Lean.Parser.Term.app"))
        .expect("an application");
    assert_eq!(found[app + 1], prefix, "{found:?}");
}

/// The identifiers of a tree, in source order.
fn idents(syntax: &Syntax) -> Vec<Name> {
    let mut out = Vec::new();
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Ident { val, .. } => out.push(val.clone()),
            Syntax::Node { args, .. } => pending.extend(args.iter().rev()),
            _ => {}
        }
    }
    out
}

#[test]
fn a_declared_notation_expands_hygienically() {
    let mut grammar = grammar_after(
        &["Init"],
        &[
            "infixl:65 \" +++ \" => myAppend",
            "notation \"twice\" x => (fun y => y + y) x",
        ],
    );
    let parse = |grammar: &FileGrammar, source: &str| {
        with_grammar(&grammar.grammar(), || {
            parse_source_command(source.as_bytes())
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    };
    // `expandMixfix`: `a +++ b` is `myAppend a b`, the template's `myAppend` macro-scoped so
    // that a use-site local `myAppend` cannot capture it; the operands are the use's own.
    let parsed = parse(&grammar, "def r (a b : Nat) : Nat := a +++ b");
    let expanded = grammar.expand(parsed.syntax()).expect("expands");
    let found = idents(&expanded);
    let head = found
        .iter()
        .find(|name| name.erase_macro_scopes() == name_of("myAppend"))
        .expect("the template's function");
    assert!(head.has_macro_scopes(), "{head:?}");
    assert!(kinds(&expanded).contains(&name("Lean.Parser.Term.app")));
    assert!(!kinds(&expanded).contains(&name("«term_+++_»")));
    assert!(found.contains(&name_of("a")) && found.contains(&name_of("b")));
    // `elabNotation`'s `macro_rules`: `x` is the child, the template's own binder `y` and its
    // uses share one fresh scope, distinct from the next expansion's.
    let parsed = parse(&grammar, "def s (n : Nat) : Nat := twice n + twice n");
    let expanded = grammar.expand(parsed.syntax()).expect("expands");
    let scoped: Vec<Name> = idents(&expanded)
        .into_iter()
        .filter(|name| name.erase_macro_scopes() == name_of("y"))
        .collect();
    assert_eq!(
        scoped.len(),
        6,
        "a binder and two uses per expansion: {scoped:?}"
    );
    assert!(scoped.iter().all(Name::has_macro_scopes));
    assert_eq!(scoped[0], scoped[2]);
    assert_ne!(scoped[0], scoped[3], "each expansion takes a fresh scope");
    assert!(idents(&expanded).contains(&name_of("n")));
}

fn name_of(text: &str) -> Name {
    Name::from_components([text])
}
