//! The grammar census and the lexer table derived from it (beads `fln-vokf`,
//! `fln-notation-from-imports-0edr`; Rule D5).
//!
//! Pin-free: both census files are read as checked in. Drift against the pin is
//! `scripts/extract/gen_grammar_census.sh --check`, which regenerates them from the pinned
//! Reference and compares bytes; these tests hold what the files must satisfy and what the
//! production lexer must do with them.
//!
//! * **Derivation.** The production table holds exactly the census's tokens for an ordinary
//!   file — nothing added by hand — and the closure rule reproduces the table sizes the oracle
//!   itself measured (`closure-check` rows).
//! * **The planted check.** Removing one census row removes exactly that token: `⟨` stops
//!   lexing. A row removed without its `count` is refused, never a smaller table.
//! * **Totality of the kind-use census.** Every Init/Std file was replayed with zero errors, the
//!   file set is the module set, and every syntax kind those files use is a kind the grammar
//!   census registers.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::reference_tokens::{
    CensusError, GRAMMAR_CENSUS, TokenCensus, UnknownModule, header_table, implicit_init_table,
    reference_census,
};
use fln_parse::{NatDefinitionParseError, parse_definition, parse_source_command};
use fln_syntax::source::{BytePos, SourceText};
use fln_syntax::token::{TokenError, TokenKind, TokenTable, lex_token};
use std::collections::{BTreeMap, BTreeSet};

const KIND_USE: &str = include_str!("../../../contracts/REFERENCE_SYNTAX_KIND_USE.txt");

fn rows<'a>(text: &'a str, tag: &'a str) -> impl Iterator<Item = Vec<&'a str>> + 'a {
    text.lines()
        .filter(|line| !line.starts_with('#'))
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .filter(move |fields| fields[0] == tag)
}

fn count(text: &str, what: &str) -> usize {
    let found: Vec<usize> = rows(text, "count")
        .filter(|fields| fields[1] == what)
        .map(|fields| fields[2].parse().expect("a count is a numeral"))
        .collect();
    assert_eq!(found.len(), 1, "exactly one count row for {what}");
    found[0]
}

fn lex_one(table: &TokenTable, raw: &str) -> Result<TokenKind, TokenError> {
    let text = SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8");
    lex_token(&text, table, BytePos(0)).map(|lexed| lexed.kind)
}

fn module(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

#[test]
fn the_production_table_is_exactly_the_census_table_for_an_ordinary_file() {
    let census = reference_census();
    let derived = census.tokens_for(false, &[]).expect("Init is in the census");
    let production: BTreeSet<String> = implicit_init_table()
        .tokens()
        .into_iter()
        .map(str::to_string)
        .collect();
    assert_eq!(
        production, derived,
        "the production lexer table must be the census table, with nothing added by hand"
    );
    for token in census.builtin_tokens() {
        assert!(production.contains(token), "builtin token {token} missing");
    }
    // The measured symptoms (2026-10-04): builtin and Init tokens the hand table refused.
    for token in ["⟨", "⟩", "$", "▸", "⋯", "≤", "≥", ">", "≠", "×", "∃", "<|", "|>", "∘", "&&", "||", "sorry"] {
        assert!(production.contains(token), "{token} is a token at the pin");
    }
    // The hand table carried a token the pin does not have.
    assert!(!production.contains("|-"), "`|-` is not a token at v4.32.0");
    // Header-only tokens are not body tokens.
    for token in census.header_only_tokens() {
        assert!(!production.contains(token), "{token} is header-only");
    }
}

#[test]
fn the_closure_rule_reproduces_every_table_the_oracle_measured() {
    let census = reference_census();
    let checks: Vec<(String, usize)> = rows(GRAMMAR_CENSUS, "closure-check")
        .map(|fields| {
            assert_eq!(fields[3], "agrees", "the extractor only publishes agreeing closures");
            let size = fields[2]
                .strip_prefix("tokens=")
                .expect("tokens=")
                .parse()
                .expect("numeral");
            (fields[1].to_string(), size)
        })
        .collect();
    assert!(checks.len() >= 6, "the oracle measured at least six closures: {checks:?}");
    for (root, size) in &checks {
        // `importModules #[root]` has no implicit Init, so it is the `prelude` closure.
        let tokens = census
            .tokens_for(true, &[module(root)])
            .expect("every sampled root is a census module");
        assert_eq!(tokens.len(), *size, "closure of {root}");
    }
    // `prelude import Init.Prelude` sees only the builtin table: `+` comes from the syntax DSL,
    // `=` and `at` from Init notation it does not import.
    let prelude = census
        .tokens_for(true, &[module("Init.Prelude")])
        .expect("Init.Prelude");
    assert_eq!(prelude.len(), census.builtin_tokens().count());
    assert!(prelude.contains("⟨") && prelude.contains("+"));
    assert!(!prelude.contains("=") && !prelude.contains("at") && !prelude.contains("≤"));
    let list_basic = census
        .tokens_for(true, &[module("Init.Data.List.Basic")])
        .expect("Init.Data.List.Basic");
    assert!(list_basic.contains("=") && list_basic.contains("≤"));
    // A module the census cannot describe is refused, not skipped.
    assert_eq!(
        census.tokens_for(true, &[module("Mathlib.Logic.Basic")]),
        Err(UnknownModule(module("Mathlib.Logic.Basic")))
    );
}

/// The planted check the bead asks for: the lexer's acceptance of `⟨` is caused by the census
/// row and by nothing else.
#[test]
fn removing_a_census_row_makes_its_token_refuse() {
    let real = TokenCensus::parse(GRAMMAR_CENSUS).expect("the checked-in census parses");
    let real_table = real.table_for(true, &[]).expect("no imports");
    assert_eq!(
        lex_one(&real_table, "⟨hp, hq⟩"),
        Ok(TokenKind::Symbol("⟨".to_string()))
    );

    let declared = count(GRAMMAR_CENSUS, "builtin-tokens");
    let row = "builtin-token\t⟨\t";
    let planted: String = GRAMMAR_CENSUS
        .lines()
        .filter(|line| !line.starts_with(row))
        .map(|line| {
            if line == format!("count\tbuiltin-tokens\t{declared}") {
                format!("count\tbuiltin-tokens\t{}\n", declared - 1)
            } else {
                format!("{line}\n")
            }
        })
        .collect();
    assert_eq!(planted.lines().count(), GRAMMAR_CENSUS.lines().count() - 1);
    let mutant = TokenCensus::parse(&planted).expect("a consistent mutant parses");
    let mutant_table = mutant.table_for(true, &[]).expect("no imports");
    assert_eq!(
        lex_one(&mutant_table, "⟨hp, hq⟩"),
        Err(TokenError::NotAToken { at: BytePos(0) }),
        "without its census row `⟨` must refuse exactly as the hand table did"
    );
    // Only that token moved.
    let mut expected: BTreeSet<&str> = real_table.tokens().into_iter().collect();
    expected.remove("⟨");
    assert_eq!(mutant_table.tokens().into_iter().collect::<BTreeSet<_>>(), expected);

    // Dropping the row but not its count is a truncated census: refused, never a smaller table.
    let truncated: String = GRAMMAR_CENSUS
        .lines()
        .filter(|line| !line.starts_with(row))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_eq!(
        TokenCensus::parse(&truncated),
        Err(CensusError::CountMismatch {
            what: "builtin-tokens",
            declared,
            found: declared - 1
        })
    );
}

#[test]
fn malformed_censuses_are_refused_by_name() {
    assert_eq!(
        TokenCensus::parse("schema\tsomething-else/1\n"),
        Err(CensusError::Schema {
            found: Some("schema\tsomething-else/1".to_string())
        })
    );
    assert_eq!(
        TokenCensus::parse("# only a comment\n"),
        Err(CensusError::Schema { found: None })
    );
    // A duplicated token row.
    let first = GRAMMAR_CENSUS
        .lines()
        .find(|line| line.starts_with("builtin-token\t"))
        .expect("a builtin-token row");
    let doubled = GRAMMAR_CENSUS.replacen(first, &format!("{first}\n{first}"), 1);
    assert!(matches!(
        TokenCensus::parse(&doubled),
        Err(CensusError::Duplicate { .. })
    ));
    // An import that leaves the census.
    let opened = GRAMMAR_CENSUS.replacen(
        "module\tInit.Core\timports=",
        "module\tInit.Core\timports=Lean.Elab ",
        1,
    );
    assert_ne!(opened, GRAMMAR_CENSUS, "the Init.Core module row exists");
    assert_eq!(
        TokenCensus::parse(&opened),
        Err(CensusError::OpenClosure {
            module: "Init.Core".to_string(),
            import: "Lean.Elab".to_string()
        })
    );
}

#[test]
fn the_header_and_the_body_use_the_pins_two_tables() {
    // `prelude` is a token only while the header is parsed (`Module.updateTokens`).
    assert_eq!(
        lex_one(header_table(), "prelude"),
        Ok(TokenKind::Symbol("prelude".to_string()))
    );
    assert!(matches!(
        lex_one(implicit_init_table(), "prelude"),
        Ok(TokenKind::Ident(_))
    ));
    // The header is lexed before any import, so Init notation is absent there.
    assert!(!header_table().contains("="));
    assert!(implicit_init_table().contains("="));
}

#[test]
fn production_lexes_the_tokens_the_hand_table_refused() {
    // Before: `lexical analysis reported 1 diagnostic(s)` at the `⟨`. Now the bytes lex, and
    // what remains is the seed grammar's own typed refusal, which says nothing about validity.
    for source in [
        "example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩",
        "def p : Nat × Nat := (1, 2)",
        "theorem o (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega",
    ] {
        match parse_source_command(source.as_bytes()) {
            Err(NatDefinitionParseError::Lexical { diagnostics }) => {
                panic!("{source}: still refused lexically: {diagnostics:?}")
            }
            Ok(_) | Err(_) => {}
        }
    }
}

#[test]
fn a_builtin_keyword_is_no_longer_an_identifier() {
    // `at`, `from` and `show` are tokens wherever `Init` is imported; the Reference refuses
    // them as declaration names, and so does the derived table (z8j.1.6.2's direction).
    for keyword in ["at", "from", "show", "exists", "using"] {
        let source = format!("def {keyword} : Nat := 1");
        assert!(
            parse_definition(source.as_bytes()).is_err(),
            "{source} must be refused: `{keyword}` is a keyword at the pin"
        );
    }
    // An escaped keyword is an identifier, exactly as upstream.
    assert!(matches!(
        lex_one(implicit_init_table(), "«at»"),
        Ok(TokenKind::Ident(_))
    ));
}

/// Totality of the kind-use census, against the grammar census.
#[test]
fn every_kind_init_and_std_use_is_registered_and_every_replay_was_faithful() {
    // The replay set is the module set.
    let modules: BTreeSet<&str> = rows(GRAMMAR_CENSUS, "module").map(|f| f[1]).collect();
    let files: BTreeMap<&str, Vec<&str>> = rows(KIND_USE, "file").map(|f| (f[1], f)).collect();
    assert_eq!(
        files.keys().copied().collect::<BTreeSet<_>>(),
        modules,
        "every Init/Std module is replayed exactly once"
    );
    assert_eq!(count(KIND_USE, "files"), files.len());
    assert!(files.len() >= 1000, "a broken scan, not a small stdlib: {}", files.len());

    // Every replay was faithful: zero errors, no fault, and real work done.
    let mut commands = 0;
    for (module, fields) in &files {
        assert_eq!(fields.len(), 6, "{module}: a faulted replay has no counts: {fields:?}");
        assert_eq!(fields[4], "errors=0", "{module}: the Reference's own replay must be clean");
        commands += fields[3]
            .strip_prefix("commands=")
            .and_then(|n| n.parse::<usize>().ok())
            .expect("commands=");
    }
    assert_eq!(commands, count(KIND_USE, "commands"));
    assert_eq!(count(KIND_USE, "errors"), 0);
    assert_eq!(count(KIND_USE, "faults"), 0);

    // Every kind used is one the Reference knows: a builtin node kind, a header-parser kind, a
    // named special kind (`identKind`, `fieldIdxKind`, …), a kind some module's parser extension
    // declares (Lean.* included: Init's Verso docstrings build `Lean.Doc.Syntax` nodes), a
    // syntax declaration's own kind, or a category's antiquotation pseudo-kind.
    let mut registered: BTreeSet<&str> = BTreeSet::new();
    registered.extend(rows(GRAMMAR_CENSUS, "builtin-node-kind").map(|f| f[1]));
    registered.extend(rows(GRAMMAR_CENSUS, "header-node-kind").map(|f| f[1]));
    registered.extend(rows(GRAMMAR_CENSUS, "syntax-node-kind-constant").map(|f| f[2]));
    registered.extend(rows(GRAMMAR_CENSUS, "syntax-decl").map(|f| f[2]));
    for fields in rows(GRAMMAR_CENSUS, "module-kinds") {
        registered.extend(fields[3].split(' '));
    }
    let mut categories: BTreeSet<&str> = rows(GRAMMAR_CENSUS, "category").map(|f| f[1]).collect();
    categories.extend(rows(GRAMMAR_CENSUS, "module-category").map(|f| f[2]));
    assert!(registered.len() >= 2000 && categories.len() >= 10, "a broken scan");

    let mut used = BTreeSet::new();
    let mut unknown: BTreeMap<&str, &str> = BTreeMap::new();
    for fields in rows(KIND_USE, "uses") {
        assert!(files.contains_key(fields[1]), "a uses row for an unreplayed module");
        for kind in fields[2].split(' ').filter(|kind| !kind.is_empty()) {
            used.insert(kind);
            let pseudo = kind
                .strip_suffix(".pseudo.antiquot")
                .is_some_and(|category| categories.contains(category));
            if !registered.contains(kind) && !pseudo {
                unknown.entry(kind).or_insert(fields[1]);
            }
        }
    }
    assert_eq!(used.len(), count(KIND_USE, "distinct-kinds"));
    // The reviewed remainder: kinds the pinned parser FUNCTIONS build with a literal name and
    // register nowhere, so no census row can name them. Exact in both directions — a new
    // unregistered kind fails, and so does a member that stops occurring.
    let remainder: BTreeSet<&str> = [
        // `Lean/Parser/Term.lean:54`: `nodeFn `Lean.Parser.Command.versoCommentBody …`
        "Lean.Parser.Command.versoCommentBody",
        // `Lean/Parser/Basic.lean:1871`: `s.mkNode (kind ++ `antiquot_suffix_splice) …`
        "many.antiquot_suffix_splice",
        "optional.antiquot_suffix_splice",
        "sepBy.antiquot_suffix_splice",
        // `Lean/Parser/Basic.lean:1785`: `s.mkNode (`token_antiquot) …`
        "token_antiquot",
    ]
    .into_iter()
    .collect();
    assert_eq!(
        unknown.keys().copied().collect::<BTreeSet<_>>(),
        remainder,
        "kinds Init/Std use that the grammar census does not register (kind -> first user): {unknown:?}"
    );
    assert!(!used.contains("missing"), "no replayed command contains a parse hole");

    // The syntax-extension commands are counted per kind and listed per file.
    let listed = rows(KIND_USE, "syntax-command").count();
    let per_kind: usize = rows(KIND_USE, "syntax-command-kind")
        .map(|f| f[2].parse::<usize>().expect("numeral"))
        .sum();
    assert_eq!(listed, per_kind);
    assert_eq!(listed, count(KIND_USE, "syntax-commands"));
}

/// The registrations the bead lists exist in the census with the shape it asks for.
#[test]
fn the_builtin_registration_census_names_kinds_categories_and_precedences() {
    let parsers: Vec<Vec<&str>> = rows(GRAMMAR_CENSUS, "builtin-parser").collect();
    assert_eq!(parsers.len(), count(GRAMMAR_CENSUS, "builtin-parsers"));
    let categories: BTreeMap<&str, usize> = rows(GRAMMAR_CENSUS, "category")
        .map(|f| (f[1], f[4].strip_prefix("parsers=").and_then(|n| n.parse().ok()).expect("parsers=")))
        .collect();
    assert_eq!(categories.values().sum::<usize>(), parsers.len());
    for category in ["term", "command", "tactic", "level", "prio", "prec", "attr", "doElem"] {
        assert!(categories.contains_key(category), "category {category}");
    }
    let anonymous = parsers
        .iter()
        .find(|f| f[2] == "Lean.Parser.Term.anonymousCtor")
        .expect("the anonymous-constructor parser is a builtin term parser");
    assert_eq!(anonymous[1], "term");
    assert_eq!(anonymous[3], "leading");
    assert_eq!(anonymous[5], "prec=1024");
    let tokens: BTreeSet<&str> = anonymous[9]
        .strip_prefix("tokens=")
        .expect("tokens=")
        .split(' ')
        .collect();
    assert!(tokens.contains("⟨") && tokens.contains("⟩"));
    let app = parsers
        .iter()
        .find(|f| f[2] == "Lean.Parser.Term.app")
        .expect("application");
    assert_eq!((app[3], app[5], app[6]), ("trailing", "prec=1022", "lhs-prec=1024"));

    let keyed: BTreeSet<&str> = rows(GRAMMAR_CENSUS, "registration").map(|f| f[1]).collect();
    for attribute in [
        "builtin_term_elab",
        "builtin_command_elab",
        "builtin_tactic",
        "builtin_macro",
        "builtin_doElem_elab",
    ] {
        assert!(keyed.contains(attribute), "{attribute} registrations");
    }
    assert_eq!(
        rows(GRAMMAR_CENSUS, "registration").count(),
        count(GRAMMAR_CENSUS, "keyed-registrations")
    );
    let families: usize = rows(GRAMMAR_CENSUS, "registration-family")
        .map(|f| f[2].parse::<usize>().expect("numeral"))
        .sum();
    assert_eq!(
        families,
        count(GRAMMAR_CENSUS, "registrations"),
        "every _regBuiltin declaration is classified into exactly one family"
    );
    assert_eq!(
        rows(GRAMMAR_CENSUS, "syntax-decl").count(),
        count(GRAMMAR_CENSUS, "init-std-syntax-decls")
    );
}
