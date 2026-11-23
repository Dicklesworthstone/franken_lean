//! Real source syntax declarations use the pin-extracted builtin combinators.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::command_scope::ScopeCommand;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::{DefinitionParseError, parse_definition, parse_source_command};
use fln_syntax::tree::Syntax;

const EXECUTABLE_FIXTURE: &str = include_str!("fixtures/native_generated_aliases.lean");

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn declare(file: &mut FileGrammar, source: &str) {
    let parsed = with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    file.declare(parsed.syntax())
        .unwrap_or_else(|error| panic!("{source}: {error}"));
}

fn grammar(declarations: &[&str]) -> FileGrammar {
    let mut file = FileGrammar::new(false, &[], Some(name("GeneratedAliases")))
        .unwrap()
        .own_syntax_only();
    for declaration in declarations {
        declare(&mut file, declaration);
    }
    file
}

fn parse(file: &FileGrammar, source: &str) -> Result<Syntax, DefinitionParseError> {
    with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
        .map(|command| command.syntax().clone())
}

fn nodes<'a>(syntax: &'a Syntax, expected: &str) -> Vec<&'a Syntax> {
    let expected = name(expected);
    let mut found = Vec::new();
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                found.push(syntax);
            }
            pending.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn bracketed_binder_alias_composes_with_live_term_macros_and_keeps_source_spans() {
    let file = grammar(&[
        "syntax \"bindfun \" bracketedBinder \" => \" term : term",
        "macro_rules | `(bindfun ($n:ident : $ty:term) => $body) => `(fun ($n : $ty) => $body)",
    ]);
    let source = "/- lead -/\r\ndef composed : Nat := (bindfun (n /- type -/ : Nat) => n) 42\r\n";
    let parsed = with_grammar(&file.grammar(), || parse_definition(source.as_bytes())).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
    assert_eq!(
        nodes(parsed.syntax(), "Lean.Parser.Term.explicitBinder").len(),
        1
    );
    let expanded = with_grammar(&file.grammar(), || parsed.expanded()).unwrap();
    assert_eq!(nodes(expanded.syntax(), "Lean.Parser.Term.fun").len(), 1);
}

#[test]
fn declaration_signature_and_do_sequence_aliases_produce_canonical_syntax() {
    let file = grammar(&[
        "syntax (name := sigProbe) \"sigProbe \" ident optDeclSig \" complete\" : command",
        "syntax (name := sequenceProbe) \"sequenceProbe \" doSeq \" finish\" : term",
    ]);
    let signature = parse(&file, "sigProbe generated (x : Nat) : Nat complete").unwrap();
    assert_eq!(nodes(&signature, "Lean.Parser.Command.optDeclSig").len(), 1);
    assert_eq!(
        nodes(&signature, "Lean.Parser.Term.explicitBinder").len(),
        1
    );
    let sequence = parse(&file, "def q := sequenceProbe\n  pure 23\nfinish").unwrap();
    assert_eq!(nodes(&sequence, "Lean.Parser.Term.doSeqIndent").len(), 1);
    assert!(parse(&file, "def q := sequenceProbe\n  pure 23\n pure 42\nfinish").is_err());
}

#[test]
fn generated_builtin_operands_use_current_scoped_user_syntax_and_priority() {
    let mut file =
        grammar(&["syntax (name := signature) \"signature \" declSig \" done\" : command"]);
    file.apply(&ScopeCommand::Namespace(name("ScopedType")));
    declare(
        &mut file,
        "scoped syntax (name := lower) (priority := 900) \"⊙\" : term",
    );
    declare(
        &mut file,
        "scoped syntax (name := higher) (priority := 1100) \"⊙\" : term",
    );
    let active = parse(&file, "signature : ⊙ done").unwrap();
    assert_eq!(nodes(&active, "ScopedType.higher").len(), 1);
    assert!(nodes(&active, "ScopedType.lower").is_empty());
    file.apply(&ScopeCommand::End(Some(name("ScopedType"))));
    assert!(parse(&file, "signature : ⊙ done").is_err());
    file.apply(&ScopeCommand::OpenScoped(vec![name("ScopedType")]));
    let reopened = parse(&file, "signature : ⊙ done").unwrap();
    assert_eq!(nodes(&reopened, "ScopedType.higher").len(), 1);
}

#[test]
fn consuming_errors_refuse_but_declared_alternatives_and_atomic_can_backtrack() {
    let file = grammar(&[
        "syntax (name := binder) \"bound \" optional(bracketedBinder) \" done\" : command",
    ]);
    assert!(parse(&file, "bound done").is_ok());
    assert!(parse(&file, "bound (x : Nat) done").is_ok());
    assert!(parse(&file, "bound (x :) done").is_err());
    assert!(parse(&file, "bound (x : Nat done").is_err());

    let file = grammar(&[
        "syntax (name := binder) \"bound \" optional(bracketedBinder) \" done\" : command",
        "syntax (name := fallback) \"bound \" \"(\" ident \":\" \")\" \" done\" : command",
    ]);
    let accepted = parse(&file, "bound (x :) done").unwrap();
    assert_eq!(accepted.kind(), Some(&name("fallback")));

    let atomic = grammar(&[
        "syntax (name := atomicBinder) \"trial \" orelse(atomic(bracketedBinder), (\"(\" ident \":\" \")\")) \" done\" : command",
    ]);
    assert!(parse(&atomic, "trial (x :) done").is_ok());
    let committed = grammar(&[
        "syntax (name := committedBinder) \"trial \" orelse(bracketedBinder, (\"(\" ident \":\" \")\")) \" done\" : command",
    ]);
    assert!(parse(&committed, "trial (x :) done").is_err());
}

#[test]
fn generated_table_does_not_grant_qualified_parser_declaration_visibility() {
    for prelude in [false, true] {
        let mut file = FileGrammar::new(prelude, &[], Some(name("NoVisibility")))
            .unwrap()
            .own_syntax_only();
        let parsed = with_grammar(&file.grammar(), || {
            parse_source_command(b"syntax \"hidden \" Lean.Parser.Term.bracketedBinder : command")
        })
        .unwrap();
        assert!(file.declare(parsed.syntax()).is_err());
    }
}

#[test]
fn builtin_aliases_can_enter_user_categories_and_keep_recovered_errors() {
    let file = grammar(&[
        "declare_syntax_cat carrier",
        "syntax (name := tinyCarrier) \"Tiny\" : carrier",
        "syntax (name := carrierType) \"carry[\" carrier \"]\" : term",
        "syntax (name := signature) \"signature \" declSig \" done\" : command",
    ]);
    let syntax = parse(&file, "signature : carry[Tiny] done").unwrap();
    assert_eq!(nodes(&syntax, "tinyCarrier").len(), 1);
    assert_eq!(nodes(&syntax, "carrierType").len(), 1);

    let file = grammar(&[
        "syntax (name := recovery) \"recovering \" recover((\"bad \" \"value\"), \"restored\") : term",
        "syntax (name := signature) \"signature \" declSig \" done\" : command",
    ]);
    assert!(parse(&file, "signature : recovering bad value done").is_ok());
    assert!(matches!(
        parse(&file, "signature : recovering bad restored done"),
        Err(DefinitionParseError::GeneratedParser {
            error: fln_parse::builtin_interpreter::ParserFailure::Recovered { .. },
            ..
        })
    ));
}

#[test]
fn deep_generated_operand_reports_a_typed_resource_stop() {
    let depth = fln_parse::builtin_interpreter::DEFAULT_MAX_DEPTH + 2;
    let file = grammar(&["syntax (name := signature) \"signature \" declSig \" done\" : command"]);
    let source = format!(
        "signature : {}Nat{} done",
        "(".repeat(depth),
        ")".repeat(depth)
    );
    assert!(matches!(
        parse(&file, &source),
        Err(DefinitionParseError::GeneratedParser {
            error: fln_parse::builtin_interpreter::ParserFailure::Resource(
                fln_parse::builtin_interpreter::ParserResourceLimit::Depth
            ),
            ..
        })
    ));
    assert!(
        parse(&file, "signature : Nat done").is_ok(),
        "resource failure leaked into a later command"
    );

    let file = grammar(&[
        "syntax \"boundedLambda \" bracketedBinder \" => \" term : term",
        "macro_rules | `(boundedLambda ($n:ident : $ty:term) => $body) => `(fun ($n : $ty) => $body)",
    ]);
    let source = format!(
        "def bounded : Nat := (boundedLambda (x : {}Nat{}) => x) 42",
        "(".repeat(depth),
        ")".repeat(depth)
    );
    assert!(matches!(
        parse(&file, &source),
        Err(DefinitionParseError::GeneratedParser {
            error: fln_parse::builtin_interpreter::ParserFailure::Resource(
                fln_parse::builtin_interpreter::ParserResourceLimit::Depth
            ),
            ..
        })
    ));
    assert!(
        parse(
            &file,
            "def bounded : Nat := (boundedLambda (x : Nat) => x) 42"
        )
        .is_ok()
    );
}

#[test]
fn quotations_without_an_active_file_grammar_produce_the_pinned_tree() {
    // Verified against Lean 4 v4.32.0: `` `(do $body) `` produces `Term.doSeq.pseudo.antiquot`.
    let source = b"def quoted := `(do $body)";
    let parsed = parse_definition(source).unwrap();
    assert_eq!(parsed.reconstruct_original(), source);
    assert_eq!(
        nodes(parsed.syntax(), "Lean.Parser.Term.doSeq.pseudo.antiquot").len(),
        1
    );
}

#[test]
fn executable_fixture_registers_every_macro_and_expands_generated_declarations() {
    let mut file = grammar(&[]);
    // Fixture command boundaries are explicit. Keep continuation lines (the
    // macro rule and the doSeq body/delimiter) with their enclosing command.
    let mut starts = vec![0];
    for (newline, _) in EXECUTABLE_FIXTURE.match_indices('\n') {
        let at = newline + 1;
        let rest = &EXECUTABLE_FIXTURE[at..];
        if [
            "syntax ",
            "macro_rules",
            "def ",
            "theorem ",
            "#eval ",
            "sigProbe ",
        ]
        .iter()
        .any(|prefix| rest.starts_with(prefix))
        {
            starts.push(at);
        }
    }
    starts.push(EXECUTABLE_FIXTURE.len());
    let mut declarations = 0;
    for bounds in starts.windows(2) {
        let source = EXECUTABLE_FIXTURE[bounds[0]..bounds[1]].trim();
        let active = file.grammar();
        let parsed = with_grammar(&active, || parse_source_command(source.as_bytes()))
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        if file
            .declare(parsed.syntax())
            .unwrap_or_else(|error| panic!("{source}: {error}"))
            .is_some()
        {
            continue;
        }
        let expanded = with_grammar(&active, || {
            fln_parse::extensions::expand_active(parsed.syntax())
        })
        .unwrap_or_else(|error| panic!("{source}: {error}"));
        let syntax = expanded.as_ref().unwrap_or(parsed.syntax());
        if source.starts_with("def ") || source.starts_with("sigProbe ") {
            assert_eq!(
                syntax.kind(),
                Some(&name("Lean.Parser.Command.declaration"))
            );
            assert!(
                nodes(syntax, "termBindfun_=>_").is_empty(),
                "unexpanded binder macro: {source}"
            );
            assert!(
                nodes(syntax, "sequenceProbe").is_empty(),
                "unexpanded doSeq macro: {source}"
            );
            if source.starts_with("def fromSequence") {
                assert_eq!(
                    nodes(syntax, "Lean.Parser.Term.doSeqIndent").len(),
                    1,
                    "a whole sequence capture must not become a doExpr containing another sequence"
                );
            }
            declarations += 1;
        }
    }
    assert_eq!(declarations, 3);
}

#[test]
fn nested_tactic_terms_keep_the_native_parenthesis_hygiene_nodes() {
    let parsed = parse_definition(
        b"theorem nested (P : Prop) (witness : P) : P := by exact (by exact witness)",
    )
    .unwrap();
    assert_eq!(
        nodes(parsed.syntax(), "Lean.Parser.Term.hygienicLParen").len(),
        1
    );
    assert_eq!(nodes(parsed.syntax(), "hygieneInfo").len(), 1);
    assert_eq!(nodes(parsed.syntax(), "Lean.Parser.Term.byTactic").len(), 2);
}
