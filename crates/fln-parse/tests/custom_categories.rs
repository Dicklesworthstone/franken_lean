//! Category parsing follows active descriptors, never a hand-written example grammar.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::{command_scope, parse_source_command};
use fln_syntax::tree::Syntax;

fn grammar(commands: &[&str]) -> FileGrammar {
    let mut grammar = FileGrammar::new(false, &[], Some(Name::from_components(["Test"])))
        .unwrap()
        .own_syntax_only();
    for command in commands {
        let active = grammar.grammar();
        if let Ok(Some(scope)) = command_scope::parse(command.as_bytes()) {
            grammar.apply(&scope);
        } else {
            let parsed = with_grammar(&active, || parse_source_command(command.as_bytes()))
                .unwrap_or_else(|e| panic!("{command}: {e:?}"));
            grammar.declare(parsed.syntax()).unwrap();
        }
    }
    grammar
}
fn parse(grammar: &FileGrammar, source: &str) -> Result<Syntax, String> {
    with_grammar(&grammar.grammar(), || {
        parse_source_command(source.as_bytes())
    })
    .map(|c| c.syntax().clone())
    .map_err(|e| format!("{e:?}"))
}
fn contains(syntax: &Syntax, name: &str) -> bool {
    let expected = Name::from_components([name]);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return true;
            }
            pending.extend(args);
        }
    }
    false
}

fn node<'a>(syntax: &'a Syntax, name: &str) -> &'a [Syntax] {
    let expected = Name::from_components([name]);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return args;
            }
            pending.extend(args.iter().rev());
        }
    }
    panic!("missing {name}: {syntax:?}")
}

fn assert_kinds(syntax: &[Syntax], expected: &[&str]) {
    let kinds: Vec<_> = syntax
        .iter()
        .map(|syntax| {
            let Syntax::Node { kind, .. } = syntax else {
                panic!("expected parser node: {syntax:?}");
            };
            kind.clone()
        })
        .collect();
    assert_eq!(
        kinds,
        expected
            .iter()
            .map(|name| Name::from_components([*name]))
            .collect::<Vec<_>>()
    );
}
#[test]
fn longest_match_precedes_priority_and_equal_matches_use_priority() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := high) (priority := high) \"v\" : item",
        "syntax (name := low) (priority := low) \"v\" : item",
        "syntax (name := longest) (priority := low) \"v\" \"x\" : item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
    ]);
    let short = parse(&grammar, "#check inspectItem [v]").unwrap();
    assert!(contains(&short, "high") && !contains(&short, "low"));
    let long = parse(&grammar, "#check inspectItem [v x]").unwrap();
    assert!(contains(&long, "longest") && !contains(&long, "high"));
    assert!(parse(&grammar, "#check inspectItem [v x x]").is_err());
}
#[test]
fn equal_priority_readings_survive_in_newest_first_choice_nodes() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := one) \"v\" : item",
        "syntax (name := low) (priority := low) \"v\" : item",
        "syntax (name := two) \"v\" : item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
    ]);
    let syntax = parse(&grammar, "#check inspectItem [v]").unwrap();
    assert_kinds(node(&syntax, "choice"), &["two", "one"]);
    assert!(!contains(&syntax, "low"));
    assert!(parse(&grammar, "#check inspectItem [v v]").is_err());
    assert!(parse(&grammar, "#check (42 : Nat)").is_ok());
}

#[test]
fn trailing_choices_preserve_both_readings_and_left_association() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := value) \"v\" : item",
        "syntax:70 (name := older) item:70 \"++\" item:71 : item",
        "syntax:70 (name := newer) item:70 \"++\" item:71 : item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
    ]);
    let syntax = parse(&grammar, "#check inspectItem [v ++ v ++ v]").unwrap();
    let choices = node(&syntax, "choice");
    assert_kinds(choices, &["newer", "older"]);
    for choice in choices {
        let Syntax::Node { args, .. } = choice else {
            unreachable!()
        };
        assert_kinds(node(&args[0], "choice"), &["newer", "older"]);
        assert!(contains(&args[2], "value"));
        assert!(!contains(&args[2], "choice"));
    }
    assert!(parse(&grammar, "#check inspectItem [v ++]").is_err());
}

#[test]
fn choices_use_the_minimum_precedence_of_only_the_winning_readings() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax:90 (name := high) \"v\" : item",
        "syntax:80 (name := low) \"v\" : item",
        "syntax:10 (name := ignored) (priority := low) \"v\" : item",
        "syntax:70 (name := allowed) item:80 \"!!\" : item",
        "syntax:70 (name := forbidden) item:81 \"??\" : item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
        "syntax \"inspectHigh \" \"[\" item:85 \"]\" : term",
    ]);
    let syntax = parse(&grammar, "#check inspectItem [v !!]").unwrap();
    assert!(contains(&syntax, "allowed"));
    assert_kinds(node(&syntax, "choice"), &["low", "high"]);
    assert!(!contains(&syntax, "ignored"));
    assert!(parse(&grammar, "#check inspectItem [v ??]").is_err());
    let high = parse(&grammar, "#check inspectHigh [v]").unwrap();
    assert!(contains(&high, "high"));
    assert!(!contains(&high, "choice"));
}

#[test]
fn ambiguous_trailing_tree_copies_share_the_category_work_budget() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := value) \"v\" : item",
        "syntax:70 (name := older) item:70 \"++\" item:71 : item",
        "syntax:70 (name := newer) item:70 \"++\" item:71 : item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
    ]);
    // Copying each left-hand choice into both trailing readings would otherwise
    // build an exponential tree from a linear number of parser descriptions.
    let expression = std::iter::repeat_n("v", 32)
        .collect::<Vec<_>>()
        .join(" ++ ");
    assert!(parse(&grammar, &format!("#check inspectItem [{expression}]")).is_err());
    assert!(parse(&grammar, "#check inspectItem [v ++ v]").is_ok());
}
#[test]
fn failed_leading_candidates_cannot_hide_behind_a_shorter_choice() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := older) \"v\" : item",
        "syntax (name := newer) \"v\" : item",
        "syntax (name := longer) \"v\" \"x\" \"y\" : item",
        "syntax \"inspectItem \" \"[\" item \"x\" \"]\" : term",
    ]);
    // The longer parser reaches the closing bracket expecting y. Its error
    // outranks both short v readings at the pin; the outer x cannot rescue them.
    assert!(parse(&grammar, "#check inspectItem [v x]").is_err());
    assert!(parse(&grammar, "#check (42 : Nat)").is_ok());
}

#[test]
fn failed_trailing_candidates_cannot_hide_behind_leading_choices() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := older) \"v\" : item",
        "syntax (name := newer) \"v\" : item",
        "syntax:70 item:70 \"x\" \"y\" : item",
        "syntax \"inspectItem \" \"[\" item \"x\" \"]\" : term",
        "syntax \"plainItem \" \"[\" item \"]\" : term",
    ]);
    assert!(parse(&grammar, "#check inspectItem [v x]").is_err());
    let safe = parse(&grammar, "#check plainItem [v]").unwrap();
    assert_kinds(node(&safe, "choice"), &["newer", "older"]);
}

#[test]
fn failed_candidates_cannot_hide_behind_nested_choices() {
    let grammar = grammar(&[
        "declare_syntax_cat leaf",
        "declare_syntax_cat item",
        "syntax (name := older) \"v\" : leaf",
        "syntax (name := newer) \"v\" : leaf",
        "syntax \"box\" leaf : item",
        "syntax \"box\" leaf \"x\" \"y\" : item",
        "syntax \"inspectItem \" \"[\" item \"x\" \"]\" : term",
    ]);
    assert!(parse(&grammar, "#check inspectItem [box v x]").is_err());
}

#[test]
fn earlier_failures_remain_visible_when_a_trailing_parser_adds_choices() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax \"v\" : item",
        "syntax \"v\" \"++\" \"v\" \"x\" \"y\" : item",
        "syntax:70 (name := older) item:70 \"++\" item:71 : item",
        "syntax:70 (name := newer) item:70 \"++\" item:71 : item",
        "syntax \"inspectItem \" \"[\" item \"x\" \"]\" : term",
    ]);
    assert!(parse(&grammar, "#check inspectItem [v ++ v x]").is_err());
}

#[test]
fn local_and_scoped_productions_remain_lexical() {
    let mut grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
        "namespace Hidden",
        "scoped syntax \"secret\" : item",
        "end Hidden",
    ]);
    assert!(parse(&grammar, "#check inspectItem [secret]").is_err());
    grammar.apply(&command_scope::ScopeCommand::Section(None));
    grammar.apply(&command_scope::ScopeCommand::OpenScoped(vec![
        Name::from_components(["Hidden"]),
    ]));
    assert!(parse(&grammar, "#check inspectItem [secret]").is_ok());
    grammar.apply(&command_scope::ScopeCommand::End(None));
    assert!(parse(&grammar, "#check inspectItem [secret]").is_err());
    let active = grammar.grammar();
    let local = with_grammar(&active, || {
        parse_source_command(b"local syntax \"temporary\" : item")
    })
    .unwrap();
    grammar.apply(&command_scope::ScopeCommand::Section(None));
    grammar.declare(local.syntax()).unwrap();
    assert!(parse(&grammar, "#check inspectItem [temporary]").is_ok());
    grammar.apply(&command_scope::ScopeCommand::End(None));
    assert!(parse(&grammar, "#check inspectItem [temporary]").is_err());
}
#[test]
fn category_recursion_exhaustion_cannot_choose_a_cheaper_alternative() {
    let grammar = grammar(&[
        "declare_syntax_cat first",
        "declare_syntax_cat second",
        "syntax num : first",
        "syntax second : first",
        "syntax first : second",
        "syntax \"inspectItem \" \"[\" first \"]\" : term",
    ]);
    assert!(parse(&grammar, "#check inspectItem [42]").is_err());
    assert!(parse(&grammar, "#check (42 : Nat)").is_ok());
    let safe = self::grammar(&[
        "declare_syntax_cat first",
        "syntax num : first",
        "syntax \"inspectItem \" \"[\" first \"]\" : term",
    ]);
    assert!(parse(&safe, "#check inspectItem [42]").is_ok());
}

#[test]
fn unnamed_productions_use_the_last_component_of_a_qualified_category() {
    let grammar = grammar(&[
        "declare_syntax_cat Left.item",
        "declare_syntax_cat Right.item",
        "syntax \"v\" : Left.item",
        "syntax \"v\" : Right.item",
        "syntax \"other\" : Right.item",
        "syntax \"inspectLeft \" \"[\" Left.item \"]\" : term",
        "syntax \"inspectRight \" \"[\" Right.item \"]\" : term",
    ]);
    let left = parse(&grammar, "#check inspectLeft [v]").unwrap();
    let right = parse(&grammar, "#check inspectRight [v]").unwrap();
    assert!(contains(&left, "itemV"));
    assert!(contains(&right, "itemV_1"));
    assert!(parse(&grammar, "#check inspectLeft [other]").is_err());
    assert!(contains(
        &parse(&grammar, "#check inspectRight [other]").unwrap(),
        "itemOther"
    ));
}

#[test]
fn category_redeclarations_preserve_the_active_grammar_and_exports() {
    let library = grammar(&["declare_syntax_cat importedItem"]);
    let mut consumer = grammar(&[
        "declare_syntax_cat localItem",
        "syntax (name := localValue) \"vv\" : localItem",
        "syntax \"readLocal \" \"[\" localItem \"]\" : term",
    ]);
    consumer
        .import_native(&library.export_native().unwrap())
        .unwrap();
    let before = consumer.export_native().unwrap();
    for category in ["«term»", "importedItem", "localItem"] {
        let declaration = parse(&consumer, &format!("declare_syntax_cat {category}")).unwrap();
        assert!(consumer.declare(&declaration).is_err(), "{category}");
        assert_eq!(consumer.export_native().unwrap(), before);
    }
    assert!(contains(
        &parse(&consumer, "#check readLocal [vv]").unwrap(),
        "localValue"
    ));
}
