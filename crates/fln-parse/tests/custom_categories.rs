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
fn unresolved_equal_priority_ambiguity_never_selects_an_arbitrary_kind() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := one) \"v\" : item",
        "syntax (name := two) \"v\" : item",
        "syntax \"inspectItem \" \"[\" item \"]\" : term",
    ]);
    assert!(parse(&grammar, "#check inspectItem [v]").is_err());
    assert!(parse(&grammar, "#check (42 : Nat)").is_ok());
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
