//! Native category quoters preserve the pin's envelope and pseudo-capture kinds.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::tree::Syntax;

fn grammar(declarations: &[&str]) -> FileGrammar {
    let mut grammar = FileGrammar::new(false, &[], Some(Name::from_components(["Quotes"])))
        .unwrap()
        .own_syntax_only();
    for declaration in declarations {
        let active = grammar.grammar();
        let command = with_grammar(&active, || parse_source_command(declaration.as_bytes()))
            .unwrap_or_else(|e| panic!("{declaration}: {e:?}"));
        grammar.declare(command.syntax()).unwrap();
    }
    grammar
}
fn parse(grammar: &FileGrammar, source: &str) -> Result<Syntax, String> {
    with_grammar(&grammar.grammar(), || {
        parse_source_command(source.as_bytes())
    })
    .map(|command| command.syntax().clone())
    .map_err(|e| format!("{e:?}"))
}
fn node<'a>(syntax: &'a Syntax, path: &[&str]) -> &'a [Syntax] {
    let expected = Name::from_components(path.iter().copied());
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return args;
            }
            pending.extend(args.iter().rev());
        }
    }
    panic!("missing {expected:?}: {syntax:?}");
}
#[test]
fn generated_and_dynamic_quotations_have_distinct_exact_envelopes() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := itemNumber) num : item",
    ]);
    let syntax = parse(&grammar, "def q := `(item| 0x2a)").unwrap();
    let outer = node(&syntax, &["Lean", "Parser", "Term", "quot"]);
    assert_eq!(
        outer.len(),
        1,
        "generated category quotation has one inner node"
    );
    let inner = node(&outer[0], &["item", "quot"]);
    assert_eq!(inner.len(), 3);
    assert!(matches!(&inner[0], Syntax::Atom { val, .. } if val == "`(item|"));
    assert!(matches!(&inner[2], Syntax::Atom { val, .. } if val == ")"));
    let payload = node(&inner[1], &["num"]);
    assert!(matches!(&payload[0], Syntax::Atom { val, .. } if val == "0x2a"));
    let syntax = parse(&grammar, "def q := `(item | 0x2a)").unwrap();
    let dynamic = node(&syntax, &["Lean", "Parser", "Term", "dynamicQuot"]);
    assert_eq!(dynamic.len(), 5);
    assert!(
        matches!(&dynamic[1], Syntax::Ident { val, .. } if *val == Name::from_components(["item"]))
    );
    assert!(matches!(&dynamic[2], Syntax::Atom { val, .. } if val == "|"));
    assert_eq!(node(&dynamic[3], &["num"]).len(), 1);
}
#[test]
fn empty_categories_accept_only_pseudo_captures_in_quotations() {
    let grammar = grammar(&["declare_syntax_cat emptyCategory"]);
    for prefix in ["`(emptyCategory|", "`(emptyCategory |"] {
        for capture in ["$x", "$_", "$x:emptyCategory", "$_:emptyCategory", "$(x)"] {
            let source = format!("def q := {prefix} {capture})");
            let tree = parse(&grammar, &source).unwrap_or_else(|e| panic!("{source}: {e}"));
            let capture = node(&tree, &["emptyCategory", "pseudo", "antiquot"]);
            assert_eq!(capture.len(), 4);
        }
        for bad in [
            "42",
            "ordinary",
            "$x:term",
            "$x:missing",
            "$x:",
            "$x*",
            "$$x",
        ] {
            let source = format!("def q := {prefix} {bad})");
            assert!(parse(&grammar, &source).is_err(), "accepted {source}");
        }
    }
    assert!(parse(&grammar, "def outside := $x:emptyCategory").is_err());
    assert!(parse(&grammar, "def recovered := `(emptyCategory| $x)").is_ok());
}
#[test]
fn concrete_capture_kinds_survive_category_productions() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax (name := itemNumber) num : item",
    ]);
    let syntax = parse(&grammar, "def q := `(item| $n:num)").unwrap();
    assert_eq!(node(&syntax, &["itemNumber"]).len(), 1);
    assert_eq!(node(&syntax, &["num", "antiquot"]).len(), 4);
    assert!(parse(&grammar, "def q := `(item| $n:str)").is_err());
    assert!(parse(&grammar, "def q := `(item| $n:other)").is_err());
    assert!(parse(&grammar, "def q := `(unknownCategory| $n)").is_err());
}
#[test]
fn category_quotations_preserve_term_argument_bounds_and_nested_capture_depth() {
    let grammar = grammar(&[
        "declare_syntax_cat item",
        "syntax num : item",
        "syntax \"consumeQuote \" term:max \"endQuote\" : term",
    ]);
    for source in [
        "def q := f `(item| 42)",
        "def q := consumeQuote `(item| 42) endQuote",
        "def q := consumeQuote `(item | 42) endQuote",
        "def q := `(item| $(f `(item| 42)))",
    ] {
        assert!(parse(&grammar, source).is_ok(), "refused {source}");
    }
    for source in [
        "def q := consumeQuote `(item| 42 endQuote)",
        "def q := `(item| $(f $outside))",
        "def q := `(item| 42 43)",
        "def q := `(item| $(f `(item| 42))",
    ] {
        assert!(parse(&grammar, source).is_err(), "accepted {source}");
    }
    assert!(parse(&grammar, "def recovered := `(item| 7)").is_ok());
}
