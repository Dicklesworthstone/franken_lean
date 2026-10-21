//! Repetition suffixes belong to their slot's parser, not a scalar operand.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::tree::Syntax;

fn grammar() -> FileGrammar {
    let mut file = FileGrammar::new(false, &[], None)
        .unwrap()
        .own_syntax_only();
    for source in [
        "syntax \"nums!\" \"[\" num,* \"]\" : term",
        "syntax \"many!\" \"[\" num* \"]\" : term",
        "syntax \"some!\" \"[\" (num)? \"]\" : term",
        "syntax \"oneOrMore!\" \"[\" num,+ \"]\" : term",
    ] {
        let command =
            with_grammar(&file.grammar(), || parse_source_command(source.as_bytes())).unwrap();
        file.declare(command.syntax()).unwrap();
    }
    file
}
fn parse(file: &FileGrammar, source: &str) -> Result<Syntax, String> {
    with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
        .map(|command| command.syntax().clone())
        .map_err(|e| format!("{e:?}"))
}
fn suffixes(tree: &Syntax) -> Vec<(Name, String)> {
    let mut pending = vec![tree];
    let mut found = Vec::new();
    while let Some(node) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = node {
            if kind.leaf_view() == fln_core::name::LeafView::Str("antiquot_suffix_splice") {
                let [capture, Syntax::Atom { val, .. }] = args.as_slice() else {
                    panic!("{node:?}")
                };
                assert_eq!(
                    capture.kind().unwrap().leaf_view(),
                    fln_core::name::LeafView::Str("antiquot")
                );
                found.push((kind.parent(), val.clone()));
            }
            pending.extend(args);
        }
    }
    found
}
#[test]
fn repeated_slots_preserve_the_pins_suffix_node_shapes() {
    let file = grammar();
    for (input, kind, suffix) in [
        ("nums![$xs:num,*]", "sepBy", ",*"),
        ("many![$xs*]", "many", "*"),
        ("some![$(xs)?]", "optional", "?"),
        ("oneOrMore![$xs,*]", "sepBy", ",*"),
        ("[$xs,*]", "sepBy", ",*"),
        ("#[$xs,*]", "sepBy", ",*"),
    ] {
        let source = format!("def q := `({input})");
        let tree = parse(&file, &source).unwrap_or_else(|e| panic!("{source}: {e}"));
        assert_eq!(
            suffixes(&tree),
            vec![(Name::from_components([kind]), suffix.into())],
            "{source}"
        );
    }
}
#[test]
fn wrong_slots_suffixes_and_outside_quotation_dollars_refuse() {
    let file = grammar();
    for input in [
        "def q := nums![$xs,*]",
        "def q := many![$xs*]",
        "def q := `($xs,*)",
        "def q := `(nums![$xs:str,*])",
        "def q := `(nums![$xs,+])",
        "def q := `(many![$(xs)?])",
        "def q := `(some![$xs*])",
        "def q := `(xs[$ns,*])",
        "def q := `([f $xs,*])",
        "def q := `([$$xs,*])",
    ] {
        assert!(parse(&file, input).is_err(), "{input}");
    }
    assert!(parse(&file, "def q := `(nums![1, 2])").is_ok());
}
