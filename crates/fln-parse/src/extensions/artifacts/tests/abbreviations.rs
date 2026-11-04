//! Syntax abbreviations reconstructed from artifact descriptions. The live
//! cell compares the resulting quotation trees with the pinned parser; these
//! data-product fixtures alone do not claim `.olean` admission or decoding.
use super::*;

fn abbreviation(label: &str, body: Descr) -> Descr {
    Descr::NodeWithAntiquot(
        label.into(),
        name(&format!("Library.{label}")),
        Box::new(body),
    )
}

fn number() -> Descr {
    abbreviation("number", Descr::Const(name("num")))
}

fn term(declaration: &str, body: Descr) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "term",
        None,
        Descr::Node {
            kind: name(declaration),
            prec: LEAD_PREC,
            body: Box::new(body),
        },
    )
}

fn imported() -> FileGrammar {
    let payload = abbreviation(
        "payload",
        sequence(symbol("["), sequence(number(), symbol("]"))),
    );
    let binding = abbreviation(
        "binding",
        sequence(
            Descr::Const(name("ident")),
            sequence(symbol(":="), Descr::Const(name("num"))),
        ),
    );
    let mut entries: Vec<_> = [
        "packet!", "boxed!", "bind!", "done!", "gather!", "end!", "colored!", "red",
    ]
    .into_iter()
    .map(|text| token(text, None))
    .collect();
    entries.extend([
        term(
            "Library.packet",
            sequence(abbreviation("head", symbol("packet!")), payload),
        ),
        term("Library.boxed", sequence(symbol("boxed!"), number())),
        term(
            "Library.bound",
            sequence(symbol("bind!"), sequence(binding, symbol("done!"))),
        ),
        term(
            "Library.gather",
            sequence(
                symbol("gather!"),
                sequence(
                    Descr::Unary(name("many"), Box::new(number())),
                    symbol("end!"),
                ),
            ),
        ),
        term(
            "Library.colored",
            sequence(symbol("colored!"), abbreviation("red", symbol("red"))),
        ),
    ]);
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule { entries })
        .unwrap();
    file
}

fn node<'a>(syntax: &'a Syntax, expected: &str) -> &'a [Syntax] {
    let expected = name(expected);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return args;
            }
            pending.extend(args);
        }
    }
    panic!("missing {expected:?} in {syntax:?}");
}

#[test]
fn imported_abbreviations_keep_leading_tokens_and_nested_node_shapes() {
    let file = imported();
    let syntax = parse(&file, "def value := packet! [0x2a]").unwrap();
    let packet = node(&syntax, "Library.packet");
    assert_eq!(packet.len(), 2);
    assert_eq!(packet[0].kind(), Some(&name("Library.head")));
    assert_eq!(packet[1].kind(), Some(&name("Library.payload")));
    let payload = node(&packet[1], "Library.payload");
    assert_eq!(payload.len(), 3);
    assert!(matches!(&payload[0], Syntax::Atom { val, .. } if val == "["));
    assert_eq!(payload[1].kind(), Some(&name("Library.number")));
    assert_eq!(
        node(&payload[1], "Library.number")[0].kind(),
        Some(&name("num"))
    );
    assert!(matches!(&payload[2], Syntax::Atom { val, .. } if val == "]"));
    assert!(parse(&file, "def value := f (packet! [42])").is_ok());
    assert!(parse(&file, "def value := f packet! [42]").is_err());
    assert!(parse(&file, "def value := packet! [42] extra").is_err());
    assert!(file.export_native().unwrap().is_empty());
}

#[test]
fn imported_abbreviation_quotations_capture_the_node_or_the_longer_body() {
    let file = imported();
    for input in [
        "def q := `(boxed! $x)",
        "def q := `(boxed! $x:number)",
        "def q := `(boxed! $_:number)",
        "def q := `(boxed! $(f x):number)",
        "def q := `(boxed! $(f `(boxed! 7)):number)",
    ] {
        let syntax = parse(&file, input).unwrap_or_else(|error| panic!("{input}: {error}"));
        let boxed = node(&syntax, "Library.boxed");
        assert_eq!(
            boxed[1].kind(),
            Some(&name("Library.number.antiquot")),
            "{input}"
        );
    }
    let concrete = parse(&file, "def q := `(boxed! $n:num)").unwrap();
    assert!(contains(&concrete, "Library.number"));
    assert!(contains(&concrete, "num.antiquot"));
    assert!(!contains(&concrete, "Library.number.antiquot"));
    let longer = parse(&file, "def q := `(bind! $id := $n done!)").unwrap();
    assert!(contains(&longer, "Library.binding"));
    assert!(contains(&longer, "ident.antiquot"));
    assert!(contains(&longer, "num.antiquot"));
    assert!(!contains(&longer, "Library.binding.antiquot"));
    let whole = parse(&file, "def q := `(bind! $binding:binding done!)").unwrap();
    assert!(contains(&whole, "Library.binding.antiquot"));
    let reserved_label = parse(&file, "def q := `(colored! $c:red)").unwrap();
    assert!(contains(&reserved_label, "Library.red.antiquot"));

    for input in [
        "def q := `(boxed! $x:str)",
        "def q := `(boxed! $x:Library.number)",
        "def q := `(boxed! $x:missing)",
        "def q := `(boxed! $x:)",
        "def q := `(boxed! $ x)",
        "def q := `(boxed! $(f $outside):number)",
        "def q := `(boxed! $x:number*)",
        "def q := boxed! $x:number",
    ] {
        assert!(parse(&file, input).is_err(), "accepted {input}");
    }
    assert!(parse(&file, "def recovered := boxed! 7").is_ok());
}

#[test]
fn imported_abbreviation_captures_keep_repetition_ownership() {
    let file = imported();
    for (input, expected) in [
        (
            "def q := `(gather! $xs:number* end!)",
            "many.antiquot_suffix_splice",
        ),
        (
            "def q := `(gather! $(items):number* end!)",
            "many.antiquot_suffix_splice",
        ),
        (
            "def q := `(gather! $[$n:number]* end!)",
            "many.antiquot_scope",
        ),
    ] {
        let syntax = parse(&file, input).unwrap_or_else(|error| panic!("{input}: {error}"));
        assert!(contains(&syntax, expected), "{input}");
        assert!(contains(&syntax, "Library.number.antiquot"), "{input}");
    }
    for input in [
        "def q := `(gather! $xs:missing* end!)",
        "def q := `(gather! $xs:number,* end!)",
        "def q := `(gather! $[$n:number] end!)",
    ] {
        assert!(parse(&file, input).is_err(), "accepted {input}");
    }
}

#[test]
fn imported_abbreviations_can_wrap_a_custom_category_primitive() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            token("`(artifactItem|", None),
            category_quoter(None),
            parser(
                "Library.itemNumber",
                "artifactItem",
                None,
                Descr::Node {
                    kind: name("Library.itemNumber"),
                    prec: MAX_PREC,
                    body: Box::new(number()),
                },
            ),
        ],
    })
    .unwrap();
    for (input, expected) in [
        ("def q := `(artifactItem| 42)", "Library.number"),
        (
            "def q := `(artifactItem| $x)",
            "artifactItem.pseudo.antiquot",
        ),
        (
            "def q := `(artifactItem| $x:number)",
            "Library.number.antiquot",
        ),
        ("def q := `(artifactItem| $x:num)", "num.antiquot"),
    ] {
        let syntax = parse(&file, input).unwrap_or_else(|error| panic!("{input}: {error}"));
        assert!(contains(&syntax, expected), "{input}");
    }
}

// This independent producer uses source declarations, not the constructed
// descriptors above. Compare all node kinds, child order, null nodes, atoms and
// identifier names; source positions and trivia are outside this comparison.
const ORACLE: &str = r#"
import Lean
open Lean Elab Command
namespace Library
syntax number := num
syntax payload := "[" number "]"
syntax head := "packet!"
syntax binding := ident ":=" num
syntax red := "red"
syntax (name := packet) head payload : term
syntax (name := boxed) "boxed!" number : term
syntax (name := bound) "bind!" binding "done!" : term
syntax (name := gather) "gather!" number* "end!" : term
syntax (name := colored) "colored!" red : term
end Library
private partial def shape : Syntax → String
  | .missing => "M"
  | .node _ kind args => "N:" ++ kind.toString ++ "(" ++ String.intercalate "," (args.toList.map shape) ++ ")"
  | .atom _ value => "A:" ++ reprStr value
  | .ident _ _ value _ => "I:" ++ value.toString
"#;

fn shape(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "M".into(),
        Syntax::Node { kind, args, .. } => format!(
            "N:{}({})",
            kind.to_display_string(),
            args.iter().map(shape).collect::<Vec<_>>().join(",")
        ),
        Syntax::Atom { val, .. } => format!("A:{val:?}"),
        Syntax::Ident { val, .. } => format!("I:{}", val.to_display_string()),
    }
}

#[test]
fn live_imported_abbreviation_quotation_trees_match_pinned_reference() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN") else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the abbreviation quotation oracle requires FLN_REFERENCE_LEAN"
        );
        eprintln!("SKIP live abbreviation quotation oracle: pinned Reference not configured");
        return;
    };
    let pin = include_str!("../../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .unwrap()
        .split_whitespace()
        .find_map(|field| field.strip_prefix("commit="))
        .unwrap();
    let identity = std::process::Command::new(&reference)
        .arg("--githash")
        .output()
        .unwrap();
    assert!(identity.status.success(), "{identity:?}");
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);

    let sources = [
        "def value := packet! [0x2a]",
        "def q := `(boxed! $x)",
        "def q := `(boxed! $x:number)",
        "def q := `(boxed! $_:number)",
        "def q := `(boxed! $x:num)",
        "def q := `(boxed! $(f x):number)",
        "def q := `(boxed! $(f `(boxed! 7)):number)",
        "def q := `(bind! $id := $n done!)",
        "def q := `(bind! $binding:binding done!)",
        "def q := `(colored! $c:red)",
        "def q := `(gather! $xs:number* end!)",
        "def q := `(gather! $(items):number* end!)",
        "def q := `(boxed! $x:str)",
        "def q := `(boxed! $x:Library.number)",
        "def q := `(boxed! $x:missing)",
        "def q := `(boxed! $x:)",
        "def q := `(boxed! $ x)",
        "def q := `(boxed! $x:number*)",
    ];
    let directory = std::env::temp_dir().join(format!(
        "fln-abbreviation-trees-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&directory).unwrap();
    let queries = sources
        .iter()
        .map(|source| format!("{source:?}"))
        .collect::<Vec<_>>()
        .join(",\n    ");
    let producer = format!(
        "{ORACLE}\nrun_cmd do\n  for source in #[{queries}] do\n    match Parser.runParserCategory (← getEnv) `command source with\n    | .ok stx => liftIO <| IO.println (shape stx)\n    | .error _ => liftIO <| IO.println \"REFUSED\"\n"
    );
    let path = directory.join("AbbreviationTrees.lean");
    std::fs::write(&path, producer).unwrap();
    let mut command = std::process::Command::new(reference);
    command.arg("-j1").arg(&path);
    if let Some(library) = std::env::var_os("FLN_REFERENCE_LIB") {
        command.env("LEAN_PATH", library);
    }
    let output = command.output().unwrap();
    std::fs::write(directory.join("oracle.stdout"), &output.stdout).unwrap();
    std::fs::write(directory.join("oracle.stderr"), &output.stderr).unwrap();
    assert!(output.status.success(), "{directory:?}: {output:?}");
    assert!(output.stderr.is_empty(), "{directory:?}: {output:?}");
    let expected = String::from_utf8(output.stdout).unwrap();
    let expected: Vec<_> = expected.lines().collect();
    assert_eq!(expected.len(), sources.len(), "{directory:?}");
    let file = imported();
    for (source, expected) in sources.into_iter().zip(expected) {
        let actual = parse(&file, source).map_or_else(|_| "REFUSED".into(), |tree| shape(&tree));
        assert_eq!(
            actual, expected,
            "{source}; oracle retained at {directory:?}"
        );
    }
}
