//! Source fidelity and binder boundaries for named-pattern lambdas and lets.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;

fn aliases(syntax: &Syntax) -> Vec<&[Syntax]> {
    let mut todo = vec![syntax];
    let mut found = Vec::new();
    let named = Name::from_components(["Lean", "Parser", "Term", "namedPattern"]);
    while let Some(syntax) = todo.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &named {
                found.push(args.as_slice());
            }
            todo.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn named_binders_preserve_original_tokens_spans_and_trivia() {
    for body in [
        "fun «𝒘»@ /-comment-/ ⟨x, y⟩ other => other",
        "fun ((«𝒘»@(Pair.mk x y))) => x",
        "fun «𝒘»@(x, y) (other : Nat) => x",
        "let «𝒘»@(Pair.mk x y) : Pair := value; «𝒘»",
        "fun value => let «𝒘»@⟨x, y⟩ := value; x",
        "match value with | _ => let «𝒘»@⟨x, y⟩ := value; y",
    ] {
        let source = format!("def f := {body}\r\n");
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let aliases = aliases(parsed.syntax());
        assert_eq!(aliases.len(), 1, "{source}");
        assert_eq!(aliases[0].len(), 4);
        let Syntax::Atom {
            info: SourceInfo::Original { pos, end_pos, .. },
            val,
        } = &aliases[0][1]
        else {
            panic!("missing original @ span")
        };
        assert_eq!(val, "@");
        assert_eq!(
            &parsed.source_view().normalized().as_bytes()[pos.0..end_pos.0],
            b"@"
        );
    }
}

#[test]
fn named_lambda_payload_does_not_capture_the_next_binder() {
    let parsed = parse_definition(b"def f := fun whole@_ (other : Nat) => other").unwrap();
    let alias = aliases(parsed.syntax());
    assert_eq!(alias.len(), 1);
    assert_eq!(
        alias[0][3].kind(),
        Some(&Name::from_components(["Lean", "Parser", "Term", "hole"]))
    );
}

#[test]
fn malformed_or_unsupported_binders_are_not_silently_repaired() {
    for source in [
        "def f := fun whole @⟨x, y⟩ => x",
        "def f := fun whole@ => whole",
        "def f := fun whole@h:Nat => whole",
        "def f := fun (whole@⟨x, y)) => x",
        "def f := let whole@h : Nat := value; whole",
        "def f := let whole@ := value; whole",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn deeply_grouped_named_lambda_binders_use_heap_planning() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut pattern = String::from("⟨x, y⟩");
            for n in 0..256 {
                pattern = format!("a{n}@({pattern})");
            }
            let source = format!("def f := fun ({pattern}) => x");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(aliases(parsed.syntax()).len(), 256);
        })
        .unwrap()
        .join()
        .unwrap();
}
