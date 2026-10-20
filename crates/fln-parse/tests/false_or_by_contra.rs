//! Preserve the pinned nullary tactic shape and the existing lexer policy.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_syntax::tree::Syntax;

fn canonical_tactics(source: &str) -> usize {
    let parsed = fln_parse::parse_definition(source.as_bytes())
        .unwrap_or_else(|problem| panic!("{source}\n{problem:?}"));
    let expected = Name::from_components(["Lean", "Parser", "Tactic", "falseOrByContra"]);
    let mut pending = vec![parsed.syntax()];
    let mut found = 0;
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &expected {
                assert!(
                    matches!(args.as_slice(), [Syntax::Atom { val, .. }]
                        if val == "false_or_by_contra"),
                    "unexpected tactic shape: {syntax:?}"
                );
                found += 1;
            }
            pending.extend(args);
        }
    }
    found
}

#[test]
fn nullary_tactic_has_the_pinned_canonical_kind() {
    for source in [
        "theorem t : False := by false_or_by_contra",
        "theorem t : False := by\n  false_or_by_contra\n",
        "theorem t : False := by\r\n  /- λ -/ false_or_by_contra -- preserved trivia\r\n",
    ] {
        assert_eq!(canonical_tactics(source), 1, "{source}");
    }
}

#[test]
fn tactic_composes_with_sequences_and_backtracking() {
    for (source, count) in [
        (
            "theorem t : False := by false_or_by_contra; false_or_by_contra",
            2,
        ),
        (
            "theorem t : False := by first | (false_or_by_contra; fail) | false_or_by_contra",
            2,
        ),
        ("theorem t : False := by all_goals false_or_by_contra", 1),
        (
            "theorem t : False := by constructor <;> false_or_by_contra",
            1,
        ),
    ] {
        assert_eq!(canonical_tactics(source), count, "{source}");
    }
}

#[test]
fn arguments_and_configuration_are_not_silently_ignored() {
    for tactic in [
        "false_or_by_contra h",
        "false_or_by_contra 2",
        "false_or_by_contra (config := {})",
        "false_or_by_contra at h",
    ] {
        let source = format!("theorem t : False := by {tactic}");
        assert!(
            fln_parse::parse_definition(source.as_bytes()).is_err(),
            "{source}"
        );
    }
}

#[test]
fn quoted_tactic_spelling_remains_an_ordinary_identifier() {
    for source in [
        "def useName («false_or_by_contra» : Nat) : Nat := «false_or_by_contra»",
        "def «false_or_by_contra» : Nat := 0",
    ] {
        assert_eq!(canonical_tactics(source), 0, "{source}");
    }
}
