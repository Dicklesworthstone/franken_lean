//! Prefix and infix notation retain source leaves, grouping and bounded parsing.
#![forbid(unsafe_code)]
use fln_parse::{parse_definition, parse_nat_definition, parse_source_command};

#[test]
fn all_logical_spellings_preserve_unicode_ascii_comments_and_crlf() {
    for source in [
        "theorem p (a b c : Prop) : a ∧ b ∨ ¬c := by assumption",
        r"theorem p (a b c : Prop) : a /\ b \/ c <-> ¬c := by assumption",
        "-- header\r\ntheorem p : True ∧ -- conjunction\r\n  ¬False := by decide\r\n",
        "def predicate := fun p => ¬p",
        "def predicate := forall h : ¬False, True ∧ True",
        "def proposition := (¬False : Prop)",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}: {e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        assert!(
            parse_nat_definition(source.as_bytes()).is_err(),
            "the Nat-only grammar must not widen"
        );
    }
    for source in [
        "#check True ∧ ¬False",
        r"#eval decide (True \/ False)",
        "#check True ↔ False",
    ] {
        assert!(parse_source_command(source.as_bytes()).is_ok(), "{source}");
    }
}

#[test]
fn malformed_logic_and_unparenthesized_iff_chains_are_not_repaired() {
    for source in [
        "def x := ¬",
        "def x := True ∧",
        "def x := ∨ True",
        "def x := ¬∧ True",
        "def x := True ↔ False ↔ True",
        "def x := True <-> False ↔ True",
        "def x := True ∧ ∨ False",
        "def x := (¬False",
        "def x := ¬(True ∧)",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    for source in [
        "def x := (True ↔ False) ↔ True",
        "def x := True <-> (False ↔ True)",
    ] {
        assert!(parse_definition(source.as_bytes()).is_ok(), "{source}");
    }
}

#[test]
fn deeply_nested_negations_and_right_associative_connectives_use_heap_frames() {
    let source = format!(
        "def proposition := {}False ∧ {}True",
        "¬".repeat(4000),
        "True ∧ ".repeat(4000)
    );
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
