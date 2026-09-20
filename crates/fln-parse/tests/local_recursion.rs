//! `let rec` owns its keywords, declaration, and continuation.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn local_recursive_source_retains_comments_unicode_and_original_positions() {
    for source in [
        "def total : Nat := let rec loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop k + 1; loop 3",
        "def τ : Nat := let /- a -/ rec /- b -/ loop (n : Nat) : Nat := match n with | .zero => 0 | .succ k => loop k;\r\n -- continuation\r\n loop 2\r\n",
        "def n : Nat := let rec f (n : Nat) : Nat := let rec g (x : Nat) : Nat := x; g n; f 0",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}: {e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let mut pending = vec![parsed.syntax()];
        let mut recursors = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                if kind == &Name::from_components(["Lean", "Parser", "Term", "letrec"]) {
                    assert_eq!(args.len(), 4);
                    recursors += 1;
                }
                pending.extend(args);
            }
        }
        assert!(recursors > 0);
    }
}

#[test]
fn incomplete_or_unsupported_recursive_groups_do_not_lose_tokens() {
    for source in [
        "def n : Nat := let rec",
        "def n : Nat := let rec f (n : Nat) : Nat := n;",
        "def n : Nat := let rec f (n : Nat) : Nat := ; 0",
        "def n : Nat := let rec f (n : Nat) : Nat := n, g (n : Nat) : Nat := n; g 0",
        "def n : Nat := let rec f (n : Nat) : Nat := n termination_by n; f 0",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn escaped_rec_is_still_an_ordinary_local_identifier() {
    let source = "def n : Nat := let «rec» (n : Nat) : Nat := n; «rec» 3";
    assert_eq!(
        parse_definition(source.as_bytes())
            .unwrap()
            .reconstruct_original(),
        source.as_bytes()
    );
}

#[test]
fn deeply_nested_local_recursive_values_parse_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def n : Nat := ");
            for _ in 0..400 {
                source.push_str("let rec f (x : Nat) : Nat := ");
            }
            source.push('0');
            for _ in 0..400 {
                source.push_str("; f 0");
            }
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn parenthesized_locals_are_lossless_in_tactic_arguments() {
    for source in [
        "def n : Nat := ((let rec f (n : Nat) : Nat := n; f 3))",
        "def n : Nat := by exact (let rec f (n : Nat) : Nat := match n with | .zero => 0 | .succ k => f k; f 3)",
        "def n : Nat := (let «rec» (n : Nat) : Nat := n; «rec» 3)",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}: {e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}

#[test]
fn newline_recursion_preserves_crlf_comments_and_unicode() {
    let source = "def τ (n : Nat) : Nat :=\r\n  let rec go (k : Nat) : Nat :=\r\n    match k with\r\n    | .zero => 0\r\n    | .succ j => go j + 1\r\n  /- unchanged 😄 -/\r\n  go n\r\n";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}
