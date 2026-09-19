//! List/cons patterns preserve source structure before checked matrix lowering.
#![forbid(unsafe_code)]
use fln_parse::parse_definition;

#[test]
fn literal_cons_nested_and_multi_column_patterns_preserve_source() {
    for source in [
        "def first (xs : List Nat) : Nat := match xs with | [] => 0 | h :: t => h",
        "def two (xs : List Nat) : Nat := match xs with | [a, b,] => a + b | _ => 0",
        "def nested (xs : List (List Nat)) : Nat := match xs with | [[], [x]] => x | _ => 0",
        "def both (xs ys : List Nat) : Nat := match xs, ys with | x :: _, [y] => x + y | _, _ => 0",
        "def unwrap (xs : Option (List Nat)) : Nat := match xs with | Option.some [x] => x | _ => 0",
        "def first : List Nat -> Nat := fun | [] => 0 | x :: _ => x",
        "def first : List Nat -> Nat | [] => 0 | x :: _ => x",
        "def f (xs : List Nat) : Nat := match xs with\r\n  | [x, /- item -/ y,] => x + y\r\n  | _ => 0",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
    }
}

#[test]
fn incomplete_patterns_and_mixed_delimiters_fail_closed() {
    for pattern in [
        "[,]",
        "[x,,y]",
        "[x,,]",
        "[x)",
        "(x]",
        "[x, (y]",
        "[x,",
        ":: xs",
        "x ::",
        "x :: :: xs",
        "[x] ::",
        "[x] junk",
        "[] []",
    ] {
        let source = format!("def f (xs : List Nat) : Nat := match xs with | {pattern} => 0");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn long_cons_patterns_and_deep_lists_do_not_recurse_in_the_host_parser() {
    let chain = format!("{}[]", "x :: ".repeat(512));
    let nested = format!("{}x{}", "[".repeat(128), "]".repeat(128));
    let literal = format!("[{}]", vec!["x"; 512].join(","));
    for pattern in [chain, nested, literal] {
        // This is parser evidence only: duplicate binders and the deliberately
        // schematic domain still have to be refused by ordinary elaboration.
        let source = format!("def f (xs : List Nat) : Nat := match xs with | {pattern} => 0");
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}
