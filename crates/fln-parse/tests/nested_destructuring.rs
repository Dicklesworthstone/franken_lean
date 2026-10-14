//! Nested let patterns reuse the heap constructor-pattern planner.
#![forbid(unsafe_code)]
use fln_parse::parse_definition;

#[test]
fn nested_destructuring_preserves_source_bytes_and_pattern_boundaries() {
    for source in [
        "def f := fun p => let ⟨x, y⟩ := p; x\r\n",
        "def f := id (let (x, y) : Nat × Nat := p; x)\r\n",
        "def f := fun p => let (Pair.mk x y) := p; y\r\n",
        "def f := fun p => let ⟨«λ», /- keep -/ whole@y⟩ := p; whole\r\n",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}
#[test]
fn nonpatterns_and_mismatched_delimiters_are_not_repaired() {
    for source in [
        "def f := fun p => let (fun x => x) := p; 0",
        "def f := fun p => let ⟨x, y) := p; x",
        "def f := fun p => let (x, y) p; x",
        "def f := fun p => let (x, y) := ; x",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
#[test]
fn many_nested_destructuring_binders_stay_off_the_host_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def f := fun p => ");
            for n in 0..256 {
                source.push_str(&format!("let (x{n}, y{n}) := p; "));
            }
            source.push_str("x255");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
