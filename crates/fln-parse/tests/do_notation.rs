//! Original source and small-stack contracts for native sequential do syntax.
#![forbid(unsafe_code)]
use fln_parse::parse_definition;
fn parses(source: &str) {
    let parsed = parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace('\r', "").as_bytes()
    );
}
#[test]
fn sequential_actions_bindings_and_terminal_returns_preserve_source() {
    for source in [
        "def work := do return 7",
        "def work := do pure 7",
        "def work := do let n ← read; return n",
        "def work := do let n : Nat <- read; write n; return n",
        "def work := do let n := 7; let k : Nat := n; return k",
        "def work := do let n ← (do return 7); return n",
        "def work := f (do read; return 7) 2",
        "def work := do return 7;",
        "def work := f (do return 7;) 2",
        "def work := do\r\n  let n ← read -- bind\r\n  write n\r\n  return n\r\n",
        "def work := do\n  let n : Nat := 7\n  let k ← read n\n  return k",
        "def work := do\n  let n ← do\n    write 0\n    return 7\n  return n",
        "def work := do\n  let f := fun (n : Nat) => n\n  return (f 7)",
    ] {
        parses(source);
    }
}
#[test]
fn malformed_or_unsupported_do_never_drops_a_statement() {
    for value in [
        "do",
        "do return",
        "do let",
        "do let n ←",
        "do let n ← read",
        "do let n := 7",
        "do let n : ← read; return n",
        "do let n ← ; return n",
        "do return 7; return 8",
        "do let mut n := 0; return n",
        "do for n in ns do return n",
        "do if c then return 7",
        "do break",
        "do let (x, y) ← pair; return x",
        "do read;; return 7",
    ] {
        let source = format!("def work := {value}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
#[test]
fn nested_blocks_and_long_sequences_use_heap_frames() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def work := do ");
            for _ in 0..600 {
                source.push_str("let n ← read; ");
            }
            source.push_str("return n");
            parses(&source);
            let mut source = String::from("def work := ");
            for _ in 0..600 {
                source.push_str("do let n ← (");
            }
            source.push_str("read");
            for _ in 0..600 {
                source.push_str("); return n");
            }
            parses(&source);
        })
        .unwrap()
        .join()
        .unwrap();
}
