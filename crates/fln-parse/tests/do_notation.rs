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
        "do for n ns do return n",
        "do if c then",
        "do break 7",
        "do read;; return 7",
    ] {
        let source = format!("def work := {value}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    // `let mut` and a reassignment are the pin's `doLet` with its `mut` slot and `doReassign`;
    // the elaborator refuses both (`mutable_do_variables_are_refused_not_dropped`, `crates/fln`).
    for value in [
        "do let mut n := 0; return n",
        "do let mut n := 0; n := n + 1; return n",
    ] {
        let source = format!("def work := {value}");
        assert!(parse_definition(source.as_bytes()).is_ok(), "{source}");
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

// Scope and result-type refusals belong to elaboration, not token parsing.
// Keep positive coverage when a formerly unsupported doElem gains syntax.
#[test]
fn newly_supported_control_syntax_is_retained_for_semantic_checking() {
    for source in [
        "def work := do for n in ns do return n",
        "def work := do if c then return 7",
        "def work := do break",
    ] {
        parses(source);
    }
}

/// `letIdDecl := atomic(letIdLhs " := ") term` before `letPatDecl`: a do-block `let` whose name
/// takes bracketed binders is a local function, as the pin reads it (captured with
/// `scripts/extract/dump_command_syntax.lean` on 2026-10-09), not a pattern applying the name to
/// a structure instance; a pattern stays a pattern, and `let some x := e | alt` keeps its term.
#[test]
fn do_let_local_functions_take_bracketed_binders() {
    let kinds = |source: &str| -> Vec<String> {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        let mut out = Vec::new();
        let mut pending = vec![parsed.syntax()];
        while let Some(node) = pending.pop() {
            if let fln_syntax::tree::Syntax::Node { kind, args, .. } = node {
                out.push(kind.to_display_string());
                pending.extend(args.iter().rev());
            }
        }
        out
    };
    let has = |source: &str, kind: &str| kinds(source).iter().any(|found| found == kind);
    let local = "def f : Nat := Id.run do\n  let g {n : Nat} (x : Nat) : Nat := x + n\n  pure 0\n";
    assert!(has(local, "Lean.Parser.Term.letIdDecl"));
    assert!(has(local, "Lean.Parser.Term.implicitBinder"));
    assert!(!has(local, "Lean.Parser.Term.structInst"));
    let instance = "def f : Nat := Id.run do\n  let k [Inhabited Nat] (z : Nat) := z\n  pure 0\n";
    assert!(has(instance, "Lean.Parser.Term.instBinder"));
    let pattern = "def f : Nat := Id.run do\n  let (a, b) := (1, 2)\n  pure a\n";
    assert!(has(pattern, "Lean.Parser.Term.letPatDecl"));
    let otherwise =
        "def f (o : Option Nat) : Nat := Id.run do\n  let some x := o | pure 0\n  pure x\n";
    assert!(has(otherwise, "Lean.Parser.Term.doLetElse"));
    assert!(!has(otherwise, "Lean.Parser.Term.letIdDecl"));
}
