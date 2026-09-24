//! Ordinary transparent lets share the bounded heap-frame term parser.
#![forbid(unsafe_code)]
use fln_parse::parse_definition;

#[test]
fn lambda_bodies_accept_transparent_local_bindings() {
    let source = "def apply : Nat := (fun x => let y : Nat := x + 1; y) 41";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}

#[test]
fn ordinary_term_positions_keep_original_tokens_and_transparent_nodes() {
    for source in [
        "def f : Nat -> Nat := fun x => let y := x + 1; let z := y + 1; z",
        "def f : Nat := (fun x => x) (let y := 42; y)",
        "def f : Nat := 1 + (let y := 41; y)",
        "def f : Nat := (fun x => let y := (let z := x; z); y) 42",
        "def f : Nat := (fun x => { value := let y := x + 1; y }) 41",
        "def f : Nat := (fun x => [let y := x; y, let z := x + 1; z]) 41",
        "def f : Nat := (fun x => let y := match x with | 0 => 1 | Nat.succ k => k; y) 42",
        "def f : (let A := Type; A) := Nat",
        "def f : Nat := (fun (x : Nat) => let h : x = x := (by rfl); x) 42",
        "def f : Nat := (fun x => have h : x = x := (by rfl); let y := x; y) 42",
        "def τ : Nat := (fun x => let /- kept -/ ψ : Nat := x;\r\n --🦀\r\n ψ) 42\r\n",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        let mut todo = vec![parsed.syntax()];
        let mut lets = 0;
        while let Some(node) = todo.pop() {
            if let fln_syntax::tree::Syntax::Node { kind, args, .. } = node {
                if kind.to_display_string() == "Lean.Parser.Term.let" {
                    lets += 1;
                    assert_eq!(args.len(), 5);
                    assert!(
                        matches!(&args[0], fln_syntax::tree::Syntax::Atom { val, .. } if val == "let")
                    );
                    assert_eq!(
                        args[2].kind().unwrap().to_display_string(),
                        "Lean.Parser.Term.letDecl"
                    );
                }
                todo.extend(args);
            }
        }
        assert!(lets > 0, "no transparent binding: {source}");
    }
}

#[test]
fn nested_layout_bodies_do_not_consume_surrounding_delimiters() {
    for source in [
        "def f : Nat -> Nat := fun x =>\n  let y := x + 1\n  let z := y + 1\n  z\n",
        "def f : Nat -> Nat := fun x =>\n  let y :=\n    let z := x + 1\n    z\n  y\n",
        "def f : Nat := (fun x =>\n  let y := x + 1\n  y) 41",
        "def f : Nat -> Nat := fun x =>\n  let h : x = x := by\n    rfl\n  let y := x + 1\n  y\n",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}

#[test]
fn malformed_nested_bindings_are_never_silently_dropped() {
    for tail in [
        "let",
        "let x",
        "let := 1; 2",
        "let : Nat := 1; 2",
        "let x : := 1; x",
        "let x := ; x",
        "let x := 1",
        "let x := 1;",
        "let x Nat := 1; x",
    ] {
        let source = format!("def f : Nat -> Nat := fun n => {tail}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn nested_lets_use_heap_frames_on_a_small_host_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            for layout in [false, true] {
                let mut source = String::from("def f : Nat -> Nat := fun n =>\n");
                for _ in 0..600 {
                    source.push_str(if layout {
                        "  let x : Nat := n\n"
                    } else {
                        "let x : Nat := n; "
                    });
                }
                source.push_str("  x");
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
