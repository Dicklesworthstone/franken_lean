//! Closure lifting consumes the original local names, binders and nested scopes.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn helper_headers_bodies_and_nested_names_preserve_original_source() {
    for source in [
        "/-- λ 🦀 -/\r\ndef owner (unused offset n : Nat) : Nat :=\r\n  let rec go (m : Nat) : Nat := match m with | 0 => offset | k+1 => go k + 1\r\n  go n\r\n",
        "def owner : Nat := let rec inner : Nat := let rec nested : Nat := 12; nested; inner",
        "def owner : Nat := helper where\n  helper : Nat := 5\n",
        "theorem owner (P : Prop) (h : P) : P := let rec evidence : P := h; evidence",
        "def owner : (let rec A : Type := Nat; A) := (5 : Nat)",
        "unsafe def owner : Nat := let rec helper : Nat := 42; helper",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}

#[test]
fn escaped_atomic_helper_names_do_not_become_namespace_paths() {
    let source = "def owner : Nat := let rec «a.b» (x : Nat) : Nat := x; «a.b» 8";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let mut pending = vec![parsed.syntax()];
    let mut names = Vec::new();
    while let Some(node) = pending.pop() {
        match node {
            Syntax::Ident { val, .. } => names.push(val),
            Syntax::Node { args, .. } => pending.extend(args),
            _ => {}
        }
    }
    let atomic = Name::from_components(["a.b"]);
    assert_eq!(names.iter().filter(|&&name| name == &atomic).count(), 2);
    assert!(!names.contains(&&Name::from_components(["a", "b"])));
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}

#[test]
fn malformed_closure_headers_never_drop_the_unchecked_helper_or_continuation() {
    for source in [
        "def owner : Nat := let rec : Nat := 1; 2",
        "def owner : Nat := let rec helper (x : ) : Nat := 1; helper 2",
        "def owner : Nat := let rec helper : Nat := ; 2",
        "def owner : Nat := let rec helper : Nat := 1;",
        "def owner : Nat := helper where\n  helper : Nat :=",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
