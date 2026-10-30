//! A do binding's proof must leave the following statement in the do sequence.
#![forbid(unsafe_code)]

use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn nodes<'a>(root: &'a Syntax, label: &str) -> Vec<&'a Syntax> {
    let expected = format!("Lean.Parser.{label}");
    let mut pending = vec![root];
    let mut found = Vec::new();
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind.to_display_string() == expected {
                found.push(syntax);
            }
            pending.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn do_binding_proofs_end_before_the_next_statement() {
    // These forms are accepted by the exact Lean 4.32.0 pin. The proof parser
    // must not receive the `return` as another tactic.
    for source in [
        "def f : Id Nat := do\n  let h : True := by trivial\n  return 7",
        "def f : Id Nat := do\n  let h : True := by\n    trivial\n  return 7",
        "def f : Id Nat := do {\n  let h : True := by trivial\n  return 7\n}",
        "def f : Id Nat := do\r\n  let /- fact -/ «𝒉» : True := by\r\n    trivial -- proof\r\n  return 7\r\n",
        "def f : Id Nat := do\n  let n : Nat ← by exact 7\n  return n",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert_eq!(nodes(parsed.syntax(), "Term.byTactic").len(), 1, "{source}");
        assert_eq!(nodes(parsed.syntax(), "Term.doReturn").len(), 1, "{source}");
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
    }
}

#[test]
fn nested_tactics_remain_inside_the_binding_proof() {
    let source = "def f : Id Nat := do\n  let h : True := by\n    have h1 : True := by trivial\n    exact h1\n  return 7";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let proofs = nodes(parsed.syntax(), "Term.byTactic");
    assert_eq!(proofs.len(), 2);
    assert_eq!(nodes(proofs[0], "Term.byTactic").len(), 2);
    assert_eq!(nodes(parsed.syntax(), "Term.doReturn").len(), 1);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}

#[test]
fn conditional_branches_keep_their_own_proofs_and_returns() {
    let source = "def f (b : Bool) : Id Nat := do\n  if _ : b then\n    let evidence : b = true := by assumption\n    return 7\n  else\n    let evidence : Not (b = true) := by assumption\n    return 9";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(nodes(parsed.syntax(), "Term.doIf").len(), 1);
    assert_eq!(nodes(parsed.syntax(), "Term.byTactic").len(), 2);
    assert_eq!(nodes(parsed.syntax(), "Term.doReturn").len(), 2);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}

#[test]
fn grouped_proofs_keep_their_own_layout_and_tactic_semicolons() {
    for source in [
        "def f : Id Nat := do\n  let h : True := (by\n  trivial)\n  return 7",
        "def f : Id Nat := do { let h : True ∧ True := (by constructor; exact True.intro; exact True.intro); return 7 }",
        "def f : Id Nat := do\n  let h : True := by\n    exact (by\n  trivial)\n  return 7",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert_eq!(nodes(parsed.syntax(), "Term.doReturn").len(), 1, "{source}");
        assert_eq!(nodes(parsed.syntax(), "Term.doExpr").len(), 0, "{source}");
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}

#[test]
fn same_column_statement_is_not_invented_as_proof_evidence() {
    // Lean parses the empty proof, then the next do action, and rejects the
    // definition during elaboration. Do not relax the proof's baseline and
    // silently turn that action into a successful `trivial` tactic.
    let source = "def f : Id Nat := do\n  let h : True := by\n  trivial\n  return 7";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let proofs = nodes(parsed.syntax(), "Term.byTactic");
    assert_eq!(proofs.len(), 1);
    let sequences = nodes(proofs[0], "Tactic.tacticSeq1Indented");
    let [Syntax::Node { args, .. }] = sequences.as_slice() else {
        panic!("one empty proof sequence expected");
    };
    assert!(matches!(args.as_slice(), [Syntax::Node { args, .. }] if args.is_empty()));
    assert_eq!(nodes(parsed.syntax(), "Term.doExpr").len(), 1);
    assert_eq!(nodes(parsed.syntax(), "Term.doReturn").len(), 1);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}

#[test]
fn bounded_proofs_do_not_hide_invalid_tactics_or_malformed_continuations() {
    for source in [
        "def f : Id Nat := do\n  let h : True := by notATactic\n  return 7",
        "def f : Id Nat := do\n  let h : True := by trivial\n  let n :=",
        "def f : Id Nat := do\n  let h : True := by trivial\n  return (",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
