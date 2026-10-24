//! Mutual partial declarations retain the ordinary parser's complete modifiers.
#![forbid(unsafe_code)]
mod common;

use fln_core::name::Name;
use fln_parse::command_scope::{mutual, partition};
use fln_syntax::tree::Syntax;

fn args(syntax: &Syntax) -> &[Syntax] {
    let Syntax::Node { args, .. } = syntax else {
        panic!("expected a node");
    };
    args
}

#[test]
fn documented_private_members_keep_exact_declaration_trees() {
    let body = "\r\n  /-- 🦀 private partial def end mutual -/\r\n  private partial def left (n : Nat) : Nat := right n\r\n  /-- A different documentation string. -/\r\n  partial def right (n : Nat) : Nat := left n\r\n";
    let source = format!("mutual{body}end");
    let members = mutual::parse(source.as_bytes()).unwrap().unwrap();
    let commands = partition(body.as_bytes()).unwrap();
    assert_eq!(members.len(), 2);
    assert_eq!(commands.len(), 2);
    for (member, (offset, bytes)) in members.iter().zip(&commands) {
        let normalized_offset = 6 + body[..offset.0].replace("\r\n", "\n").len();
        common::assert_member_in_group(member, bytes, normalized_offset);
        let modifiers = args(&args(member)[0]);
        assert_eq!(modifiers.len(), 7);
        assert_eq!(
            args(&modifiers[0]).len(),
            1,
            "retain the attached doc comment"
        );
        assert_eq!(args(&modifiers[6]).len(), 1, "retain the partial marker");
    }
    assert_eq!(args(&args(&args(&members[0])[0])[2]).len(), 1);
    assert!(args(&args(&args(&members[1])[0])[2]).is_empty());
}

#[test]
fn effect_modifiers_are_preserved_for_elaboration_not_erased() {
    for declaration in [
        "@[inline] private partial def left (n : Nat) : Nat := left n",
        "noncomputable partial def left (n : Nat) : Nat := left n",
        "unsafe partial def left (n : Nat) : Nat := left n",
    ] {
        let body = format!("\n  {declaration}\n");
        let source = format!("mutual{body}end");
        let members = mutual::parse(source.as_bytes()).unwrap().unwrap();
        let commands = partition(body.as_bytes()).unwrap();
        assert_eq!(members.len(), 1);
        let normalized_offset = 6 + body[..commands[0].0.0].replace("\r\n", "\n").len();
        common::assert_member_in_group(&members[0], commands[0].1, normalized_offset);
    }
}

#[test]
fn escaped_member_names_and_trivia_do_not_end_or_forge_groups() {
    let source = "mutual\n  /-- end -/\n  private partial def «end» (n : Nat) : Nat := «mutual» n\n  /- ordinary end -/\n  private partial def «mutual» (n : Nat) : Nat := «end» n\nend";
    assert_eq!(mutual::parse(source.as_bytes()).unwrap().unwrap().len(), 2);
    for source in [
        "mutual\n/-- partial -/\ndef left : Nat := 7\nend",
        "mutual\nprivate def «partial» : Nat := 7\nend",
    ] {
        // Ordinary groups now parse. A comment or escaped name still cannot
        // forge a partial modifier; the exact syntax keeps that slot empty.
        let members = mutual::parse(source.as_bytes()).unwrap().unwrap();
        assert_eq!(members.len(), 1);
        assert!(args(&args(&args(&members[0])[0])[6]).is_empty());
    }
    for source in [
        "mutual\npartial def left : String := \"partial def\"\nprivate def right : Nat := 1\nend",
        "mutual\nprivate partial def left : Nat := 1\naxiom right : Nat\nend",
        "mutual\nprivate partial def left : Nat := 1\nend\npartial def escaped : Nat := 2",
    ] {
        assert!(mutual::parse(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn documented_member_errors_retain_original_unicode_and_crlf_positions() {
    let source = "-- 🦀\r\nmutual\r\n  /-- end is doc text -/\r\n  private partial def left : Nat := 7\r\n  /-- second member -/\r\n  private partial def right : Nat := if true then )\r\nend";
    let error = mutual::parse(source.as_bytes()).unwrap_err();
    assert_eq!(
        error.primary_offset().unwrap().0,
        source.rfind(')').unwrap()
    );
    // The parser must recover normally on the very next request.
    let members = mutual::parse(b"mutual\npartial def identity (n : Nat) : Nat := n\nend")
        .unwrap()
        .unwrap();
    assert_eq!(
        members[0].kind(),
        Some(&Name::from_components([
            "Lean",
            "Parser",
            "Command",
            "declaration"
        ]))
    );
}
