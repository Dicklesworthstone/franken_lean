//! Ordinary mutual classification retains source and never mixes proof/data modes.
#![forbid(unsafe_code)]
use fln_parse::command_scope::{mutual, partition};

#[test]
fn ordinary_definitions_abbreviations_and_theorems_keep_complete_member_syntax() {
    for source in [
        "mutual def x := 1 def y := x end",
        "mutual\n def x : Nat := y\n abbrev y : Nat := 42\nend",
        "mutual\n theorem x : True := y\n theorem y : True := True.intro\nend",
        "-- 😀\r\nmutual\r\n /-- doc -/ def «end» : Nat := next\r\n /- mutual end -/ def next : Nat := 42\r\nend\r\n",
    ] {
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 1);
        assert_eq!(commands[0].1, source.as_bytes());
        let members = mutual::parse(source.as_bytes()).unwrap().unwrap();
        assert_eq!(members.len(), 2);
    }
}
#[test]
fn ordinary_groups_preserve_kind_boundaries_and_existing_size_limit() {
    for source in [
        "mutual def x : Nat := 1 theorem y : True := True.intro end",
        "mutual def x : Nat := 1 partial def y : Nat := 1 end",
        "mutual def x : Nat := 1 unsafe def y : Nat := 1 end",
        "mutual def x : Nat := 1 axiom y : Nat end",
        "mutual def x : Nat := 1 inductive Y where | mk end",
        "mutual def x : Nat := 1 open Nat end",
    ] {
        assert!(mutual::parse(source.as_bytes()).is_err(), "{source}");
    }
    for count in [8, 9] {
        let declarations: String = (0..count)
            .map(|i| format!(" def item{i} : Nat := 0\n"))
            .collect();
        let source = format!("mutual\n{declarations}end");
        assert_eq!(mutual::parse(source.as_bytes()).is_ok(), count == 8);
    }
}
