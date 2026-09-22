//! Runtime module partitioning must retain each mutual admission unit intact.
#![forbid(unsafe_code)]
use fln_parse::{command_scope, partition_source_module};

#[test]
fn headers_and_mutual_members_retain_original_module_byte_coordinates() {
    let source = "import Data\r\n/- α -/\r\nmutual\r\ninductive Tree where | node (xs : Forest)\r\ninductive Forest where | nil | cons (t : Tree)\r\nend\r\n#eval 42\r\n";
    let module = partition_source_module(source.as_bytes()).unwrap();
    assert_eq!(module.imports.len(), 1);
    assert_eq!(module.commands.len(), 2);
    for (offset, bytes) in &module.commands {
        assert_eq!(*bytes, &source.as_bytes()[offset.0..offset.0 + bytes.len()]);
    }
    assert_eq!(module.commands[0].0.0, source.find("mutual").unwrap());
    let group = command_scope::mutual::parse(module.commands[0].1)
        .unwrap()
        .expect("one group");
    assert_eq!(group.len(), 2);
    assert_eq!(module.commands[1].0.0, source.find("#eval").unwrap());
}

#[test]
fn quoted_names_and_comments_cannot_open_or_close_a_mutual_group() {
    let source =
        b"-- mutual\ninductive \xc2\xabmutual\xc2\xbb where | \xc2\xabend\xc2\xbb\n#eval 42\n";
    let module = partition_source_module(source).unwrap();
    assert_eq!(module.commands.len(), 2);
    assert!(
        command_scope::mutual::parse(module.commands[0].1)
            .unwrap()
            .is_none()
    );
}

#[test]
fn malformed_groups_never_become_individually_publishable_members() {
    for source in [
        "mutual\ninductive X where | mk\n",
        "mutual\ninductive X where | mk\nend extra\n#eval 42",
    ] {
        match partition_source_module(source.as_bytes()) {
            Err(_) => {}
            Ok(module) => assert!(command_scope::mutual::parse(module.commands[0].1).is_err()),
        }
    }
}
