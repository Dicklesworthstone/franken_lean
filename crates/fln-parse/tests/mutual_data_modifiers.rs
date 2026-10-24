//! Mutual inductive grouping delegates member boundaries to the ordinary parser.
#![forbid(unsafe_code)]
mod common;
use fln_parse::command_scope::{mutual, partition};

#[test]
fn private_documented_inductives_keep_complete_ordinary_member_syntax() {
    for body in [
        "\r\n /-- 🦀 end -/\r\n private inductive A where | mk (b : B)\r\n /-- mutual is only doc text -/\r\n private inductive B where | mk\r\n",
        "\n inductive A where | mk (b : B)\n /-- second only -/\n inductive B where | mk\n",
        " inductive A where | mk (b : B) inductive B where | mk ",
        "\n @[expose] public inductive A where | mk (b : B)\n @[expose] public inductive B where | mk\n",
    ] {
        let source = format!("mutual{body}end");
        let parsed = mutual::parse(source.as_bytes()).unwrap().unwrap();
        let ordinary = partition(body.as_bytes()).unwrap();
        assert_eq!(parsed.len(), 2);
        assert_eq!(ordinary.len(), 2);
        for (member, (offset, bytes)) in parsed.iter().zip(&ordinary) {
            let normalized_offset = 6 + body[..offset.0].replace("\r\n", "\n").len();
            common::assert_member_in_group(member, bytes, normalized_offset);
        }
    }
}

#[test]
fn mixed_families_commands_and_oversized_groups_never_become_sequential_declarations() {
    for body in [
        "\n/-- a -/\ninductive A where | mk\n/-- b -/\npartial def B : Nat := 0\n",
        "\n/-- a -/\npartial def A : Nat := 0\n/-- b -/\ninductive B where | mk\n",
        "\nprivate inductive A where | mk\nstructure B where\n x : Nat\n",
        "\ninductive A where | mk\nnamespace Hidden\nend\n",
        "\n/-- a -/\ninductive A where | mk\naxiom B : Type\n",
    ] {
        assert!(
            mutual::parse(format!("mutual{body}end").as_bytes()).is_err(),
            "{body}"
        );
    }
    let body = (0..9)
        .map(|i| format!("\n/-- member {i} -/\nprivate inductive T{i} where | mk\n"))
        .collect::<String>();
    assert!(mutual::parse(format!("mutual{body}end").as_bytes()).is_err());
    assert!(mutual::parse(b"mutual\n/-- empty -/\nend").is_err());
}

#[test]
fn prefixed_inductive_diagnostics_retain_original_crlf_byte_positions() {
    let source = "-- 🦀\r\nmutual\r\n /-- first -/\r\n private inductive A where | mk\r\n /-- second -/\r\n private inductive B where | bad (n : Nat]\r\nend";
    let error = mutual::parse(source.as_bytes()).unwrap_err();
    assert_eq!(error.primary_offset().unwrap().0, source.find(']').unwrap());
    let source = "mutual\n/-- first -/\ninductive A where | mk\n/-- second -/\ninductive B where | bad deriving , Nat\nend";
    let error = mutual::parse(source.as_bytes()).unwrap_err();
    assert_eq!(error.primary_offset().unwrap().0, source.find(',').unwrap());
}
