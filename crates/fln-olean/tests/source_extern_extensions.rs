//! Explicit extern metadata is decoded separately from constant declarations.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{
    DecodeError, DecodeLimits, EXTERN_EXTENSION, ExternAttribute, ExternEntry, decode,
};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::{audit, compact};
use std::path::PathBuf;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn list(entries: Vec<Obj>) -> Obj {
    entries
        .into_iter()
        .rev()
        .fold(Obj::mk_nat(0), |tail, head| {
            Obj::mk_ctor(1, vec![head, tail], &[])
        })
}

fn attribute(entries: Obj) -> Obj {
    Obj::mk_ctor(0, vec![inject_name(&name("sample")), entries], &[])
}

fn standard() -> Obj {
    Obj::mk_ctor(
        2,
        vec![
            inject_name(&name("all")),
            Obj::mk_string("lean_string_length"),
        ],
        &[],
    )
}

fn blocks(obj: &Obj) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: name(EXTERN_EXTENSION),
        entries: vec![compact(obj, 0).unwrap()],
    }]
}

#[test]
fn all_extern_kinds_and_order_are_preserved_without_granting_authority() {
    let payload = attribute(list(vec![
        Obj::mk_ctor(0, vec![inject_name(&name("llvm"))], &[]),
        Obj::mk_ctor(
            1,
            vec![inject_name(&name("cpp")), Obj::mk_string("#1 + λ")],
            &[],
        ),
        standard(),
        Obj::mk_nat(3),
    ]));
    let decoded = decode(&blocks(&payload), DecodeLimits::default()).unwrap();
    assert_eq!(
        decoded.externs,
        [ExternAttribute {
            declaration: name("sample"),
            entries: vec![
                ExternEntry::Adhoc {
                    backend: name("llvm")
                },
                ExternEntry::Inline {
                    backend: name("cpp"),
                    pattern: "#1 + λ".into()
                },
                ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "lean_string_length".into()
                },
                ExternEntry::Opaque,
            ],
        }]
    );
    assert!(decoded.uninterpreted.is_empty());
    let absent = decode(&[], DecodeLimits::default()).unwrap();
    assert!(absent.externs.is_empty());
    let empty = decode(&blocks(&attribute(list(vec![]))), DecodeLimits::default()).unwrap();
    assert_eq!(empty.externs.len(), 1);
    assert!(empty.externs[0].entries.is_empty());
    let mut lookalike = blocks(&payload);
    lookalike[0].name = Name::from_components([EXTERN_EXTENSION]);
    let decoded = decode(&lookalike, DecodeLimits::default()).unwrap();
    assert!(decoded.externs.is_empty());
    assert_eq!(
        decoded.uninterpreted,
        [Name::from_components([EXTERN_EXTENSION])]
    );
}

#[test]
fn malformed_extern_tags_fields_names_and_list_tails_refuse_atomically() {
    let valid = blocks(&attribute(list(vec![standard()])));
    let malformed_entries = [
        Obj::mk_nat(0), // adhoc requires its backend.
        Obj::mk_nat(4),
        Obj::mk_ctor(3, vec![inject_name(&name("all"))], &[]),
        Obj::mk_ctor(4, vec![inject_name(&name("all"))], &[]),
        Obj::mk_ctor(2, vec![inject_name(&name("all"))], &[]),
        Obj::mk_ctor(0, vec![Obj::mk_string("all")], &[]),
        Obj::mk_ctor(0, vec![inject_name(&Name::anonymous())], &[]),
        Obj::mk_ctor(1, vec![inject_name(&name("cpp")), Obj::mk_nat(7)], &[]),
        Obj::mk_ctor(2, vec![inject_name(&name("all")), Obj::mk_nat(7)], &[]),
    ];
    for entry in malformed_entries {
        let mut prefixed = valid.clone();
        prefixed[0]
            .entries
            .push(compact(&attribute(list(vec![entry])), 0).unwrap());
        assert!(decode(&prefixed, DecodeLimits::default()).is_err());
    }
    for malformed in [
        Obj::mk_nat(0),
        Obj::mk_ctor(1, vec![inject_name(&name("sample")), list(vec![])], &[]),
        Obj::mk_ctor(0, vec![inject_name(&name("sample"))], &[]),
        Obj::mk_ctor(0, vec![Obj::mk_string("sample"), list(vec![])], &[]),
        attribute(Obj::mk_nat(1)),
        attribute(Obj::mk_ctor(0, vec![standard(), Obj::mk_nat(0)], &[])),
        attribute(Obj::mk_ctor(1, vec![standard()], &[])),
        attribute(Obj::mk_ctor(
            1,
            vec![standard(), Obj::mk_string("tail")],
            &[],
        )),
    ] {
        assert!(decode(&blocks(&malformed), DecodeLimits::default()).is_err());
    }
    let mut truncated = valid.clone();
    let mut bytes = valid[0].entries[0].clone();
    bytes.truncate(bytes.len() / 2);
    truncated[0].entries.push(bytes);
    assert!(decode(&truncated, DecodeLimits::default()).is_err());
}

#[test]
fn extern_list_cells_and_payload_resources_are_cumulatively_bounded() {
    let payload = blocks(&attribute(list(vec![Obj::mk_nat(3), Obj::mk_nat(3)])));
    let mut repeated = payload.clone();
    repeated[0].entries.push(payload[0].entries[0].clone());
    let bound = |max_entries| DecodeLimits {
        max_entries,
        ..DecodeLimits::default()
    };
    assert!(decode(&repeated, bound(6)).is_ok());
    assert!(matches!(
        decode(&repeated, bound(5)),
        Err(DecodeError::Limit { .. })
    ));
    let bytes = payload[0].entries[0].len();
    let objects = audit(&payload[0].entries[0], 0).unwrap().objects;
    for limits in [
        DecodeLimits {
            max_bytes: bytes * 2 - 1,
            ..DecodeLimits::default()
        },
        DecodeLimits {
            max_objects: objects * 2 - 1,
            ..DecodeLimits::default()
        },
        bound(0),
    ] {
        assert!(decode(&repeated, limits).unwrap_err().is_resource());
    }
    let duplicate = [payload[0].clone(), payload[0].clone()];
    assert!(decode(&duplicate, DecodeLimits::default()).is_err());
}

#[test]
fn actual_bootstrap_journal_names_the_pinned_string_extern_symbols() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned library required"
        );
        eprintln!("SKIP: FLN_REFERENCE_LIB not supplied");
        return;
    };
    let path = library.join("Init/Data/String/Bootstrap.olean");
    let public = std::fs::read(&path).unwrap();
    let server = std::fs::read(path.with_extension("olean.server")).unwrap();
    let private = std::fs::read(path.with_extension("olean.private")).unwrap();
    let captured = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 << 20)
        .unwrap();
    let actual = captured
        .into_iter()
        .filter(|block| block.name == name(EXTERN_EXTENSION))
        .collect::<Vec<_>>();
    assert_eq!(
        actual.len(),
        1,
        "the actual extension registration is present"
    );
    let decoded = decode(&actual, DecodeLimits::default()).unwrap();
    for (declaration, symbol) in [
        ("String.Internal.append", "lean_string_append"),
        ("String.Internal.length", "lean_string_length"),
    ] {
        let rows = decoded
            .externs
            .iter()
            .filter(|entry| entry.declaration == name(declaration))
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), 1, "{declaration} has one explicit attribute");
        assert_eq!(
            rows[0].entries,
            [ExternEntry::Standard {
                backend: name("all"),
                symbol: symbol.into()
            }]
        );
    }
}
