//! Selective payload retention preserves the full opaque-capture contract.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::format;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, RegionError, WalkBudget};
use fln_olean::source_extensions as metadata;
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};
use fln_rt::abi;
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::compact;

const BASE: u64 = 1 << 16;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn fixture(blocks: Vec<(Name, Vec<Obj>)>) -> (Vec<u8>, Vec<OpaqueExtensionBlock>) {
    let expected = blocks
        .iter()
        .map(|(name, entries)| OpaqueExtensionBlock {
            name: name.clone(),
            entries: entries
                .iter()
                .map(|entry| compact(entry, 0).unwrap())
                .collect(),
        })
        .collect();
    let entries = Obj::mk_array(
        blocks
            .into_iter()
            .map(|(name, entries)| {
                Obj::mk_ctor(0, vec![inject_name(&name), Obj::mk_array(entries)], &[])
            })
            .collect(),
    );
    let empty = Obj::mk_array(Vec::new());
    let fields = format::MODULE_DATA_FIELDS
        .iter()
        .filter(|field| field.lean_type != "Bool")
        .map(|field| {
            if field.name == "entries" {
                entries.clone_ref()
            } else {
                empty.clone_ref()
            }
        })
        .collect();
    let root = Obj::mk_ctor(0, fields, &[0]);
    let encoded = encode_module(
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: 2,
            flags: 1,
            lean_version: "4.32.0",
            githash: format::PIN_COMMIT,
            base_addr: BASE,
        },
        WriteBudget::default(),
    )
    .unwrap();
    let mut bytes = encoded.bytes[..format::OLEAN_HEADER_SIZE].to_vec();
    bytes.extend(compact(&root, BASE + format::OLEAN_HEADER_SIZE as u64).unwrap());
    (bytes, expected)
}

#[test]
fn selection_preserves_order_structural_names_empty_blocks_and_exact_bytes() {
    let leaf = Obj::mk_string("shared opaque graph");
    let shared = Obj::mk_array(vec![leaf.clone_ref(), leaf]);
    let (bytes, expected) = fixture(vec![
        (Name::num(Name::anonymous(), 7), vec![shared.clone_ref()]),
        (name("7"), vec![Obj::mk_nat(77), shared]),
        (name("empty"), vec![]),
        (name("omittedEmpty"), vec![]),
    ]);
    let view = OleanView::parse(&bytes).unwrap();
    let total: usize = expected
        .iter()
        .flat_map(|block| &block.entries)
        .map(Vec::len)
        .sum();
    assert_eq!(
        view.extension_payloads(WalkBudget::default(), total)
            .unwrap(),
        expected
    );
    let visited = std::cell::RefCell::new(Vec::new());
    let keep = |n: &Name| *n == name("7") || *n == name("empty");
    let selected = view
        .selected_extension_payloads(WalkBudget::default(), total, |n| {
            visited.borrow_mut().push(n.clone());
            keep(n)
        })
        .unwrap();
    assert_eq!(
        visited.into_inner(),
        expected
            .iter()
            .map(|block| block.name.clone())
            .collect::<Vec<_>>()
    );
    for (actual, full) in selected.iter().zip(&expected) {
        assert_eq!(actual.name, full.name);
        assert_eq!(actual.entry_count, full.entries.len());
        assert_eq!(
            actual.payload_bytes,
            full.entries.iter().map(Vec::len).sum::<usize>()
        );
        assert_eq!(
            actual.entries.as_ref(),
            keep(&full.name).then_some(&full.entries)
        );
    }
    assert_eq!(selected[2].entries, Some(Vec::new()));
    assert_eq!(selected[3].entries, None);
    assert_eq!(selected[3].entry_count, 0);
    for budget in 0..=total + 1 {
        let full = view
            .extension_payloads(WalkBudget::default(), budget)
            .map(|_| ());
        for all in [false, true] {
            assert_eq!(
                view.selected_extension_payloads(WalkBudget::default(), budget, |_| all)
                    .map(|_| ()),
                full,
                "omission must not change byte-boundary refusal at {budget}"
            );
        }
        assert_eq!(
            view.selected_extension_payloads(WalkBudget::default(), budget, keep)
                .map(|_| ()),
            full
        );
    }
    let tiny = WalkBudget { max_objects: 1 };
    assert_eq!(
        view.selected_extension_payloads(tiny, total, |_| false)
            .unwrap_err(),
        view.extension_payloads(tiny, total).unwrap_err()
    );
}

fn word(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

#[test]
fn malformed_omitted_graphs_have_the_same_refusal_as_full_capture() {
    let payload = Obj::mk_ctor(0, vec![Obj::mk_string("audited even when omitted")], &[]);
    let (bytes, _) = fixture(vec![(name("ignored"), vec![payload])]);
    let offset = |pointer: u64| usize::try_from(pointer - BASE).unwrap();
    let root = offset(word(&bytes, format::OLEAN_HEADER_SIZE));
    let entries_field = format::MODULE_DATA_FIELDS
        .iter()
        .filter(|field| field.lean_type != "Bool")
        .position(|field| field.name == "entries")
        .unwrap();
    let blocks = offset(word(&bytes, root + 8 * (entries_field + 1)));
    let pair = offset(word(&bytes, blocks + 24));
    let entries = offset(word(&bytes, pair + 16));
    let pointer = word(&bytes, entries + 24);
    let payload = offset(pointer);
    for mutation in 0..4 {
        let mut corrupt = bytes.clone();
        match mutation {
            0 => corrupt[payload..payload + 4].copy_from_slice(&1i32.to_le_bytes()),
            1 => corrupt[payload + 8..payload + 16].copy_from_slice(&pointer.to_le_bytes()),
            2 => corrupt[entries + 24..entries + 32].copy_from_slice(&(pointer + 8).to_le_bytes()),
            _ => corrupt[payload + 7] = abi::TAG_CLOSURE,
        }
        let view = OleanView::parse(&corrupt).unwrap();
        let full = view
            .extension_payloads(WalkBudget::default(), 4096)
            .unwrap_err();
        assert!(!matches!(full, RegionError::PayloadBudgetExhausted { .. }));
        assert_eq!(
            view.selected_extension_payloads(WalkBudget::default(), 4096, |_| false)
                .unwrap_err(),
            full,
            "malformed omitted graph {mutation}"
        );
    }
    assert!(
        OleanView::parse(&bytes)
            .unwrap()
            .selected_extension_payloads(WalkBudget::default(), 4096, |_| false)
            .is_ok()
    );
}

#[test]
fn selected_real_pin_companion_payloads_equal_full_capture() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required"
        );
        eprintln!("SKIP: pinned Reference artifacts absent");
        return;
    };
    let selected_names = [
        metadata::CLASS_EXTENSION,
        metadata::INSTANCE_EXTENSION,
        metadata::macros::MACRO_EXTENSION,
    ]
    .map(name);
    let parser = metadata::parsers::extension_name();
    let keep = |name: &Name| selected_names.contains(name) || *name == parser;
    let mut retained = 0usize;
    let mut omitted = 0usize;
    for module in ["Init/Prelude", "Init/Tactics", "Init/Grind/Tactics"] {
        let parts = ["olean", "olean.server", "olean.private"].map(|suffix| {
            let bytes = std::fs::read(library.join(format!("{module}.{suffix}"))).unwrap();
            fln_olean::pin::check_pinned_header(&bytes).unwrap();
            bytes
        });
        let view = OleanView::parse_with_dependencies(&parts[2], &[&parts[0], &parts[1]]).unwrap();
        let full = view
            .extension_payloads(WalkBudget::default(), 64 * 1024 * 1024)
            .unwrap();
        let total: usize = full
            .iter()
            .flat_map(|block| &block.entries)
            .map(Vec::len)
            .sum();
        let selected = view
            .selected_extension_payloads(WalkBudget::default(), total, keep)
            .unwrap();
        assert_eq!(selected.len(), full.len());
        for (actual, full) in selected.iter().zip(&full) {
            assert_eq!(actual.name, full.name);
            assert_eq!(actual.entry_count, full.entries.len());
            assert_eq!(
                actual.payload_bytes,
                full.entries.iter().map(Vec::len).sum::<usize>()
            );
            assert_eq!(
                actual.entries.as_ref(),
                keep(&full.name).then_some(&full.entries)
            );
            if keep(&full.name) {
                retained += actual.payload_bytes;
            } else {
                omitted += actual.payload_bytes;
            }
        }
        assert_eq!(
            view.selected_extension_payloads(WalkBudget::default(), total - 1, |_| false)
                .unwrap_err(),
            view.extension_payloads(WalkBudget::default(), total - 1)
                .unwrap_err()
        );
    }
    assert!(
        retained > 0 && omitted > retained,
        "actual pin must exercise substantial omitted payloads"
    );
}
