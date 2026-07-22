//! Declaration-decoder suite (bead franken_lean-z6c seed): real pinned-Reference
//! declarations decoded from the C3 fixture corpus, with the identity-layer
//! cross-checks (Name.hash / Level.Data / Expr.Data) that make a layout misread
//! or a hash-law divergence a typed error rather than silent corruption.

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_env::constants::ConstantInfo;
use fln_olean::decl::{DeclDecoder, DeclError};
use fln_olean::region::{OleanView, WalkBudget};

fn fixture(name: &str) -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3")
        .join(name);
    let data = std::fs::read(&path);
    assert!(
        data.is_ok(),
        "missing C3 fixture {}: {:?}",
        path.display(),
        data.err()
    );
    data.expect("asserted above")
}

#[test]
fn binder_name_hint_declarations_decode_with_crosschecks() {
    let bytes = fixture("Init.BinderNameHint.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    // Cross-checks default ON: every Name.hash / Level.Data / Expr.Data word
    // in these declarations must equal our recomputation, or decode errors.
    let infos = decoder.decode_module_constants().expect("decode");
    assert_eq!(infos.len(), 2);

    let names: Vec<String> = infos.iter().map(|i| i.name().to_display_string()).collect();
    assert!(names.iter().any(|n| n == "binderNameHint"), "{names:?}");

    // binderNameHint is a def: `@[reducible] def binderNameHint ... := ...`.
    let def = infos
        .iter()
        .find(|i| i.name().to_display_string() == "binderNameHint");
    assert!(
        matches!(def, Some(ConstantInfo::Defn(_))),
        "expected a definition"
    );
}

#[test]
fn size_of_lemmas_theorems_and_defs_decode() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder.decode_module_constants().expect("decode");
    assert_eq!(infos.len(), 16);
    let thms = infos
        .iter()
        .filter(|i| matches!(i, ConstantInfo::Thm(_)))
        .count();
    let defs = infos
        .iter()
        .filter(|i| matches!(i, ConstantInfo::Defn(_)))
        .count();
    let axioms = infos
        .iter()
        .filter(|i| matches!(i, ConstantInfo::Axiom(_)))
        .count();
    assert_eq!(
        (axioms, defs, thms),
        (9, 0, 7),
        "kind census for SizeOfLemmas"
    );

    // Every constant carries a well-formed type; theorems carry a value.
    for info in &infos {
        assert!(!info.name().to_display_string().is_empty());
        if let ConstantInfo::Thm(t) = info {
            // A theorem's type is a Prop-shaped statement; at minimum it and
            // its proof decoded without a cross-check failure (already proven
            // by reaching here). Spot-check the level-param arity is sane.
            assert!(t.base.level_params.len() <= 8);
        }
    }
}

#[test]
fn crosscheck_catches_a_corrupted_hash_word() {
    // Flip a bit somewhere in the data region and demand that decoding either
    // fails typed (a cross-check or shape error) or returns Ok — but NEVER
    // panics. Reaching the end of the loop is itself the no-panic proof
    // (FL-INV-07). The constant-decoder only traverses declarations reachable
    // from the `constants` array, so flips landing in extension payloads or
    // unreferenced objects legitimately leave the decoded set unchanged; the
    // detection floor below asserts the cross-checks are genuinely live without
    // demanding coverage of unreachable bytes. Deterministic sweep.
    let good = fixture("Init.BinderNameHint.olean");
    let mut seed: u64 = 0x7a_36_63_5f_69_6f_74_61;
    let mut flips = 0u32;
    let mut typed = 0u32;
    while flips < 200 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let pos = 88 + (seed as usize) % (good.len() - 88);
        let mut bad = good.clone();
        bad[pos] ^= 1 << ((seed >> 40) % 8);
        flips += 1;
        if let Ok(view) = OleanView::parse(&bad) {
            let mut decoder = DeclDecoder::new(
                &view,
                WalkBudget {
                    max_objects: 2_000_000,
                },
            );
            if decoder.decode_module_constants().is_err() {
                typed += 1;
            }
        } else {
            typed += 1;
        }
    }
    assert_eq!(flips, 200);
    assert!(
        typed > 25,
        "only {typed}/200 flips detected — cross-checks not live"
    );
}

#[test]
fn disabling_crosscheck_still_decodes_clean_fixtures() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    decoder.cross_check = false;
    let infos = decoder
        .decode_module_constants()
        .expect("decode without cross-check");
    assert_eq!(infos.len(), 16);
}

#[test]
fn budget_exhaustion_is_typed() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget { max_objects: 5 });
    let r = decoder.decode_module_constants();
    assert!(matches!(r, Err(DeclError::Budget { .. })), "{r:?}");
}
