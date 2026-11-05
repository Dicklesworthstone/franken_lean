//! Genuine Lean 4.32.0 artifact for imported private constructor coverage.
//! Pin: 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
//! Reproduce from Provider.lean with `lean -j1 -o Provider.olean Provider.lean`.
//! The complete public/server/private chain is stored as hexadecimal text.
//! Decoding is not authority: every use admits it through both native checkers.
//! The original Prelude import remains in the decoded header. These tests check
//! every Provider declaration against their already admitted selected foundation;
//! they do not claim admission of the entire named Prelude module closure.

fn bytes(text: &str) -> Vec<u8> {
    let text: String = text.split_whitespace().collect();
    assert!(text.len().is_multiple_of(2));
    (0..text.len())
        .step_by(2)
        .map(|offset| u8::from_str_radix(&text[offset..offset + 2], 16).unwrap())
        .collect()
}

pub fn admitted(base: &fln::Engine, admission: fln::EngineAdmissionLimits) -> fln::Engine {
    let public = bytes(include_str!("Provider.olean.hex"));
    let server = bytes(include_str!("Provider.olean.server.hex"));
    let private = bytes(include_str!("Provider.olean.private.hex"));
    let decoded = fln::decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        fln::OleanDecodeLimits::new(1 << 20),
    )
    .expect("both readers decode the unchanged genuine module artifact chain");
    assert!(matches!(
        decoded.independent,
        fln::IndependentReading::Read(_)
    ));
    assert!(decoded.module.is_module);
    assert_eq!(decoded.module.imports.len(), 1);
    assert_eq!(
        decoded.module.imports[0].module,
        fln::Name::from_components(["Init", "Prelude"])
    );
    // This is the declaration-admission door, not the standalone artifact door:
    // every actual constant dependency must already be in the checked foundation
    // or among this unchanged Provider's complete declarations. No import row,
    // declaration or independent reading is removed or replaced.
    let checked = base
        .check_decoded_olean(
            decoded,
            &fln::KVMap::new(),
            fln::OleanCheckLimits::new(1 << 20, admission.kernel),
        )
        .expect("the actual pin's private constructor families pass both readers and checkers")
        .into_complete()
        .expect("complete checked private constructor declarations");
    assert_eq!(checked.declarations.len(), checked.decoded.constants.len());
    assert!(!checked.declarations.is_empty());
    for declaration in &checked.declarations {
        assert_eq!(declaration.checker.schema, "fln.checker-admission/1");
    }
    checked.engine
}
