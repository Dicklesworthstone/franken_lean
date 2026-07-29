//! G0-4 quotation, antiquotation, splice, and generated-identity model.

#![forbid(unsafe_code)]

use fln_conformance::syntax_hygiene::{QuotationPart, model_quotation_splice, observe_hygiene};
use fln_core::name::Name;
use std::collections::BTreeSet;

#[test]
fn quotation_splice_model() {
    let context = Name::from_components(["FlnG04", "matrix"]);
    let parts = [
        QuotationPart::Literal("prefix".to_string()),
        QuotationPart::Antiquotation("row0".to_string()),
        QuotationPart::Splice(vec![
            "row1".to_string(),
            "row1".to_string(),
            "row2".to_string(),
        ]),
        QuotationPart::Splice(Vec::new()),
        QuotationPart::Literal("suffix".to_string()),
    ];
    let observation = model_quotation_splice(&parts, &context, 41);

    assert_eq!(
        observation.flattened,
        ["prefix", "row0", "row1", "row1", "row2", "suffix"]
    );
    assert_eq!(
        observation.provenance,
        [
            "literal:0",
            "antiquotation:1",
            "splice:2:0",
            "splice:2:1",
            "splice:2:2",
            "literal:4",
        ],
        "a zero-width splice emits nothing and every nonempty splice preserves order"
    );
    assert_eq!(observation.generated_ids.len(), observation.flattened.len());
    assert!(
        observation
            .generated_ids
            .iter()
            .all(|generated| generated.has_macro_scopes)
    );
    let identities = observation
        .generated_ids
        .iter()
        .map(|generated| generated.decorated.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        identities.len(),
        observation.generated_ids.len(),
        "equal antiquoted text still receives distinct generated identities"
    );

    let replay = model_quotation_splice(&parts, &context, 41);
    let another_scope = model_quotation_splice(&parts, &context, 42);
    assert_eq!(replay, observation, "the bounded model is deterministic");
    assert_eq!(replay.flattened, another_scope.flattened);
    assert_ne!(replay.root, another_scope.root);
    assert_ne!(
        observe_hygiene(&Name::from_components(["row1"])).root,
        observation.generated_ids[2].root
    );
}
