//! G0-4 dynamic grammar epoch and source-order interleaving model.

#![forbid(unsafe_code)]

use fln_conformance::syntax_hygiene::{FixtureManifest, grammar_phase_roots};

#[test]
fn grammar_epoch_transition_model() {
    let manifest = FixtureManifest::load_embedded().expect("manifest");
    manifest.validate_grammar_roots().expect("grammar roots");
    let roots = grammar_phase_roots();

    let builtin = roots.get("builtin").expect("builtin phase");
    let pre_call = roots.get("pre-call").expect("pre-call phase");
    let post_call = roots.get("post-call").expect("post-call phase");
    let post_matrix = roots.get("post-matrix").expect("post-matrix phase");
    assert_eq!(builtin.0.0, 4);
    assert_eq!(pre_call, builtin, "registration is not retroactive");
    assert_eq!(post_call.0.0, 5);
    assert_eq!(post_matrix.0.0, 6);
    assert_ne!(builtin.1, post_call.1);
    assert_ne!(post_call.1, post_matrix.1);

    let observed = manifest
        .rows()
        .iter()
        .map(|row| {
            (
                row.id.as_str(),
                row.grammar_phase.as_str(),
                row.grammar_epoch.0,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        observed,
        [
            ("c0_pratt_trivia", "builtin", 4),
            ("c0_unicode_positions", "builtin", 4),
            ("c0_missing_rhs", "builtin", 4),
            ("c1_call_before_registration", "pre-call", 4),
            ("c1_call_parse", "post-call", 5),
            ("c1_call_expand", "post-call", 5),
            ("c1_call_malformed", "post-call", 5),
            ("c2_matrix_parse", "post-matrix", 6),
            ("c2_matrix_expand", "post-matrix", 6),
            ("c2_matrix_uneven", "post-matrix", 6),
        ],
        "fixture order is the registration/parse interleaving contract"
    );
}
