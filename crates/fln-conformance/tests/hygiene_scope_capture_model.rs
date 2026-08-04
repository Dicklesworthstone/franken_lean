//! G0-4 macro-scope capture model over the production `Name` representation.

#![forbid(unsafe_code)]

use fln_conformance::syntax_hygiene::{model_macro_scope_name, observe_hygiene};
use fln_core::name::Name;

#[test]
fn hygiene_scope_capture_model() {
    let plain = Name::from_components(["local", "binder"]);
    let context = Name::from_components(["Fixture", "quotation"]);
    let first = model_macro_scope_name(plain.clone(), &context, &[7, 11]);
    let repeated = model_macro_scope_name(plain.clone(), &context, &[7, 12]);
    let first_observation = observe_hygiene(&first);
    let repeated_observation = observe_hygiene(&repeated);

    assert!(first_observation.has_macro_scopes);
    assert!(repeated_observation.has_macro_scopes);
    assert_eq!(first_observation.erased, plain.to_display_string());
    assert_eq!(repeated_observation.erased, plain.to_display_string());
    assert_eq!(first_observation.simplified, "local.binder.7.11");
    assert_eq!(repeated_observation.simplified, "local.binder.7.12");
    assert_ne!(
        first_observation.decorated, repeated_observation.decorated,
        "two generated binders in one quotation must not capture each other"
    );
    assert_ne!(first_observation.root, repeated_observation.root);

    let ordinary = observe_hygiene(&plain);
    assert!(!ordinary.has_macro_scopes);
    assert_eq!(ordinary.decorated, ordinary.erased);
    assert_eq!(ordinary.erased, ordinary.simplified);
}
