//! Completion uses real source checking; no injected environment or fake provider.
#![forbid(unsafe_code)]
use fln::source_check::inspect::{CompletionLookupLimits, SourceCompletion};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits, SourceModuleInput,
};
use fln_core::name::Name;

fn run(test: impl FnOnce(&mut SourceModuleSession) + Send + 'static) {
    const STACK: usize = 16 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK));
            let engine = match Engine::with_coercion_seed(admission).expect("seed input") {
                Outcome::Complete(engine) => engine,
                other => panic!("seed did not complete: {other:?}"),
            };
            let mut session = SourceModuleSession::new(
                engine,
                KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
                SourceModuleCacheLimits::default(),
            );
            test(&mut session);
        })
        .expect("test thread")
        .join()
        .expect("completion assertions");
}

fn complete(session: &mut SourceModuleSession, source: &str, cursor: usize) -> SourceCompletion {
    let entry = Name::from_components(["Main"]);
    let inputs = [SourceModuleInput {
        name: &entry,
        source: source.as_bytes(),
    }];
    match session
        .complete(&inputs, &entry, cursor)
        .expect("completion input")
    {
        Outcome::Complete(Some(result)) => result,
        other => panic!("no completion: {other:?}"),
    }
}

#[test]
fn unfinished_and_later_commands_are_not_admitted_or_suggested() {
    run(|session| {
        let source =
            "prelude\ndef value : Nat := 1\ndef use : Nat := val\ndef valuable : Nat := 2\n";
        let cursor = source.find(":= val").unwrap() + ":= val".len();
        let result = complete(session, source, cursor);
        assert_eq!(
            result
                .items
                .iter()
                .map(|item| item.label.as_str())
                .collect::<Vec<_>>(),
            ["value"]
        );
        assert_eq!(&source[result.range.clone()], "val");
        assert_eq!(result.items[0].replacement, "_root_.value");
        assert!(!result.is_incomplete);
        let again = complete(session, source, cursor);
        assert_eq!(result, again, "a warm session has identical results");
        let broken_later =
            "prelude\ndef value : Nat := 1\ndef use : Nat := val\ndef broken := \"unterminated";
        assert_eq!(
            result,
            complete(session, broken_later, cursor),
            "a lexical error after the cursor cannot change the checked prefix"
        );
    });
}

#[test]
fn root_qualified_replacement_is_checked_even_under_local_shadowing() {
    run(|session| {
        let source = "prelude\ndef value : Nat := 1\ndef use (value : Bool) : Nat := val\n";
        let cursor = source.rfind("val").unwrap() + 3;
        let result = complete(session, source, cursor);
        let selected = result
            .items
            .iter()
            .find(|item| item.label == "value")
            .unwrap();
        let mut edited = source.to_owned();
        edited.replace_range(result.range, &selected.replacement);
        let entry = Name::from_components(["Main"]);
        assert!(matches!(
            session.check(
                &[SourceModuleInput {
                    name: &entry,
                    source: edited.as_bytes(),
                }],
                &entry
            ),
            Ok(Outcome::Complete(_))
        ));
        let unqualified = edited.replace("_root_.value", "value");
        assert!(!matches!(
            session.check(
                &[SourceModuleInput {
                    name: &entry,
                    source: unqualified.as_bytes(),
                }],
                &entry
            ),
            Ok(Outcome::Complete(_))
        ));
    });
}

#[test]
fn namespaces_unicode_and_cursor_suffixes_have_exact_source_ranges() {
    run(|session| {
        let source = "prelude\r\nnamespace Demo\r\ndef αvalue : Nat := 1\r\nend Demo\r\ndef use : Nat := Demo.αvalue\r\n";
        let cursor = source.rfind("Demo.αva").unwrap() + "Demo.αva".len();
        let result = complete(session, source, cursor);
        assert_eq!(&source[result.range.clone()], "Demo.αvalue");
        assert!(
            result
                .items
                .iter()
                .any(|item| item.replacement == "_root_.Demo.αvalue")
        );
        let dot = source.rfind("Demo.αvalue").unwrap() + "Demo.".len();
        let result = complete(session, source, dot);
        assert!(result.items.iter().any(|item| item.label == "Demo.αvalue"));
    });
}

#[test]
fn result_limits_are_deterministic_and_never_hide_truncation() {
    run(|session| {
        let source = "prelude\ndef choice_z : Nat := 1\ndef choice_a : Nat := 2\ndef choice_m : Nat := 3\ndef use : Nat := choice_\n";
        let entry = Name::from_components(["Main"]);
        let inputs = [SourceModuleInput {
            name: &entry,
            source: source.as_bytes(),
        }];
        let cursor = source.rfind("choice_").unwrap() + "choice_".len();
        let mut limits = CompletionLookupLimits {
            max_items: 2,
            ..CompletionLookupLimits::default()
        };
        let query = |session: &mut SourceModuleSession, limits| match session
            .complete_with_limits(&inputs, &entry, cursor, limits)
            .unwrap()
        {
            Outcome::Complete(Some(result)) => result,
            other => panic!("no completion: {other:?}"),
        };
        let result = query(session, limits);
        assert!(result.is_incomplete);
        assert_eq!(
            result
                .items
                .iter()
                .map(|item| item.label.as_str())
                .collect::<Vec<_>>(),
            ["choice_a", "choice_m"]
        );
        assert_eq!(result, query(session, limits));
        limits.max_result_bytes = 0;
        let result = query(session, limits);
        assert!(result.is_incomplete && result.items.is_empty());
        limits.max_candidates = 0;
        assert!(
            session
                .complete_with_limits(&inputs, &entry, cursor, limits)
                .is_err()
        );
    });
}

#[test]
fn changing_or_failing_an_import_cannot_reuse_old_suggestions() {
    run(|session| {
        let entry = Name::from_components(["Main"]);
        let library = Name::from_components(["Library"]);
        let source = "prelude\nimport Library\ndef use : Nat := library_\n";
        let cursor = source.rfind("library_").unwrap() + "library_".len();
        let query = |session: &mut SourceModuleSession, library_source: &str| {
            session.complete(
                &[
                    SourceModuleInput {
                        name: &entry,
                        source: source.as_bytes(),
                    },
                    SourceModuleInput {
                        name: &library,
                        source: library_source.as_bytes(),
                    },
                ],
                &entry,
                cursor,
            )
        };
        for (text, expected) in [
            ("prelude\ndef library_old : Nat := 1\n", "library_old"),
            ("prelude\ndef library_new : Nat := 2\n", "library_new"),
        ] {
            let result = match query(session, text).unwrap() {
                Outcome::Complete(Some(result)) => result,
                other => panic!("no completion: {other:?}"),
            };
            assert_eq!(
                result
                    .items
                    .iter()
                    .map(|item| item.label.as_str())
                    .collect::<Vec<_>>(),
                [expected]
            );
        }
        assert!(!matches!(
            query(session, "prelude\ndef library_old : Nat := true\n"),
            Ok(Outcome::Complete(Some(_)))
        ));
        assert!(matches!(
            query(session, "prelude\ndef library_recovered : Nat := 3\n"),
            Ok(Outcome::Complete(Some(_)))
        ));
    });
}

#[test]
fn invalid_byte_boundaries_and_failed_prefixes_are_not_successes() {
    run(|session| {
        let source = "prelude\ndef αvalue : Nat := 1\ndef use : Nat := αva\n";
        let entry = Name::from_components(["Main"]);
        let inputs = [SourceModuleInput {
            name: &entry,
            source: source.as_bytes(),
        }];
        let split_scalar = source.rfind('α').unwrap() + 1;
        assert!(session.complete(&inputs, &entry, split_scalar).is_err());
        assert!(session.complete(&inputs, &entry, source.len() + 1).is_err());
        let failed = "prelude\ndef value : Nat := true\ndef use : Nat := val\n";
        let cursor = failed.rfind("val").unwrap() + 3;
        assert!(!matches!(
            session.complete(
                &[SourceModuleInput {
                    name: &entry,
                    source: failed.as_bytes(),
                }],
                &entry,
                cursor
            ),
            Ok(Outcome::Complete(Some(_)))
        ));
    });
}
