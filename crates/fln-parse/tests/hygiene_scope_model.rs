//! Exact, total macro-scope name model on the production `fln-syntax` path.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_syntax::hygiene::{
    FIRST_FRONTEND_MACRO_SCOPE, HygieneError, MacroScopesView, add_macro_scope,
    extract_macro_scopes,
};
use std::process::Command;

fn name(parts: &[&str]) -> Name {
    Name::from_components(parts.iter().copied())
}

#[test]
fn plain_names_have_the_reference_empty_view() {
    let plain = name(&["Lean", "Parser", "Term"]);
    let view = extract_macro_scopes(&plain).expect("plain names are total");
    assert_eq!(
        view,
        MacroScopesView {
            name: plain.clone(),
            imported: Name::anonymous(),
            context: Name::anonymous(),
            scopes: Vec::new(),
        }
    );
    assert_eq!(view.review(), plain);
}

#[test]
fn same_context_appends_scopes_and_context_changes_roll_history_into_imported() {
    let plain = name(&["x"]);
    let main = name(&["Main", "command17", "_hygCtx"]);
    let imported = name(&["Imported", "command4", "_hygCtx"]);

    let first = add_macro_scope(&main, &plain, FIRST_FRONTEND_MACRO_SCOPE).expect("first scope");
    let second = add_macro_scope(&main, &first, 8).expect("same-context scope");
    let transitioned = add_macro_scope(&imported, &second, 3).expect("context transition");
    let final_name = add_macro_scope(&imported, &transitioned, 5).expect("new-context scope");

    let view = extract_macro_scopes(&final_name).expect("well-formed scope name");
    assert_eq!(view.name, plain);
    assert_eq!(view.context, imported);
    assert_eq!(view.scopes, vec![3, 5]);
    assert_eq!(
        view.imported.to_display_string(),
        "Main.command17._hygCtx.1.8"
    );
    assert_eq!(view.review(), final_name);
    assert_eq!(final_name.erase_macro_scopes(), name(&["x"]));
}

#[test]
fn repeated_import_transitions_preserve_every_prior_context_and_scope() {
    let contexts = [
        name(&["A", "a", "_hygCtx"]),
        name(&["B", "b", "_hygCtx"]),
        name(&["C", "c", "_hygCtx"]),
    ];
    let mut scoped = name(&["binder"]);
    for (index, context) in contexts.iter().enumerate() {
        scoped = add_macro_scope(context, &scoped, (index as u64) + 1).expect("transition");
        scoped = add_macro_scope(context, &scoped, (index as u64) + 11).expect("append");
    }

    let view = extract_macro_scopes(&scoped).expect("extracts");
    assert_eq!(view.name, name(&["binder"]));
    assert_eq!(view.context, contexts[2]);
    assert_eq!(view.scopes, vec![3, 13]);
    assert_eq!(
        view.imported.to_display_string(),
        "A.a._hygCtx.1.11.B.b._hygCtx.2.12"
    );
    assert_eq!(view.review(), scoped);
}

#[test]
fn malformed_decorations_are_refused_without_panicking() {
    let missing_scope = Name::str(Name::str(name(&["x", "Ctx"]), "_@"), "_hyg");
    assert!(matches!(
        extract_macro_scopes(&missing_scope),
        Err(HygieneError::EmptyScopeStack { .. })
    ));

    let missing_separator = Name::num(Name::str(name(&["x", "Ctx"]), "_hyg"), 1);
    assert!(matches!(
        extract_macro_scopes(&missing_separator),
        Err(HygieneError::MissingSeparator { .. })
    ));

    let overflowing = Name::num_overflowing(
        Name::str(Name::str(name(&["x", "Ctx"]), "_@"), "_hyg"),
        u64::MAX,
    );
    assert!(matches!(
        extract_macro_scopes(&overflowing),
        Err(HygieneError::OverflowingScope { .. })
    ));
}

#[test]
fn every_small_scope_stack_round_trips_exactly() {
    let contexts = [
        Name::anonymous(),
        name(&["Main", "_hygCtx"]),
        name(&["M", "decl", "_hygCtx"]),
    ];
    for base_depth in 0..5 {
        let mut base = Name::anonymous();
        for index in 0..base_depth {
            base = if index % 2 == 0 {
                Name::str(base, format!("s{index}"))
            } else {
                Name::num(base, index as u64)
            };
        }
        for context in &contexts {
            let mut scoped = base.clone();
            for scope in 1..=8 {
                scoped = add_macro_scope(context, &scoped, scope).expect("well formed");
                let view = extract_macro_scopes(&scoped).expect("extracts");
                assert_eq!(view.name, base);
                assert_eq!(view.context, *context);
                assert_eq!(view.scopes, (1..=scope).collect::<Vec<_>>());
                assert_eq!(view.review(), scoped);
            }
        }
    }
}

#[test]
fn deep_hygiene_name_operations_fit_on_a_small_thread_stack() {
    const CHILD: &str = "FLN_HYGIENE_DEEP_CHILD";
    if std::env::var_os(CHILD).is_some() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut deep = Name::anonymous();
                for index in 0..50_000u64 {
                    deep = Name::num(deep, index);
                }
                let context = name(&["Main", "deep", "_hygCtx"]);
                let scoped = add_macro_scope(&context, &deep, 1).expect("adds");
                let view = extract_macro_scopes(&scoped).expect("extracts");
                assert_eq!(view.name, deep);
                assert_eq!(view.review(), scoped);
            })
            .expect("small-stack thread starts")
            .join()
            .expect("small-stack hygiene walk completes");
        return;
    }

    let result = Command::new(std::env::current_exe().expect("current test binary"))
        .arg("--exact")
        .arg("deep_hygiene_name_operations_fit_on_a_small_thread_stack")
        .arg("--nocapture")
        .env(CHILD, "1")
        .status()
        .expect("child test process runs");
    assert!(result.success(), "small-stack child failed: {result}");
}
