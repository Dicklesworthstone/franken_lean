//! Live pinned compilation exercises a MacroM callback from genuine emitted
//! user IR. This fixture supplies decoded owners to the dispatch boundary; it
//! does not claim full toolchain admission. Without the Reference, this body is
//! visibly skipped and must not be counted as differential evidence.
use super::*;
use fln_olean::region::{OleanView, WalkBudget};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_recursive_macro_method_preserves_scope_fallback_state_and_diagnostics() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for recursive imported macros"
        );
        eprintln!("SKIP: recursive imported macro fixture requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success(), "{version:?}");
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("recursive-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("NativeRecursiveMacroModule.lean"),
        include_str!("../../../../../fln-olean/fixtures/ir/NativeRecursiveMacroModule.lean"),
    )
    .unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "NativeRecursiveMacroModule.olean",
            "NativeRecursiveMacroModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(result.stdout, b"10\n20\n10\n30\n40\n");
    assert!(result.stderr.is_empty());
    let public = std::fs::read(dir.join("NativeRecursiveMacroModule.olean")).unwrap();
    let server = std::fs::read(dir.join("NativeRecursiveMacroModule.olean.server")).unwrap();
    let private = std::fs::read(dir.join("NativeRecursiveMacroModule.olean.private")).unwrap();
    let decoded = crate::decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        OleanDecodeLimits::new(public.len() + server.len() + private.len()),
    )
    .unwrap();
    let extensions = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 * 1024 * 1024)
        .unwrap();
    let rows = macros::decode(&extensions, DecodeLimits::default()).unwrap();
    let row = |kind: &str, scope: Option<&str>| {
        let matching: Vec<_> = rows
            .iter()
            .filter(|row| row.key == name(kind) && row.scope == scope.map(name))
            .collect();
        assert_eq!(matching.len(), 1, "one emitted registration for {kind}");
        matching[0].declaration.clone()
    };
    let code = [crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeRecursiveMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap()];
    let users = users(&code);
    let root = Environment::new().logical_root(&KVMap::new());
    let checked = CheckedOleanModule {
        name: name("NativeRecursiveMacroModule"),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: Vec::new(),
    };
    let admitted = environment(&[&checked]);
    let registry = RegisteredMacros::prepare(
        &[MacroRegistrationModule {
            checked: &checked,
            extensions: &extensions,
        }],
        &admitted,
        &code,
        &VerifiedPartition::user_fixture(),
        &users,
        MacroRegistryLimits::default(),
    )
    .unwrap_or_else(|error| panic!("{error}; {dir:?}"));
    let activated = registry.activate_scoped(&name("RecursiveScope")).unwrap();
    let source = SourceText::from_utf8(b"").unwrap();
    let left = Syntax::atom(SourceInfo::None, "left");
    let right = Syntax::atom(SourceInfo::None, "right");
    let input = Syntax::node(
        name("recursiveOuter"),
        vec![
            Syntax::atom(SourceInfo::None, "recursiveOuter%"),
            left.clone(),
            Syntax::atom(SourceInfo::None, ","),
            right.clone(),
        ],
    );
    let outer = row("recursiveOuter", None);
    for (snapshot, expected, scope) in [
        (&registry, &left, None),
        (&activated, &right, Some("RecursiveScope")),
        (&registry, &left, None),
    ] {
        let report = snapshot.expand_root(
            &input,
            &source,
            &context(),
            MacroState::default(),
            MacroDispatchLimits::default(),
            None,
        );
        let inner = row("recursiveInner", scope);
        assert!(
            matches!(&report.outcome,
                Outcome::Complete(Ok(RegisteredExpansion::Expanded {
                    syntax, declaration, state, ..
                })) if syntax == expected && declaration == &outer
                    && state.macro_scope == 2
                    && state.expanded_macro_declarations == [outer.clone(), inner.clone()]),
            "{report:?}; {dir:?}"
        );
        assert_eq!(
            report.attempts.len(),
            2,
            "callback executes inside outer IR"
        );
        assert_eq!(report.attempts[0].declaration, outer);
        assert_eq!(report.attempts[1].declaration, inner);
        assert!(report.completed_vm_usage.steps > 0);
    }
    for (kind, attempted, scope) in [("recursiveNone", 1, 1), ("recursiveUnsupported", 2, 2)] {
        let input = Syntax::node(
            name(kind),
            vec![
                Syntax::atom(SourceInfo::None, format!("{kind}%")),
                left.clone(),
            ],
        );
        let report = registry.expand_root(
            &input,
            &source,
            &context(),
            MacroState::default(),
            MacroDispatchLimits::default(),
            None,
        );
        assert!(
            matches!(&report.outcome,
                Outcome::Complete(Ok(RegisteredExpansion::Expanded { syntax, state, .. }))
                    if syntax == &left && state.macro_scope == scope
                        && state.expanded_macro_declarations == [row(kind, None)]),
            "{report:?}; {dir:?}"
        );
        assert_eq!(report.attempts.len(), attempted);
    }
    let input = Syntax::node(
        name("recursiveErrorOuter"),
        vec![Syntax::atom(SourceInfo::None, "recursiveErrorOuter%"), left],
    );
    let report = registry.expand_root(
        &input,
        &source,
        &context(),
        MacroState::default(),
        MacroDispatchLimits::default(),
        None,
    );
    assert!(
        matches!(&report.outcome,
            Outcome::Complete(Ok(RegisteredExpansion::Error { message, .. }))
                if message == "recursive fixture failure"),
        "{report:?}; {dir:?}"
    );
    assert_eq!(report.attempts.len(), 2);
}
