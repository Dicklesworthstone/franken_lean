//! Discover the callable solely from a real pinned macro-attribute journal.
//! The full toolchain census/admission environment is independently gated: this
//! fixture supplies exact decoded owners as test caller inputs, never as a
//! production bypass of `VerifiedPartition` or the admission council.
use super::*;
use fln_olean::region::{OleanView, WalkBudget};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_metadata_drives_ordered_macro_dispatch_state_diagnostics_and_authority() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for registered imported macros"
        );
        eprintln!("SKIP: registered imported macros require FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
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
    let dir = root.join(format!("registered-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("NativeRegisteredMacroModule.lean"),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fln-olean/fixtures/ir/NativeRegisteredMacroModule.lean"
        )),
    )
    .unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "NativeRegisteredMacroModule.olean",
            "NativeRegisteredMacroModule.lean",
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
    assert_eq!(
        result.stdout, b"10\n20\n",
        "the pin's source caller exercises both competing expansions"
    );
    assert!(result.stderr.is_empty());

    let public = std::fs::read(dir.join("NativeRegisteredMacroModule.olean")).unwrap();
    let server = std::fs::read(dir.join("NativeRegisteredMacroModule.olean.server")).unwrap();
    let private = std::fs::read(dir.join("NativeRegisteredMacroModule.olean.private")).unwrap();
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
    let kind = name("registeredChoice");
    let rows: Vec<_> = rows.iter().filter(|row| row.key == kind).collect();
    assert_eq!(
        rows.len(),
        3,
        "three actual registrations, including generated names"
    );
    assert!(rows.iter().all(|row| row.scope.is_none()));
    let expected_order: Vec<_> = rows
        .iter()
        .rev()
        .map(|row| row.declaration.clone())
        .collect();
    assert_eq!(expected_order.iter().collect::<BTreeSet<_>>().len(), 3);
    let ir = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeRegisteredMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let code = [ir];
    let users = users(&code);
    assert!(expected_order.iter().all(|entry| users.contains(entry)));

    // This is a decoded-artifact/dispatch test, not a substitute for admitting
    // Init. Supply the exact by-value artifact owners at the caller boundary.
    let root = Environment::new().logical_root(&KVMap::new());
    let checked = CheckedOleanModule {
        name: name("NativeRegisteredMacroModule"),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: Vec::new(),
    };
    let admitted = environment(&[&checked]);
    let modules = [MacroRegistrationModule {
        checked: &checked,
        extensions: &extensions,
    }];
    let registry = RegisteredMacros::prepare(
        &modules,
        &admitted,
        &code,
        &VerifiedPartition::user_fixture(),
        &users,
        MacroRegistryLimits::default(),
    )
    .unwrap_or_else(|error| panic!("{error}; {dir:?}"));

    // This is the same unchanged imported macro code as above, now used through
    // the recursive consumer. The outer macro selects a still-unexpanded child;
    // only then does that result select its own branch. A sibling checks that
    // traversal order and the cumulative state survive the join.
    let choice = |a, b| {
        Syntax::node(
            name("registeredChoice"),
            vec![
                Syntax::atom(SourceInfo::None, "registeredChoice%"),
                a,
                Syntax::atom(SourceInfo::None, ","),
                b,
            ],
        )
    };
    let branch = |text| Syntax::node(name("branch"), vec![Syntax::atom(SourceInfo::None, text)]);
    let nested = Syntax::node(
        name("container"),
        vec![
            choice(
                Syntax::atom(SourceInfo::None, "plain"),
                choice(branch("ten"), branch("twenty")),
            ),
            choice(branch("thirty"), branch("forty")),
        ],
    );
    let expected_tree = Syntax::node(name("container"), vec![branch("ten"), branch("thirty")]);
    let tree_report = registry.expand_tree(
        &nested,
        &SourceText::from_utf8(b"").unwrap(),
        &context(),
        MacroState {
            macro_scope: 17,
            ..MacroState::default()
        },
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&tree_report.outcome, Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, state }))
        if syntax == &expected_tree && state.macro_scope == 28
        && state.expanded_macro_declarations == [expected_order[2].clone(), expected_order[2].clone(), expected_order[1].clone()]),
        "{tree_report:?}; {dir:?}"
    );
    assert_eq!(tree_report.attempts.len(), 8);
    assert_ne!(
        nested, expected_tree,
        "negative control: skipping the recursive consumer changes the tree"
    );
    let root_first = choice(choice(branch("ten"), branch("twenty")), branch("winner"));
    let root_report = registry.expand_tree(
        &root_first,
        &SourceText::from_utf8(b"").unwrap(),
        &context(),
        MacroState::default(),
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(root_report.outcome, Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, .. })) if syntax == branch("winner"))
    );
    assert_eq!(
        root_report.attempts.len(),
        2,
        "expanding the discarded child first changes which branch wins"
    );

    let oracle = r#"import Lean
import NativeRegisteredMacroModule
open Lean Elab Command
private def branch (text : String) : Syntax := .node .none `branch #[.atom .none text]
private def choice (a b : Syntax) : Syntax :=
  .node .none `registeredChoice #[.atom .none "registeredChoice%", a, .atom .none ",", b]
run_cmd do
  let input := Syntax.node .none `container #[
    choice (.atom .none "plain") (choice (branch "ten") (branch "twenty")),
    choice (branch "thirty") (branch "forty")]
  let expected := Syntax.node .none `container #[branch "ten", branch "thirty"]
  let actual ← liftMacroM (expandMacros input)
  if reprStr actual != reprStr expected then throwError "recursive expansion mismatch: {repr actual}"
  if reprStr actual == reprStr input then throwError "wrong-expansion control survived"
  let rootFirst ← liftMacroM (expandMacros (choice (choice (branch "ten") (branch "twenty")) (branch "winner")))
  if reprStr rootFirst != reprStr (branch "winner") then throwError "root-before-children mismatch"
  logInfo "recursive tree identical; unchanged-tree control differs"
"#;
    std::fs::write(dir.join("RecursiveOracle.lean"), oracle).unwrap();
    let oracle_result = Command::new(&reference)
        .current_dir(&dir)
        .env("LEAN_PATH", &dir)
        .arg("RecursiveOracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("recursive-oracle.stdout"), &oracle_result.stdout).unwrap();
    std::fs::write(dir.join("recursive-oracle.stderr"), &oracle_result.stderr).unwrap();
    assert!(
        oracle_result.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle_result.stdout),
        String::from_utf8_lossy(&oracle_result.stderr)
    );
    assert_eq!(
        oracle_result.stdout,
        b"recursive tree identical; unchanged-tree control differs\n"
    );
    assert!(oracle_result.stderr.is_empty());
    assert_eq!(
        registry.declarations(&kind).cloned().collect::<Vec<_>>(),
        expected_order
    );
    let source = SourceText::from_utf8(b"").unwrap();
    let second = Syntax::atom(SourceInfo::None, "α\0🙂");
    let input = |first| {
        Syntax::node(
            kind.clone(),
            vec![
                Syntax::atom(SourceInfo::None, "registeredChoice%"),
                first,
                Syntax::atom(SourceInfo::None, ","),
                second.clone(),
            ],
        )
    };
    let first = Syntax::node(
        name("branch"),
        vec![Syntax::atom(SourceInfo::None, "first")],
    );
    for (first, expected, attempts, scope, chosen) in [
        (first.clone(), first, 3, 21, 2),
        (
            Syntax::atom(SourceInfo::None, "plain"),
            second.clone(),
            2,
            20,
            1,
        ),
    ] {
        let input = input(first);
        let execute = |limits| {
            registry.expand_root(
                &input,
                &source,
                &context(),
                MacroState {
                    macro_scope: 17,
                    ..MacroState::default()
                },
                limits,
                None,
            )
        };
        let report = execute(MacroDispatchLimits::default());
        let Outcome::Complete(Ok(RegisteredExpansion::Expanded {
            declaration,
            syntax,
            state,
            ..
        })) = &report.outcome
        else {
            panic!("{report:?}; {dir:?}")
        };
        assert_eq!(declaration, &expected_order[chosen]);
        assert_eq!(syntax, &expected);
        assert_eq!(
            state.macro_scope, scope,
            "fresh outer scopes and the unsupported candidate's nested scope survive"
        );
        assert_eq!(
            state.expanded_macro_declarations,
            [expected_order[chosen].clone()]
        );
        assert!(state.trace_messages.is_empty());
        assert_eq!(report.attempts.len(), attempts);
        assert_eq!(
            report
                .attempts
                .iter()
                .map(|attempt| &attempt.declaration)
                .collect::<Vec<_>>(),
            expected_order[..attempts].iter().collect::<Vec<_>>()
        );
        assert_eq!(
            report.completed_vm_usage.steps,
            report
                .attempts
                .iter()
                .map(|attempt| attempt.vm_usage.unwrap().steps)
                .sum::<u64>()
        );
        assert!(report.completed_vm_usage.steps > 0);
        assert!(report.attempts.iter().all(|attempt| {
            attempt
                .reference_functions
                .iter()
                .any(|function| function.name == attempt.declaration)
        }));
        assert!(
            report
                .attempts
                .iter()
                .flat_map(|attempt| &attempt.reference_functions)
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                )
        );
        assert!(
            report
                .attempts
                .iter()
                .flat_map(|attempt| &attempt.native_functions)
                .any(|native| native == "mirror:Lean.Syntax.getArg")
        );
        let mut exact = MacroDispatchLimits::default();
        exact.execution.vm.max_steps = report.completed_vm_usage.steps;
        let replay = execute(exact);
        assert!(
            matches!(replay.outcome, Outcome::Complete(Ok(RegisteredExpansion::Expanded { syntax, .. })) if syntax == expected)
        );
        exact.execution.vm.max_steps -= 1;
        assert!(matches!(execute(exact).outcome, Outcome::Inconclusive(_)));
    }
    let empty = Syntax::node(kind, vec![]);
    let diagnostic = registry.expand_root(
        &empty,
        &source,
        &context(),
        MacroState {
            macro_scope: 17,
            ..MacroState::default()
        },
        MacroDispatchLimits::default(),
        None,
    );
    assert_eq!(diagnostic.attempts.len(), 1);
    assert!(
        matches!(&diagnostic.outcome, Outcome::Complete(Ok(RegisteredExpansion::Error {
        declaration, reference, message, state, ..
    })) if declaration == &expected_order[0] && reference == &empty &&
        message == "registered λ\0error" && state.macro_scope == 19 && state.expanded_macro_declarations.is_empty()),
        "{diagnostic:?}; {dir:?}"
    );

    // The same valid metadata cannot classify code or borrow another module's
    // owner, even though all bytes were produced by the exact pin.
    assert!(matches!(
        RegisteredMacros::prepare(
            &modules,
            &admitted,
            &code,
            &VerifiedPartition::user_fixture(),
            &BTreeSet::new(),
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::Compile {
            ref error,
            ..
        }) if matches!(error.as_ref(), MacroExecutionError::Compile(IrExecutionError::Unclassified(_)))
    ));
    assert!(matches!(
        RegisteredMacros::prepare(
            &modules,
            &Environment::new(),
            &code,
            &VerifiedPartition::user_fixture(),
            &users,
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::Owner { .. })
    ));
}
