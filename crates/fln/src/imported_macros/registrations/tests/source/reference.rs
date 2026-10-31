//! Actual pinned Lean source macros, decoded from their emitted attribute
//! journal and executed as imported IR before the Engine's ordinary checker.
use super::*;
use fln_olean::region::{OleanView, WalkBudget};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_imported_ir_changes_source_checks_with_the_pins_order_and_scoped_behavior() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for imported macro source checks"
        );
        eprintln!("SKIP: imported source macro reference requires FLN_REFERENCE_LEAN");
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
    let dir = root.join(format!("source-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeSourceMacroModule.lean"
    ));
    std::fs::write(dir.join("NativeSourceMacroModule.lean"), source).unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "NativeSourceMacroModule.olean",
            "NativeSourceMacroModule.lean",
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
        result.stdout,
        b"Bool : Type\n11\n11\nNat : Type\n7\n7\nBool : Type\n11\n11\n11\n"
    );
    assert!(result.stderr.is_empty());
    // Same successful prefix, one false proof appended. A query's preceding
    // output does not make a failing file a positive oracle result.
    std::fs::write(
        dir.join("FalseSourceMacroModule.lean"),
        format!("{source}\nexample : pinDeclaredValue = 18 := by rfl\n"),
    )
    .unwrap();
    let rejected = Command::new(&reference)
        .current_dir(&dir)
        .arg("FalseSourceMacroModule.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("false.stdout"), &rejected.stdout).unwrap();
    std::fs::write(dir.join("false.stderr"), &rejected.stderr).unwrap();
    assert!(
        !rejected.status.success(),
        "the pin must refuse the false theorem"
    );

    let public = std::fs::read(dir.join("NativeSourceMacroModule.olean")).unwrap();
    let server = std::fs::read(dir.join("NativeSourceMacroModule.olean.server")).unwrap();
    let private = std::fs::read(dir.join("NativeSourceMacroModule.olean.private")).unwrap();
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
    let plus_rows: Vec<_> = rows
        .iter()
        .filter(|row| row.key == name("term_+_"))
        .collect();
    assert_eq!(plus_rows.len(), 3);
    assert_eq!(plus_rows[0].declaration, name("sourceChooseRight"));
    assert_eq!(plus_rows[1].declaration, name("sourceTryNext"));
    assert_eq!(
        plus_rows[2].declaration,
        name("SourceScoped.sourceChooseLeft")
    );
    assert_eq!(plus_rows[2].scope, Some(name("SourceScoped")));
    let code = [crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeSourceMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap()];

    // Exact decoded owners are test caller inputs, as in the parent live
    // registry test. This does not claim to admit Lean's full import closure.
    let root = Environment::new().logical_root(&KVMap::new());
    let module = CheckedOleanModule {
        name: name("NativeSourceMacroModule"),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: Vec::new(),
    };
    let registry = RegisteredMacros::prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &extensions,
        }],
        &environment(&[&module]),
        &code,
        &VerifiedPartition::user_fixture(),
        &users(&code),
        MacroRegistryLimits::default(),
    )
    .unwrap_or_else(|error| panic!("{error}; {dir:?}"));
    let engine = bound_engine(&module);
    let before = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_command(b"#check (Nat + Bool)", &KVMap::new(), admission())
            .is_err()
    );

    let report = run(
        &engine,
        &registry,
        b"#check (Nat + Bool)",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&report, "Bool");
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(report.attempts[0].declaration, name("sourceTryNext"));
    assert_eq!(report.attempts[1].declaration, name("sourceChooseRight"));
    assert!(report.attempts.iter().all(|attempt| {
        attempt
            .reference_functions
            .iter()
            .any(|function| function.name == attempt.declaration)
    }));
    let scoped = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let scoped_report = run(
        &engine,
        &scoped,
        b"#check (Nat + Bool)",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&scoped_report, "Nat");
    assert_eq!(scoped_report.attempts.len(), 1);
    assert_eq!(
        scoped_report.attempts[0].declaration,
        name("SourceScoped.sourceChooseLeft")
    );
    let diagnostic = run(
        &engine,
        &registry,
        b"#check Nat - Bool",
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(
        diagnostic.outcome,
        Outcome::Complete(Err(SourceMacroError::Diagnostic { message, .. }))
            if message == "source macro diagnostic"
    ));
    assert!(diagnostic.state.is_none());
    let mut artifacts = Vec::new();
    for (active, expected) in [(&registry, 11), (&scoped, 7), (&registry, 11)] {
        let report = evaluate(
            &engine,
            active,
            b"#eval (7 + 11)",
            MacroTreeLimits::default(),
            execution_limits(),
            None,
        );
        let result = evaluated_nat(&report, expected);
        artifacts.push(result.execution.flbc_artifact.clone());
        assert!(report.attempts.iter().all(|attempt| {
            attempt
                .reference_functions
                .iter()
                .any(|function| function.name == attempt.declaration)
        }));
    }
    assert_eq!(artifacts[0], artifacts[2]);
    assert_ne!(artifacts[0], artifacts[1]);
    let named = admit(
        &engine,
        &registry,
        b"def nativeDeclaredValue : Nat := 7 + 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    let named = admitted(&named);
    assert_declared_value(&named.admission.engine, "nativeDeclaredValue", 11);
    let proof = admit(
        &named.admission.engine,
        &registry,
        b"theorem nativeDeclaredValue_eq : nativeDeclaredValue = 11 := by rfl",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    admitted(&proof);
    let false_proof = admit(
        &named.admission.engine,
        &registry,
        b"theorem falseDeclaredValue : nativeDeclaredValue = 18 := by rfl",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert!(matches!(
        false_proof.outcome,
        Outcome::Complete(Err(SourceMacroError::Frontend(_)))
    ));
    assert!(false_proof.state.is_none());
    let scoped_named = admit(
        &engine,
        &scoped,
        b"def nativeScopedDeclaredValue : Nat := 7 + 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert_declared_value(
        &admitted(&scoped_named).admission.engine,
        "nativeScopedDeclaredValue",
        7,
    );
    let helper = admit(&engine, &registry, b"def nativeDeclaredHelper (n : Nat) : Nat := let helper (x : Nat) : Nat := x + 11; helper n", MacroTreeLimits::default(), admission(), None);
    let helper = admitted(&helper);
    assert!(helper.admission.admissions.len() >= 2);
    assert_declared_value(&helper.admission.engine, "nativeDeclaredHelper 7", 11);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
