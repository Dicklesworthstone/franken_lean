#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::path::Path;

fn module_bytes(constants: &[fln::ConstantInfo], base_addr: u64) -> Vec<u8> {
    let lean_version = fln::OLEAN_PIN_TAG
        .strip_prefix('v')
        .expect("the pin tag starts with v");
    fln::encode_olean_module(
        fln::OleanModuleWriteInput {
            is_module: true,
            imports: &[],
            constants,
            extra_const_names: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version,
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr,
        },
        fln::OleanWriteBudget::default(),
    )
    .expect("the module-system reporting fixture encodes")
    .bytes
}

fn axiom(name: fln::Name, type_: fln::Expr) -> fln::ConstantInfo {
    fln::ConstantInfo::Axiom(fln::AxiomVal {
        base: fln::ConstantVal {
            name,
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    })
}

fn write(path: &Path, bytes: Vec<u8>) {
    std::fs::write(path, bytes).expect("write module-system reporting fixture");
}

#[test]
fn check_olean_reports_private_auxiliaries_from_the_authoritative_companion_part() {
    let proposition = fln::Name::from_components(["CliPrivateReport", "P"]);
    let public_witness = fln::Name::from_components(["CliPrivateReport", "witness"]);
    let private_auxiliary = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "loop",
    ]);
    let core_observables_loop_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Syntax",
        "getHeadInfo?",
        "loop",
        "match_1",
    ]);
    let private_eq_def_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "eq_def",
    ]);
    let private_match_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "match_1",
    ]);
    let private_unsafe_rec_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "_unsafe_rec",
    ]);
    let private_sunfold_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "_sunfold",
    ]);
    let proposition_type = fln::Expr::sort(fln::Level::zero());
    let proposition_expr = fln::Expr::const_(proposition.clone(), Vec::new());
    let public_constants = vec![
        axiom(proposition.clone(), proposition_type),
        axiom(public_witness, proposition_expr.clone()),
    ];
    let mut private_constants = public_constants.clone();
    private_constants.push(axiom(private_auxiliary, proposition_expr));
    private_constants.push(axiom(
        core_observables_loop_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_eq_def_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_match_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_sunfold_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));

    let unique = format!(
        "fln-cli-check-olean-private-auxiliaries-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system time is after the Unix epoch")
            .as_nanos()
    );
    let root = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(Into::into)
        .unwrap_or_else(std::env::temp_dir)
        .join(unique);
    std::fs::create_dir_all(&root).expect("create module-system reporting fixture directory");
    let exported = root.join("CliPrivateReport.olean");
    write(
        &exported,
        module_bytes(&public_constants, (fln::OLEAN_REGION_ALIGN as u64) * 2),
    );
    write(
        &root.join("CliPrivateReport.olean.server"),
        module_bytes(&[], (fln::OLEAN_REGION_ALIGN as u64) * 4),
    );
    write(
        &root.join("CliPrivateReport.olean.private"),
        module_bytes(&private_constants, (fln::OLEAN_REGION_ALIGN as u64) * 6),
    );

    let json = fln_cli::run([
        OsString::from("check-olean"),
        OsString::from("--json"),
        exported.clone().into_os_string(),
    ]);
    assert_eq!(json.exit_code, 0, "{}", json.stderr);
    assert!(json.stderr.is_empty());
    assert!(json.stdout.contains("\"companionPartsLoaded\":true"));
    assert!(json.stdout.contains("\"decodedPrivateAuxiliaries\":6"));
    assert!(json.stdout.contains(
        "\"decodedPrivateLoopAuxiliaries\":{\"observed\":2,"
    ));
    assert!(json.stdout.contains(
        "\"coreObservablesLoopResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateEqDefMatchResiduals\":{\"observed\":3,\"names\":[{\"name\":\"_private.CliPrivateReport.0.eq_def\",\"nameTruncated\":false},{\"name\":\"_private.CliPrivateReport.0.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateUnsafeRecSunfoldResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.CliPrivateReport.0._sunfold\",\"nameTruncated\":false},{\"name\":\"_private.CliPrivateReport.0._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains("\"g1Satisfied\":false"));

    let human = fln_cli::run([OsString::from("check-olean"), exported.into_os_string()]);
    assert_eq!(human.exit_code, 0, "{}", human.stderr);
    assert!(human.stderr.is_empty());
    assert!(
        human
            .stdout
            .contains("decoded _private auxiliaries: 6 (reporting only; not a G1 claim)")
    );
    assert!(human.stdout.contains(
        "decoded _private.loop auxiliaries: 2 (reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private.loop auxiliary names: _private.CliPrivateReport.0.loop"));
    assert!(human
        .stdout
        .contains("decoded _private.loop auxiliary names omitted: 0"));
    assert!(human.stdout.contains(
        "core-observables .loop residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "core-observables .loop residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"
    ));
    assert!(human
        .stdout
        .contains("core-observables .loop residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private eq_def/match_N residuals: 3 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private eq_def/match_N residual names: _private.CliPrivateReport.0.eq_def, _private.CliPrivateReport.0.match_1, _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"
    ));
    assert!(human
        .stdout
        .contains("decoded _private eq_def/match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private _unsafe_rec/_sunfold residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private _unsafe_rec/_sunfold residual names: _private.CliPrivateReport.0._sunfold, _private.CliPrivateReport.0._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("decoded _private _unsafe_rec/_sunfold residual names omitted: 0"));
    assert!(human.stdout.contains("G1 satisfied: no"));
}
