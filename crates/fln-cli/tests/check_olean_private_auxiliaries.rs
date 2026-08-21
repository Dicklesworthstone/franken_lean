#![forbid(unsafe_code)]

use std::collections::BTreeSet;
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

fn json_object_field<'a>(json: &'a str, field: &str) -> &'a str {
    let marker = format!("\"{field}\":");
    let value = json
        .split_once(&marker)
        .map(|(_, value)| value)
        .expect("JSON report contains the requested object field");
    assert!(value.starts_with('{'), "JSON field is an object: {json}");

    let mut depth = 0_usize;
    let mut in_string = false;
    let mut escaped = false;
    for (index, byte) in value.bytes().enumerate() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'\"' {
                in_string = false;
            }
            continue;
        }
        match byte {
            b'\"' => in_string = true,
            b'{' => depth = depth.saturating_add(1),
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return &value[..=index];
                }
            }
            _ => {}
        }
    }
    panic!("JSON object field is closed: {json}");
}

fn json_usize_field(object: &str, field: &str) -> usize {
    let marker = format!("\"{field}\":");
    let value = object
        .split_once(&marker)
        .map(|(_, value)| value)
        .expect("JSON object contains the requested integer field");
    let digits = value
        .bytes()
        .take_while(|byte| byte.is_ascii_digit())
        .count();
    value[..digits]
        .parse()
        .expect("JSON integer field is a decimal usize")
}

fn json_name_set(object: &str) -> BTreeSet<String> {
    object
        .split("\"name\":\"")
        .skip(1)
        .map(|value| {
            value
                .split_once('\"')
                .map(|(name, _)| name.to_owned())
                .expect("JSON name field is terminated")
        })
        .collect()
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
    let private_loop_eq_def_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "loop",
        "eq_def",
    ]);
    let private_insert_idx_loop_unary_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Syntax",
        "insertIdx",
        "loop",
        "_unary",
    ]);
    let private_eq_n_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "eq_1",
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
    let private_merge_sort_tr_unsafe_rec_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "mergeSortTR",
        "_unsafe_rec",
    ]);
    let string_extra_consume_spaces_unsafe_rec_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Data",
        "String",
        "Extra",
        "0",
        "String",
        "findLeadingSpacesSize",
        "consumeSpaces",
        "_unsafe_rec",
    ]);
    let string_extra_find_next_line_unsafe_rec_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Data",
        "String",
        "Extra",
        "0",
        "String",
        "findLeadingSpacesSize",
        "findNextLine",
        "_unsafe_rec",
    ]);
    let merge_sort_tr_run_unsafe_rec_residual = fln::Name::from_components([
        "_private", "Init", "Data", "List", "Sort", "Impl", "0", "List", "MergeSort",
        "Internal", "mergeSortTR", "run", "_unsafe_rec",
    ]);
    let merge_tr_go_unsafe_rec_residual = fln::Name::from_components([
        "_private", "Init", "Data", "List", "Sort", "Impl", "0", "List", "MergeSort",
        "Internal", "mergeTR", "go", "_unsafe_rec",
    ]);
    let split_rev_at_go_unsafe_rec_residual = fln::Name::from_components([
        "_private", "Init", "Data", "List", "Sort", "Impl", "0", "List", "MergeSort",
        "Internal", "splitRevAt", "go", "_unsafe_rec",
    ]);
    let private_sunfold_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "_sunfold",
    ]);
    let private_f_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "_f",
    ]);
    let private_loop_proof_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "loop",
        "_proof_1",
    ]);
    let private_standalone_proof_n_residual = fln::Name::from_components([
        "_private",
        "CliPrivateReport",
        "0",
        "_proof_2",
    ]);
    let lean_name_hash_proof_one_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Name",
        "hash",
        "_proof_1",
    ]);
    let lean_name_hash_proof_two_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Name",
        "hash",
        "_proof_2",
    ]);
    let lean_name_beq_match_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Name",
        "beq",
        "match_1",
    ]);
    let list_to_array_aux_match_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Data",
        "List",
        "ToArrayImpl",
        "0",
        "List",
        "toArrayAux",
        "match_1",
    ]);
    let core_observables_head_match_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Syntax",
        "getHeadInfo?",
        "match_1",
    ]);
    let core_observables_tail_match_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Syntax",
        "getTailPos?",
        "match_1",
    ]);
    let array_map_m_proof_one_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Data",
        "Array",
        "BasicAux",
        "0",
        "Array",
        "mapM'",
        "_proof_1",
    ]);
    let array_map_m_proof_two_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Data",
        "Array",
        "BasicAux",
        "0",
        "Array",
        "mapM'",
        "_proof_2",
    ]);
    let array_map_m_go_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Data",
        "Array",
        "BasicAux",
        "0",
        "Array",
        "mapM'",
        "go",
    ]);
    let core_observables_head_loop_unsafe_rec_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Syntax",
        "getHeadInfo?",
        "loop",
        "_unsafe_rec",
    ]);
    let core_observables_tail_loop_unsafe_rec_residual = fln::Name::from_components([
        "_private",
        "Init",
        "Prelude",
        "0",
        "Lean",
        "Syntax",
        "getTailPos?",
        "loop",
        "_unsafe_rec",
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
        private_loop_eq_def_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_insert_idx_loop_unary_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_eq_n_residual,
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
        private_merge_sort_tr_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        string_extra_consume_spaces_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        string_extra_find_next_line_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        merge_sort_tr_run_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        merge_tr_go_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        split_rev_at_go_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_sunfold_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_f_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_loop_proof_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        private_standalone_proof_n_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        lean_name_hash_proof_one_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        lean_name_hash_proof_two_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        lean_name_beq_match_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        list_to_array_aux_match_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        core_observables_head_match_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        core_observables_tail_match_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        array_map_m_proof_one_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        array_map_m_proof_two_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        array_map_m_go_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        core_observables_head_loop_unsafe_rec_residual,
        fln::Expr::const_(proposition.clone(), Vec::new()),
    ));
    private_constants.push(axiom(
        core_observables_tail_loop_unsafe_rec_residual,
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
    assert!(json.stdout.contains("\"decodedPrivateAuxiliaries\":29"));
    assert!(json.stdout.contains(
        "\"decodedPrivateLoopAuxiliaries\":{\"observed\":7,"
    ));
    assert!(json.stdout.contains(
        "\"coreObservablesLoopResiduals\":{\"observed\":3,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    let private_eq_def_match = json_object_field(&json.stdout, "privateEqDefMatchResiduals");
    assert_eq!(json_usize_field(private_eq_def_match, "observed"), 8, "{}", json.stdout);
    assert_eq!(json_usize_field(private_eq_def_match, "omitted"), 0, "{}", json.stdout);
    assert_eq!(
        json_name_set(private_eq_def_match),
        BTreeSet::from([
            "_private.CliPrivateReport.0.eq_def".to_owned(),
            "_private.CliPrivateReport.0.loop.eq_def".to_owned(),
            "_private.CliPrivateReport.0.match_1".to_owned(),
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1".to_owned(),
            "_private.Init.Prelude.0.Lean.Name.beq.match_1".to_owned(),
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1".to_owned(),
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1".to_owned(),
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1".to_owned(),
        ]),
        "{}",
        json.stdout,
    );
    assert!(json.stdout.contains(
        "\"privateMatchNResiduals\":{\"observed\":6,\"names\":[{\"name\":\"_private.CliPrivateReport.0.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Name.beq.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateEqDefResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.CliPrivateReport.0.eq_def\",\"nameTruncated\":false},{\"name\":\"_private.CliPrivateReport.0.loop.eq_def\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateEqNResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.CliPrivateReport.0.eq_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateUnsafeRecSunfoldResiduals\":{\"observed\":10,"
    ));
    assert!(json.stdout.contains(
        "\"privateSunfoldFResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.CliPrivateReport.0._f\",\"nameTruncated\":false},{\"name\":\"_private.CliPrivateReport.0._sunfold\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateSunfoldResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.CliPrivateReport.0._sunfold\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateUnsafeRecResiduals\":{\"observed\":9,"
    ));
    assert!(json.stdout.contains(
        "\"privateLoopProofResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.CliPrivateReport.0.loop._proof_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateStandaloneProofNResiduals\":{\"observed\":5,\"names\":[{\"name\":\"_private.CliPrivateReport.0._proof_2\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Name.hash._proof_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Name.hash._proof_2\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"leanNameHashProofResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Name.hash._proof_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Name.hash._proof_2\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"leanNameBeqMatchResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Name.beq.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"listToArrayAuxMatchResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"coreObservablesSyntaxMatchResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"arrayMapMProofResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"arrayMapMGoResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Data.Array.BasicAux.0.Array.mapM'.go\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateGoResiduals\":{\"observed\":3,\"names\":[{\"name\":\"_private.Init.Data.Array.BasicAux.0.Array.mapM'.go\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"stringExtraUnsafeRecResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"mergeSortCompanionOnlyUnsafeRecResiduals\":{\"observed\":3,\"names\":[{\"name\":\"_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateLoopMatchOneResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateLoopMatchNResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateLoopUnsafeRecResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateLoopEqDefResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.CliPrivateReport.0.loop.eq_def\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateInsertIdxLoopUnaryResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateUnaryResiduals\":{\"observed\":1,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains(
        "\"privateMergeSortTRUnsafeRecResiduals\":{\"observed\":2,"
    ));
    assert!(json.stdout.contains(
        "\"coreObservablesLoopUnsafeRecResiduals\":{\"observed\":2,\"names\":[{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec\",\"nameTruncated\":false},{\"name\":\"_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec\",\"nameTruncated\":false}],\"omitted\":0}"
    ));
    assert!(json.stdout.contains("\"g1Satisfied\":false"));

    let human = fln_cli::run([OsString::from("check-olean"), exported.into_os_string()]);
    assert_eq!(human.exit_code, 0, "{}", human.stderr);
    assert!(human.stderr.is_empty());
    assert!(
        human
            .stdout
            .contains("decoded _private auxiliaries: 29 (reporting only; not a G1 claim)")
    );
    assert!(human.stdout.contains(
        "decoded _private.loop auxiliaries: 7 (reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private.loop auxiliary names: _private.CliPrivateReport.0.loop"));
    assert!(human
        .stdout
        .contains("decoded _private.loop auxiliary names omitted: 0"));
    assert!(human.stdout.contains(
        "core-observables .loop residuals: 3 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "core-observables .loop residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec, _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1, _private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("core-observables .loop residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private eq_def/match_N residuals: 8 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private eq_def/match_N residual names: _private.CliPrivateReport.0.eq_def, _private.CliPrivateReport.0.match_1, _private.CliPrivateReport.0.loop.eq_def, _private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1, _private.Init.Prelude.0.Lean.Name.beq.match_1, _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1, _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1, _private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1"
    ));
    assert!(human
        .stdout
        .contains("decoded _private eq_def/match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private match_N residuals: 6 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private match_N residual names: _private.CliPrivateReport.0.match_1, _private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1, _private.Init.Prelude.0.Lean.Name.beq.match_1, _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1, _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1, _private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1"
    ));
    assert!(human
        .stdout
        .contains("decoded _private match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private eq_def residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private eq_def residual names: _private.CliPrivateReport.0.eq_def, _private.CliPrivateReport.0.loop.eq_def"
    ));
    assert!(human
        .stdout
        .contains("decoded _private eq_def residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private eq_N residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private eq_N residual names: _private.CliPrivateReport.0.eq_1"));
    assert!(human
        .stdout
        .contains("decoded _private eq_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private _unsafe_rec/_sunfold residuals: 10 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private _unsafe_rec/_sunfold residual names: _private.CliPrivateReport.0._sunfold"));
    assert!(human
        .stdout
        .contains("decoded _private _unsafe_rec/_sunfold residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private _sunfold/_f residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private _sunfold/_f residual names: _private.CliPrivateReport.0._f, _private.CliPrivateReport.0._sunfold"
    ));
    assert!(human
        .stdout
        .contains("decoded _private _sunfold/_f residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private _sunfold residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private _sunfold residual names: _private.CliPrivateReport.0._sunfold"));
    assert!(human
        .stdout
        .contains("decoded _private _sunfold residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private _unsafe_rec residuals: 9 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private _unsafe_rec residual names: _private.CliPrivateReport.0._unsafe_rec"));
    assert!(human
        .stdout
        .contains("decoded _private _unsafe_rec residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private .loop._proof_* residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private .loop._proof_* residual names: _private.CliPrivateReport.0.loop._proof_1"
    ));
    assert!(human
        .stdout
        .contains("decoded _private .loop._proof_* residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded standalone _private _proof_N residuals: 5 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded standalone _private _proof_N residual names: _private.CliPrivateReport.0._proof_2, _private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1, _private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2, _private.Init.Prelude.0.Lean.Name.hash._proof_1, _private.Init.Prelude.0.Lean.Name.hash._proof_2"));
    assert!(human
        .stdout
        .contains("decoded standalone _private _proof_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private Lean.Name.hash._proof_N residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private Lean.Name.hash._proof_N residual names: _private.Init.Prelude.0.Lean.Name.hash._proof_1, _private.Init.Prelude.0.Lean.Name.hash._proof_2"
    ));
    assert!(human
        .stdout
        .contains("decoded _private Lean.Name.hash._proof_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private Lean.Name.beq.match_N residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private Lean.Name.beq.match_N residual names: _private.Init.Prelude.0.Lean.Name.beq.match_1"));
    assert!(human
        .stdout
        .contains("decoded _private Lean.Name.beq.match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private List.toArrayAux.match_N residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private List.toArrayAux.match_N residual names: _private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"));
    assert!(human
        .stdout
        .contains("decoded _private List.toArrayAux.match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "core-observables Lean.Syntax match_N residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "core-observables Lean.Syntax match_N residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1, _private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1"
    ));
    assert!(human
        .stdout
        .contains("core-observables Lean.Syntax match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private Array.mapM'._proof_N residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private Array.mapM'._proof_N residual names: _private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1, _private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2"
    ));
    assert!(human
        .stdout
        .contains("decoded _private Array.mapM'._proof_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private Array.mapM'.go residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private Array.mapM'.go residual names: _private.Init.Data.Array.BasicAux.0.Array.mapM'.go"));
    assert!(human
        .stdout
        .contains("decoded _private Array.mapM'.go residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private .go residuals: 3 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private .go residual names: _private.Init.Data.Array.BasicAux.0.Array.mapM'.go, _private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec, _private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("decoded _private .go residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private String.findLeadingSpacesSize _unsafe_rec residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private String.findLeadingSpacesSize _unsafe_rec residual names: _private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec, _private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("decoded _private String.findLeadingSpacesSize _unsafe_rec residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private List.MergeSort companion-only _unsafe_rec residuals: 3 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private List.MergeSort companion-only _unsafe_rec residual names: _private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec, _private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec, _private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("decoded _private List.MergeSort companion-only _unsafe_rec residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private .loop.match_1 residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private .loop.match_1 residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"
    ));
    assert!(human
        .stdout
        .contains("decoded _private .loop.match_1 residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private .loop.match_N residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private .loop.match_N residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"
    ));
    assert!(human
        .stdout
        .contains("decoded _private .loop.match_N residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private .loop._unsafe_rec residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private .loop._unsafe_rec residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec, _private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("decoded _private .loop._unsafe_rec residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private .loop.eq_def residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private .loop.eq_def residual names: _private.CliPrivateReport.0.loop.eq_def"));
    assert!(human
        .stdout
        .contains("decoded _private .loop.eq_def residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private insertIdx.loop._unary residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "decoded _private insertIdx.loop._unary residual names: _private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary"
    ));
    assert!(human
        .stdout
        .contains("decoded _private insertIdx.loop._unary residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private _unary residuals: 1 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private _unary residual names: _private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary"));
    assert!(human
        .stdout
        .contains("decoded _private _unary residual names omitted: 0"));
    assert!(human.stdout.contains(
        "decoded _private mergeSortTR._unsafe_rec residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human
        .stdout
        .contains("decoded _private mergeSortTR._unsafe_rec residual names: _private.CliPrivateReport.0.mergeSortTR._unsafe_rec"));
    assert!(human
        .stdout
        .contains("decoded _private mergeSortTR._unsafe_rec residual names omitted: 0"));
    assert!(human.stdout.contains(
        "core-observables Lean.Syntax .loop._unsafe_rec residuals: 2 (decoded companion names; reporting only; not a G1 claim)"
    ));
    assert!(human.stdout.contains(
        "core-observables Lean.Syntax .loop._unsafe_rec residual names: _private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec, _private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec"
    ));
    assert!(human
        .stdout
        .contains("core-observables Lean.Syntax .loop._unsafe_rec residual names omitted: 0"));
    assert!(human.stdout.contains("G1 satisfied: no"));
}
