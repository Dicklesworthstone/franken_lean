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

fn json_array_field<'a>(json: &'a str, field: &str) -> &'a str {
    let marker = format!("\"{field}\":");
    let value = json
        .split_once(&marker)
        .map(|(_, value)| value)
        .unwrap_or_else(|| panic!("missing required JSON array field `{field}`: {json}"));
    assert!(value.starts_with('['), "JSON field is an array: {json}");

    let mut depth = 0_usize;
    let mut in_string = false;
    let mut escaped = false;
    for (index, byte) in value.bytes().enumerate() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }
        match byte {
            b'"' => in_string = true,
            b'[' => depth = depth.saturating_add(1),
            b']' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return &value[..=index];
                }
            }
            _ => {}
        }
    }
    panic!("JSON array field is closed: {json}");
}

fn json_array_len(array: &str) -> usize {
    assert!(array.starts_with('[') && array.ends_with(']'));

    let mut object_depth = 0_usize;
    let mut array_depth = 0_usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut values = 0_usize;
    let mut value_started = false;

    for byte in array.as_bytes()[1..array.len() - 1].iter().copied() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }

        match byte {
            byte if byte.is_ascii_whitespace() => {}
            b'"' => {
                value_started = true;
                in_string = true;
            }
            b'{' => {
                value_started = true;
                object_depth = object_depth.saturating_add(1);
            }
            b'}' => object_depth = object_depth.saturating_sub(1),
            b'[' => {
                value_started = true;
                array_depth = array_depth.saturating_add(1);
            }
            b']' => array_depth = array_depth.saturating_sub(1),
            b',' if object_depth == 0 && array_depth == 0 => {
                assert!(value_started, "JSON array does not have an empty element");
                values = values.saturating_add(1);
                value_started = false;
            }
            _ => value_started = true,
        }
    }

    assert!(
        !in_string && object_depth == 0 && array_depth == 0,
        "JSON array is closed",
    );
    values.saturating_add(usize::from(value_started))
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
    assert!(digits > 0, "JSON integer field starts with a number: {object}");
    assert!(
        matches!(value.as_bytes().get(digits), Some(b',') | Some(b'}')),
        "JSON integer field is terminated: {object}",
    );
    value[..digits]
        .parse()
        .expect("JSON integer field is a decimal usize")
}

fn json_bool_field(object: &str, field: &str) -> bool {
    let marker = format!("\"{field}\":");
    let value = object
        .split_once(&marker)
        .map(|(_, value)| value)
        .expect("JSON object contains the requested boolean field");
    match value.strip_prefix("true") {
        Some(_) => true,
        None => match value.strip_prefix("false") {
            Some(_) => false,
            None => panic!("JSON boolean field has a boolean value"),
        },
    }
}

fn json_object_key_set(object: &str) -> BTreeSet<String> {
    assert!(object.starts_with('{') && object.ends_with('}'));

    let bytes = object.as_bytes();
    let mut keys = BTreeSet::new();
    let mut object_depth = 0_usize;
    let mut array_depth = 0_usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut key_start = None;

    for (index, byte) in bytes.iter().copied().enumerate() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
                if let Some(start) = key_start.take() {
                    keys.insert(object[start..index].to_owned());
                }
            }
            continue;
        }

        match byte {
            b'{' => object_depth = object_depth.saturating_add(1),
            b'}' => object_depth = object_depth.saturating_sub(1),
            b'[' => array_depth = array_depth.saturating_add(1),
            b']' => array_depth = array_depth.saturating_sub(1),
            b'"' => {
                let previous = bytes[..index]
                    .iter()
                    .rev()
                    .copied()
                    .find(|byte| !byte.is_ascii_whitespace());
                if object_depth == 1
                    && array_depth == 0
                    && matches!(previous, Some(b'{') | Some(b','))
                {
                    key_start = Some(index + 1);
                }
                in_string = true;
            }
            _ => {}
        }
    }

    assert!(!in_string && key_start.is_none(), "JSON object keys are closed");
    keys
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

fn json_non_empty_name_strings(array: &str) -> Vec<String> {
    let marker = "\"name\":";
    let mut names = Vec::new();
    let mut cursor = 0_usize;

    while let Some(offset) = array[cursor..].find(marker) {
        let value_start = cursor + offset + marker.len();
        assert_eq!(
            array.as_bytes().get(value_start),
            Some(&b'"'),
            "JSON name value is a string: {array}",
        );

        let mut escaped = false;
        let mut value_end = None;
        for (offset, byte) in array.as_bytes()[value_start + 1..].iter().copied().enumerate() {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                value_end = Some(value_start + 1 + offset);
                break;
            }
        }
        let value_end = value_end.expect("JSON name string is closed");
        assert!(value_end > value_start + 1, "JSON name string is non-empty");
        names.push(array[value_start + 1..value_end].to_owned());
        cursor = value_end + 1;
    }

    names
}

fn json_name_strings_are_subsequence(names: &[String], decoded_names: &[String]) -> bool {
    let mut next_name = 0_usize;
    for decoded_name in decoded_names {
        if next_name < names.len() && names[next_name].as_str() == decoded_name.as_str() {
            next_name = next_name.saturating_add(1);
        }
    }
    next_name == names.len()
}

fn assert_json_named_residuals(json: &str, field: &str, observed: usize, expected_names: &[&str]) {
    let residuals = json_object_field(json, field);
    let actual_observed = json_usize_field(residuals, "observed");
    let actual_names = json_name_set(residuals);
    let decoded_name_entries = residuals.matches("\"name\":\"").count();
    assert_eq!(actual_observed, observed, "{json}");
    assert_eq!(actual_observed, actual_names.len(), "{field}: {json}");
    assert_eq!(decoded_name_entries, actual_names.len(), "{field}: {json}");
    assert_eq!(json_usize_field(residuals, "omitted"), 0, "{json}");
    assert_eq!(
        actual_names,
        expected_names
            .iter()
            .map(|name| (*name).to_owned())
            .collect::<BTreeSet<_>>(),
        "{json}",
    );
}

fn assert_json_private_companion_residual_report(report: &fln_cli::MultiplexerOutput) {
    assert_eq!(report.exit_code, 0, "{}", report.stderr);
    assert!(report.stderr.is_empty());
    assert_eq!(
        include_str!("../src/lib.rs")
            .match_indices(r#"\"decodedPrivateAuxiliaryNames\":{}"#)
            .count(),
        2,
        "both check-olean JSON render paths emit decodedPrivateAuxiliaryNames",
    );
    assert_eq!(
        include_str!("../src/lib.rs")
            .match_indices(
                r#"\"decodedPrivateLoopAuxiliaries\":{{\"observed\":{},\"names\":{},\"omitted\":{},\"missing\":{}}}"#,
            )
            .count(),
        2,
        "both check-olean JSON render paths emit the decoded-private loop object",
    );

    let json = &report.stdout;
    let g1_satisfied = json_bool_field(json, "g1Satisfied");
    assert!(!g1_satisfied, "{json}");
    let companion_parts_loaded = json_bool_field(json, "companionPartsLoaded");
    let private_companion_residuals = json_object_field(json, "privateCompanionResiduals");
    assert_eq!(
        json_object_key_set(private_companion_residuals),
        ["missing", "names", "observed", "omitted"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
        "{json}",
    );
    let private_companion_omitted = json_usize_field(private_companion_residuals, "omitted");
    assert_eq!(private_companion_omitted, 0, "{json}");
    let private_companion_missing = json_usize_field(private_companion_residuals, "missing");
    assert_eq!(private_companion_missing, 0, "{json}");
    let private_companion_observed = json_usize_field(private_companion_residuals, "observed");
    let private_companion_names = json_array_field(private_companion_residuals, "names");
    let private_companion_name_count = json_array_len(private_companion_names);
    let private_companion_name_strings = json_non_empty_name_strings(private_companion_names);
    assert!(
        private_companion_name_strings
            .iter()
            .all(|name| name.starts_with("_private.")),
        "{json}",
    );
    let private_companion_name_set = private_companion_name_strings
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        private_companion_name_set.len(),
        private_companion_name_count,
        "{json}",
    );
    assert_eq!(
        private_companion_name_count,
        private_companion_observed,
        "{json}",
    );
    assert_eq!(
        private_companion_observed == 0,
        private_companion_name_count == 0,
        "{json}",
    );
    let decoded_private_auxiliary_names = json_array_field(
        json,
        "decodedPrivateAuxiliaryNames",
    );
    let decoded_private_auxiliary_name_count = json_array_len(decoded_private_auxiliary_names);
    let decoded_private_auxiliaries = json_usize_field(json, "decodedPrivateAuxiliaries");
    assert_eq!(
        decoded_private_auxiliaries,
        private_companion_name_count,
        "{json}",
    );
    assert!(
        decoded_private_auxiliaries == 0 || companion_parts_loaded,
        "{json}",
    );
    assert!(
        decoded_private_auxiliaries > 0 && !g1_satisfied,
        "{json}",
    );
    assert_eq!(
        decoded_private_auxiliary_name_count,
        private_companion_observed,
        "{json}",
    );
    assert_eq!(
        decoded_private_auxiliary_name_count,
        decoded_private_auxiliaries,
        "{json}",
    );
    let decoded_private_auxiliary_name_strings =
        json_non_empty_name_strings(decoded_private_auxiliary_names);
    assert!(
        decoded_private_auxiliary_name_strings
            .iter()
            .all(|name| name.starts_with("_private.")),
        "{json}",
    );
    let decoded_private_auxiliary_name_set = decoded_private_auxiliary_name_strings
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        decoded_private_auxiliary_name_set.len(),
        decoded_private_auxiliary_name_count,
        "{json}",
    );
    assert!(
        private_companion_name_set.is_subset(&decoded_private_auxiliary_name_set),
        "{json}",
    );
    assert!(
        json_name_strings_are_subsequence(
            &private_companion_name_strings,
            &decoded_private_auxiliary_name_strings,
        ),
        "{json}",
    );
    assert_eq!(
        private_companion_omitted
            .checked_add(private_companion_name_count)
            .and_then(|count| count.checked_add(private_companion_missing))
            .expect("private companion residual counters do not overflow"),
        decoded_private_auxiliaries,
        "{json}",
    );
    let decoded_private_loop_auxiliaries = json_object_field(json, "decodedPrivateLoopAuxiliaries");
    assert_eq!(
        json_object_key_set(decoded_private_loop_auxiliaries),
        ["missing", "names", "observed", "omitted"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
        "{json}",
    );
    assert_eq!(
        [
            json_usize_field(decoded_private_loop_auxiliaries, "omitted"),
            json_usize_field(decoded_private_loop_auxiliaries, "missing"),
        ],
        [0, 0],
        "{json}",
    );
    let decoded_private_loop_observed =
        json_usize_field(decoded_private_loop_auxiliaries, "observed");
    let decoded_private_loop_names = json_array_field(
        decoded_private_loop_auxiliaries,
        "names",
    );
    let decoded_private_loop_name_count = json_array_len(decoded_private_loop_names);
    assert_eq!(
        decoded_private_loop_observed > 0,
        decoded_private_loop_name_count > 0,
        "{json}",
    );
    assert_eq!(
        decoded_private_loop_observed == 0,
        decoded_private_loop_name_count == 0,
        "{json}",
    );
    let decoded_private_loop_name_strings =
        json_non_empty_name_strings(decoded_private_loop_names);
    assert!(
        decoded_private_loop_name_strings
            .iter()
            .all(|name| name.starts_with("_private.")),
        "{json}",
    );
    let decoded_private_loop_name_set = decoded_private_loop_name_strings
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        decoded_private_loop_name_set.len(),
        decoded_private_loop_name_count,
        "{json}",
    );
    assert_eq!(
        decoded_private_loop_name_count,
        decoded_private_loop_observed,
        "{json}",
    );
    assert!(
        decoded_private_loop_name_set.is_subset(&private_companion_name_set),
        "{json}",
    );
    assert!(
        json_name_strings_are_subsequence(
            &decoded_private_loop_name_strings,
            &private_companion_name_strings,
        ),
        "{json}",
    );
    assert!(
        decoded_private_loop_name_set.is_subset(&decoded_private_auxiliary_name_set),
        "{json}",
    );
    assert!(
        json_name_strings_are_subsequence(
            &decoded_private_loop_name_strings,
            &decoded_private_auxiliary_name_strings,
        ),
        "{json}",
    );
    assert!(
        decoded_private_loop_observed <= decoded_private_auxiliaries,
        "{json}",
    );
    assert_eq!(
        decoded_private_auxiliaries > 0,
        decoded_private_loop_observed > 0,
        "{json}",
    );
}

fn assert_json_private_companion_partition_is_disjoint(json: &str, fields: &[&str]) {
    let private_companions = json_name_set(json_object_field(json, "privateCompanionResiduals"));
    let groups = fields
        .iter()
        .map(|field| (field, json_name_set(json_object_field(json, field))))
        .collect::<Vec<_>>();

    let mut covered = BTreeSet::new();
    for (field, names) in &groups {
        assert!(
            names.is_subset(&private_companions),
            "{field} includes a name outside privateCompanionResiduals: {json}",
        );
        covered.extend(names.iter().cloned());
    }

    for (index, (left_field, left_names)) in groups.iter().enumerate() {
        for (right_field, right_names) in groups.iter().skip(index + 1) {
            assert!(
                left_names.is_disjoint(right_names),
                "{left_field} overlaps {right_field}: {json}",
            );
        }
    }

    assert_eq!(covered, private_companions, "{json}");
}

fn assert_json_named_residual_groups_are_non_empty(json: &str, fields: &[&str]) {
    for field in fields {
        let residuals = json_object_field(json, field);
        assert!(
            json_usize_field(residuals, "observed") > 0,
            "{field} is vacuous: {json}",
        );
        assert!(
            !json_name_set(residuals).is_empty(),
            "{field} has no decoded names: {json}",
        );
        assert_eq!(json_usize_field(residuals, "omitted"), 0, "{json}");
    }
}

fn assert_json_residual_group_union_equals(json: &str, expected_field: &str, fields: &[&str]) {
    let expected = json_name_set(json_object_field(json, expected_field));
    let mut covered = BTreeSet::new();

    for field in fields {
        let names = json_name_set(json_object_field(json, field));
        assert!(
            names.is_subset(&expected),
            "{field} includes a name outside {expected_field}: {json}",
        );
        covered.extend(names);
    }

    assert_eq!(covered, expected, "{json}");
}

fn assert_canonical_residual_group_keys_match_human_prefixes(json: &str, human: &str) {
    let json_keys = [
        "privateCliPrivateReportResiduals",
        "privateInitDataResiduals",
        "privateInitPreludeResiduals",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect::<BTreeSet<_>>();
    for key in &json_keys {
        let _ = json_object_field(json, key);
    }

    let human_keys = human
        .lines()
        .filter_map(|line| line.strip_prefix("decoded _private "))
        .filter_map(|line| line.split_once(" residuals:").map(|(prefix, _)| prefix))
        .filter(|prefix| matches!(*prefix, "CliPrivateReport" | "Init.Data" | "Init.Prelude"))
        .map(|prefix| format!("private{}Residuals", prefix.replace('.', "")))
        .collect::<BTreeSet<_>>();

    assert_eq!(human_keys, json_keys, "{json}\n{human}");
}

fn human_line_suffix<'a>(stdout: &'a str, prefix: &str) -> &'a str {
    stdout
        .lines()
        .find_map(|line| line.strip_prefix(prefix))
        .unwrap_or_else(|| panic!("human report is missing {prefix:?}: {stdout}"))
}

fn assert_human_named_residuals(
    stdout: &str,
    summary_label: &str,
    names_label: &str,
    observed: usize,
    expected_names: &[&str],
) {
    let observed_text = human_line_suffix(stdout, &format!("{summary_label}: "));
    let actual_observed = observed_text
        .split_once(" (")
        .map(|(value, _)| value)
        .expect("human residual summary has a reporting suffix")
        .parse::<usize>()
        .expect("human residual observed count is a usize");
    assert_eq!(actual_observed, observed, "{stdout}");

    let rendered_names = human_line_suffix(stdout, &format!("{names_label}: "));
    let actual_names = if rendered_names == "none" {
        BTreeSet::new()
    } else {
        rendered_names
            .split(", ")
            .map(str::to_owned)
            .collect::<BTreeSet<_>>()
    };
    let expected_names = expected_names
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(actual_names, expected_names, "{stdout}");

    let omitted = human_line_suffix(stdout, &format!("{names_label} omitted: "))
        .parse::<usize>()
        .expect("human residual omitted count is a usize");
    assert_eq!(omitted, 0, "{stdout}");
}

#[test]
#[should_panic(expected = "missing required JSON array field `decodedPrivateAuxiliaryNames`")]
fn decoded_private_auxiliary_names_is_required() {
    let _ = json_array_field("{}", "decodedPrivateAuxiliaryNames");
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
    let private_companion_names = &[
        "_private.CliPrivateReport.0._f",
        "_private.CliPrivateReport.0._proof_2",
        "_private.CliPrivateReport.0._sunfold",
        "_private.CliPrivateReport.0._unsafe_rec",
        "_private.CliPrivateReport.0.eq_1",
        "_private.CliPrivateReport.0.eq_def",
        "_private.CliPrivateReport.0.loop",
        "_private.CliPrivateReport.0.loop.eq_def",
        "_private.CliPrivateReport.0.loop._proof_1",
        "_private.CliPrivateReport.0.match_1",
        "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
        "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
        "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
        "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
        "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
        "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
        "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Name.beq.match_1",
        "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
        "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
    ];
    assert_json_named_residuals(
        &json.stdout,
        "decodedPrivateLoopAuxiliaries",
        7,
        &[
            "_private.CliPrivateReport.0.loop",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.loop._proof_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCompanionResiduals",
        29,
        private_companion_names,
    );
    assert_json_private_companion_partition_is_disjoint(
        &json.stdout,
        &[
            "privateCliPrivateReportResiduals",
            "privateInitDataResiduals",
            "privateInitPreludeResiduals",
        ],
    );
    assert_json_named_residual_groups_are_non_empty(
        &json.stdout,
        &[
            "coreObservablesLoopResiduals",
            "privateInitPreludeUnsafeRecResiduals",
            "privateInitPreludeProofNResiduals",
            "leanNameHashProofResiduals",
            "leanNameBeqMatchResiduals",
            "privateLeanNameResiduals",
            "privateInitPreludeResiduals",
            "coreObservablesSyntaxMatchResiduals",
            "privateLeanSyntaxResiduals",
            "privateLoopMatchOneResiduals",
            "privateLoopMatchNResiduals",
            "privateLoopUnsafeRecResiduals",
            "privateInsertIdxLoopUnaryResiduals",
            "privateUnaryResiduals",
            "coreObservablesLoopUnsafeRecResiduals",
        ],
    );
    assert_json_residual_group_union_equals(
        &json.stdout,
        "privateInitPreludeResiduals",
        &[
            "privateInitPreludeProofNResiduals",
            "leanNameBeqMatchResiduals",
            "privateInitPreludeUnsafeRecResiduals",
            "coreObservablesSyntaxMatchResiduals",
            "privateLoopMatchNResiduals",
            "privateInsertIdxLoopUnaryResiduals",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportLoopResiduals",
        3,
        &[
            "_private.CliPrivateReport.0.loop",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.loop._proof_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportResiduals",
        11,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0._sunfold",
            "_private.CliPrivateReport.0._unsafe_rec",
            "_private.CliPrivateReport.0.eq_1",
            "_private.CliPrivateReport.0.eq_def",
            "_private.CliPrivateReport.0.loop",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.loop._proof_1",
            "_private.CliPrivateReport.0.match_1",
            "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "coreObservablesLoopResiduals",
        3,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateEqDefMatchResiduals",
        8,
        &[
            "_private.CliPrivateReport.0.eq_def",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.match_1",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateMatchNResiduals",
        6,
        &[
            "_private.CliPrivateReport.0.match_1",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportMatchResiduals",
        1,
        &["_private.CliPrivateReport.0.match_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportEquationResiduals",
        4,
        &[
            "_private.CliPrivateReport.0.eq_1",
            "_private.CliPrivateReport.0.eq_def",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.match_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateEqDefResiduals",
        2,
        &[
            "_private.CliPrivateReport.0.eq_def",
            "_private.CliPrivateReport.0.loop.eq_def",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateEqNResiduals",
        1,
        &["_private.CliPrivateReport.0.eq_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateUnsafeRecSunfoldResiduals",
        10,
        &[
            "_private.CliPrivateReport.0._sunfold",
            "_private.CliPrivateReport.0._unsafe_rec",
            "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateSunfoldFResiduals",
        2,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._sunfold",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportSunfoldFResiduals",
        2,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._sunfold",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportFResiduals",
        1,
        &["_private.CliPrivateReport.0._f"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportImplementationAuxResiduals",
        4,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0._sunfold",
            "_private.CliPrivateReport.0._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateSunfoldResiduals",
        1,
        &["_private.CliPrivateReport.0._sunfold"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateUnsafeRecResiduals",
        9,
        &[
            "_private.CliPrivateReport.0._unsafe_rec",
            "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitUnsafeRecResiduals",
        7,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitDataUnsafeRecResiduals",
        5,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitPreludeUnsafeRecResiduals",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportUnsafeRecResiduals",
        2,
        &[
            "_private.CliPrivateReport.0._unsafe_rec",
            "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportStandaloneUnsafeRecResiduals",
        1,
        &["_private.CliPrivateReport.0._unsafe_rec"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLoopProofResiduals",
        1,
        &["_private.CliPrivateReport.0.loop._proof_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateStandaloneProofNResiduals",
        5,
        &[
            "_private.CliPrivateReport.0._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateProofNResiduals",
        6,
        &[
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0.loop._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitProofNResiduals",
        4,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitDataProofNResiduals",
        2,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitPreludeProofNResiduals",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportProofResiduals",
        2,
        &[
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0.loop._proof_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateCliPrivateReportStandaloneProofNResiduals",
        1,
        &["_private.CliPrivateReport.0._proof_2"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "leanNameHashProofResiduals",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "leanNameBeqMatchResiduals",
        1,
        &["_private.Init.Prelude.0.Lean.Name.beq.match_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLeanNameResiduals",
        3,
        &[
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitPreludeResiduals",
        9,
        &[
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitResiduals",
        18,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "listToArrayAuxMatchResiduals",
        1,
        &["_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitDataListToArrayResiduals",
        1,
        &["_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitDataListResiduals",
        4,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInitDataResiduals",
        9,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "coreObservablesSyntaxMatchResiduals",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLeanSyntaxResiduals",
        6,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "arrayMapMProofResiduals",
        2,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "arrayMapMGoResiduals",
        1,
        &["_private.Init.Data.Array.BasicAux.0.Array.mapM'.go"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateArrayMapMResiduals",
        3,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateGoResiduals",
        3,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "stringExtraUnsafeRecResiduals",
        2,
        &[
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "mergeSortCompanionOnlyUnsafeRecResiduals",
        3,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "mergeSortInternalMergeUnsafeRecResiduals",
        2,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLoopMatchOneResiduals",
        1,
        &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLoopMatchNResiduals",
        1,
        &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLoopUnsafeRecResiduals",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateLoopEqDefResiduals",
        1,
        &["_private.CliPrivateReport.0.loop.eq_def"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateInsertIdxLoopUnaryResiduals",
        1,
        &["_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateUnaryResiduals",
        1,
        &["_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateMergeSortTRUnsafeRecResiduals",
        1,
        &["_private.CliPrivateReport.0.mergeSortTR._unsafe_rec"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateRunUnsafeRecResiduals",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateGoUnsafeRecResiduals",
        2,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateMergeTrGoUnsafeRecResiduals",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateSplitRevAtGoUnsafeRecResiduals",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "mergeSortInternalSplitTraversalUnsafeRecResiduals",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateFindLeadingSpacesConsumeUnsafeRecResiduals",
        1,
        &[
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "privateFindLeadingSpacesNextLineUnsafeRecResiduals",
        1,
        &[
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_json_named_residuals(
        &json.stdout,
        "coreObservablesLoopUnsafeRecResiduals",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_json_private_companion_residual_report(&json);

    let human = fln_cli::run([OsString::from("check-olean"), exported.into_os_string()]);
    assert_eq!(human.exit_code, 0, "{}", human.stderr);
    assert!(human.stderr.is_empty());
    assert!(
        human
            .stdout
            .contains("decoded _private auxiliaries: 29 (reporting only; not a G1 claim)")
    );
    assert_canonical_residual_group_keys_match_human_prefixes(&json.stdout, &human.stdout);
    assert_human_named_residuals(
        &human.stdout, "decoded _private.loop auxiliaries", "decoded _private.loop auxiliary names", 7,
        &[
            "_private.CliPrivateReport.0.loop", "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.loop._proof_1", "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec", "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private companion residuals",
        "decoded _private companion residual names",
        29,
        private_companion_names,
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport.loop residuals",
        "decoded _private CliPrivateReport.loop residual names",
        3,
        &[
            "_private.CliPrivateReport.0.loop",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.loop._proof_1",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport residuals",
        "decoded _private CliPrivateReport residual names",
        11,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0._sunfold",
            "_private.CliPrivateReport.0._unsafe_rec",
            "_private.CliPrivateReport.0.eq_1",
            "_private.CliPrivateReport.0.eq_def",
            "_private.CliPrivateReport.0.loop",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.loop._proof_1",
            "_private.CliPrivateReport.0.match_1",
            "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "core-observables .loop residuals", "core-observables .loop residual names", 3,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec", "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private eq_def/match_N residuals", "decoded _private eq_def/match_N residual names", 8,
        &[
            "_private.CliPrivateReport.0.eq_def", "_private.CliPrivateReport.0.loop.eq_def", "_private.CliPrivateReport.0.match_1",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1", "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1", "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private match_N residuals", "decoded _private match_N residual names", 6,
        &[
            "_private.CliPrivateReport.0.match_1", "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Prelude.0.Lean.Name.beq.match_1", "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1", "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport.match_N residuals",
        "decoded _private CliPrivateReport.match_N residual names",
        1,
        &["_private.CliPrivateReport.0.match_1"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport equation residuals",
        "decoded _private CliPrivateReport equation residual names",
        4,
        &[
            "_private.CliPrivateReport.0.eq_1",
            "_private.CliPrivateReport.0.eq_def",
            "_private.CliPrivateReport.0.loop.eq_def",
            "_private.CliPrivateReport.0.match_1",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private eq_def residuals", "decoded _private eq_def residual names", 2,
        &["_private.CliPrivateReport.0.eq_def", "_private.CliPrivateReport.0.loop.eq_def"],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private eq_N residuals", "decoded _private eq_N residual names", 1, &["_private.CliPrivateReport.0.eq_1"]);
    assert_human_named_residuals(
        &human.stdout, "decoded _private _unsafe_rec/_sunfold residuals", "decoded _private _unsafe_rec/_sunfold residual names", 10,
        &[
            "_private.CliPrivateReport.0._sunfold", "_private.CliPrivateReport.0._unsafe_rec", "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec", "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec", "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec", "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private _sunfold/_f residuals", "decoded _private _sunfold/_f residual names", 2,
        &["_private.CliPrivateReport.0._f", "_private.CliPrivateReport.0._sunfold"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport _sunfold/_f residuals",
        "decoded _private CliPrivateReport _sunfold/_f residual names",
        2,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._sunfold",
        ],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private _sunfold residuals", "decoded _private _sunfold residual names", 1, &["_private.CliPrivateReport.0._sunfold"]);
    assert_human_named_residuals(
        &human.stdout, "decoded _private _unsafe_rec residuals", "decoded _private _unsafe_rec residual names", 9,
        &[
            "_private.CliPrivateReport.0._unsafe_rec", "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec", "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec", "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec", "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport _f residuals",
        "decoded _private CliPrivateReport _f residual names",
        1,
        &["_private.CliPrivateReport.0._f"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport direct implementation auxiliary residuals",
        "decoded _private CliPrivateReport direct implementation auxiliary residual names",
        4,
        &[
            "_private.CliPrivateReport.0._f",
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0._sunfold",
            "_private.CliPrivateReport.0._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init _unsafe_rec residuals",
        "decoded _private Init _unsafe_rec residual names",
        7,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Data _unsafe_rec residuals",
        "decoded _private Init.Data _unsafe_rec residual names",
        5,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Prelude _unsafe_rec residuals",
        "decoded _private Init.Prelude _unsafe_rec residual names",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport _unsafe_rec residuals",
        "decoded _private CliPrivateReport _unsafe_rec residual names",
        2,
        &[
            "_private.CliPrivateReport.0._unsafe_rec",
            "_private.CliPrivateReport.0.mergeSortTR._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport standalone _unsafe_rec residuals",
        "decoded _private CliPrivateReport standalone _unsafe_rec residual names",
        1,
        &["_private.CliPrivateReport.0._unsafe_rec"],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private .loop._proof_* residuals", "decoded _private .loop._proof_* residual names", 1, &["_private.CliPrivateReport.0.loop._proof_1"]);
    assert_human_named_residuals(
        &human.stdout, "decoded standalone _private _proof_N residuals", "decoded standalone _private _proof_N residual names", 5,
        &[
            "_private.CliPrivateReport.0._proof_2", "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2", "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private _proof_N residuals",
        "decoded _private _proof_N residual names",
        6,
        &[
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0.loop._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init _proof_N residuals",
        "decoded _private Init _proof_N residual names",
        4,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Data _proof_N residuals",
        "decoded _private Init.Data _proof_N residual names",
        2,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Prelude _proof_N residuals",
        "decoded _private Init.Prelude _proof_N residual names",
        2,
        &[
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport _proof_N residuals",
        "decoded _private CliPrivateReport _proof_N residual names",
        2,
        &[
            "_private.CliPrivateReport.0._proof_2",
            "_private.CliPrivateReport.0.loop._proof_1",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private CliPrivateReport standalone _proof_N residuals",
        "decoded _private CliPrivateReport standalone _proof_N residual names",
        1,
        &["_private.CliPrivateReport.0._proof_2"],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private Lean.Name.hash._proof_N residuals", "decoded _private Lean.Name.hash._proof_N residual names", 2,
        &["_private.Init.Prelude.0.Lean.Name.hash._proof_1", "_private.Init.Prelude.0.Lean.Name.hash._proof_2"],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private Lean.Name.beq.match_N residuals", "decoded _private Lean.Name.beq.match_N residual names", 1, &["_private.Init.Prelude.0.Lean.Name.beq.match_1"]);
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Lean.Name residuals",
        "decoded _private Lean.Name residual names",
        3,
        &[
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Prelude residuals",
        "decoded _private Init.Prelude residual names",
        9,
        &[
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init residuals",
        "decoded _private Init residual names",
        18,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Name.beq.match_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
            "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private List.toArrayAux.match_N residuals", "decoded _private List.toArrayAux.match_N residual names", 1, &["_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"]);
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Data.List.ToArrayImpl residuals",
        "decoded _private Init.Data.List.ToArrayImpl residual names",
        1,
        &["_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Data.List residuals",
        "decoded _private Init.Data.List residual names",
        4,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Init.Data residuals",
        "decoded _private Init.Data residual names",
        9,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
            "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "core-observables Lean.Syntax match_N residuals", "core-observables Lean.Syntax match_N residual names", 2,
        &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1", "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Lean.Syntax residuals",
        "decoded _private Lean.Syntax residual names",
        6,
        &[
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
            "_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private Array.mapM'._proof_N residuals", "decoded _private Array.mapM'._proof_N residual names", 2,
        &["_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1", "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2"],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private Array.mapM'.go residuals", "decoded _private Array.mapM'.go residual names", 1, &["_private.Init.Data.Array.BasicAux.0.Array.mapM'.go"]);
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private Array.mapM' residuals",
        "decoded _private Array.mapM' residual names",
        3,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private .go residuals", "decoded _private .go residual names", 3,
        &[
            "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go", "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private String.findLeadingSpacesSize _unsafe_rec residuals", "decoded _private String.findLeadingSpacesSize _unsafe_rec residual names", 2,
        &[
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "decoded _private List.MergeSort companion-only _unsafe_rec residuals", "decoded _private List.MergeSort companion-only _unsafe_rec residual names", 3,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private List.MergeSort internal merge _unsafe_rec residuals",
        "decoded _private List.MergeSort internal merge _unsafe_rec residual names",
        2,
        &[
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
        ],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private .loop.match_1 residuals", "decoded _private .loop.match_1 residual names", 1, &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"]);
    assert_human_named_residuals(&human.stdout, "decoded _private .loop.match_N residuals", "decoded _private .loop.match_N residual names", 1, &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"]);
    assert_human_named_residuals(
        &human.stdout, "decoded _private .loop._unsafe_rec residuals", "decoded _private .loop._unsafe_rec residual names", 2,
        &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec", "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec"],
    );
    assert_human_named_residuals(&human.stdout, "decoded _private .loop.eq_def residuals", "decoded _private .loop.eq_def residual names", 1, &["_private.CliPrivateReport.0.loop.eq_def"]);
    assert_human_named_residuals(&human.stdout, "decoded _private insertIdx.loop._unary residuals", "decoded _private insertIdx.loop._unary residual names", 1, &["_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary"]);
    assert_human_named_residuals(&human.stdout, "decoded _private _unary residuals", "decoded _private _unary residual names", 1, &["_private.Init.Prelude.0.Lean.Syntax.insertIdx.loop._unary"]);
    assert_human_named_residuals(&human.stdout, "decoded _private mergeSortTR._unsafe_rec residuals", "decoded _private mergeSortTR._unsafe_rec residual names", 1, &["_private.CliPrivateReport.0.mergeSortTR._unsafe_rec"]);
    assert_human_named_residuals(&human.stdout, "decoded _private .run._unsafe_rec residuals", "decoded _private .run._unsafe_rec residual names", 1, &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec"]);
    assert_human_named_residuals(
        &human.stdout, "decoded _private .go._unsafe_rec residuals", "decoded _private .go._unsafe_rec residual names", 2,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec", "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private mergeTR.go._unsafe_rec residuals",
        "decoded _private mergeTR.go._unsafe_rec residual names",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private splitRevAt.go._unsafe_rec residuals",
        "decoded _private splitRevAt.go._unsafe_rec residual names",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private List.MergeSort internal split traversal _unsafe_rec residuals",
        "decoded _private List.MergeSort internal split traversal _unsafe_rec residual names",
        1,
        &["_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec"],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residuals",
        "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residual names",
        1,
        &[
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout,
        "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residuals",
        "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residual names",
        1,
        &[
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ],
    );
    assert_human_named_residuals(
        &human.stdout, "core-observables Lean.Syntax .loop._unsafe_rec residuals", "core-observables Lean.Syntax .loop._unsafe_rec residual names", 2,
        &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec", "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec"],
    );
    assert!(
        human.stdout.contains("G1 satisfied: no")
            && !json_bool_field(&json.stdout, "g1Satisfied"),
        "human: {}\njson: {}",
        human.stdout,
        json.stdout,
    );
}
