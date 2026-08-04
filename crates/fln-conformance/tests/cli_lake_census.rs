//! Mutation-backed contract tests for the pinned CLI/Lake census.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use fln_conformance::cli_lake_census::{
    CliDisposition, CliLakeInventory, CliModelError, CliPersonality, EMBEDDED_INVENTORY,
    EMBEDDED_POLICY, LakeTargetKind, ProcessOutcome, SemanticRecord, SurfaceKind, TelemetryRecord,
    TranscriptBundle, ValueSource, classify_process, parse_lake_target_spec, parse_package_url_map,
    project_arguments, resolve_value,
};

fn inventory() -> CliLakeInventory {
    CliLakeInventory::load_embedded().expect("the checked-in CLI/Lake census must parse")
}

fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn framed_hash<'a>(domain: &'a str, lines: impl IntoIterator<Item = &'a str>) -> String {
    let mut payload = Vec::new();
    for field in std::iter::once(domain).chain(lines) {
        payload.extend_from_slice(&(field.len() as u64).to_le_bytes());
        payload.extend_from_slice(field.as_bytes());
    }
    fnv(&payload)
}

fn reseal(inventory: &str, policy: &str) -> String {
    let mut lines = inventory.lines().map(str::to_string).collect::<Vec<_>>();
    let raw_begin = lines
        .iter()
        .position(|line| line == "raw-begin")
        .expect("raw-begin");
    let raw_end = lines
        .iter()
        .position(|line| line == "raw-end")
        .expect("raw-end");
    let raw_root = framed_hash(
        "fln-cli-lake-raw/1",
        lines[raw_begin + 1..raw_end].iter().map(String::as_str),
    );
    replace_scalar(&mut lines, "raw-root ", &raw_root);
    replace_scalar(
        &mut lines,
        "policy-root ",
        &framed_hash("fln-cli-lake-policy/1", policy.lines()),
    );
    let transcript_lines = lines[raw_begin + 1..raw_end]
        .iter()
        .filter_map(|line| {
            line.strip_prefix("transcript ")
                .map(|rest| format!("probe {rest}"))
        })
        .collect::<Vec<_>>();
    replace_scalar(
        &mut lines,
        "transcript-root ",
        &framed_hash(
            "fln-cli-lake-transcripts/1",
            transcript_lines.iter().map(String::as_str),
        ),
    );
    let root_index = lines
        .iter()
        .position(|line| line.starts_with("inventory-root "))
        .expect("inventory-root");
    let root = framed_hash(
        "fln-cli-lake-inventory/1",
        lines[..root_index].iter().map(String::as_str),
    );
    lines[root_index] = format!("inventory-root {root}");
    lines.join("\n") + "\n"
}

fn replace_scalar(lines: &mut [String], prefix: &str, value: &str) {
    let line = lines
        .iter_mut()
        .find(|line| line.starts_with(prefix))
        .expect("scalar root row");
    *line = format!("{prefix}{value}");
}

#[test]
fn cli_surface_inventory() {
    let inventory = inventory();
    inventory
        .validate_workspace_sources(&fln_conformance::pin::workspace_root())
        .expect("every mechanically cited source still has its recorded bytes");

    let commands = inventory.surfaces_of_kind(SurfaceKind::Command).count();
    let options = inventory.surfaces_of_kind(SurfaceKind::Option).count();
    let facets = inventory.surfaces_of_kind(SurfaceKind::Facet).count();
    let environments = inventory.surfaces_of_kind(SurfaceKind::Environment).count();
    assert!(commands >= 35, "command census collapsed to {commands}");
    assert!(options >= 100, "option census collapsed to {options}");
    assert!(facets >= 35, "facet census collapsed to {facets}");
    assert!(
        environments >= 25,
        "environment census collapsed to {environments}"
    );
    for key in [
        "personality:lean",
        "personality:leanc",
        "personality:lake",
        "option:lean:--json",
        "option:lean:-D",
        "command:lake:build",
        "command:lake:upgrade",
        "command:lake:exec",
        "environment:lake:LAKE_CONFIG",
        "environment:lake:LEAN_CC",
        "config-default:lake:defaultManifestFile",
        "leanc-rule:forward",
        "outcome:cancelled",
        "outcome:resource-exhausted",
    ] {
        assert!(inventory.surface(key).is_some(), "missing surface {key}");
    }
    assert_eq!(
        inventory
            .surface("config-default:lake:defaultManifestFile")
            .and_then(|surface| surface.attribute("value")),
        Some("lake-manifest.json")
    );
    assert_eq!(inventory.transcripts.len(), 25);
    assert_eq!(inventory.platform, "linux-x86_64");
    assert_eq!(
        inventory
            .surface("executable:lean")
            .and_then(|surface| surface.attribute("sha256")),
        Some("e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550")
    );

    // M1: an omitted source fact cannot be hidden by resealing the raw artifact.
    let omitted = EMBEDDED_INVENTORY
        .lines()
        .filter(|line| !line.contains("key=option:lean:--json "))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let omitted = omitted.replace(
        &format!("surface-count {}", inventory.surfaces.len()),
        &format!("surface-count {}", inventory.surfaces.len() - 1),
    );
    let omitted = reseal(&omitted, EMBEDDED_POLICY);
    assert!(
        CliLakeInventory::parse(&omitted, EMBEDDED_POLICY)
            .expect_err("an omitted fact must die at the policy bijection")
            .to_string()
            .contains("bijection")
    );

    // M2: cancellation cannot be re-labelled as rejection even after root repair.
    let cancellation = EMBEDDED_INVENTORY.replacen(
        "disposition=inconclusive input=cancelled personality=all",
        "disposition=rejected input=cancelled personality=all",
        1,
    );
    let cancellation = reseal(&cancellation, EMBEDDED_POLICY);
    assert!(
        CliLakeInventory::parse(&cancellation, EMBEDDED_POLICY)
            .expect_err("the FL-INV-07 mutant must be refused")
            .to_string()
            .contains("not typed inconclusive")
    );

    // M3: inherited compiler delegation cannot be promoted to native authority.
    let inherited = EMBEDDED_POLICY.replacen(
        "row leanc-rule:forward authority=inherited",
        "row leanc-rule:forward authority=native-target",
        1,
    );
    let inherited_inventory = reseal(EMBEDDED_INVENTORY, &inherited);
    assert!(
        CliLakeInventory::parse(&inherited_inventory, &inherited)
            .expect_err("leanc authority laundering must be refused")
            .to_string()
            .contains("overclaims native authority")
    );

    // M4: a complete-looking but shortened real probe manifest remains incomplete.
    let missing_probe = EMBEDDED_INVENTORY
        .lines()
        .filter(|line| !line.contains("key=leanc:unknown-option "))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let missing_probe = missing_probe.replace("transcript-count 25", "transcript-count 24");
    let missing_probe = reseal(&missing_probe, EMBEDDED_POLICY);
    assert!(
        CliLakeInventory::parse(&missing_probe, EMBEDDED_POLICY)
            .expect_err("a shortened real transcript must be refused")
            .to_string()
            .contains("complete matrix")
    );

    // M5: source bytes are checked independently of artifact roots.
    let source_mutant = EMBEDDED_INVENTORY.replacen(
        "source path=SUITE.lock hash=fnv1a64:",
        "source path=SUITE.lock hash=fnv1a64:0",
        1,
    );
    let source_mutant = reseal(&source_mutant, EMBEDDED_POLICY);
    let parsed = CliLakeInventory::parse(&source_mutant, EMBEDDED_POLICY)
        .expect("root-resealed source mutant remains syntactically valid");
    assert!(
        parsed
            .validate_workspace_sources(&fln_conformance::pin::workspace_root())
            .expect_err("source drift must be observed")
            .to_string()
            .contains("source binding drifted")
    );
}

#[test]
fn argument_precedence_model() {
    let inventory = inventory();
    let lean = project_arguments(
        &inventory,
        CliPersonality::Lean,
        &["--json", "--run", "Probe.lean", "--not-an-option-to-lean"],
    )
    .expect("run terminates Lean option parsing");
    assert_eq!(lean.command.as_deref(), Some("run"));
    assert_eq!(lean.forwarded, ["Probe.lean", "--not-an-option-to-lean"]);
    assert_eq!(lean.options.get("--json").map(String::as_str), Some("true"));

    assert!(matches!(
        project_arguments(&inventory, CliPersonality::Lean, &["--root"]),
        Err(CliModelError::MissingOptionArgument(_))
    ));
    assert!(matches!(
        project_arguments(&inventory, CliPersonality::Lean, &["--fln-census-unknown"]),
        Err(CliModelError::UnknownOption(_))
    ));

    let lake = project_arguments(
        &inventory,
        CliPersonality::Lake,
        &[
            "--dir=first",
            "build",
            "--dir=second",
            "Probe",
            "--",
            "--forwarded",
        ],
    )
    .expect("Lake admits options on both sides of its command");
    assert_eq!(lake.command.as_deref(), Some("build"));
    assert_eq!(
        lake.options.get("--dir").map(String::as_str),
        Some("second")
    );
    assert_eq!(lake.positionals, ["Probe"]);
    assert_eq!(lake.forwarded, ["--forwarded"]);

    let leanc = project_arguments(&inventory, CliPersonality::Leanc, &["-O3", "-c", "probe.c"])
        .expect("leanc forwards the inherited compiler surface");
    assert_eq!(leanc.forwarded, ["-O3", "-c", "probe.c"]);
}

#[test]
fn exit_channel_matrix() {
    let inventory = inventory();
    assert_eq!(
        classify_process(ProcessOutcome::Exited(0)),
        CliDisposition::Accepted
    );
    assert_eq!(
        classify_process(ProcessOutcome::Exited(1)),
        CliDisposition::Rejected
    );
    for outcome in [
        ProcessOutcome::Cancelled,
        ProcessOutcome::TimedOut,
        ProcessOutcome::OutputBudgetExceeded,
    ] {
        assert_eq!(classify_process(outcome), CliDisposition::Inconclusive);
    }
    assert_eq!(
        classify_process(ProcessOutcome::SpawnFault),
        CliDisposition::InternalFault
    );

    for key in [
        "lean:unknown-option",
        "lean:malformed-timeout",
        "lean:json-error",
        "lake:unknown-command",
        "lake:unknown-option",
        "lake:missing-dir-value",
        "lake:missing-root",
        "leanc:unknown-option",
    ] {
        let row = inventory
            .transcript(key)
            .unwrap_or_else(|| panic!("missing transcript {key}"));
        assert_ne!(row.exit_code, 0, "{key} must be a real error observation");
        assert!(
            matches!(
                (key, row.channel.as_str()),
                ("lean:json-error", "stdout") | (_, "stderr") | (_, "split")
            ),
            "{key} lost its diagnostic channel: {}",
            row.channel
        );
    }
    for key in [
        "lean:help",
        "lean:version",
        "lake:help",
        "lake:version",
        "leanc:help",
        "leanc:version",
    ] {
        let row = inventory
            .transcript(key)
            .unwrap_or_else(|| panic!("missing transcript {key}"));
        assert_eq!(row.exit_code, 0);
        assert!(matches!(row.channel.as_str(), "stdout" | "split"));
    }
}

#[test]
fn lake_verb_facet_contract() {
    let inventory = inventory();
    let commands = inventory
        .surfaces_of_kind(SurfaceKind::Command)
        .map(|surface| surface.key.as_str())
        .collect::<BTreeSet<_>>();
    for command in [
        "command:lake:build",
        "command:lake:update",
        "command:lake:upgrade",
        "command:lake:exe",
        "command:lake:exec",
        "command:lake:cache/get",
        "command:lake:script/run",
    ] {
        assert!(commands.contains(command), "missing Lake verb {command}");
    }

    let module =
        parse_lake_target_spec(&inventory, "@pkg/+Probe:c").expect("pinned module C facet");
    assert_eq!(module.package.as_deref(), Some("pkg"));
    assert_eq!(module.target, "Probe");
    assert_eq!(module.facet.as_deref(), Some("c"));
    assert_eq!(module.kind, LakeTargetKind::Module);

    let root_facet = parse_lake_target_spec(&inventory, ":leanArts").expect("root facet");
    assert_eq!(root_facet.kind, LakeTargetKind::RootFacet);
    assert!(matches!(
        parse_lake_target_spec(&inventory, "@pkg/+Probe:not-a-real-facet"),
        Err(CliModelError::UnknownFacet { .. })
    ));
}

#[test]
fn config_environment_precedence() {
    let inventory = inventory();
    let cli = resolve_value(Some("cli"), Some("config"), Some("environment"), "default");
    assert_eq!(cli.source, ValueSource::Cli);
    assert_eq!(cli.value, "cli");
    assert_eq!(
        resolve_value(None, Some("config"), Some("environment"), "default").source,
        ValueSource::Config
    );
    assert_eq!(
        resolve_value(None, None, Some("environment"), "default").source,
        ValueSource::Environment
    );
    assert_eq!(
        resolve_value(None, None, None, "default").source,
        ValueSource::Default
    );

    let map =
        parse_package_url_map(r#"{"mathlib":"https://example.invalid/mathlib","std":"local/std"}"#)
            .expect("flat package URL map");
    assert_eq!(map.len(), 2);
    assert!(matches!(
        parse_package_url_map("{not-json}"),
        Err(CliModelError::MalformedJsonEnvironment(_))
    ));

    for name in [
        "LAKE_CONFIG",
        "LAKE_NO_CACHE",
        "LAKE_PKG_URL_MAP",
        "LEAN",
        "LEAN_SYSROOT",
        "LEAN_CC",
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "PATH",
    ] {
        let surface = inventory
            .surface(&format!("environment:lake:{name}"))
            .unwrap_or_else(|| panic!("missing environment row {name}"));
        assert_eq!(surface.policy.support, "optional");
        assert_eq!(surface.policy.precedence, "environment-fallback");
    }
}

#[test]
fn semantic_and_telemetry_ndjson_are_strictly_separate() {
    let inventory = inventory();
    let semantic = inventory
        .transcripts
        .iter()
        .enumerate()
        .map(|(sequence, probe)| SemanticRecord {
            sequence: sequence as u64,
            epoch_id: inventory.reference.commit.clone(),
            probe_id: probe.key.clone(),
            personality: probe.personality.clone(),
            expected_exit: probe.exit_code,
            actual_exit: probe.exit_code,
            expected_stdout: probe.stdout_hash.clone(),
            actual_stdout: probe.stdout_hash.clone(),
            expected_stderr: probe.stderr_hash.clone(),
            actual_stderr: probe.stderr_hash.clone(),
            authority_root: inventory.inventory_root.clone(),
            disposition: classify_process(ProcessOutcome::Exited(probe.exit_code)),
            final_state: "two-pass-match".to_string(),
        })
        .collect::<Vec<_>>();
    let telemetry = inventory
        .transcripts
        .iter()
        .enumerate()
        .map(|(sequence, probe)| TelemetryRecord {
            sequence: sequence as u64,
            probe_id: probe.key.clone(),
            elapsed_micros: sequence as u64 + 1,
            output_bytes: (probe.stdout_bytes + probe.stderr_bytes) as u64,
        })
        .collect::<Vec<_>>();
    let bundle = TranscriptBundle::new(semantic, telemetry).expect("sequential bundle");
    bundle
        .validate_authority(&inventory)
        .expect("manifest-complete authority");
    let semantic_ndjson = bundle.semantic_ndjson();
    let telemetry_ndjson = bundle.telemetry_ndjson();
    assert!(!semantic_ndjson.contains("elapsed_micros"));
    assert!(!semantic_ndjson.contains("output_bytes"));
    assert!(!telemetry_ndjson.contains("authority_root"));
    assert!(!telemetry_ndjson.contains("expected_stdout"));
    assert_eq!(
        TranscriptBundle::from_ndjson(&semantic_ndjson, &telemetry_ndjson),
        Ok(bundle.clone())
    );
    assert_ne!(bundle.semantic_root(), bundle.telemetry_root());

    let extra = semantic_ndjson.replacen(
        "\"final_state\":\"two-pass-match\"}",
        "\"final_state\":\"two-pass-match\",\"elapsed_micros\":1}",
        1,
    );
    assert!(
        TranscriptBundle::from_ndjson(&extra, &telemetry_ndjson)
            .expect_err("semantic telemetry contamination must be refused")
            .to_string()
            .contains("field set mismatch")
    );
    let nonsequential = semantic_ndjson.replacen("\"sequence\":1", "\"sequence\":9", 1);
    assert!(
        TranscriptBundle::from_ndjson(&nonsequential, &telemetry_ndjson)
            .expect_err("sequence gaps must be refused")
            .to_string()
            .contains("sequence is noncanonical")
    );
}
