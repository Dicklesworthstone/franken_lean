//! Structural regression laws for the evidence publisher's finalization order.

#![forbid(unsafe_code)]

use std::fs;
use std::path::Path;

fn check_script() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/check.sh");
    fs::read_to_string(path).expect("scripts/check.sh must be readable")
}

fn env_snapshots_script() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/e2e/env_snapshots.sh");
    fs::read_to_string(path).expect("scripts/e2e/env_snapshots.sh must be readable")
}

fn trusted_script(relative: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative);
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{relative} must be readable: {error}"))
}

#[test]
fn terminal_human_log_is_sealed_before_manifest_generation() {
    let script = check_script();
    let note = script
        .split_once("note() {\n")
        .expect("check.sh must define note")
        .1
        .split_once("\n}\n\nset_final()")
        .expect("check.sh note must end before set_final")
        .0;
    let finalizer = script
        .split_once("on_exit() {\n")
        .expect("check.sh must define on_exit")
        .1
        .split_once("\n}\n\ntrap 'on_signal HUP 129' HUP")
        .expect("check.sh on_exit must end before the signal traps")
        .0;

    let terminal_append = finalizer
        .find(
            r#"note "terminal verdict=$FINAL_VERDICT reason=$FINAL_REASON process_exit=$FINAL_EXIT""#,
        )
        .expect("the finalizer must append its terminal human record");
    let human_seal = finalizer[terminal_append..]
        .find("HUMAN_LOG_SEALED=1")
        .map(|offset| terminal_append + offset)
        .expect("the finalizer must seal human.log after its terminal record");
    let manifest_generation = finalizer
        .find(r#"run_finalizer_command python3 "$EVIDENCE" manifest"#)
        .expect("the finalizer must generate an evidence manifest");

    let sealed_note_branch = note
        .find(r#"if [ "$HUMAN_LOG_SEALED" -eq 1 ]; then"#)
        .expect("note must recognize a sealed human log");
    let sealed_note_return = note[sealed_note_branch..]
        .find("return 0")
        .map(|offset| sealed_note_branch + offset)
        .expect("sealed note handling must return without appending");
    let human_append = note
        .find(r#"tee -a "$HUMAN""#)
        .expect("unsealed notes must append to human.log");

    assert!(
        terminal_append < human_seal && human_seal < manifest_generation,
        "human.log must receive its terminal record and be sealed before the manifest inventories it"
    );
    assert!(
        sealed_note_branch < sealed_note_return && sealed_note_return < human_append,
        "post-seal notes must return after stderr output and before the human.log append path"
    );
}

#[test]
fn env_snapshots_parent_is_authoritative_and_preserves_nested_children() {
    let script = env_snapshots_script();
    let normalized = script.replace("\\\n  ", "");

    assert!(
        script.contains("SCHEMA=\"fln.e2e/2\""),
        "env_snapshots must publish the authoritative fln.e2e/2 parent"
    );
    assert!(
        !script.contains("fln-e2e/1"),
        "env_snapshots must not retain the legacy parent schema"
    );
    assert!(
        script.contains(r#"if [ -e "$ART_DIR" ] || [ -L "$ART_DIR" ]; then"#),
        "the parent must refuse reused or symlink artifact directories"
    );
    assert!(
        script.contains(r#"run_finalizer_command python3 "$EVIDENCE" validate-run"#)
            && script.contains(r#"run_finalizer_command python3 "$EVIDENCE" manifest"#)
            && script.contains(r#"run_finalizer_command python3 "$EVIDENCE" complete-bundle"#)
            && script.contains(r#"run_finalizer_command python3 "$EVIDENCE" adopt-bundle"#),
        "the parent must validate, manifest, complete, and adopt through its durable finalizer"
    );

    for (scenario, child) in [
        (
            "declaration_tag_matrix",
            "declaration-tag-matrix-fln-amv.12",
        ),
        ("declaration_membership", "declaration-membership-fln-amv.1"),
        (
            "extension_descriptor_matrix",
            "extension-descriptor-matrix-fln-amv.2",
        ),
    ] {
        assert_eq!(
            script.matches(child).count(),
            1,
            "identity child {child} must have one exact registration"
        );
        assert!(
            script.contains(&format!("run_identity_child {scenario} ")),
            "identity child {child} must bind scenario {scenario}"
        );
    }
    assert_eq!(
        script
            .matches(r#"validate_child_reference "$scenario" "$child_rel""#)
            .count(),
        1,
        "each identity child must flow through the single parent-reference helper"
    );

    for (scenario, child) in [
        ("environment_collision", "collision-fln-amv.10"),
        (
            "environment_resource_collision",
            "resource-collision-fln-amv.13",
        ),
    ] {
        let reference = format!("validate_child_reference {scenario} {child}");
        assert_eq!(
            normalized.matches(&reference).count(),
            1,
            "the parent must reference nested child {child} exactly once"
        );
    }
}

#[test]
fn env_snapshots_seals_human_log_before_parent_manifest() {
    let script = env_snapshots_script();
    let note = script
        .split_once("note() {\n")
        .expect("env_snapshots must define note")
        .1
        .split_once("\n}\n\nbuild_event_command()")
        .expect("env_snapshots note must end before build_event_command")
        .0;
    let finalizer = script
        .split_once("on_exit() {\n")
        .expect("env_snapshots must define on_exit")
        .1
        .split_once("\n}\n\ntrap 'on_signal HUP 129' HUP")
        .expect("env_snapshots on_exit must end before signal traps")
        .0;

    let terminal_append = finalizer
        .find(
            r#"note "terminal verdict=$FINAL_VERDICT reason=$FINAL_REASON process_exit=$FINAL_EXIT""#,
        )
        .expect("the parent finalizer must append its terminal human record");
    let human_seal = finalizer[terminal_append..]
        .find("HUMAN_LOG_SEALED=1")
        .map(|offset| terminal_append + offset)
        .expect("the parent finalizer must seal human.log");
    let manifest_generation = finalizer
        .find(r#"run_finalizer_command python3 "$EVIDENCE" manifest"#)
        .expect("the parent finalizer must generate a manifest");
    let sealed_return = note
        .find(r#"if [ "$HUMAN_LOG_SEALED" -eq 1 ]; then"#)
        .and_then(|offset| note[offset..].find("return 0").map(|tail| offset + tail))
        .expect("post-seal notes must return before appending");
    let human_append = note
        .find(r#"tee -a "$HUMAN""#)
        .expect("unsealed notes must append to human.log");

    assert!(
        terminal_append < human_seal && human_seal < manifest_generation,
        "the terminal record and seal must precede parent manifest generation"
    );
    assert!(
        sealed_return < human_append,
        "post-seal diagnostics must not reach the human.log append"
    );
}

#[test]
fn every_supervisor_launcher_seals_python_configuration_before_imports() {
    let check = check_script();
    assert!(
        check.contains(r#"PYTHON=("$PYTHON_BIN" -I -S)"#)
            && check.contains(r#"local -a runner=("${PYTHON[@]}" "$EVIDENCE" run"#)
            && check.contains(r#"setsid -- "${PYTHON[@]}" "$EVIDENCE" run"#),
        "check.sh must use its resolved -I -S interpreter argv for every supervisor"
    );

    for relative in [
        "scripts/e2e/closure_audit.sh",
        "scripts/e2e/env_snapshots.sh",
        "scripts/e2e/kernel_replay.sh",
        "scripts/e2e/structure_gate.sh",
        "scripts/e2e/vellum_naming_no_mock_e2e.sh",
        "scripts/e2e/verdict_schema.sh",
    ] {
        let script = trusted_script(relative);
        assert!(
            script.contains(r#"python3 -I -S "$EVIDENCE" run"#),
            "{relative} must launch the supervisor through Python -I -S"
        );
        assert!(
            !script.contains(r#"python3 "$EVIDENCE" run"#),
            "{relative} retains an unsealed supervisor launch"
        );
    }

    let stress = trusted_script("scripts/e2e/evidence_runner.sh");
    assert!(
        stress.contains(r#""$PYTHON_BIN" -I -S "$EVIDENCE" run"#),
        "the evidence-runner stress lane must launch its supervisor through -I -S"
    );
}
