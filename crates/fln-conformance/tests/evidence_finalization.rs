//! Structural regression laws for the evidence publisher's finalization order.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

fn check_script() -> String {
    let path = fln_conformance::checked_workspace_root!().join("scripts/check.sh");
    fs::read_to_string(path).expect("scripts/check.sh must be readable")
}

fn env_snapshots_script() -> String {
    let path = fln_conformance::checked_workspace_root!().join("scripts/e2e/env_snapshots.sh");
    fs::read_to_string(path).expect("scripts/e2e/env_snapshots.sh must be readable")
}

fn trusted_script(relative: &str) -> String {
    let path = fln_conformance::checked_workspace_root!().join(relative);
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{relative} must be readable: {error}"))
}

#[test]
fn parity_ledger_evidence_references_are_resolved_on_both_production_paths() {
    let evidence = trusted_script("scripts/evidence.py");
    let loader = evidence
        .split_once("def load_ndjson_snapshot(")
        .expect("evidence.py must define its NDJSON snapshot loader")
        .1
        .split_once("\ndef load_ndjson(")
        .expect("the NDJSON snapshot loader must have a bounded source body")
        .0;
    let self_test = evidence
        .split_once("def cmd_self_test(")
        .expect("evidence.py must define its hermetic self-test")
        .1
        .split_once("\ndef build_parser(")
        .expect("the evidence self-test must have a bounded source body")
        .0;

    assert!(
        evidence.contains("def validate_parity_ledger_reference(")
            && evidence.contains("def validate_parity_ledger_emitters("),
        "evidence.py must retain the shared reference resolver and governed-emitter scan"
    );
    assert!(
        loader.contains("validate_parity_ledger_reference(")
            && loader.contains("load_parity_ledger_symbols()"),
        "every produced NDJSON record must resolve parity_ledger_row while loading"
    );
    assert!(
        self_test.contains("validate_parity_ledger_emitters()")
            && self_test.contains("\"parity_ledger_reference_integrity\""),
        "the mandatory evidence self-test must scan legacy and central shell emitters"
    );
}

const RECEIPT_EXECUTION_AUTHORITY_PROBE: &str = r#"
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("fln_evidence_xes2_probe", sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
cells = module.self_test_verification_receipt_execution_authority()
for name in sorted(cells):
    print(f"{name}={cells[name]}")
print("PROBE-COMPLETE")
"#;

/// A passing libtest line is not an observation that the function reached its
/// assertion-bearing end. Exercise the production receipt validator, including the
/// non-overbroad control: process-level structured events retain authority, and a
/// test-function identity may be inventoried only under non-discharging `bundle_only`.
#[test]
fn verification_receipts_never_promote_libtest_ok_to_execution() {
    let root = fln_conformance::checked_workspace_root!();
    let evidence = root.join("scripts/evidence.py");
    let run = std::process::Command::new("python3")
        .args(["-I", "-S", "-B", "-c", RECEIPT_EXECUTION_AUTHORITY_PROBE])
        .arg(&evidence)
        .output()
        .expect("the sealed interpreter must run the receipt-authority probe");
    let stdout = String::from_utf8_lossy(&run.stdout);
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        run.status.success() && stdout.contains("PROBE-COMPLETE"),
        "receipt-authority probe did not complete against {}: status={:?} stderr={stderr}",
        evidence.display(),
        run.status.code()
    );
    for expected in [
        "bundle_only_test_inventory=accepted",
        "log_derived_libtest_execution=refused",
        "structured_stage_execution=accepted",
    ] {
        assert!(
            stdout.lines().any(|line| line == expected),
            "receipt-authority probe omitted {expected:?}: {stdout}"
        );
    }
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
        .find(r#"run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" manifest"#)
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
        script.contains(r#"if ! mkdir "$ART_DIR" 2>/dev/null; then"#)
            && script.contains("ART_DIR_CLAIMED=1"),
        "the parent must acquire its single-writer artifact claim atomically"
    );
    assert!(
        script.contains(r#"run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" validate-run"#,)
            && script.contains(r#"run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" manifest"#,)
            && script
                .contains(r#"run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" complete-bundle"#,)
            && script.contains(r#"run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" adopt-bundle"#,),
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
        .find(r#"run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" manifest"#)
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
        "scripts/check.sh",
        "scripts/e2e/bignum_vectors.sh",
        "scripts/e2e/closure_audit.sh",
        "scripts/e2e/contract_drift.sh",
        "scripts/e2e/env_snapshots.sh",
        "scripts/e2e/kernel_replay.sh",
        "scripts/e2e/olean_resurrection.sh",
        "scripts/e2e/structure_gate.sh",
        "scripts/e2e/vellum_naming_no_mock_e2e.sh",
        "scripts/e2e/verdict_schema.sh",
    ] {
        let script = trusted_script(relative);
        assert!(
            script.contains(r#"PYTHON_BIN="$(command -v python3 || true)""#)
                && script.contains(r#"PYTHON=("$PYTHON_BIN" -I -S)"#)
                && script.contains("HOSTILE_PYTHON_CONFIGURATION=()")
                && script.contains("sealed_interpreter_hostile_environment names="),
            "{relative} must resolve Python once, freeze -I -S, and refuse ambient Python configuration"
        );
        for (line_number, line) in script.lines().enumerate() {
            if line.contains("python3")
                && !line.contains("command -v python3")
                && !line.contains("python3 is required")
            {
                panic!(
                    "{relative}:{} retains a bare Python token: {line}",
                    line_number + 1
                );
            }
        }
    }

    let stress = trusted_script("scripts/e2e/evidence_runner.sh");
    assert!(
        stress.contains(r#""$PYTHON_BIN" -I -S "$EVIDENCE" run"#),
        "the evidence-runner stress lane must launch its supervisor through -I -S"
    );

    let vendor = trusted_script("scripts/verify_vendor_tree.sh");
    assert!(
        vendor.contains(r#"exec "$PYTHON_BIN" -I -S "$ROOT/scripts/evidence.py""#)
            && vendor.contains("sealed_interpreter_hostile_environment names="),
        "the standalone vendor verifier must refuse ambient configuration and seal Python before imports"
    );

    for relative in [
        "scripts/evidence.py",
        "scripts/extract/convert_blake3_vectors.py",
        "scripts/extract/gen_abi_contract.py",
        "scripts/extract/gen_bignum_vectors.py",
        "scripts/extract/gen_olean_contract.py",
    ] {
        let script = trusted_script(relative);
        assert!(
            script.starts_with("#!/usr/bin/env -S python3 -I -S\n")
                && (relative == "scripts/evidence.py"
                    || script.contains("sealed_interpreter_unsealed_startup")
                        && script.contains("sealed_interpreter_hostile_environment")),
            "{relative} must seal direct shebang execution and refuse bypassed startup"
        );
    }

    let evidence = trusted_script("scripts/evidence.py");
    assert!(
        evidence.contains(r#"if args.subcommand != "run":"#)
            && evidence.contains("prepare_sealed_interpreter(os.environ)"),
        "direct evidence subcommands must refuse unsealed or hostile startup at runtime"
    );
}

/// The bead-text write guard must compare complete payloads and bind comment read-back to the
/// immutable record created by this process.
///
/// The first implementation stripped trailing newlines while claiming byte identity, even though
/// the installed `br` preserves them. It also discovered its write with a before/after set
/// difference. A concurrent peer comment therefore made the guard refuse only after its own
/// immutable comment had landed, inviting a duplicate on retry. The script's hermetic self-test
/// plants both failures: one missing trailing newline, and a later peer comment whose id is newer
/// than the id returned by `br comments add --json`. Launching the script directly also binds the
/// documented CLI to its executable bit and isolated shebang rather than bypassing both. The same
/// matrix drives the mutable-description path named separately by the bead's acceptance criteria.
#[test]
fn bead_text_guard_binds_the_created_id_and_complete_utf8_payload() {
    let repo = fln_conformance::checked_workspace_root!();
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let heading = "### A comment or description body is a shell word before it is a record";
    let section = agents
        .split_once(heading)
        .unwrap_or_else(|| panic!("AGENTS.md must retain the fln-qpkj write-path section"))
        .1;
    let section = section
        .split_once("\n### ")
        .map_or(section, |(body, _)| body);
    for obligation in [
        "br comments add <id> -f body.md",
        "scripts/br_comment.py description <id> body.md",
        "br create --description",
    ] {
        assert!(
            section.contains(obligation),
            "AGENTS.md's fln-qpkj section no longer states {obligation:?}"
        );
    }

    let script = repo.join("scripts/br_comment.py");
    let output = std::process::Command::new(&script)
        .arg("self-test")
        .output()
        .unwrap_or_else(|error| panic!("{} self-test must launch: {error}", script.display()));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{} self-test failed\nstdout:\n{stdout}\nstderr:\n{stderr}",
        script.display()
    );
    for proof in [
        "exact-payload",
        "trailing-newline-drift",
        "returned-write-id",
        "description-payload",
        "malformed-schema",
        "typed-diagnostic",
    ] {
        assert!(
            stdout.contains(proof),
            "{} self-test did not report the {proof} cell\nstdout:\n{stdout}\nstderr:\n{stderr}",
            script.display()
        );
    }
}

#[test]
fn armed_finalizers_publish_only_after_their_process_wins_the_directory_claim() {
    for relative in [
        "scripts/check.sh",
        "scripts/e2e/closure_audit.sh",
        "scripts/e2e/env_snapshots.sh",
        "scripts/e2e/structure_gate.sh",
        "scripts/e2e/verdict_schema.sh",
    ] {
        let script = trusted_script(relative);
        assert!(
            script.contains("ART_DIR_CLAIMED=0")
                && script.contains(r#"if ! mkdir "$ART_DIR" 2>/dev/null; then"#)
                && script.contains("ART_DIR_CLAIMED=1")
                && script
                    .contains(r#"if [ "$ART_DIR_CLAIMED" -eq 1 ] && [ -d "$ART_DIR" ]; then"#,),
            "{relative} must bind finalization authority to its successful atomic directory claim"
        );

        let claim = script
            .find(r#"if ! mkdir "$ART_DIR" 2>/dev/null; then"#)
            .expect("atomic claim must exist");
        let owned = script[claim..]
            .find("ART_DIR_CLAIMED=1")
            .map(|offset| claim + offset)
            .expect("successful claim must record ownership");
        let first_artifact_write = script[owned..]
            .find(r#""$ART_DIR/"#)
            .map(|offset| owned + offset)
            .expect("the claimed directory must eventually receive evidence");
        assert!(
            claim < owned && owned < first_artifact_write,
            "{relative} must record ownership before writing its first artifact"
        );
    }
}

/// Every lane that allocates an evidence root must claim it atomically, so that a
/// `RUN_ID` collision is a typed refusal rather than two lanes silently sharing one
/// directory.
///
/// `RUN_ID` is `<lane>-<UTC second>-$$` in every lane, sealed and unsealed alike, so
/// uniqueness rests entirely on a (second, PID) pair never repeating — an assumption
/// nobody wrote down and nothing checks. `mkdir -p` converts that improbable collision
/// into silent sharing instead of a fault, and two lanes take a caller-supplied root
/// (`FLN_E2E_ARTIFACT_DIR`, `FLN_E2E_ART_ROOT`) and so have no uniqueness argument at all.
///
/// The scope is DERIVED from the filesystem rather than listed. The hand-list in
/// `armed_finalizers_publish_only_after_their_process_wins_the_directory_claim` above
/// is precisely why this was needed: it froze five scripts while the lane surface kept
/// growing, and twelve other roots stayed unsealed behind it (`franken_lean-h40t`). Two
/// of those twelve were missed even by the manual sweep that found the other ten.
#[test]
fn every_evidence_lane_claims_its_artifact_root_atomically() {
    let repo = fln_conformance::checked_workspace_root!();
    let mut lanes: Vec<(String, String)> = Vec::new();

    for dir in ["scripts/e2e", "scripts/tribunal"] {
        let entries =
            fs::read_dir(repo.join(dir)).unwrap_or_else(|e| panic!("{dir} must be readable: {e}"));
        for entry in entries {
            let path = entry.expect("directory entry must be readable").path();
            if path.extension().and_then(|e| e.to_str()) != Some("sh") {
                continue;
            }
            let name = path
                .file_name()
                .expect("a matched file has a name")
                .to_string_lossy()
                .into_owned();
            let body = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("{dir}/{name} must be readable: {e}"));
            // A lane is in scope exactly when it allocates its own evidence root.
            if body.contains("ART_DIR=") {
                lanes.push((format!("{dir}/{name}"), body));
            }
        }
    }
    // Directory order is not specified; the report must not depend on it (FL-INV-01).
    lanes.sort_by(|a, b| a.0.cmp(&b.0));

    // A moved directory or a broken filter must fail loudly rather than pass an empty
    // scan. A derived scope that silently derives nothing is worse than a hand-list.
    assert!(
        lanes.len() >= 20,
        "derived lane scan found only {} evidence lanes, so the scan scope is wrong; \
         this guard must never report success over an empty or truncated set",
        lanes.len()
    );

    for (relative, body) in &lanes {
        let atomic = body.contains(r#"if ! mkdir "$ART_DIR" 2>/dev/null; then"#)
            || body.contains(r#"if ! mkdir -- "$ART_DIR"; then"#);
        assert!(
            atomic,
            "{relative} allocates an evidence root but never claims it atomically; \
             on a RUN_ID collision two lanes would share one directory instead of one refusing"
        );
        assert!(
            !body.contains(r#"mkdir -p "$ART_DIR""#),
            "{relative} creates its evidence root with `mkdir -p`, which succeeds on an \
             existing directory and therefore cannot detect a collision at all"
        );
    }
}

/// The one launcher that must start Python UNSEALED, and the marker that says why.
///
/// Checked in both directions. The entry is honoured only while the file still carries
/// the negative-control assertion that *requires* an unsealed launch; sealing the probe,
/// or deleting the control, makes this entry stale and fails the guard rather than
/// leaving a permanent hole behind a name.
const UNSEALED_LAUNCH_ALLOWANCE: &[(&str, &str)] = &[(
    "scripts/tribunal/python_isolation_probe.sh",
    r#"check "script_dir_vector_reproduces_while_unprotected" "HIJACKED""#,
)];

fn scripts_tree(dir: &Path, found: &mut Vec<(String, String)>, repo: &Path) {
    let entries =
        fs::read_dir(dir).unwrap_or_else(|e| panic!("{} must be readable: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("directory entry must be readable").path();
        if path.is_dir() {
            scripts_tree(&path, found, repo);
            continue;
        }
        // Binary or non-UTF-8 files are not launchers; a read failure is not.
        let Ok(body) = fs::read_to_string(&path) else {
            continue;
        };
        let relative = path
            .strip_prefix(repo)
            .expect("a scanned path lies under the repository")
            .to_string_lossy()
            .into_owned();
        found.push((relative, body));
    }
}

/// Fold backslash continuations into one logical command, keeping the physical line
/// number the command started on. A launcher's flags routinely sit several continuation
/// lines below the interpreter token, and a per-physical-line reading calls those sealed
/// launches bare.
fn logical_lines(body: &str) -> Vec<(usize, String)> {
    let mut commands = Vec::new();
    let mut pending: Option<(usize, String)> = None;
    for (index, line) in body.lines().enumerate() {
        let continues = line.ends_with('\\');
        let piece = line.strip_suffix('\\').unwrap_or(line);
        match pending.as_mut() {
            Some((_, buffer)) => {
                buffer.push(' ');
                buffer.push_str(piece.trim());
            }
            None => pending = Some((index + 1, piece.to_owned())),
        }
        if !continues {
            commands.push(pending.take().expect("a command was started above"));
        }
    }
    if let Some(tail) = pending {
        commands.push(tail);
    }
    commands
}

/// Is this shell command an actual interpreter launch, as opposed to a mention?
fn launches_python(line: &str) -> bool {
    let trimmed = line.trim_start();
    if trimmed.starts_with('#') {
        return false;
    }
    // `command -v python3` resolves an interpreter without starting one; `-n`/`-z` test
    // that the resolution succeeded; the remaining forms name it in a diagnostic
    // message. None of them begins execution. The emptiness tests are matched on the
    // operator rather than on `[[`, so a launch inside a command substitution in a test
    // is still judged.
    if line.contains("command -v python3")
        || line.contains(r#"-n "$PYTHON_BIN""#)
        || line.contains(r#"-z "$PYTHON_BIN""#)
        || line.contains("python3 is required")
        || line.contains("python3_")
    {
        return false;
    }
    line.contains("python3") || line.contains("$PYTHON_BIN") || line.contains("${PYTHON[@]}")
}

/// Every trusted Python launcher under `scripts/` starts its interpreter sealed, and the
/// scope of "every" is derived from the tree rather than written down.
///
/// Python resolves imports from the launched script's own directory and from `PYTHONPATH`
/// ahead of the standard library, so a `scripts/hashlib.py` or an ambient `PYTHONPATH`
/// replaces the module that computes the governed digests and decides the verdicts
/// (`franken_lean-h40t`; both vectors are reproduced then refused, live, by
/// `scripts/tribunal/python_isolation_probe.sh`). `-I -S` closes both channels.
///
/// `every_supervisor_launcher_seals_python_configuration_before_imports` above asserts
/// that, but over a hand-written list of ten shell scripts and five Python entry points.
/// Measured at `4dc3e5fb`, that list had already gone stale in three places, and the
/// mutants say so: dropping `-I -S` from `scripts/e2e/contract_handoff.sh`, from
/// `scripts/e2e/unsafe_note_clippy.sh`, or the sealed shebang from
/// `scripts/extract/validate_extern_builtin_census.py` each left the suite green, while
/// the identical mutation in the listed `scripts/e2e/closure_audit.sh` exited 101. The
/// rig could always kill the mutant; it could not see the file. All three were sealed —
/// by their authors' care, and by nothing else.
///
/// The hand-list also could not have absorbed them as it stands: its "no bare `python3`
/// token" rule panics on `python3 -I -S "$root/..."`, which is a *sealed* launch, so
/// three correct files would have reddened the gate on being added. This guard judges
/// each launch line instead, which is the property that actually matters.
///
/// **What it does not catch, stated so nobody has to rediscover it.** Judgement is per
/// logical command, so a continued command carrying *two* interpreter starts passes on
/// the sealed one and an unsealed sibling rides along. No such command exists in this
/// tree — the shapes that do exist are a lone launch, or an interpreter path passed as
/// an expected-executable argument beside a sealed launch — but the guard cannot tell
/// those apart, and a future lane could introduce one. It is a *line* scanner over shell
/// text, not a parser, and it does not observe a single interpreter actually start:
/// that is `scripts/tribunal/python_isolation_probe.sh`'s job, and asserting `-I` is set
/// is not evidence that `-I` works.
#[test]
fn every_python_launch_under_scripts_is_sealed() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let mut files = Vec::new();
    scripts_tree(&repo.join("scripts"), &mut files, &repo);
    // Directory order is not specified; the report must not depend on it (FL-INV-01).
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let mut python_entry_points = 0usize;
    let mut shell_launchers = 0usize;
    let mut allowance_used: Vec<&str> = Vec::new();

    for (relative, body) in &files {
        if relative.ends_with(".py") {
            // A Python entry point is launched by its own shebang whenever it is run
            // directly, so the shebang is the launch and must carry the flags.
            python_entry_points += 1;
            assert!(
                body.starts_with("#!/usr/bin/env -S python3 -I -S\n"),
                "{relative} is a trusted Python entry point whose shebang does not seal \
                 startup; run directly, it resolves imports from its own directory first"
            );
            continue;
        }

        let allowed = UNSEALED_LAUNCH_ALLOWANCE
            .iter()
            .find(|(path, _)| path == relative);
        let mut launches = false;
        let mut unsealed: Vec<(usize, String)> = Vec::new();

        for (first_line, command) in logical_lines(body) {
            if !launches_python(&command) {
                continue;
            }
            launches = true;
            let sealed = command.contains("python3 -I")
                || command.contains(r#""$PYTHON_BIN" -I -S"#)
                || command.contains(r#"${PYTHON[@]}"#)
                || command.contains(r#"PYTHON=("$PYTHON_BIN" -I -S)"#);
            if !sealed {
                unsealed.push((first_line, command.trim().to_owned()));
            }
        }

        if !launches {
            continue;
        }
        shell_launchers += 1;

        // `${PYTHON[@]}` is an indirection, so a sealed-looking call site proves nothing
        // unless the array it expands to is itself frozen with the flags. This is the
        // mutation that survived: `PYTHON=("$PYTHON_BIN")` leaves every downstream
        // `"${PYTHON[@]}"` reading as a sealed launch while sealing nothing.
        if body.contains(r#"${PYTHON[@]}"#) {
            assert!(
                body.contains(r#"PYTHON=("$PYTHON_BIN" -I -S)"#),
                "{relative} launches Python through the ${{PYTHON[@]}} array but never \
                 freezes it as PYTHON=(\"$PYTHON_BIN\" -I -S), so every call site through \
                 that array starts an unsealed interpreter"
            );
        }

        if let Some((_, marker)) = allowed {
            assert!(
                body.contains(marker),
                "{relative} holds an unsealed-launch allowance whose stated reason is \
                 gone: the negative control {marker:?} is no longer in the file, so the \
                 allowance names something that is not there"
            );
            assert!(
                !unsealed.is_empty(),
                "{relative} no longer launches Python unsealed, so its allowance is \
                 stale and must be removed — this list may only shrink"
            );
            allowance_used.push(relative);
        } else {
            assert!(
                unsealed.is_empty(),
                "{relative} starts Python without -I -S at {unsealed:?}; an ambient \
                 PYTHONPATH or a module beside the script would then replace the \
                 stdlib under a trusted evidence producer"
            );
        }
    }

    // A moved directory or a broken filter must fail loudly rather than pass an empty
    // scan. A derived scope that silently derives nothing is worse than a hand-list,
    // because it reads as coverage. Floors, not equalities: a new sealed launcher must
    // not redden a correct tree.
    assert!(
        shell_launchers >= 12 && python_entry_points >= 5,
        "derived scan found {shell_launchers} shell launchers and {python_entry_points} \
         Python entry points under scripts/, which is too few for this tree; the scan \
         scope is wrong and this guard must never report success over a truncated set"
    );
    assert_eq!(
        allowance_used.len(),
        UNSEALED_LAUNCH_ALLOWANCE.len(),
        "an unsealed-launch allowance entry never matched a scanned file: {:?} were used \
         of {:?}. A dead entry is a hole with a name on it",
        allowance_used,
        UNSEALED_LAUNCH_ALLOWANCE
            .iter()
            .map(|(path, _)| *path)
            .collect::<Vec<_>>()
    );
}

/// The interpreter-configuration channels `franken_lean-h40t` requires the evidence
/// runner to classify. Transcribed once, from the bead's own scope paragraph, because
/// there is no machine-readable list to derive them from — and used only as a FLOOR, so
/// a runner that classifies more than these still passes.
const REQUIRED_PYTHON_CONFIGURATION_CHANNELS: &[&str] = &[
    "PYTHONEXECUTABLE",
    "PYTHONHOME",
    "PYTHONNOUSERSITE",
    "PYTHONPATH",
    "PYTHONSAFEPATH",
    "PYTHONSTARTUP",
    "PYTHONUSERBASE",
];

/// Loads the real `scripts/evidence.py` and asks its real classifier to judge a
/// synthetic environment. Sealed (`-I -S`) like every other trusted launch, and `-B` so
/// a guard can never leave a `__pycache__` in a governed directory.
///
/// An optional second argument is source executed **in the loaded module's own
/// namespace**, which is how the mutants below are planted. Injecting into the real
/// namespace rather than copying the file is not a shortcut: rebound constants are seen
/// by the module's own functions at call time, so a mutated constant behaves exactly as
/// an edited one would — and nothing is written to disk. The first version of this guard
/// wrote six 859 KB copies per run into a machine-wide shared target directory, an
/// unbounded growth vector for a test that runs on every commit.
const PYTHON_CLASSIFIER_PROBE: &str = r#"
import importlib.util, sys

spec = importlib.util.spec_from_file_location("fln_evidence_classifier_probe", sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

if len(sys.argv) > 2:
    exec(sys.argv[2], vars(module))

declared = sorted(module.PYTHON_CONFIGURATION_ENV_EXACT)
environ = {name: "hostile" for name in declared}
# Matches the prefix rule and is deliberately NOT in the named set, so the prefix has to
# be doing work of its own rather than restating the set.
environ["PYTHONBREAKPOINT"] = "hostile"
# Controls. A classifier that simply returned its whole input would satisfy every
# positive assertion below while classifying nothing.
environ.update({
    "PATH": "/usr/bin",
    "HOME": "/home/probe",
    "RUSTFLAGS": "-C debuginfo=0",
    "CARGO_HOME": "/cargo",
})

print("DECLARED " + " ".join(declared))
print("CLASSIFIED " + " ".join(module.overridden_python_environment(environ)))
print("PROBE-COMPLETE")
"#;

/// Ambient names that are not interpreter configuration. The probe plants these so a
/// classifier that admits everything cannot pass by breadth.
const PYTHON_CLASSIFIER_CONTROLS: &[&str] = &["PATH", "HOME", "RUSTFLAGS", "CARGO_HOME"];

/// Load `path` as the evidence runner and return `(declared, classified)`.
///
/// A probe that did not complete is a broken probe, never a clean result: it panics here
/// rather than returning empty vectors for the judgement below to quantify over.
fn classify_python_configuration(
    path: &Path,
    mutation: Option<&str>,
) -> (Vec<String>, Vec<String>) {
    let mut command = std::process::Command::new("python3");
    command
        .args(["-I", "-S", "-B", "-c", PYTHON_CLASSIFIER_PROBE])
        .arg(path);
    if let Some(mutation) = mutation {
        command.arg(mutation);
    }
    let run = command
        .output()
        .expect("the sealed interpreter must be able to load the evidence runner");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&run.stderr).into_owned();
    assert!(
        run.status.success() && stdout.contains("PROBE-COMPLETE"),
        "the classifier probe did not complete against {}, so nothing was measured. This \
         is a broken probe, not a clean result. status={:?} stderr={stderr}",
        path.display(),
        run.status.code()
    );
    let field = |tag: &str| -> Vec<String> {
        stdout
            .lines()
            .find_map(|line| line.strip_prefix(tag))
            .unwrap_or_else(|| panic!("the probe must report {tag}; got: {stdout}"))
            .split_whitespace()
            .map(str::to_owned)
            .collect()
    };
    (field("DECLARED "), field("CLASSIFIED "))
}

/// The whole judgement, in one place that a forged caller can drive.
///
/// Kept separate from the call site deliberately: a guard that can only be exercised
/// through its own producer cannot demonstrate that it discriminates, and this project
/// has already shipped one coverage check that was satisfied by an empty referent. Each
/// arm returns a distinct reason token, so a mutant can be required to die *for its
/// stated reason* rather than merely to fail.
fn judge_python_classification(declared: &[String], classified: &[String]) -> Result<(), String> {
    // (1) Declaration-level: the runner still NAMES every channel the bead requires.
    for channel in REQUIRED_PYTHON_CONFIGURATION_CHANNELS {
        if !declared.iter().any(|name| name == channel) {
            return Err(format!("undeclared-required-channel:{channel}"));
        }
    }
    // (2) Behavioural: a declared channel that is not classified is decoration.
    for channel in declared {
        if !classified.contains(channel) {
            return Err(format!("declared-but-unclassified:{channel}"));
        }
    }
    // (3) Behavioural: the prefix rule classifies something the named set does not list,
    // which is the only part of this family that carries behaviour at all.
    if !classified.iter().any(|name| name == "PYTHONBREAKPOINT") {
        return Err("prefix-rule-inert".to_owned());
    }
    // (4) The control: a classifier that returns its whole input classifies nothing.
    for control in PYTHON_CLASSIFIER_CONTROLS {
        if classified.iter().any(|name| name == control) {
            return Err(format!("control-admitted:{control}"));
        }
    }
    // (5) The one producer/validator join that IS bound today: the strict run-record
    // validator refuses an `overridden_env` that is not sorted and duplicate-free.
    let mut canonical = classified.to_vec();
    canonical.sort();
    canonical.dedup();
    if classified != canonical.as_slice() {
        return Err("not-sorted-duplicate-free".to_owned());
    }
    Ok(())
}

/// The Python configuration channels the evidence runner refuses are verified by
/// *running* its classifier, never by reading its constants — because reading them is
/// precisely what would have missed the defect this guard was written from.
///
/// `scripts/evidence.py` declares the interpreter-configuration family twice:
/// `PYTHON_CONFIGURATION_ENV_EXACT`, the seven named channels `franken_lean-h40t`
/// requires, and `PYTHON_CONFIGURATION_ENV_PREFIXES = ("PYTHON",)`.
/// `overridden_python_environment` admits a name that is in the set **or** matches a
/// prefix. Every member of the set begins with `PYTHON`, so the set is wholly subsumed
/// by the prefix and contributes nothing to the verdict. Measured at `5b6158ad` by
/// loading the real module and emptying one constant at a time: emptying
/// `PYTHON_CONFIGURATION_ENV_EXACT` returns a list **identical** to the baseline, while
/// emptying the prefix tuple drops `PYTHONBREAKPOINT` (8 names to 7). Dropping only
/// `PYTHONPATH` from the set is likewise identical.
///
/// That is worth stating because the bead asks for a mutant "that drops a `PYTHON*`
/// classification, killed by a discriminating test". For the **named set** no such test
/// can be written: the mutation is semantically a no-op, so a behavioural rig scores it
/// SURVIVED and is right to. Only the prefix tuple carries behaviour. So the two halves
/// below are deliberately different in kind, and the difference is the point:
///
/// * the floor over the declared set is a **declaration**-level check — it fails if the
///   runner stops naming a channel the bead requires, and it earns nothing about what
///   the runner does at runtime;
/// * everything else is **behavioural** — it fails only if a channel stops actually
///   being classified.
///
/// A guard that read the source and reported "seven channels classified" would have
/// been green on an inert set, which is the same shape as reporting coverage from a
/// list that no longer matches the tree.
///
/// **What this does not earn.** The classifier's output is recorded in evidence, and a
/// strict NDJSON validator elsewhere in the same file independently re-derives the rule
/// as a hardcoded `name.startswith("PYTHON")` rather than reading
/// `PYTHON_CONFIGURATION_ENV_PREFIXES`. The two copies are unbound: measured the same
/// way, widening the producer's tuple to `("PYTHON", "PY_", "PYVENV")` makes it emit
/// `PY_HOSTILE` and `PYVENV_LAUNCHER`, which that validator then refuses as malformed —
/// the runner rejecting a record it had just produced. This guard cannot close that; the
/// repair is one line inside `scripts/evidence.py`. Filed, not fixed here.
#[test]
fn python_configuration_channels_are_classified_by_measurement_not_declaration() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let (declared, classified) =
        classify_python_configuration(&repo.join("scripts/evidence.py"), None);

    if let Err(reason) = judge_python_classification(&declared, &classified) {
        panic!(
            "the evidence runner's interpreter-configuration classification is unsound \
             ({reason}). A channel in this family that stops being classified is one an \
             ambient environment can reopen under the process that computes the governed \
             digests and decides the verdicts (franken_lean-h40t). \
             declared={declared:?} classified={classified:?}"
        );
    }
}

/// Every arm of the judgement above kills a mutation, and each dies for its own reason.
///
/// The mutants are injected into the loaded module's namespace, never into the file in
/// the tree. That is not merely politeness toward whoever else is editing it: a campaign
/// that mutates a shared file cannot be re-run by the next reader, so its verdicts age
/// into a claim with nothing behind it. These re-run on every commit, write nothing, and
/// are anchored on nothing, so no mutant can silently fail to apply for want of a match.
///
/// The last mutant is the one worth reading. It drops `PYTHONPATH` from the named set,
/// which changes **no behaviour at all** — the prefix still classifies it — so every
/// behavioural arm stays green and only the declaration-level floor kills it. That is
/// the measurement from the doc comment above turned into a standing test: without arm
/// (1) the runner could quietly stop naming the channels the bead requires.
#[test]
fn the_python_configuration_guard_kills_each_mutation_it_claims_to() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let evidence = repo.join("scripts/evidence.py");

    // (name, source injected into the module namespace, the reason the guard must give)
    let mutants: &[(&str, &str, &str)] = &[
        (
            "prefix-tuple-emptied",
            "\ndef overridden_python_environment(environ):\n    \
             return sorted(n for n in environ if n in PYTHON_CONFIGURATION_ENV_EXACT)\n",
            "prefix-rule-inert",
        ),
        (
            "one-declared-channel-not-classified",
            "\ndef overridden_python_environment(environ):\n    \
             return sorted(n for n in environ \
             if n.startswith(\"PYTHON\") and n != \"PYTHONPATH\")\n",
            "declared-but-unclassified:PYTHONPATH",
        ),
        (
            "classifier-admits-everything",
            "\ndef overridden_python_environment(environ):\n    return sorted(environ)\n",
            "control-admitted:PATH",
        ),
        (
            "classification-not-canonical",
            "\ndef overridden_python_environment(environ):\n    \
             return list(reversed(sorted(n for n in environ if n.startswith(\"PYTHON\"))))\n",
            "not-sorted-duplicate-free",
        ),
        (
            "required-channel-undeclared-behaviour-unchanged",
            "\nPYTHON_CONFIGURATION_ENV_EXACT = frozenset({\"PYTHONHOME\", \"PYTHONSTARTUP\", \
             \"PYTHONEXECUTABLE\", \"PYTHONUSERBASE\", \"PYTHONNOUSERSITE\", \"PYTHONSAFEPATH\"})\n",
            "undeclared-required-channel:PYTHONPATH",
        ),
    ];

    // The unmutated control. If the injection channel silently did nothing, every mutant
    // below would report this same verdict, so it is measured rather than assumed.
    let (clean_declared, clean_classified) = classify_python_configuration(&evidence, None);
    assert_eq!(
        judge_python_classification(&clean_declared, &clean_classified),
        Ok(()),
        "the unmutated runner must pass, or the mutants below prove nothing about the \
         mutations and everything about a broken baseline"
    );

    for (name, mutation, expected_reason) in mutants {
        let (declared, classified) = classify_python_configuration(&evidence, Some(mutation));
        // A mutant that does not create the condition it claims is not evidence of a
        // hole. Every one of these must move at least one of the two observations —
        // including the last, which moves `declared` while leaving behaviour untouched.
        assert!(
            declared != clean_declared || classified != clean_classified,
            "mutant {name} produced exactly the unmutated result, so it did not apply and \
             scoring it proves nothing"
        );
        let verdict = judge_python_classification(&declared, &classified);
        assert_eq!(
            verdict.as_ref().map_err(String::as_str),
            Err(*expected_reason),
            "mutant {name} was not killed for its stated reason. A rig that accepts any \
             failure would score a mutant killed by a check that had stopped testing the \
             property. declared={declared:?} classified={classified:?}"
        );
    }

    // The harness's own control. If a broken probe returned empty vectors instead of
    // panicking, every mutant above would "die" on the first arm and this whole test
    // would be theatre. A module that no longer supplies a classification at all must be
    // refused as a broken probe, not judged as a clean one.
    let refused = std::panic::catch_unwind(|| {
        classify_python_configuration(&evidence, Some("del PYTHON_CONFIGURATION_ENV_EXACT"))
    });
    assert!(
        refused.is_err(),
        "a module supplying no classification was judged instead of being refused, so this \
         guard cannot tell a clean tree from a probe that measured nothing"
    );
}

/// The evidence surface refuses a root whose `.git` is a gitdir pointer, and AGENTS.md
/// still says which surfaces that takes down.
///
/// `run_git` lstats `ROOT/.git` and refuses unless it is a real directory. In a linked git
/// worktree `.git` is a *file* holding a `gitdir:` pointer, so every trusted path reaching
/// `run_git` refuses there — `scripts/check.sh`, the evidence self-test,
/// `scripts/verify_vendor_tree.sh`, and every `fln.e2e/2` lane, whose first governed step
/// is `hash-tree --vendor-path` (bead `franken_lean-worktree-gitdir-refusal-hugg`).
///
/// This cost real verification before anyone noticed, for a reason no amount of care
/// prevents: each failure announces something else. `check.sh` reports that it cannot
/// inventory UBS inputs, so the reader goes looking for a missing tool; a lane reports
/// that it cannot hash governed inputs, or cannot verify the pinned Reference tree. The
/// true line is printed once, above the lane's louder and wrong summary.
///
/// **The exit code is not the discriminator — the message is.** A root whose `.git` is a
/// real directory also exits 2, because git then runs and reports "not a git repository".
/// So the control here is the file/directory distinction itself: only the pointer form may
/// produce the refusal. Without it, a mistyped invocation would exit 2 and this test would
/// pass with no content.
///
/// The second half binds the doctrine to the behaviour. A guard that only checked the
/// refusal would let AGENTS.md quietly stop naming the affected surfaces, which is the
/// half that actually strands a reader; a guard that only read AGENTS.md would keep
/// asserting a rule after the code changed underneath it.
#[test]
fn the_evidence_surface_refuses_a_gitdir_pointer_root() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let evidence = repo.join("scripts/evidence.py");
    let scratch = std::env::var("CARGO_TARGET_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| repo.join("target"))
        .join(format!("fln-gitdir-refusal-{}", std::process::id()));

    // Three shapes, because the refusal now has to DISCRIMINATE rather than merely fire.
    // A plain regular file reaches the same refusal as a gitdir pointer, so a message that
    // announced a linked worktree for any non-directory would be wrong exactly half the
    // time — and wrong in the direction that sends the reader to look for a worktree they
    // are not in.
    enum GitShape {
        Directory,
        Pointer,
        PlainFile,
    }

    let probe = |name: &str, shape: GitShape| -> (Option<i32>, String) {
        let root = scratch.join(name);
        fs::create_dir_all(&root).expect("probe root must be creatable");
        let git = root.join(".git");
        match shape {
            GitShape::Directory => {
                fs::create_dir_all(&git).expect("probe .git directory must be creatable");
            }
            // Exactly what `git worktree add` writes into a linked worktree.
            GitShape::Pointer => {
                fs::write(
                    &git,
                    "gitdir: /nonexistent/repository/.git/worktrees/probe\n",
                )
                .expect("probe .git pointer must be writable");
            }
            // A regular file that is NOT a pointer. Same refusal, different cause.
            GitShape::PlainFile => {
                fs::write(&git, "this file is not a gitdir pointer\n")
                    .expect("probe .git plain file must be writable");
            }
        }
        let run = std::process::Command::new("python3")
            .args(["-I", "-S"])
            .arg(&evidence)
            .arg("ubs-inventory")
            .arg("--root")
            .arg(&root)
            .args(["--scope", "all-tracked"])
            .arg("--output")
            .arg(root.join("inventory.json"))
            .arg("--artifact-root")
            .arg(&root)
            .output()
            .expect("the sealed interpreter must be able to run the evidence runner");
        (
            run.status.code(),
            String::from_utf8_lossy(&run.stderr).into_owned(),
        )
    };

    const REFUSAL: &str = "requires a real repository .git directory";
    // The half of the message that does the reader's diagnosis for them. Before this
    // existed, the refusal fired correctly and named nothing, so `check.sh` saying "cannot
    // inventory UBS inputs" was the loudest true-sounding thing on the screen and people
    // spent a day looking for a missing tool (bead `franken_lean-worktree-gitdir-refusal-hugg`).
    const NAMES_THE_WORKTREE: &str = "LINKED GIT WORKTREE";

    let (pointer_code, pointer_stderr) = probe("gitdir-pointer", GitShape::Pointer);
    assert_eq!(
        pointer_code,
        Some(2),
        "a gitdir-pointer root must be a typed setup failure, not a crash or a pass: {pointer_stderr}"
    );
    assert!(
        pointer_stderr.contains(REFUSAL),
        "a root whose .git is a gitdir pointer must be refused by name, so the reader is \
         not sent to diagnose a missing tool; got: {pointer_stderr}"
    );
    assert!(
        pointer_stderr.contains(NAMES_THE_WORKTREE),
        "the refusal fired but did not SAY what it found. Firing is not the point: every \
         caller prints a louder and wrong summary underneath this line, so a refusal that \
         names no cause leaves the reader diagnosing a missing tool, a dirty tree or an \
         absent pin. The message must name the linked worktree; got: {pointer_stderr}"
    );

    // The control. A real .git directory must NOT produce this refusal -- git runs and
    // fails on its own terms. Same exit code, different reason, which is the whole point.
    let (_, directory_stderr) = probe("gitdir-directory", GitShape::Directory);
    assert!(
        !directory_stderr.contains(REFUSAL),
        "the refusal fired for a root whose .git IS a real directory, so it is not keyed on \
         the worktree condition at all and the probe above proves nothing: {directory_stderr}"
    );

    // The second control, and the one that keeps the new sentence honest. A plain regular
    // file hits the SAME refusal, so a message that announced a worktree for every
    // non-directory would be wrong here -- and wrong in the direction that sends a reader
    // hunting for a worktree they are not in. Refuse, but do not diagnose what you did not
    // find.
    let (plain_code, plain_stderr) = probe("gitdir-plain-file", GitShape::PlainFile);
    assert_eq!(
        plain_code,
        Some(2),
        "a .git that is a plain regular file must still be a typed setup failure: {plain_stderr}"
    );
    assert!(
        plain_stderr.contains(REFUSAL),
        "a .git that is a plain regular file must still be refused: {plain_stderr}"
    );
    assert!(
        !plain_stderr.contains(NAMES_THE_WORKTREE),
        "the refusal called a plain regular .git a linked worktree. It is not one, and this \
         is the failure mode the new message introduces: a diagnosis confident enough to be \
         wrong. Key it on the `gitdir:` pointer bytes, not on `not a directory`; \
         got: {plain_stderr}"
    );

    // --- the doctrine half, scoped to the section that must carry it ------------------
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let heading = "### Where a green bar may be taken from";
    let start = agents
        .find(heading)
        .expect("AGENTS.md must keep the section stating where a green bar may be taken from");
    let section = &agents[start..];
    let section = &section[..section.find("\n---").unwrap_or(section.len())];

    for surface in [
        "scripts/check.sh",
        "evidence self-test",
        "scripts/verify_vendor_tree.sh",
        "fln.e2e/2",
        "ubs-inventory",
        "vendor-binding",
        "--vendor-path",
        "main tree",
        "the_evidence_surface_refuses_a_gitdir_pointer_root",
    ] {
        assert!(
            section.contains(surface),
            "the AGENTS.md green-bar section no longer names {surface:?}. A reader who \
             verifies in a worktree is stranded by exactly this omission, and the omission \
             is invisible at the point of failure"
        );
    }
}

/// The same refusal, in a **real** linked worktree rather than a hand-built one — the half
/// `franken_lean-worktree-gitdir-refusal-hugg` asks for in its own words: *"No claim that
/// reading the source substitutes for running the trusted path in a real worktree."*
///
/// **What this adds over the sibling above is exactly one property, and naming it is the whole
/// justification for a second test.** The sibling writes `gitdir: /nonexistent/repository/…`,
/// so its pointer **never resolves**. `run_git` does not resolve the pointer today, so both
/// roots refuse identically and the sibling is correct — but that equivalence is a property of
/// the *current* implementation, not of the shapes. The bead's candidate 2 is precisely the
/// change that breaks it: *"if [a linked worktree] is [admissible], resolve the gitdir pointer
/// and bind the run to the resolved repository identity."* On the day anyone implements that,
/// the sibling keeps passing while describing a root no worktree resembles, because a
/// dangling pointer would refuse for a reason that has nothing to do with worktrees.
///
/// So this test asserts the resolution **as a precondition** before it asserts anything else.
/// Without that assertion it degenerates into a slower copy of the sibling, and a duplicated
/// test that has silently stopped testing anything extra is worse than no test at all.
///
/// **It builds its own repository rather than using this one.** `git worktree add` against the
/// real checkout would write into the shared `.git/worktrees/`, from a test, in a tree six
/// panes share — and would leave an entry behind that nobody owns. A purpose-built repo in the
/// scratch target gives a pointer written by **git itself**, pointing at a gitdir that **exists**,
/// for 240 KB and about 0.6 s measured.
///
/// **The exit code discriminates nothing here either**: the worktree cell and the control both
/// exit 2 in the sibling's world, and the control below exits **0** only because a real `.git`
/// directory lets the run succeed outright. The message is the discriminator, as everywhere in
/// this family.
#[test]
fn the_evidence_surface_refuses_a_real_linked_worktree_whose_pointer_resolves() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let evidence = repo.join("scripts/evidence.py");
    let scratch = std::env::var("CARGO_TARGET_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| repo.join("target"))
        .join(format!("fln-real-worktree-{}", std::process::id()));
    let source = scratch.join("source-repo");
    let worktree = scratch.join("linked-worktree");
    fs::create_dir_all(&source).expect("the purpose-built repository root must be creatable");

    let git = |args: &[&str], cwd: &Path| -> bool {
        std::process::Command::new("git")
            .args(args)
            .current_dir(cwd)
            .output()
            .map(|out| out.status.success())
            .unwrap_or(false)
    };

    // Setup failures must be LOUD. A silent skip here would leave the suite green while the
    // only cell that exercises a resolving pointer never ran.
    assert!(git(&["init", "-q", "."], &source), "git init must succeed");
    assert!(
        git(&["config", "user.email", "probe@example.invalid"], &source)
            && git(&["config", "user.name", "probe"], &source),
        "git identity must be configurable in the purpose-built repository"
    );
    fs::write(source.join("f.txt"), "x\n").expect("a file must be writable in the probe repo");
    assert!(git(&["add", "f.txt"], &source), "git add must succeed");
    assert!(
        git(&["commit", "-qm", "base"], &source),
        "the probe repository needs one commit before a worktree can be added"
    );
    assert!(
        git(
            &[
                "worktree",
                "add",
                "--no-checkout",
                "--detach",
                worktree.to_str().expect("scratch path must be UTF-8"),
                "HEAD",
            ],
            &source,
        ),
        "git worktree add must succeed; without a REAL worktree this test is the sibling"
    );

    // --- the precondition that makes this test different from the sibling above ----------
    let pointer_path = worktree.join(".git");
    let pointer = fs::read_to_string(&pointer_path).expect("git must write a .git pointer file");
    assert!(
        pointer.starts_with("gitdir: "),
        "git did not write a gitdir pointer into the linked worktree: {pointer:?}"
    );
    let target = Path::new(pointer.trim_start_matches("gitdir: ").trim());
    assert!(
        target.exists(),
        "the pointer target {target:?} does not exist, so this root is the sibling's \
         dangling-pointer fixture wearing a real worktree's name and it tests nothing extra"
    );

    let probe = |root: &Path, name: &str| -> (Option<i32>, String) {
        let out_dir = scratch.join(name);
        fs::create_dir_all(&out_dir).expect("probe output root must be creatable");
        let run = std::process::Command::new("python3")
            .args(["-I", "-S"])
            .arg(&evidence)
            .arg("ubs-inventory")
            .arg("--root")
            .arg(root)
            .args(["--scope", "all-tracked"])
            .arg("--output")
            .arg(out_dir.join("inventory.json"))
            .arg("--artifact-root")
            .arg(&out_dir)
            .output()
            .expect("the sealed interpreter must be able to run the evidence runner");
        (
            run.status.code(),
            String::from_utf8_lossy(&run.stderr).into_owned(),
        )
    };

    const REFUSAL: &str = "requires a real repository .git directory";
    const NAMES_THE_WORKTREE: &str = "LINKED GIT WORKTREE";

    let (code, stderr) = probe(&worktree, "cell-worktree");
    assert_eq!(
        code,
        Some(2),
        "a real linked worktree must be a typed setup failure, not a crash or a pass: {stderr}"
    );
    assert!(
        stderr.contains(REFUSAL),
        "a real linked worktree must be refused by name: {stderr}"
    );
    assert!(
        stderr.contains(NAMES_THE_WORKTREE),
        "the refusal fired in a REAL linked worktree and did not say so. Every caller prints a \
         louder and wrong summary underneath this line, so a refusal naming no cause leaves the \
         reader diagnosing a missing tool; got: {stderr}"
    );

    // The control, and it is not the same control as the sibling's. There, a `.git` directory
    // was empty and git failed on its own terms at exit 2. Here the source repo is REAL, so a
    // correct implementation SUCCEEDS — which separates "refuses everything it is pointed at"
    // from "refuses the worktree condition specifically".
    let (source_code, source_stderr) = probe(&source, "cell-source");
    assert!(
        !source_stderr.contains(REFUSAL),
        "the refusal fired against a genuine repository with a real .git directory, so it is \
         not keyed on the worktree condition and the cell above proves nothing: {source_stderr}"
    );
    assert_eq!(
        source_code,
        Some(0),
        "the same command against the worktree's own source repository must SUCCEED. If it \
         does not, the cell above may be refusing for an unrelated reason and this test is \
         vacuous: {source_stderr}"
    );
}

/// The fourth `.git` shape: **no `.git` at all**, which is the RCH worker's checkout
/// (bead `fln-yihl`, the host half of `franken_lean-worktree-gitdir-refusal-hugg`).
///
/// The sibling above covers three shapes and every one of them is about the wrong **tree**. This
/// is the wrong **host**, and it is the shape nobody chooses: RCH's PreToolUse hook offloads a
/// bare `cargo test` with nothing in the command saying so, and the worker's checkout is synced
/// without `.git` (bead `franken_lean-rch-clean-overlay-has-no-git-dir-46pw`). So an agent who
/// runs the mandated gate exactly as AGENTS.md prescribes it can have the whole evidence surface
/// refuse on a machine they never chose, and read a cause that names something else.
///
/// **The exit code discriminates nothing, which is why this is a message assertion.** Measured at
/// `ef389785` against both the committed and the working-tree copy of `scripts/evidence.py` —
/// they agree — a root with no `.git` exits **2**, and so does a root whose `.git` is a real
/// directory, because there git runs and fails on its own terms. Only the text separates them.
///
/// **And the message must not over-diagnose.** The pointer refusal names a LINKED GIT WORKTREE.
/// A worker is not a worktree, so borrowing that sentence here would be the same failure the
/// sibling guards against one shape over: a diagnosis confident enough to be wrong, sending the
/// reader to hunt for a worktree they are not in.
/// The absent-`.git` refusal is its OWN sentence, not the non-directory one.
const WORKER_ABSENT_REFUSAL: &str = "requires an explicit repository .git directory";
const WORKER_NAMES_THE_WORKTREE: &str = "LINKED GIT WORKTREE";

/// Run `ubs-inventory` against a purpose-built root, with or without a real `.git` directory.
fn worker_probe(
    evidence: &Path,
    scratch: &Path,
    name: &str,
    with_git_dir: bool,
) -> (Option<i32>, String) {
    let root = scratch.join(name);
    fs::create_dir_all(&root).expect("probe root must be creatable");
    if with_git_dir {
        fs::create_dir_all(root.join(".git")).expect("probe .git directory must be creatable");
    }
    let run = std::process::Command::new("python3")
        .args(["-I", "-S"])
        .arg(evidence)
        .arg("ubs-inventory")
        .arg("--root")
        .arg(&root)
        .args(["--scope", "all-tracked"])
        .arg("--output")
        .arg(root.join("inventory.json"))
        .arg("--artifact-root")
        .arg(&root)
        .output()
        .expect("the sealed interpreter must be able to run the evidence runner");
    (
        run.status.code(),
        String::from_utf8_lossy(&run.stderr).into_owned(),
    )
}

/// Judge one (evidence surface, doctrine text) pair, returning a finding per broken property.
///
/// Findings rather than assertions, so a mutant is planted in the ARGUMENTS and each property
/// can be gutted alone. `scripts/evidence.py` is an orphaned working-tree file this session may
/// not modify (bead `franken_lean-h4o1`), so every mutant below is a doctored COPY in scratch and
/// the real file is never written.
fn worker_refusal_findings(evidence: &Path, agents: &str, scratch: &Path) -> Vec<String> {
    let mut findings = Vec::new();

    let (absent_code, absent_stderr) = worker_probe(evidence, scratch, "worker-no-git", false);
    if absent_code != Some(2) {
        findings.push(format!(
            "absent-exit: a root with no .git must be a typed setup failure (exit 2), got \
             {absent_code:?}. An RCH worker's checkout is exactly this root, so a pass here is a \
             verdict about a machine the caller never chose: {absent_stderr}"
        ));
    }
    if !absent_stderr.contains(WORKER_ABSENT_REFUSAL) {
        findings.push(format!(
            "absent-unnamed: a root with no .git must be refused BY NAME. Every caller prints a \
             louder and wrong summary over this line — check.sh says it cannot inventory UBS \
             inputs — so a refusal naming no cause sends the reader after a missing tool: \
             {absent_stderr}"
        ));
    }
    if absent_stderr.contains(WORKER_NAMES_THE_WORKTREE) {
        findings.push(format!(
            "absent-over-diagnosed: the refusal called a checkout with no .git a LINKED GIT \
             WORKTREE. It is not one — this is the RCH worker shape — and announcing a worktree \
             sends the reader to diagnose a checkout they are not in: {absent_stderr}"
        ));
    }

    // The control that makes the three above mean anything: a real `.git` directory exits 2 as
    // well, because there git runs and fails on its own terms. Nothing about the status
    // separates a genuine refusal from a probe that merely failed, so a rig checking "non-zero"
    // would pass with no content at all.
    let (directory_code, directory_stderr) =
        worker_probe(evidence, scratch, "worker-real-git", true);
    if directory_code != Some(2) {
        findings.push(format!(
            "control-exit: the real-.git control must reach the same exit code, or this check is \
             discriminating on the status rather than on the refusal: {directory_stderr}"
        ));
    }
    if directory_stderr.contains(WORKER_ABSENT_REFUSAL) {
        findings.push(format!(
            "control-refused: the absent-.git refusal fired for a root whose .git IS a real \
             directory, so it is not keyed on the missing-repository condition at all and the \
             probes above prove nothing: {directory_stderr}"
        ));
    }

    // --- the doctrine half. The rule this earns lives in the section readers consult ------
    let heading = "### Where a green bar may be taken from";
    let Some(start) = agents.find(heading) else {
        findings.push(
            "doctrine-missing-section: AGENTS.md no longer carries the section stating where a \
             green bar may be taken from, so this check has nothing to hold and refuses rather \
             than passing vacuously."
                .to_string(),
        );
        return findings;
    };
    let section = &agents[start..];
    let section = &section[..section.find("\n---").unwrap_or(section.len())];

    // Each needle is a load-bearing half of the rule. The reason they are checked rather than
    // trusted to prose is `hugg`: that correction was broadcast three times in one day and did
    // not survive a pane restart. A rule nobody can read at session start is not a rule.
    for needed in [
        "RCH",
        "unattributed",
        "--clean-overlay",
        "--overlay-path",
        WORKER_ABSENT_REFUSAL,
        "the_evidence_surface_refuses_a_worker_checkout_with_no_git_at_all",
    ] {
        if !section.contains(needed) {
            findings.push(format!(
                "doctrine-dropped: the AGENTS.md green-bar section no longer names {needed:?}. \
                 That section is where an agent decides whether a green may be cited, and an RCH \
                 default-mode green is about the worker's tree rather than theirs — an omission \
                 here is invisible at the point of failure, which is a bead closed on somebody \
                 else's build."
            ));
        }
    }
    findings
}

fn worker_scratch(tag: &str) -> PathBuf {
    let dir = std::env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("target"))
        .join(format!("fln-worker-refusal-{}-{tag}", std::process::id()));
    fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

fn worker_repo() -> PathBuf {
    fln_conformance::checked_workspace_root!()
        .canonicalize()
        .expect("the repository root must resolve")
}

/// Write a doctored copy of the evidence surface. The original is never touched.
fn doctored_evidence(tag: &str, edit: impl Fn(String) -> String) -> (PathBuf, PathBuf) {
    let repo = worker_repo();
    let source = fs::read_to_string(repo.join("scripts/evidence.py")).expect("evidence.py");
    let scratch = worker_scratch(tag);
    let path = scratch.join("evidence_mutant.py");
    let mutated = edit(source.clone());
    assert_ne!(
        mutated, source,
        "mutant {tag} changed nothing, so the cell below would score a pass against the real \
         surface and prove nothing. The needle it edits has moved."
    );
    fs::write(&path, mutated).expect("doctored evidence surface is writable");
    (path, scratch)
}

#[test]
fn the_evidence_surface_refuses_a_worker_checkout_with_no_git_at_all() {
    let repo = worker_repo();
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let findings = worker_refusal_findings(
        &repo.join("scripts/evidence.py"),
        &agents,
        &worker_scratch("live"),
    );
    assert!(
        findings.is_empty(),
        "the evidence surface no longer refuses an RCH worker's checkout as this repository's \
         doctrine says it does:\n\n{}",
        findings.join("\n\n")
    );
}

/// Gut 1: the refusal stops naming the missing repository.
#[test]
fn a_worker_refusal_that_stops_naming_its_cause_is_caught() {
    let (evidence, scratch) = doctored_evidence("unnamed", |text| {
        text.replace(WORKER_ABSENT_REFUSAL, "cannot proceed")
    });
    let agents = fs::read_to_string(worker_repo().join("AGENTS.md")).expect("AGENTS.md");
    let findings = worker_refusal_findings(&evidence, &agents, &scratch);
    assert!(
        findings.iter().any(|f| f.starts_with("absent-unnamed")),
        "a refusal that fires without naming its cause must be caught — that is the whole \
         `hugg` defect, one host over: {findings:?}"
    );
}

/// Gut 2: the refusal over-diagnoses, calling a worker a linked worktree.
#[test]
fn a_worker_refusal_that_claims_a_linked_worktree_is_caught() {
    let (evidence, scratch) = doctored_evidence("overdiagnosed", |text| {
        text.replace(
            WORKER_ABSENT_REFUSAL,
            "requires an explicit repository .git directory (LINKED GIT WORKTREE)",
        )
    });
    let agents = fs::read_to_string(worker_repo().join("AGENTS.md")).expect("AGENTS.md");
    let findings = worker_refusal_findings(&evidence, &agents, &scratch);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("absent-over-diagnosed")),
        "a diagnosis confident enough to be wrong must be caught: {findings:?}"
    );
}

/// Gut 3: the surface stops refusing an absent `.git` and lets git fail on its own terms.
///
/// This is the mutant that proves the exit code is not the discriminator. The doctored surface
/// still exits 2 — git simply fails for its own reason — so only the missing message catches it.
#[test]
fn a_surface_that_stops_refusing_a_worker_checkout_is_caught() {
    let (evidence, scratch) = doctored_evidence("permissive", |text| {
        text.replace(
            "raise EvidenceError(f\"{subject} requires an explicit repository .git directory\") from error",
            "git_mode = stat.S_IFDIR",
        )
    });
    let agents = fs::read_to_string(worker_repo().join("AGENTS.md")).expect("AGENTS.md");
    let findings = worker_refusal_findings(&evidence, &agents, &scratch);
    assert!(
        findings.iter().any(|f| f.starts_with("absent-unnamed")),
        "a surface that stopped refusing a repository-less root must be caught: {findings:?}"
    );
}

/// Gut 4: the refusal becomes unconditional and fires on a real repository too.
///
/// The direction a "does it fire?" rig cannot see. An always-refusing surface satisfies every
/// positive cell above and is useless, which is why the control is not decoration.
#[test]
fn a_worker_refusal_that_fires_on_a_real_repository_is_caught() {
    let (evidence, scratch) = doctored_evidence("overbroad", |text| {
        text.replace(
            "        git_mode = git_dir.lstat().st_mode",
            "        raise FileNotFoundError(str(git_dir))",
        )
    });
    let agents = fs::read_to_string(worker_repo().join("AGENTS.md")).expect("AGENTS.md");
    let findings = worker_refusal_findings(&evidence, &agents, &scratch);
    assert!(
        findings.iter().any(|f| f.starts_with("control-refused")),
        "a refusal that fires for a real repository must be caught by the control: {findings:?}"
    );
}

/// Gut 7, and the one that matters most: the surface returns empty instead of refusing.
///
/// Measured — this mutant exits **0** and prints nothing, so a worker checkout produces a
/// clean-looking inventory of a repository the surface could not read. Every other cell here is
/// a refusal behaving wrongly; this is the *false clean*, which is the same "a broken walk and a
/// clean tree are the same green" hazard one host over, and the only shape that would be quoted
/// into a bead as evidence.
///
/// It is deliberately **not isolated**: it fires `absent-exit` and `absent-unnamed` together.
/// That over-determination is reported rather than tuned away, because the alternative is
/// contriving a mutant that changes the exit code while preserving the message, which no real
/// regression looks like.
#[test]
fn a_surface_that_returns_empty_instead_of_refusing_is_caught() {
    let (evidence, scratch) = doctored_evidence("silent", |text| {
        text.replace(
            "raise EvidenceError(f\"{subject} requires an explicit repository .git directory\") from error",
            "return b\"\"",
        )
    });
    let agents = fs::read_to_string(worker_repo().join("AGENTS.md")).expect("AGENTS.md");
    let findings = worker_refusal_findings(&evidence, &agents, &scratch);
    assert!(
        findings.iter().any(|f| f.starts_with("absent-exit")),
        "a surface that answers a repository-less root with exit 0 and an empty inventory must \
         be caught: that is a green bar about a checkout nothing could read: {findings:?}"
    );
}

/// Gut 5: the doctrine is softened — the attributable invocation stops being named.
///
/// `hugg`'s lesson is that the mechanism and the sentence must fail together. A reader who
/// cannot find `--clean-overlay` has no way to obtain an attributable green and will take the
/// default-mode one.
#[test]
fn a_doctrine_that_drops_the_attributable_invocation_is_caught() {
    let repo = worker_repo();
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md");
    let softened = agents.replace("--clean-overlay", "the attributable mode");
    let findings = worker_refusal_findings(
        &repo.join("scripts/evidence.py"),
        &softened,
        &worker_scratch("softened"),
    );
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("doctrine-dropped") && f.contains("clean-overlay")),
        "dropping the attributable invocation from the doctrine must be caught: {findings:?}"
    );
}

/// Gut 6: the section itself disappears, which must refuse rather than pass vacuously.
#[test]
fn a_missing_green_bar_section_refuses_rather_than_passing_vacuously() {
    let repo = worker_repo();
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md");
    let gutted = agents.replace("### Where a green bar may be taken from", "### Removed");
    let findings = worker_refusal_findings(
        &repo.join("scripts/evidence.py"),
        &gutted,
        &worker_scratch("sectionless"),
    );
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("doctrine-missing-section")),
        "a doctrine section this check cannot locate is a broken scan, never a clean file: \
         {findings:?}"
    );
}

/// The closure-binding instant AGENTS.md publishes is the one the validator enforces.
///
/// `scripts/evidence.py` refuses a `complete` coverage row for a bead closed at or after
/// `CLOSURE_BINDING_EFFECTIVE_FROM` unless the row cites a bead comment created at or after
/// that bead's own `closed_at` (bead `fln-judgement-row-not-bound-to-its-closure-iumd`). The
/// instruction that tells six panes how to close a bead lives in AGENTS.md and names that
/// instant literally, so the two artifacts are a join: move the constant and the doctrine
/// silently misstates the rule, in the direction where a pane authors a row it believes is
/// compliant and the gate refuses it for a reason the doc does not mention.
///
/// This is deliberately the cheap half. The law's own behaviour — planted violation, planted
/// correct repair, borrowed citation, absent referent, undecidable instant — is a mutation
/// matrix inside `evidence.py self-test`, which is where the validator's other twenty-two
/// mutants already live. What `cargo test` adds here is that deleting the refusal or moving
/// its boundary cannot pass silently in a tree whose doctrine still promises them.
#[test]
fn the_closure_binding_instant_is_the_one_agents_md_publishes() {
    let repo = fln_conformance::checked_workspace_root!();
    let validator = trusted_script("scripts/evidence.py");

    let assignment = "CLOSURE_BINDING_EFFECTIVE_FROM = \"";
    let start = validator.find(assignment).unwrap_or_else(|| {
        panic!(
            "scripts/evidence.py no longer assigns CLOSURE_BINDING_EFFECTIVE_FROM. Either the \
             closure-binding law was removed — in which case AGENTS.md is still telling every \
             pane to cite a post-close comment — or it was renamed and this join must follow it"
        )
    }) + assignment.len();
    let instant: String = validator[start..]
        .chars()
        .take_while(|c| *c != '"')
        .collect();
    // A whole-second UTC instant, which is what the law compares at and what the doctrine
    // quotes. Asserting the shape keeps the extraction from silently yielding an empty
    // string and then "finding" it in a document that never mentioned it.
    assert_eq!(
        instant.len(),
        30,
        "CLOSURE_BINDING_EFFECTIVE_FROM is not a nanosecond UTC instant: {instant:?}"
    );
    let published = format!("{}Z", &instant[..19]);

    // The refusal AGENTS.md promises, asserted against the validator that must produce it.
    // Scoped to the sentence, not the file: a check that the words appear *somewhere* in a
    // 23k-line script is satisfied by this test's own quotation of them if it ever moves.
    for produced in ["does not judge the closure it is filed for", "bead-comment"] {
        assert!(
            validator.contains(produced),
            "scripts/evidence.py no longer produces {produced:?}, which AGENTS.md tells \
             closers to expect and to take the requirement from"
        );
    }

    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let heading = "### Closing a bead: the judgement row";
    let start = agents
        .find(heading)
        .expect("AGENTS.md must keep the section on closing a bead and its judgement row");
    let section = &agents[start..];
    let section = &section[..section.find("\n---").unwrap_or(section.len())];

    assert!(
        section.contains(&published),
        "the AGENTS.md closing-a-bead section names an instant other than the validator's \
         CLOSURE_BINDING_EFFECTIVE_FROM ({published}). A pane reading the doc would compute \
         the wrong obligation from it, and the gate would refuse for a reason the doc denies"
    );
    for obligation in [
        "bead-comment:<bead-id>:<comment-id>",
        "br comments add",
        "closed_at",
        "structural",
    ] {
        assert!(
            section.contains(obligation),
            "the AGENTS.md closing-a-bead section no longer states {obligation:?}. The rule \
             is enforced mechanically, so an unstated obligation surfaces as a refusal at \
             commit time with no instruction anywhere for satisfying it"
        );
    }
}

/// The negative probe that every interpreter-isolation citation attributes its outcome to.
const ISOLATION_PROBE: &str = "scripts/tribunal/python_isolation_probe.sh";

/// One run of the probe, read back from the record it wrote rather than from its narration.
struct ProbeRun {
    exit: Option<i32>,
    /// `(check name, passed)`, in emission order.
    outcomes: Vec<(String, bool)>,
    /// The `run_end` verdict token: `pass`, `fail`, or `inconclusive`.
    verdict: String,
    /// The `run_end` reason, carried only by a typed setup failure.
    reason: String,
    stderr: String,
}

/// Pull a compact-JSON string field out of one NDJSON line.
fn ndjson_string(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\":\"");
    let start = line.find(&needle)? + needle.len();
    Some(line[start..].chars().take_while(|c| *c != '"').collect())
}

/// Run the probe and read back its run record.
///
/// A run that could not be addressed or read is returned as `inconclusive` rather than
/// panicking, so the judgement below owns every reason token and the mutants can drive
/// that arm too.
fn run_isolation_probe(script: &Path) -> ProbeRun {
    let run = std::process::Command::new("bash")
        .arg(script)
        .output()
        .unwrap_or_else(|error| panic!("{} must be launchable: {error}", script.display()));
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&run.stderr).into_owned();
    let mut probe = ProbeRun {
        exit: run.status.code(),
        outcomes: Vec::new(),
        verdict: "inconclusive".to_owned(),
        reason: String::new(),
        stderr,
    };

    // stdout is data-only and carries exactly the artifact directory. Without it there is
    // no run record to read, which is a probe that cannot be checked, not a clean one.
    let Some(art_dir) = stdout
        .lines()
        .next()
        .map(str::trim)
        .filter(|d| !d.is_empty())
    else {
        probe.reason = "artifact_directory_unclaimed".to_owned();
        return probe;
    };
    let Ok(record) = fs::read_to_string(Path::new(art_dir).join("run.ndjson")) else {
        probe.reason = "run_record_unreadable".to_owned();
        return probe;
    };

    for line in record.lines() {
        match ndjson_string(line, "event").as_deref() {
            Some("probe") => {
                let name = ndjson_string(line, "name").unwrap_or_default();
                probe.outcomes.push((name, line.contains("\"pass\":true")));
            }
            Some("run_end") => {
                probe.verdict = ndjson_string(line, "verdict").unwrap_or_default();
                probe.reason = ndjson_string(line, "reason").unwrap_or_default();
            }
            _ => {}
        }
    }
    probe
}

/// Every outcome the verification manifest attributes to the probe, derived from the file.
///
/// Scope comes from the manifest rather than from a list here, so a row that starts citing
/// the probe is bound without anyone remembering to add it — the `fln-guard-scope-must-be-
/// derived` rule. Citations carry an optional ` -> OBSERVATION` suffix; the outcome name is
/// what the probe emits and what can be compared.
fn cited_probe_outcomes(manifest: &str) -> Vec<String> {
    let needle = format!("{ISOLATION_PROBE}: ");
    let mut cited: Vec<String> = Vec::new();
    let mut rest = manifest;
    while let Some(at) = rest.find(&needle) {
        rest = &rest[at + needle.len()..];
        let citation: String = rest.chars().take_while(|c| *c != '"').collect();
        let outcome = citation
            .split(" -> ")
            .next()
            .unwrap_or_default()
            .trim()
            .to_owned();
        if !outcome.is_empty() {
            cited.push(outcome);
        }
    }
    cited.sort();
    cited.dedup();
    cited
}

/// The probe exists to establish two directions, and only those two carry the claim.
///
/// `isolated_run_reports_the_flag` is deliberately outside this set: the probe's own header
/// and the coverage row's behaviour note both say the flag is not the evidence, so binding
/// the row to it would re-admit the thing the probe was written to replace.
fn is_load_bearing_outcome(name: &str) -> bool {
    name.ends_with("_reproduces_while_unprotected") || name.ends_with("_refused_under_isolation")
}

/// The whole judgement, in one place a forged caller can drive.
///
/// Each arm returns a distinct reason token so a mutant can be required to die *for its
/// stated reason*, and the ordering is load-bearing: a per-check failure is reported before
/// the run-level verdict, or a broken negative control and a broken refusal would be
/// indistinguishable at `probe-verdict:fail`.
fn judge_isolation_probe(cited: &[String], run: &ProbeRun) -> Result<(), String> {
    // (0) The scan's own anti-vacuity. A manifest citing nothing makes every arm below
    // quantify over the empty set and report a clean sweep.
    if cited.is_empty() {
        return Err("no-row-cites-the-probe".to_owned());
    }
    // (1) "We could not look" is not "we looked and found nothing" (FL-INV-07). This is
    // refused, and refused as *inconclusive* — never rendered as a refutation of the
    // isolation, which is a claim no failed setup can support.
    if run.verdict == "inconclusive" || run.outcomes.is_empty() {
        let reason = if run.reason.is_empty() {
            "no_outcomes_recorded"
        } else {
            run.reason.as_str()
        };
        return Err(format!("probe-setup-inconclusive:{reason}"));
    }
    // (2) Every check the probe ran, including the two negative controls. A hijack that
    // stopped reproducing dies here, which is the arm that keeps the isolated half from
    // being a pass with no content.
    for (name, passed) in &run.outcomes {
        if !passed {
            return Err(format!("probe-check-failed:{name}"));
        }
    }
    let mut produced: Vec<String> = run
        .outcomes
        .iter()
        .map(|(name, _)| name.clone())
        .filter(|name| is_load_bearing_outcome(name))
        .collect();
    produced.sort();
    produced.dedup();
    // (3) Both directions must be present. A probe reduced to refusals alone never
    // reproduces the attack, and one reduced to reproductions alone never refuses it;
    // either reads as five green checks.
    if !produced
        .iter()
        .any(|name| name.ends_with("_reproduces_while_unprotected"))
    {
        return Err("probe-has-no-negative-control".to_owned());
    }
    if !produced
        .iter()
        .any(|name| name.ends_with("_refused_under_isolation"))
    {
        return Err("probe-has-no-isolated-refusal".to_owned());
    }
    // (4)/(5) Equality, both directions. A citation the probe no longer produces is a
    // claim with no producer; an outcome nothing cites is a direction the manifest stopped
    // disclosing. Neither is a floor: this is a disclosure of a measured population, and
    // one-way-plus-remainder would let it drift on the unwatched side.
    for outcome in cited {
        if !produced.contains(outcome) {
            return Err(format!("cited-outcome-not-produced:{outcome}"));
        }
    }
    for outcome in &produced {
        if !cited.contains(outcome) {
            return Err(format!("produced-outcome-not-cited:{outcome}"));
        }
    }
    // (6) The run's own verdict and status, last, so they cannot mask a named check.
    if run.verdict != "pass" {
        return Err(format!("probe-verdict:{}", run.verdict));
    }
    if run.exit != Some(0) {
        return Err(format!("probe-exit:{:?}", run.exit));
    }
    Ok(())
}

/// The interpreter-isolation probe **runs**, and every outcome the manifest attributes to
/// it is one this run produced.
///
/// `every_python_launch_under_scripts_is_sealed` above ends by saying that it "does not
/// observe a single interpreter actually start: that is
/// `scripts/tribunal/python_isolation_probe.sh`'s job, and asserting `-I` is set is not
/// evidence that `-I` works." Measured at `94fa9e7e`, that job was delegated to a script
/// **nothing ran**: the probe appeared in `.beads/issues.jsonl`, in
/// `ci/VERIFICATION_MANIFEST.jsonl`, and in this file's `UNSEALED_LAUNCH_ALLOWANCE` — which
/// declares an exemption *for* it — and in no runnable surface at all. Not `scripts/check.sh`,
/// not `.github/workflows/ci.yml`, not a lane. `franken_lean-h40t`'s coverage row cites four
/// of its outcomes across `boundary` and `error`; all four were one hand-run, recorded.
///
/// That is `franken_lean-pnav`'s row in AGENTS.md item 7 — an assertion and the lane it
/// delegates to — reproduced inside the guard whose own doc comment states the delegation,
/// and `franken_lean-worktree-gitdir-refusal-hugg`'s lesson in its general form: where a
/// claim rests on a run, check that the run *happened*.
///
/// So the flag half and the behaviour half now both execute per commit, and the join
/// between the row and the probe is walked in **both** directions. A citation the probe
/// stopped producing fails; an outcome no row cites fails; a negative control that stops
/// reproducing the hijack fails; a run that could not be established is refused as
/// inconclusive rather than counted clean.
///
/// **What this does not earn.** The probe is a bounded model — two vectors, one host, one
/// CPython — and running it per commit does not widen it: an opaque `PYTHONHOME`, a
/// `sitecustomize`, or a shadow module reached through some path neither vector plants are
/// all outside it, and `-I` closing those is untested here. It says nothing about whether
/// `scripts/evidence.py` is *launched* sealed; that is the scanner above. And the two
/// halves share no code, so a future third vector must be added to both the probe and a
/// citation or the equality refuses it — deliberately, since the alternative is a probe
/// that grows silently.
///
/// Cost: 0.16 s and 5.1 KB per run, written under the gitignored `target/e2e/`. Disclosed
/// because the last guard in this file to write per-run artifacts put 4.3 MB a run into a
/// machine-wide shared target directory before anyone measured it.
#[test]
fn the_interpreter_isolation_probe_runs_and_produces_every_outcome_cited_for_it() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let manifest = fs::read_to_string(repo.join("ci/VERIFICATION_MANIFEST.jsonl"))
        .expect("ci/VERIFICATION_MANIFEST.jsonl must be readable");
    let cited = cited_probe_outcomes(&manifest);
    let run = run_isolation_probe(&repo.join(ISOLATION_PROBE));

    if let Err(reason) = judge_isolation_probe(&cited, &run) {
        panic!(
            "the interpreter-isolation evidence is not bound to a run that produced it \
             ({reason}). `-I -S` is the only thing standing between an ambient PYTHONPATH \
             and the module that computes the governed digests, and the flag being present \
             in an argv is not evidence that it shuts the channel (franken_lean-h40t). \
             cited={cited:?} produced={:?} verdict={:?} exit={:?}\n--- probe stderr ---\n{}",
            run.outcomes, run.verdict, run.exit, run.stderr
        );
    }
}

/// Every arm of the judgement above kills a mutation, and each dies for its own reason.
///
/// The base run is **forged from the manifest's own citations** rather than written down,
/// so it cannot drift away from the population the real test judges, and nothing is
/// mutated on disk: a campaign that edits a shared file cannot be re-run by the next
/// reader, and this one has to survive six panes editing the tree around it.
///
/// Two of the mutants are the same violation from opposite sides — a produced outcome
/// nobody cites, and a citation removed from the row — and both are kept, because that is
/// what "equality in both directions" means and a one-sided check would pass one of them.
#[test]
fn the_interpreter_isolation_binding_kills_each_mutation_it_claims_to() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let manifest = fs::read_to_string(repo.join("ci/VERIFICATION_MANIFEST.jsonl"))
        .expect("ci/VERIFICATION_MANIFEST.jsonl must be readable");
    let cited = cited_probe_outcomes(&manifest);

    // The unmutated control, judged first. If the base were already refused, every mutant
    // below would "die" on the same arm and this whole test would be theatre.
    let base = ProbeRun {
        exit: Some(0),
        outcomes: cited.iter().map(|name| (name.clone(), true)).collect(),
        verdict: "pass".to_owned(),
        reason: String::new(),
        stderr: String::new(),
    };
    assert_eq!(
        judge_isolation_probe(&cited, &base),
        Ok(()),
        "the unmutated binding must hold, or the mutants below prove nothing about the \
         mutations and everything about a broken baseline. cited={cited:?}"
    );

    let reproduces = cited
        .iter()
        .find(|name| name.ends_with("_reproduces_while_unprotected"))
        .expect("the manifest must cite at least one negative control")
        .clone();
    let refuses = cited
        .iter()
        .find(|name| name.ends_with("_refused_under_isolation"))
        .expect("the manifest must cite at least one isolated refusal")
        .clone();

    let flip = |target: &str| -> ProbeRun {
        ProbeRun {
            outcomes: base
                .outcomes
                .iter()
                .map(|(name, passed)| (name.clone(), *passed && name != target))
                .collect(),
            verdict: "fail".to_owned(),
            exit: Some(1),
            reason: String::new(),
            stderr: String::new(),
        }
    };
    let without = |target: &str| -> ProbeRun {
        ProbeRun {
            outcomes: base
                .outcomes
                .iter()
                .filter(|(name, _)| name != target)
                .cloned()
                .collect(),
            verdict: "pass".to_owned(),
            exit: Some(0),
            reason: String::new(),
            stderr: String::new(),
        }
    };
    let with_extra = |extra: &str| -> ProbeRun {
        let mut outcomes = base.outcomes.clone();
        outcomes.push((extra.to_owned(), true));
        ProbeRun {
            outcomes,
            verdict: "pass".to_owned(),
            exit: Some(0),
            reason: String::new(),
            stderr: String::new(),
        }
    };

    let renamed: Vec<(String, bool)> = base
        .outcomes
        .iter()
        .map(|(name, passed)| (format!("{name}_note"), *passed))
        .collect();

    // (mutant, cited set, run, the reason the guard must give)
    let mutants: Vec<(&str, Vec<String>, ProbeRun, String)> = vec![
        (
            "negative-control-did-not-reproduce",
            cited.clone(),
            flip(&reproduces),
            format!("probe-check-failed:{reproduces}"),
        ),
        (
            "isolation-did-not-refuse",
            cited.clone(),
            flip(&refuses),
            format!("probe-check-failed:{refuses}"),
        ),
        (
            "outcome-dropped-from-the-probe",
            cited.clone(),
            without(&refuses),
            format!("cited-outcome-not-produced:{refuses}"),
        ),
        (
            "outcome-added-without-a-citation",
            cited.clone(),
            with_extra("stdin_vector_refused_under_isolation"),
            "produced-outcome-not-cited:stdin_vector_refused_under_isolation".to_owned(),
        ),
        (
            "citation-removed-from-the-row",
            cited
                .iter()
                .filter(|name| **name != refuses)
                .cloned()
                .collect(),
            ProbeRun {
                outcomes: base.outcomes.clone(),
                verdict: "pass".to_owned(),
                exit: Some(0),
                reason: String::new(),
                stderr: String::new(),
            },
            format!("produced-outcome-not-cited:{refuses}"),
        ),
        (
            "probe-produced-nothing",
            cited.clone(),
            ProbeRun {
                outcomes: Vec::new(),
                verdict: "pass".to_owned(),
                exit: Some(0),
                reason: String::new(),
                stderr: String::new(),
            },
            "probe-setup-inconclusive:no_outcomes_recorded".to_owned(),
        ),
        (
            "probe-could-not-be-established",
            cited.clone(),
            ProbeRun {
                outcomes: Vec::new(),
                verdict: "inconclusive".to_owned(),
                exit: Some(2),
                reason: "python3_absent".to_owned(),
                stderr: String::new(),
            },
            "probe-setup-inconclusive:python3_absent".to_owned(),
        ),
        (
            "nothing-cites-the-probe",
            Vec::new(),
            ProbeRun {
                outcomes: base.outcomes.clone(),
                verdict: "pass".to_owned(),
                exit: Some(0),
                reason: String::new(),
                stderr: String::new(),
            },
            "no-row-cites-the-probe".to_owned(),
        ),
        (
            "no-outcome-carries-a-direction",
            cited.clone(),
            ProbeRun {
                outcomes: renamed,
                verdict: "pass".to_owned(),
                exit: Some(0),
                reason: String::new(),
                stderr: String::new(),
            },
            "probe-has-no-negative-control".to_owned(),
        ),
        (
            "run-failed-while-every-named-check-passed",
            cited.clone(),
            ProbeRun {
                outcomes: base.outcomes.clone(),
                verdict: "fail".to_owned(),
                exit: Some(1),
                reason: String::new(),
                stderr: String::new(),
            },
            "probe-verdict:fail".to_owned(),
        ),
    ];

    for (name, mutant_cited, mutant_run, expected_reason) in &mutants {
        // A mutant that does not create the condition it claims is not evidence of a hole.
        let moved = *mutant_cited != cited
            || mutant_run.outcomes != base.outcomes
            || mutant_run.verdict != base.verdict
            || mutant_run.exit != base.exit;
        assert!(
            moved,
            "mutant {name} is identical to the unmutated base, so it did not apply and \
             scoring it proves nothing"
        );
        let verdict = judge_isolation_probe(mutant_cited, mutant_run);
        assert_eq!(
            verdict.as_ref().map_err(String::as_str),
            Err(expected_reason.as_str()),
            "mutant {name} was not killed for its stated reason. A rig that accepted any \
             failure would score a mutant killed by an arm that had stopped testing the \
             property"
        );
    }

    // The citation side is PARSED, and driving the judgement over a forged vector proves
    // only that the comparison discriminates — never that the scan reads the manifest. A
    // scan whose needle had gone stale would return an empty set and be caught by
    // `no-row-cites-the-probe`; a scan that silently dropped the ` -> OBSERVATION` suffix
    // would return names that match nothing and read as a manifest problem. So the parser
    // is mutated too, over an **in-memory copy**, because writing a tracked file while a
    // lane runs can end it. Which mechanism it would trip is per-lane and not derivable
    // from the path: `e8be303c` parsed all 21 lanes in `scripts/e2e/` and found eight
    // declaring a governed set and thirteen declaring none — those thirteen cannot raise
    // M2/M3/M4 under any write and rest on M1 alone — while `verdict_schema.sh` governs
    // bare `scripts`, so any write anywhere beneath it voids that lane. Do not reason from
    // a path to a mechanism without reading that lane's own `INPUT_PATHS`; the safe rule
    // during a park is that the whole repository is frozen.
    assert!(
        cited.iter().all(|name| !name.contains(" -> ")),
        "a citation's observation suffix survived into the outcome name, so no cited name \
         can ever match one the probe emits: {cited:?}"
    );
    assert!(
        manifest.contains(&format!("{ISOLATION_PROBE}: {reproduces} -> ")),
        "the manifest no longer carries a suffixed citation, so the assertion above that \
         suffixes are stripped is quantifying over a case that is not present"
    );
    let withdrawn = manifest.replace(
        &format!("{ISOLATION_PROBE}: {refuses}"),
        &format!("{ISOLATION_PROBE}: withdrawn"),
    );
    assert_ne!(
        withdrawn, manifest,
        "the citation mutation did not apply, so the parser was never exercised"
    );
    let reparsed = cited_probe_outcomes(&withdrawn);
    assert!(
        !reparsed.contains(&refuses) && reparsed.iter().any(|name| name == "withdrawn"),
        "cited_probe_outcomes did not track a mutated manifest, so its result does not \
         come from the file it claims to read: {reparsed:?}"
    );
    assert_eq!(
        judge_isolation_probe(&reparsed, &base)
            .as_ref()
            .map_err(String::as_str),
        Err("cited-outcome-not-produced:withdrawn"),
        "a citation naming an outcome no probe emits was accepted"
    );
}

/// The file-stability family in the evidence runner, derived from its own definitions.
///
/// This is the family that actually grew. `stable_file_facts` `fstat`s a governed file before
/// and after reading it; `stable_symlink_facts` is its sibling for a governed symlink and
/// `lstat`s instead, hashing the link *target string* — so retargeting a symlink moves the
/// governed root with no content edited anywhere. A future `stable_dir_facts` would be a sixth
/// mechanism arriving the same way this fifth one did: as a new sibling, silently.
fn stability_family(evidence: &str) -> Vec<String> {
    let mut family: Vec<String> = evidence
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("def "))
        .filter_map(|rest| rest.split('(').next())
        .filter(|name| name.starts_with("stable_") && name.ends_with("_facts"))
        .map(str::to_owned)
        .collect();
    family.sort();
    family.dedup();
    family
}

/// The Build Gate section, cut at the next top-level heading.
fn build_gate_section(agents: &str) -> &str {
    let start = agents
        .find("## The Build Gate")
        .expect("AGENTS.md must keep the Build Gate section");
    let section = &agents[start..];
    match section[3..].find("\n## ") {
        Some(end) => &section[..end + 3],
        None => section,
    }
}

/// The mechanism rows, as `(id, row text)`.
fn mechanism_rows(section: &str) -> Vec<(String, String)> {
    section
        .lines()
        .filter(|line| line.trim_start().starts_with("| **M"))
        .filter_map(|line| {
            let rest = line.trim_start().strip_prefix("| **")?;
            let id = rest.split("**").next()?.to_owned();
            Some((id, line.to_owned()))
        })
        .collect()
}

/// The headline's spelled-out count. A lexicon, not a scope: it maps words to numbers and has
/// nothing to derive.
fn headline_mechanism_count(section: &str) -> Option<usize> {
    let marker = "** checks can end a lane";
    let at = section.find(marker)?;
    let word = section[..at]
        .rsplit("**")
        .next()?
        .trim()
        .to_ascii_lowercase();
    [
        "zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
    ]
    .iter()
    .position(|spelled| *spelled == word)
}

/// Backticked snake_case tokens in a table row that could name a producer.
fn cited_symbols(row: &str) -> Vec<String> {
    row.split('`')
        .skip(1)
        .step_by(2)
        .map(|token| token.trim_end_matches("()").trim())
        .filter(|token| {
            token.len() > 3
                && !token.contains(' ')
                && token
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c == '_' || c.is_ascii_digit())
        })
        .map(str::to_owned)
        .collect()
}

/// One forged Build Gate reading, so the mutant table below is a list of named cases rather
/// than a tuple nobody can read.
struct BuildGateMutant {
    name: &'static str,
    family: Vec<String>,
    rows: Vec<(String, String)>,
    headline: Option<usize>,
    expected: &'static str,
}

/// The whole judgement, in one place a forged caller can drive.
fn judge_build_gate(
    family: &[String],
    rows: &[(String, String)],
    headline: Option<usize>,
    producers: &str,
) -> Result<(), String> {
    // (0)/(1) A scan that finds nothing is a broken scan, never a clean tree. Both sides are
    // derived, so both can silently derive nothing when a definition style or a table format
    // moves — and an empty set makes every arm below quantify over nothing.
    if family.is_empty() {
        return Err("stability-family-scan-empty".to_owned());
    }
    // A scan that narrows from two members to one is NOT caught by anything above: arm 4
    // quantifies over the family, so a shorter family satisfies it trivially, and the vanished
    // member's row still cites a symbol that is still in the corpus. Measured — planted as a
    // mutant and it was ACCEPTED. So a floor, in the same shape and for the same reason as
    // `every_python_launch_under_scripts_is_sealed`'s: a truncated derived scope reads as
    // coverage. If the family legitimately shrinks, this reddens and its author lowers the
    // floor deliberately, which is the disclosure the number exists to force.
    if family.len() < 2 {
        return Err(format!("stability-family-scan-truncated:{}", family.len()));
    }
    if rows.len() < 2 {
        return Err("mechanism-table-scan-empty".to_owned());
    }
    // (2)/(3) The headline count is the sentence that has now been wrong twice. Binding it to
    // the number of rows is what stops a third hand-transcription: a row added without moving
    // the word, or a word moved without adding the row, both fail.
    let Some(headline) = headline else {
        return Err("headline-count-unreadable".to_owned());
    };
    if headline != rows.len() {
        return Err(format!(
            "headline-count-disagrees-with-table:{headline}-vs-{}",
            rows.len()
        ));
    }
    // (4) code -> table. A new sibling in the stability family that no row names is exactly how
    // the fifth mechanism arrived, and exactly what nothing noticed.
    for member in family {
        if !rows.iter().any(|(_, row)| row.contains(member.as_str())) {
            return Err(format!("mechanism-not-in-table:{member}"));
        }
    }
    // (5) table -> code. A row whose every cited producer has been renamed away is a claim with
    // nothing behind it, which is the shape this whole section is about.
    for (id, row) in rows {
        let symbols = cited_symbols(row);
        if symbols.is_empty() {
            return Err(format!("row-cites-no-symbol:{id}"));
        }
        if !symbols
            .iter()
            .any(|symbol| producers.contains(symbol.as_str()))
        {
            return Err(format!("row-cites-no-live-symbol:{id}"));
        }
    }
    Ok(())
}

/// AGENTS.md's Build Gate table names every freeze mechanism the code actually has.
///
/// **This sentence has been wrong twice, and the second time was the repair of the first.**
/// It first said the freeze "asserts that the whole repository held still" (false: M1's content
/// check is scoped to the pinned Reference tree). The correction replaced it with "**Four**
/// checks can end a lane" — a hand-transcribed count, which rotted on exactly the schedule the
/// claim it replaced did, because `stable_symlink_facts` was added as a sibling of
/// `stable_file_facts` and nothing anywhere compared the table against the code
/// (`franken_lean-pfei` instance six; measured by cc_1 in `76298969`).
///
/// So the count is no longer transcribed: it is bound to the number of rows, and the rows are
/// bound to the code in **both** directions. A sixth mechanism arriving as another
/// `stable_*_facts` sibling now reddens the build until the table names it; a row whose
/// producer was renamed away reddens too; and either side deriving *nothing* is refused as a
/// broken scan rather than reported as agreement.
///
/// **What it does not earn, and this is the honest limit.** The derived family is the
/// `stable_*_facts` one only — the family that grew. M1, M2 and M3 are still recognised by the
/// symbols their rows cite, so a genuinely new mechanism of a *different* shape (a fresh
/// `repository_state` sampler, a new `require_unchanged` call site in a lane) is not derived
/// and would not be caught. That is a narrower claim than "the table is complete", and it is
/// the claim this test makes. Widening it is `98np` R4's job, not this guard's.
///
/// Unlike `fln-8zsq`'s guard, this one's own text is **not** in its search space: it scans
/// `scripts/evidence.py` and AGENTS.md, never this file. No self-exclusion is needed, and none
/// is present — a reader checking for one should stop here rather than conclude it was missed.
#[test]
fn the_build_gate_table_names_every_freeze_mechanism_in_the_code() {
    let repo = fln_conformance::checked_workspace_root!();
    let evidence = trusted_script("scripts/evidence.py");
    // The producer corpus is the whole of `scripts/`, walked, not a list of the two files that
    // happen to hold M1 and M2. Written as a hand-list first and it was already wrong: M3's
    // `require_unchanged` lives in the lane scripts, so the guard refused a correct table with
    // `row-cites-no-live-symbol:M3`. That is `fln-guard-scope-must-be-derived` reproduced inside
    // a guard written to stop claims drifting from their producers, caught only because the
    // wrong scope happened to fail loudly rather than quietly agreeing.
    let producers = {
        let root = repo
            .canonicalize()
            .expect("the repository root must resolve");
        let mut files = Vec::new();
        scripts_tree(&root.join("scripts"), &mut files, &root);
        files
            .into_iter()
            .map(|(_, body)| body)
            .collect::<Vec<_>>()
            .join("\n")
    };
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let section = build_gate_section(&agents);

    let family = stability_family(&evidence);
    let rows = mechanism_rows(section);
    let headline = headline_mechanism_count(section);

    if let Err(reason) = judge_build_gate(&family, &rows, headline, &producers) {
        panic!(
            "the Build Gate table no longer matches the code it describes ({reason}). Six panes \
             read this section at session start to decide what is safe to do mid-lane, and a \
             mechanism it omits is one nobody defends against — the last omission cost two \
             lanes (franken_lean-pfei, franken_lean-build-gate-lane-governed-set-98np). \
             derived_family={family:?} table_rows={:?} headline={headline:?}",
            rows.iter().map(|(id, _)| id).collect::<Vec<_>>()
        );
    }
}

/// Every arm above kills a mutation, including a planted decoy proving the scan is not vacuous.
///
/// The decoy is the arm that matters. Arms 4 and 5 compare two derived sets, and two scans that
/// both silently return nothing agree perfectly — so a guard built only from the real tree can
/// pass while measuring neither side. A sixth mechanism is therefore *planted* into an in-memory
/// copy of the runner, and the guard is required to notice it is absent from the table.
#[test]
fn the_build_gate_guard_kills_each_mutation_it_claims_to() {
    let repo = fln_conformance::checked_workspace_root!();
    let evidence = trusted_script("scripts/evidence.py");
    // The producer corpus is the whole of `scripts/`, walked, not a list of the two files that
    // happen to hold M1 and M2. Written as a hand-list first and it was already wrong: M3's
    // `require_unchanged` lives in the lane scripts, so the guard refused a correct table with
    // `row-cites-no-live-symbol:M3`. That is `fln-guard-scope-must-be-derived` reproduced inside
    // a guard written to stop claims drifting from their producers, caught only because the
    // wrong scope happened to fail loudly rather than quietly agreeing.
    let producers = {
        let root = repo
            .canonicalize()
            .expect("the repository root must resolve");
        let mut files = Vec::new();
        scripts_tree(&root.join("scripts"), &mut files, &root);
        files
            .into_iter()
            .map(|(_, body)| body)
            .collect::<Vec<_>>()
            .join("\n")
    };
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let section = build_gate_section(&agents).to_owned();

    let family = stability_family(&evidence);
    let rows = mechanism_rows(&section);
    let headline = headline_mechanism_count(&section);

    // The unmutated control, judged first, or every mutant below dies on a broken baseline.
    assert_eq!(
        judge_build_gate(&family, &rows, headline, &producers),
        Ok(()),
        "the unmutated Build Gate binding must hold. family={family:?} rows={} headline={headline:?}",
        rows.len()
    );

    // THE DECOY. A sixth mechanism planted in the runner, absent from the table.
    let decoyed = format!("{evidence}\ndef stable_decoy_facts(path):\n    return ()\n");
    let grown = stability_family(&decoyed);
    assert!(
        grown.len() == family.len() + 1 && grown.iter().any(|n| n == "stable_decoy_facts"),
        "the planted decoy did not enter the derived family, so this scan does not read \
         definitions and every agreement it reports is between two empty sets: {grown:?}"
    );
    assert_eq!(
        judge_build_gate(&grown, &rows, headline, &producers)
            .as_ref()
            .map_err(String::as_str),
        Err("mechanism-not-in-table:stable_decoy_facts"),
        "a mechanism present in the code and absent from the table was accepted — which is \
         precisely the state this section was in for two days"
    );

    let dropped: Vec<String> = family.iter().skip(1).cloned().collect();
    let extra_row = {
        let mut grown_rows = rows.clone();
        grown_rows.push((
            "M9".to_owned(),
            "| **M9** | `repository_state` |".to_owned(),
        ));
        grown_rows
    };
    let dead_row = {
        let mut bad = rows.clone();
        bad.push((
            "M9".to_owned(),
            "| **M9** | `a_producer_that_was_renamed_away` |".to_owned(),
        ));
        bad
    };

    let mutants: Vec<BuildGateMutant> = vec![
        BuildGateMutant {
            name: "family-scan-returns-nothing",
            family: Vec::new(),
            rows: rows.clone(),
            headline,
            expected: "stability-family-scan-empty",
        },
        BuildGateMutant {
            name: "table-scan-returns-nothing",
            family: family.clone(),
            rows: Vec::new(),
            headline,
            expected: "mechanism-table-scan-empty",
        },
        BuildGateMutant {
            name: "headline-word-unreadable",
            family: family.clone(),
            rows: rows.clone(),
            headline: None,
            expected: "headline-count-unreadable",
        },
        BuildGateMutant {
            name: "row-added-without-moving-the-headline",
            family: family.clone(),
            rows: extra_row,
            headline,
            expected: "headline-count-disagrees-with-table",
        },
        // This one was ACCEPTED before the truncation floor existed, and it is the mutant worth
        // reading: it models the family scan silently narrowing, which every other arm agrees
        // with perfectly because both sides shrink together.
        BuildGateMutant {
            name: "mechanism-dropped-from-the-derived-family",
            family: dropped,
            rows: rows.clone(),
            headline,
            expected: "stability-family-scan-truncated:1",
        },
        BuildGateMutant {
            name: "row-whose-producer-was-renamed-away",
            family: family.clone(),
            rows: dead_row,
            headline: headline.map(|n| n + 1),
            expected: "row-cites-no-live-symbol:M9",
        },
    ];

    for mutant in &mutants {
        let moved = mutant.family != family || mutant.rows != rows || mutant.headline != headline;
        assert!(
            moved,
            "mutant {} is identical to the unmutated base, so it did not apply",
            mutant.name
        );
        let verdict = judge_build_gate(&mutant.family, &mutant.rows, mutant.headline, &producers);
        let reason = verdict
            .as_ref()
            .err()
            .map(String::as_str)
            .unwrap_or("<accepted>");
        assert!(
            reason.starts_with(mutant.expected),
            "mutant {} was not killed for its stated reason: expected {:?}, got {reason:?}. A \
             rig accepting any failure would score a mutant killed by an arm that had stopped \
             testing the property",
            mutant.name,
            mutant.expected
        );
    }
}

// ---------------------------------------------------------------------------------------
// The worktree-refusal SCOPE, derived rather than listed
// (bead `franken_lean-worktree-gitdir-refusal-hugg`).
//
// The sibling guard above proves the refusal FIRES and that AGENTS.md still names the
// surfaces it takes down. AGENTS.md's own "what it does not earn" says what that leaves
// open, in its own words: "the affected-surface list is written down, not derived — so a
// *new* lane that starts refusing would go unnamed and nothing would notice."
//
// **Static reachability is provably wrong for deriving the affected set, and is used here
// only to prove a NEGATIVE.** Fifteen of `evidence.py`'s 45 subcommands have handlers that
// reach `run_git`, and `hash-tree` is one of them yet exits 0 without `--vendor-path`
// (cc_2, measured at `115ef2fd` against a main-tree positive control). So reachability
// cannot say a lane dies. What it CAN say soundly is the contrapositive: a handler that
// never reaches `run_git` cannot possibly raise the refusal. That asymmetry is the whole
// design — a positive verdict needs a MEASURED invocation shape, a negative verdict may
// rest on the walk, and anything else is `Indeterminate` and named.
// ---------------------------------------------------------------------------------------

/// Whether the evidence surface refuses inside a linked worktree, for one lane script.
#[derive(Debug, Clone, PartialEq, Eq)]
enum LaneWorktreeVerdict {
    /// A measured refusing invocation shape is present. The witness is named, because
    /// "this lane refuses" and "this lane refuses BECAUSE of X" are different claims and
    /// AGENTS.md was asserting the second while only the first had been measured.
    Refuses(&'static str),
    /// Every subcommand it invokes is proven unable to reach `run_git`.
    Runs,
    /// It invokes subcommands that CAN reach `run_git` in shapes nobody has measured.
    /// **Not "clean" — unknown.** Reported with the names, so the next reader measures
    /// those instead of re-deriving the question.
    Indeterminate(Vec<String>),
}

/// The invocation shapes measured to refuse, each with the anchor it was measured at.
///
/// Declared as data rather than derived, because the refusal is ARGUMENT-gated and no call
/// graph can see that: `hash-tree` refuses with `--vendor-path` and succeeds without it.
/// A shape may be added here only with a measurement, never with an argument.
const MEASURED_REFUSING_SHAPES: &[(&str, &str)] = &[
    // Unconditional: the handler hashes the pinned Reference tree through git.
    // cc_2 at `115ef2fd`, worktree vs main-tree control.
    ("vendor-binding", "vendor-binding"),
    // Unconditional: enumerates tracked inputs via `git ls-files`. Same measurement, and
    // it is the invocation the sibling guard above probes directly.
    ("ubs-inventory", "ubs-inventory"),
];

/// `hash-tree` is the counterexample that makes static derivation unsafe, so it is named
/// once, here, and keyed on its flag rather than on the subcommand.
const VENDOR_PATH_FLAG: &str = "--vendor-path";

/// Top-level `def` blocks of a Python source, in file order.
fn python_def_blocks(source: &str) -> std::collections::BTreeMap<String, String> {
    let lines: Vec<&str> = source.lines().collect();
    let starts: Vec<(usize, String)> = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| {
            let rest = line.strip_prefix("def ")?;
            let name: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            (!name.is_empty() && rest[name.len()..].starts_with('(')).then_some((index, name))
        })
        .collect();
    let mut blocks = std::collections::BTreeMap::new();
    for (position, (index, name)) in starts.iter().enumerate() {
        let end = starts
            .get(position + 1)
            .map(|(next, _)| *next)
            .unwrap_or(lines.len());
        blocks.insert(name.clone(), lines[*index..end].join("\n"));
    }
    blocks
}

/// Every top-level function that can reach `run_git`, transitively.
///
/// Over-approximating is the correct direction: a false "reaches" only makes a lane
/// `Indeterminate`, which asks for a measurement. A false "cannot reach" would silently
/// call a refusing lane clean, so the walk closes to a fixpoint rather than one hop.
fn defs_reaching_run_git(source: &str) -> std::collections::BTreeSet<String> {
    let blocks = python_def_blocks(source);
    let mut reaching: std::collections::BTreeSet<String> = blocks
        .iter()
        .filter(|(_, body)| body.contains("run_git("))
        .map(|(name, _)| name.clone())
        .collect();
    let calls: std::collections::BTreeMap<&String, std::collections::BTreeSet<&String>> = blocks
        .iter()
        .map(|(name, body)| {
            let called = blocks
                .keys()
                .filter(|candidate| *candidate != name && body.contains(&format!("{candidate}(")))
                .collect();
            (name, called)
        })
        .collect();
    loop {
        let mut grew = false;
        for (name, called) in &calls {
            if !reaching.contains(*name) && called.iter().any(|c| reaching.contains(*c)) {
                reaching.insert((*name).clone());
                grew = true;
            }
        }
        if !grew {
            return reaching;
        }
    }
}

/// Classify one lane script.
fn classify_lane(
    text: &str,
    subcommands: &std::collections::BTreeSet<String>,
    reaching: &std::collections::BTreeSet<String>,
) -> LaneWorktreeVerdict {
    for (needle, witness) in MEASURED_REFUSING_SHAPES {
        if text.contains(needle) {
            return LaneWorktreeVerdict::Refuses(witness);
        }
    }
    let invoked: std::collections::BTreeSet<&String> = subcommands
        .iter()
        .filter(|name| text.contains(name.as_str()))
        .collect();
    if invoked.iter().any(|name| *name == "hash-tree") && text.contains(VENDOR_PATH_FLAG) {
        return LaneWorktreeVerdict::Refuses("hash-tree --vendor-path");
    }
    let unresolved: Vec<String> = invoked
        .iter()
        // `hash-tree` without `--vendor-path` is MEASURED to exit 0, so it is resolved
        // rather than unknown — the one place a reaching subcommand is excused, and it is
        // excused by a measurement.
        .filter(|name| reaching.contains(**name) && name.as_str() != "hash-tree")
        .map(|name| (*name).clone())
        .collect();
    if unresolved.is_empty() {
        LaneWorktreeVerdict::Runs
    } else {
        LaneWorktreeVerdict::Indeterminate(unresolved)
    }
}

/// The set of surfaces a linked worktree takes down is DERIVED, and AGENTS.md's counts
/// match it in both directions.
///
/// **What this changes about the row it binds.** AGENTS.md said `any fln.e2e/2 lane —
/// **no** — hash-tree --vendor-path is its first governed step`: a universal verdict with a
/// single stated producer. The verdict survives measurement; the producer does not. Of the
/// eleven declared `fln.e2e/2` lanes, ten carry `vendor-binding`, and the eleventh —
/// `unsafe_note_clippy.sh` — carries no `--vendor-path` anywhere and reaches `run_git`, if
/// it does, through `emit --governed-path` / `--producer-binding-root` and
/// `manifest --input-root` instead. So the row was right for a reason that is wrong for at
/// least one member, which is item 7's shape: a claim whose stated producer is not the
/// thing producing it.
///
/// **I did not resolve that eleventh lane and this guard says so rather than guessing.** Its
/// distinctive subcommand IS measured — `unsafe-note-clippy-sites --operation extract`
/// exits 0 on a gitdir-pointer root with an empty report, against a real-`.git` control —
/// but six other subcommands it invokes reach `run_git` statically in unmeasured shapes.
/// A first pass here classified it `Runs` off a three-needle scan, and that was wrong in
/// exactly the way this bead's own row warns about; `Indeterminate` is the honest verdict
/// and it names the six.
#[test]
fn the_worktree_refusal_scope_is_derived_from_the_lane_population() {
    const LANE_FLOOR: usize = 20;
    const SUBCOMMAND_FLOOR: usize = 30;

    let repo = fln_conformance::checked_workspace_root!();
    let evidence = trusted_script("scripts/evidence.py");

    // --- the subcommand population, from the PARSER rather than from a regex ------------
    // `add_parser` calls span lines and one is registered from a loop variable, so a scan
    // of the source undercounts. The parser is the authority on what exists.
    let help = std::process::Command::new("python3")
        .args(["-I", "-S"])
        .arg(repo.join("scripts/evidence.py"))
        .arg("--help")
        .output()
        .expect("the evidence runner must be able to print its own help");
    let help = String::from_utf8_lossy(&help.stdout);
    let listing = help
        .split_once('{')
        .and_then(|(_, rest)| rest.split_once('}'))
        .map(|(names, _)| names)
        .expect("evidence.py --help must list its subcommands in {a,b,c} form");
    let subcommands: std::collections::BTreeSet<String> =
        listing.split(',').map(str::to_string).collect();
    assert!(
        subcommands.len() >= SUBCOMMAND_FLOOR,
        "the parser listed only {} subcommands, below the floor of {SUBCOMMAND_FLOOR}. A \
         short list is a broken extraction, not a small program — and it would make every \
         lane below classify as Runs",
        subcommands.len()
    );

    // --- subcommand -> handler, by the convention, refusing an exception ----------------
    let defs = python_def_blocks(&evidence);
    let unmapped: Vec<&String> = subcommands
        .iter()
        .filter(|name| !defs.contains_key(&format!("cmd_{}", name.replace('-', "_"))))
        .collect();
    assert!(
        unmapped.is_empty(),
        "these subcommands have no `cmd_<name>` handler, so their reachability cannot be \
         decided and they must not be silently treated as unable to reach git: {unmapped:?}"
    );

    let reaching_defs = defs_reaching_run_git(&evidence);
    let reaching: std::collections::BTreeSet<String> = subcommands
        .iter()
        .filter(|name| reaching_defs.contains(&format!("cmd_{}", name.replace('-', "_"))))
        .cloned()
        .collect();
    // Anti-vacuity, and it is the assertion that matters most. If the walk broke and
    // returned nothing, every lane would classify as `Runs`, the counts would agree with a
    // row saying nothing refuses, and this guard would be a confident false clean.
    assert!(
        reaching.contains("vendor-binding"),
        "the call walk did not find `vendor-binding` able to reach run_git, which is the \
         one invocation measured to refuse unconditionally. The walk is broken, and a \
         broken walk classifies every lane as running: {} subcommands judged reaching",
        reaching.len()
    );

    // --- the lane population, derived from git ------------------------------------------
    let listed = std::process::Command::new("git")
        .arg("-C")
        .arg(&repo)
        .args(["ls-files", "scripts/e2e/*.sh"])
        .output()
        .expect("git ls-files must run: the lane population is derived from it");
    assert!(
        listed.status.success(),
        "git ls-files failed, so the lane population is unknown and no scope claim can be \
         made: {}",
        String::from_utf8_lossy(&listed.stderr)
    );
    let lane_paths: Vec<String> = String::from_utf8_lossy(&listed.stdout)
        .lines()
        .map(str::to_string)
        .collect();
    assert!(
        lane_paths.len() >= LANE_FLOOR,
        "only {} lane scripts were found, below the floor of {LANE_FLOOR}. A scan that \
         reads almost nothing is a broken scan, not a repository with no lanes — the \
         derivation for AGENTS.md's build-gate table already produced a wrong zero once \
         because a character class excluded a digit",
        lane_paths.len()
    );

    let mut declared_lanes: Vec<(String, LaneWorktreeVerdict)> = Vec::new();
    for path in &lane_paths {
        let text = fs::read_to_string(repo.join(path))
            .unwrap_or_else(|error| panic!("{path} must be readable: {error}"));
        // The row speaks of `fln.e2e/2` lanes, not of every script in the directory. Those
        // are different sets — 24 scripts, 11 declared lanes — and conflating them is
        // `bkw6`'s shape, the scope measured differing from the scope meant.
        if !text.contains("fln.e2e/2") {
            continue;
        }
        let name = path.rsplit('/').next().unwrap_or(path).to_string();
        declared_lanes.push((name, classify_lane(&text, &subcommands, &reaching)));
    }
    assert!(
        !declared_lanes.is_empty(),
        "no script declares the fln.e2e/2 schema, so the row's population is empty and \
         every count below would be a vacuous zero"
    );

    let refusing = declared_lanes
        .iter()
        .filter(|(_, verdict)| matches!(verdict, LaneWorktreeVerdict::Refuses(_)))
        .count();
    let unmeasured: Vec<&String> = declared_lanes
        .iter()
        .filter(|(_, verdict)| matches!(verdict, LaneWorktreeVerdict::Indeterminate(_)))
        .map(|(name, _)| name)
        .collect();
    let running: Vec<&String> = declared_lanes
        .iter()
        .filter(|(_, verdict)| *verdict == LaneWorktreeVerdict::Runs)
        .map(|(name, _)| name)
        .collect();

    // --- bind AGENTS.md's row to the derived counts, both directions --------------------
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let heading = "### Where a green bar may be taken from";
    let start = agents
        .find(heading)
        .expect("AGENTS.md must keep the section stating where a green bar may be taken from");
    let section = &agents[start..];
    let section = &section[..section.find("\n---").unwrap_or(section.len())];

    for (marker, measured) in [
        (" declared fln.e2e/2 lanes", declared_lanes.len()),
        (" refuse on a measured invocation shape", refusing),
        (" whose verdict is unmeasured", unmeasured.len()),
    ] {
        let occurrences = section.matches(marker).count();
        assert_eq!(
            occurrences, 1,
            "the green-bar section must state `…{marker}` exactly once and states it \
             {occurrences} times; zero means the count is compared against nothing and \
             more than one makes it undecidable"
        );
        let head = &section[..section.find(marker).expect("one occurrence")];
        let digits: String = {
            let mut d: Vec<char> = head
                .chars()
                .rev()
                .take_while(char::is_ascii_digit)
                .collect();
            d.reverse();
            d.into_iter().collect()
        };
        let declared: usize = digits.parse().unwrap_or_else(|_| {
            panic!("`…{marker}` in the green-bar section is not preceded by a count")
        });
        assert_eq!(
            declared, measured,
            "the green-bar section declares {declared} for `…{marker}` and the lane \
             population measures {measured}. A new lane, a renamed subcommand or a \
             measured shape moves this number, and the row must move with it — that is the \
             half this bead left open: an affected-surface list nobody re-derives"
        );
    }

    // Every unresolved lane must be NAMED where a reader looks, not folded into a count.
    for name in &unmeasured {
        assert!(
            section.contains(name.as_str()),
            "lane {name} has an unmeasured worktree verdict and the green-bar section does \
             not name it. A reader is told the class refuses and would take a green from a \
             lane nobody has measured: {:?}",
            declared_lanes
        );
    }
    assert!(
        running.is_empty(),
        "these lanes are now PROVEN to run in a linked worktree, which is new and makes a \
         verification path available that the section still denies. Say so there: {running:?}"
    );
}

// ---------------------------------------------------------------------------
// The rch tracker exclusion, and the population a worker would answer for
// ---------------------------------------------------------------------------

/// The floor beneath the tracker walk.
///
/// 214 Rust files under `crates/` and `tools/` at `c0f2ace5`. The floor sits far enough below
/// that ordinary churn never reaches it and a walk that has stopped descending always does. A
/// collapsed scan finds no mentions, which is indistinguishable from a tree in which nobody
/// reads the tracker — and the second one is a clean bill of health.
const RCH_WALK_FLOOR: usize = 150;

/// The rch tracker section of AGENTS.md, sliced to its own heading.
///
/// Scoped to the section rather than the file for `fln-8zsq`'s reason: a check satisfied by the
/// words appearing *somewhere* in a 600-line document is satisfied by this test's own quotation
/// of them the moment either moves.
fn rch_section_of(agents: &str) -> &str {
    let heading = "### The worker does not have the tracker";
    let start = agents.find(heading).unwrap_or_else(|| {
        panic!(
            "AGENTS.md no longer carries the section warning that an rch worker lacks the beads \
             tracker. A pane that offloads a beads-reading suite gets exit 101 — libtest's own \
             failure code — and nothing left in the tree tells them why"
        )
    });
    let section = &agents[start..];
    &section[..section.find("\n---").unwrap_or(section.len())]
}

/// The single disclosure line beginning with `key`.
///
/// Refuses a missing line and a doubled one alike. Two producers for one population is the
/// defect this block exists to remove, so finding two is a refusal and never a preference.
fn rch_disclosure_line<'a>(section: &'a str, key: &str) -> &'a str {
    let mut found: Option<&str> = None;
    for line in section.lines() {
        if let Some(rest) = line.trim_start().strip_prefix(key) {
            assert!(
                found.is_none(),
                "the rch tracker section states {key:?} twice, so the population has two \
                 producers and nothing stops them disagreeing"
            );
            found = Some(rest.trim());
        }
    }
    found.unwrap_or_else(|| {
        panic!(
            "the rch tracker section no longer carries a {key:?} line. That block is the single \
             producer for this section's figures; without it the doctrine states counts that \
             nothing rechecks, which is item 7's shape"
        )
    })
}

/// One `key=value` count, matched on whole tokens.
///
/// Whole-token matching is load-bearing rather than tidy: `reads=` is a substring of
/// `non-reads=`, so a `contains` search silently reads the wrong field and still parses a
/// number — agreement reached by measuring the wrong thing.
fn rch_count(line: &str, key: &str) -> usize {
    let mut found: Option<usize> = None;
    for token in line.split_whitespace() {
        let Some(rest) = token.strip_prefix(key) else {
            continue;
        };
        assert!(found.is_none(), "{key:?} appears twice in {line:?}");
        found = Some(
            rest.parse()
                .unwrap_or_else(|_| panic!("{key:?} is not a count in {line:?}")),
        );
    }
    found.unwrap_or_else(|| panic!("the rch disclosure has no {key:?} field: {line:?}"))
}

/// One `key=value` string field, matched on whole tokens.
fn rch_field<'a>(line: &'a str, key: &str) -> &'a str {
    line.split_whitespace()
        .find_map(|token| token.strip_prefix(key))
        .unwrap_or_else(|| panic!("the rch provenance line has no {key:?}: {line:?}"))
}

/// The declared member list on `key`, refusing a repeated path.
///
/// A duplicate would make a declared cardinality meet a strictly smaller set, so the count
/// could agree with the tree while the membership did not.
fn rch_paths(section: &str, key: &str) -> BTreeSet<String> {
    let listed: Vec<&str> = rch_disclosure_line(section, key)
        .split_whitespace()
        .collect();
    let set: BTreeSet<String> = listed.iter().map(|path| (*path).to_string()).collect();
    assert_eq!(
        set.len(),
        listed.len(),
        "{key:?} lists a path twice, so its declared count meets a smaller set than it appears to"
    );
    set
}

/// Every Rust file under `crates/` and `tools/` naming the tracker, plus the number walked.
///
/// Takes the root so the campaign can drive the real walker over a staged tree. The walk count
/// comes back with the set because an empty result and a clean tree are otherwise the same
/// green — the defect `c0f2ace5` had to repair one section down.
fn rch_tracker_mentions(root: &Path) -> (BTreeSet<String>, usize) {
    const NEEDLE: &str = ".beads/issues.jsonl";
    let mut mentions = BTreeSet::new();
    let mut walked = 0usize;
    let mut stack: Vec<PathBuf> = vec![root.join("crates"), root.join("tools")];
    while let Some(directory) = stack.pop() {
        let entries = fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("{} must be readable: {error}", directory.display()));
        for entry in entries {
            let entry = entry.expect("a directory entry must be readable");
            let file_type = entry.file_type().expect("a file type must be readable");
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().into_owned();
            if file_type.is_symlink() {
                continue;
            }
            if file_type.is_dir() {
                if name != "target" && !name.starts_with('.') {
                    stack.push(path);
                }
                continue;
            }
            if !name.ends_with(".rs") {
                continue;
            }
            walked += 1;
            let text = fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("{} must be readable: {error}", path.display()));
            if text.contains(NEEDLE) {
                let relative = path.strip_prefix(root).unwrap_or(&path);
                mentions.insert(relative.to_string_lossy().replace('\\', "/"));
            }
        }
    }
    (mentions, walked)
}

/// Compare a disclosed population against a measured one, both directions.
///
/// Findings are returned rather than asserted so the campaign can drive this at a staged root
/// and read what fired. Broken *scans* and broken *parses* panic instead, because they are
/// refusals: yielding "no findings" for a walk that found nothing would report a clean tree on
/// the strength of a scan that never ran.
fn judge_rch_population(
    section: &str,
    measured: &BTreeSet<String>,
    walked: usize,
    floor: usize,
) -> Vec<String> {
    assert!(
        walked >= floor,
        "the walk found only {walked} Rust files under crates/ and tools/ against a floor of \
         {floor}. That is a broken scan, not a small tree, and it is refused rather than \
         reported as agreement"
    );
    assert!(
        !measured.is_empty(),
        "no file under crates/ or tools/ names the beads tracker at all. The needle has moved or \
         the walk is broken; either way this is a refusal and never a clean tree"
    );

    let mut findings = Vec::new();

    // The cells nothing in this tree can hold must at least still carry their provenance, and
    // must not contradict the interception the prose claims.
    let provenance = rch_disclosure_line(section, "rch-measured-at:");
    for field in ["head=", "rch="] {
        if rch_field(provenance, field).is_empty() {
            findings.push(format!(
                "provenance: {field:?} is empty, so the unmechanised rch cells claim a \
                 provenance they do not have"
            ));
        }
    }
    let number = |field: &str| -> f64 {
        rch_field(provenance, field)
            .parse()
            .unwrap_or_else(|_| panic!("{field:?} is not a number in {provenance:?}"))
    };
    let (confidence, threshold) = (number("confidence="), number("threshold="));
    if confidence < threshold {
        findings.push(format!(
            "coherence: the section says a plain `cargo test` WOULD INTERCEPT while disclosing \
             confidence {confidence} BELOW threshold {threshold}. One of the two is wrong, and \
             the reader who trusts the prose offloads a beads-reading suite to a worker that has \
             no tracker"
        ));
    }

    let counts = rch_disclosure_line(section, "rch-tracker-population:");
    let mentions = rch_count(counts, "mentions=");
    let non_reads = rch_count(counts, "non-reads=");
    let reads = rch_count(counts, "reads=");
    let declared_reads = rch_paths(section, "rch-tracker-reads:");
    let declared_non_reads = rch_paths(section, "rch-tracker-non-reads:");

    if declared_reads.len() != reads {
        findings.push(format!(
            "counts: rch-tracker-population says reads={reads} while rch-tracker-reads lists {} \
             paths",
            declared_reads.len()
        ));
    }
    if declared_non_reads.len() != non_reads {
        findings.push(format!(
            "counts: rch-tracker-population says non-reads={non_reads} while \
             rch-tracker-non-reads lists {} paths",
            declared_non_reads.len()
        ));
    }
    if reads + non_reads != mentions {
        findings.push(format!(
            "conservation: reads={reads} + non-reads={non_reads} != mentions={mentions}. Every \
             file naming the tracker is one or the other"
        ));
    }

    let declared: BTreeSet<String> = declared_reads.union(&declared_non_reads).cloned().collect();
    if declared.len() != declared_reads.len() + declared_non_reads.len() {
        let both: Vec<&String> = declared_reads.intersection(&declared_non_reads).collect();
        findings.push(format!(
            "overlap: {both:?} are listed as BOTH a read and a non-read, so the classification \
             says two things about one file"
        ));
    }

    let arrived: Vec<&String> = measured.difference(&declared).collect();
    if !arrived.is_empty() {
        findings.push(format!(
            "arrived: these files now name the beads tracker and are in neither list: \
             {arrived:?}. If one READS it, it breaks under rch and joins rch-tracker-reads; if it \
             only mentions the path, it joins rch-tracker-non-reads. Then move mentions= and the \
             matching count. Growing silently is what strands the next reader"
        ));
    }
    let departed: Vec<&String> = declared.difference(measured).collect();
    if !departed.is_empty() {
        findings.push(format!(
            "departed: these paths are listed in the rch tracker population but no longer name \
             the tracker — moved, renamed, or the mention was deleted: {departed:?}. Drop them \
             and lower the counts; a list that denotes nothing reads as maintained and is not"
        ));
    }

    findings
}

/// The rch tracker-exclusion row describes the population this tree actually has.
///
/// `~/.config/rch/config.toml` drops `.beads/` from the worker sync while the tracker is a
/// tracked file, so an offloaded suite that reads it dies on the worker at exit 101 — the code
/// libtest also uses for a real assertion failure. One command produced both in one session.
/// The doctrine section is the only place that says so, and `hugg` is the standing proof that a
/// correction delivered by broadcast does not survive a pane restart.
///
/// **What this binds.** The in-repo population a worker would answer for: membership and
/// cardinality, in both directions and per member, so a file that starts naming the tracker
/// cannot arrive silently and a listed member cannot rot away. Both directions matter for
/// opposite reasons — silent growth strands the next reader with a number that was true once,
/// and a stale member makes the list look maintained while denoting nothing.
///
/// **What it cannot.** `~/.config/rch/config.toml` is outside the repository, so no test here
/// can hold the exclusion, the threshold or the confidence; a version bump moves all three and
/// this tree would not notice. Those cells are disclosed with the version they were measured at
/// so a reader can tell whether they still describe their machine, and the only mechanical claim
/// made about them is internal: a section asserting interception while disclosing a confidence
/// *below* its own threshold is incoherent, and that is refused. The read/non-read
/// classification is likewise reviewed prose — this refuses a member appearing or vanishing,
/// never a member filed under the wrong heading.
#[test]
fn the_rch_tracker_exclusion_row_matches_the_measured_population() {
    let repo = fln_conformance::checked_workspace_root!();
    let agents = fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md must be readable");
    let section = rch_section_of(&agents);
    let (measured, walked) = rch_tracker_mentions(&repo);
    let findings = judge_rch_population(section, &measured, walked, RCH_WALK_FLOOR);
    assert!(findings.is_empty(), "{}", findings.join("\n\n"));
}

// --- the campaign, at a staged root -----------------------------------------------------
//
// The floors above exist for the day the scan breaks, and a healthy tree can never exercise
// them: with 214 real files present, `walked >= 150` cannot fire. `build_gate_governed_sets`
// paid for that lesson — inject the inputs or the check is decorative.

/// A staged root with `crates/` and `tools/`, uniquely named so no run inherits another's files.
fn rch_staged_root(tag: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("the clock must be after the epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!("fln-rch-{}-{tag}-{nanos}", std::process::id()));
    fs::create_dir_all(root.join("crates")).expect("the staged crates dir must be creatable");
    fs::create_dir_all(root.join("tools")).expect("the staged tools dir must be creatable");
    root
}

/// Write `relative` under the staged root, naming the tracker or not.
fn rch_stage_file(root: &Path, relative: &str, names_the_tracker: bool) {
    let path = root.join(relative);
    fs::create_dir_all(path.parent().expect("a staged file must have a parent"))
        .expect("the staged parent must be creatable");
    let body = if names_the_tracker {
        "fn probe() { let _ = \".beads/issues.jsonl\"; }\n"
    } else {
        "fn probe() { let _ = \"nothing of interest\"; }\n"
    };
    fs::write(path, body).expect("the staged file must be writable");
}

/// The baseline section: one read, one non-read, agreeing with the baseline root.
fn rch_baseline_section() -> String {
    rch_section(
        "head=abcd1234 rch=1.0.52 confidence=0.95 threshold=0.85",
        "mentions=2 non-reads=1 reads=1",
        "crates/alpha/src/reader.rs",
        "tools/beta/src/mentioner.rs",
    )
}

fn rch_section(provenance: &str, population: &str, reads: &str, non_reads: &str) -> String {
    format!(
        "### The worker does not have the tracker — staged\n\n```text\n\
         rch-measured-at: {provenance}\n\
         rch-tracker-population: {population}\n\
         rch-tracker-reads: {reads}\n\
         rch-tracker-non-reads: {non_reads}\n```\n"
    )
}

/// The baseline root the whole campaign varies one thing against.
fn rch_baseline_root(tag: &str) -> PathBuf {
    let root = rch_staged_root(tag);
    rch_stage_file(&root, "crates/alpha/src/reader.rs", true);
    rch_stage_file(&root, "tools/beta/src/mentioner.rs", true);
    rch_stage_file(&root, "crates/alpha/src/quiet.rs", false);
    root
}

/// The control. Every mutant below must be shown against a baseline that is genuinely clean,
/// or a red proves nothing about the change that produced it.
#[test]
fn rch_control_a_disclosure_that_matches_its_root_yields_no_findings() {
    let root = rch_baseline_root("control");
    let (measured, walked) = rch_tracker_mentions(&root);
    assert_eq!(walked, 3, "the staged walk must see all three staged files");
    let findings = judge_rch_population(&rch_baseline_section(), &measured, walked, 2);
    assert!(
        findings.is_empty(),
        "the baseline must be clean: {findings:?}"
    );
}

#[test]
fn rch_mutant_a_new_file_naming_the_tracker_is_caught() {
    let root = rch_baseline_root("arrived");
    rch_stage_file(&root, "crates/gamma/tests/newcomer.rs", true);
    let (measured, walked) = rch_tracker_mentions(&root);
    let findings = judge_rch_population(&rch_baseline_section(), &measured, walked, 2);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("arrived:")
                && finding.contains("crates/gamma/tests/newcomer.rs")),
        "a file that starts naming the tracker must be caught and NAMED: {findings:?}"
    );
}

#[test]
fn rch_mutant_a_listed_path_that_stopped_naming_it_is_caught() {
    let root = rch_baseline_root("departed");
    // The one variable: the listed read stops naming the tracker. Nothing else moves.
    rch_stage_file(&root, "crates/alpha/src/reader.rs", false);
    let (measured, walked) = rch_tracker_mentions(&root);
    let findings = judge_rch_population(&rch_baseline_section(), &measured, walked, 2);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("departed:")
                && finding.contains("crates/alpha/src/reader.rs")),
        "a listed member that has rotted away must be caught and NAMED: {findings:?}"
    );
}

#[test]
fn rch_mutant_a_count_that_does_not_conserve_is_caught() {
    let root = rch_baseline_root("conservation");
    let (measured, walked) = rch_tracker_mentions(&root);
    let section = rch_section(
        "head=abcd1234 rch=1.0.52 confidence=0.95 threshold=0.85",
        "mentions=3 non-reads=1 reads=1",
        "crates/alpha/src/reader.rs",
        "tools/beta/src/mentioner.rs",
    );
    let findings = judge_rch_population(&section, &measured, walked, 2);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("conservation:")),
        "reads + non-reads must equal mentions: {findings:?}"
    );
}

#[test]
fn rch_mutant_a_list_shorter_than_its_count_is_caught() {
    let root = rch_baseline_root("shortlist");
    let (measured, walked) = rch_tracker_mentions(&root);
    let section = rch_section(
        "head=abcd1234 rch=1.0.52 confidence=0.95 threshold=0.85",
        "mentions=2 non-reads=1 reads=1",
        "",
        "tools/beta/src/mentioner.rs",
    );
    let findings = judge_rch_population(&section, &measured, walked, 2);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("counts:")),
        "a declared count that its own list cannot meet must be caught: {findings:?}"
    );
}

#[test]
fn rch_mutant_a_path_in_both_lists_is_caught() {
    let root = rch_baseline_root("overlap");
    let (measured, walked) = rch_tracker_mentions(&root);
    let section = rch_section(
        "head=abcd1234 rch=1.0.52 confidence=0.95 threshold=0.85",
        "mentions=2 non-reads=1 reads=1",
        "crates/alpha/src/reader.rs",
        "crates/alpha/src/reader.rs",
    );
    let findings = judge_rch_population(&section, &measured, walked, 2);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("overlap:")),
        "one file classified two ways must be caught: {findings:?}"
    );
}

#[test]
fn rch_mutant_interception_claimed_below_its_own_threshold_is_caught() {
    let root = rch_baseline_root("coherence");
    let (measured, walked) = rch_tracker_mentions(&root);
    let section = rch_section(
        "head=abcd1234 rch=1.0.52 confidence=0.50 threshold=0.85",
        "mentions=2 non-reads=1 reads=1",
        "crates/alpha/src/reader.rs",
        "tools/beta/src/mentioner.rs",
    );
    let findings = judge_rch_population(&section, &measured, walked, 2);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("coherence:")),
        "a section claiming interception below its own threshold must be caught: {findings:?}"
    );
}

#[test]
#[should_panic(expected = "broken scan")]
fn rch_mutant_a_collapsed_walk_refuses_instead_of_agreeing() {
    let root = rch_baseline_root("collapsed");
    let (measured, walked) = rch_tracker_mentions(&root);
    // The floor is what a healthy tree can never exercise, so it is exercised here.
    let _ = judge_rch_population(&rch_baseline_section(), &measured, walked, 4);
}

#[test]
#[should_panic(expected = "never a clean tree")]
fn rch_mutant_an_empty_scan_refuses_instead_of_reporting_clean() {
    let root = rch_staged_root("empty");
    rch_stage_file(&root, "crates/alpha/src/quiet.rs", false);
    rch_stage_file(&root, "tools/beta/src/quiet.rs", false);
    let (measured, walked) = rch_tracker_mentions(&root);
    assert!(measured.is_empty(), "the staged root must name nothing");
    let _ = judge_rch_population(&rch_baseline_section(), &measured, walked, 2);
}

#[test]
#[should_panic(expected = "twice")]
fn rch_mutant_a_doubled_disclosure_line_refuses() {
    let root = rch_baseline_root("doubled");
    let (measured, walked) = rch_tracker_mentions(&root);
    let doubled = format!(
        "{}\nrch-tracker-population: mentions=9 non-reads=9 reads=9\n",
        rch_baseline_section()
    );
    let _ = judge_rch_population(&doubled, &measured, walked, 2);
}

#[test]
#[should_panic(expected = "no longer carries")]
fn rch_mutant_a_missing_disclosure_line_refuses() {
    let root = rch_baseline_root("missing");
    let (measured, walked) = rch_tracker_mentions(&root);
    let section = rch_baseline_section().replace("rch-tracker-population:", "rch-tracker-absent:");
    let _ = judge_rch_population(&section, &measured, walked, 2);
}

#[test]
#[should_panic(expected = "no longer carries the section")]
fn rch_mutant_deleting_the_doctrine_section_refuses() {
    let _ = rch_section_of("# AGENTS.md\n\nEverything except the section that must exist.\n");
}

// ---------------------------------------------------------------------------------------------
// franken_lean-h40t: the OTHER half of the launch population — Rust-side launches
//
// `every_python_launch_under_scripts_is_sealed` derives its scope from `scripts/`, and the `.py`
// half of it enforces a sealed **shebang**. Neither reaches a launch written in Rust, and the
// shebang rule is not merely out of scope there — it is INAPPLICABLE. A shebang is consulted only
// when a script is executed directly; `Command::new("python3").arg(script)` names the interpreter
// itself, so the sealed `#!/usr/bin/env -S python3 -I -S` line is never read and buys nothing.
//
// The two guards therefore look complementary and leave a population between them: measured at
// `b6e6b732`, five Rust-side launches of trusted scripts live under `crates/` and `tools/`, every
// one of them sealed by hand, held by nothing. A sixth written without `-I` would restore exactly
// the channel this bead exists to shut — an ambient `PYTHONPATH`, or a `hashlib.py` beside the
// script, replacing the stdlib under the process that computes governed digests and decides
// verdicts — and no check in this tree would notice.
//
// The judgement is a PURE FUNCTION over (path, body) pairs so the decoy can be INJECTED. A guard
// whose only input is a healthy tree cannot demonstrate that it finds anything: with five sealed
// call sites present, "no unsealed launch" is what a scan returning nothing at all also reports.
// ---------------------------------------------------------------------------------------------

/// The file with full-line `//` comments blanked, line numbering preserved.
///
/// **The first run of this guard failed on its own doc comment**, which explains the defect in
/// English and so contains the pattern it searches for. That is `fln-8zsq`'s lesson reproduced
/// inside the fix for a different bead, and the direction it failed in was the correct one: a
/// scanner that cannot separate prose from code should redden, not quietly widen. Blanking rather
/// than deleting keeps every reported line number equal to the line in the real file. Only
/// whole-line comments are removed — a trailing `//` is left alone, because cutting at one risks
/// truncating a line whose string literal merely contains `//`.
fn code_only(body: &str) -> String {
    body.lines()
        .map(|line| {
            if line.trim_start().starts_with("//") {
                ""
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Every Rust-side interpreter launch that does not seal startup, as (path, line, command).
///
/// `-I` is the load-bearing flag: isolated mode ignores `PYTHONPATH` and refuses to put the
/// script's own directory on `sys.path`. `-S` is required with it because that is the standard
/// the `.py` entry points in this tree already hold, and a launch sealed against the environment
/// but still importing `site` is a weaker guarantee wearing the same name.
fn unsealed_rust_launches(files: &[(String, String)]) -> Vec<(String, usize, String)> {
    const LAUNCH: &str = concat!("Command::new(\"", "python3\")");
    let mut found = Vec::new();
    for (path, raw) in files {
        let body = code_only(raw);
        let body = &body;
        let mut cursor = 0usize;
        while let Some(offset) = body[cursor..].find(LAUNCH) {
            let start = cursor + offset;
            let line = body[..start].matches('\n').count() + 1;
            // The builder chain ends where the process is actually started; flags added after
            // that would belong to a different command.
            let tail = &body[start..];
            let end = ["\n    ;", ".output()", ".status()", ".spawn()"]
                .iter()
                .filter_map(|marker| tail.find(marker))
                .min()
                .unwrap_or(tail.len().min(800));
            let chain = &tail[..end];
            let sealed = chain.contains("\"-I\"") && chain.contains("\"-S\"");
            if !sealed {
                let shown: String = chain.split_whitespace().collect::<Vec<_>>().join(" ");
                found.push((path.clone(), line, shown.chars().take(120).collect()));
            }
            cursor = start + LAUNCH.len();
        }
    }
    found
}

/// Repository-relative directories the repo itself declares as generated output.
///
/// Derived from `.gitignore`'s own rooted-directory entries (`/scripts/e2e/artifacts/`,
/// `/target`, …) rather than named here. Walking from the repository root without this picked up
/// **twelve** untracked `.rs` files under `scripts/e2e/artifacts/` — generated structural-gate
/// fixtures — which is `fln-bench-apparatus-empty-referent-bkw6`'s documented trap reproduced to
/// the exact count. A generated fixture is not this repository's source, and reddening the build
/// over one is the cry-wolf failure. Deriving the exclusion keeps it honest in the safe
/// direction: if `.gitignore` stops declaring a directory the scan WIDENS, which can only make
/// this guard noisier, never blind.
fn declared_generated_directories(repo: &Path) -> BTreeSet<String> {
    let Ok(text) = fs::read_to_string(repo.join(".gitignore")) else {
        return BTreeSet::new();
    };
    text.lines()
        .map(str::trim)
        .filter(|line| line.starts_with('/') && !line.starts_with("/*"))
        .map(|line| {
            line.trim_start_matches('/')
                .trim_end_matches('/')
                .to_string()
        })
        .filter(|line| !line.is_empty() && !line.contains('*'))
        .collect()
}

/// Collect `*.rs` under `dir`, skipping build and vendor output.
fn rust_tree(dir: &Path, found: &mut Vec<(String, String)>, repo: &Path) {
    let generated = declared_generated_directories(repo);
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let Ok(entry) = entry else { continue };
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if path.is_dir() {
            if name == "target" || name == "vendor" || name == ".git" {
                continue;
            }
            let relative = path
                .strip_prefix(repo)
                .map(|rel| rel.to_string_lossy().into_owned())
                .unwrap_or_default();
            if generated.contains(&relative) {
                continue;
            }
            rust_tree(&path, found, repo);
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let Ok(body) = fs::read_to_string(&path) else {
            continue;
        };
        let relative = path
            .strip_prefix(repo)
            .expect("a scanned path lies under the repository")
            .to_string_lossy()
            .into_owned();
        found.push((relative, body));
    }
}

#[test]
fn every_rust_side_launch_of_a_trusted_script_is_sealed() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    // The scan roots are NOT named. The first version of this guard walked `crates/` and
    // `tools/`, which is a hand-listed scope — the defect this repository keeps producing, and
    // the one the guard itself was written about. Measured immediately after it landed: 214 of
    // 232 tracked `.rs` files were scanned and **18 were invisible**, the whole of
    // `tribunal/epoch-lab/`, which `k60n`'s row already records as a nested workspace the
    // members glob never walks. No launch lived there, so it was an unwatched population rather
    // than a live hole — which is exactly what the five `crates/`+`tools/` launches were. A
    // named root cannot drift if there is no named root, so the walk starts at the repository.
    // The exclusion must not be INERT. A `.gitignore` that failed to parse would return an empty
    // set, the walk would silently widen to include generated fixtures, and nothing would say so
    // — `fln-inert-declaration-shape`: a declaration that reads as behaviour and does nothing.
    // Checked in both halves: the repo must declare generated directories, and at least one of
    // them must actually be on disk, or the declaration is naming only absent paths.
    let generated = declared_generated_directories(&repo);
    assert!(
        !generated.is_empty(),
        "no generated-output directories were derived from .gitignore, so the exclusion this \
         walk depends on is inert and the scan has silently widened to include build products"
    );
    assert!(
        generated.iter().any(|dir| repo.join(dir).is_dir()),
        "every directory .gitignore declares as generated output is absent from disk ({generated:?}); \
         the derivation is parsing something, but not paths this tree has, so the exclusion \
         cannot be shown to exclude anything"
    );

    let mut files = Vec::new();
    rust_tree(&repo, &mut files, &repo);
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let launches: usize = files
        .iter()
        .map(|(_, body)| {
            code_only(body)
                .matches(concat!("Command::new(\"", "python3\")"))
                .count()
        })
        .sum();
    // A moved directory or a broken filter must fail loudly rather than report a clean tree.
    // Five were measured at `b6e6b732`; this is a FLOOR, so removing one is allowed and only a
    // scan that has lost its scope reddens.
    assert!(
        launches >= 5 && files.len() >= 200,
        "derived scan found {launches} Rust-side interpreter launch(es) across {} Rust files in \
         the repository, which is too few for this tree. Five launches over 232 files were \
         measured at 887db274, so an empty or truncated scan is a BROKEN SCAN and is refused \
         rather than reported as a clean tree. Both figures are floors: a launch removed or a \
         file deleted is allowed, a collapsed scope is not.",
        files.len()
    );

    let unsealed = unsealed_rust_launches(&files);
    assert!(
        unsealed.is_empty(),
        "these Rust-side launches start Python without `-I -S`: {unsealed:#?}\n\n\
         A shebang does NOT protect them: `Command::new(\"python3\").arg(script)` names the \
         interpreter, so the script's sealed `#!` line is never read. Without `-I` an ambient \
         PYTHONPATH, or a module beside the script, replaces the stdlib under a trusted evidence \
         producer. Add `.args([\"-I\", \"-S\"])` before the script path."
    );
}

/// The decoy, and the mutant that deletes it.
///
/// With five sealed call sites in the tree, the test above cannot distinguish "found nothing
/// wrong" from "found nothing". These feed the judgement synthetic bodies, so the finding and
/// its absence are both demonstrated (`franken_lean-pfei` R4's shape).
#[test]
fn the_rust_launch_scan_finds_a_planted_unsealed_launch_and_clears_a_sealed_one() {
    let sealed = (
        "crates/decoy/tests/sealed.rs".to_string(),
        "let out = Command::new(\"python3\")\n.args([\"-I\", \"-S\"])\n.arg(script)\n.output();"
            .to_string(),
    );
    assert!(
        unsealed_rust_launches(std::slice::from_ref(&sealed)).is_empty(),
        "a launch carrying -I and -S must be judged sealed, or the guard reddens a correct tree"
    );

    let decoy = (
        "crates/decoy/tests/unsealed.rs".to_string(),
        "let out = Command::new(\"python3\")\n.arg(script)\n.arg(\"validate\")\n.output();"
            .to_string(),
    );
    let found = unsealed_rust_launches(std::slice::from_ref(&decoy));
    assert_eq!(
        found.len(),
        1,
        "the planted unsealed launch was not found; the scan is not reading what it claims to"
    );
    assert_eq!(
        found[0].1, 1,
        "the finding must carry the line it was found at"
    );

    // -S alone is not isolation: this is the mutation that would otherwise read as sealed.
    let site_only = (
        "crates/decoy/tests/site_only.rs".to_string(),
        "Command::new(\"python3\").args([\"-S\"]).arg(script).output();".to_string(),
    );
    assert_eq!(
        unsealed_rust_launches(std::slice::from_ref(&site_only)).len(),
        1,
        "`-S` without `-I` leaves PYTHONPATH and the script directory live and must not pass"
    );

    // The prose/code split, in BOTH directions. Blanking comments is what stopped this guard
    // reporting its own doc comment as a finding, and a stripper that swallowed real code would
    // hide launches instead — the failure that looks identical to a clean tree.
    let commented = (
        "crates/decoy/tests/commented.rs".to_string(),
        "// explains that Command::new(\"python3\").arg(script) skips the shebang\n".to_string(),
    );
    assert!(
        unsealed_rust_launches(std::slice::from_ref(&commented)).is_empty(),
        "a launch pattern inside a whole-line comment is prose, not a launch; counting it is what \
         made the first run of this guard redden on its own explanation"
    );
    let same_line_in_code = (
        "crates/decoy/tests/code.rs".to_string(),
        "    let out = Command::new(\"python3\").arg(script).output();\n".to_string(),
    );
    assert_eq!(
        unsealed_rust_launches(std::slice::from_ref(&same_line_in_code)).len(),
        1,
        "the identical text in CODE must still be found; a comment stripper that swallows real \
         launches reports a clean tree for the same reason a broken scan does"
    );

    // Flags added AFTER the process starts belong to a different command and must not seal it.
    let after = (
        "crates/decoy/tests/after.rs".to_string(),
        "Command::new(\"python3\").arg(script).output();\nlet other = [\"-I\", \"-S\"];"
            .to_string(),
    );
    assert_eq!(
        unsealed_rust_launches(std::slice::from_ref(&after)).len(),
        1,
        "flags appearing after .output() are not part of the launch and must not seal it"
    );
}

// ---------------------------------------------------------------------------------------------
// franken_lean-h40t: the THIRD launch surface — the workflows, where the bootstrap runs
//
// The sealing family now has three members and they were found one at a time, each by asking
// where the previous one's scope ended:
//
//   1. `scripts/**` — shebangs and shell launches         (pre-existing)
//   2. `crates/**`, `tools/**` — Rust launches            (887db274, then 83f851af for its scope)
//   3. `.github/workflows/*.yml` — THIS                   (nothing watched it per commit)
//
// The third is the one that matters most and was guarded least. `ci.yml` bootstraps the
// toolchain: it parses `rust-toolchain.toml` under Python to decide which compiler the whole
// build uses. A shadowed `tomllib` there chooses the compiler — the exact vector this bead was
// filed for, proven live under `fln-8mj`.
//
// **`ci.yml` does carry a self-check, and it has three defects, each from a family this
// repository has recorded before.** `ci.yml:149` greps for unsealed bootstrap snippets, but
//   (a) it greps the literal path `.github/workflows/ci.yml`, so `contract-drift.yml` is outside
//       it — a hand-listed scope, in the guard for this very property;
//   (b) it is a workflow step, so it runs only in CI and never under `cargo test` — `pnav`'s
//       shape, a producer that exists but is registered nowhere a commit reaches;
//   (c) its pattern matches only the bare-stdin `python3 - ` form, so `-c`, a script path, and
//       the `subprocess` list form are all invisible to it.
//
// Measured at 83f851af: every launch in both workflows is sealed. So this is an UNWATCHED
// POPULATION, not a live defect — the same thing the five Rust launches were, one layer out.
// ---------------------------------------------------------------------------------------------

/// Lines in a workflow that start Python **without** `-I`, and the reason each is permitted.
///
/// Every entry carries a marker that must still be present in the same file, so an allowance
/// cannot outlive the reason it was granted for. Two are the isolation probe's negative-control
/// arms — they must run *unprotected* to prove the hijack reproduces, exactly like
/// `python_isolation_probe.sh`'s entry in `UNSEALED_LAUNCH_ALLOWANCE`. The third is not a launch
/// at all but a grep PATTERN, and declaring it buys something: this guard now fails if `ci.yml`'s
/// own self-check is deleted, which closes defect (b) above from the outside.
const WORKFLOW_UNSEALED_ALLOWANCE: &[(&str, &str, &str)] = &[
    (
        ".github/workflows/ci.yml",
        "vulnerable=\"$(cd \"$shadow\"",
        "isolated=\"$(cd \"$shadow\"",
    ),
    (
        ".github/workflows/ci.yml",
        "vulnerable_env=\"$(PYTHONPATH=",
        "isolated_env=\"$(PYTHONPATH=",
    ),
    (
        ".github/workflows/ci.yml",
        "if grep -nE",
        "a bootstrap snippet invokes python3 without -I",
    ),
];

/// `.github/workflows/*.{yml,yaml}`, workspace-relative, with their text.
///
/// An unreadable workflow FAILS rather than contributing the empty string: a workflow read as
/// empty launches nothing and would look exactly like a clean one, which is `ci_execution_join`'s
/// recorded reason for the same refusal.
fn workflow_files(repo: &Path) -> Vec<(String, String)> {
    let dir = repo.join(".github/workflows");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .expect(".github/workflows must be readable")
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|ext| ext == "yml" || ext == "yaml")
        })
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let relative = path
                .strip_prefix(repo)
                .expect("a workflow lies under the repository")
                .to_string_lossy()
                .into_owned();
            let body = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("{relative} must be readable to be judged: {e}"));
            (relative, body)
        })
        .collect()
}

/// Is this workflow line a Python *launch*, as opposed to prose about one?
///
/// `echo` lines and comments talk about interpreters; they do not start them. This is the same
/// prose/code split that made the Rust guard redden on its own doc comment, met deliberately
/// here rather than discovered — and it is why the remaining grep PATTERN is declared in the
/// allowance instead of filtered, since a filter for it would also hide a real launch.
fn workflow_launches_python(command: &str) -> bool {
    let trimmed = command.trim();
    if trimmed.starts_with('#') || trimmed.starts_with("echo ") || trimmed.starts_with("echo\"") {
        return false;
    }
    launches_python(trimmed)
}

#[test]
fn every_workflow_python_launch_is_sealed_or_declared() {
    let repo = fln_conformance::checked_workspace_root!();
    let repo = repo
        .canonicalize()
        .expect("the repository root must resolve");
    let workflows = workflow_files(&repo);
    assert!(
        workflows.len() >= 2,
        "derived {} workflow file(s); two were measured at 83f851af, so a scan that has lost \
         the directory is refused rather than reported as a clean tree",
        workflows.len()
    );

    let mut launches = 0usize;
    let mut unsealed: Vec<String> = Vec::new();
    let mut allowance_used: Vec<(&str, &str)> = Vec::new();

    for (relative, body) in &workflows {
        for (line_no, command) in logical_lines(body) {
            if !workflow_launches_python(&command) {
                continue;
            }
            launches += 1;
            // The subprocess list form spells the flag as its own quoted argument.
            if command.contains("python3 -I") || command.contains(r#""python3","#) {
                continue;
            }
            match WORKFLOW_UNSEALED_ALLOWANCE
                .iter()
                .find(|(path, needle, _)| path == relative && command.contains(needle))
            {
                Some((_, needle, marker)) => {
                    assert!(
                        body.contains(marker),
                        "{relative}:{line_no} holds an unsealed-launch allowance whose stated \
                         reason is gone: the marker {marker:?} is no longer in the file, so the \
                         allowance names something that is not there"
                    );
                    allowance_used.push((relative, needle));
                }
                None => unsealed.push(format!("{relative}:{line_no}: {}", command.trim())),
            }
        }
    }

    assert!(
        launches >= 8,
        "derived only {launches} Python launch(es) across the workflows; fourteen were measured \
         at 83f851af. A pattern that has stopped matching is a BROKEN SCAN and is refused rather \
         than reported as a workflow set that starts no interpreters."
    );
    assert!(
        unsealed.is_empty(),
        "these workflow lines start Python without `-I`: {unsealed:#?}\n\n\
         `ci.yml` bootstraps the toolchain by parsing rust-toolchain.toml under Python, so a \
         shadowed module here chooses the compiler for the whole build. Add `-I`, or declare the \
         line in WORKFLOW_UNSEALED_ALLOWANCE with the marker that states why it must run \
         unprotected."
    );
    assert_eq!(
        allowance_used.len(),
        WORKFLOW_UNSEALED_ALLOWANCE.len(),
        "an allowance entry never matched a scanned line: {allowance_used:?} of {:?}. A dead \
         entry is a hole with a name on it, and this list may only shrink.",
        WORKFLOW_UNSEALED_ALLOWANCE
            .iter()
            .map(|(path, needle, _)| (*path, *needle))
            .collect::<Vec<_>>()
    );
}

// ------------------------------------------------------------------------------------------
// franken_lean-m3fq — the pin declares components, and nothing verifies them.
//
// `fln-y0f7` above is a worker missing a FILE. This is a worker missing a COMPONENT of the
// toolchain, and it reaches further because one of the two gates it breaks reports the
// breakage in the shape of a code defect.
//
// `rust-toolchain.toml` declares four components of the pin. `parse_rust_lock` in
// `scripts/evidence.py` — the sealed-cargo path's toolchain check — reads that file for
// `channel` only and never reads `components`, so a machine holding the pinned nightly
// WITHOUT `clippy` passes every identity check this repository performs. Locally rustup
// installs them from the same file, which is why it has never been felt on a developer
// machine and why the remote case went four reproductions without a rule.
//
// Measured at `925e6604` in a scratch crate, one variable per cell: `cargo clippy
// --all-targets -- -D warnings` exits **101** on a real finding and **1** when the component
// is absent, so `check.sh`'s registration of 101 puts an absent component OUTSIDE the
// semantic set, where it types `internal_fault` rather than a stage failure. `cargo fmt
// --check` exits **1** for BOTH. The clippy separation is load-bearing and undocumented
// until now — changing that 101 to a 1 would convert every environment fault on the stage
// into a reported code defect, which is FL-INV-07 exactly.
// ------------------------------------------------------------------------------------------

/// The exit code a cargo gate returns when its component is absent, measured rather than assumed.
const COMPONENT_ABSENT_EXIT: &str = "1";

/// Derive the pin's declared components from `rust-toolchain.toml`.
///
/// Derived, never transcribed: a second copy of this list here would be free to drift from the
/// pin, which is the defect this whole family is about. An unparseable manifest is a refusal.
fn declared_pin_components(manifest: &str) -> Vec<String> {
    let Some(rest) = manifest.split_once("components") else {
        return Vec::new();
    };
    let Some((_, body)) = rest.1.split_once('[') else {
        return Vec::new();
    };
    let Some((body, _)) = body.split_once(']') else {
        return Vec::new();
    };
    body.split(',')
        .map(|raw| raw.trim().trim_matches('"').trim().to_string())
        .filter(|item| !item.is_empty())
        .collect()
}

/// The `--semantic-failure-exit` a `check.sh` stage registers, read from the case arm naming it.
///
/// Returns `None` when the arm or its registration cannot be located, so a restructured
/// `check.sh` refuses here instead of silently reporting whatever it found last.
fn registered_semantic_exit(check_sh: &str, stage: &str) -> Option<String> {
    let arm = check_sh.find(&format!("|{stage}|"))?;
    let tail = &check_sh[arm..];
    let at = tail.find("--semantic-failure-exit ")?;
    let value = tail[at + "--semantic-failure-exit ".len()..]
        .split(|c: char| !c.is_ascii_digit())
        .next()?;
    (!value.is_empty()).then(|| value.to_string())
}

/// Judge the pin/gate/doctrine triple, returning a finding per broken property.
///
/// Findings rather than assertions so each property can be gutted alone and every mutant is
/// planted in the ARGUMENTS. All four inputs are plain text, so the campaign below costs no
/// process spawns and never writes a governed file.
fn pin_component_findings(
    manifest: &str,
    check_sh: &str,
    evidence: &str,
    agents: &str,
) -> Vec<String> {
    let mut findings = Vec::new();
    let components = declared_pin_components(manifest);
    if components.len() < 4 {
        findings.push(format!(
            "pin-floor: rust-toolchain.toml declared only {} pin component(s): {components:?}. \
             Four were declared when this binding landed, and a scan that cannot read the array \
             looks exactly like a pin that declares nothing — refuse rather than report a clean \
             pin.",
            components.len()
        ));
    }

    let heading = "### The worker may lack a component of the pin";
    let Some(start) = agents.find(heading) else {
        findings.push(
            "doctrine-missing: AGENTS.md no longer carries the section stating that the pin's \
             components are unverified. That section is what stops an agent diagnosing this \
             repository when a worker answers without `clippy`, and it is the only place the \
             measured exit-code separation is written down."
                .to_string(),
        );
        return findings;
    };
    let section = &agents[start..];
    let section = &section[..section.find("\n---").unwrap_or(section.len())];

    // Every declared component must be named where the rule is stated. Derived from the pin, so
    // adding a fifth component obliges its author to say whether its absence is separable.
    for component in &components {
        if !section.contains(component.as_str()) {
            findings.push(format!(
                "component-unclassified: the pin declares {component:?} and the AGENTS.md \
                 section on unverified components does not name it. A component nobody has \
                 classified is one whose absence will be diagnosed as a defect of this \
                 repository."
            ));
        }
    }

    // The load-bearing half: the clippy stage must register an exit OUTSIDE the code an absent
    // component returns. This is the single edit that would convert every environment fault on
    // that stage into a reported code defect.
    let Some(clippy_exit) = registered_semantic_exit(check_sh, "clippy") else {
        findings.push(
            "gate-unreadable: could not locate the clippy stage's `--semantic-failure-exit` \
             registration in scripts/check.sh. A restructured gate refuses here rather than \
             passing on a registration this can no longer see."
                .to_string(),
        );
        return findings;
    };
    if clippy_exit == COMPONENT_ABSENT_EXIT {
        findings.push(format!(
            "gate-conflates: scripts/check.sh registers exit {clippy_exit} as the clippy stage's \
             SEMANTIC failure, and {COMPONENT_ABSENT_EXIT} is the exit a cargo gate returns when \
             its component is absent. Registering it means an environment fault — a worker or a \
             fresh clone without the `clippy` component of the pin — is reported as a code \
             defect, which is FL-INV-07's prohibition: an inconclusive outcome rendered as a \
             rejection. Measured at `925e6604`: a real clippy finding exits 101, an absent \
             component exits 1."
        ));
    }
    // A check that the SECTION still quotes the live registration stood here and was DELETED,
    // because the mutation campaign proved it could not fail. Two reasons compound: the section
    // legitimately quotes both registrations (101 for clippy, 1 for fmt) since the whole point
    // is the contrast, and `"--semantic-failure-exit 101"` contains `"--semantic-failure-exit 1"`
    // as a substring anyway. So no change to the gate could make it fire. An assertion that
    // cannot fail reads exactly like coverage, which is the one thing worse than an absent
    // check — `f2t9`'s two deleted `dep:`/`pkg/feat` assertions, same reasoning.

    // U4J7 closes the ambiguous-exit hole before process spawn. The raw cargo command still
    // returns 1 both when formatting differs and when rustfmt is absent, so the only sound join
    // is the sealed admission check plus its missing/recovery execution cells. Bind all three
    // producer tokens: a dormant check or a negative cell with no recovery is not the repair.
    let fmt_preflight_bound = evidence.contains("sealed_compiler_component_absent")
        && evidence.contains("sealed_fmt_component_absent")
        && evidence.contains("sealed_fmt_component_undeclared")
        && evidence.contains("sealed_fmt_components_unreadable")
        && evidence.contains("sealed_fmt_component_recovery")
        && evidence.contains("component_marker.read_text() == \"executed\\n\"")
        && evidence.contains("\"validator_mutants\": 4");
    if !fmt_preflight_bound {
        findings.push(
            "fmt-preflight-unbound: scripts/evidence.py no longer carries the typed missing-\
             rustfmt refusal, the planted absent-component cell, and the executable recovery \
             control as one mechanism. The raw cargo fmt exit remains ambiguous, so losing any \
             one of those joins reopens an environment fault as a code finding."
                .to_string(),
        );
    }
    if !(section.contains("cargo fmt --check")
        && section.contains("sealed_compiler_component_absent")
        && section.contains("sealed_fmt_component_recovery"))
    {
        findings.push(
            "fmt-doctrine-stale: AGENTS.md no longer states that sealed admission separates the \
             raw cargo fmt exit by refusing absent rustfmt before spawn and admitting the \
             executable recovery control. A live check whose operator doctrine still says \
             'non-separable' is an unbound repair."
                .to_string(),
        );
    }
    findings
}

fn pin_inputs() -> (String, String, String, String) {
    let repo = worker_repo();
    (
        fs::read_to_string(repo.join("rust-toolchain.toml")).expect("rust-toolchain.toml"),
        fs::read_to_string(repo.join("scripts/check.sh")).expect("scripts/check.sh"),
        fs::read_to_string(repo.join("scripts/evidence.py")).expect("scripts/evidence.py"),
        fs::read_to_string(repo.join("AGENTS.md")).expect("AGENTS.md"),
    )
}

#[test]
fn the_pin_declares_components_and_sealed_admission_separates_fmt_absence() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let findings = pin_component_findings(&manifest, &check_sh, &evidence, &agents);
    assert!(
        findings.is_empty(),
        "the pin's declared components, the gate that consumes them, and the doctrine that \
         classifies their absence have come apart:\n\n{}",
        findings.join("\n\n")
    );
}

/// Gut 1: the clippy stage starts registering the environment-fault exit as semantic.
#[test]
fn a_clippy_stage_that_registers_the_component_absent_exit_is_caught() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = check_sh.replace("--semantic-failure-exit 101", "--semantic-failure-exit 1");
    assert_ne!(mutated, check_sh, "the registration needle has moved");
    let findings = pin_component_findings(&manifest, &mutated, &evidence, &agents);
    assert!(
        findings.iter().any(|f| f.starts_with("gate-conflates")),
        "registering the component-absent exit as a semantic failure must be caught — that one \
         edit turns every environment fault into a code defect: {findings:?}"
    );
}

/// Gut 2: a component is added to the pin and nobody classifies it.
#[test]
fn a_new_pin_component_that_nobody_classifies_is_caught() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = manifest.replace(
        "components = [\"rustfmt\"",
        "components = [\"llvm-tools-preview\", \"rustfmt\"",
    );
    assert_ne!(mutated, manifest, "the components needle has moved");
    let findings = pin_component_findings(&mutated, &check_sh, &evidence, &agents);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("component-unclassified") && f.contains("llvm-tools-preview")),
        "a component added to the pin without being classified must be caught: {findings:?}"
    );
}

/// Gut 3: the pin's component array becomes unreadable — a refusal, never a clean pin.
#[test]
fn a_pin_whose_components_cannot_be_read_refuses() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = manifest.replace("components = [", "components_disabled = (");
    assert_ne!(mutated, manifest, "the components needle has moved");
    let findings = pin_component_findings(&mutated, &check_sh, &evidence, &agents);
    assert!(
        findings.iter().any(|f| f.starts_with("pin-floor")),
        "a pin whose component array cannot be read must refuse, because that is \
         indistinguishable from a pin declaring nothing: {findings:?}"
    );
}

/// Gut 4: the doctrine section disappears.
#[test]
fn a_missing_component_doctrine_section_refuses() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = agents.replace(
        "### The worker may lack a component of the pin",
        "### Removed",
    );
    assert_ne!(mutated, agents, "the heading needle has moved");
    let findings = pin_component_findings(&manifest, &check_sh, &evidence, &mutated);
    assert!(
        findings.iter().any(|f| f.starts_with("doctrine-missing")),
        "losing the section that classifies a component-absent failure must refuse: {findings:?}"
    );
}

/// Gut 5: the executable recovery half of the fmt preflight disappears.
#[test]
fn dropping_the_fmt_component_recovery_cell_is_caught() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = evidence.replace(
        "sealed_fmt_component_recovery",
        "fmt_component_recovery_removed",
    );
    assert_ne!(mutated, evidence, "the recovery-cell needle has moved");
    let findings = pin_component_findings(&manifest, &check_sh, &mutated, &agents);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("fmt-preflight-unbound")),
        "dropping the recovery half of the fmt preflight must be caught: {findings:?}"
    );
}

/// Gut 6: component declaration drift is no longer exercised.
#[test]
fn dropping_the_fmt_component_declaration_cells_is_caught() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = evidence
        .replace(
            "sealed_fmt_component_undeclared",
            "fmt_component_undeclared_removed",
        )
        .replace(
            "sealed_fmt_components_unreadable",
            "fmt_components_unreadable_removed",
        );
    assert_ne!(mutated, evidence, "the declaration-cell needles have moved");
    let findings = pin_component_findings(&manifest, &check_sh, &mutated, &agents);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("fmt-preflight-unbound")),
        "dropping the declaration-binding cells must be caught: {findings:?}"
    );
}

/// Gut 7: the metadata validator's mutation campaign disappears.
#[test]
fn dropping_the_fmt_component_validator_mutants_is_caught() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = evidence.replace("\"validator_mutants\": 4", "\"validator_mutants\": 0");
    assert_ne!(mutated, evidence, "the validator-mutant needle has moved");
    let findings = pin_component_findings(&manifest, &check_sh, &mutated, &agents);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("fmt-preflight-unbound")),
        "dropping the component-fact validator mutants must be caught: {findings:?}"
    );
}

/// Gut 8: `check.sh` is restructured so the registration cannot be found.
#[test]
fn a_gate_whose_registration_cannot_be_located_refuses() {
    let (manifest, check_sh, evidence, agents) = pin_inputs();
    let mutated = check_sh.replace("|clippy|", "|clippy-stage|");
    assert_ne!(mutated, check_sh, "the case-arm needle has moved");
    let findings = pin_component_findings(&manifest, &mutated, &evidence, &agents);
    assert!(
        findings.iter().any(|f| f.starts_with("gate-unreadable")),
        "a gate whose registration this can no longer read must refuse rather than pass on a \
         stale reading: {findings:?}"
    );
}
