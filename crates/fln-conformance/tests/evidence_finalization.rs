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
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
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
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
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
