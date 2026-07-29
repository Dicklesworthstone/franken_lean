//! Two-pass, no-mock transcript matrix for the pinned CLI personalities.

#![forbid(unsafe_code)]

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use fln_conformance::cli_lake_census::{
    CliLakeInventory, ProcessOutcome, SemanticRecord, TelemetryRecord, TranscriptBundle,
    classify_process,
};
use fln_conformance::pin;

const TIMEOUT: Duration = Duration::from_secs(20);
const MAX_CAPTURE_BYTES: u64 = 4 * 1024 * 1024;

#[derive(Clone, Copy)]
struct Probe {
    key: &'static str,
    personality: &'static str,
    argv: &'static [&'static str],
    stdin: &'static [u8],
}

const PROBES: &[Probe] = &[
    Probe {
        key: "lean:help",
        personality: "lean",
        argv: &["--help"],
        stdin: b"",
    },
    Probe {
        key: "lean:version",
        personality: "lean",
        argv: &["--version"],
        stdin: b"",
    },
    Probe {
        key: "lean:short-version",
        personality: "lean",
        argv: &["--short-version"],
        stdin: b"",
    },
    Probe {
        key: "lean:githash",
        personality: "lean",
        argv: &["--githash"],
        stdin: b"",
    },
    Probe {
        key: "lean:features",
        personality: "lean",
        argv: &["--features"],
        stdin: b"",
    },
    Probe {
        key: "lean:print-prefix",
        personality: "lean",
        argv: &["--print-prefix"],
        stdin: b"",
    },
    Probe {
        key: "lean:print-libdir",
        personality: "lean",
        argv: &["--print-libdir"],
        stdin: b"",
    },
    Probe {
        key: "lean:unknown-option",
        personality: "lean",
        argv: &["--fln-census-unknown"],
        stdin: b"",
    },
    Probe {
        key: "lean:malformed-timeout",
        personality: "lean",
        argv: &["--timeout=not-a-number"],
        stdin: b"",
    },
    Probe {
        key: "lean:stdin-success",
        personality: "lean",
        argv: &["--stdin"],
        stdin: b"#check Nat\n",
    },
    Probe {
        key: "lean:json-error",
        personality: "lean",
        argv: &["--json", "--stdin"],
        stdin: b"#check CliLakeCensusMissing\n",
    },
    Probe {
        key: "lake:usage",
        personality: "lake",
        argv: &[],
        stdin: b"",
    },
    Probe {
        key: "lake:help",
        personality: "lake",
        argv: &["--help"],
        stdin: b"",
    },
    Probe {
        key: "lake:help-build",
        personality: "lake",
        argv: &["help", "build"],
        stdin: b"",
    },
    Probe {
        key: "lake:help-query",
        personality: "lake",
        argv: &["help", "query"],
        stdin: b"",
    },
    Probe {
        key: "lake:help-env",
        personality: "lake",
        argv: &["help", "env"],
        stdin: b"",
    },
    Probe {
        key: "lake:version",
        personality: "lake",
        argv: &["--version"],
        stdin: b"",
    },
    Probe {
        key: "lake:unknown-command",
        personality: "lake",
        argv: &["fln-census-unknown"],
        stdin: b"",
    },
    Probe {
        key: "lake:unknown-option",
        personality: "lake",
        argv: &["--fln-census-unknown", "help"],
        stdin: b"",
    },
    Probe {
        key: "lake:missing-dir-value",
        personality: "lake",
        argv: &["--dir"],
        stdin: b"",
    },
    Probe {
        key: "lake:missing-root",
        personality: "lake",
        argv: &["--dir", "/fln-cli-census/absent", "build"],
        stdin: b"",
    },
    Probe {
        key: "lake:json-help",
        personality: "lake",
        argv: &["--json", "help", "query"],
        stdin: b"",
    },
    Probe {
        key: "leanc:help",
        personality: "leanc",
        argv: &["--help"],
        stdin: b"",
    },
    Probe {
        key: "leanc:version",
        personality: "leanc",
        argv: &["--version"],
        stdin: b"",
    },
    Probe {
        key: "leanc:unknown-option",
        personality: "leanc",
        argv: &["--fln-census-unknown"],
        stdin: b"",
    },
];

#[derive(Clone, Debug, Eq, PartialEq)]
struct Observation {
    key: String,
    personality: String,
    argv: String,
    stdin_hash: String,
    exit_code: i32,
    stdout_hash: String,
    stderr_hash: String,
    stdout_bytes: usize,
    stderr_bytes: usize,
    channel: String,
}

fn toolchain_binaries(lean: &Path) -> Result<(PathBuf, [PathBuf; 3]), String> {
    let bin = lean
        .parent()
        .ok_or_else(|| format!("pinned Lean path has no parent: {}", lean.display()))?;
    let root = bin
        .parent()
        .ok_or_else(|| format!("pinned Lean bin has no toolchain root: {}", bin.display()))?
        .to_path_buf();
    let binaries = [bin.join("lean"), bin.join("leanc"), bin.join("lake")];
    for binary in &binaries {
        if !binary.is_file() {
            return Err(format!(
                "pinned CLI sibling is absent: {}",
                binary.display()
            ));
        }
    }
    Ok((root, binaries))
}

fn binary<'a>(personality: &str, binaries: &'a [PathBuf; 3]) -> Result<&'a Path, String> {
    match personality {
        "lean" => Ok(&binaries[0]),
        "leanc" => Ok(&binaries[1]),
        "lake" => Ok(&binaries[2]),
        other => Err(format!("unknown probe personality {other:?}")),
    }
}

fn run_probe(
    probe: Probe,
    binaries: &[PathBuf; 3],
    toolchain_root: &Path,
    workspace_root: &Path,
) -> Result<(Observation, u64), String> {
    let started = Instant::now();
    let mut command = Command::new(binary(probe.personality, binaries)?);
    command
        .args(probe.argv)
        .current_dir(workspace_root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .env("TERM", "dumb")
        .env("NO_COLOR", "1")
        .env("CLICOLOR", "0")
        .env(
            "PATH",
            format!("{}:/usr/bin:/bin", toolchain_root.join("bin").display()),
        );
    for name in [
        "LAKE_CONFIG",
        "LAKE_HOME",
        "LAKE_NO_CACHE",
        "LAKE_PKG_URL_MAP",
        "LAKE_OVERRIDE_LEAN",
        "LEAN",
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "LEAN_SYSROOT",
        "LEAN_CC",
        "LEAN_AR",
        "LEAN_GITHASH",
        "ELAN_TOOLCHAIN",
    ] {
        command.env_remove(name);
    }
    let mut child = command
        .spawn()
        .map_err(|error| format!("spawn {}: {error}", probe.key))?;
    let mut stdin = child
        .stdin
        .take()
        .ok_or_else(|| format!("{} has no stdin pipe", probe.key))?;
    stdin
        .write_all(probe.stdin)
        .map_err(|error| format!("write {} stdin: {error}", probe.key))?;
    drop(stdin);
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| format!("{} has no stdout pipe", probe.key))?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| format!("{} has no stderr pipe", probe.key))?;
    let stdout_reader = std::thread::spawn(move || read_bounded(stdout));
    let stderr_reader = std::thread::spawn(move || read_bounded(stderr));
    let deadline = Instant::now() + TIMEOUT;
    let status = loop {
        match child
            .try_wait()
            .map_err(|error| format!("wait {}: {error}", probe.key))?
        {
            Some(status) => break status,
            None if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(10));
            }
            None => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = stdout_reader.join();
                let _ = stderr_reader.join();
                return Err(format!(
                    "{} produced typed inconclusive timeout after {}s",
                    probe.key,
                    TIMEOUT.as_secs()
                ));
            }
        }
    };
    let stdout = stdout_reader
        .join()
        .map_err(|_| format!("{} stdout reader faulted", probe.key))??;
    let stderr = stderr_reader
        .join()
        .map_err(|_| format!("{} stderr reader faulted", probe.key))??;
    let exit_code = status
        .code()
        .ok_or_else(|| format!("{} produced typed inconclusive cancellation", probe.key))?;
    let replacements = [
        (
            toolchain_root.to_string_lossy().into_owned(),
            "<TOOLCHAIN>".to_string(),
        ),
        (
            workspace_root.to_string_lossy().into_owned(),
            "<WORKSPACE>".to_string(),
        ),
        (
            std::env::var("HOME").unwrap_or_default(),
            "<HOME>".to_string(),
        ),
    ];
    let stdout = normalize(&stdout, &replacements);
    let stderr = normalize(&stderr, &replacements);
    let channel = if !stdout.is_empty() && !stderr.is_empty() {
        "split"
    } else if !stdout.is_empty() {
        "stdout"
    } else if !stderr.is_empty() {
        "stderr"
    } else {
        "silent"
    };
    let elapsed = started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64;
    Ok((
        Observation {
            key: probe.key.to_string(),
            personality: probe.personality.to_string(),
            argv: if probe.argv.is_empty() {
                "<none>".to_string()
            } else {
                probe.argv.join("\u{1f}")
            },
            stdin_hash: if probe.stdin.is_empty() {
                "none".to_string()
            } else {
                fnv(probe.stdin)
            },
            exit_code,
            stdout_hash: fnv(&stdout),
            stderr_hash: fnv(&stderr),
            stdout_bytes: stdout.len(),
            stderr_bytes: stderr.len(),
            channel: channel.to_string(),
        },
        elapsed,
    ))
}

fn read_bounded(pipe: impl Read) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    pipe.take(MAX_CAPTURE_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read child output: {error}"))?;
    if bytes.len() as u64 > MAX_CAPTURE_BYTES {
        return Err(format!(
            "child output exceeded the {MAX_CAPTURE_BYTES}-byte resource budget"
        ));
    }
    Ok(bytes)
}

fn normalize(payload: &[u8], replacements: &[(String, String)]) -> Vec<u8> {
    let mut text = String::from_utf8_lossy(payload).replace("\r\n", "\n");
    text = strip_ansi(&text);
    let mut replacements = replacements.to_vec();
    replacements.sort_by_key(|(actual, _)| std::cmp::Reverse(actual.len()));
    for (actual, symbolic) in replacements {
        if !actual.is_empty() {
            text = text.replace(&actual, &symbolic);
        }
    }
    text.into_bytes()
}

fn strip_ansi(value: &str) -> String {
    let bytes = value.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes.get(index) == Some(&0x1b) && bytes.get(index + 1) == Some(&b'[') {
            index += 2;
            while let Some(byte) = bytes.get(index).copied() {
                index += 1;
                if (0x40..=0x7e).contains(&byte) {
                    break;
                }
            }
        } else {
            output.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8_lossy(&output).into_owned()
}

fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn persist_transcripts(bundle: &TranscriptBundle) -> Result<(), String> {
    let Some(records) = std::env::var_os(pin::RIG_EXECUTION_DIR_ENV) else {
        return Ok(());
    };
    let records = PathBuf::from(records);
    let root = records.parent().ok_or_else(|| {
        format!(
            "rig execution directory has no parent: {}",
            records.display()
        )
    })?;
    persist_new(
        &root.join("cli-lake-census-semantic.ndjson"),
        &bundle.semantic_ndjson(),
    )?;
    persist_new(
        &root.join("cli-lake-census-telemetry.ndjson"),
        &bundle.telemetry_ndjson(),
    )?;
    persist_new(
        &root.join("cli-lake-census-roots.txt"),
        &format!(
            "schema=fln.cli-lake.transcript-roots/1\nsemantic_root={}\ntelemetry_root={}\n",
            bundle.semantic_root(),
            bundle.telemetry_root()
        ),
    )
}

fn persist_new(path: &Path, text: &str) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(path)
        .map_err(|error| format!("create {}: {error}", path.display()))?;
    file.write_all(text.as_bytes())
        .map_err(|error| format!("write {}: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("sync {}: {error}", path.display()))
}

#[test]
fn cli_lake_census_no_mock_e2e() -> Result<(), String> {
    let run = pin::RigRun::new(pin::PinRig::CliLakeCensusNoMockE2e);
    let Some(lean) = pin::pinned_lean() else {
        let notice = run.typed_skip()?;
        eprintln!("{notice}");
        return Ok(());
    };
    let root = pin::workspace_root();
    let inventory = CliLakeInventory::load_embedded().map_err(|error| error.to_string())?;
    inventory
        .validate_workspace_sources(&root)
        .map_err(|error| error.to_string())?;
    let (toolchain_root, binaries) = toolchain_binaries(&lean)?;
    let expected_keys = inventory
        .transcripts
        .iter()
        .map(|transcript| transcript.key.as_str())
        .collect::<Vec<_>>();
    let compiled_keys = PROBES.iter().map(|probe| probe.key).collect::<Vec<_>>();
    if expected_keys != compiled_keys {
        return Err("compiled probe matrix and inventory differ".to_string());
    }

    let mut first = Vec::new();
    let mut second = Vec::new();
    let mut telemetry = Vec::new();
    for (sequence, probe) in PROBES.iter().copied().enumerate() {
        let (observation, elapsed) = run_probe(probe, &binaries, &toolchain_root, &root)?;
        first.push(observation);
        telemetry.push(TelemetryRecord {
            sequence: sequence as u64,
            probe_id: probe.key.to_string(),
            elapsed_micros: elapsed,
            output_bytes: 0,
        });
    }
    for probe in PROBES.iter().copied() {
        let (observation, elapsed) = run_probe(probe, &binaries, &toolchain_root, &root)?;
        second.push(observation);
        let record = telemetry
            .iter_mut()
            .find(|record| record.probe_id == probe.key)
            .ok_or_else(|| format!("telemetry record vanished for {}", probe.key))?;
        record.elapsed_micros = record.elapsed_micros.saturating_add(elapsed);
    }
    if first != second {
        return Err("two fresh complete CLI matrices produced different semantics".to_string());
    }

    let mut semantic = Vec::new();
    for (sequence, ((actual, expected), probe)) in first
        .iter()
        .zip(&inventory.transcripts)
        .zip(PROBES)
        .enumerate()
    {
        let matches = actual.key == expected.key
            && actual.personality == expected.personality
            && actual.argv == expected.argv
            && actual.stdin_hash == expected.stdin_hash
            && actual.exit_code == expected.exit_code
            && actual.stdout_hash == expected.stdout_hash
            && actual.stderr_hash == expected.stderr_hash
            && actual.stdout_bytes == expected.stdout_bytes
            && actual.stderr_bytes == expected.stderr_bytes
            && actual.channel == expected.channel;
        if !matches {
            return Err(format!(
                "real pinned transcript drifted for {}: expected={expected:?} actual={actual:?}",
                probe.key
            ));
        }
        let telemetry_record = telemetry
            .get_mut(sequence)
            .ok_or_else(|| format!("telemetry sequence vanished for {}", probe.key))?;
        telemetry_record.output_bytes = (actual.stdout_bytes + actual.stderr_bytes) as u64;
        semantic.push(SemanticRecord {
            sequence: sequence as u64,
            epoch_id: inventory.reference.commit.clone(),
            probe_id: probe.key.to_string(),
            personality: probe.personality.to_string(),
            expected_exit: expected.exit_code,
            actual_exit: actual.exit_code,
            expected_stdout: expected.stdout_hash.clone(),
            actual_stdout: actual.stdout_hash.clone(),
            expected_stderr: expected.stderr_hash.clone(),
            actual_stderr: actual.stderr_hash.clone(),
            authority_root: inventory.inventory_root.clone(),
            disposition: classify_process(ProcessOutcome::Exited(actual.exit_code)),
            final_state: "two-pass-match".to_string(),
        });
    }
    let bundle = TranscriptBundle::new(semantic, telemetry).map_err(|error| error.to_string())?;
    bundle
        .validate_authority(&inventory)
        .map_err(|error| error.to_string())?;
    let reparsed =
        TranscriptBundle::from_ndjson(&bundle.semantic_ndjson(), &bundle.telemetry_ndjson())
            .map_err(|error| error.to_string())?;
    if reparsed != bundle {
        return Err("strict semantic/telemetry NDJSON did not round-trip".to_string());
    }
    if bundle.semantic_ndjson().contains("elapsed_micros")
        || bundle.telemetry_ndjson().contains("authority_root")
    {
        return Err("semantic and telemetry authority domains were mixed".to_string());
    }
    persist_transcripts(&bundle)?;
    run.executed()
}
