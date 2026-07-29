//! Real-process join across the three pinned PublicSurface input domains.
//!
//! The exhaustive CLI/Lake and LSP probes remain separate registered rigs. This
//! join proves that their canonical products, the option receipt, and a fresh
//! binary/server observation all name one Reference and one contract root.

#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use fln_conformance::pin;
use fln_conformance::public_surface::{
    EvidenceBundle, PublicSurfaceContract, SemanticDisposition, SemanticRecord, TelemetryRecord,
};

const TIMEOUT: Duration = Duration::from_secs(20);
const MAX_CAPTURE_BYTES: u64 = 4 * 1024 * 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Observation {
    domain: String,
    key: String,
    input_root: String,
    output_root: String,
    expected: String,
    actual: String,
    client: String,
    authority: String,
}

fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn toolchain_binaries(lean: &Path) -> Result<(PathBuf, [PathBuf; 3]), String> {
    let bin = lean
        .parent()
        .ok_or_else(|| format!("pinned Lean path has no parent: {}", lean.display()))?;
    let toolchain_root = bin
        .parent()
        .ok_or_else(|| format!("pinned Lean bin has no toolchain root: {}", bin.display()))?
        .to_path_buf();
    let binaries = [bin.join("lean"), bin.join("leanc"), bin.join("lake")];
    for binary in &binaries {
        if !binary.is_file() {
            return Err(format!(
                "pinned toolchain sibling is absent: {}",
                binary.display()
            ));
        }
    }
    Ok((toolchain_root, binaries))
}

fn toolchain_path(lean: &Path) -> Result<OsString, String> {
    let bin = lean
        .parent()
        .ok_or_else(|| format!("pinned Lean path has no parent: {}", lean.display()))?;
    let mut paths = vec![bin.to_path_buf()];
    if let Some(ambient) = std::env::var_os("PATH") {
        paths.extend(std::env::split_paths(&ambient));
    }
    std::env::join_paths(paths).map_err(|error| format!("construct pinned PATH: {error}"))
}

fn run_bounded(mut command: Command, label: &str) -> Result<Output, String> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command
        .spawn()
        .map_err(|error| format!("spawn {label}: {error}"))?;
    let stdout = match child.stdout.take() {
        Some(stdout) => stdout,
        None => {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!("{label} has no stdout pipe"));
        }
    };
    let stderr = match child.stderr.take() {
        Some(stderr) => stderr,
        None => {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!("{label} has no stderr pipe"));
        }
    };
    let stdout_reader = std::thread::spawn(move || read_bounded(stdout));
    let stderr_reader = std::thread::spawn(move || read_bounded(stderr));
    let deadline = Instant::now() + TIMEOUT;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Ok(None) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = stdout_reader.join();
                let _ = stderr_reader.join();
                return Err(format!(
                    "{label} produced typed inconclusive timeout after {}s",
                    TIMEOUT.as_secs()
                ));
            }
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = stdout_reader.join();
                let _ = stderr_reader.join();
                return Err(format!("wait for {label}: {error}"));
            }
        }
    };
    let stdout = stdout_reader
        .join()
        .map_err(|_| format!("{label} stdout reader faulted"))??;
    let stderr = stderr_reader
        .join()
        .map_err(|_| format!("{label} stderr reader faulted"))??;
    Ok(Output {
        status,
        stdout,
        stderr,
    })
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

fn run_version(
    contract: &PublicSurfaceContract,
    binary: &Path,
    personality: &str,
    toolchain_root: &Path,
    root: &Path,
) -> Result<(Observation, u64), String> {
    let started = Instant::now();
    let mut command = Command::new(binary); // ubs:ignore — verified pinned sibling; fixed argv; no shell
    command
        .arg("--version")
        .current_dir(root)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SYSROOT")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .env("TERM", "dumb")
        .env("NO_COLOR", "1")
        .env("CLICOLOR", "0")
        .env(
            "PATH",
            format!("{}:/usr/bin:/bin", toolchain_root.join("bin").display()),
        );
    let output = run_bounded(command, &format!("pinned {personality} --version"))?;
    let elapsed = started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64;
    let code = output
        .status
        .code()
        .ok_or_else(|| format!("pinned {personality} --version ended by signal"))?;
    let replacements = [
        (
            toolchain_root.to_string_lossy().into_owned(),
            "<TOOLCHAIN>".to_string(),
        ),
        (
            root.to_string_lossy().into_owned(),
            "<WORKSPACE>".to_string(),
        ),
        (
            std::env::var("HOME").unwrap_or_default(),
            "<HOME>".to_string(),
        ),
    ];
    let stdout = normalize(&output.stdout, &replacements);
    let stderr = normalize(&output.stderr, &replacements);
    let actual = format!(
        "exit={code};stdout={};stderr={}",
        fnv(&stdout),
        fnv(&stderr)
    );
    let fixture_key = format!("{personality}:version");
    let fixture = contract
        .fixtures
        .iter()
        .find(|fixture| fixture.domain == "cli-lake" && fixture.key == fixture_key)
        .ok_or_else(|| format!("contract lacks fixture cli-lake:{fixture_key}"))?;
    if actual != fixture.expected {
        return Err(format!(
            "fresh pinned {personality} version transcript drifted: expected {}, actual {actual}",
            fixture.expected
        ));
    }
    let domain = contract
        .domain("cli-lake")
        .ok_or_else(|| "contract lacks CLI/Lake domain".to_string())?;
    let mut transcript = stdout;
    transcript.extend_from_slice(&stderr);
    Ok((
        Observation {
            domain: "cli-lake".to_string(),
            key: fixture_key,
            input_root: domain.input_root.clone(),
            output_root: fnv(&transcript),
            expected: actual.clone(),
            actual,
            client: personality.to_string(),
            authority: fixture.authority.clone(),
        },
        elapsed,
    ))
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

fn run_option_dump(
    contract: &PublicSurfaceContract,
    lean: &Path,
    root: &Path,
) -> Result<(Observation, u64), String> {
    let fixture = root.join("crates/fln-conformance/fixtures/x4_option_dump.lean");
    let started = Instant::now();
    let mut command = Command::new(lean); // ubs:ignore — verified Reference binary; fixed argv; no shell
    command
        .arg(&fixture) // ubs:ignore — fixture is a fixed repository path under the validated root
        .current_dir(root)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SYSROOT")
        .env("LANG", "C")
        .env("LC_ALL", "C");
    let output = run_bounded(command, "pinned option registry dump")?;
    let elapsed = started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!(
            "pinned option registry dump failed: status={:?}, stderr-bytes={}",
            output.status.code(),
            output.stderr.len()
        ));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|_| "pinned option registry dump is not UTF-8".to_string())?;
    let actual = stdout
        .lines()
        .last()
        .ok_or_else(|| "pinned option registry dump is empty".to_string())?;
    if actual != "TOTAL\t661" {
        return Err(format!("pinned option registry total drifted: {actual:?}"));
    }
    let domain = contract
        .domain("option")
        .ok_or_else(|| "contract lacks option domain".to_string())?;
    Ok((
        Observation {
            domain: "option".to_string(),
            key: "dump".to_string(),
            input_root: domain.input_root.clone(),
            output_root: fnv(&output.stdout),
            expected: "TOTAL=661".to_string(),
            actual: "TOTAL=661".to_string(),
            client: "lean".to_string(),
            authority: "pinned-reference-binary".to_string(),
        },
        elapsed,
    ))
}

struct Server {
    child: Child,
    input: Option<std::process::ChildStdin>,
    frames: Receiver<Result<String, String>>,
    reader: Option<JoinHandle<()>>,
}

impl Server {
    fn start(lean: &Path, path: &OsString, root: &Path) -> Result<Self, String> {
        let mut child = Command::new(lean) // ubs:ignore — verified Reference binary; fixed argv; no shell
            .args(["--server", "-DstderrAsMessages=false"])
            .current_dir(root)
            .env("PATH", path) // ubs:ignore — path begins with the verified pinned toolchain bin
            .env_remove("LEAN_PATH")
            .env_remove("LEAN_SYSROOT")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|error| format!("start pinned lean --server: {error}"))?;
        let input = child
            .stdin
            .take()
            .ok_or_else(|| "pinned server has no stdin".to_string())?;
        let output = child
            .stdout
            .take()
            .ok_or_else(|| "pinned server has no stdout".to_string())?;
        let (sender, frames) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut reader = BufReader::new(output);
            loop {
                let frame = read_frame(&mut reader);
                let terminal = frame.is_err();
                if sender.send(frame).is_err() || terminal {
                    break;
                }
            }
        });
        Ok(Self {
            child,
            input: Some(input),
            frames,
            reader: Some(reader),
        })
    }

    fn send(&mut self, json: &str) -> Result<(), String> {
        let input = self
            .input
            .as_mut()
            .ok_or_else(|| "pinned server stdin is closed".to_string())?;
        write!(input, "Content-Length: {}\r\n\r\n{json}", json.len())
            .map_err(|error| format!("write pinned server frame: {error}"))?;
        input
            .flush()
            .map_err(|error| format!("flush pinned server frame: {error}"))
    }

    fn response(&self, id: u64) -> Result<String, String> {
        let deadline = Instant::now() + TIMEOUT;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(format!("timed out waiting for pinned server response {id}"));
            }
            let frame = self
                .frames
                .recv_timeout(remaining)
                .map_err(|error| format!("receive pinned server response {id}: {error}"))??;
            if frame_has_numeric_id(&frame, id) {
                return Ok(frame);
            }
        }
    }

    fn finish(mut self) -> Result<(), String> {
        self.input.take();
        let deadline = Instant::now() + TIMEOUT;
        let status = loop {
            if let Some(status) = self
                .child
                .try_wait()
                .map_err(|error| format!("poll pinned server: {error}"))?
            {
                break status;
            }
            if Instant::now() >= deadline {
                let _ = self.child.kill();
                let _ = self.child.wait();
                return Err("pinned server did not exit after the exit notification".to_string());
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        if let Some(reader) = self.reader.take() {
            reader
                .join()
                .map_err(|_| "pinned server frame reader did not join".to_string())?;
        }
        if !status.success() {
            return Err(format!(
                "pinned server exited with status {:?}",
                status.code()
            ));
        }
        Ok(())
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}

fn frame_has_numeric_id(frame: &str, expected: u64) -> bool {
    frame.match_indices("\"id\"").any(|(offset, key)| {
        let Some(after_key) = frame.get(offset + key.len()..) else {
            return false;
        };
        let Some(after_colon) = after_key.trim_start().strip_prefix(':') else {
            return false;
        };
        let value = after_colon.trim_start();
        let digits = value.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            return false;
        }
        let Some((token, remainder)) = value.get(..digits).zip(value.get(digits..)) else {
            return false;
        };
        token.parse::<u64>().ok() == Some(expected)
            && remainder
                .bytes()
                .next()
                .is_some_and(|byte| byte.is_ascii_whitespace() || matches!(byte, b',' | b'}'))
    })
}

fn read_frame(reader: &mut BufReader<std::process::ChildStdout>) -> Result<String, String> {
    let mut content_length = None;
    loop {
        let mut line = String::new();
        let read = reader
            .read_line(&mut line)
            .map_err(|error| format!("read pinned server header: {error}"))?;
        if read == 0 {
            return Err("pinned server stream closed".to_string());
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if let Some(value) = trimmed.strip_prefix("Content-Length: ") {
            content_length = Some(
                value
                    .parse::<usize>()
                    .map_err(|error| format!("parse server Content-Length: {error}"))?,
            );
        }
    }
    let length = content_length.ok_or_else(|| "server frame lacks Content-Length".to_string())?;
    if length as u64 > MAX_CAPTURE_BYTES {
        return Err(format!(
            "server frame exceeds the {MAX_CAPTURE_BYTES}-byte resource budget"
        ));
    }
    let mut payload = vec![0_u8; length];
    reader
        .read_exact(&mut payload)
        .map_err(|error| format!("read pinned server payload: {error}"))?;
    String::from_utf8(payload).map_err(|_| "pinned server payload is not UTF-8".to_string())
}

fn run_lsp_handshake(
    contract: &PublicSurfaceContract,
    lean: &Path,
    path: &OsString,
    root: &Path,
) -> Result<(Observation, u64), String> {
    let started = Instant::now();
    let mut server = Server::start(lean, path, root)?;
    server.send(
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\
         \"processId\":null,\"rootUri\":null,\"capabilities\":{},\
         \"futureClientField\":{\"accepted\":true}}}",
    )?;
    let initialize = server.response(1)?;
    if !initialize.contains("\"result\"") || initialize.contains("\"error\"") {
        return Err(format!(
            "minimal-profile initialize was not accepted: {initialize}"
        ));
    }
    server.send("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}")?;
    server.send("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\",\"params\":null}")?;
    let shutdown = server.response(2)?;
    if !shutdown.contains("\"result\":null") {
        return Err(format!("shutdown response is not canonical: {shutdown}"));
    }
    server.send("{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}")?;
    server.finish()?;
    let elapsed = started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64;
    let domain = contract
        .domain("lsp")
        .ok_or_else(|| "contract lacks LSP domain".to_string())?;
    let transcript = format!("{initialize}\n{shutdown}\n");
    Ok((
        Observation {
            domain: "lsp".to_string(),
            key: "request:initialize+shutdown".to_string(),
            input_root: domain.input_root.clone(),
            output_root: fnv(transcript.as_bytes()),
            expected: "initialize=result;shutdown=null".to_string(),
            actual: "initialize=result;shutdown=null".to_string(),
            client: "minimal-client".to_string(),
            authority: "pinned-reference-server".to_string(),
        },
        elapsed,
    ))
}

fn run_pass(
    contract: &PublicSurfaceContract,
    lean: &Path,
    binaries: &[PathBuf; 3],
    toolchain_root: &Path,
    path: &OsString,
    root: &Path,
) -> Result<(Vec<Observation>, Vec<u64>), String> {
    let mut observations = Vec::new();
    let mut elapsed = Vec::new();
    for (personality, binary) in ["lean", "leanc", "lake"].into_iter().zip(binaries) {
        let (observation, duration) =
            run_version(contract, binary, personality, toolchain_root, root)?;
        observations.push(observation);
        elapsed.push(duration);
    }
    let (option, duration) = run_option_dump(contract, lean, root)?;
    observations.push(option);
    elapsed.push(duration);
    let (lsp, duration) = run_lsp_handshake(contract, lean, path, root)?;
    observations.push(lsp);
    elapsed.push(duration);
    Ok((observations, elapsed))
}

#[test]
fn response_id_matching_is_numeric_token_exact() {
    assert!(frame_has_numeric_id(
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":null}",
        1
    ));
    assert!(frame_has_numeric_id("{\"jsonrpc\":\"2.0\",\"id\": 1 }", 1));
    assert!(!frame_has_numeric_id(
        "{\"jsonrpc\":\"2.0\",\"id\":10,\"result\":null}",
        1
    ));
    assert!(!frame_has_numeric_id(
        "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"result\":null}",
        1
    ));
}

#[test]
fn public_surface_no_mock_e2e() -> Result<(), String> {
    let run = pin::RigRun::new(pin::PinRig::PublicSurfaceNoMockE2e);
    let Some(lean) = pin::pinned_lean() else {
        let notice = run.typed_skip()?;
        eprintln!("{notice}");
        return Ok(());
    };
    let root = pin::workspace_root();
    let contract = PublicSurfaceContract::load_embedded().map_err(|error| error.to_string())?;
    if pin::pinned_tag().as_deref() != Some(contract.reference.tag.as_str())
        || pin::pinned_commit().as_deref() != Some(contract.reference.commit.as_str())
    {
        return Err("PublicSurface contract and SUITE.lock name different References".to_string());
    }
    for dependency in [
        pin::PinRig::CliLakeCensusNoMockE2e,
        pin::PinRig::LspCensusNoMockE2e,
        pin::PinRig::PinOptionDefaults,
    ] {
        if !pin::PinRig::ALL.contains(&dependency) {
            return Err(format!(
                "PublicSurface input rig {} is not registered",
                dependency.identity()
            ));
        }
    }

    let (toolchain_root, binaries) = toolchain_binaries(&lean)?;
    let path = toolchain_path(&lean)?;
    let (first, first_elapsed) =
        run_pass(&contract, &lean, &binaries, &toolchain_root, &path, &root)?;
    let (second, second_elapsed) =
        run_pass(&contract, &lean, &binaries, &toolchain_root, &path, &root)?;
    if first != second {
        return Err(
            "two fresh PublicSurface process joins produced different semantics".to_string(),
        );
    }
    if first.len() != 5 || first_elapsed.len() != first.len() || second_elapsed.len() != first.len()
    {
        return Err("PublicSurface real-process join population is incomplete".to_string());
    }

    let epoch = format!("{}@{}", contract.reference.tag, contract.reference.commit);
    let semantic = first
        .iter()
        .enumerate()
        .map(|(sequence, observation)| {
            let platform = contract
                .domain(&observation.domain)
                .map(|domain| domain.platform.clone())
                .ok_or_else(|| {
                    format!(
                        "real-process observation names absent domain {}",
                        observation.domain
                    )
                })?;
            Ok(SemanticRecord {
                run_id: "public-surface-no-mock-e2e".to_string(),
                sequence,
                domain: observation.domain.clone(),
                row: observation.key.clone(),
                epoch: epoch.clone(),
                platform,
                client: observation.client.clone(),
                profile: "faithful,sound".to_string(),
                mode: "all".to_string(),
                fixture: "public-surface-no-mock-e2e".to_string(),
                comparison: "exact-two-pass".to_string(),
                authority: observation.authority.clone(),
                input_root: observation.input_root.clone(),
                output_root: observation.output_root.clone(),
                expected: observation.expected.clone(),
                actual: observation.actual.clone(),
                resource_class: "bounded-process".to_string(),
                resource_used: 2,
                disposition: SemanticDisposition::Accepted,
                decision: "record".to_string(),
                cleanup: "complete".to_string(),
                final_state: "two-pass-match".to_string(),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let telemetry = first
        .iter()
        .zip(first_elapsed.iter().zip(&second_elapsed))
        .enumerate()
        .map(
            |(sequence, (observation, (first_duration, second_duration)))| TelemetryRecord {
                run_id: "public-surface-no-mock-e2e".to_string(),
                sequence,
                host: format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH),
                pid: std::process::id(),
                worker: sequence,
                elapsed_micros: (*first_duration).saturating_add(*second_duration),
                path: lean.display().to_string(),
                cache: "unclassified".to_string(),
                detail: format!("{}:{}", observation.domain, observation.key),
            },
        )
        .collect::<Vec<_>>();
    let bundle = EvidenceBundle::new(semantic, telemetry).map_err(|error| error.to_string())?;
    let reparsed =
        EvidenceBundle::from_ndjson(&bundle.semantic_ndjson(), &bundle.telemetry_ndjson())
            .map_err(|error| error.to_string())?;
    if reparsed.semantic_root() != bundle.semantic_root()
        || reparsed.telemetry_root() != bundle.telemetry_root()
        || bundle.semantic_root() == bundle.telemetry_root()
    {
        return Err(
            "strict PublicSurface semantic/telemetry evidence did not round-trip".to_string(),
        );
    }
    run.executed()
}
