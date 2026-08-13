//! **fln-cli** — front-door diagnostic adapters for the `lean`/`leanc`/`lake`
//! personalities and the `fln` multiplexer (plan §17.1; bead
//! `franken_lean-wlan`).
//!
//! `fln-core` supplies a typed [`ProjectionSnapshot`]. This crate owns the CLI
//! framing and JSON/NDJSON bytes. The bytes never become authority: exit class,
//! cause, positions, related spans, evidence links, and truncation markers all
//! remain bound to the snapshot returned beside them.

#![forbid(unsafe_code)]

use fln_core::diag::{
    DIAGNOSTIC_PROJECTION_SCHEMA, DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME, DiagnosticChannel,
    DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, DiagnosticPathPolicy, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity,
    StructuredDiagnostic, StructuredInconclusive, StructuredInternalFault,
};
use fln_core::mode::Mode;
use fln_core::outcome::BoundedText;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};

/// Default whole-file ceiling for `fln olean inspect`.
///
/// The largest pinned module is far smaller than this. Keeping the ceiling
/// explicit prevents an accidental path to an unbounded `read_to_end` before
/// the codec's own structural budgets take over.
pub const OLEAN_INSPECT_DEFAULT_MAX_BYTES: usize = 512 * 1024 * 1024;

/// Default aggregate source ceiling for the current bounded source runner.
pub const SOURCE_RUN_DEFAULT_MAX_BYTES: usize = 1024 * 1024;

/// Native stack provided to the kernel worker used by `fln run`.
const SOURCE_RUN_KERNEL_STACK_BYTES: usize = 2 * 1024 * 1024;

const OLEAN_INSPECT_SCHEMA: &str = "fln.olean-inspect/1";
const OLEAN_REBUILD_SCHEMA: &str = "fln.olean-rebuild/1";
const CHECK_OLEAN_SCHEMA: &str = "fln.check-olean/1";
const FLBC_RUN_SCHEMA: &str = "fln.flbc-run/2";
const SOURCE_RUN_SCHEMA: &str = "fln.source-run/4";
const PRODUCT_SIDECAR_MAX_BYTES: usize = 64 * 1024;
const TOOLCHAIN_IMAGE_MAX_BYTES: usize = 512 * 1024 * 1024;

const USAGE: &str = concat!(
    "Usage:\n",
    "  fln check-olean [--json] [--max-bytes BYTES] PATH\n",
    "  fln run [--json] [--max-bytes BYTES] [--emit-flbc PATH] [--emit-sidecar PATH] PATH...\n",
    "  fln flbc run [--json] [--max-bytes BYTES] [--sidecar PATH] PATH\n",
    "  fln olean inspect [--json] [--max-bytes BYTES] PATH\n",
    "  fln olean verify-rebuild [--json] [--max-bytes BYTES] PATH\n",
    "  fln --help\n",
    "  fln --version\n",
    "\n",
    "`olean inspect` audits and decodes one pinned-format .olean. It does not\n",
    "resolve imports, kernel-check declarations, or re-emit an artifact.\n",
    "`olean verify-rebuild` re-derives one pinned-format .olean from parsed\n",
    "semantics and requires byte identity with no codec findings. It is not\n",
    "fresh emission and does not kernel-check declarations.\n",
    "`check-olean` checks every declaration in one import-free pinned-format\n",
    ".olean, or a directory containing a closed import set, through K1 and the\n",
    "independent checker, atomically. It derives dependency order but does not\n",
    "reconstruct inductive/quotient or mutual units, interpret extensions, run\n",
    "K2, or satisfy G1. Module-system inputs load complete .olean.server and\n",
    ".olean.private companion chains and refuse an incomplete chain.\n",
    "\n",
    "`run` executes supported Nat definitions from each path, in dependency order,\n",
    "through the native parser, elaborator, K1, independent checker, compiler,\n",
    "and Golem. The final path must produce the closed Nat result to report. The\n",
    "batch is atomic, and --max-bytes bounds all source inputs together. With\n",
    "--emit-flbc, the final definition's exact executed artifact is published\n",
    "only after the whole batch succeeds; any existing PATH is refused, never\n",
    "replaced. --emit-sidecar requires\n",
    "--emit-flbc and publishes a standard-profile closure manifest before the\n",
    "product, so any interrupted pair fails closed by root mismatch. It is not\n",
    "general Lean,\n",
    "Prelude/import processing, a project build, a certified build product, or\n",
    "evidence that `check-olean` is complete.\n",
    "\n",
    "`flbc run` validates and executes one canonical FLBC artifact through Golem.\n",
    "With --sidecar it first binds the exact artifact, current toolchain image,\n",
    "mode, epoch, target, profile, and static closure inputs. The v1 sidecar is\n",
    "standard-profile provenance, not certified source reproducibility. It does\n",
    "not admit declarations or prove how the artifact was compiled.\n",
);

/// Complete process result produced by the `fln` multiplexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiplexerOutput {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: u8,
}

impl MultiplexerOutput {
    fn success(stdout: String) -> Self {
        Self {
            stdout,
            stderr: String::new(),
            exit_code: 0,
        }
    }

    fn failure(stderr: String, exit_code: u8) -> Self {
        Self {
            stdout: String::new(),
            stderr,
            exit_code,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum MultiplexerCommand {
    Help,
    Version,
    CheckOlean {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    SourceRun {
        paths: Vec<PathBuf>,
        max_bytes: usize,
        json: bool,
        emit_flbc: Option<PathBuf>,
        emit_sidecar: Option<PathBuf>,
    },
    FlbcRun {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
        sidecar: Option<PathBuf>,
    },
    OleanInspect {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    OleanVerifyRebuild {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
}

#[derive(Debug)]
enum BoundedReadFailure {
    Input {
        subject: &'static str,
        detail: String,
    },
    TooLarge {
        subject: &'static str,
        observed: usize,
        limit: usize,
    },
    Allocation {
        subject: &'static str,
        requested: usize,
    },
}

impl BoundedReadFailure {
    const fn class(&self) -> &'static str {
        match self {
            Self::Input { .. } => "input",
            Self::TooLarge { .. } | Self::Allocation { .. } => "resource",
        }
    }
}

impl fmt::Display for BoundedReadFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input { subject, detail } => write!(f, "could not read {subject}: {detail}"),
            Self::TooLarge {
                subject,
                observed,
                limit,
            } => write!(
                f,
                "{subject} exceeded the {limit}-byte input limit after reading {observed} bytes"
            ),
            Self::Allocation { subject, requested } => write!(
                f,
                "could not reserve memory for {requested} bytes of bounded {subject} input"
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UsageError(String);

impl fmt::Display for UsageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Debug)]
enum OleanInspectFailure {
    Read(BoundedReadFailure),
    Decode(fln::OleanDecodeError),
}

impl OleanInspectFailure {
    const fn class(&self) -> &'static str {
        match self {
            Self::Read(error) => error.class(),
            Self::Decode(error) if error.is_resource_exhaustion() => "resource",
            Self::Decode(_) => "decode",
        }
    }
}

impl fmt::Display for OleanInspectFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(error) => write!(f, "{error}"),
            Self::Decode(error) => write!(f, "{error}"),
        }
    }
}

fn parse_byte_limit(value: &OsString) -> Result<usize, UsageError> {
    let Some(value) = value.to_str() else {
        return Err(UsageError(
            "--max-bytes requires an ASCII integer".to_owned(),
        ));
    };
    let parsed = value.parse::<u64>().map_err(|_| {
        UsageError(format!(
            "invalid --max-bytes value {value:?}; expected a non-negative integer"
        ))
    })?;
    usize::try_from(parsed).map_err(|_| {
        UsageError(format!(
            "--max-bytes value {parsed} does not fit this platform"
        ))
    })
}

fn parse_path_options(
    arguments: Vec<OsString>,
    command: &'static str,
    default_max_bytes: usize,
) -> Result<Option<(Vec<PathBuf>, usize, bool)>, UsageError> {
    let mut paths = Vec::new();
    let mut max_bytes = default_max_bytes;
    let mut json = false;
    let mut options = true;
    let mut arguments = arguments.into_iter();

    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && (argument == "--help" || argument == "-h") {
            return Ok(None);
        }
        if options && argument == "--json" {
            json = true;
            continue;
        }
        if options && argument == "--max-bytes" {
            let value = arguments
                .next()
                .ok_or_else(|| UsageError("--max-bytes requires a following integer".to_owned()))?;
            max_bytes = parse_byte_limit(&value)?;
            continue;
        }
        if options
            && let Some(value) = argument
                .to_str()
                .and_then(|value| value.strip_prefix("--max-bytes="))
        {
            max_bytes = parse_byte_limit(&OsString::from(value))?;
            continue;
        }
        if options && argument.to_string_lossy().starts_with('-') {
            return Err(UsageError(format!(
                "unknown {command} option {:?}",
                argument.to_string_lossy()
            )));
        }
        paths.push(PathBuf::from(argument));
    }

    if paths.is_empty() {
        return Err(UsageError(format!("{command} requires PATH")));
    }
    Ok(Some((paths, max_bytes, json)))
}

fn parse_source_run(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut filtered = Vec::new();
    let mut emit_flbc = None;
    let mut emit_sidecar = None;
    let mut options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            filtered.push(argument);
            continue;
        }
        if options && (argument == "--help" || argument == "-h") {
            return Ok(MultiplexerCommand::Help);
        }
        let sidecar = if options && argument == "--emit-sidecar" {
            Some(arguments.next().ok_or_else(|| {
                UsageError("--emit-sidecar requires a following output path".to_owned())
            })?)
        } else if options {
            argument
                .to_str()
                .and_then(|value| value.strip_prefix("--emit-sidecar="))
                .map(OsString::from)
        } else {
            None
        };
        if let Some(path) = sidecar {
            if path.is_empty() {
                return Err(UsageError(
                    "--emit-sidecar path must not be empty".to_owned(),
                ));
            }
            if emit_sidecar.replace(PathBuf::from(path)).is_some() {
                return Err(UsageError(
                    "--emit-sidecar may be supplied at most once".to_owned(),
                ));
            }
            continue;
        }
        let emitted = if options && argument == "--emit-flbc" {
            Some(arguments.next().ok_or_else(|| {
                UsageError("--emit-flbc requires a following output path".to_owned())
            })?)
        } else if options {
            argument
                .to_str()
                .and_then(|value| value.strip_prefix("--emit-flbc="))
                .map(OsString::from)
        } else {
            None
        };
        if let Some(path) = emitted {
            if path.is_empty() {
                return Err(UsageError("--emit-flbc path must not be empty".to_owned()));
            }
            if emit_flbc.replace(PathBuf::from(path)).is_some() {
                return Err(UsageError(
                    "--emit-flbc may be supplied at most once".to_owned(),
                ));
            }
            continue;
        }
        filtered.push(argument);
    }
    let Some((paths, max_bytes, json)) =
        parse_path_options(filtered, "run", SOURCE_RUN_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    if emit_sidecar.is_some() && emit_flbc.is_none() {
        return Err(UsageError(
            "--emit-sidecar requires --emit-flbc so the manifest has a published product"
                .to_owned(),
        ));
    }
    if emit_sidecar
        .as_deref()
        .zip(emit_flbc.as_deref())
        .is_some_and(|(sidecar, product)| output_paths_alias(sidecar, product))
    {
        return Err(UsageError(
            "--emit-sidecar and --emit-flbc must name different paths".to_owned(),
        ));
    }
    for output in [emit_flbc.as_deref(), emit_sidecar.as_deref()]
        .into_iter()
        .flatten()
    {
        if let Some(source) = paths
            .iter()
            .find(|source| output_paths_alias(output, source))
        {
            return Err(UsageError(format!(
                "output path {} aliases source input {}",
                output.display(),
                source.display()
            )));
        }
    }
    Ok(MultiplexerCommand::SourceRun {
        paths,
        max_bytes,
        json,
        emit_flbc,
        emit_sidecar,
    })
}

fn output_paths_alias(left: &Path, right: &Path) -> bool {
    if left == right {
        return true;
    }
    let identity = |path: &Path| {
        let file_name = path.file_name()?;
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        std::fs::canonicalize(parent)
            .ok()
            .map(|parent| parent.join(file_name))
    };
    identity(left)
        .zip(identity(right))
        .is_some_and(|pair| pair.0 == pair.1)
}

fn parse_check_olean(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((paths, max_bytes, json)) =
        parse_path_options(arguments, "check-olean", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "check-olean accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::CheckOlean {
        path: path.clone(),
        max_bytes,
        json,
    })
}

fn parse_flbc_run(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut filtered = Vec::new();
    let mut sidecar = None;
    let mut options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            filtered.push(argument);
            continue;
        }
        let selected = if options && argument == "--sidecar" {
            Some(arguments.next().ok_or_else(|| {
                UsageError("--sidecar requires a following input path".to_owned())
            })?)
        } else if options {
            argument
                .to_str()
                .and_then(|value| value.strip_prefix("--sidecar="))
                .map(OsString::from)
        } else {
            None
        };
        if let Some(path) = selected {
            if path.is_empty() {
                return Err(UsageError("--sidecar path must not be empty".to_owned()));
            }
            if sidecar.replace(PathBuf::from(path)).is_some() {
                return Err(UsageError(
                    "--sidecar may be supplied at most once".to_owned(),
                ));
            }
            continue;
        }
        filtered.push(argument);
    }
    let Some((paths, max_bytes, json)) = parse_path_options(
        filtered,
        "flbc run",
        fln::CodecLimits::default().max_artifact_bytes,
    )?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "flbc run accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::FlbcRun {
        path: path.clone(),
        max_bytes,
        json,
        sidecar,
    })
}

fn parse_olean_inspect(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((paths, max_bytes, json)) =
        parse_path_options(arguments, "olean inspect", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "olean inspect accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::OleanInspect {
        path: path.clone(),
        max_bytes,
        json,
    })
}

fn parse_olean_verify_rebuild(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((paths, max_bytes, json)) = parse_path_options(
        arguments,
        "olean verify-rebuild",
        OLEAN_INSPECT_DEFAULT_MAX_BYTES,
    )?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "olean verify-rebuild accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::OleanVerifyRebuild {
        path: path.clone(),
        max_bytes,
        json,
    })
}

fn parse_command(
    arguments: impl IntoIterator<Item = OsString>,
) -> Result<MultiplexerCommand, UsageError> {
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        return Ok(MultiplexerCommand::Help);
    };
    if command == "--help" || command == "-h" || command == "help" {
        return Ok(MultiplexerCommand::Help);
    }
    if command == "--version" || command == "-V" || command == "version" {
        return Ok(MultiplexerCommand::Version);
    }
    if command == "run" {
        return parse_source_run(arguments.collect());
    }
    if command == "check-olean" {
        return parse_check_olean(arguments.collect());
    }
    if command == "flbc" {
        let Some(subcommand) = arguments.next() else {
            return Err(UsageError("flbc requires the `run` subcommand".to_owned()));
        };
        if subcommand == "--help" || subcommand == "-h" || subcommand == "help" {
            return Ok(MultiplexerCommand::Help);
        }
        if subcommand == "run" {
            return parse_flbc_run(arguments.collect());
        }
        return Err(UsageError(format!(
            "unknown flbc subcommand {:?}",
            subcommand.to_string_lossy()
        )));
    }
    if command != "olean" {
        return Err(UsageError(format!(
            "unknown fln command {:?}",
            command.to_string_lossy()
        )));
    }
    let Some(subcommand) = arguments.next() else {
        return Err(UsageError(
            "olean requires the `inspect` subcommand".to_owned(),
        ));
    };
    if subcommand == "--help" || subcommand == "-h" || subcommand == "help" {
        return Ok(MultiplexerCommand::Help);
    }
    if subcommand == "inspect" {
        return parse_olean_inspect(arguments.collect());
    }
    if subcommand == "verify-rebuild" {
        return parse_olean_verify_rebuild(arguments.collect());
    }
    Err(UsageError(format!(
        "unknown olean subcommand {:?}",
        subcommand.to_string_lossy()
    )))
}

fn read_bounded_from(
    reader: &mut impl Read,
    max_bytes: usize,
    subject: &'static str,
) -> Result<Vec<u8>, BoundedReadFailure> {
    let mut bytes = Vec::new();
    let mut chunk = [0_u8; 8192];
    loop {
        let read = match reader.read(&mut chunk) {
            Ok(read) => read,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => {
                return Err(BoundedReadFailure::Input {
                    subject,
                    detail: error.to_string(),
                });
            }
        };
        if read == 0 {
            return Ok(bytes);
        }
        let observed = bytes.len().saturating_add(read);
        if observed > max_bytes {
            return Err(BoundedReadFailure::TooLarge {
                subject,
                observed,
                limit: max_bytes,
            });
        }
        bytes
            .try_reserve_exact(read)
            .map_err(|_| BoundedReadFailure::Allocation {
                subject,
                requested: observed,
            })?;
        bytes.extend_from_slice(&chunk[..read]);
    }
}

fn read_bounded(
    path: &Path,
    max_bytes: usize,
    subject: &'static str,
) -> Result<Vec<u8>, BoundedReadFailure> {
    let mut file = std::fs::File::open(path).map_err(|error| BoundedReadFailure::Input {
        subject,
        detail: format!("cannot open {}: {error}", path.display()),
    })?;
    read_bounded_from(&mut file, max_bytes, subject)
}

fn vm_value_kind_name(kind: fln::VmValueKind) -> String {
    match kind {
        fln::VmValueKind::Scalar => "scalar".to_owned(),
        fln::VmValueKind::Ctor(tag) => format!("constructor:{tag}"),
        fln::VmValueKind::Promise => "promise".to_owned(),
        fln::VmValueKind::Closure => "closure".to_owned(),
        fln::VmValueKind::Array => "array".to_owned(),
        fln::VmValueKind::StructArray => "struct-array".to_owned(),
        fln::VmValueKind::ScalarArray => "scalar-array".to_owned(),
        fln::VmValueKind::String => "string".to_owned(),
        fln::VmValueKind::Mpz => "mpz".to_owned(),
        fln::VmValueKind::Thunk => "thunk".to_owned(),
        fln::VmValueKind::Task => "task".to_owned(),
        fln::VmValueKind::Ref => "reference".to_owned(),
        fln::VmValueKind::External => "external".to_owned(),
        fln::VmValueKind::Reserved => "reserved".to_owned(),
    }
}

fn root_hex(root: fln::ContentRoot) -> String {
    let mut rendered = String::with_capacity(64);
    for byte in root.bytes() {
        rendered.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble < 16"));
        rendered.push(char::from_digit(u32::from(byte & 0x0f), 16).expect("nibble < 16"));
    }
    rendered
}

fn render_flbc_success(
    bytes: usize,
    returned: &fln::VmExit,
    sidecar: Option<&fln::FlbcProductSidecarV1>,
    json: bool,
) -> MultiplexerOutput {
    let fln::VmExit::Returned(returned) = returned else {
        return flbc_failure(
            "internal-fault",
            "non-returning VM exit reached the FLBC success renderer",
            false,
            None,
            json,
            4,
        );
    };
    let kind = vm_value_kind_name(fln::vm_value_kind(&returned.value));
    let scalar = returned.value.is_scalar().then(|| returned.value.unbox());
    let usage = (
        returned.usage.steps,
        returned.usage.system_polls,
        returned.usage.peak_stack_depth,
    );
    let stdout = if json {
        let value = scalar
            .map(|value| value.to_string())
            .unwrap_or_else(|| "null".to_owned());
        let sidecar = sidecar.map_or_else(
            || "null".to_owned(),
            |sidecar| {
                format!(
                    concat!(
                        "{{\"verified\":true,\"mode\":\"sound\",",
                        "\"profile\":\"standard\",\"closureRoot\":{},",
                        "\"productRoot\":{}}}"
                    ),
                    json_string(&root_hex(sidecar.closure_root())),
                    json_string(&root_hex(sidecar.product_root())),
                )
            },
        );
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"artifactBytes\":{},\"returnKind\":{},\"scalarValue\":{},",
                "\"sidecar\":{},",
                "\"execution\":{{\"steps\":{},\"systemPolls\":{},",
                "\"peakStackDepth\":{}}}}}\n"
            ),
            json_string(FLBC_RUN_SCHEMA),
            bytes,
            json_string(&kind),
            value,
            sidecar,
            usage.0,
            usage.1,
            usage.2,
        )
    } else {
        let value = scalar
            .map(|value| value.to_string())
            .unwrap_or_else(|| "not a scalar".to_owned());
        let sidecar = sidecar.map_or_else(String::new, |sidecar| {
            format!(
                concat!(
                    "sidecar: verified sound/standard\n",
                    "closure root: {}\n",
                    "product root: {}\n"
                ),
                root_hex(sidecar.closure_root()),
                root_hex(sidecar.product_root()),
            )
        });
        format!(
            concat!(
                "canonical FLBC execution: complete\n",
                "artifact bytes: {}\n",
                "return kind: {}\n",
                "scalar value: {}\n",
                "{}",
                "execution: {} steps, {} system polls, peak stack {}\n"
            ),
            bytes, kind, value, sidecar, usage.0, usage.1, usage.2,
        )
    };
    MultiplexerOutput::success(stdout)
}

fn flbc_failure(
    class: &'static str,
    detail: &str,
    authority: bool,
    usage: Option<(u64, u64, u64)>,
    json: bool,
    exit_code: u8,
) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        let usage = usage
            .map(|(steps, polls, peak)| {
                format!("{{\"steps\":{steps},\"systemPolls\":{polls},\"peakStackDepth\":{peak}}}")
            })
            .unwrap_or_else(|| "null".to_owned());
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":{},",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{},",
                "\"execution\":{}}}\n"
            ),
            json_string(FLBC_RUN_SCHEMA),
            authority,
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
            usage,
        )
    } else {
        let usage = usage
            .map(|(steps, polls, peak)| {
                format!("\nexecution: {steps} steps, {polls} system polls, peak stack {peak}")
            })
            .unwrap_or_default();
        let truncation = if detail.truncated() {
            format!("\n[detail truncated after {} bytes]", BoundedText::LIMIT)
        } else {
            String::new()
        };
        format!(
            "fln flbc run: {class}: {}{usage}{truncation}\n",
            detail.text()
        )
    };
    MultiplexerOutput::failure(stderr, exit_code)
}

fn execute_flbc_bytes_with_sidecar(
    bytes: &[u8],
    max_bytes: usize,
    sidecar: Option<&fln::FlbcProductSidecarV1>,
    json: bool,
) -> MultiplexerOutput {
    let mut limits = fln::FlbcExecutionLimits::default();
    limits.codec.max_artifact_bytes = max_bytes;
    let outcome = match fln::execute_flbc_artifact(bytes, &fln::KVMap::new(), limits) {
        Ok(outcome) => outcome,
        Err(error) => {
            let (class, authority, exit_code) = match error {
                fln::CodecError::ResourceLimit { .. }
                | fln::CodecError::AllocationFailure { .. } => ("resource", false, 3),
                _ => ("codec", true, 1),
            };
            return flbc_failure(class, &error.to_string(), authority, None, json, exit_code);
        }
    };
    match outcome {
        fln::Outcome::Complete(exit @ fln::VmExit::Returned(_)) => {
            render_flbc_success(bytes.len(), &exit, sidecar, json)
        }
        fln::Outcome::Complete(fln::VmExit::Panicked { message, usage }) => flbc_failure(
            "program-panic",
            &message,
            true,
            Some((usage.steps, usage.system_polls, usage.peak_stack_depth)),
            json,
            1,
        ),
        fln::Outcome::Complete(fln::VmExit::Refused { refusal, usage }) => flbc_failure(
            "vm-refusal",
            &refusal.to_string(),
            true,
            Some((usage.steps, usage.system_polls, usage.peak_stack_depth)),
            json,
            1,
        ),
        fln::Outcome::Inconclusive(inconclusive) => flbc_failure(
            "inconclusive",
            &format!("{inconclusive:?}"),
            false,
            None,
            json,
            3,
        ),
        fln::Outcome::InternalFault(fault) => flbc_failure(
            "internal-fault",
            &format!("{fault:?}"),
            false,
            None,
            json,
            4,
        ),
    }
}

#[cfg(test)]
fn execute_flbc_bytes(bytes: &[u8], max_bytes: usize, json: bool) -> MultiplexerOutput {
    execute_flbc_bytes_with_sidecar(bytes, max_bytes, None, json)
}

fn read_current_toolchain_image() -> Result<Vec<u8>, BoundedReadFailure> {
    // The v1 producer is registered only for Linux. `/proc/self/exe` keeps the
    // executing inode open even if the pathname returned by `current_exe` is
    // replaced concurrently, so the sidecar binds the producer that is actually
    // running rather than whatever later appeared at the same filesystem name.
    #[cfg(target_os = "linux")]
    let path = PathBuf::from("/proc/self/exe");
    #[cfg(not(target_os = "linux"))]
    let path = std::env::current_exe().map_err(|error| BoundedReadFailure::Input {
        subject: "current toolchain image",
        detail: error.to_string(),
    })?;
    read_bounded(&path, TOOLCHAIN_IMAGE_MAX_BYTES, "current toolchain image")
}

fn run_flbc(
    path: &Path,
    max_bytes: usize,
    sidecar_path: Option<&Path>,
    json: bool,
) -> MultiplexerOutput {
    let bytes = match read_bounded(path, max_bytes, "FLBC artifact") {
        Ok(bytes) => bytes,
        Err(error) => {
            let class = error.class();
            return flbc_failure(
                class,
                &error.to_string(),
                false,
                None,
                json,
                if class == "resource" { 3 } else { 1 },
            );
        }
    };
    let verified_sidecar = if let Some(sidecar_path) = sidecar_path {
        let sidecar_bytes = match read_bounded(
            sidecar_path,
            PRODUCT_SIDECAR_MAX_BYTES,
            "FLBC product sidecar",
        ) {
            Ok(bytes) => bytes,
            Err(error) => {
                let class = error.class();
                return flbc_failure(
                    class,
                    &error.to_string(),
                    false,
                    None,
                    json,
                    if class == "resource" { 3 } else { 1 },
                );
            }
        };
        let toolchain_image = match read_current_toolchain_image() {
            Ok(bytes) => bytes,
            Err(error) => {
                return flbc_failure("internal-fault", &error.to_string(), false, None, json, 4);
            }
        };
        match fln::verify_source_run_flbc_sidecar(&sidecar_bytes, &bytes, &toolchain_image) {
            Ok(sidecar) => Some(sidecar),
            Err(error) => {
                return flbc_failure("sidecar", &error.to_string(), true, None, json, 1);
            }
        }
    } else {
        None
    };
    execute_flbc_bytes_with_sidecar(&bytes, max_bytes, verified_sidecar.as_ref(), json)
}

fn render_olean_human(bytes: usize, decoded: &fln::DecodedOlean) -> String {
    format!(
        concat!(
            "pinned .olean audit: complete\n",
            "bytes: {}\n",
            "format version: {}\n",
            "lean version: {}\n",
            "reference commit: {}\n",
            "flags: 0x{:02x}\n",
            "base address: {}\n",
            "module: {}\n",
            "imports: {}\n",
            "constants: {}\n",
            "extension blocks: {}\n",
            "reachable objects: {}\n"
        ),
        bytes,
        decoded.header.version,
        decoded.header.lean_version,
        decoded.header.githash,
        decoded.header.flags,
        decoded.header.base_addr,
        decoded.module.is_module,
        decoded.module.imports.len(),
        decoded.constants.len(),
        decoded.module.extensions.len(),
        decoded.walk.objects,
    )
}

fn render_olean_json(bytes: usize, decoded: &fln::DecodedOlean) -> String {
    format!(
        concat!(
            "{{\"schema\":{},\"outcome\":\"complete\",\"bytes\":{},",
            "\"header\":{{\"version\":{},\"leanVersion\":{},\"githash\":{},",
            "\"flags\":{},\"baseAddress\":{}}},",
            "\"module\":{{\"isModule\":{},\"imports\":{},\"constantNames\":{},",
            "\"constants\":{},\"decodedConstants\":{},\"extraConstantNames\":{},",
            "\"extensionBlocks\":{}}},",
            "\"walk\":{{\"objects\":{},\"constructors\":{},\"arrays\":{},",
            "\"scalarArrays\":{},\"strings\":{},\"bigIntegers\":{},",
            "\"thunks\":{},\"tasks\":{},\"references\":{},\"scalarReferences\":{}}}}}\n"
        ),
        json_string(OLEAN_INSPECT_SCHEMA),
        bytes,
        decoded.header.version,
        json_string(&decoded.header.lean_version),
        json_string(&decoded.header.githash),
        decoded.header.flags,
        decoded.header.base_addr,
        decoded.module.is_module,
        decoded.module.imports.len(),
        decoded.module.const_names.len(),
        decoded.module.constants,
        decoded.constants.len(),
        decoded.module.extra_const_names,
        decoded.module.extensions.len(),
        decoded.walk.objects,
        decoded.walk.ctors,
        decoded.walk.arrays,
        decoded.walk.scalar_arrays,
        decoded.walk.strings,
        decoded.walk.mpz,
        decoded.walk.thunks,
        decoded.walk.tasks,
        decoded.walk.refs,
        decoded.walk.scalar_refs,
    )
}

fn inspect_olean_bytes(bytes: &[u8], max_bytes: usize, json: bool) -> MultiplexerOutput {
    match fln::decode_olean_artifact(bytes, fln::OleanDecodeLimits::new(max_bytes)) {
        Ok(decoded) => MultiplexerOutput::success(if json {
            render_olean_json(bytes.len(), &decoded)
        } else {
            render_olean_human(bytes.len(), &decoded)
        }),
        Err(error) => inspect_failure(OleanInspectFailure::Decode(error), json),
    }
}

fn inspect_failure(error: OleanInspectFailure, json: bool) -> MultiplexerOutput {
    let detail = error.to_string();
    let class = error.class();
    let stderr = if json {
        format!(
            "{{\"schema\":{},\"outcome\":\"error\",\"class\":{},\"detail\":{}}}\n",
            json_string(OLEAN_INSPECT_SCHEMA),
            json_string(class),
            json_string(&detail),
        )
    } else {
        format!("fln olean inspect: {detail}\n")
    };
    MultiplexerOutput::failure(stderr, if class == "resource" { 3 } else { 1 })
}

fn inspect_olean(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    match read_bounded(path, max_bytes, ".olean artifact") {
        Ok(bytes) => inspect_olean_bytes(&bytes, max_bytes, json),
        Err(error) => inspect_failure(OleanInspectFailure::Read(error), json),
    }
}

fn render_olean_rebuild_success(
    bytes: usize,
    report: &fln::OleanRebuildReport,
    json: bool,
) -> MultiplexerOutput {
    let Some(copied_content_bytes) = report
        .copied_string_bytes
        .checked_add(report.copied_sarray_bytes)
        .and_then(|total| total.checked_add(report.copied_ctor_tail_bytes))
        .and_then(|total| total.checked_add(report.copied_mpz_limb_bytes))
    else {
        return olean_rebuild_failure(
            "internal-fault",
            "rebuild report content-byte accounting overflowed",
            json,
            4,
        );
    };
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"bytes\":{},",
                "\"byteIdentity\":true,\"objects\":{},",
                "\"accounting\":{{\"rederivedBytes\":{},",
                "\"copiedContentBytes\":{},\"paddingBytes\":{},",
                "\"nonzeroPaddingBytes\":{},\"slackBytes\":{}}},",
                "\"findings\":0}}\n"
            ),
            json_string(OLEAN_REBUILD_SCHEMA),
            bytes,
            report.objects,
            report.rederived_bytes,
            copied_content_bytes,
            report.padding_bytes,
            report.nonzero_padding_bytes,
            report.slack_bytes,
        )
    } else {
        format!(
            concat!(
                "pinned .olean rebuild audit: complete\n",
                "bytes: {}\n",
                "byte identity: exact\n",
                "objects: {}\n",
                "re-derived bytes: {}\n",
                "declared content bytes: {}\n",
                "padding bytes: {} ({} nonzero)\n",
                "capacity slack bytes: {}\n",
                "findings: 0\n"
            ),
            bytes,
            report.objects,
            report.rederived_bytes,
            copied_content_bytes,
            report.padding_bytes,
            report.nonzero_padding_bytes,
            report.slack_bytes,
        )
    };
    MultiplexerOutput::success(stdout)
}

fn olean_rebuild_failure(
    class: &'static str,
    detail: &str,
    json: bool,
    exit_code: u8,
) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"class\":{},",
                "\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(OLEAN_REBUILD_SCHEMA),
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        let truncation = if detail.truncated() {
            format!("\n[detail truncated after {} bytes]", BoundedText::LIMIT)
        } else {
            String::new()
        };
        format!(
            "fln olean verify-rebuild: {class}: {}{truncation}\n",
            detail.text()
        )
    };
    MultiplexerOutput::failure(stderr, exit_code)
}

fn olean_rebuild_error_class(error: &fln::OleanRebuildError) -> (&'static str, u8) {
    match error {
        fln::OleanRebuildError::ArtifactTooLarge { .. }
        | fln::OleanRebuildError::Region(fln::OleanRegionError::BudgetExhausted { .. }) => {
            ("resource", 3)
        }
        fln::OleanRebuildError::Region(_) => ("rebuild", 1),
    }
}

fn first_byte_difference(left: &[u8], right: &[u8]) -> Option<usize> {
    left.iter()
        .zip(right)
        .position(|(left, right)| left != right)
        .or_else(|| (left.len() != right.len()).then(|| left.len().min(right.len())))
}

fn verify_olean_rebuild_bytes(bytes: &[u8], max_bytes: usize, json: bool) -> MultiplexerOutput {
    let (rebuilt, report) = match fln::rebuild_olean_artifact(bytes, max_bytes) {
        Ok(rebuilt) => rebuilt,
        Err(error) => {
            let (class, exit_code) = olean_rebuild_error_class(&error);
            return olean_rebuild_failure(class, &error.to_string(), json, exit_code);
        }
    };
    if let Some(offset) = first_byte_difference(bytes, &rebuilt) {
        return olean_rebuild_failure(
            "divergence",
            &format!(
                "re-derived artifact first differs at byte {offset}; input has {} bytes and rebuild has {} bytes",
                bytes.len(),
                rebuilt.len()
            ),
            json,
            1,
        );
    }
    if let Some(first) = report.findings.first() {
        return olean_rebuild_failure(
            "finding",
            &format!(
                "rebuild reported {} codec finding(s); first: {first}",
                report.findings.len()
            ),
            json,
            1,
        );
    }
    render_olean_rebuild_success(bytes.len(), &report, json)
}

fn verify_olean_rebuild(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    let bytes = match read_bounded(path, max_bytes, ".olean artifact") {
        Ok(bytes) => bytes,
        Err(error) => {
            let class = error.class();
            return olean_rebuild_failure(
                class,
                &error.to_string(),
                json,
                if class == "resource" { 3 } else { 1 },
            );
        }
    };
    verify_olean_rebuild_bytes(&bytes, max_bytes, json)
}

fn admission_error_disposition(error: &fln::EngineAdmissionError) -> (&'static str, bool, u8) {
    match error {
        fln::EngineAdmissionError::BatchDeclaration { error, .. } => {
            admission_error_disposition(error)
        }
        fln::EngineAdmissionError::AllocationFailure { .. } => ("resource", false, 3),
        fln::EngineAdmissionError::KernelRejected { .. } => ("kernel-rejection", true, 1),
        // A halt is "kernel accepted ∧ some seat objected". The objection may be
        // Disagrees, NoAnswer, Exhausted, or incomparable bounds. `run` already
        // renders the same variant as inconclusive; folding a checker non-answer
        // into checker-disagreement / exit 1 is an FL-INV-07 promotion.
        fln::EngineAdmissionError::CouncilHalted { .. } => ("inconclusive", false, 3),
        fln::EngineAdmissionError::CheckerBridge { .. }
        | fln::EngineAdmissionError::UnexpectedPublication { .. } => ("internal-fault", false, 4),
        fln::EngineAdmissionError::EmptyBatch
        | fln::EngineAdmissionError::UnsupportedDeclaration { .. }
        | fln::EngineAdmissionError::DuplicateName { .. } => ("admission", false, 1),
    }
}

fn check_olean_error_disposition(error: &fln::OleanCheckError) -> (&'static str, bool, u8) {
    match error {
        fln::OleanCheckError::Decode(error) | fln::OleanCheckError::ModuleDecode { error, .. }
            if error.is_resource_exhaustion() =>
        {
            ("resource", false, 3)
        }
        fln::OleanCheckError::ModuleLimit { .. }
        | fln::OleanCheckError::TotalBytesLimit { .. }
        | fln::OleanCheckError::DeclarationLimit { .. }
        | fln::OleanCheckError::DependencyPresentationLimit { .. }
        | fln::OleanCheckError::AllocationFailure { .. } => ("resource", false, 3),
        fln::OleanCheckError::Decode(_) | fln::OleanCheckError::ModuleDecode { .. } => {
            ("decode", false, 1)
        }
        fln::OleanCheckError::EmptyModuleSet
        | fln::OleanCheckError::MissingCompanionParts { .. } => ("input", false, 1),
        fln::OleanCheckError::ImportsRequireResolver { .. } => ("unresolved-imports", false, 1),
        fln::OleanCheckError::MissingModuleImports { .. } => ("unresolved-imports", false, 1),
        fln::OleanCheckError::DuplicateModule { .. }
        | fln::OleanCheckError::ModuleImportCycle { .. } => ("module-graph", false, 1),
        fln::OleanCheckError::InternalInvariant { .. } => ("internal-fault", false, 4),
        fln::OleanCheckError::UnsupportedDeclaration { .. }
        | fln::OleanCheckError::MutualEnvelopeUnsupported { .. } => {
            ("unsupported-declaration-unit", false, 1)
        }
        fln::OleanCheckError::DuplicateDeclaration { .. }
        | fln::OleanCheckError::MissingConstants { .. }
        | fln::OleanCheckError::DependencyCycle { .. } => ("declaration-closure", false, 1),
        fln::OleanCheckError::Admission(error) => admission_error_disposition(error),
    }
}

fn check_olean_failure(
    class: &'static str,
    detail: &str,
    authority: bool,
    json: bool,
    exit_code: u8,
) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":{},",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(CHECK_OLEAN_SCHEMA),
            authority,
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        let truncation = if detail.truncated() {
            format!("\n[detail truncated after {} bytes]", BoundedText::LIMIT)
        } else {
            String::new()
        };
        format!("fln check-olean: {class}: {}{truncation}\n", detail.text())
    };
    MultiplexerOutput::failure(stderr, exit_code)
}

fn render_check_olean_success(
    bytes: usize,
    checked: &fln::CheckedOlean,
    json: bool,
) -> MultiplexerOutput {
    let constants = checked.declarations.len();
    let extensions = checked.decoded.module.extensions.len();
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"scope\":\"decoded-declarations\",\"artifactBytes\":{},",
                "\"declarationsChecked\":{},\"dependencyOrderDerived\":true,",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"module\":{{\"isModulePart\":{},\"imports\":0,",
                "\"extensionBlocksObserved\":{},\"extensionsInterpreted\":false,",
                "\"companionPartsLoaded\":{}}},",
                "\"k2Checked\":false,\"g1Satisfied\":false}}\n"
            ),
            json_string(CHECK_OLEAN_SCHEMA),
            bytes,
            constants,
            json_string(&checked.base_logical_root.to_string()),
            json_string(&checked.result_logical_root.to_string()),
            checked.decoded.module.is_module,
            extensions,
            checked.decoded.companion_parts_loaded,
        )
    } else {
        format!(
            concat!(
                "standalone .olean declaration check: complete\n",
                "authority: K1 + independent checker\n",
                "artifact bytes: {}\n",
                "declarations checked: {}\n",
                "dependency order: derived\n",
                "base logical root: {}\n",
                "result logical root: {}\n",
                "extension blocks observed: {} (not interpreted)\n",
                "companion artifact parts loaded: {}\n",
                "K2 checked: no\n",
                "G1 satisfied: no\n"
            ),
            bytes,
            constants,
            checked.base_logical_root,
            checked.result_logical_root,
            extensions,
            if checked.decoded.companion_parts_loaded {
                "yes"
            } else {
                "no"
            },
        )
    };
    MultiplexerOutput::success(stdout)
}

#[cfg(test)]
fn check_olean_bytes(bytes: Vec<u8>, max_bytes: usize, json: bool) -> MultiplexerOutput {
    check_olean_part_bytes(bytes, None, None, max_bytes, json)
}

fn check_olean_part_bytes(
    bytes: Vec<u8>,
    server_bytes: Option<Vec<u8>>,
    private_bytes: Option<Vec<u8>>,
    max_bytes: usize,
    json: bool,
) -> MultiplexerOutput {
    let total_bytes = [
        Some(bytes.len()),
        server_bytes.as_ref().map(Vec::len),
        private_bytes.as_ref().map(Vec::len),
    ]
    .into_iter()
    .flatten()
    .fold(0_usize, usize::saturating_add);
    let worker = match std::thread::Builder::new()
        .name("fln-check-olean".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
        .spawn(move || {
            let engine = fln::Engine::from_environment(fln::Environment::new());
            match engine.check_olean_artifact_parts(
                &bytes,
                server_bytes.as_deref(),
                private_bytes.as_deref(),
                &fln::KVMap::new(),
                fln::OleanCheckLimits::new(
                    max_bytes,
                    fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
                ),
            ) {
                Ok(fln::Outcome::Complete(checked)) => {
                    render_check_olean_success(total_bytes, &checked, json)
                }
                Ok(fln::Outcome::Inconclusive(reason)) => {
                    check_olean_failure("inconclusive", &format!("{reason:?}"), false, json, 3)
                }
                Ok(fln::Outcome::InternalFault(fault)) => {
                    check_olean_failure("internal-fault", &format!("{fault:?}"), false, json, 4)
                }
                Err(error) => {
                    let (class, authority, exit_code) = check_olean_error_disposition(&error);
                    check_olean_failure(class, &error.to_string(), authority, json, exit_code)
                }
            }
        }) {
        Ok(worker) => worker,
        Err(error) => {
            return check_olean_failure(
                "internal-fault",
                &format!("could not start bounded kernel worker: {error}"),
                false,
                json,
                4,
            );
        }
    };
    match worker.join() {
        Ok(output) => output,
        Err(_) => check_olean_failure(
            "internal-fault",
            "bounded kernel worker panicked",
            false,
            json,
            4,
        ),
    }
}

fn read_optional_olean_companion(
    path: &Path,
    max_bytes: usize,
) -> Result<Option<Vec<u8>>, BoundedReadFailure> {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(BoundedReadFailure::Input {
                subject: ".olean companion part",
                detail: format!("cannot inspect {}: {error}", path.display()),
            });
        }
    };
    if metadata.file_type().is_symlink() {
        return Err(BoundedReadFailure::Input {
            subject: ".olean companion part",
            detail: format!("refusing symlink {}", path.display()),
        });
    }
    if !metadata.is_file() {
        return Err(BoundedReadFailure::Input {
            subject: ".olean companion part",
            detail: format!("{} is not a regular file", path.display()),
        });
    }
    read_bounded(path, max_bytes, ".olean artifact chain").map(Some)
}

#[derive(Debug)]
struct NamedOleanBytes {
    name: fln::Name,
    bytes: Vec<u8>,
    server_bytes: Option<Vec<u8>>,
    private_bytes: Option<Vec<u8>>,
}

fn module_name_from_relative(path: &Path) -> Result<fln::Name, String> {
    let without_extension = path.with_extension("");
    let mut components = Vec::new();
    for component in without_extension.components() {
        let std::path::Component::Normal(component) = component else {
            return Err(format!(
                "module path {} is not a normalized relative path",
                path.display()
            ));
        };
        let Some(component) = component.to_str() else {
            return Err(format!(
                "module path {} contains a non-UTF-8 component",
                path.display()
            ));
        };
        if component.is_empty() {
            return Err(format!(
                "module path {} contains an empty component",
                path.display()
            ));
        }
        components.push(component.to_owned());
    }
    if components.is_empty() {
        return Err(format!(
            "module path {} has no name components",
            path.display()
        ));
    }
    Ok(fln::Name::from_components(
        components.iter().map(String::as_str),
    ))
}

fn collect_olean_directory(
    root: &Path,
    max_bytes: usize,
) -> Result<Vec<NamedOleanBytes>, BoundedReadFailure> {
    let mut pending = vec![root.to_path_buf()];
    let mut paths = Vec::new();
    let mut companion_paths = BTreeMap::<PathBuf, (Option<PathBuf>, Option<PathBuf>)>::new();
    while let Some(directory) = pending.pop() {
        let entries = std::fs::read_dir(&directory).map_err(|error| BoundedReadFailure::Input {
            subject: ".olean directory",
            detail: format!("cannot read {}: {error}", directory.display()),
        })?;
        for entry in entries {
            let entry = entry.map_err(|error| BoundedReadFailure::Input {
                subject: ".olean directory",
                detail: format!(
                    "cannot read an entry under {}: {error}",
                    directory.display()
                ),
            })?;
            let file_type = entry
                .file_type()
                .map_err(|error| BoundedReadFailure::Input {
                    subject: ".olean directory",
                    detail: format!("cannot classify {}: {error}", entry.path().display()),
                })?;
            let path = entry.path();
            if file_type.is_symlink() {
                return Err(BoundedReadFailure::Input {
                    subject: ".olean directory",
                    detail: format!(
                        "refusing symlink {} while deriving a closed module set",
                        path.display()
                    ),
                });
            }
            if file_type.is_dir() {
                pending.push(path);
            } else if file_type.is_file() {
                if path.extension() == Some(std::ffi::OsStr::new("olean")) {
                    paths.push(path);
                } else if path
                    .file_name()
                    .is_some_and(|name| name.as_encoded_bytes().ends_with(b".olean.server"))
                {
                    let public_path = path.with_extension("");
                    companion_paths.entry(public_path).or_default().0 = Some(path);
                } else if path
                    .file_name()
                    .is_some_and(|name| name.as_encoded_bytes().ends_with(b".olean.private"))
                {
                    let public_path = path.with_extension("");
                    companion_paths.entry(public_path).or_default().1 = Some(path);
                }
            }
        }
    }
    paths.sort();
    let public_paths = paths.iter().cloned().collect::<BTreeSet<_>>();
    if let Some(orphan) = companion_paths
        .keys()
        .find(|public| !public_paths.contains(*public))
    {
        return Err(BoundedReadFailure::Input {
            subject: ".olean directory",
            detail: format!(
                "companion part has no exported .olean file at {}",
                orphan.display()
            ),
        });
    }

    let module_limit = fln::OleanCheckLimits::new(
        max_bytes,
        fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
    )
    .max_modules;
    if paths.len() > module_limit {
        return Err(BoundedReadFailure::TooLarge {
            subject: ".olean module count",
            observed: paths.len(),
            limit: module_limit,
        });
    }
    let mut modules = Vec::new();
    modules
        .try_reserve_exact(paths.len())
        .map_err(|_| BoundedReadFailure::Allocation {
            subject: ".olean module table",
            requested: paths.len(),
        })?;
    let mut total_bytes = 0_usize;
    for path in paths {
        let relative = path
            .strip_prefix(root)
            .map_err(|error| BoundedReadFailure::Input {
                subject: ".olean directory",
                detail: format!("cannot relativize {}: {error}", path.display()),
            })?;
        let name =
            module_name_from_relative(relative).map_err(|detail| BoundedReadFailure::Input {
                subject: ".olean directory",
                detail,
            })?;
        let remaining = max_bytes.saturating_sub(total_bytes);
        let bytes = read_bounded(&path, remaining, ".olean module set")?;
        total_bytes = total_bytes.saturating_add(bytes.len());
        let (server_path, private_path) = companion_paths.remove(&path).unwrap_or_default();
        let (server_bytes, private_bytes) = match (server_path, private_path) {
            (Some(server), Some(private)) => {
                let remaining = max_bytes.saturating_sub(total_bytes);
                let server_bytes = read_bounded(&server, remaining, ".olean module set")?;
                total_bytes = total_bytes.saturating_add(server_bytes.len());
                let remaining = max_bytes.saturating_sub(total_bytes);
                let private_bytes = read_bounded(&private, remaining, ".olean module set")?;
                total_bytes = total_bytes.saturating_add(private_bytes.len());
                (Some(server_bytes), Some(private_bytes))
            }
            (Some(_), None) => {
                return Err(BoundedReadFailure::Input {
                    subject: ".olean directory",
                    detail: format!("{} has .olean.server but no .olean.private", path.display()),
                });
            }
            (None, Some(_)) => {
                return Err(BoundedReadFailure::Input {
                    subject: ".olean directory",
                    detail: format!("{} has .olean.private but no .olean.server", path.display()),
                });
            }
            (None, None) => (None, None),
        };
        modules.push(NamedOleanBytes {
            name,
            bytes,
            server_bytes,
            private_bytes,
        });
    }
    if modules.is_empty() {
        return Err(BoundedReadFailure::Input {
            subject: ".olean directory",
            detail: format!("{} contains no .olean files", root.display()),
        });
    }
    Ok(modules)
}

fn render_check_olean_set_success(
    bytes: usize,
    checked: &fln::CheckedOleanSet,
    json: bool,
) -> MultiplexerOutput {
    let declarations: usize = checked
        .modules
        .iter()
        .map(|module| module.declarations.len())
        .sum();
    let imports: usize = checked
        .modules
        .iter()
        .map(|module| module.decoded.module.imports.len())
        .sum();
    let extensions: usize = checked
        .modules
        .iter()
        .map(|module| module.decoded.module.extensions.len())
        .sum();
    let companion_modules = checked
        .modules
        .iter()
        .filter(|module| module.decoded.companion_parts_loaded)
        .count();
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"scope\":\"closed-module-set-declarations\",\"artifactBytes\":{},",
                "\"modulesChecked\":{},\"importsResolved\":{},",
                "\"declarationsChecked\":{},\"dependencyOrderDerived\":true,",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"extensionBlocksObserved\":{},\"extensionsInterpreted\":false,",
                "\"companionPartsLoaded\":{},\"companionModulesLoaded\":{},",
                "\"k2Checked\":false,",
                "\"g1Satisfied\":false}}\n"
            ),
            json_string(CHECK_OLEAN_SCHEMA),
            bytes,
            checked.modules.len(),
            imports,
            declarations,
            json_string(&checked.base_logical_root.to_string()),
            json_string(&checked.result_logical_root.to_string()),
            extensions,
            companion_modules > 0,
            companion_modules,
        )
    } else {
        format!(
            concat!(
                "closed .olean module-set declaration check: complete\n",
                "authority: K1 + independent checker\n",
                "artifact bytes: {}\n",
                "modules checked: {}\n",
                "imports resolved: {}\n",
                "declarations checked: {}\n",
                "module and declaration dependency order: derived\n",
                "base logical root: {}\n",
                "result logical root: {}\n",
                "extension blocks observed: {} (not interpreted)\n",
                "complete module companion chains loaded: {}\n",
                "K2 checked: no\n",
                "G1 satisfied: no\n"
            ),
            bytes,
            checked.modules.len(),
            imports,
            declarations,
            checked.base_logical_root,
            checked.result_logical_root,
            extensions,
            companion_modules,
        )
    };
    MultiplexerOutput::success(stdout)
}

fn check_olean_module_bytes(
    modules: Vec<NamedOleanBytes>,
    max_bytes: usize,
    json: bool,
) -> MultiplexerOutput {
    let total_bytes = modules.iter().fold(0_usize, |total, module| {
        [
            Some(module.bytes.len()),
            module.server_bytes.as_ref().map(Vec::len),
            module.private_bytes.as_ref().map(Vec::len),
        ]
        .into_iter()
        .flatten()
        .fold(total, usize::saturating_add)
    });
    let worker = match std::thread::Builder::new()
        .name("fln-check-olean-set".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
        .spawn(move || {
            let inputs: Vec<fln::OleanModuleInput<'_>> = modules
                .iter()
                .map(|module| fln::OleanModuleInput {
                    name: &module.name,
                    artifact: &module.bytes,
                    server_artifact: module.server_bytes.as_deref(),
                    private_artifact: module.private_bytes.as_deref(),
                })
                .collect();
            let engine = fln::Engine::from_environment(fln::Environment::new());
            match engine.check_olean_modules(
                &inputs,
                &fln::KVMap::new(),
                fln::OleanCheckLimits::new(
                    max_bytes,
                    fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
                ),
            ) {
                Ok(fln::Outcome::Complete(checked)) => {
                    render_check_olean_set_success(total_bytes, &checked, json)
                }
                Ok(fln::Outcome::Inconclusive(reason)) => {
                    check_olean_failure("inconclusive", &format!("{reason:?}"), false, json, 3)
                }
                Ok(fln::Outcome::InternalFault(fault)) => {
                    check_olean_failure("internal-fault", &format!("{fault:?}"), false, json, 4)
                }
                Err(error) => {
                    let (class, authority, exit_code) = check_olean_error_disposition(&error);
                    check_olean_failure(class, &error.to_string(), authority, json, exit_code)
                }
            }
        }) {
        Ok(worker) => worker,
        Err(error) => {
            return check_olean_failure(
                "internal-fault",
                &format!("could not start bounded kernel worker: {error}"),
                false,
                json,
                4,
            );
        }
    };
    match worker.join() {
        Ok(output) => output,
        Err(_) => check_olean_failure(
            "internal-fault",
            "bounded kernel worker panicked",
            false,
            json,
            4,
        ),
    }
}

fn check_olean(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) => {
            return check_olean_failure(
                "input",
                &format!("cannot inspect {}: {error}", path.display()),
                false,
                json,
                1,
            );
        }
    };
    if metadata.file_type().is_symlink() {
        return check_olean_failure(
            "input",
            &format!("refusing symlink {} as a check root", path.display()),
            false,
            json,
            1,
        );
    }
    if metadata.is_dir() {
        let modules = match collect_olean_directory(path, max_bytes) {
            Ok(modules) => modules,
            Err(error) => {
                let class = error.class();
                return check_olean_failure(
                    class,
                    &error.to_string(),
                    false,
                    json,
                    if class == "resource" { 3 } else { 1 },
                );
            }
        };
        return check_olean_module_bytes(modules, max_bytes, json);
    }
    if !metadata.is_file() {
        return check_olean_failure(
            "input",
            &format!(
                "{} is neither a regular file nor a directory",
                path.display()
            ),
            false,
            json,
            1,
        );
    }
    let bytes = match read_bounded(path, max_bytes, ".olean artifact") {
        Ok(bytes) => bytes,
        Err(error) => {
            let class = error.class();
            return check_olean_failure(
                class,
                &error.to_string(),
                false,
                json,
                if class == "resource" { 3 } else { 1 },
            );
        }
    };
    let mut total_bytes = bytes.len();
    let mut read_companion = |companion: &Path| {
        let remaining = max_bytes.saturating_sub(total_bytes);
        let result = read_optional_olean_companion(companion, remaining);
        if let Ok(Some(bytes)) = &result {
            total_bytes = total_bytes.saturating_add(bytes.len());
        }
        result
    };
    let server_path = path.with_extension("olean.server");
    let server_bytes = match read_companion(&server_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            let class = error.class();
            return check_olean_failure(
                class,
                &error.to_string(),
                false,
                json,
                if class == "resource" { 3 } else { 1 },
            );
        }
    };
    let private_path = path.with_extension("olean.private");
    let private_bytes = match read_companion(&private_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            let class = error.class();
            return check_olean_failure(
                class,
                &error.to_string(),
                false,
                json,
                if class == "resource" { 3 } else { 1 },
            );
        }
    };
    check_olean_part_bytes(bytes, server_bytes, private_bytes, max_bytes, json)
}

fn checker_ground_name(ground: fln::CheckerAdmissionGround) -> &'static str {
    match ground {
        fln::CheckerAdmissionGround::AxiomPreamble => "axiom-preamble",
        fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType => {
            "body-checked-against-declared-type"
        }
        fln::CheckerAdmissionGround::UnsafeQuarantine => "unsafe-quarantine",
        fln::CheckerAdmissionGround::PartialQuarantine => "partial-quarantine",
    }
}

struct SourceSuccess<'a> {
    definitions: usize,
    source_bytes: usize,
    final_value: usize,
    flbc_bytes: usize,
    base_root: &'a str,
    result_root: &'a str,
    checker_schema: &'a str,
    checker_ground: &'a str,
    emitted_flbc: Option<(&'a Path, usize)>,
    emitted_sidecar: Option<(&'a Path, usize, fln::ContentRoot, fln::ContentRoot)>,
    steps: u64,
    system_polls: u64,
    peak_stack_depth: u64,
}

fn render_source_success(result: SourceSuccess<'_>, json: bool) -> MultiplexerOutput {
    let emitted_flbc_json = result.emitted_flbc.map_or_else(
        || "null".to_owned(),
        |(path, bytes)| {
            format!(
                "{{\"path\":{},\"bytes\":{bytes}}}",
                json_string(&path.to_string_lossy())
            )
        },
    );
    let emitted_sidecar_json = result.emitted_sidecar.map_or_else(
        || "null".to_owned(),
        |(path, bytes, closure_root, product_root)| {
            format!(
                concat!(
                    "{{\"path\":{},\"bytes\":{},\"mode\":\"sound\",",
                    "\"profile\":\"standard\",\"closureRoot\":{},",
                    "\"productRoot\":{}}}"
                ),
                json_string(&path.to_string_lossy()),
                bytes,
                json_string(&root_hex(closure_root)),
                json_string(&root_hex(product_root)),
            )
        },
    );
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"definitions\":{},\"sourceBytes\":{},\"finalValue\":{},",
                "\"flbcBytes\":{},\"emittedFlbc\":{},\"emittedSidecar\":{},",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"checker\":{{\"definitions\":{},\"finalSchema\":{},",
                "\"finalGround\":{}}},",
                "\"finalExecution\":{{\"steps\":{},\"systemPolls\":{},",
                "\"peakStackDepth\":{}}}}}\n"
            ),
            json_string(SOURCE_RUN_SCHEMA),
            result.definitions,
            result.source_bytes,
            result.final_value,
            result.flbc_bytes,
            emitted_flbc_json,
            emitted_sidecar_json,
            json_string(result.base_root),
            json_string(result.result_root),
            result.definitions,
            json_string(result.checker_schema),
            json_string(result.checker_ground),
            result.steps,
            result.system_polls,
            result.peak_stack_depth,
        )
    } else {
        let emitted_flbc = result
            .emitted_flbc
            .map_or_else(String::new, |(path, bytes)| {
                format!("emitted FLBC: {bytes} bytes to {}\n", path.display())
            });
        let emitted_sidecar = result.emitted_sidecar.map_or_else(
            String::new,
            |(path, bytes, closure_root, product_root)| {
                format!(
                    concat!(
                        "emitted sidecar: {} bytes to {}\n",
                        "closure root: {}\n",
                        "product root: {}\n"
                    ),
                    bytes,
                    path.display(),
                    root_hex(closure_root),
                    root_hex(product_root),
                )
            },
        );
        format!(
            concat!(
                "native source batch: complete\n",
                "definitions: {}\n",
                "final value: {}\n",
                "source bytes: {}\n",
                "canonical FLBC bytes: {} total\n",
                "{}",
                "{}",
                "base logical root: {}\n",
                "result logical root: {}\n",
                "independent checker: {} definitions agreed; final {} ({})\n",
                "final execution: {} steps, {} system polls, peak stack {}\n"
            ),
            result.definitions,
            result.final_value,
            result.source_bytes,
            result.flbc_bytes,
            emitted_flbc,
            emitted_sidecar,
            result.base_root,
            result.result_root,
            result.definitions,
            result.checker_schema,
            result.checker_ground,
            result.steps,
            result.system_polls,
            result.peak_stack_depth,
        )
    };
    MultiplexerOutput::success(stdout)
}

fn source_failure(
    class: &'static str,
    detail: &str,
    authority: bool,
    json: bool,
    exit_code: u8,
) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":{},",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(SOURCE_RUN_SCHEMA),
            authority,
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        let truncation = if detail.truncated() {
            format!("\n[detail truncated after {} bytes]", BoundedText::LIMIT)
        } else {
            String::new()
        };
        format!("fln run: {class}: {}{truncation}\n", detail.text())
    };
    MultiplexerOutput::failure(stderr, exit_code)
}

fn source_terminal(
    class: &'static str,
    detail: &str,
    steps: u64,
    system_polls: u64,
    peak_stack_depth: u64,
    json: bool,
) -> MultiplexerOutput {
    let detail = format!(
        "{detail}; execution used {} steps, {} system polls, peak stack {}",
        steps, system_polls, peak_stack_depth
    );
    source_failure(class, &detail, true, json, 1)
}

fn execution_error_disposition(error: &fln::EngineExecutionError) -> (&'static str, bool, u8) {
    match error {
        fln::EngineExecutionError::BatchCommand { error, .. } => execution_error_disposition(error),
        fln::EngineExecutionError::AllocationFailure { .. } => ("resource", false, 3),
        fln::EngineExecutionError::Ingress(error) if error.is_resource_exhaustion() => {
            ("resource", false, 3)
        }
        fln::EngineExecutionError::Codec(error) if error.is_resource_exhaustion() => {
            ("resource", false, 3)
        }
        fln::EngineExecutionError::Lowering(error) => {
            if error.is_resource_exhaustion() {
                ("resource", false, 3)
            } else if error.is_internal_fault() {
                ("internal-fault", false, 4)
            } else {
                ("execution", true, 1)
            }
        }
        fln::EngineExecutionError::CouncilHalted { .. } => ("inconclusive", false, 3),
        fln::EngineExecutionError::CheckerBridge { .. }
        | fln::EngineExecutionError::UnexpectedPublication { .. } => ("internal-fault", false, 4),
        _ => ("execution", true, 1),
    }
}

trait SourcePublicationFailure: std::fmt::Display {
    fn target_created(&self) -> Option<bool> {
        None
    }

    fn is_resource_exhaustion(&self) -> bool {
        false
    }
}

const fn publication_io_kind_is_resource(kind: std::io::ErrorKind) -> bool {
    matches!(
        kind,
        std::io::ErrorKind::StorageFull
            | std::io::ErrorKind::QuotaExceeded
            | std::io::ErrorKind::OutOfMemory
    )
}

impl SourcePublicationFailure for std::io::Error {
    fn is_resource_exhaustion(&self) -> bool {
        publication_io_kind_is_resource(self.kind())
    }
}

impl SourcePublicationFailure for fln::AtomicCreateError<std::convert::Infallible> {
    fn target_created(&self) -> Option<bool> {
        Some(self.target_created())
    }

    fn is_resource_exhaustion(&self) -> bool {
        self.primary_io_error_kind()
            .is_some_and(publication_io_kind_is_resource)
    }
}

fn publication_state(error: &impl SourcePublicationFailure) -> &'static str {
    match error.target_created() {
        Some(true) => {
            "the complete target already exists, but later cleanup or directory durability did not complete"
        }
        Some(false) => "the target was not created",
        None => "the injected publisher did not report whether the target was created",
    }
}

fn publication_failure_disposition(
    error: &impl SourcePublicationFailure,
) -> (&'static str, bool, u8) {
    if error.is_resource_exhaustion() {
        ("resource", false, 3)
    } else {
        ("output", true, 1)
    }
}

fn execute_source_bytes_with_publisher<P, E>(
    sources: Vec<Vec<u8>>,
    emit_flbc: Option<PathBuf>,
    emit_sidecar: Option<PathBuf>,
    toolchain_image: Option<Vec<u8>>,
    json: bool,
    mut publish: P,
) -> MultiplexerOutput
where
    P: FnMut(&[u8], &Path) -> Result<(), E>,
    E: SourcePublicationFailure,
{
    let Some(source_bytes) = sources
        .iter()
        .try_fold(0_usize, |total, source| total.checked_add(source.len()))
    else {
        return source_failure(
            "resource",
            "aggregate source byte count exceeded this platform",
            false,
            json,
            3,
        );
    };
    let mut source_refs = Vec::new();
    if source_refs.try_reserve_exact(sources.len()).is_err() {
        return source_failure(
            "resource",
            "could not reserve the bounded source batch table",
            false,
            json,
            3,
        );
    }
    source_refs.extend(sources.iter().map(Vec::as_slice));
    let kernel_budget = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
    let engine = match fln::Engine::with_nat_seed(fln::EngineAdmissionLimits::new(kernel_budget)) {
        Ok(fln::Outcome::Complete(engine)) => engine,
        Ok(fln::Outcome::Inconclusive(inconclusive)) => {
            return source_failure("inconclusive", &format!("{inconclusive:?}"), false, json, 3);
        }
        Ok(fln::Outcome::InternalFault(fault)) => {
            return source_failure("internal-fault", &format!("{fault:?}"), false, json, 4);
        }
        Err(error) => {
            let (class, authority, exit_code) = match &error {
                fln::EngineAdmissionError::CouncilHalted { .. } => ("inconclusive", false, 3),
                fln::EngineAdmissionError::CheckerBridge { .. }
                | fln::EngineAdmissionError::UnexpectedPublication { .. } => {
                    ("internal-fault", false, 4)
                }
                _ => ("seed", true, 1),
            };
            return source_failure(class, &error.to_string(), authority, json, exit_code);
        }
    };
    let options = fln::KVMap::new();
    let execution = match engine.execute_nat_definitions(
        &source_refs,
        &options,
        fln::EngineExecutionLimits::new(kernel_budget),
    ) {
        Ok(execution) => execution,
        Err(error) => {
            let (class, authority, exit_code) = execution_error_disposition(&error);
            return source_failure(class, &error.to_string(), authority, json, exit_code);
        }
    };
    let completed = match execution {
        fln::Outcome::Complete(completed) => completed,
        fln::Outcome::Inconclusive(inconclusive) => {
            return source_failure("inconclusive", &format!("{inconclusive:?}"), false, json, 3);
        }
        fln::Outcome::InternalFault(fault) => {
            return source_failure("internal-fault", &format!("{fault:?}"), false, json, 4);
        }
    };
    let definitions = completed.executions.len();
    let Some(final_execution) = completed.executions.last() else {
        return source_failure(
            "internal-fault",
            "completed source batch contained no definition executions",
            false,
            json,
            4,
        );
    };
    let Some(flbc_bytes) = completed
        .executions
        .iter()
        .try_fold(0_usize, |total, execution| {
            total.checked_add(execution.flbc_artifact.len())
        })
    else {
        return source_failure(
            "internal-fault",
            "completed source batch artifact byte count overflowed",
            false,
            json,
            4,
        );
    };
    for (index, execution) in completed.executions.iter().enumerate() {
        match &execution.exit {
            fln::VmExit::Returned(_) => {}
            fln::VmExit::Panicked { message, usage } => {
                return source_terminal(
                    "program-panic",
                    &format!("definition batch command {index} panicked: {message}"),
                    usage.steps,
                    usage.system_polls,
                    usage.peak_stack_depth,
                    json,
                );
            }
            fln::VmExit::Refused { refusal, usage } => {
                return source_terminal(
                    "vm-refusal",
                    &format!("definition batch command {index} was refused: {refusal}"),
                    usage.steps,
                    usage.system_polls,
                    usage.peak_stack_depth,
                    json,
                );
            }
        }
    }
    let base_root = completed.base_logical_root.to_string();
    let result_root = completed.result_logical_root.to_string();
    let checker_ground = checker_ground_name(final_execution.checker.ground);
    let fln::VmExit::Returned(returned) = &final_execution.exit else {
        return source_failure(
            "internal-fault",
            "non-returning final execution escaped source batch refusal handling",
            false,
            json,
            4,
        );
    };
    if !returned.value.is_scalar() {
        return source_failure(
            "execution",
            "final definition did not produce a closed Nat scalar",
            true,
            json,
            1,
        );
    }
    let emitted_sidecar = if let Some(path) = emit_sidecar.as_deref() {
        let toolchain_image = match toolchain_image {
            Some(image) => image,
            None => match read_current_toolchain_image() {
                Ok(image) => image,
                Err(error) => {
                    return source_failure("internal-fault", &error.to_string(), false, json, 4);
                }
            },
        };
        let sidecar = match fln::build_source_run_flbc_sidecar(
            &source_refs,
            &options,
            &toolchain_image,
            &completed,
        ) {
            Ok(sidecar) => sidecar,
            Err(error) => {
                return source_failure("sidecar", &error.to_string(), false, json, 1);
            }
        };
        let bytes = fln::encode_flbc_product_sidecar(&sidecar);
        if let Err(error) = publish(&bytes, path) {
            let state = publication_state(&error);
            let (class, authority, exit_code) = publication_failure_disposition(&error);
            return source_failure(
                class,
                &format!(
                    "could not complete durable FLBC sidecar publication to {}: {error}; {state}; the FLBC product was not published",
                    path.display()
                ),
                authority,
                json,
                exit_code,
            );
        }
        Some((
            path,
            bytes.len(),
            sidecar.closure_root(),
            sidecar.product_root(),
        ))
    } else {
        None
    };
    let emitted_flbc = if let Some(path) = emit_flbc.as_deref() {
        if let Err(error) = publish(&final_execution.flbc_artifact, path) {
            let state = publication_state(&error);
            let (class, authority, exit_code) = publication_failure_disposition(&error);
            return source_failure(
                class,
                &format!(
                    "could not complete durable FLBC artifact publication to {}: {error}; {state}",
                    path.display()
                ),
                authority,
                json,
                exit_code,
            );
        }
        Some((path, final_execution.flbc_artifact.len()))
    } else {
        None
    };
    render_source_success(
        SourceSuccess {
            definitions,
            source_bytes,
            final_value: returned.value.unbox(),
            flbc_bytes,
            base_root: &base_root,
            result_root: &result_root,
            checker_schema: final_execution.checker.schema,
            checker_ground,
            emitted_flbc,
            emitted_sidecar,
            steps: returned.usage.steps,
            system_polls: returned.usage.system_polls,
            peak_stack_depth: returned.usage.peak_stack_depth,
        },
        json,
    )
}

#[cfg(test)]
fn execute_source_bytes(sources: Vec<Vec<u8>>, json: bool) -> MultiplexerOutput {
    execute_source_bytes_with_publisher(sources, None, None, None, json, fln::publish_file_atomic)
}

fn execute_source_bytes_with_output(
    sources: Vec<Vec<u8>>,
    emit_flbc: Option<PathBuf>,
    emit_sidecar: Option<PathBuf>,
    json: bool,
) -> MultiplexerOutput {
    execute_source_bytes_with_publisher(
        sources,
        emit_flbc,
        emit_sidecar,
        None,
        json,
        fln::publish_file_atomic_new,
    )
}

fn read_source_batch(
    paths: &[PathBuf],
    max_bytes: usize,
) -> Result<Vec<Vec<u8>>, BoundedReadFailure> {
    let mut sources = Vec::new();
    let mut source_bytes = 0_usize;
    for path in paths {
        let remaining = max_bytes.saturating_sub(source_bytes);
        let source = match read_bounded(path, remaining, "source batch") {
            Ok(source) => source,
            Err(BoundedReadFailure::TooLarge { observed, .. }) => {
                return Err(BoundedReadFailure::TooLarge {
                    subject: "source batch",
                    observed: source_bytes.saturating_add(observed),
                    limit: max_bytes,
                });
            }
            Err(BoundedReadFailure::Allocation { requested, .. }) => {
                return Err(BoundedReadFailure::Allocation {
                    subject: "source batch",
                    requested: source_bytes.saturating_add(requested),
                });
            }
            Err(error) => return Err(error),
        };
        source_bytes = source_bytes.saturating_add(source.len());
        sources.push(source);
    }
    Ok(sources)
}

fn run_sources(
    paths: &[PathBuf],
    max_bytes: usize,
    json: bool,
    emit_flbc: Option<PathBuf>,
    emit_sidecar: Option<PathBuf>,
) -> MultiplexerOutput {
    let sources = match read_source_batch(paths, max_bytes) {
        Ok(sources) => sources,
        Err(error) => {
            let exit_code = if error.class() == "resource" { 3 } else { 1 };
            return source_failure(error.class(), &error.to_string(), false, json, exit_code);
        }
    };
    let worker = match std::thread::Builder::new()
        .name("fln-source-run".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
        .spawn(move || execute_source_bytes_with_output(sources, emit_flbc, emit_sidecar, json))
    {
        Ok(worker) => worker,
        Err(error) => {
            return source_failure(
                "internal-fault",
                &format!("could not start bounded kernel worker: {error}"),
                false,
                json,
                4,
            );
        }
    };
    match worker.join() {
        Ok(output) => output,
        Err(_) => source_failure(
            "internal-fault",
            "bounded kernel worker panicked",
            false,
            json,
            4,
        ),
    }
}

/// Run the native `fln` multiplexer without touching process-global arguments
/// or streams. The binary is a thin adapter over this testable entry point.
pub fn run(arguments: impl IntoIterator<Item = OsString>) -> MultiplexerOutput {
    match parse_command(arguments) {
        Ok(MultiplexerCommand::Help) => MultiplexerOutput::success(USAGE.to_owned()),
        Ok(MultiplexerCommand::Version) => {
            MultiplexerOutput::success(format!("fln {}\n", env!("CARGO_PKG_VERSION")))
        }
        Ok(MultiplexerCommand::CheckOlean {
            path,
            max_bytes,
            json,
        }) => check_olean(&path, max_bytes, json),
        Ok(MultiplexerCommand::SourceRun {
            paths,
            max_bytes,
            json,
            emit_flbc,
            emit_sidecar,
        }) => run_sources(&paths, max_bytes, json, emit_flbc, emit_sidecar),
        Ok(MultiplexerCommand::FlbcRun {
            path,
            max_bytes,
            json,
            sidecar,
        }) => run_flbc(&path, max_bytes, sidecar.as_deref(), json),
        Ok(MultiplexerCommand::OleanInspect {
            path,
            max_bytes,
            json,
        }) => inspect_olean(&path, max_bytes, json),
        Ok(MultiplexerCommand::OleanVerifyRebuild {
            path,
            max_bytes,
            json,
        }) => verify_olean_rebuild(&path, max_bytes, json),
        Err(error) => MultiplexerOutput::failure(format!("fln: {error}\n\n{USAGE}"), 2),
    }
}

/// Rendered C-family streams plus the exact structured value that authorized them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CliProjection {
    pub stdout: String,
    pub stderr: String,
    pub exit: ExitClass,
    pub semantic: ProjectionSnapshot,
}

fn mode_name(mode: Mode) -> &'static str {
    match mode {
        Mode::Faithful => "faithful",
        Mode::Sound => "sound",
        Mode::Frontier => "frontier",
    }
}

fn projected_path(path: &str, policy: DiagnosticPathPolicy) -> &str {
    match policy {
        DiagnosticPathPolicy::Preserve => path,
        DiagnosticPathPolicy::Basename => path
            .rsplit(['/', '\\'])
            .find(|component| !component.is_empty())
            .unwrap_or(path),
    }
}

fn validate_request(request: ProjectionRequest) -> Result<(), ProjectionRefusal> {
    request
        .validated_product_class()
        .map_err(ProjectionRefusal::Mode)?;
    match request.frontend {
        DiagnosticFrontend::Cli => {
            if request.format != DiagnosticFormat::Human {
                return Err(ProjectionRefusal::UnsupportedFormat {
                    frontend: request.frontend,
                    format: request.format,
                });
            }
        }
        DiagnosticFrontend::Json => {
            if !matches!(
                request.format,
                DiagnosticFormat::Json | DiagnosticFormat::Ndjson
            ) {
                return Err(ProjectionRefusal::UnsupportedFormat {
                    frontend: request.frontend,
                    format: request.format,
                });
            }
            if request.color != DiagnosticColorPolicy::Never {
                return Err(ProjectionRefusal::UnsupportedColor {
                    frontend: request.frontend,
                    color: request.color,
                });
            }
        }
        actual => {
            return Err(ProjectionRefusal::Frontend {
                expected: DiagnosticFrontend::Cli,
                actual,
            });
        }
    }
    if !matches!(
        request.channel,
        DiagnosticChannel::Stdout | DiagnosticChannel::Stderr
    ) {
        return Err(ProjectionRefusal::UnsupportedChannel {
            frontend: request.frontend,
            channel: request.channel,
        });
    }
    Ok(())
}

fn append_bounded(target: &mut String, value: &BoundedText, label: &str) {
    target.push_str(value.text());
    if value.truncated() {
        target.push_str(&format!(
            "\n[{label} truncated after {} bytes; typed links retained]",
            BoundedText::LIMIT
        ));
    }
}

fn colored_kind(kind: &str, severity: Severity, color: DiagnosticColorPolicy) -> String {
    if color == DiagnosticColorPolicy::Never {
        return kind.to_string();
    }
    let code = match severity {
        Severity::Error => 31,
        Severity::Warning => 33,
        Severity::Information => 36,
    };
    format!("\u{1b}[{code}m{kind}\u{1b}[0m")
}

fn append_sound_links(text: &mut String, diagnostic: &StructuredDiagnostic) {
    text.push_str(&format!(
        "\n[behavior note: {DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME}]"
    ));
    text.push_str(&format!("\n[typed cause: {}]", diagnostic.cause_class));
    for related in &diagnostic.related {
        text.push_str("\n[related: ");
        text.push_str(related.file_name.text());
        text.push_str(&format!(
            ":{}:{}-{}:{} ",
            related.start.line, related.start.column, related.end.line, related.end.column
        ));
        append_bounded(text, &related.label, "related label");
        text.push(']');
    }
    for evidence in &diagnostic.evidence {
        text.push_str("\n[evidence: ");
        append_bounded(text, evidence, "evidence");
        text.push(']');
    }
    if diagnostic.omitted_related > 0 {
        text.push_str(&format!(
            "\n[related spans omitted: {}]",
            diagnostic.omitted_related
        ));
    }
    if diagnostic.omitted_evidence > 0 {
        text.push_str(&format!(
            "\n[evidence links omitted: {}]",
            diagnostic.omitted_evidence
        ));
    }
}

/// `mkErrorStringWithPos` plus `SerialMessage.toString` for v4.32.0.
///
/// Faithful mode adds no local wording. Sound/frontier wording is an explicit
/// projection trailer and cannot alter the frame, severity, or typed cause.
pub fn render_human_diagnostic(
    diagnostic: &StructuredDiagnostic,
    request: ProjectionRequest,
) -> String {
    let mut body = String::new();
    append_bounded(&mut body, &diagnostic.body, "diagnostic body");
    if !matches!(request.mode, Mode::Faithful) {
        append_sound_links(&mut body, diagnostic);
    }
    let mut text = body;
    if !diagnostic.caption.text().is_empty() {
        let mut captioned = String::new();
        append_bounded(&mut captioned, &diagnostic.caption, "caption");
        captioned.push_str(":\n");
        captioned.push_str(&text);
        text = captioned;
    }
    if diagnostic.severity != Severity::Information {
        let path = projected_path(diagnostic.file_name.text(), request.path);
        let end = diagnostic
            .end_pos
            .map(|position| format!("-{}:{}", position.line, position.column))
            .unwrap_or_default();
        let kind = colored_kind(
            diagnostic.severity.as_str(),
            diagnostic.severity,
            request.color,
        );
        let label = diagnostic
            .error_name
            .as_ref()
            .map(|name| format!(" {kind}({name}):"))
            .unwrap_or_else(|| format!(" {kind}:"));
        text = format!(
            "{path}:{}:{}{end}:{label} {text}",
            diagnostic.pos.line, diagnostic.pos.column
        );
    }
    if text.is_empty() || !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

fn render_inconclusive(value: &StructuredInconclusive) -> String {
    let mut text = format!("inconclusive ({}): ", value.cause_class);
    append_bounded(&mut text, &value.detail, "inconclusive detail");
    if let Some(diagnostic) = &value.diagnostic {
        text.push_str(&format!("\n[typed cause: {}] ", diagnostic.class_name));
        append_bounded(&mut text, &diagnostic.body, "diagnostic cause");
    }
    if let Some(progress) = &value.progress {
        text.push_str("\n[progress: ");
        append_bounded(&mut text, progress, "progress");
        text.push(']');
    }
    text.push('\n');
    text
}

fn render_internal_fault(value: &StructuredInternalFault) -> String {
    let mut text = format!("internal fault ({}): ", value.invariant);
    append_bounded(&mut text, &value.detail, "internal fault detail");
    if let Some(evidence) = &value.evidence {
        text.push_str("\n[evidence: ");
        append_bounded(&mut text, evidence, "internal fault evidence");
        text.push(']');
    }
    text.push('\n');
    text
}

fn render_human(snapshot: &ProjectionSnapshot, request: ProjectionRequest) -> String {
    match snapshot {
        ProjectionSnapshot::Complete { diagnostics } => diagnostics
            .iter()
            .map(|diagnostic| render_human_diagnostic(diagnostic, request))
            .collect(),
        ProjectionSnapshot::Inconclusive(value) => render_inconclusive(value),
        ProjectionSnapshot::InternalFault(value) => render_internal_fault(value),
    }
}

fn json_string(value: &str) -> String {
    let mut encoded = String::with_capacity(value.len() + 2);
    encoded.push('"');
    for character in value.chars() {
        match character {
            '"' => encoded.push_str("\\\""),
            '\\' => encoded.push_str("\\\\"),
            '\n' => encoded.push_str("\\n"),
            '\r' => encoded.push_str("\\r"),
            '\t' => encoded.push_str("\\t"),
            '\u{08}' => encoded.push_str("\\b"),
            '\u{0c}' => encoded.push_str("\\f"),
            character if character <= '\u{1f}' => {
                encoded.push_str(&format!("\\u{:04x}", u32::from(character)));
            }
            character => encoded.push(character),
        }
    }
    encoded.push('"');
    encoded
}

fn bounded_json(value: &BoundedText) -> String {
    format!(
        "{{\"text\":{},\"truncated\":{}}}",
        json_string(value.text()),
        value.truncated()
    )
}

fn related_json(span: &RelatedSpan, path: DiagnosticPathPolicy) -> String {
    format!(
        concat!(
            "{{\"file\":{},\"start\":{{\"line\":{},\"column\":{}}},",
            "\"end\":{{\"line\":{},\"column\":{}}},\"label\":{}}}"
        ),
        json_string(projected_path(span.file_name.text(), path)),
        span.start.line,
        span.start.column,
        span.end.line,
        span.end.column,
        bounded_json(&span.label)
    )
}

fn diagnostic_json(diagnostic: &StructuredDiagnostic, request: ProjectionRequest) -> String {
    let end = diagnostic
        .end_pos
        .map(|position| {
            format!(
                "{{\"line\":{},\"column\":{}}}",
                position.line, position.column
            )
        })
        .unwrap_or_else(|| "null".to_string());
    let error_name = diagnostic
        .error_name
        .as_deref()
        .map(json_string)
        .unwrap_or_else(|| "null".to_string());
    let related = diagnostic
        .related
        .iter()
        .map(|span| related_json(span, request.path))
        .collect::<Vec<_>>()
        .join(",");
    let evidence = diagnostic
        .evidence
        .iter()
        .map(bounded_json)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        concat!(
            "{{\"file\":{},\"position\":{{\"line\":{},\"column\":{}}},",
            "\"endPosition\":{},\"severity\":{},\"errorName\":{},\"caption\":{},",
            "\"body\":{},\"causeClass\":{},\"related\":[{}],\"evidence\":[{}],",
            "\"omittedRelated\":{},\"omittedEvidence\":{}}}"
        ),
        json_string(projected_path(diagnostic.file_name.text(), request.path)),
        diagnostic.pos.line,
        diagnostic.pos.column,
        end,
        json_string(diagnostic.severity.as_str()),
        error_name,
        bounded_json(&diagnostic.caption),
        bounded_json(&diagnostic.body),
        json_string(diagnostic.cause_class),
        related,
        evidence,
        diagnostic.omitted_related,
        diagnostic.omitted_evidence
    )
}

fn inconclusive_json(value: &StructuredInconclusive) -> String {
    let diagnostic = value
        .diagnostic
        .as_ref()
        .map(|diagnostic| {
            format!(
                "{{\"causeClass\":{},\"body\":{}}}",
                json_string(diagnostic.class_name),
                bounded_json(&diagnostic.body)
            )
        })
        .unwrap_or_else(|| "null".to_string());
    let progress = value
        .progress
        .as_ref()
        .map(bounded_json)
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{{\"causeClass\":{},\"detail\":{},\"diagnostic\":{},\"progress\":{}}}",
        json_string(value.cause_class),
        bounded_json(&value.detail),
        diagnostic,
        progress
    )
}

fn internal_fault_json(value: &StructuredInternalFault) -> String {
    let evidence = value
        .evidence
        .as_ref()
        .map(bounded_json)
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{{\"invariant\":{},\"detail\":{},\"evidence\":{}}}",
        json_string(value.invariant),
        bounded_json(&value.detail),
        evidence
    )
}

/// Canonical semantic JSON. No host, time, PID, duration, or absolute scratch path
/// is admitted to this representation; telemetry belongs in a separately rooted
/// stream.
pub fn render_semantic_json(snapshot: &ProjectionSnapshot, request: ProjectionRequest) -> String {
    let behavior_note = if matches!(request.mode, Mode::Faithful) {
        "null".to_string()
    } else {
        json_string(DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME)
    };
    let payload = match snapshot {
        ProjectionSnapshot::Complete { diagnostics } => format!(
            "\"diagnostics\":[{}]",
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic_json(diagnostic, request))
                .collect::<Vec<_>>()
                .join(",")
        ),
        ProjectionSnapshot::Inconclusive(value) => {
            format!("\"inconclusive\":{}", inconclusive_json(value))
        }
        ProjectionSnapshot::InternalFault(value) => {
            format!("\"internalFault\":{}", internal_fault_json(value))
        }
    };
    format!(
        concat!(
            "{{\"schema\":{},\"epoch\":{},\"mode\":{},\"frontend\":{},",
            "\"format\":{},\"channel\":{},\"ordering\":{},\"outcome\":{},",
            "\"authority\":{},\"exitClass\":{},\"behaviorNote\":{},{}",
            "}}\n"
        ),
        json_string(DIAGNOSTIC_PROJECTION_SCHEMA),
        json_string(request.epoch.as_str()),
        json_string(mode_name(request.mode)),
        json_string(request.frontend.as_str()),
        json_string(request.format.as_str()),
        json_string(request.channel.as_str()),
        json_string(request.ordering.as_str()),
        json_string(snapshot.outcome_class()),
        snapshot.authority().as_bool(),
        json_string(snapshot.exit_class().as_str()),
        behavior_note,
        payload
    )
}

/// Project one already-ordered typed snapshot to CLI or robot bytes.
pub fn project(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<CliProjection, ProjectionRefusal> {
    validate_request(request)?;
    let rendered = match request.frontend {
        DiagnosticFrontend::Cli => render_human(snapshot, request),
        DiagnosticFrontend::Json => render_semantic_json(snapshot, request),
        DiagnosticFrontend::Lsp | DiagnosticFrontend::Library => {
            unreachable!("validated frontend")
        }
    };
    let (stdout, stderr) = match request.channel {
        DiagnosticChannel::Stdout => (rendered, String::new()),
        DiagnosticChannel::Stderr => (String::new(), rendered),
        DiagnosticChannel::Protocol | DiagnosticChannel::ReturnValue => {
            unreachable!("validated channel")
        }
    };
    Ok(CliProjection {
        stdout,
        stderr,
        exit: snapshot.exit_class(),
        semantic: snapshot.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::{
        CHECK_OLEAN_SCHEMA, FLBC_RUN_SCHEMA, NamedOleanBytes, OLEAN_INSPECT_SCHEMA,
        OLEAN_REBUILD_SCHEMA, SOURCE_RUN_KERNEL_STACK_BYTES, SOURCE_RUN_SCHEMA,
        admission_error_disposition, check_olean_bytes, check_olean_module_bytes,
        execute_flbc_bytes, execute_source_bytes, execute_source_bytes_with_publisher,
        execution_error_disposition, inspect_olean_bytes, module_name_from_relative,
        parse_source_run, read_bounded_from, run, source_failure, verify_olean_rebuild_bytes,
    };
    use std::ffi::OsString;
    use std::io::Cursor;
    use std::path::PathBuf;

    const PINNED_OLEAN: &[u8] =
        include_bytes!("../../../tribunal/fixtures/c3/Init.BinderNameHint.olean");
    const STRING_FLBC: &[u8] = b"FLNFLBC\0\x07\0\x0b\0\0\0\0\0\x01\0\0\0\0\0\0\0\0\0\x01\0\0\0\0\0\0\x02\0\0\0\x01\0\0\x02\0\0\0hi\x0d\0\0";

    fn repository_path(relative: &str) -> PathBuf {
        let invoked_from = std::env::current_dir().expect("the test has an invocation directory");
        let root = invoked_from
            .ancestors()
            .find(|candidate| candidate.join("crates/fln-cli/Cargo.toml").is_file())
            .expect("the test is invoked from inside the FrankenLean workspace");
        root.join(relative)
    }

    fn scalar_flbc_fixture(value: u64) -> Vec<u8> {
        let kernel = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
        let engine = fln::Engine::with_nat_seed(fln::EngineAdmissionLimits::new(kernel))
            .expect("the Nat seed council does not reject")
            .into_complete()
            .expect("the Nat seed council answers completely");
        let source = format!("def flbcFixture : Nat := {value}");
        let outcome = engine
            .execute_nat_definition(
                source.as_bytes(),
                &fln::KVMap::new(),
                fln::EngineExecutionLimits::new(kernel),
            )
            .expect("the fixture source reaches the engine");
        assert!(
            matches!(&outcome, fln::Outcome::Complete(_)),
            "the fixture source must execute authoritatively: {outcome:?}"
        );
        match outcome {
            fln::Outcome::Complete(execution) => execution.flbc_artifact,
            fln::Outcome::Inconclusive(_) | fln::Outcome::InternalFault(_) => Vec::new(),
        }
    }

    fn checkable_olean_fixture() -> Vec<u8> {
        let proposition = fln::Name::from_components(["CliFixture", "P"]);
        let witness = fln::Name::from_components(["CliFixture", "p"]);
        let theorem = fln::Name::from_components(["CliFixture", "t"]);
        let proposition_expr = fln::Expr::const_(proposition.clone(), Vec::new());
        let constants = vec![
            fln::ConstantInfo::Thm(fln::TheoremVal {
                base: fln::ConstantVal {
                    name: theorem,
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: fln::Expr::const_(witness.clone(), Vec::new()),
                all: Vec::new(),
            }),
            fln::ConstantInfo::Axiom(fln::AxiomVal {
                base: fln::ConstantVal {
                    name: witness,
                    level_params: Vec::new(),
                    type_: proposition_expr,
                },
                is_unsafe: false,
            }),
            fln::ConstantInfo::Axiom(fln::AxiomVal {
                base: fln::ConstantVal {
                    name: proposition,
                    level_params: Vec::new(),
                    type_: fln::Expr::sort(fln::Level::zero()),
                },
                is_unsafe: false,
            }),
        ];
        let lean_version = fln::OLEAN_PIN_TAG
            .strip_prefix('v')
            .expect("the pin tag starts with v");
        fln::encode_olean_module(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &constants,
                extra_const_names: &[],
            },
            fln::OleanWriteHeader {
                version: fln::OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version,
                githash: fln::OLEAN_PIN_COMMIT,
                base_addr: (fln::OLEAN_REGION_ALIGN as u64) * 2,
            },
            fln::OleanWriteBudget::default(),
        )
        .expect("the CLI check fixture encodes")
        .bytes
    }

    fn empty_olean_fixture(imports: &[fln::OleanModuleImport]) -> Vec<u8> {
        let lean_version = fln::OLEAN_PIN_TAG
            .strip_prefix('v')
            .expect("the pin tag starts with v");
        fln::encode_olean_module(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports,
                constants: &[],
                extra_const_names: &[],
            },
            fln::OleanWriteHeader {
                version: fln::OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version,
                githash: fln::OLEAN_PIN_COMMIT,
                base_addr: (fln::OLEAN_REGION_ALIGN as u64) * 2,
            },
            fln::OleanWriteBudget::default(),
        )
        .expect("the empty module fixture encodes")
        .bytes
    }

    #[test]
    fn flbc_run_executes_canonical_bytes_and_preserves_typed_stops() {
        let artifact = scalar_flbc_fixture(73);
        let robot = execute_flbc_bytes(&artifact, artifact.len(), true);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(
            robot
                .stdout
                .contains(&format!("\"schema\":\"{FLBC_RUN_SCHEMA}\""))
        );
        assert!(robot.stdout.contains("\"authority\":true"));
        assert!(robot.stdout.contains("\"returnKind\":\"scalar\""));
        assert!(robot.stdout.contains("\"scalarValue\":73"));

        let human = execute_flbc_bytes(&artifact, artifact.len(), false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stdout.contains("canonical FLBC execution: complete"));
        assert!(human.stdout.contains("scalar value: 73"));

        let non_scalar = execute_flbc_bytes(STRING_FLBC, STRING_FLBC.len(), true);
        assert_eq!(non_scalar.exit_code, 0, "{}", non_scalar.stderr);
        assert!(non_scalar.stdout.contains("\"returnKind\":\"string\""));
        assert!(non_scalar.stdout.contains("\"scalarValue\":null"));

        let mut malformed = artifact.clone();
        malformed[0] ^= u8::MAX;
        let invalid = execute_flbc_bytes(&malformed, malformed.len(), true);
        assert_eq!(invalid.exit_code, 1);
        assert!(invalid.stdout.is_empty());
        assert!(invalid.stderr.contains("\"authority\":true"));
        assert!(invalid.stderr.contains("\"class\":\"codec\""));
        assert!(invalid.stderr.contains("FLBC artifact magic mismatch"));

        let exhausted = execute_flbc_bytes(&artifact, artifact.len() - 1, true);
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.contains("\"authority\":false"));
        assert!(exhausted.stderr.contains("\"class\":\"resource\""));
    }

    #[test]
    fn flbc_run_requires_exactly_one_path() {
        let missing = run([OsString::from("flbc"), OsString::from("run")]);
        assert_eq!(missing.exit_code, 2);
        assert!(missing.stderr.contains("flbc run requires PATH"));

        let extra = run([
            OsString::from("flbc"),
            OsString::from("run"),
            OsString::from("first.flbc"),
            OsString::from("second.flbc"),
        ]);
        assert_eq!(extra.exit_code, 2);
        assert!(
            extra
                .stderr
                .contains("flbc run accepts exactly one input path")
        );

        let parsed = super::parse_flbc_run(vec![
            OsString::from("--sidecar=product.sidecar"),
            OsString::from("product.flbc"),
        ])
        .expect("one explicit sidecar is valid");
        assert!(matches!(
            parsed,
            super::MultiplexerCommand::FlbcRun {
                path,
                sidecar: Some(sidecar),
                ..
            } if path == std::path::Path::new("product.flbc")
                && sidecar == std::path::Path::new("product.sidecar")
        ));

        let duplicate = super::parse_flbc_run(vec![
            OsString::from("--sidecar=one.sidecar"),
            OsString::from("--sidecar"),
            OsString::from("two.sidecar"),
            OsString::from("product.flbc"),
        ])
        .expect_err("duplicate sidecars are ambiguous");
        assert!(duplicate.to_string().contains("at most once"));
    }

    #[test]
    fn olean_inspect_reports_a_real_pinned_artifact_in_human_and_robot_forms() {
        let human = inspect_olean_bytes(PINNED_OLEAN, PINNED_OLEAN.len(), false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains("pinned .olean audit: complete"));
        assert!(human.stdout.contains("constants: 2\n"));

        let robot = inspect_olean_bytes(PINNED_OLEAN, PINNED_OLEAN.len(), true);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(
            robot
                .stdout
                .contains(&format!("\"schema\":\"{OLEAN_INSPECT_SCHEMA}\""))
        );
        assert!(robot.stdout.contains("\"outcome\":\"complete\""));
        assert!(robot.stdout.contains("\"decodedConstants\":2"));
    }

    #[test]
    fn check_olean_reaches_k1_and_the_independent_checker_in_human_and_robot_forms() {
        let artifact = checkable_olean_fixture();
        let human = check_olean_bytes(artifact.clone(), artifact.len(), false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(
            human
                .stdout
                .contains("standalone .olean declaration check: complete")
        );
        assert!(human.stdout.contains("authority: K1 + independent checker"));
        assert!(human.stdout.contains("declarations checked: 3"));
        assert!(human.stdout.contains("K2 checked: no"));
        assert!(human.stdout.contains("G1 satisfied: no"));

        let robot = check_olean_bytes(artifact.clone(), artifact.len(), true);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(
            robot
                .stdout
                .contains(&format!("\"schema\":\"{CHECK_OLEAN_SCHEMA}\""))
        );
        assert!(robot.stdout.contains("\"outcome\":\"complete\""));
        assert!(robot.stdout.contains("\"authority\":true"));
        assert!(robot.stdout.contains("\"declarationsChecked\":3"));
        assert!(robot.stdout.contains("\"extensionsInterpreted\":false"));
        assert!(robot.stdout.contains("\"k2Checked\":false"));
        assert!(robot.stdout.contains("\"g1Satisfied\":false"));

        let exhausted = check_olean_bytes(artifact.clone(), artifact.len() - 1, true);
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.contains("\"class\":\"resource\""));
        assert!(exhausted.stderr.contains("\"authority\":false"));

        let mut corrupted = artifact;
        corrupted[0] ^= u8::MAX;
        let malformed = check_olean_bytes(corrupted.clone(), corrupted.len(), true);
        assert_eq!(malformed.exit_code, 1);
        assert!(malformed.stdout.is_empty());
        assert!(malformed.stderr.contains("\"class\":\"decode\""));
        assert!(malformed.stderr.contains("bad magic"));
    }

    #[test]
    fn check_olean_path_wiring_refuses_a_module_system_public_part_without_companions() {
        let artifact = repository_path("tribunal/fixtures/c3/Init.BinderNameHint.olean");
        let imported = run([
            OsString::from("check-olean"),
            OsString::from("--json"),
            artifact.into_os_string(),
        ]);
        assert_eq!(imported.exit_code, 1);
        assert!(imported.stdout.is_empty());
        assert!(imported.stderr.contains("\"class\":\"input\""));
        assert!(
            imported
                .stderr
                .contains("missing .olean.server and .olean.private")
        );

        let missing = run([OsString::from("check-olean")]);
        assert_eq!(missing.exit_code, 2);
        assert!(missing.stderr.contains("check-olean requires PATH"));
        let extra = run([
            OsString::from("check-olean"),
            OsString::from("first.olean"),
            OsString::from("second.olean"),
        ]);
        assert_eq!(extra.exit_code, 2);
        assert!(
            extra
                .stderr
                .contains("check-olean accepts exactly one input path")
        );
    }

    #[test]
    fn check_olean_closed_module_set_and_directory_traversal_are_live() {
        let base_name = fln::Name::from_components(["Fixture", "Base"]);
        let child_name = fln::Name::from_components(["Fixture", "Child"]);
        let base = empty_olean_fixture(&[]);
        let child = empty_olean_fixture(&[fln::OleanModuleImport {
            module: base_name.clone(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        }]);
        let total = base.len() + child.len();
        let output = check_olean_module_bytes(
            vec![
                NamedOleanBytes {
                    name: child_name,
                    bytes: child,
                    server_bytes: None,
                    private_bytes: None,
                },
                NamedOleanBytes {
                    name: base_name,
                    bytes: base,
                    server_bytes: None,
                    private_bytes: None,
                },
            ],
            total,
            true,
        );
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains("\"modulesChecked\":2"));
        assert!(output.stdout.contains("\"importsResolved\":1"));
        assert!(output.stdout.contains("\"declarationsChecked\":0"));
        assert!(
            output
                .stdout
                .contains("\"scope\":\"closed-module-set-declarations\"")
        );

        assert_eq!(
            module_name_from_relative(std::path::Path::new("Init/Prelude.olean"))
                .expect("normalized module path")
                .to_display_string(),
            "Init.Prelude"
        );

        let fixture_directory = repository_path("tribunal/fixtures/c3");
        let traversed = run([
            OsString::from("check-olean"),
            OsString::from("--json"),
            fixture_directory.into_os_string(),
        ]);
        assert_eq!(traversed.exit_code, 1);
        assert!(traversed.stdout.is_empty());
        assert!(traversed.stderr.contains("\"class\":\"input\""));
        assert!(
            traversed
                .stderr
                .contains("is missing .olean.server and .olean.private")
        );
    }

    #[test]
    fn olean_inspect_preserves_corruption_as_a_typed_robot_error() {
        let mut bytes = PINNED_OLEAN.to_vec();
        bytes[0] ^= u8::MAX;

        let output = inspect_olean_bytes(&bytes, bytes.len(), true);
        assert_eq!(output.exit_code, 1);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.contains("\"outcome\":\"error\""));
        assert!(output.stderr.contains("\"class\":\"decode\""));
        assert!(output.stderr.contains("bad magic (not an olean file)"));
    }

    #[test]
    fn olean_verify_rebuild_rederives_real_bytes_in_human_and_robot_forms() {
        let artifact = repository_path("tribunal/fixtures/c3/Init.BinderNameHint.olean");
        let human = run([
            OsString::from("olean"),
            OsString::from("verify-rebuild"),
            artifact.clone().into_os_string(),
        ]);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(
            human
                .stdout
                .contains("pinned .olean rebuild audit: complete")
        );
        assert!(human.stdout.contains("byte identity: exact"));
        assert!(human.stdout.contains("findings: 0"));

        let robot = run([
            OsString::from("olean"),
            OsString::from("verify-rebuild"),
            OsString::from("--json"),
            artifact.into_os_string(),
        ]);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(
            robot
                .stdout
                .contains(&format!("\"schema\":\"{OLEAN_REBUILD_SCHEMA}\""))
        );
        assert!(robot.stdout.contains("\"outcome\":\"complete\""));
        assert!(robot.stdout.contains("\"byteIdentity\":true"));
        assert!(robot.stdout.contains("\"findings\":0"));
    }

    #[test]
    fn olean_verify_rebuild_preserves_corruption_and_resource_stops() {
        let mut corrupted = PINNED_OLEAN.to_vec();
        corrupted[0] ^= u8::MAX;
        let invalid = verify_olean_rebuild_bytes(&corrupted, corrupted.len(), true);
        assert_eq!(invalid.exit_code, 1);
        assert!(invalid.stdout.is_empty());
        assert!(invalid.stderr.contains("\"class\":\"rebuild\""));
        assert!(invalid.stderr.contains("bad magic (not an olean file)"));

        let exhausted = verify_olean_rebuild_bytes(PINNED_OLEAN, PINNED_OLEAN.len() - 1, true);
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.contains("\"class\":\"resource\""));
        assert!(exhausted.stderr.contains("\"detailTruncated\":false"));
    }

    #[test]
    fn olean_input_is_bounded_before_the_decoder_runs() {
        let mut input = Cursor::new(vec![0_u8; 17]);
        let error = read_bounded_from(&mut input, 16, ".olean artifact")
            .expect_err("the seventeenth byte must refuse");
        assert_eq!(error.class(), "resource");
        assert!(error.to_string().contains("16-byte input limit"));
        assert!(error.to_string().contains("17 bytes"));

        let output = inspect_olean_bytes(PINNED_OLEAN, PINNED_OLEAN.len() - 1, true);
        assert_eq!(output.exit_code, 3);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.contains("\"class\":\"resource\""));
    }

    #[test]
    fn source_run_reaches_the_native_pipeline_in_human_and_robot_forms() {
        let source = repository_path("vendor/lean4-src/tests/lake/examples/deps/root/Root.lean");
        let human = run([OsString::from("run"), source.clone().into_os_string()]);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains("native source batch: complete"));
        assert!(human.stdout.contains("definitions: 1\n"));
        assert!(human.stdout.contains("final value: 0\n"));
        assert!(human.stdout.contains("independent checker:"));

        let robot = run([
            OsString::from("run"),
            OsString::from("--json"),
            source.into_os_string(),
        ]);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(
            robot
                .stdout
                .contains(&format!("\"schema\":\"{SOURCE_RUN_SCHEMA}\""))
        );
        assert!(robot.stdout.contains("\"outcome\":\"complete\""));
        assert!(robot.stdout.contains("\"authority\":true"));
        assert!(robot.stdout.contains("\"definitions\":1"));
        assert!(robot.stdout.contains("\"finalValue\":0"));
        assert!(
            robot
                .stdout
                .contains("\"finalGround\":\"body-checked-against-declared-type\"")
        );
    }

    #[test]
    fn source_run_executes_multiple_real_paths_in_order() {
        let root = repository_path("vendor/lean4-src/tests/lake/examples/deps/root/Root.lean");
        let same = repository_path("vendor/lean4-src/tests/pkg/mod_clash/depA/Same.lean");
        let output = run([
            OsString::from("run"),
            OsString::from("--json"),
            root.clone().into_os_string(),
            same.clone().into_os_string(),
        ]);

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains("\"definitions\":2"));
        assert!(output.stdout.contains("\"sourceBytes\":28"));
        assert!(output.stdout.contains("\"finalValue\":0"));
        assert!(output.stdout.contains("\"definitions\":2,\"finalSchema\""));

        let exhausted = run([
            OsString::from("run"),
            OsString::from("--json"),
            OsString::from("--max-bytes=14"),
            root.into_os_string(),
            same.into_os_string(),
        ]);
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.contains("\"authority\":false"));
        assert!(exhausted.stderr.contains("14-byte input limit"));
        assert!(exhausted.stderr.contains("28 bytes"));
    }

    #[test]
    fn source_run_worker_executes_a_dependent_definition_batch() {
        let output = execute_source_bytes(
            vec![
                b"def first (x y : Nat) : Nat := x".to_vec(),
                b"def selected : Nat := first 17 29".to_vec(),
            ],
            true,
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains("\"definitions\":2"));
        assert!(output.stdout.contains("\"finalValue\":17"));
        assert!(output.stdout.contains("\"authority\":true"));
    }

    #[test]
    fn source_run_emits_only_the_final_executed_artifact_after_success() {
        let target = PathBuf::from("retained-final.flbc");
        let expected = scalar_flbc_fixture(17);
        let mut publications = Vec::new();
        let output = execute_source_bytes_with_publisher(
            vec![
                b"def earlier : Nat := 11".to_vec(),
                b"def emitted : Nat := 17".to_vec(),
            ],
            Some(target.clone()),
            None,
            None,
            true,
            |bytes, path| {
                publications.push((path.to_path_buf(), bytes.to_vec()));
                Ok::<(), std::io::Error>(())
            },
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert_eq!(publications, vec![(target, expected.clone())]);
        assert!(output.stdout.contains("\"schema\":\"fln.source-run/4\""));
        assert!(
            output
                .stdout
                .contains(&format!("\"bytes\":{}", expected.len()))
        );
        assert!(output.stdout.contains("\"path\":\"retained-final.flbc\""));

        let mut failed_batch_publications = 0;
        let failed_batch = execute_source_bytes_with_publisher(
            vec![
                b"def earlier : Nat := 11".to_vec(),
                b"def open (x : Nat) : Nat := x".to_vec(),
            ],
            Some(PathBuf::from("must-not-publish.flbc")),
            None,
            None,
            true,
            |_bytes, _path| {
                failed_batch_publications += 1;
                Ok::<(), std::io::Error>(())
            },
        );
        assert_eq!(failed_batch.exit_code, 1);
        assert_eq!(failed_batch_publications, 0);

        let publication_failure = execute_source_bytes_with_publisher(
            vec![b"def emitted : Nat := 17".to_vec()],
            Some(PathBuf::from("refused.flbc")),
            None,
            None,
            true,
            |_bytes, _path| Err(std::io::Error::other("injected output refusal")),
        );
        assert_eq!(publication_failure.exit_code, 1);
        assert!(publication_failure.stdout.is_empty());
        assert!(publication_failure.stderr.contains("\"authority\":true"));
        assert!(publication_failure.stderr.contains("\"class\":\"output\""));
        assert!(
            publication_failure
                .stderr
                .contains("injected output refusal")
        );
    }

    #[test]
    fn source_run_publication_exhaustion_is_a_nonanswer_on_both_sides_of_link() {
        let cases = [
            (
                false,
                fln::AtomicCreateStep::WriteChunk {
                    offset: 0,
                    chunk_len: 1,
                    total_len: 1,
                },
                "the target was not created",
            ),
            (
                true,
                fln::AtomicCreateStep::SyncDirectoryAfterLink,
                "the complete target already exists",
            ),
        ];

        for (target_created, step, state) in cases {
            let output = execute_source_bytes_with_publisher(
                vec![b"def emitted : Nat := 17".to_vec()],
                Some(PathBuf::from("resource-exhausted.flbc")),
                None,
                None,
                true,
                |_bytes, _path| {
                    Err::<(), _>(fln::AtomicCreateError::<std::convert::Infallible>::Io {
                        step,
                        target_created,
                        source: std::io::Error::from(std::io::ErrorKind::StorageFull),
                    })
                },
            );

            assert_eq!(output.exit_code, 3, "{}", output.stderr);
            assert!(output.stdout.is_empty());
            assert!(output.stderr.contains("\"authority\":false"));
            assert!(output.stderr.contains("\"class\":\"resource\""));
            assert!(output.stderr.contains("publication I/O failed at"));
            assert!(output.stderr.contains(state));
        }

        let compound = execute_source_bytes_with_publisher(
            vec![b"def emitted : Nat := 17".to_vec()],
            Some(PathBuf::from("resource-exhausted-compound.flbc")),
            None,
            None,
            true,
            |_bytes, _path| {
                Err::<(), _>(
                    fln::AtomicCreateError::<std::convert::Infallible>::Cleanup {
                        primary: Box::new(fln::AtomicCreateError::Io {
                            step: fln::AtomicCreateStep::WriteChunk {
                                offset: 0,
                                chunk_len: 1,
                                total_len: 1,
                            },
                            target_created: false,
                            source: std::io::Error::from(std::io::ErrorKind::StorageFull),
                        }),
                        cleanup: Box::new(fln::AtomicCreateError::Io {
                            step: fln::AtomicCreateStep::RemoveStaging,
                            target_created: false,
                            source: std::io::Error::from(std::io::ErrorKind::PermissionDenied),
                        }),
                    },
                )
            },
        );
        assert_eq!(compound.exit_code, 3, "{}", compound.stderr);
        assert!(compound.stdout.is_empty());
        assert!(compound.stderr.contains("\"authority\":false"));
        assert!(compound.stderr.contains("\"class\":\"resource\""));
        assert!(compound.stderr.contains("publication I/O failed at write"));
        assert!(compound.stderr.contains("staging cleanup also failed"));
        assert!(compound.stderr.contains("remove staging link"));
        assert!(compound.stderr.contains("the target was not created"));
    }

    #[test]
    fn source_run_sidecar_is_exact_and_published_before_its_product() {
        let flbc_path = PathBuf::from("bound-product.flbc");
        let sidecar_path = PathBuf::from("bound-product.flbc.sidecar");
        let expected_product = scalar_flbc_fixture(23);
        let mut publications = Vec::new();
        let output = execute_source_bytes_with_publisher(
            vec![b"def emitted : Nat := 23".to_vec()],
            Some(flbc_path.clone()),
            Some(sidecar_path.clone()),
            Some(b"injected toolchain image".to_vec()),
            true,
            |bytes, path| {
                publications.push((path.to_path_buf(), bytes.to_vec()));
                Ok::<(), std::io::Error>(())
            },
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert_eq!(publications.len(), 2);
        assert_eq!(publications[0].0, sidecar_path);
        assert_eq!(publications[1], (flbc_path, expected_product.clone()));
        let verified = fln::verify_source_run_flbc_sidecar(
            &publications[0].1,
            &expected_product,
            b"injected toolchain image",
        )
        .expect("the emitted sidecar binds the exact emitted product");
        let replay = super::execute_flbc_bytes_with_sidecar(
            &expected_product,
            expected_product.len(),
            Some(&verified),
            true,
        );
        assert_eq!(replay.exit_code, 0, "{}", replay.stderr);
        assert!(replay.stdout.contains("\"sidecar\":{\"verified\":true"));
        assert!(output.stdout.contains("\"emittedSidecar\":{"));
        assert!(output.stdout.contains("\"profile\":\"standard\""));

        let mut failed_publications = 0;
        let failed = execute_source_bytes_with_publisher(
            vec![b"def open (x : Nat) : Nat := x".to_vec()],
            Some(PathBuf::from("not-published.flbc")),
            Some(PathBuf::from("not-published.sidecar")),
            Some(b"injected toolchain image".to_vec()),
            true,
            |_bytes, _path| {
                failed_publications += 1;
                Ok::<(), std::io::Error>(())
            },
        );
        assert_eq!(failed.exit_code, 1);
        assert_eq!(failed_publications, 0);
    }

    #[test]
    fn source_run_emit_option_is_single_and_respects_the_option_terminator() {
        let parsed = parse_source_run(vec![
            OsString::from("--emit-flbc=product.flbc"),
            OsString::from("input.lean"),
        ])
        .expect("one emission path is valid");
        assert!(matches!(
            parsed,
            super::MultiplexerCommand::SourceRun {
                emit_flbc: Some(path),
                paths,
                ..
            } if path.as_path() == std::path::Path::new("product.flbc")
                && paths.len() == 1
                && paths[0].as_path() == std::path::Path::new("input.lean")
        ));

        let duplicate = parse_source_run(vec![
            OsString::from("--emit-flbc"),
            OsString::from("one.flbc"),
            OsString::from("--emit-flbc=two.flbc"),
            OsString::from("input.lean"),
        ])
        .expect_err("duplicate emission paths are ambiguous");
        assert!(duplicate.to_string().contains("at most once"));

        let sidecar_without_product = parse_source_run(vec![
            OsString::from("--emit-sidecar=product.sidecar"),
            OsString::from("input.lean"),
        ])
        .expect_err("a sidecar without a product is ambiguous");
        assert!(
            sidecar_without_product
                .to_string()
                .contains("requires --emit-flbc")
        );

        let same_path = parse_source_run(vec![
            OsString::from("--emit-flbc=product.flbc"),
            OsString::from("--emit-sidecar=product.flbc"),
            OsString::from("input.lean"),
        ])
        .expect_err("one path cannot carry two schemas");
        assert!(same_path.to_string().contains("different paths"));

        let aliased_path = parse_source_run(vec![
            OsString::from("--emit-flbc=product.flbc"),
            OsString::from("--emit-sidecar=./product.flbc"),
            OsString::from("input.lean"),
        ])
        .expect_err("lexical aliases cannot carry two schemas");
        assert!(aliased_path.to_string().contains("different paths"));

        let both = parse_source_run(vec![
            OsString::from("--emit-flbc=product.flbc"),
            OsString::from("--emit-sidecar=product.sidecar"),
            OsString::from("input.lean"),
        ])
        .expect("the product and sidecar pair is explicit");
        assert!(matches!(
            both,
            super::MultiplexerCommand::SourceRun {
                emit_flbc: Some(flbc),
                emit_sidecar: Some(sidecar),
                ..
            } if flbc == std::path::Path::new("product.flbc")
                && sidecar == std::path::Path::new("product.sidecar")
        ));

        let terminated = parse_source_run(vec![
            OsString::from("--"),
            OsString::from("--emit-flbc=ordinary-source-name"),
        ])
        .expect("the option terminator makes the spelling an input path");
        assert!(matches!(
            terminated,
            super::MultiplexerCommand::SourceRun {
                emit_flbc: None,
                paths,
                ..
            } if paths.len() == 1
                && paths[0].as_path()
                    == std::path::Path::new("--emit-flbc=ordinary-source-name")
        ));
    }

    #[test]
    fn source_run_executes_dependent_commands_from_one_file() {
        let output = execute_source_bytes(
            vec![b"-- def hidden\r\ndef first (x y : Nat) : Nat := x\r\ndef selected : Nat := first 17 29".to_vec()],
            true,
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains("\"definitions\":2"));
        assert!(output.stdout.contains("\"finalValue\":17"));
        assert!(output.stdout.contains("\"authority\":true"));
    }

    #[test]
    fn source_run_refuses_a_nonclosed_final_definition_without_panicking() {
        let output = execute_source_bytes(vec![b"def first (x y : Nat) : Nat := x".to_vec()], true);

        assert_eq!(output.exit_code, 1);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.contains("\"authority\":true"));
        assert!(output.stderr.contains("\"class\":\"execution\""));
        assert!(
            output
                .stderr
                .contains("final definition did not produce a closed Nat scalar")
        );
    }

    #[test]
    fn check_olean_renders_a_council_halt_as_inconclusive() {
        let halted = fln::EngineAdmissionError::BatchDeclaration {
            index: 0,
            error: Box::new(fln::EngineAdmissionError::CouncilHalted {
                summary: "independent checker did not answer".to_owned(),
            }),
        };
        assert_eq!(
            admission_error_disposition(&halted),
            ("inconclusive", false, 3)
        );
    }

    #[test]
    fn source_run_preserves_nested_nonanswers_and_internal_faults() {
        let inconclusive = fln::EngineExecutionError::BatchCommand {
            index: 1,
            error: Box::new(fln::EngineExecutionError::CouncilHalted {
                summary: "independent checker did not answer".to_owned(),
            }),
        };
        assert_eq!(
            execution_error_disposition(&inconclusive),
            ("inconclusive", false, 3)
        );

        let internal = fln::EngineExecutionError::BatchCommand {
            index: 1,
            error: Box::new(fln::EngineExecutionError::CheckerBridge {
                detail: "projection mismatch".to_owned(),
            }),
        };
        assert_eq!(
            execution_error_disposition(&internal),
            ("internal-fault", false, 4)
        );

        let exhausted = fln::EngineExecutionError::AllocationFailure {
            resource: "definition batch results",
            requested: usize::MAX,
        };
        assert_eq!(
            execution_error_disposition(&exhausted),
            ("resource", false, 3)
        );

        // Compiler-stage budgets are FL-INV-07 too. Folding them into
        // `execution` / exit 1 would promote exhaustion to a source verdict.
        let lowering_budget = fln::EngineExecutionError::BatchCommand {
            index: 0,
            error: Box::new(fln::EngineExecutionError::Lowering(
                fln::LoweringError::AllocationFailure {
                    table: "functions",
                    requested: usize::MAX,
                },
            )),
        };
        assert_eq!(
            execution_error_disposition(&lowering_budget),
            ("resource", false, 3)
        );

        let lowering_fault =
            fln::EngineExecutionError::Lowering(fln::LoweringError::InternalInvariant {
                reason: "register file shrank",
            });
        assert_eq!(
            execution_error_disposition(&lowering_fault),
            ("internal-fault", false, 4)
        );
    }

    #[test]
    fn source_run_preserves_frontend_refusal_as_an_authoritative_error() {
        let source = repository_path("crates/fln-conformance/fixtures/g04_reference_fixture.lean");
        let output = run([
            OsString::from("run"),
            OsString::from("--json"),
            source.into_os_string(),
        ]);
        assert_eq!(output.exit_code, 1);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.contains("\"outcome\":\"error\""));
        assert!(output.stderr.contains("\"authority\":true"));
        assert!(output.stderr.contains("\"class\":\"execution\""));
        assert!(output.stderr.contains("frontend refused source"));
        assert!(output.stderr.contains("lexical analysis reported"));
        assert!(output.stderr.contains("\"detailTruncated\":false"));
    }

    #[test]
    fn source_run_failure_details_are_bounded_and_marked() {
        let output = source_failure("execution", &"x".repeat(5000), true, true, 1);
        assert_eq!(output.exit_code, 1);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.contains("\"detailTruncated\":true"));
        assert!(output.stderr.len() < 5000);
    }

    #[test]
    fn source_run_input_exhaustion_is_a_nonanswer_not_a_rejection() {
        let source = repository_path("vendor/lean4-src/tests/lake/examples/deps/root/Root.lean");
        let output = run([
            OsString::from("run"),
            OsString::from("--json"),
            OsString::from("--max-bytes=0"),
            source.into_os_string(),
        ]);
        assert_eq!(output.exit_code, 3);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.contains("\"authority\":false"));
        assert!(output.stderr.contains("\"class\":\"resource\""));
        assert!(output.stderr.contains("0-byte input limit"));
    }

    #[test]
    fn multiplexer_help_and_usage_errors_have_distinct_exit_codes() {
        let help = run(std::iter::empty());
        assert_eq!(help.exit_code, 0);
        assert!(help.stdout.starts_with("Usage:\n  fln check-olean"));
        assert!(help.stdout.contains("\n  fln run"));

        let error = run([OsString::from("olean"), OsString::from("decode")]);
        assert_eq!(error.exit_code, 2);
        assert!(error.stdout.is_empty());
        assert!(error.stderr.contains("unknown olean subcommand"));
    }
}
