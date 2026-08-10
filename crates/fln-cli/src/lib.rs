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

/// Default whole-file ceiling for the current bounded source runner.
pub const SOURCE_RUN_DEFAULT_MAX_BYTES: usize = 1024 * 1024;

/// Native stack provided to the kernel worker used by `fln run`.
const SOURCE_RUN_KERNEL_STACK_BYTES: usize = 2 * 1024 * 1024;

const OLEAN_INSPECT_SCHEMA: &str = "fln.olean-inspect/1";
const SOURCE_RUN_SCHEMA: &str = "fln.source-run/1";

const USAGE: &str = concat!(
    "Usage:\n",
    "  fln run [--json] [--max-bytes BYTES] PATH\n",
    "  fln olean inspect [--json] [--max-bytes BYTES] PATH\n",
    "  fln --help\n",
    "  fln --version\n",
    "\n",
    "`olean inspect` audits and decodes one pinned-format .olean. It does not\n",
    "resolve imports, kernel-check declarations, or re-emit an artifact.\n",
    "\n",
    "`run` executes one currently supported closed Nat definition through the\n",
    "native parser, elaborator, K1, independent checker, compiler, and Golem.\n",
    "It is not general Lean, Prelude/import processing, a project build, or\n",
    "evidence that `check-olean` is complete.\n",
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
    SourceRun {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    OleanInspect {
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
) -> Result<Option<(PathBuf, usize, bool)>, UsageError> {
    let mut path = None;
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
        if path.replace(PathBuf::from(&argument)).is_some() {
            return Err(UsageError(format!(
                "{command} accepts exactly one input path"
            )));
        }
    }

    let path = path.ok_or_else(|| UsageError(format!("{command} requires PATH")))?;
    Ok(Some((path, max_bytes, json)))
}

fn parse_source_run(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((path, max_bytes, json)) =
        parse_path_options(arguments, "run", SOURCE_RUN_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    Ok(MultiplexerCommand::SourceRun {
        path,
        max_bytes,
        json,
    })
}

fn parse_olean_inspect(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((path, max_bytes, json)) =
        parse_path_options(arguments, "olean inspect", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    Ok(MultiplexerCommand::OleanInspect {
        path,
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
    if subcommand != "inspect" {
        return Err(UsageError(format!(
            "unknown olean subcommand {:?}",
            subcommand.to_string_lossy()
        )));
    }
    parse_olean_inspect(arguments.collect())
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
    let stderr = if json {
        format!(
            "{{\"schema\":{},\"outcome\":\"error\",\"class\":{},\"detail\":{}}}\n",
            json_string(OLEAN_INSPECT_SCHEMA),
            json_string(error.class()),
            json_string(&detail),
        )
    } else {
        format!("fln olean inspect: {detail}\n")
    };
    MultiplexerOutput::failure(stderr, 1)
}

fn inspect_olean(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    match read_bounded(path, max_bytes, ".olean artifact") {
        Ok(bytes) => inspect_olean_bytes(&bytes, max_bytes, json),
        Err(error) => inspect_failure(OleanInspectFailure::Read(error), json),
    }
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
    source_bytes: usize,
    value: usize,
    flbc_bytes: usize,
    base_root: &'a str,
    result_root: &'a str,
    checker_schema: &'a str,
    checker_ground: &'a str,
    steps: u64,
    system_polls: u64,
    peak_stack_depth: u64,
}

fn render_source_success(result: SourceSuccess<'_>, json: bool) -> MultiplexerOutput {
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"sourceBytes\":{},\"value\":{},\"flbcBytes\":{},",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"checker\":{{\"schema\":{},\"ground\":{}}},",
                "\"execution\":{{\"steps\":{},\"systemPolls\":{},",
                "\"peakStackDepth\":{}}}}}\n"
            ),
            json_string(SOURCE_RUN_SCHEMA),
            result.source_bytes,
            result.value,
            result.flbc_bytes,
            json_string(result.base_root),
            json_string(result.result_root),
            json_string(result.checker_schema),
            json_string(result.checker_ground),
            result.steps,
            result.system_polls,
            result.peak_stack_depth,
        )
    } else {
        format!(
            concat!(
                "native source run: complete\n",
                "value: {}\n",
                "source bytes: {}\n",
                "canonical FLBC bytes: {}\n",
                "base logical root: {}\n",
                "result logical root: {}\n",
                "independent checker: {} ({})\n",
                "execution: {} steps, {} system polls, peak stack {}\n"
            ),
            result.value,
            result.source_bytes,
            result.flbc_bytes,
            result.base_root,
            result.result_root,
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

fn execute_source_bytes(source: Vec<u8>, json: bool) -> MultiplexerOutput {
    let source_bytes = source.len();
    let kernel_budget = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
    let engine = match fln::Engine::with_nat_seed(kernel_budget) {
        Ok(engine) => engine,
        Err(error) => {
            let (class, exit_code) = match &error {
                fln::SeedEnvironmentError::Inconclusive(_) => ("inconclusive", 3),
                fln::SeedEnvironmentError::InternalFault(_) => ("internal-fault", 4),
                _ => ("seed", 1),
            };
            return source_failure(class, &error.to_string(), false, json, exit_code);
        }
    };
    let options = fln::KVMap::new();
    let execution = match engine.execute_nat_definition(
        &source,
        &options,
        fln::EngineExecutionLimits::new(kernel_budget),
    ) {
        Ok(execution) => execution,
        Err(error) => {
            let (class, authority, exit_code) = match &error {
                fln::EngineExecutionError::CouncilHalted { .. } => ("inconclusive", false, 3),
                fln::EngineExecutionError::CheckerBridge { .. }
                | fln::EngineExecutionError::UnexpectedPublication { .. } => {
                    ("internal-fault", false, 4)
                }
                _ => ("execution", true, 1),
            };
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
    let base_root = completed.base_logical_root.to_string();
    let result_root = completed.result_logical_root.to_string();
    let checker_ground = checker_ground_name(completed.checker.ground);
    let flbc_bytes = completed.flbc_artifact.len();
    match completed.exit {
        fln::VmExit::Returned(returned) => render_source_success(
            SourceSuccess {
                source_bytes,
                value: returned.value.unbox(),
                flbc_bytes,
                base_root: &base_root,
                result_root: &result_root,
                checker_schema: completed.checker.schema,
                checker_ground,
                steps: returned.usage.steps,
                system_polls: returned.usage.system_polls,
                peak_stack_depth: returned.usage.peak_stack_depth,
            },
            json,
        ),
        fln::VmExit::Panicked { message, usage } => source_terminal(
            "program-panic",
            &message,
            usage.steps,
            usage.system_polls,
            usage.peak_stack_depth,
            json,
        ),
        fln::VmExit::Refused { refusal, usage } => source_terminal(
            "vm-refusal",
            &refusal.to_string(),
            usage.steps,
            usage.system_polls,
            usage.peak_stack_depth,
            json,
        ),
    }
}

fn run_source(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    let source = match read_bounded(path, max_bytes, "source file") {
        Ok(source) => source,
        Err(error) => {
            let exit_code = if error.class() == "resource" { 3 } else { 1 };
            return source_failure(error.class(), &error.to_string(), false, json, exit_code);
        }
    };
    let worker = match std::thread::Builder::new()
        .name("fln-source-run".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
        .spawn(move || execute_source_bytes(source, json))
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
        Ok(MultiplexerCommand::SourceRun {
            path,
            max_bytes,
            json,
        }) => run_source(&path, max_bytes, json),
        Ok(MultiplexerCommand::OleanInspect {
            path,
            max_bytes,
            json,
        }) => inspect_olean(&path, max_bytes, json),
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
        OLEAN_INSPECT_SCHEMA, SOURCE_RUN_SCHEMA, inspect_olean_bytes, read_bounded_from, run,
        source_failure,
    };
    use std::ffi::OsString;
    use std::io::Cursor;
    use std::path::PathBuf;

    const PINNED_OLEAN: &[u8] =
        include_bytes!("../../../tribunal/fixtures/c3/Init.BinderNameHint.olean");

    fn repository_path(relative: &str) -> PathBuf {
        std::env::var_os("CARGO_MANIFEST_DIR")
            .map(PathBuf::from)
            .expect("cargo identifies the invoking crate directory")
            .join("../..")
            .join(relative)
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
    fn olean_input_is_bounded_before_the_decoder_runs() {
        let mut input = Cursor::new(vec![0_u8; 17]);
        let error = read_bounded_from(&mut input, 16, ".olean artifact")
            .expect_err("the seventeenth byte must refuse");
        assert_eq!(error.class(), "resource");
        assert!(error.to_string().contains("16-byte input limit"));
        assert!(error.to_string().contains("17 bytes"));
    }

    #[test]
    fn source_run_reaches_the_native_pipeline_in_human_and_robot_forms() {
        let source = repository_path("vendor/lean4-src/tests/lake/examples/deps/root/Root.lean");
        let human = run([OsString::from("run"), source.clone().into_os_string()]);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains("native source run: complete"));
        assert!(human.stdout.contains("value: 0\n"));
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
        assert!(robot.stdout.contains("\"value\":0"));
        assert!(
            robot
                .stdout
                .contains("\"ground\":\"body-checked-against-declared-type\"")
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
        assert!(help.stdout.starts_with("Usage:\n  fln run"));

        let error = run([OsString::from("olean"), OsString::from("decode")]);
        assert_eq!(error.exit_code, 2);
        assert!(error.stdout.is_empty());
        assert!(error.stderr.contains("unknown olean subcommand"));
    }
}
