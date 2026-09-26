//! **fln-cli** — front-door diagnostic adapters for the `lean`/`leanc`/`lake`
//! personalities and the `fln` multiplexer (plan §17.1; bead
//! `franken_lean-wlan`).
//!
//! `fln-core` supplies a typed [`ProjectionSnapshot`]. This crate owns the CLI
//! framing and JSON/NDJSON bytes. The bytes never become authority: exit class,
//! cause, positions, related spans, evidence links, and truncation markers all
//! remain bound to the snapshot returned beside them.

#![forbid(unsafe_code)]

mod source_check;

use fln_core::diag::{
    DIAGNOSTIC_PROJECTION_SCHEMA, DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME, DiagnosticChannel,
    DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, DiagnosticPathPolicy, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity,
    StructuredDiagnostic, StructuredInconclusive, StructuredInternalFault,
};
use fln_core::level::LevelView;
use fln_core::mode::Mode;
use fln_core::outcome::BoundedText;
use fln_hash::canon::DecodeBudget;
use fln_hash::cartridge::{
    CartridgeArchiveV1, CartridgeDecodeBudgetsV1, CartridgeIndexV1, CartridgeObjectKindV1,
    CartridgeTransportStateV1, ObjectRequirementV1, WarmDefeqCacheV1,
};
use fln_hash::certificate::DeclarationCertificateV1;
use fln_hash::domain::{Digest, Domain, DomainHasher, hash as domain_hash};
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

/// Native stack provided to the kernel worker used by both source front doors.
const SOURCE_RUN_KERNEL_STACK_BYTES: usize = 2 * 1024 * 1024;

const OLEAN_INSPECT_SCHEMA: &str = "fln.olean-inspect/1";
const OLEAN_DIFF_SCHEMA: &str = "fln.olean-diff/1";
const OLEAN_REBUILD_SCHEMA: &str = "fln.olean-rebuild/1";
const ILEAN_INSPECT_SCHEMA: &str = "fln.ilean-inspect/1";
const CHECK_OLEAN_SCHEMA: &str = "fln.check-olean/1";
const VERIFY_CAPSULE_SCHEMA: &str = "fln.verify-capsule/2";
const CAPSULE_DEFAULT_MAX_BYTES: usize = 64 * 1024 * 1024;
const FLBC_RUN_SCHEMA: &str = "fln.flbc-run/3";
const SOURCE_RUN_SCHEMA: &str = "fln.source-run/9";
const PRODUCT_SIDECAR_MAX_BYTES: usize = 64 * 1024;
const TOOLCHAIN_IMAGE_MAX_BYTES: usize = 512 * 1024 * 1024;
const OLEAN_DIFF_MAX_RENDERED_CHANGES: usize = 256;
const OLEAN_MAX_RENDERED_NAME_CHARS: usize = 256;
const OLEAN_DIFF_MAX_RENDERED_KINDS_PER_SIDE: usize = 16;
const CHECK_OLEAN_MAX_RENDERED_PRIVATE_LOOP_AUXILIARIES: usize = 32;
const CORE_OBSERVABLES_LOOP_RESIDUAL_PREFIXES: [&str; 2] = [
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.",
    "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop.",
];
const CORE_OBSERVABLES_LOOP_UNSAFE_REC_RESIDUAL_PREFIXES: [&str; 2] = [
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
    "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
];
const LEAN_NAME_HASH_PROOF_RESIDUAL_PREFIX: &str = "_private.Init.Prelude.0.Lean.Name.hash._proof_";
const LEAN_NAME_BEQ_MATCH_RESIDUAL_PREFIX: &str = "_private.Init.Prelude.0.Lean.Name.beq.match_";
const LIST_TO_ARRAY_AUX_MATCH_RESIDUAL_PREFIX: &str =
    "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_";
const CORE_OBSERVABLES_SYNTAX_MATCH_RESIDUAL_PREFIXES: [&str; 2] = [
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_",
    "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_",
];
const ARRAY_MAP_M_PROOF_RESIDUAL_PREFIX: &str =
    "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_";
const ARRAY_MAP_M_GO_RESIDUAL: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go";
const STRING_EXTRA_UNSAFE_REC_RESIDUALS: [&str; 2] = [
    "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
    "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
];
const MERGE_SORT_COMPANION_ONLY_UNSAFE_REC_RESIDUALS: [&str; 3] = [
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
];

const USAGE: &str = concat!(
    "Usage:\n",
    "  fln check-olean [--json] [--receipts PATH | --continue [--progress] [--jobs N]] [--max-bytes BYTES] PATH [ROOT...]\n",
    "  fln check-source [--json] [--max-bytes BYTES] PATH...\n",
    "    Check definitions and theorems without executing code. An import with no\n",
    "    source file under the entry's directory is read as an .olean from\n",
    "    LEAN_PATH (else the pinned toolchain's lib/lean) and its whole closure is\n",
    "    admitted by K1 and the independent checker first (trust: recheck).\n",
    "    Implicit `import Init` is not loaded.\n",
    "  fln run [--json] [--max-bytes BYTES] [--emit-flbc PATH] [--emit-sidecar PATH] [--emit-olean-snapshot PATH] PATH...\n",
    "  fln flbc run [--json] [--max-bytes BYTES] [--sidecar PATH] PATH\n",
    "  fln olean inspect [--json] [--constants] [--max-bytes BYTES] PATH\n",
    "  fln olean diff [--json] [--max-bytes BYTES] LEFT RIGHT\n",
    "  fln diff [--json] [--max-bytes BYTES] LEFT RIGHT\n",
    "  fln goals [--json] [--max-bytes BYTES] [--offset OFFSET | --line LINE [--col COL]] PATH\n",
    "  fln olean verify-rebuild [--json] [--max-bytes BYTES] PATH\n",
    "  fln ilean inspect [--json] [--max-bytes BYTES] PATH\n",
    "  fln audit --tcb [--json] [--max-bytes BYTES] PATH\n",
    "  fln why-trusts [--json] [--max-bytes BYTES] [--max-nodes N] NAME PATH\n",
    "  fln identity [--json]\n",
    "  fln serve-lsp\n",
    "  fln doctor [--json]\n",
    "  fln serve-mcp [--json]\n",
    "  fln replay [--json] PATH\n",
    "  fln cache [inspect | clear | stats]\n",
    "  fln build explain\n",
    "  fln verify-capsule [--json] [--max-bytes BYTES] PATH\n",
    "  fln --help\n",
    "  fln --version\n",
    "\n",
    "`diff` compares two pinned-format .oleans (alias for `olean diff`).\n",
    "`goals` inspects proof goals at a specified source line/column or byte offset.\n",
    "`doctor` probes the local toolchain environment (pinned Reference toolchain,\n",
    "pin agreement, census shards, optional D2 tools, a live kernel admission) and\n",
    "names the planned subsystems that are not implemented yet.\n",
    "`serve-mcp`, `replay`, and `cache` are planned capabilities that are not\n",
    "implemented; they print a typed notice and exit 5.\n",
    "`build explain` exits 5: recorded build provenance is unavailable, so it\n",
    "reports no rebuild decision.\n",
    "`verify-capsule` checks the transport completeness and content-hash integrity\n",
    "of a sealed .flnpack capsule and decodes its certificate objects; it does not\n",
    "replay certificates through a checker.\n",
    "\n",
    "Exit codes: 0 success; 1 rejected or failed; 2 usage error; 3 inconclusive or\n",
    "resource limit; 4 internal fault; 5 capability not implemented.\n",
    "\n",
    "`olean inspect` audits and decodes one pinned-format .olean. It does not\n",
    "resolve imports, kernel-check declarations, or re-emit an artifact.\n",
    "With --constants (text mode), it also prints the declaration-order\n",
    "constant inventory with bounded term sketches — the order `check-olean`\n",
    "batch indices refer to.\n",
    "`olean diff` audits and decodes two pinned-format .oleans, then reports\n",
    "bounded structural changes in module metadata and declarations. It does\n",
    "not resolve imports, kernel-check either side, or convert olean-next.\n",
    "`olean verify-rebuild` re-derives one pinned-format .olean from parsed\n",
    "semantics and requires byte identity with no codec findings. It is not\n",
    "fresh emission and does not kernel-check declarations.\n",
    "`ilean inspect` budget-decodes one pinned-format .ilean and canonical-\n",
    "reencodes it, reporting byte identity and bounded aggregate counts. It\n",
    "does not resolve modules, read source, or establish LSP compatibility.\n",
    "`check-olean` checks every declaration in one import-free pinned-format\n",
    ".olean, or a directory containing a closed import set, through K1 and the\n",
    "independent checker, atomically. It reconstructs non-safe mutual definition\n",
    "blocks, the fixed quotient initializer, and bounded safe nonrecursive Type\n",
    "inductives, and derives dependency order. It does not reconstruct other\n",
    "inductive/quotient/mutual shapes, interpret extensions, run\n",
    "K2, or satisfy G1. Module-system inputs load complete .olean.server and\n",
    ".olean.private companion chains and refuse an incomplete chain.\n",
    "With --receipts, a successful closed-module-set run (a directory root)\n",
    "also writes one hash-chained JSONL receipt set recording per-module\n",
    "verdict accounting and the independent-checker agreement grounds. Rows\n",
    "carry no clock values, so an identical set and byte content reproduce the\n",
    "file byte-for-byte. Receipts attest THIS run; they are not proof\n",
    "certificates and do not widen what the check itself establishes.\n",
    "With --continue (a directory root only), modules are checked one by one in\n",
    "the same order and each gets a verdict row: accepted, failed, inconclusive,\n",
    "internal-fault, or blocked by a named import that has no accepted verdict.\n",
    "A module is never checked against a failed import. It writes no receipts,\n",
    "and exits 0 only when every module is accepted. --progress also streams\n",
    "JSON lines to stderr: \"started\" as a module goes to the council, and\n",
    "\"decided\" with its row once every earlier row exists. --jobs N checks up to\n",
    "N modules at once; each module is checked against its own import closure, so\n",
    "the rows do not depend on N, only their wall time does. With --continue,\n",
    "further ROOT directories join the module set, so a library checks together\n",
    "with the libraries it imports (a toolchain's lib/lean, a package's build);\n",
    "a module found under two roots is refused, and --max-bytes bounds the set.\n",
    "`audit --tcb` inventories the trust surface of one import-free .olean or a\n",
    "closed directory set: every axiom declaration, plus unsafe and partial\n",
    "definitions. It decodes only; it does not kernel-check or interpret\n",
    "extensions, and it does not yet track plugins or façade classes.\n",
    "`why-trusts NAME` reports the bounded trust closure of one decoded\n",
    "constant: every axiom reachable by following constant references through\n",
    "declaration types and definition/theorem/opaque bodies across the closed\n",
    "set. Recursor reduction rules, instance selection, and rewrite provenance\n",
    "are not traversed; this is not the Palimpsest causal graph.\n",
    "`identity` prints the baked build facts: package version, product root,\n",
    "modes, and the SUITE.lock reference/corpus/toolchain pins this binary was\n",
    "compiled against. It is compile-time derived, never probed at runtime.\n",
    "\n",
    "`run` executes supported Nat/String/Bool definitions and ordered bounded #eval commands, including parenthesized checked Nat.add/sub/mul/div/mod/gcd/pred/pow/log2/shiftLeft/shiftRight/land/lor/xor/beq/ble and String.append/length/utf8ByteSize/decEq calls. The exact scalar rows also accept pin-precedence ==, |||, ^^^, &&&, +, -, ++, *, /, %, <<<, >>>, and ^ infix syntax; == is bounded Nat/String equality, not general BEq or typeclass notation,\n",
    "from an import-free caller-ordered path batch, one entry path with a bounded\n",
    "local import closure, or an explicitly supplied closed import set. One entry\n",
    "uses the same ancestor-root discovery as the native lean personality. In an\n",
    "explicit set the last path is the entry, and `import A.B` binds only a supplied\n",
    "path ending in A/B.lean. Dependency order is derived, then\n",
    "every command crosses the native parser, elaborator, K1, independent checker,\n",
    "compiler, and Golem. The final command must produce a closed Nat, String, or Bool result to report. The\n",
    "batch is atomic, and --max-bytes bounds all source inputs together. With\n",
    "--emit-flbc, the final command's exact executed artifact is published\n",
    "only after the whole batch succeeds; any existing PATH is refused, never\n",
    "replaced. --emit-sidecar requires\n",
    "--emit-flbc and publishes a standard-profile closure manifest before the\n",
    "product, so any interrupted pair fails closed by root mismatch.\n",
    "With --emit-olean-snapshot (mutually exclusive with FLBC outputs), the exact\n",
    "final checked environment is written as one import-free, non-module .olean\n",
    "snapshot and published no-clobber after success. The snapshot is for the\n",
    "bounded `check-olean` door; it is not `lean -o`, a module artifact, or a\n",
    "Reference cross-load claim. The source runner is not general Lean, LEAN_PATH\n",
    "or package discovery, implicit Prelude processing, a\n",
    "project build, a certified build product, or\n",
    "evidence that `check-olean` is complete.\n",
    "\n",
    "`flbc run` validates and executes one canonical FLBC artifact through Golem.\n",
    "With --sidecar it first binds the exact artifact, current toolchain image,\n",
    "mode, epoch, target, profile, and static closure inputs. The v1 sidecar is\n",
    "standard-profile provenance, not certified source reproducibility. It does\n",
    "not admit declarations or prove how the artifact was compiled.\n",
    "\n",
    "`serve-lsp` starts a Language Server Protocol session over stdin/stdout.\n",
    "The server handles the LSP lifecycle (initialize/shutdown/exit) and routes\n",
    "textDocument/didOpen notifications through the bounded source runner,\n",
    "projecting diagnostics via fln-server. This is a synchronous, single-file\n",
    "server suitable for editor integration testing; it is not yet the full\n",
    "asupersync-backed parallel elaboration server from the plan.\n",
);

const LEAN_USAGE: &str = concat!(
    "Usage:\n",
    "  lean [--max-bytes BYTES] PATH\n",
    "  lean --stdin [--max-bytes BYTES]\n",
    "  lean --src-deps [--max-bytes BYTES] PATH\n",
    "  lean --help\n",
    "  lean -v | --version\n",
    "  lean -V | --short-version\n",
    "  lean -g | --githash\n",
    "  lean --features\n",
    "  lean --print-prefix\n",
    "  lean --print-libdir\n",
    "  lean --server\n",
    "\n",
    "This is FrankenLean's bounded native `lean` personality. It accepts exactly\n",
    "one source path and executes the currently supported Nat/String/Bool source\n",
    "slice through the same parser, elaborator, K1, independent checker,\n",
    "compiler, canonical FLBC, and Golem path as `fln run`. Successful\n",
    "scalar and first-order function definitions are silent; unlike `fln run`,\n",
    "the final definition need not produce a closed scalar.\n",
    "Import-free #check commands may appear anywhere among supported definitions\n",
    "and #eval commands. Each is inferred and admitted through\n",
    "K1 plus the independent checker in a discarded scratch successor, then\n",
    "printed as `term : type` without compilation, VM execution, or publication.\n",
    "A query sees the checked source seed and every preceding command successor.\n",
    "Check and #eval output is buffered in source order until the whole source\n",
    "succeeds; a later failure leaves stdout empty. A local-import entry gets the\n",
    "same ordered command stream after its transitive dependency closure completes.\n",
    "An empty source file or empty --stdin stream succeeds silently.\n",
    "Dependency definitions, #eval, and scratch-only #check run silently.\n",
    "Every dependency query is checked against that module's transitive imports.\n",
    "An import-only entry succeeds silently after its checked dependency closure.\n",
    "The bounded renderer does not pretty-print dependent or other unsupported types.\n",
    "For `import A.B`,\n",
    "the first direct import must identify exactly one ancestor source root;\n",
    "the complete local A/B.lean closure is then loaded under the same aggregate\n",
    "limits before execution. Symlink, missing, and ambiguous imports are refused.\n",
    "--stdin reads one bounded import-free source from standard input.\n",
    "--src-deps prints validated direct local source imports in source order\n",
    "without elaborating or executing the file.\n",
    "-q and --quiet are accepted on source operations; this bounded personality\n",
    "currently has no verbose success messages for them to suppress. --githash\n",
    "prints the exact pinned Reference commit, and --features reports [] because\n",
    "this binary has no LLVM backend. --print-prefix and --print-libdir derive\n",
    "the conventional installation paths only when the running executable is\n",
    "located at <prefix>/bin/lean; development binaries outside that layout are\n",
    "refused instead of reporting a false toolchain root.\n",
    "--server starts the LSP server over stdin/stdout, matching the Reference's\n",
    "`lean --server` entry point used by editor extensions. The server handles\n",
    "the LSP lifecycle and textDocument/didOpen, running opened documents through\n",
    "the bounded source pipeline and projecting diagnostics. This is the same\n",
    "transport as `fln serve-lsp`.\n",
    "This does not implement the Reference CLI's option set, LEAN_PATH/package or\n",
    ".olean discovery, implicit Prelude processing, general Lean elaboration, or\n",
    "diagnostic parity. Discovery assumes a trusted filesystem namespace that\n",
    "does not change during the invocation; directory-handle race sealing is not\n",
    "yet implemented.\n",
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
    SourceCheck {
        paths: Vec<PathBuf>,
        max_bytes: usize,
        json: bool,
    },
    Help,
    Version,
    CheckOlean {
        /// The input path, then any further module-set roots (`--continue`
        /// only). Never empty.
        roots: Vec<PathBuf>,
        max_bytes: usize,
        json: bool,
        receipts: Option<PathBuf>,
        continue_on_failure: bool,
        progress: bool,
        jobs: std::num::NonZeroUsize,
    },
    SourceRun {
        paths: Vec<PathBuf>,
        max_bytes: usize,
        json: bool,
        emit_flbc: Option<PathBuf>,
        emit_sidecar: Option<PathBuf>,
        emit_olean_snapshot: Option<PathBuf>,
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
        constants: bool,
    },
    OleanDiff {
        left: PathBuf,
        right: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    OleanVerifyRebuild {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    IleanInspect {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    Identity {
        json: bool,
    },
    AuditTcb {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    WhyTrusts {
        name: String,
        path: PathBuf,
        max_bytes: usize,
        max_nodes: usize,
        json: bool,
    },
    ServeLsp,
    Goals {
        path: PathBuf,
        line: Option<usize>,
        col: Option<usize>,
        offset: Option<usize>,
        max_bytes: usize,
        json: bool,
    },
    CapabilityNotice {
        command: String,
        json: bool,
    },
    VerifyCapsule {
        path: PathBuf,
        max_bytes: usize,
        json: bool,
    },
    BuildExplain {
        target: Option<String>,
        dir: Option<PathBuf>,
        faithful_invalidation: bool,
        json: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LeanCommand {
    Help,
    Version,
    ShortVersion,
    GitHash,
    Features,
    PrintPrefix,
    PrintLibdir,
    Server,
    Stdin { max_bytes: usize },
    SourceDependencies { path: PathBuf, max_bytes: usize },
    Source { path: PathBuf, max_bytes: usize },
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
    Resource {
        detail: String,
    },
}

impl BoundedReadFailure {
    const fn class(&self) -> &'static str {
        match self {
            Self::Input { .. } => "input",
            Self::TooLarge { .. } | Self::Allocation { .. } | Self::Resource { .. } => "resource",
        }
    }

    const fn exit_code(&self) -> u8 {
        match self {
            Self::Input { .. } => 1,
            Self::TooLarge { .. } | Self::Allocation { .. } | Self::Resource { .. } => 3,
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
            Self::Resource { detail } => f.write_str(detail),
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

#[derive(Debug)]
enum OleanDiffFailure {
    Read(BoundedReadFailure),
    Decode {
        side: &'static str,
        error: fln::OleanDecodeError,
    },
    Allocation {
        resource: &'static str,
        requested: usize,
    },
}

impl OleanDiffFailure {
    const fn class(&self) -> &'static str {
        match self {
            Self::Read(error) => error.class(),
            Self::Decode { error, .. } if error.is_resource_exhaustion() => "resource",
            Self::Allocation { .. } => "resource",
            Self::Decode { .. } => "decode",
        }
    }
}

impl fmt::Display for OleanDiffFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(error) => error.fmt(formatter),
            Self::Decode { side, error } => write!(formatter, "{side} artifact: {error}"),
            Self::Allocation {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
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
    let mut emit_olean_snapshot = None;
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
        let snapshot = if options && argument == "--emit-olean-snapshot" {
            Some(arguments.next().ok_or_else(|| {
                UsageError("--emit-olean-snapshot requires a following output path".to_owned())
            })?)
        } else if options {
            argument
                .to_str()
                .and_then(|value| value.strip_prefix("--emit-olean-snapshot="))
                .map(OsString::from)
        } else {
            None
        };
        if let Some(path) = snapshot {
            if path.is_empty() {
                return Err(UsageError(
                    "--emit-olean-snapshot path must not be empty".to_owned(),
                ));
            }
            if emit_olean_snapshot.replace(PathBuf::from(path)).is_some() {
                return Err(UsageError(
                    "--emit-olean-snapshot may be supplied at most once".to_owned(),
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
    if emit_olean_snapshot.is_some() && (emit_flbc.is_some() || emit_sidecar.is_some()) {
        return Err(UsageError(
            "--emit-olean-snapshot is mutually exclusive with --emit-flbc and --emit-sidecar"
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
    for output in [
        emit_flbc.as_deref(),
        emit_sidecar.as_deref(),
        emit_olean_snapshot.as_deref(),
    ]
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
        emit_olean_snapshot,
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
    let mut receipts = None;
    let mut continue_on_failure = false;
    let mut progress = false;
    let mut jobs: Option<std::num::NonZeroUsize> = None;
    let mut filtered = Vec::new();
    let mut options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            filtered.push(argument);
            continue;
        }
        if options && argument == "--continue" {
            if continue_on_failure {
                return Err(UsageError(
                    "--continue may be supplied at most once".to_owned(),
                ));
            }
            continue_on_failure = true;
            continue;
        }
        if options && argument == "--progress" {
            if progress {
                return Err(UsageError(
                    "--progress may be supplied at most once".to_owned(),
                ));
            }
            progress = true;
            continue;
        }
        let jobs_value =
            if options && argument == "--jobs" {
                Some(arguments.next().ok_or_else(|| {
                    UsageError("--jobs requires a following thread count".to_owned())
                })?)
            } else if options {
                argument
                    .to_str()
                    .and_then(|value| value.strip_prefix("--jobs="))
                    .map(OsString::from)
            } else {
                None
            };
        if let Some(value) = jobs_value {
            if jobs.is_some() {
                return Err(UsageError("--jobs may be supplied at most once".to_owned()));
            }
            jobs = Some(
                value
                    .to_str()
                    .and_then(|text| text.parse::<std::num::NonZeroUsize>().ok())
                    .ok_or_else(|| UsageError("--jobs takes a positive thread count".to_owned()))?,
            );
            continue;
        }
        let selected = if options && argument == "--receipts" {
            Some(arguments.next().ok_or_else(|| {
                UsageError("--receipts requires a following output path".to_owned())
            })?)
        } else if options {
            argument
                .to_str()
                .and_then(|value| value.strip_prefix("--receipts="))
                .map(OsString::from)
        } else {
            None
        };
        if let Some(path) = selected {
            if path.is_empty() {
                return Err(UsageError("--receipts path must not be empty".to_owned()));
            }
            if receipts.replace(PathBuf::from(path)).is_some() {
                return Err(UsageError(
                    "--receipts may be supplied at most once".to_owned(),
                ));
            }
            continue;
        }
        filtered.push(argument);
    }
    let Some((paths, max_bytes, json)) =
        parse_path_options(filtered, "check-olean", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    match paths.as_slice() {
        [_] => {}
        [_, _, ..] if continue_on_failure => {}
        _ => {
            return Err(UsageError(
                "check-olean accepts exactly one input path, or several module-set roots with --continue".to_owned(),
            ));
        }
    }
    if progress && !continue_on_failure {
        return Err(UsageError(
            "--progress streams per-module rows, so it requires --continue".to_owned(),
        ));
    }
    if jobs.is_some() && !continue_on_failure {
        return Err(UsageError(
            "--jobs schedules per-module checks, so it requires --continue".to_owned(),
        ));
    }
    Ok(MultiplexerCommand::CheckOlean {
        roots: paths,
        max_bytes,
        json,
        receipts,
        continue_on_failure,
        progress,
        jobs: jobs.unwrap_or(std::num::NonZeroUsize::MIN),
    })
}

fn parse_audit_tcb(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut tcb = false;
    let mut filtered = Vec::new();
    let mut options = true;
    for argument in arguments {
        if options && argument == "--" {
            options = false;
            filtered.push(argument);
            continue;
        }
        if options && argument == "--tcb" {
            if tcb {
                return Err(UsageError("--tcb may be supplied at most once".to_owned()));
            }
            tcb = true;
            continue;
        }
        if options && argument.to_str() == Some("--help") {
            return Err(UsageError("--help must be used alone".to_owned()));
        }
        filtered.push(argument);
    }
    if !tcb {
        return Err(UsageError(
            "audit requires --tcb; no other audit scope is implemented".to_owned(),
        ));
    }
    let Some((paths, max_bytes, json)) =
        parse_path_options(filtered, "audit --tcb", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        // `audit --tcb --help` is answered by the multiplexer usage text.
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "audit accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::AuditTcb {
        path: path.clone(),
        max_bytes,
        json,
    })
}

fn parse_why_trusts(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    const DEFAULT_MAX_NODES: usize = 50_000;
    const MAX_NODES_CEILING: usize = 10_000_000;
    let mut max_nodes = DEFAULT_MAX_NODES;
    let mut max_nodes_seen = false;
    let mut filtered = Vec::new();
    let mut options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            filtered.push(argument);
            continue;
        }
        let value =
            if options && argument == "--max-nodes" {
                Some(arguments.next().ok_or_else(|| {
                    UsageError("--max-nodes requires a following integer".to_owned())
                })?)
            } else if options {
                argument
                    .to_str()
                    .and_then(|value| value.strip_prefix("--max-nodes="))
                    .map(OsString::from)
            } else {
                None
            };
        if let Some(value) = value {
            if max_nodes_seen {
                return Err(UsageError(
                    "--max-nodes may be supplied at most once".to_owned(),
                ));
            }
            max_nodes_seen = true;
            max_nodes = parse_byte_limit(&value).map_err(|_| {
                UsageError("--max-nodes requires an ASCII integer within range".to_owned())
            })?;
            if max_nodes > MAX_NODES_CEILING {
                return Err(UsageError(format!(
                    "--max-nodes exceeds the {MAX_NODES_CEILING}-node ceiling"
                )));
            }
            continue;
        }
        filtered.push(argument);
    }
    let Some((paths, max_bytes, json)) =
        parse_path_options(filtered, "why-trusts", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [name, path] = paths.as_slice() else {
        return Err(UsageError(
            "why-trusts accepts exactly one constant name and one input path".to_owned(),
        ));
    };
    let Some(name) = name.to_str() else {
        return Err(UsageError(
            "why-trusts constant names are dotted ASCII identifiers".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::WhyTrusts {
        name: name.to_owned(),
        path: path.clone(),
        max_bytes,
        max_nodes,
        json,
    })
}

fn parse_identity(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut json = false;
    for argument in arguments {
        if argument == "--json" {
            if json {
                return Err(UsageError("--json may be supplied at most once".to_owned()));
            }
            json = true;
            continue;
        }
        return Err(UsageError(format!(
            "identity accepts only an optional --json, not {:?}",
            argument.to_string_lossy()
        )));
    }
    Ok(MultiplexerCommand::Identity { json })
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
    let mut constants = false;
    let filtered: Vec<OsString> = arguments
        .into_iter()
        .filter(|argument| {
            if argument.to_string_lossy() == "--constants" {
                constants = true;
                false
            } else {
                true
            }
        })
        .collect();
    let Some((paths, max_bytes, json)) =
        parse_path_options(filtered, "olean inspect", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
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
        constants,
    })
}

fn parse_olean_diff(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((paths, max_bytes, json)) =
        parse_path_options(arguments, "olean diff", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [left, right] = paths.as_slice() else {
        return Err(UsageError(
            "olean diff accepts exactly two input paths".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::OleanDiff {
        left: left.clone(),
        right: right.clone(),
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

fn parse_ilean_inspect(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((paths, max_bytes, json)) =
        parse_path_options(arguments, "ilean inspect", OLEAN_INSPECT_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "ilean inspect accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::IleanInspect {
        path: path.clone(),
        max_bytes,
        json,
    })
}

fn parse_path_line_col(s: &str) -> Option<(&str, usize, Option<usize>)> {
    let mut parts = s.rsplitn(3, ':');
    let last = parts.next()?;
    let second = parts.next()?;
    if let (Ok(c), Ok(l)) = (last.parse::<usize>(), second.parse::<usize>()) {
        let p = parts.next()?;
        if !p.is_empty() {
            return Some((p, l, Some(c)));
        }
    }
    if let Ok(l) = last.parse::<usize>() {
        let p = second;
        if !p.is_empty() && parts.next().is_none() {
            return Some((p, l, None));
        }
    }
    None
}

fn parse_goals(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut path: Option<PathBuf> = None;
    let mut line: Option<usize> = None;
    let mut col: Option<usize> = None;
    let mut offset: Option<usize> = None;
    let mut max_bytes = SOURCE_RUN_DEFAULT_MAX_BYTES;
    let mut json = false;

    let mut iter = arguments.into_iter();
    while let Some(arg) = iter.next() {
        if arg == "--help" || arg == "-h" || arg == "help" {
            return Ok(MultiplexerCommand::Help);
        }
        if arg == "--json" {
            json = true;
            continue;
        }
        if arg == "--max-bytes" {
            let Some(val) = iter.next() else {
                return Err(UsageError(
                    "--max-bytes requires an integer value".to_owned(),
                ));
            };
            let val_str = val.to_string_lossy();
            max_bytes = val_str
                .parse::<usize>()
                .map_err(|_| UsageError(format!("invalid --max-bytes value {val_str:?}")))?;
            continue;
        }
        if arg == "--offset" {
            let Some(val) = iter.next() else {
                return Err(UsageError("--offset requires an integer value".to_owned()));
            };
            let val_str = val.to_string_lossy();
            offset = Some(
                val_str
                    .parse::<usize>()
                    .map_err(|_| UsageError(format!("invalid --offset value {val_str:?}")))?,
            );
            continue;
        }
        if arg == "--line" {
            let Some(val) = iter.next() else {
                return Err(UsageError("--line requires an integer value".to_owned()));
            };
            let val_str = val.to_string_lossy();
            line = Some(
                val_str
                    .parse::<usize>()
                    .map_err(|_| UsageError(format!("invalid --line value {val_str:?}")))?,
            );
            continue;
        }
        if arg == "--col" {
            let Some(val) = iter.next() else {
                return Err(UsageError("--col requires an integer value".to_owned()));
            };
            let val_str = val.to_string_lossy();
            col = Some(
                val_str
                    .parse::<usize>()
                    .map_err(|_| UsageError(format!("invalid --col value {val_str:?}")))?,
            );
            continue;
        }
        if let Some(arg_str) = arg.to_str()
            && arg_str.starts_with("--")
        {
            return Err(UsageError(format!("unknown option {arg_str:?}")));
        }
        if path.is_some() {
            return Err(UsageError(
                "goals accepts exactly one input path".to_owned(),
            ));
        }
        let arg_str = arg.to_string_lossy();
        if let Some((p, l, c)) = parse_path_line_col(&arg_str) {
            path = Some(PathBuf::from(p));
            if line.is_none() {
                line = Some(l);
            }
            if col.is_none() && c.is_some() {
                col = c;
            }
        } else {
            path = Some(PathBuf::from(arg));
        }
    }

    let Some(path) = path else {
        return Err(UsageError("goals requires a source path".to_owned()));
    };

    if offset.is_some() && (line.is_some() || col.is_some()) {
        return Err(UsageError(
            "cannot combine --offset with --line or --col".to_owned(),
        ));
    }

    Ok(MultiplexerCommand::Goals {
        path,
        line,
        col,
        offset,
        max_bytes,
        json,
    })
}

fn parse_capability_notice(
    command: String,
    arguments: Vec<OsString>,
) -> Result<MultiplexerCommand, UsageError> {
    let mut json = false;
    for arg in arguments {
        if arg == "--help" || arg == "-h" || arg == "help" {
            return Ok(MultiplexerCommand::Help);
        }
        if arg == "--json" {
            json = true;
        }
    }
    Ok(MultiplexerCommand::CapabilityNotice { command, json })
}

fn parse_doctor(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut json = false;
    let mut sql = false;
    for arg in arguments {
        if arg == "--help" || arg == "-h" || arg == "help" {
            return Ok(MultiplexerCommand::Help);
        } else if arg == "--json" {
            json = true;
        } else if arg == "--sql" {
            sql = true;
        } else {
            return Err(UsageError(format!(
                "doctor accepts only --json (and the unimplemented --sql), got {:?}",
                arg.to_string_lossy()
            )));
        }
    }
    let command = if sql { "doctor --sql" } else { "doctor" };
    Ok(MultiplexerCommand::CapabilityNotice {
        command: command.to_owned(),
        json,
    })
}

fn parse_verify_capsule(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let Some((paths, max_bytes, json)) =
        parse_path_options(arguments, "verify-capsule", CAPSULE_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(
            "verify-capsule accepts exactly one input path".to_owned(),
        ));
    };
    Ok(MultiplexerCommand::VerifyCapsule {
        path: path.clone(),
        max_bytes,
        json,
    })
}

fn parse_build_explain(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let mut dir: Option<PathBuf> = None;
    let mut target: Option<String> = None;
    let mut faithful_invalidation = false;
    let mut json = false;
    let mut iter = arguments.into_iter();

    while let Some(arg) = iter.next() {
        let s = arg.to_string_lossy();
        if s == "--help" || s == "-h" || s == "help" {
            return Ok(MultiplexerCommand::Help);
        }
        if s == "--json" || s == "-J" {
            json = true;
            continue;
        }
        if s == "--faithful-invalidation" {
            faithful_invalidation = true;
            continue;
        }
        if s == "--dir" || s == "-d" {
            let Some(d) = iter.next() else {
                return Err(UsageError(
                    "missing directory argument for --dir".to_owned(),
                ));
            };
            dir = Some(PathBuf::from(d));
            continue;
        }
        if let Some(rest) = s.strip_prefix("--dir=") {
            dir = Some(PathBuf::from(rest));
            continue;
        }
        if let Some(rest) = s.strip_prefix("-d=") {
            dir = Some(PathBuf::from(rest));
            continue;
        }
        if s.starts_with('-') {
            return Err(UsageError(format!(
                "unknown option '{s}' for build explain"
            )));
        }
        if target.is_none() {
            target = Some(s.into_owned());
        } else {
            return Err(UsageError(format!(
                "unexpected argument '{s}' for build explain"
            )));
        }
    }

    Ok(MultiplexerCommand::BuildExplain {
        target,
        dir,
        faithful_invalidation,
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
    if command == "check-source" {
        return source_check::parse(arguments.collect());
    }
    if command == "run" {
        return parse_source_run(arguments.collect());
    }
    if command == "check-olean" {
        return parse_check_olean(arguments.collect());
    }
    if command == "audit" {
        return parse_audit_tcb(arguments.collect());
    }
    if command == "why-trusts" {
        return parse_why_trusts(arguments.collect());
    }
    if command == "identity" {
        return parse_identity(arguments.collect());
    }
    if command == "serve-lsp" {
        return Ok(MultiplexerCommand::ServeLsp);
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
    if command == "ilean" {
        let Some(subcommand) = arguments.next() else {
            return Err(UsageError(
                "ilean requires the `inspect` subcommand".to_owned(),
            ));
        };
        if subcommand == "--help" || subcommand == "-h" || subcommand == "help" {
            return Ok(MultiplexerCommand::Help);
        }
        if subcommand == "inspect" {
            return parse_ilean_inspect(arguments.collect());
        }
        return Err(UsageError(format!(
            "unknown ilean subcommand {:?}",
            subcommand.to_string_lossy()
        )));
    }
    if command == "diff" {
        return parse_olean_diff(arguments.collect());
    }
    if command == "goals" {
        return parse_goals(arguments.collect());
    }
    if command == "verify-capsule" {
        return parse_verify_capsule(arguments.collect());
    }
    if command == "doctor" {
        return parse_doctor(arguments.collect());
    }
    if command == "serve-mcp" || command == "replay" || command == "cache" {
        return parse_capability_notice(
            command.to_string_lossy().into_owned(),
            arguments.collect(),
        );
    }
    if command == "build" {
        let mut rest: Vec<OsString> = arguments.collect();
        if rest.first().map(|s| s.to_string_lossy()) == Some("explain".into()) {
            rest.remove(0);
            return parse_build_explain(rest);
        }
        return parse_capability_notice("build".to_owned(), rest);
    }
    if command != "olean" {
        return Err(UsageError(format!(
            "unknown fln command {:?}",
            command.to_string_lossy()
        )));
    }
    let Some(subcommand) = arguments.next() else {
        return Err(UsageError(
            "olean requires an `inspect`, `diff`, or `verify-rebuild` subcommand".to_owned(),
        ));
    };
    if subcommand == "--help" || subcommand == "-h" || subcommand == "help" {
        return Ok(MultiplexerCommand::Help);
    }
    if subcommand == "inspect" {
        return parse_olean_inspect(arguments.collect());
    }
    if subcommand == "diff" {
        return parse_olean_diff(arguments.collect());
    }
    if subcommand == "verify-rebuild" {
        return parse_olean_verify_rebuild(arguments.collect());
    }
    Err(UsageError(format!(
        "unknown olean subcommand {:?}",
        subcommand.to_string_lossy()
    )))
}

fn parse_lean_command(
    arguments: impl IntoIterator<Item = OsString>,
) -> Result<LeanCommand, UsageError> {
    let mut arguments = arguments.into_iter();
    let Some(first) = arguments.next() else {
        return Ok(LeanCommand::Help);
    };
    if first == "--help" || first == "-h" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::Help)
        } else {
            Err(UsageError("--help must be used alone".to_owned()))
        };
    }
    if first == "--version" || first == "-v" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::Version)
        } else {
            Err(UsageError("--version must be used alone".to_owned()))
        };
    }
    if first == "--short-version" || first == "-V" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::ShortVersion)
        } else {
            Err(UsageError("--short-version must be used alone".to_owned()))
        };
    }
    if first == "--githash" || first == "-g" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::GitHash)
        } else {
            Err(UsageError("--githash must be used alone".to_owned()))
        };
    }
    if first == "--features" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::Features)
        } else {
            Err(UsageError("--features must be used alone".to_owned()))
        };
    }
    if first == "--print-prefix" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::PrintPrefix)
        } else {
            Err(UsageError("--print-prefix must be used alone".to_owned()))
        };
    }
    if first == "--print-libdir" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::PrintLibdir)
        } else {
            Err(UsageError("--print-libdir must be used alone".to_owned()))
        };
    }
    if first == "--server" {
        return if arguments.next().is_none() {
            Ok(LeanCommand::Server)
        } else {
            Err(UsageError("--server must be used alone".to_owned()))
        };
    }

    let mut path = None;
    let mut max_bytes = SOURCE_RUN_DEFAULT_MAX_BYTES;
    let mut max_bytes_seen = false;
    let mut stdin_source = false;
    let mut source_dependencies = false;
    let mut options = true;
    let mut arguments = std::iter::once(first).chain(arguments);
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && argument == "--max-bytes" {
            if max_bytes_seen {
                return Err(UsageError(
                    "--max-bytes may be supplied at most once".to_owned(),
                ));
            }
            let value = arguments
                .next()
                .ok_or_else(|| UsageError("--max-bytes requires a following integer".to_owned()))?;
            max_bytes = parse_byte_limit(&value)?;
            max_bytes_seen = true;
            continue;
        }
        if options && argument == "--src-deps" {
            if source_dependencies {
                return Err(UsageError(
                    "--src-deps may be supplied at most once".to_owned(),
                ));
            }
            source_dependencies = true;
            continue;
        }
        if options && argument == "--stdin" {
            if stdin_source {
                return Err(UsageError(
                    "--stdin may be supplied at most once".to_owned(),
                ));
            }
            stdin_source = true;
            continue;
        }
        if options && (argument == "--quiet" || argument == "-q") {
            continue;
        }
        if options
            && let Some(value) = argument
                .to_str()
                .and_then(|value| value.strip_prefix("--max-bytes="))
        {
            if max_bytes_seen {
                return Err(UsageError(
                    "--max-bytes may be supplied at most once".to_owned(),
                ));
            }
            max_bytes = parse_byte_limit(&OsString::from(value))?;
            max_bytes_seen = true;
            continue;
        }
        if options && argument.to_string_lossy().starts_with('-') {
            if argument == "--help" || argument == "-h" {
                return Err(UsageError("--help must be used alone".to_owned()));
            }
            if argument == "--version" || argument == "-v" {
                return Err(UsageError("--version must be used alone".to_owned()));
            }
            if argument == "--short-version" || argument == "-V" {
                return Err(UsageError("--short-version must be used alone".to_owned()));
            }
            if argument == "--githash" || argument == "-g" {
                return Err(UsageError("--githash must be used alone".to_owned()));
            }
            if argument == "--features" {
                return Err(UsageError("--features must be used alone".to_owned()));
            }
            if argument == "--print-prefix" {
                return Err(UsageError("--print-prefix must be used alone".to_owned()));
            }
            if argument == "--print-libdir" {
                return Err(UsageError("--print-libdir must be used alone".to_owned()));
            }
            return Err(UsageError(format!(
                "unknown lean option {:?}",
                argument.to_string_lossy()
            )));
        }
        if argument.is_empty() {
            return Err(UsageError("source path must not be empty".to_owned()));
        }
        if path.replace(PathBuf::from(argument)).is_some() {
            return Err(UsageError(
                "lean accepts exactly one source path".to_owned(),
            ));
        }
    }

    if stdin_source {
        if source_dependencies {
            return Err(UsageError(
                "--stdin and --src-deps cannot be combined in the bounded native personality"
                    .to_owned(),
            ));
        }
        if path.is_some() {
            return Err(UsageError(
                "--stdin does not accept a source path".to_owned(),
            ));
        }
        return Ok(LeanCommand::Stdin { max_bytes });
    }
    let path = path.ok_or_else(|| UsageError("lean requires PATH or --stdin".to_owned()))?;
    if source_dependencies {
        Ok(LeanCommand::SourceDependencies { path, max_bytes })
    } else {
        Ok(LeanCommand::Source { path, max_bytes })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LeanInstallationPaths {
    prefix: PathBuf,
    libdir: PathBuf,
}

fn derive_lean_installation_paths(executable: &Path) -> Result<LeanInstallationPaths, String> {
    if let Some(sysroot) = std::env::var_os("LEAN_SYSROOT")
        && !sysroot.is_empty()
    {
        let prefix = PathBuf::from(sysroot);
        let libdir = prefix.join("lib").join("lean");
        return Ok(LeanInstallationPaths { prefix, libdir });
    }
    let bin = executable.parent().ok_or_else(|| {
        format!(
            "current executable {} has no parent directory",
            executable.display()
        )
    })?;
    if bin.file_name() != Some(std::ffi::OsStr::new("bin")) {
        return Err(format!(
            "current executable {} is not located at <prefix>/bin/lean",
            executable.display()
        ));
    }
    let prefix = bin.parent().ok_or_else(|| {
        format!(
            "current executable {} has no installation prefix",
            executable.display()
        )
    })?;
    if prefix.as_os_str().is_empty() {
        return Err(format!(
            "current executable {} has an empty installation prefix",
            executable.display()
        ));
    }
    Ok(LeanInstallationPaths {
        prefix: prefix.to_path_buf(),
        libdir: prefix.join("lib").join("lean"),
    })
}

fn lean_installation_path_output(
    select: impl FnOnce(LeanInstallationPaths) -> PathBuf,
) -> MultiplexerOutput {
    let executable = match std::env::current_exe() {
        Ok(executable) => executable,
        Err(error) => {
            return MultiplexerOutput::failure(
                format!("lean: installation: cannot locate the running executable: {error}\n"),
                1,
            );
        }
    };
    let paths = match derive_lean_installation_paths(&executable) {
        Ok(paths) => paths,
        Err(error) => {
            return MultiplexerOutput::failure(format!("lean: installation: {error}\n"), 1);
        }
    };
    let path = select(paths);
    let Some(path) = path.to_str() else {
        return MultiplexerOutput::failure(
            "lean: installation: derived path is not valid UTF-8\n".to_owned(),
            1,
        );
    };
    if path
        .chars()
        .any(|character| matches!(character, '\n' | '\r'))
    {
        return MultiplexerOutput::failure(
            "lean: installation: derived path contains a line break\n".to_owned(),
            1,
        );
    }
    MultiplexerOutput::success(format!("{path}\n"))
}

fn read_bounded_from<R: Read + ?Sized>(
    reader: &mut R,
    max_bytes: usize,
    subject: &'static str,
) -> Result<Vec<u8>, BoundedReadFailure> {
    let mut bytes = Vec::new();
    let mut chunk = [0_u8; 8192];
    loop {
        let read = match reader.read(&mut chunk) {
            Ok(read) => read,
            Err(error) if matches!(error.kind(), std::io::ErrorKind::Interrupted) => continue,
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

fn closed_cli_value(
    exit: &fln::VmExit,
) -> Result<Option<SourceFinalValue>, fln::ClosedVmValueError> {
    fln::closed_vm_value(exit).map(|value| {
        value.map(|value| match value {
            fln::ClosedVmValue::Scalar(value) => SourceFinalValue::Nat(value.to_string()),
            fln::ClosedVmValue::NonnegativeMpz(value) => SourceFinalValue::Nat(value),
            fln::ClosedVmValue::String(value) => SourceFinalValue::String(value),
        })
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SourceResultKind {
    Nat,
    String,
    Bool,
}

impl SourceResultKind {
    const fn name(self) -> &'static str {
        match self {
            Self::Nat => "Nat",
            Self::String => "String",
            Self::Bool => "Bool",
        }
    }
}

fn source_result_kind(type_: &fln::Expr) -> Option<SourceResultKind> {
    if type_ == &fln::Expr::const_(fln::Name::from_components(["Nat"]), Vec::new()) {
        Some(SourceResultKind::Nat)
    } else if type_ == &fln::Expr::const_(fln::Name::from_components(["String"]), Vec::new()) {
        Some(SourceResultKind::String)
    } else if type_ == &fln::Expr::const_(fln::Name::from_components(["Bool"]), Vec::new()) {
        Some(SourceResultKind::Bool)
    } else {
        None
    }
}

#[derive(Debug)]
enum SourceValueProjectionError {
    Runtime(fln::ClosedVmValueError),
    InvalidBoolScalar(usize),
    RepresentationMismatch {
        declared: SourceResultKind,
        runtime: &'static str,
    },
}

impl std::fmt::Display for SourceValueProjectionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Runtime(error) => error.fmt(formatter),
            Self::InvalidBoolScalar(value) => write!(
                formatter,
                "checked Bool result used invalid runtime scalar {value}; expected 0 or 1"
            ),
            Self::RepresentationMismatch { declared, runtime } => write!(
                formatter,
                "checked {} result used incompatible {runtime} runtime representation",
                declared.name()
            ),
        }
    }
}

impl std::error::Error for SourceValueProjectionError {}

impl From<fln::ClosedVmValueError> for SourceValueProjectionError {
    fn from(error: fln::ClosedVmValueError) -> Self {
        Self::Runtime(error)
    }
}

fn closed_source_cli_value(
    runtime_type: &fln::Expr,
    exit: &fln::VmExit,
) -> Result<Option<SourceFinalValue>, SourceValueProjectionError> {
    let Some(declared) = source_result_kind(runtime_type) else {
        return Ok(None);
    };
    let Some(value) = fln::closed_vm_value(exit)? else {
        return Ok(None);
    };
    project_source_closed_value(declared, value).map(Some)
}

fn project_source_closed_value(
    declared: SourceResultKind,
    value: fln::ClosedVmValue,
) -> Result<SourceFinalValue, SourceValueProjectionError> {
    match (declared, value) {
        (SourceResultKind::Nat, fln::ClosedVmValue::Scalar(value)) => {
            Ok(SourceFinalValue::Nat(value.to_string()))
        }
        (SourceResultKind::Nat, fln::ClosedVmValue::NonnegativeMpz(value)) => {
            Ok(SourceFinalValue::Nat(value))
        }
        (SourceResultKind::String, fln::ClosedVmValue::String(value)) => {
            Ok(SourceFinalValue::String(value))
        }
        (SourceResultKind::Bool, fln::ClosedVmValue::Scalar(0)) => {
            Ok(SourceFinalValue::Bool(false))
        }
        (SourceResultKind::Bool, fln::ClosedVmValue::Scalar(1)) => Ok(SourceFinalValue::Bool(true)),
        (SourceResultKind::Bool, fln::ClosedVmValue::Scalar(value)) => {
            Err(SourceValueProjectionError::InvalidBoolScalar(value))
        }
        (declared, fln::ClosedVmValue::Scalar(_)) => {
            Err(SourceValueProjectionError::RepresentationMismatch {
                declared,
                runtime: "scalar",
            })
        }
        (declared, fln::ClosedVmValue::NonnegativeMpz(_)) => {
            Err(SourceValueProjectionError::RepresentationMismatch {
                declared,
                runtime: "nonnegative mpz",
            })
        }
        (declared, fln::ClosedVmValue::String(_)) => {
            Err(SourceValueProjectionError::RepresentationMismatch {
                declared,
                runtime: "String",
            })
        }
    }
}

fn render_flbc_success(
    bytes: usize,
    returned: &fln::VmExit,
    sidecar: Option<&fln::FlbcProductSidecarV1>,
    json: bool,
) -> MultiplexerOutput {
    let value = match closed_cli_value(returned) {
        Ok(value) => value,
        Err(error) => {
            return flbc_failure("internal-fault", &error.to_string(), false, None, json, 4);
        }
    };
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
    let usage = (
        returned.usage.steps,
        returned.usage.system_polls,
        returned.usage.peak_stack_depth,
    );
    let stdout = if json {
        let value = value
            .as_ref()
            .map(SourceFinalValue::json)
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
                "\"artifactBytes\":{},\"returnKind\":{},\"returnValue\":{},",
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
        let value = value
            .as_ref()
            .map(ToString::to_string)
            .unwrap_or_else(|| "not a closed scalar or String".to_owned());
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
                "return value: {}\n",
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

fn render_olean_human(bytes: usize, decoded: &fln::DecodedOlean, constants: bool) -> String {
    let mut out = format!(
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
    );
    if constants {
        out.push_str(&render_constant_sketch(decoded));
    }
    out
}

/// Bounded per-constant diagnostic sketch (`olean inspect --constants`).
///
/// Human-mode only. Renders the declaration order the checker council walks,
/// which is the order `fln check-olean` reports batch indices against, with a
/// depth-and-width-bounded term sketch per constant so admission halts can be
/// diagnosed without another tool.
const CONSTANT_SKETCH_ROWS: usize = 4096;
const CONSTANT_SKETCH_TERM_CHARS: usize = 700;

fn constant_kind_label(info: &fln::ConstantInfo) -> &'static str {
    match info {
        fln::ConstantInfo::Axiom(_) => "axiom",
        fln::ConstantInfo::Defn(_) => "def",
        fln::ConstantInfo::Thm(_) => "thm",
        fln::ConstantInfo::Opaque(_) => "opaque",
        fln::ConstantInfo::Quot(_) => "quot",
        fln::ConstantInfo::Induct(_) => "inductive",
        fln::ConstantInfo::Ctor(_) => "ctor",
        fln::ConstantInfo::Rec(_) => "rec",
    }
}

fn sketch_level(level: &fln::Level, out: &mut String) {
    match level.view() {
        LevelView::Zero => out.push('0'),
        LevelView::Succ(inner) => {
            out.push_str("succ(");
            sketch_level(inner, out);
            out.push(')');
        }
        LevelView::Max(lhs, rhs) => {
            out.push_str("max(");
            sketch_level(lhs, out);
            out.push(',');
            sketch_level(rhs, out);
            out.push(')');
        }
        LevelView::IMax(lhs, rhs) => {
            out.push_str("imax(");
            sketch_level(lhs, out);
            out.push(',');
            sketch_level(rhs, out);
            out.push(')');
        }
        LevelView::Param(name) => out.push_str(&name.to_display_string()),
        LevelView::MVar(_) => out.push_str("?mvar"),
    }
}

fn sketch_expr(expr: &fln::Expr, budget: &mut usize, out: &mut String) {
    if *budget == 0 || out.len() > CONSTANT_SKETCH_TERM_CHARS {
        out.push('…');
        return;
    }
    *budget -= 1;
    match expr.node() {
        fln::ExprNode::BVar { idx } => {
            out.push('#');
            out.push_str(&idx.to_string());
        }
        fln::ExprNode::Sort { level } => {
            out.push_str("Sort{");
            sketch_level(level, out);
            out.push('}');
        }
        fln::ExprNode::Const { name, levels } => {
            out.push_str(&name.to_display_string());
            if !levels.is_empty() {
                out.push_str("@{");
                for (index, level) in levels.iter().enumerate() {
                    if index != 0 {
                        out.push(',');
                    }
                    sketch_level(level, out);
                }
                out.push('}');
            }
        }
        fln::ExprNode::App { f, a } => {
            out.push('(');
            sketch_expr(f, budget, out);
            out.push(' ');
            sketch_expr(a, budget, out);
            out.push(')');
        }
        fln::ExprNode::Lam {
            binder_info,
            binder_type,
            body,
            ..
        } => {
            out.push_str("(λ");
            out.push_str(style_marker(binder_info));
            out.push('#');
            sketch_expr(binder_type, budget, out);
            out.push_str(", ");
            sketch_expr(body, budget, out);
            out.push(')');
        }
        fln::ExprNode::ForallE {
            binder_info,
            binder_type,
            body,
            ..
        } => {
            out.push_str("(Π");
            out.push_str(style_marker(binder_info));
            out.push('#');
            sketch_expr(binder_type, budget, out);
            out.push_str(", ");
            sketch_expr(body, budget, out);
            out.push(')');
        }
        fln::ExprNode::LetE { body, .. } => {
            out.push_str("(let ");
            sketch_expr(body, budget, out);
            out.push(')');
        }
        fln::ExprNode::MData { expr, .. } | fln::ExprNode::Proj { expr, .. } => {
            sketch_expr(expr, budget, out)
        }
        _ => out.push('…'),
    }
}

fn render_constant_sketch(decoded: &fln::DecodedOlean) -> String {
    let mut out = String::new();
    let rendered = decoded.constants.len().min(CONSTANT_SKETCH_ROWS);
    out.push_str(&format!(
        "constant order (first {rendered} of {}):\n",
        decoded.constants.len()
    ));
    for (index, info) in decoded
        .constants
        .iter()
        .enumerate()
        .take(CONSTANT_SKETCH_ROWS)
    {
        let val = info.constant_val();
        let mut term = String::new();
        let mut budget = 64usize;
        sketch_expr(&val.type_, &mut budget, &mut term);
        let truncated = if term.len() > CONSTANT_SKETCH_TERM_CHARS {
            term.truncate(CONSTANT_SKETCH_TERM_CHARS);
            "…"
        } else {
            ""
        };

        out.push_str(&format!(
            "[{index}] {} {} levels={:?} : {term}{truncated}\n",
            constant_kind_label(info),
            val.name.to_display_string(),
            val.level_params
                .iter()
                .map(|level| level.to_display_string())
                .collect::<Vec<_>>(),
        ));
    }
    if decoded.constants.len() > CONSTANT_SKETCH_ROWS {
        out.push_str(&format!(
            "[…] {} more constants omitted\n",
            decoded.constants.len() - CONSTANT_SKETCH_ROWS
        ));
    }
    out
}

fn style_marker(info: &fln::BinderInfo) -> &'static str {
    match info {
        fln::BinderInfo::Default => "",
        fln::BinderInfo::Implicit => "i",
        fln::BinderInfo::StrictImplicit => "s",
        fln::BinderInfo::InstImplicit => "e",
    }
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

fn inspect_olean_bytes(
    bytes: &[u8],
    max_bytes: usize,
    json: bool,
    constants: bool,
) -> MultiplexerOutput {
    match fln::decode_olean_artifact(bytes, fln::OleanDecodeLimits::new(max_bytes)) {
        Ok(decoded) => MultiplexerOutput::success(if json {
            render_olean_json(bytes.len(), &decoded)
        } else {
            render_olean_human(bytes.len(), &decoded, constants)
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

fn inspect_olean(path: &Path, max_bytes: usize, json: bool, constants: bool) -> MultiplexerOutput {
    match read_bounded(path, max_bytes, ".olean artifact") {
        Ok(bytes) => inspect_olean_bytes(&bytes, max_bytes, json, constants),
        Err(error) => inspect_failure(OleanInspectFailure::Read(error), json),
    }
}

#[derive(Debug)]
enum IleanInspectFailure {
    Read(BoundedReadFailure),
    Codec {
        phase: &'static str,
        error: fln::IleanError,
    },
}

impl IleanInspectFailure {
    const fn class(&self) -> &'static str {
        match self {
            Self::Read(error) => error.class(),
            Self::Codec {
                error: fln::IleanError::Budget { .. },
                ..
            } => "resource",
            Self::Codec { .. } => "codec",
        }
    }
}

impl fmt::Display for IleanInspectFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(error) => error.fmt(formatter),
            Self::Codec { phase, error } => write!(formatter, "{phase}: {error}"),
        }
    }
}

fn ilean_inspect_failure(error: IleanInspectFailure, json: bool) -> MultiplexerOutput {
    let class = error.class();
    let detail = BoundedText::new(error.to_string());
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":false,",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(ILEAN_INSPECT_SCHEMA),
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        format!("fln ilean inspect: {class}: {}\n", detail.text())
    };
    MultiplexerOutput::failure(stderr, if class == "resource" { 3 } else { 1 })
}

fn inspect_ilean_bytes(bytes: &[u8], max_bytes: usize, json: bool) -> MultiplexerOutput {
    let budget = fln::IleanBudget {
        max_bytes,
        ..fln::IleanBudget::default()
    };
    let decoded = match fln::decode_ilean(bytes, budget) {
        Ok(decoded) => decoded,
        Err(error) => {
            return ilean_inspect_failure(
                IleanInspectFailure::Codec {
                    phase: "decode",
                    error,
                },
                json,
            );
        }
    };
    let canonical = match fln::encode_ilean(&decoded, budget) {
        Ok(canonical) => canonical,
        Err(error) => {
            return ilean_inspect_failure(
                IleanInspectFailure::Codec {
                    phase: "canonical re-encode",
                    error,
                },
                json,
            );
        }
    };
    let module = BoundedText::new(decoded.module.clone());
    let byte_identity = canonical == bytes;
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":false,",
                "\"bytes\":{},\"canonicalBytes\":{},\"byteIdentity\":{},",
                "\"version\":{},\"module\":{},\"moduleTruncated\":{},",
                "\"directImports\":{},\"references\":{},\"declarations\":{}}}\n"
            ),
            json_string(ILEAN_INSPECT_SCHEMA),
            bytes.len(),
            canonical.len(),
            byte_identity,
            decoded.version,
            json_string(module.text()),
            module.truncated(),
            decoded.direct_imports.len(),
            decoded.references.len(),
            decoded.decls.len(),
        )
    } else {
        format!(
            concat!(
                "pinned .ilean audit: complete\n",
                "authority: no\n",
                "bytes: {}\n",
                "canonical bytes: {}\n",
                "byte identity: {}\n",
                "format version: {}\n",
                "module: {}{}\n",
                "direct imports: {}\n",
                "references: {}\n",
                "declarations: {}\n"
            ),
            bytes.len(),
            canonical.len(),
            if byte_identity { "exact" } else { "different" },
            decoded.version,
            module.text(),
            if module.truncated() {
                " [truncated]"
            } else {
                ""
            },
            decoded.direct_imports.len(),
            decoded.references.len(),
            decoded.decls.len(),
        )
    };
    MultiplexerOutput::success(stdout)
}

fn inspect_ilean(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    match read_bounded(path, max_bytes, ".ilean artifact") {
        Ok(bytes) => inspect_ilean_bytes(&bytes, max_bytes, json),
        Err(error) => ilean_inspect_failure(IleanInspectFailure::Read(error), json),
    }
}

#[derive(Debug)]
enum VerifyCapsuleFailure {
    Read(BoundedReadFailure),
    Refusal(String),
    Resource(String),
    Internal(String),
    IncompleteTransport(CartridgeTransportStateV1),
    Corrupt(String),
}

impl VerifyCapsuleFailure {
    fn class(&self) -> &'static str {
        match self {
            Self::Read(err) => err.class(),
            Self::Resource(_) => "resource",
            Self::Internal(_) => "internal_fault",
            Self::Refusal(_) => "refusal",
            Self::IncompleteTransport(_) => "incomplete_transport",
            Self::Corrupt(_) => "corruption",
        }
    }
}

impl fmt::Display for VerifyCapsuleFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(err) => err.fmt(formatter),
            Self::Refusal(msg) => write!(formatter, "capsule refusal: {msg}"),
            Self::Resource(msg) => write!(formatter, "resource limit exceeded: {msg}"),
            Self::Internal(msg) => write!(formatter, "internal fault: {msg}"),
            Self::IncompleteTransport(state) => write!(
                formatter,
                "transport state {state:?} is incomplete; sealed or complete capsule required"
            ),
            Self::Corrupt(msg) => write!(formatter, "corrupt capsule: {msg}"),
        }
    }
}

fn verify_capsule_failure(error: VerifyCapsuleFailure, json: bool) -> MultiplexerOutput {
    let class = error.class();
    let detail = BoundedText::new(error.to_string());
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":false,",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(VERIFY_CAPSULE_SCHEMA),
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        format!("fln verify-capsule: {class}: {}\n", detail.text())
    };
    MultiplexerOutput::failure(stderr, if class == "resource" { 3 } else { 1 })
}

fn verify_capsule_bytes(
    path: &Path,
    bytes: &[u8],
    max_bytes: usize,
    json: bool,
) -> MultiplexerOutput {
    let max_nodes = 4 * 1024 * 1024;
    let budgets = CartridgeDecodeBudgetsV1 {
        archive: DecodeBudget::new(bytes.len() as u64, max_nodes),
        manifest: DecodeBudget::new(bytes.len() as u64, max_nodes),
    };
    let archive = match CartridgeArchiveV1::from_canonical_bytes_budgeted(bytes, budgets) {
        fln::Outcome::Complete(Ok(archive)) => archive,
        fln::Outcome::Complete(Err(refusal)) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Refusal(format!("{refusal:?}")),
                json,
            );
        }
        fln::Outcome::Inconclusive(inc) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Resource(format!("{inc:?}")),
                json,
            );
        }
        fln::Outcome::InternalFault(fault) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Internal(format!("{fault:?}")),
                json,
            );
        }
    };

    let state = archive.transport_state();
    if !matches!(
        state,
        CartridgeTransportStateV1::Complete | CartridgeTransportStateV1::Sealed { .. }
    ) {
        return verify_capsule_failure(VerifyCapsuleFailure::IncompleteTransport(state), json);
    }

    let index = match CartridgeIndexV1::from_canonical_bytes(bytes, budgets) {
        fln::Outcome::Complete(Ok(index)) => index,
        fln::Outcome::Complete(Err(refusal)) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Refusal(format!("index decode: {refusal:?}")),
                json,
            );
        }
        fln::Outcome::Inconclusive(inc) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Resource(format!("index decode: {inc:?}")),
                json,
            );
        }
        fln::Outcome::InternalFault(fault) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Internal(format!("index decode: {fault:?}")),
                json,
            );
        }
    };

    let manifest_root = match archive.manifest_root() {
        Ok(root) => root,
        Err(refusal) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Refusal(format!("manifest root: {refusal:?}")),
                json,
            );
        }
    };

    if index.manifest_root != manifest_root || index.chunks.len() != archive.frames.len() {
        return verify_capsule_failure(
            VerifyCapsuleFailure::Corrupt(
                "derived index does not match archive frames or manifest root".into(),
            ),
            json,
        );
    }

    for frame in &archive.frames {
        let indexed = match index.read_chunk(bytes, frame.id) {
            Ok(chunk) => chunk,
            Err(err) => {
                return verify_capsule_failure(
                    VerifyCapsuleFailure::Corrupt(format!("indexed chunk read: {err:?}")),
                    json,
                );
            }
        };
        if indexed != frame.bytes {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Corrupt(
                    "chunk bytes mismatch between index and frame".into(),
                ),
                json,
            );
        }
    }

    let mut certificates_decoded = 0usize;
    let mut warm_cache_decoded = false;
    let mut objects_present = 0usize;

    for object in &archive.manifest.objects {
        let assembled = match archive.assemble_object(object.id, max_bytes as u64) {
            fln::Outcome::Complete(Ok(assembled)) => assembled,
            fln::Outcome::Complete(Err(refusal)) => {
                return verify_capsule_failure(
                    VerifyCapsuleFailure::Refusal(format!(
                        "assemble object {:?}: {refusal:?}",
                        object.kind
                    )),
                    json,
                );
            }
            fln::Outcome::Inconclusive(inc) => {
                return verify_capsule_failure(
                    VerifyCapsuleFailure::Resource(format!(
                        "assemble object {:?}: {inc:?}",
                        object.kind
                    )),
                    json,
                );
            }
            fln::Outcome::InternalFault(fault) => {
                return verify_capsule_failure(
                    VerifyCapsuleFailure::Internal(format!(
                        "assemble object {:?}: {fault:?}",
                        object.kind
                    )),
                    json,
                );
            }
        };

        if let Some(object_bytes) = assembled {
            objects_present += 1;
            if object.kind == CartridgeObjectKindV1::Certificate {
                match DeclarationCertificateV1::from_canonical_bytes_budgeted(
                    &object_bytes,
                    DecodeBudget::new(object_bytes.len() as u64, max_nodes),
                ) {
                    fln::Outcome::Complete(Ok(_cert)) => {
                        certificates_decoded += 1;
                    }
                    fln::Outcome::Complete(Err(refusal)) => {
                        return verify_capsule_failure(
                            VerifyCapsuleFailure::Refusal(format!(
                                "certificate codec: {refusal:?}"
                            )),
                            json,
                        );
                    }
                    fln::Outcome::Inconclusive(inc) => {
                        return verify_capsule_failure(
                            VerifyCapsuleFailure::Resource(format!("certificate decode: {inc:?}")),
                            json,
                        );
                    }
                    fln::Outcome::InternalFault(fault) => {
                        return verify_capsule_failure(
                            VerifyCapsuleFailure::Internal(format!(
                                "certificate decode: {fault:?}"
                            )),
                            json,
                        );
                    }
                }
            } else if object.kind == CartridgeObjectKindV1::WarmDefeqCache {
                match WarmDefeqCacheV1::from_canonical_bytes_budgeted(
                    &object_bytes,
                    DecodeBudget::new(object_bytes.len() as u64, max_nodes),
                ) {
                    fln::Outcome::Complete(Ok(_cache)) => {
                        warm_cache_decoded = true;
                    }
                    fln::Outcome::Complete(Err(refusal)) => {
                        return verify_capsule_failure(
                            VerifyCapsuleFailure::Refusal(format!("warm cache codec: {refusal:?}")),
                            json,
                        );
                    }
                    fln::Outcome::Inconclusive(inc) => {
                        return verify_capsule_failure(
                            VerifyCapsuleFailure::Resource(format!("warm cache decode: {inc:?}")),
                            json,
                        );
                    }
                    fln::Outcome::InternalFault(fault) => {
                        return verify_capsule_failure(
                            VerifyCapsuleFailure::Internal(format!("warm cache decode: {fault:?}")),
                            json,
                        );
                    }
                }
            }
        } else if object.requirement == ObjectRequirementV1::Required {
            return verify_capsule_failure(VerifyCapsuleFailure::IncompleteTransport(state), json);
        }
    }

    let archive_digest = match archive.archive_digest() {
        Ok(digest) => digest,
        Err(refusal) => {
            return verify_capsule_failure(
                VerifyCapsuleFailure::Refusal(format!("archive digest: {refusal:?}")),
                json,
            );
        }
    };

    let transport_state_str = match state {
        CartridgeTransportStateV1::Complete => "complete",
        CartridgeTransportStateV1::Sealed { .. } => "sealed",
        CartridgeTransportStateV1::Partial { .. } => "partial",
        CartridgeTransportStateV1::Thin => "thin",
    };

    if json {
        let stdout = format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"path\":{},",
                "\"status\":\"integrity_verified\",\"manifest_root\":{},\"archive_digest\":{},",
                "\"transport_state\":{},\"objects_present\":{},\"objects_declared\":{},",
                "\"chunk_count\":{},\"bytes\":{},\"certificates_decoded\":{},",
                "\"certificate_replay\":\"not_implemented\",",
                "\"warm_cache_decoded\":{}}}\n"
            ),
            json_string(VERIFY_CAPSULE_SCHEMA),
            json_string(&path.display().to_string()),
            json_string(&manifest_root.to_hex()),
            json_string(&archive_digest.to_hex()),
            json_string(transport_state_str),
            objects_present,
            archive.manifest.objects.len(),
            archive.frames.len(),
            bytes.len(),
            certificates_decoded,
            warm_cache_decoded,
        );
        MultiplexerOutput::success(stdout)
    } else {
        let stdout = format!(
            concat!(
                "fln verify-capsule: integrity verified for capsule at {}\n",
                "  manifest root: {}\n",
                "  archive digest: {}\n",
                "  transport state: {}\n",
                "  objects: {} present ({} declared)\n",
                "  chunks: {}\n",
                "  bytes: {}\n",
                "  certificates decoded: {} (not replayed through a checker)\n",
                "  warm defeq cache: {}\n",
                "capsule integrity verification passed.\n"
            ),
            path.display(),
            manifest_root.to_hex(),
            archive_digest.to_hex(),
            transport_state_str,
            objects_present,
            archive.manifest.objects.len(),
            archive.frames.len(),
            bytes.len(),
            certificates_decoded,
            if warm_cache_decoded {
                "decoded"
            } else {
                "none"
            },
        );
        MultiplexerOutput::success(stdout)
    }
}

fn verify_capsule(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    match read_bounded(path, max_bytes, ".flnpack capsule") {
        Ok(bytes) => verify_capsule_bytes(path, &bytes, max_bytes, json),
        Err(error) => verify_capsule_failure(VerifyCapsuleFailure::Read(error), json),
    }
}

#[derive(Clone, Copy)]
enum OleanDiffChange {
    Added,
    Removed,
    Modified,
}

impl OleanDiffChange {
    const fn name(self) -> &'static str {
        match self {
            Self::Added => "added",
            Self::Removed => "removed",
            Self::Modified => "modified",
        }
    }
}

struct OleanDiffEntry {
    name: String,
    name_truncated: bool,
    change: OleanDiffChange,
    left_kinds: Vec<&'static str>,
    left_kinds_omitted: usize,
    right_kinds: Vec<&'static str>,
    right_kinds_omitted: usize,
}

struct OleanDiffSummary {
    byte_identity: bool,
    header_identity: bool,
    module_identity: bool,
    constant_sequence_identity: bool,
    left_bytes: usize,
    right_bytes: usize,
    left_constants: usize,
    right_constants: usize,
    added_constants: usize,
    removed_constants: usize,
    modified_names: usize,
    unchanged_constants: usize,
    changes: Vec<OleanDiffEntry>,
    omitted_changes: usize,
}

impl OleanDiffSummary {
    const fn semantic_identity(&self) -> bool {
        self.module_identity && self.constant_sequence_identity
    }
}

fn bounded_olean_name(name: &fln::Name) -> (String, bool) {
    let full = name.to_display_string();
    let mut characters = full.chars();
    let mut rendered = characters
        .by_ref()
        .take(OLEAN_MAX_RENDERED_NAME_CHARS)
        .collect::<String>();
    let truncated = characters.next().is_some();
    if truncated {
        rendered.push('…');
    }
    (rendered, truncated)
}

fn constant_order(
    constants: &[fln::ConstantInfo],
    side: &'static str,
) -> Result<Vec<usize>, OleanDiffFailure> {
    let mut order = Vec::new();
    order
        .try_reserve_exact(constants.len())
        .map_err(|_| OleanDiffFailure::Allocation {
            resource: side,
            requested: constants.len(),
        })?;
    order.extend(0..constants.len());
    order.sort_unstable_by(|left, right| {
        constants[*left]
            .name()
            .cmp(constants[*right].name())
            .then_with(|| left.cmp(right))
    });
    Ok(order)
}

fn constant_group_end(constants: &[fln::ConstantInfo], order: &[usize], start: usize) -> usize {
    let name = constants[order[start]].name();
    let mut end = start + 1;
    while end < order.len() && constants[order[end]].name() == name {
        end += 1;
    }
    end
}

fn constant_groups_equal(
    left: &[fln::ConstantInfo],
    left_order: &[usize],
    right: &[fln::ConstantInfo],
    right_order: &[usize],
) -> bool {
    left_order.len() == right_order.len()
        && left_order
            .iter()
            .zip(right_order)
            .all(|(left_index, right_index)| left[*left_index] == right[*right_index])
}

fn rendered_constant_kinds(
    constants: &[fln::ConstantInfo],
    order: &[usize],
    side: &'static str,
) -> Result<(Vec<&'static str>, usize), OleanDiffFailure> {
    let shown = order.len().min(OLEAN_DIFF_MAX_RENDERED_KINDS_PER_SIDE);
    let mut kinds = Vec::new();
    kinds
        .try_reserve_exact(shown)
        .map_err(|_| OleanDiffFailure::Allocation {
            resource: side,
            requested: shown,
        })?;
    kinds.extend(
        order
            .iter()
            .take(shown)
            .map(|index| constants[*index].kind_name()),
    );
    Ok((kinds, order.len() - shown))
}

fn record_olean_diff_entry(
    summary: &mut OleanDiffSummary,
    name: &fln::Name,
    change: OleanDiffChange,
    left: &[fln::ConstantInfo],
    left_order: &[usize],
    right: &[fln::ConstantInfo],
    right_order: &[usize],
) -> Result<(), OleanDiffFailure> {
    if summary.changes.len() >= OLEAN_DIFF_MAX_RENDERED_CHANGES {
        summary.omitted_changes = summary.omitted_changes.saturating_add(1);
        return Ok(());
    }
    let (left_kinds, left_kinds_omitted) =
        rendered_constant_kinds(left, left_order, "left diff kind list")?;
    let (right_kinds, right_kinds_omitted) =
        rendered_constant_kinds(right, right_order, "right diff kind list")?;
    let (name, name_truncated) = bounded_olean_name(name);
    summary.changes.push(OleanDiffEntry {
        name,
        name_truncated,
        change,
        left_kinds,
        left_kinds_omitted,
        right_kinds,
        right_kinds_omitted,
    });
    Ok(())
}

fn compare_decoded_oleans(
    left_bytes: &[u8],
    left: &fln::DecodedOlean,
    right_bytes: &[u8],
    right: &fln::DecodedOlean,
) -> Result<OleanDiffSummary, OleanDiffFailure> {
    let left_order = constant_order(&left.constants, "left constant order")?;
    let right_order = constant_order(&right.constants, "right constant order")?;
    let mut summary = OleanDiffSummary {
        byte_identity: left_bytes == right_bytes,
        header_identity: left.header == right.header,
        module_identity: left.module == right.module,
        constant_sequence_identity: left.constants == right.constants,
        left_bytes: left_bytes.len(),
        right_bytes: right_bytes.len(),
        left_constants: left.constants.len(),
        right_constants: right.constants.len(),
        added_constants: 0,
        removed_constants: 0,
        modified_names: 0,
        unchanged_constants: 0,
        changes: Vec::new(),
        omitted_changes: 0,
    };
    summary
        .changes
        .try_reserve_exact(
            left.constants
                .len()
                .saturating_add(right.constants.len())
                .min(OLEAN_DIFF_MAX_RENDERED_CHANGES),
        )
        .map_err(|_| OleanDiffFailure::Allocation {
            resource: ".olean diff change list",
            requested: OLEAN_DIFF_MAX_RENDERED_CHANGES,
        })?;

    let mut left_position = 0;
    let mut right_position = 0;
    while left_position < left_order.len() || right_position < right_order.len() {
        let left_name = left_order
            .get(left_position)
            .map(|index| left.constants[*index].name());
        let right_name = right_order
            .get(right_position)
            .map(|index| right.constants[*index].name());
        match (left_name, right_name) {
            (Some(left_name), Some(right_name)) if left_name < right_name => {
                let left_end = constant_group_end(&left.constants, &left_order, left_position);
                let group = &left_order[left_position..left_end];
                summary.removed_constants = summary.removed_constants.saturating_add(group.len());
                record_olean_diff_entry(
                    &mut summary,
                    left_name,
                    OleanDiffChange::Removed,
                    &left.constants,
                    group,
                    &right.constants,
                    &[],
                )?;
                left_position = left_end;
            }
            (Some(left_name), Some(right_name)) if left_name > right_name => {
                let right_end = constant_group_end(&right.constants, &right_order, right_position);
                let group = &right_order[right_position..right_end];
                summary.added_constants = summary.added_constants.saturating_add(group.len());
                record_olean_diff_entry(
                    &mut summary,
                    right_name,
                    OleanDiffChange::Added,
                    &left.constants,
                    &[],
                    &right.constants,
                    group,
                )?;
                right_position = right_end;
            }
            (Some(name), Some(_)) => {
                let left_end = constant_group_end(&left.constants, &left_order, left_position);
                let right_end = constant_group_end(&right.constants, &right_order, right_position);
                let left_group = &left_order[left_position..left_end];
                let right_group = &right_order[right_position..right_end];
                if constant_groups_equal(&left.constants, left_group, &right.constants, right_group)
                {
                    summary.unchanged_constants =
                        summary.unchanged_constants.saturating_add(left_group.len());
                } else {
                    summary.modified_names = summary.modified_names.saturating_add(1);
                    record_olean_diff_entry(
                        &mut summary,
                        name,
                        OleanDiffChange::Modified,
                        &left.constants,
                        left_group,
                        &right.constants,
                        right_group,
                    )?;
                }
                left_position = left_end;
                right_position = right_end;
            }
            (Some(name), None) => {
                let left_end = constant_group_end(&left.constants, &left_order, left_position);
                let group = &left_order[left_position..left_end];
                summary.removed_constants = summary.removed_constants.saturating_add(group.len());
                record_olean_diff_entry(
                    &mut summary,
                    name,
                    OleanDiffChange::Removed,
                    &left.constants,
                    group,
                    &right.constants,
                    &[],
                )?;
                left_position = left_end;
            }
            (None, Some(name)) => {
                let right_end = constant_group_end(&right.constants, &right_order, right_position);
                let group = &right_order[right_position..right_end];
                summary.added_constants = summary.added_constants.saturating_add(group.len());
                record_olean_diff_entry(
                    &mut summary,
                    name,
                    OleanDiffChange::Added,
                    &left.constants,
                    &[],
                    &right.constants,
                    group,
                )?;
                right_position = right_end;
            }
            (None, None) => break,
        }
    }
    Ok(summary)
}

fn render_olean_diff_kinds(kinds: &[&str]) -> String {
    format!(
        "[{}]",
        kinds
            .iter()
            .map(|kind| json_string(kind))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn render_olean_diff_success(summary: &OleanDiffSummary, json: bool) -> MultiplexerOutput {
    if json {
        let changes = summary
            .changes
            .iter()
            .map(|entry| {
                format!(
                    concat!(
                        "{{\"name\":{},\"nameTruncated\":{},\"change\":{},",
                        "\"leftKinds\":{},\"leftKindsOmitted\":{},",
                        "\"rightKinds\":{},\"rightKindsOmitted\":{}}}"
                    ),
                    json_string(&entry.name),
                    entry.name_truncated,
                    json_string(entry.change.name()),
                    render_olean_diff_kinds(&entry.left_kinds),
                    entry.left_kinds_omitted,
                    render_olean_diff_kinds(&entry.right_kinds),
                    entry.right_kinds_omitted,
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        return MultiplexerOutput::success(format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":false,",
                "\"leftBytes\":{},\"rightBytes\":{},\"byteIdentity\":{},",
                "\"semanticIdentity\":{},\"headerIdentity\":{},",
                "\"moduleIdentity\":{},\"constantSequenceIdentity\":{},",
                "\"constants\":{{\"left\":{},\"right\":{},\"added\":{},",
                "\"removed\":{},\"modifiedNames\":{},\"unchanged\":{}}},",
                "\"changes\":[{}],\"omittedChanges\":{}}}\n"
            ),
            json_string(OLEAN_DIFF_SCHEMA),
            summary.left_bytes,
            summary.right_bytes,
            summary.byte_identity,
            summary.semantic_identity(),
            summary.header_identity,
            summary.module_identity,
            summary.constant_sequence_identity,
            summary.left_constants,
            summary.right_constants,
            summary.added_constants,
            summary.removed_constants,
            summary.modified_names,
            summary.unchanged_constants,
            changes,
            summary.omitted_changes,
        ));
    }

    let mut changes = String::new();
    for entry in &summary.changes {
        let left = if entry.left_kinds.is_empty() {
            "none".to_owned()
        } else {
            entry.left_kinds.join(",")
        };
        let right = if entry.right_kinds.is_empty() {
            "none".to_owned()
        } else {
            entry.right_kinds.join(",")
        };
        changes.push_str(&format!(
            "- {} {}: {} -> {}",
            entry.change.name(),
            entry.name,
            left,
            right
        ));
        if entry.name_truncated || entry.left_kinds_omitted != 0 || entry.right_kinds_omitted != 0 {
            changes.push_str(&format!(
                " [truncated: name={}, left kinds={}, right kinds={}]",
                entry.name_truncated, entry.left_kinds_omitted, entry.right_kinds_omitted
            ));
        }
        changes.push('\n');
    }
    MultiplexerOutput::success(format!(
        concat!(
            "pinned .olean semantic diff: {}\n",
            "bytes: left {} / right {} (identical: {})\n",
            "header identical: {}\n",
            "module metadata identical: {}\n",
            "constant sequence identical: {}\n",
            "constants: left {}, right {}, added {}, removed {}, modified names {}, unchanged {}\n",
            "changes shown: {} ({} omitted)\n",
            "{}"
        ),
        if summary.semantic_identity() {
            "identical"
        } else {
            "different"
        },
        summary.left_bytes,
        summary.right_bytes,
        summary.byte_identity,
        summary.header_identity,
        summary.module_identity,
        summary.constant_sequence_identity,
        summary.left_constants,
        summary.right_constants,
        summary.added_constants,
        summary.removed_constants,
        summary.modified_names,
        summary.unchanged_constants,
        summary.changes.len(),
        summary.omitted_changes,
        changes,
    ))
}

fn olean_diff_failure(error: OleanDiffFailure, json: bool) -> MultiplexerOutput {
    let class = error.class();
    let detail = BoundedText::new(error.to_string());
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":false,",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(OLEAN_DIFF_SCHEMA),
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        format!("fln olean diff: {class}: {}\n", detail.text())
    };
    MultiplexerOutput::failure(stderr, if class == "resource" { 3 } else { 1 })
}

fn diff_olean_bytes(
    left_bytes: &[u8],
    right_bytes: &[u8],
    max_bytes: usize,
    json: bool,
) -> MultiplexerOutput {
    let observed = left_bytes.len().checked_add(right_bytes.len());
    let Some(observed) = observed else {
        return olean_diff_failure(
            OleanDiffFailure::Read(BoundedReadFailure::TooLarge {
                subject: ".olean diff inputs",
                observed: usize::MAX,
                limit: max_bytes,
            }),
            json,
        );
    };
    if observed > max_bytes {
        return olean_diff_failure(
            OleanDiffFailure::Read(BoundedReadFailure::TooLarge {
                subject: ".olean diff inputs",
                observed,
                limit: max_bytes,
            }),
            json,
        );
    }
    let left =
        match fln::decode_olean_artifact(left_bytes, fln::OleanDecodeLimits::new(left_bytes.len()))
        {
            Ok(decoded) => decoded,
            Err(error) => {
                return olean_diff_failure(
                    OleanDiffFailure::Decode {
                        side: "left",
                        error,
                    },
                    json,
                );
            }
        };
    let right = match fln::decode_olean_artifact(
        right_bytes,
        fln::OleanDecodeLimits::new(right_bytes.len()),
    ) {
        Ok(decoded) => decoded,
        Err(error) => {
            return olean_diff_failure(
                OleanDiffFailure::Decode {
                    side: "right",
                    error,
                },
                json,
            );
        }
    };
    match compare_decoded_oleans(left_bytes, &left, right_bytes, &right) {
        Ok(summary) => render_olean_diff_success(&summary, json),
        Err(error) => olean_diff_failure(error, json),
    }
}

fn diff_olean(left: &Path, right: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    let left_bytes = match read_bounded(left, max_bytes, "left .olean artifact") {
        Ok(bytes) => bytes,
        Err(error) => return olean_diff_failure(OleanDiffFailure::Read(error), json),
    };
    let remaining = max_bytes.saturating_sub(left_bytes.len());
    let right_bytes = match read_bounded(right, remaining, "right .olean artifact") {
        Ok(bytes) => bytes,
        Err(error) => return olean_diff_failure(OleanDiffFailure::Read(error), json),
    };
    diff_olean_bytes(&left_bytes, &right_bytes, max_bytes, json)
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
        | fln::OleanRebuildError::Region(
            fln::OleanRegionError::BudgetExhausted { .. }
            | fln::OleanRegionError::PayloadBudgetExhausted { .. },
        ) => ("resource", 3),
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
        | fln::OleanCheckError::MutualEnvelopeUnsupported { .. }
        | fln::OleanCheckError::InductiveEnvelopeUnsupported { .. }
        | fln::OleanCheckError::QuotientEnvelopeUnsupported { .. } => {
            ("unsupported-declaration-unit", false, 1)
        }
        fln::OleanCheckError::DuplicateDeclaration { .. }
        | fln::OleanCheckError::ConflictingModuleDeclaration { .. }
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

/// Count declarations whose logical name is rooted at Lean's `_private`
/// namespace. Module-system checking decodes these from the authoritative
/// private companion part; this is a report-only observation, not a corpus or
/// G1-completeness claim.
fn decoded_private_auxiliaries(constants: &[fln::ConstantInfo]) -> usize {
    constants
        .iter()
        .filter(|constant| constant.name().to_display_string().starts_with("_private."))
        .count()
}

/// A bounded, deterministic presentation of decoded residual names.
/// `observed` counts every matching declaration while `names` keeps the
/// lexicographically earliest names for a stable, bounded report.
struct DecodedNamedResiduals {
    observed: usize,
    names: Vec<fln::Name>,
}

impl DecodedNamedResiduals {
    fn observe_matching(
        &mut self,
        constants: &[fln::ConstantInfo],
        matches_residual: fn(&str) -> bool,
    ) {
        for constant in constants {
            let name = constant.name();
            if matches_residual(&name.to_display_string()) {
                self.observe_name(name);
            }
        }
    }

    fn observe_name(&mut self, name: &fln::Name) {
        self.observed = self.observed.saturating_add(1);
        if self.names.len() < CHECK_OLEAN_MAX_RENDERED_PRIVATE_LOOP_AUXILIARIES {
            self.names.push(name.clone());
            return;
        }
        let mut greatest = 0;
        for index in 1..self.names.len() {
            if self.names[index] > self.names[greatest] {
                greatest = index;
            }
        }
        if name < &self.names[greatest] {
            self.names[greatest] = name.clone();
        }
    }

    fn omitted(&self) -> usize {
        self.observed.saturating_sub(self.names.len())
    }

    fn sorted_names(&mut self) -> &[fln::Name] {
        self.names.sort();
        &self.names
    }
}

fn is_private_loop_auxiliary(display: &str) -> bool {
    display.starts_with("_private.") && display.split('.').any(|component| component == "loop")
}

fn is_private_companion_residual(display: &str) -> bool {
    display.starts_with("_private.")
}

fn is_private_cli_private_report_loop_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
        && display.split('.').any(|component| component == "loop")
}

fn is_private_cli_private_report_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
}

fn is_core_observables_loop_residual(display: &str) -> bool {
    CORE_OBSERVABLES_LOOP_RESIDUAL_PREFIXES
        .iter()
        .any(|prefix| display.starts_with(prefix))
}

fn is_private_eq_def_or_match_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display.split('.').any(|component| {
            component == "eq_def"
                || component.strip_prefix("match_").is_some_and(|suffix| {
                    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                })
        })
}

fn is_private_match_n_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display.split('.').any(|component| {
            component.strip_prefix("match_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_cli_private_report_match_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
        && display.split('.').any(|component| {
            component.strip_prefix("match_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_cli_private_report_equation_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
        && display.split('.').any(|component| {
            component == "eq_def"
                || component.strip_prefix("match_").is_some_and(|suffix| {
                    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                })
                || component.strip_prefix("eq_").is_some_and(|suffix| {
                    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                })
        })
}

fn is_private_eq_def_residual(display: &str) -> bool {
    display.starts_with("_private.") && display.split('.').any(|component| component == "eq_def")
}

fn is_private_eq_n_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display.split('.').any(|component| {
            component.strip_prefix("eq_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_unsafe_rec_or_sunfold_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display
            .split('.')
            .any(|component| matches!(component, "_unsafe_rec" | "_sunfold"))
}

fn is_private_sunfold_or_f_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display
            .split('.')
            .any(|component| matches!(component, "_sunfold" | "_f"))
}

fn is_private_cli_private_report_sunfold_f_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
        && display
            .split('.')
            .any(|component| matches!(component, "_sunfold" | "_f"))
}

fn is_private_cli_private_report_f_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.") && display.ends_with("._f")
}

fn is_private_cli_private_report_implementation_aux_residual(display: &str) -> bool {
    let Some(suffix) = display.strip_prefix("_private.CliPrivateReport.0.") else {
        return false;
    };

    matches!(suffix, "_f" | "_sunfold" | "_unsafe_rec")
        || suffix.strip_prefix("_proof_").is_some_and(|number| {
            !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn is_private_sunfold_residual(display: &str) -> bool {
    display.starts_with("_private.") && display.split('.').any(|component| component == "_sunfold")
}

fn is_private_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display
            .split('.')
            .any(|component| component == "_unsafe_rec")
}

fn is_private_init_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.Init.")
        && display
            .split('.')
            .any(|component| component == "_unsafe_rec")
}

fn is_private_init_data_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.")
        && display
            .split('.')
            .any(|component| component == "_unsafe_rec")
}

fn is_private_init_prelude_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Prelude.")
        && display
            .split('.')
            .any(|component| component == "_unsafe_rec")
}

fn is_private_cli_private_report_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
        && display
            .split('.')
            .any(|component| component == "_unsafe_rec")
}

fn is_private_cli_private_report_standalone_unsafe_rec_residual(display: &str) -> bool {
    display == "_private.CliPrivateReport.0._unsafe_rec"
}

fn is_private_loop_proof_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "loop"
            && components.next().is_some_and(|next| {
                next.strip_prefix("_proof_")
                    .is_some_and(|suffix| !suffix.is_empty())
            })
        {
            return true;
        }
    }
    false
}

fn is_private_standalone_proof_n_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut has_proof_n = false;
    for component in display.split('.') {
        if component == "loop" {
            return false;
        }
        has_proof_n |= component.strip_prefix("_proof_").is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        });
    }
    has_proof_n
}

fn is_private_proof_n_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display.split('.').any(|component| {
            component.strip_prefix("_proof_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_init_proof_n_residual(display: &str) -> bool {
    display.starts_with("_private.Init.")
        && display.split('.').any(|component| {
            component.strip_prefix("_proof_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_init_data_proof_n_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.")
        && display.split('.').any(|component| {
            component.strip_prefix("_proof_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_init_prelude_proof_n_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Prelude.")
        && display.split('.').any(|component| {
            component.strip_prefix("_proof_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_cli_private_report_proof_residual(display: &str) -> bool {
    display.starts_with("_private.CliPrivateReport.")
        && display.split('.').any(|component| {
            component.strip_prefix("_proof_").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_cli_private_report_standalone_proof_n_residual(display: &str) -> bool {
    is_private_cli_private_report_proof_residual(display) && !display.contains(".loop.")
}

fn is_lean_name_hash_proof_residual(display: &str) -> bool {
    display
        .strip_prefix(LEAN_NAME_HASH_PROOF_RESIDUAL_PREFIX)
        .is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn is_lean_name_beq_match_residual(display: &str) -> bool {
    display
        .strip_prefix(LEAN_NAME_BEQ_MATCH_RESIDUAL_PREFIX)
        .is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn is_private_lean_name_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Prelude.0.Lean.Name.")
}

fn is_private_init_prelude_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Prelude.")
}

fn is_private_init_residual(display: &str) -> bool {
    display.starts_with("_private.Init.")
}

fn is_list_to_array_aux_match_residual(display: &str) -> bool {
    display
        .strip_prefix(LIST_TO_ARRAY_AUX_MATCH_RESIDUAL_PREFIX)
        .is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn is_private_init_data_list_to_array_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.List.ToArrayImpl.")
        && display.contains(".List.toArrayAux.match_")
}

fn is_private_init_data_list_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.List.")
}

fn is_private_init_data_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.")
}

fn is_core_observables_syntax_match_residual(display: &str) -> bool {
    CORE_OBSERVABLES_SYNTAX_MATCH_RESIDUAL_PREFIXES
        .iter()
        .any(|prefix| {
            display.strip_prefix(prefix).is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

fn is_private_lean_syntax_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Prelude.0.Lean.Syntax.")
}

fn is_array_map_m_proof_residual(display: &str) -> bool {
    display
        .strip_prefix(ARRAY_MAP_M_PROOF_RESIDUAL_PREFIX)
        .is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn is_array_map_m_go_residual(display: &str) -> bool {
    display == ARRAY_MAP_M_GO_RESIDUAL
}

fn is_private_array_map_m_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.Array.BasicAux.0.Array.mapM'")
}

fn is_private_go_residual(display: &str) -> bool {
    display.starts_with("_private.") && display.split('.').any(|component| component == "go")
}

fn is_string_extra_unsafe_rec_residual(display: &str) -> bool {
    STRING_EXTRA_UNSAFE_REC_RESIDUALS.contains(&display)
}

fn is_merge_sort_companion_only_unsafe_rec_residual(display: &str) -> bool {
    MERGE_SORT_COMPANION_ONLY_UNSAFE_REC_RESIDUALS.contains(&display)
}

fn is_merge_sort_internal_merge_unsafe_rec_residual(display: &str) -> bool {
    is_merge_sort_companion_only_unsafe_rec_residual(display) && !display.contains(".splitRevAt.")
}

fn is_private_loop_match_one_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "loop" && components.next() == Some("match_1") {
            return true;
        }
    }
    false
}

fn is_private_loop_match_n_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "loop"
            && components.next().is_some_and(|next| {
                next.strip_prefix("match_").is_some_and(|suffix| {
                    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                })
            })
        {
            return true;
        }
    }
    false
}

fn is_private_loop_unsafe_rec_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "loop" && components.next() == Some("_unsafe_rec") {
            return true;
        }
    }
    false
}

fn is_private_loop_eq_def_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "loop" && components.next() == Some("eq_def") {
            return true;
        }
    }
    false
}

fn is_private_insert_idx_loop_unary_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "insertIdx"
            && components.next() == Some("loop")
            && components.next() == Some("_unary")
        {
            return true;
        }
    }
    false
}

fn is_private_unary_residual(display: &str) -> bool {
    display.starts_with("_private.") && display.split('.').any(|component| component == "_unary")
}

fn is_private_merge_sort_tr_unsafe_rec_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "mergeSortTR" && components.next() == Some("_unsafe_rec") {
            return true;
        }
    }
    false
}

fn is_private_run_unsafe_rec_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "run" && components.next() == Some("_unsafe_rec") {
            return true;
        }
    }
    false
}

fn is_private_go_unsafe_rec_residual(display: &str) -> bool {
    if !display.starts_with("_private.") {
        return false;
    }

    let mut components = display.split('.');
    while let Some(component) = components.next() {
        if component == "go" && components.next() == Some("_unsafe_rec") {
            return true;
        }
    }
    false
}

fn is_private_merge_tr_go_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.") && display.contains(".mergeTR.go._unsafe_rec")
}

fn is_private_split_rev_at_go_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.") && display.contains(".splitRevAt.go._unsafe_rec")
}

fn is_merge_sort_internal_split_traversal_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.Init.Data.List.Sort.Impl.")
        && display.contains(".List.MergeSort.Internal.splitRevAt.go._unsafe_rec")
}

fn is_private_find_leading_spaces_consume_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display.contains(".String.findLeadingSpacesSize.consumeSpaces._unsafe_rec")
}

fn is_private_find_leading_spaces_next_line_unsafe_rec_residual(display: &str) -> bool {
    display.starts_with("_private.")
        && display.contains(".String.findLeadingSpacesSize.findNextLine._unsafe_rec")
}

fn is_core_observables_loop_unsafe_rec_residual(display: &str) -> bool {
    CORE_OBSERVABLES_LOOP_UNSAFE_REC_RESIDUAL_PREFIXES
        .iter()
        .any(|prefix| display.starts_with(prefix))
}

fn render_named_residuals_json(residuals: &mut DecodedNamedResiduals) -> String {
    format!(
        "[{}]",
        residuals
            .sorted_names()
            .iter()
            .map(|name| {
                let (name, truncated) = bounded_olean_name(name);
                format!(
                    "{{\"name\":{},\"nameTruncated\":{truncated}}}",
                    json_string(&name),
                )
            })
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn render_named_residuals_human(residuals: &mut DecodedNamedResiduals) -> String {
    let names = residuals
        .sorted_names()
        .iter()
        .map(|name| bounded_olean_name(name).0)
        .collect::<Vec<_>>();
    if names.is_empty() {
        "none".to_owned()
    } else {
        names.join(", ")
    }
}

fn render_check_olean_success(
    bytes: usize,
    checked: &fln::CheckedOlean,
    json: bool,
) -> MultiplexerOutput {
    let constants = checked.declarations.len();
    let extensions = checked.decoded.module.extensions.len();
    let private_auxiliaries = decoded_private_auxiliaries(&checked.decoded.constants);
    let mut private_loop_auxiliaries = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_loop_auxiliaries
        .observe_matching(&checked.decoded.constants, is_private_loop_auxiliary);
    let mut private_companion_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_companion_residuals
        .observe_matching(&checked.decoded.constants, is_private_companion_residual);
    let mut private_cli_private_report_loop_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_loop_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_loop_residual,
    );
    let mut private_cli_private_report_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_residual,
    );
    let mut core_observables_loop_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    core_observables_loop_residuals.observe_matching(
        &checked.decoded.constants,
        is_core_observables_loop_residual,
    );
    let mut private_equation_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_equation_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_eq_def_or_match_residual,
    );
    let mut private_match_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_match_n_residuals
        .observe_matching(&checked.decoded.constants, is_private_match_n_residual);
    let mut private_cli_private_report_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_match_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_match_residual,
    );
    let mut private_cli_private_report_equation_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_equation_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_equation_residual,
    );
    let mut private_eq_def_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_eq_def_residuals
        .observe_matching(&checked.decoded.constants, is_private_eq_def_residual);
    let mut private_eq_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_eq_n_residuals.observe_matching(&checked.decoded.constants, is_private_eq_n_residual);
    let mut private_unsafe_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_unsafe_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_unsafe_rec_or_sunfold_residual,
    );
    let mut private_sunfold_f_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_sunfold_f_residuals
        .observe_matching(&checked.decoded.constants, is_private_sunfold_or_f_residual);
    let mut private_cli_private_report_sunfold_f_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_sunfold_f_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_sunfold_f_residual,
    );
    let mut private_cli_private_report_f_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_f_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_f_residual,
    );
    let mut private_cli_private_report_implementation_aux_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_implementation_aux_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_implementation_aux_residual,
    );
    let mut private_sunfold_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_sunfold_residuals
        .observe_matching(&checked.decoded.constants, is_private_sunfold_residual);
    let mut private_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_unsafe_rec_residuals
        .observe_matching(&checked.decoded.constants, is_private_unsafe_rec_residual);
    let mut private_init_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_unsafe_rec_residual,
    );
    let mut private_init_data_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_data_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_data_unsafe_rec_residual,
    );
    let mut private_init_prelude_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_prelude_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_prelude_unsafe_rec_residual,
    );
    let mut private_cli_private_report_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_unsafe_rec_residual,
    );
    let mut private_cli_private_report_standalone_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_standalone_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_standalone_unsafe_rec_residual,
    );
    let mut private_loop_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_loop_proof_residuals
        .observe_matching(&checked.decoded.constants, is_private_loop_proof_residual);
    let mut private_standalone_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_standalone_proof_n_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_standalone_proof_n_residual,
    );
    let mut private_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_proof_n_residuals
        .observe_matching(&checked.decoded.constants, is_private_proof_n_residual);
    let mut private_init_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_proof_n_residuals
        .observe_matching(&checked.decoded.constants, is_private_init_proof_n_residual);
    let mut private_init_data_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_data_proof_n_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_data_proof_n_residual,
    );
    let mut private_init_prelude_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_prelude_proof_n_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_prelude_proof_n_residual,
    );
    let mut private_cli_private_report_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_proof_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_proof_residual,
    );
    let mut private_cli_private_report_standalone_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_cli_private_report_standalone_proof_n_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_cli_private_report_standalone_proof_n_residual,
    );
    let mut lean_name_hash_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    lean_name_hash_proof_residuals
        .observe_matching(&checked.decoded.constants, is_lean_name_hash_proof_residual);
    let mut lean_name_beq_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    lean_name_beq_match_residuals
        .observe_matching(&checked.decoded.constants, is_lean_name_beq_match_residual);
    let mut private_lean_name_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_lean_name_residuals
        .observe_matching(&checked.decoded.constants, is_private_lean_name_residual);
    let mut private_init_prelude_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_prelude_residuals
        .observe_matching(&checked.decoded.constants, is_private_init_prelude_residual);
    let mut private_init_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_residuals.observe_matching(&checked.decoded.constants, is_private_init_residual);
    let mut list_to_array_aux_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    list_to_array_aux_match_residuals.observe_matching(
        &checked.decoded.constants,
        is_list_to_array_aux_match_residual,
    );
    let mut private_init_data_list_to_array_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_data_list_to_array_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_data_list_to_array_residual,
    );
    let mut private_init_data_list_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_data_list_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_init_data_list_residual,
    );
    let mut private_init_data_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_init_data_residuals
        .observe_matching(&checked.decoded.constants, is_private_init_data_residual);
    let mut core_observables_syntax_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    core_observables_syntax_match_residuals.observe_matching(
        &checked.decoded.constants,
        is_core_observables_syntax_match_residual,
    );
    let mut private_lean_syntax_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_lean_syntax_residuals
        .observe_matching(&checked.decoded.constants, is_private_lean_syntax_residual);
    let mut array_map_m_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    array_map_m_proof_residuals
        .observe_matching(&checked.decoded.constants, is_array_map_m_proof_residual);
    let mut array_map_m_go_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    array_map_m_go_residuals
        .observe_matching(&checked.decoded.constants, is_array_map_m_go_residual);
    let mut private_array_map_m_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_array_map_m_residuals
        .observe_matching(&checked.decoded.constants, is_private_array_map_m_residual);
    let mut private_go_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_go_residuals.observe_matching(&checked.decoded.constants, is_private_go_residual);
    let mut string_extra_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    string_extra_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_string_extra_unsafe_rec_residual,
    );
    let mut merge_sort_companion_only_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    merge_sort_companion_only_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_merge_sort_companion_only_unsafe_rec_residual,
    );
    let mut merge_sort_internal_merge_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    merge_sort_internal_merge_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_merge_sort_internal_merge_unsafe_rec_residual,
    );
    let mut private_loop_match_one_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_loop_match_one_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_loop_match_one_residual,
    );
    let mut private_loop_match_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_loop_match_n_residuals
        .observe_matching(&checked.decoded.constants, is_private_loop_match_n_residual);
    let mut private_loop_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_loop_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_loop_unsafe_rec_residual,
    );
    let mut private_loop_eq_def_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_loop_eq_def_residuals
        .observe_matching(&checked.decoded.constants, is_private_loop_eq_def_residual);
    let mut private_insert_idx_loop_unary_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_insert_idx_loop_unary_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_insert_idx_loop_unary_residual,
    );
    let mut private_unary_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_unary_residuals.observe_matching(&checked.decoded.constants, is_private_unary_residual);
    let mut private_merge_sort_tr_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_merge_sort_tr_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_merge_sort_tr_unsafe_rec_residual,
    );
    let mut private_run_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_run_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_run_unsafe_rec_residual,
    );
    let mut private_go_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_go_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_go_unsafe_rec_residual,
    );
    let mut private_merge_tr_go_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_merge_tr_go_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_merge_tr_go_unsafe_rec_residual,
    );
    let mut private_split_rev_at_go_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_split_rev_at_go_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_split_rev_at_go_unsafe_rec_residual,
    );
    let mut merge_sort_internal_split_traversal_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    merge_sort_internal_split_traversal_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_merge_sort_internal_split_traversal_unsafe_rec_residual,
    );
    let mut private_find_leading_spaces_consume_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_find_leading_spaces_consume_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_find_leading_spaces_consume_unsafe_rec_residual,
    );
    let mut private_find_leading_spaces_next_line_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    private_find_leading_spaces_next_line_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_private_find_leading_spaces_next_line_unsafe_rec_residual,
    );
    let mut core_observables_loop_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    core_observables_loop_unsafe_rec_residuals.observe_matching(
        &checked.decoded.constants,
        is_core_observables_loop_unsafe_rec_residual,
    );
    let private_loop_observed = private_loop_auxiliaries.observed;
    let private_loop_omitted = private_loop_auxiliaries.omitted();
    let private_loop_missing = private_loop_auxiliaries
        .observed
        .saturating_sub(private_loop_observed);
    let private_loop_names = if json {
        render_named_residuals_json(&mut private_loop_auxiliaries)
    } else {
        render_named_residuals_human(&mut private_loop_auxiliaries)
    };
    let private_companion_observed = private_companion_residuals.observed;
    let private_companion_omitted = private_companion_residuals.omitted();
    let private_companion_missing = private_auxiliaries.saturating_sub(private_companion_observed);
    let private_companion_names = if json {
        render_named_residuals_json(&mut private_companion_residuals)
    } else {
        render_named_residuals_human(&mut private_companion_residuals)
    };
    let private_cli_private_report_loop_observed =
        private_cli_private_report_loop_residuals.observed;
    let private_cli_private_report_loop_omitted =
        private_cli_private_report_loop_residuals.omitted();
    let private_cli_private_report_loop_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_loop_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_loop_residuals)
    };
    let private_cli_private_report_observed = private_cli_private_report_residuals.observed;
    let private_cli_private_report_omitted = private_cli_private_report_residuals.omitted();
    let private_cli_private_report_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_residuals)
    };
    let core_observables_loop_observed = core_observables_loop_residuals.observed;
    let core_observables_loop_omitted = core_observables_loop_residuals.omitted();
    let core_observables_loop_names = if json {
        render_named_residuals_json(&mut core_observables_loop_residuals)
    } else {
        render_named_residuals_human(&mut core_observables_loop_residuals)
    };
    let private_equation_observed = private_equation_residuals.observed;
    let private_equation_omitted = private_equation_residuals.omitted();
    let private_equation_names = if json {
        render_named_residuals_json(&mut private_equation_residuals)
    } else {
        render_named_residuals_human(&mut private_equation_residuals)
    };
    let private_match_n_observed = private_match_n_residuals.observed;
    let private_match_n_omitted = private_match_n_residuals.omitted();
    let private_match_n_names = if json {
        render_named_residuals_json(&mut private_match_n_residuals)
    } else {
        render_named_residuals_human(&mut private_match_n_residuals)
    };
    let private_cli_private_report_match_observed =
        private_cli_private_report_match_residuals.observed;
    let private_cli_private_report_match_omitted =
        private_cli_private_report_match_residuals.omitted();
    let private_cli_private_report_match_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_match_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_match_residuals)
    };
    let private_cli_private_report_equation_observed =
        private_cli_private_report_equation_residuals.observed;
    let private_cli_private_report_equation_omitted =
        private_cli_private_report_equation_residuals.omitted();
    let private_cli_private_report_equation_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_equation_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_equation_residuals)
    };
    let private_eq_def_observed = private_eq_def_residuals.observed;
    let private_eq_def_omitted = private_eq_def_residuals.omitted();
    let private_eq_def_names = if json {
        render_named_residuals_json(&mut private_eq_def_residuals)
    } else {
        render_named_residuals_human(&mut private_eq_def_residuals)
    };
    let private_eq_n_observed = private_eq_n_residuals.observed;
    let private_eq_n_omitted = private_eq_n_residuals.omitted();
    let private_eq_n_names = if json {
        render_named_residuals_json(&mut private_eq_n_residuals)
    } else {
        render_named_residuals_human(&mut private_eq_n_residuals)
    };
    let private_unsafe_observed = private_unsafe_residuals.observed;
    let private_unsafe_omitted = private_unsafe_residuals.omitted();
    let private_unsafe_names = if json {
        render_named_residuals_json(&mut private_unsafe_residuals)
    } else {
        render_named_residuals_human(&mut private_unsafe_residuals)
    };
    let private_sunfold_f_observed = private_sunfold_f_residuals.observed;
    let private_sunfold_f_omitted = private_sunfold_f_residuals.omitted();
    let private_sunfold_f_names = if json {
        render_named_residuals_json(&mut private_sunfold_f_residuals)
    } else {
        render_named_residuals_human(&mut private_sunfold_f_residuals)
    };
    let private_cli_private_report_sunfold_f_observed =
        private_cli_private_report_sunfold_f_residuals.observed;
    let private_cli_private_report_sunfold_f_omitted =
        private_cli_private_report_sunfold_f_residuals.omitted();
    let private_cli_private_report_sunfold_f_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_sunfold_f_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_sunfold_f_residuals)
    };
    let private_cli_private_report_f_observed = private_cli_private_report_f_residuals.observed;
    let private_cli_private_report_f_omitted = private_cli_private_report_f_residuals.omitted();
    let private_cli_private_report_f_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_f_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_f_residuals)
    };
    let private_cli_private_report_implementation_aux_observed =
        private_cli_private_report_implementation_aux_residuals.observed;
    let private_cli_private_report_implementation_aux_omitted =
        private_cli_private_report_implementation_aux_residuals.omitted();
    let private_cli_private_report_implementation_aux_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_implementation_aux_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_implementation_aux_residuals)
    };
    let private_sunfold_observed = private_sunfold_residuals.observed;
    let private_sunfold_omitted = private_sunfold_residuals.omitted();
    let private_sunfold_names = if json {
        render_named_residuals_json(&mut private_sunfold_residuals)
    } else {
        render_named_residuals_human(&mut private_sunfold_residuals)
    };
    let private_unsafe_rec_observed = private_unsafe_rec_residuals.observed;
    let private_unsafe_rec_omitted = private_unsafe_rec_residuals.omitted();
    let private_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_unsafe_rec_residuals)
    };
    let private_init_unsafe_rec_observed = private_init_unsafe_rec_residuals.observed;
    let private_init_unsafe_rec_omitted = private_init_unsafe_rec_residuals.omitted();
    let private_init_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_init_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_init_unsafe_rec_residuals)
    };
    let private_init_data_unsafe_rec_observed = private_init_data_unsafe_rec_residuals.observed;
    let private_init_data_unsafe_rec_omitted = private_init_data_unsafe_rec_residuals.omitted();
    let private_init_data_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_init_data_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_unsafe_rec_residuals)
    };
    let private_init_prelude_unsafe_rec_observed =
        private_init_prelude_unsafe_rec_residuals.observed;
    let private_init_prelude_unsafe_rec_omitted =
        private_init_prelude_unsafe_rec_residuals.omitted();
    let private_init_prelude_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_init_prelude_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_init_prelude_unsafe_rec_residuals)
    };
    let private_cli_private_report_unsafe_rec_observed =
        private_cli_private_report_unsafe_rec_residuals.observed;
    let private_cli_private_report_unsafe_rec_omitted =
        private_cli_private_report_unsafe_rec_residuals.omitted();
    let private_cli_private_report_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_unsafe_rec_residuals)
    };
    let private_cli_private_report_standalone_unsafe_rec_observed =
        private_cli_private_report_standalone_unsafe_rec_residuals.observed;
    let private_cli_private_report_standalone_unsafe_rec_omitted =
        private_cli_private_report_standalone_unsafe_rec_residuals.omitted();
    let private_cli_private_report_standalone_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_standalone_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(
            &mut private_cli_private_report_standalone_unsafe_rec_residuals,
        )
    };
    let private_loop_proof_observed = private_loop_proof_residuals.observed;
    let private_loop_proof_omitted = private_loop_proof_residuals.omitted();
    let private_loop_proof_names = if json {
        render_named_residuals_json(&mut private_loop_proof_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_proof_residuals)
    };
    let private_standalone_proof_n_observed = private_standalone_proof_n_residuals.observed;
    let private_standalone_proof_n_omitted = private_standalone_proof_n_residuals.omitted();
    let private_standalone_proof_n_names = if json {
        render_named_residuals_json(&mut private_standalone_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_standalone_proof_n_residuals)
    };
    let private_proof_n_observed = private_proof_n_residuals.observed;
    let private_proof_n_omitted = private_proof_n_residuals.omitted();
    let private_proof_n_names = if json {
        render_named_residuals_json(&mut private_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_proof_n_residuals)
    };
    let private_init_proof_n_observed = private_init_proof_n_residuals.observed;
    let private_init_proof_n_omitted = private_init_proof_n_residuals.omitted();
    let private_init_proof_n_names = if json {
        render_named_residuals_json(&mut private_init_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_init_proof_n_residuals)
    };
    let private_init_data_proof_n_observed = private_init_data_proof_n_residuals.observed;
    let private_init_data_proof_n_omitted = private_init_data_proof_n_residuals.omitted();
    let private_init_data_proof_n_names = if json {
        render_named_residuals_json(&mut private_init_data_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_proof_n_residuals)
    };
    let private_init_prelude_proof_n_observed = private_init_prelude_proof_n_residuals.observed;
    let private_init_prelude_proof_n_omitted = private_init_prelude_proof_n_residuals.omitted();
    let private_init_prelude_proof_n_names = if json {
        render_named_residuals_json(&mut private_init_prelude_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_init_prelude_proof_n_residuals)
    };
    let private_cli_private_report_proof_observed =
        private_cli_private_report_proof_residuals.observed;
    let private_cli_private_report_proof_omitted =
        private_cli_private_report_proof_residuals.omitted();
    let private_cli_private_report_proof_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_proof_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_proof_residuals)
    };
    let private_cli_private_report_standalone_proof_n_observed =
        private_cli_private_report_standalone_proof_n_residuals.observed;
    let private_cli_private_report_standalone_proof_n_omitted =
        private_cli_private_report_standalone_proof_n_residuals.omitted();
    let private_cli_private_report_standalone_proof_n_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_standalone_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_standalone_proof_n_residuals)
    };
    let lean_name_hash_proof_observed = lean_name_hash_proof_residuals.observed;
    let lean_name_hash_proof_omitted = lean_name_hash_proof_residuals.omitted();
    let lean_name_hash_proof_names = if json {
        render_named_residuals_json(&mut lean_name_hash_proof_residuals)
    } else {
        render_named_residuals_human(&mut lean_name_hash_proof_residuals)
    };
    let lean_name_beq_match_observed = lean_name_beq_match_residuals.observed;
    let lean_name_beq_match_omitted = lean_name_beq_match_residuals.omitted();
    let lean_name_beq_match_names = if json {
        render_named_residuals_json(&mut lean_name_beq_match_residuals)
    } else {
        render_named_residuals_human(&mut lean_name_beq_match_residuals)
    };
    let private_lean_name_observed = private_lean_name_residuals.observed;
    let private_lean_name_omitted = private_lean_name_residuals.omitted();
    let private_lean_name_names = if json {
        render_named_residuals_json(&mut private_lean_name_residuals)
    } else {
        render_named_residuals_human(&mut private_lean_name_residuals)
    };
    let private_init_prelude_observed = private_init_prelude_residuals.observed;
    let private_init_prelude_omitted = private_init_prelude_residuals.omitted();
    let private_init_prelude_names = if json {
        render_named_residuals_json(&mut private_init_prelude_residuals)
    } else {
        render_named_residuals_human(&mut private_init_prelude_residuals)
    };
    let private_init_observed = private_init_residuals.observed;
    let private_init_omitted = private_init_residuals.omitted();
    let private_init_names = if json {
        render_named_residuals_json(&mut private_init_residuals)
    } else {
        render_named_residuals_human(&mut private_init_residuals)
    };
    let list_to_array_aux_match_observed = list_to_array_aux_match_residuals.observed;
    let list_to_array_aux_match_omitted = list_to_array_aux_match_residuals.omitted();
    let list_to_array_aux_match_names = if json {
        render_named_residuals_json(&mut list_to_array_aux_match_residuals)
    } else {
        render_named_residuals_human(&mut list_to_array_aux_match_residuals)
    };
    let private_init_data_list_to_array_observed =
        private_init_data_list_to_array_residuals.observed;
    let private_init_data_list_to_array_omitted =
        private_init_data_list_to_array_residuals.omitted();
    let private_init_data_list_to_array_names = if json {
        render_named_residuals_json(&mut private_init_data_list_to_array_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_list_to_array_residuals)
    };
    let private_init_data_list_observed = private_init_data_list_residuals.observed;
    let private_init_data_list_omitted = private_init_data_list_residuals.omitted();
    let private_init_data_list_names = if json {
        render_named_residuals_json(&mut private_init_data_list_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_list_residuals)
    };
    let private_init_data_observed = private_init_data_residuals.observed;
    let private_init_data_omitted = private_init_data_residuals.omitted();
    let private_init_data_names = if json {
        render_named_residuals_json(&mut private_init_data_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_residuals)
    };
    let core_observables_syntax_match_observed = core_observables_syntax_match_residuals.observed;
    let core_observables_syntax_match_omitted = core_observables_syntax_match_residuals.omitted();
    let core_observables_syntax_match_names = if json {
        render_named_residuals_json(&mut core_observables_syntax_match_residuals)
    } else {
        render_named_residuals_human(&mut core_observables_syntax_match_residuals)
    };
    let private_lean_syntax_observed = private_lean_syntax_residuals.observed;
    let private_lean_syntax_omitted = private_lean_syntax_residuals.omitted();
    let private_lean_syntax_names = if json {
        render_named_residuals_json(&mut private_lean_syntax_residuals)
    } else {
        render_named_residuals_human(&mut private_lean_syntax_residuals)
    };
    let array_map_m_proof_observed = array_map_m_proof_residuals.observed;
    let array_map_m_proof_omitted = array_map_m_proof_residuals.omitted();
    let array_map_m_proof_names = if json {
        render_named_residuals_json(&mut array_map_m_proof_residuals)
    } else {
        render_named_residuals_human(&mut array_map_m_proof_residuals)
    };
    let array_map_m_go_observed = array_map_m_go_residuals.observed;
    let array_map_m_go_omitted = array_map_m_go_residuals.omitted();
    let array_map_m_go_names = if json {
        render_named_residuals_json(&mut array_map_m_go_residuals)
    } else {
        render_named_residuals_human(&mut array_map_m_go_residuals)
    };
    let private_array_map_m_observed = private_array_map_m_residuals.observed;
    let private_array_map_m_omitted = private_array_map_m_residuals.omitted();
    let private_array_map_m_names = if json {
        render_named_residuals_json(&mut private_array_map_m_residuals)
    } else {
        render_named_residuals_human(&mut private_array_map_m_residuals)
    };
    let private_go_observed = private_go_residuals.observed;
    let private_go_omitted = private_go_residuals.omitted();
    let private_go_names = if json {
        render_named_residuals_json(&mut private_go_residuals)
    } else {
        render_named_residuals_human(&mut private_go_residuals)
    };
    let string_extra_unsafe_rec_observed = string_extra_unsafe_rec_residuals.observed;
    let string_extra_unsafe_rec_omitted = string_extra_unsafe_rec_residuals.omitted();
    let string_extra_unsafe_rec_names = if json {
        render_named_residuals_json(&mut string_extra_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut string_extra_unsafe_rec_residuals)
    };
    let merge_sort_companion_only_unsafe_rec_observed =
        merge_sort_companion_only_unsafe_rec_residuals.observed;
    let merge_sort_companion_only_unsafe_rec_omitted =
        merge_sort_companion_only_unsafe_rec_residuals.omitted();
    let merge_sort_companion_only_unsafe_rec_names = if json {
        render_named_residuals_json(&mut merge_sort_companion_only_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut merge_sort_companion_only_unsafe_rec_residuals)
    };
    let merge_sort_internal_merge_unsafe_rec_observed =
        merge_sort_internal_merge_unsafe_rec_residuals.observed;
    let merge_sort_internal_merge_unsafe_rec_omitted =
        merge_sort_internal_merge_unsafe_rec_residuals.omitted();
    let merge_sort_internal_merge_unsafe_rec_names = if json {
        render_named_residuals_json(&mut merge_sort_internal_merge_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut merge_sort_internal_merge_unsafe_rec_residuals)
    };
    let private_loop_match_one_observed = private_loop_match_one_residuals.observed;
    let private_loop_match_one_omitted = private_loop_match_one_residuals.omitted();
    let private_loop_match_one_names = if json {
        render_named_residuals_json(&mut private_loop_match_one_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_match_one_residuals)
    };
    let private_loop_match_n_observed = private_loop_match_n_residuals.observed;
    let private_loop_match_n_omitted = private_loop_match_n_residuals.omitted();
    let private_loop_match_n_names = if json {
        render_named_residuals_json(&mut private_loop_match_n_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_match_n_residuals)
    };
    let private_loop_unsafe_rec_observed = private_loop_unsafe_rec_residuals.observed;
    let private_loop_unsafe_rec_omitted = private_loop_unsafe_rec_residuals.omitted();
    let private_loop_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_loop_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_unsafe_rec_residuals)
    };
    let private_loop_eq_def_observed = private_loop_eq_def_residuals.observed;
    let private_loop_eq_def_omitted = private_loop_eq_def_residuals.omitted();
    let private_loop_eq_def_names = if json {
        render_named_residuals_json(&mut private_loop_eq_def_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_eq_def_residuals)
    };
    let private_insert_idx_loop_unary_observed = private_insert_idx_loop_unary_residuals.observed;
    let private_insert_idx_loop_unary_omitted = private_insert_idx_loop_unary_residuals.omitted();
    let private_insert_idx_loop_unary_names = if json {
        render_named_residuals_json(&mut private_insert_idx_loop_unary_residuals)
    } else {
        render_named_residuals_human(&mut private_insert_idx_loop_unary_residuals)
    };
    let private_unary_observed = private_unary_residuals.observed;
    let private_unary_omitted = private_unary_residuals.omitted();
    let private_unary_names = if json {
        render_named_residuals_json(&mut private_unary_residuals)
    } else {
        render_named_residuals_human(&mut private_unary_residuals)
    };
    let private_merge_sort_tr_unsafe_rec_observed =
        private_merge_sort_tr_unsafe_rec_residuals.observed;
    let private_merge_sort_tr_unsafe_rec_omitted =
        private_merge_sort_tr_unsafe_rec_residuals.omitted();
    let private_merge_sort_tr_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_merge_sort_tr_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_merge_sort_tr_unsafe_rec_residuals)
    };
    let private_run_unsafe_rec_observed = private_run_unsafe_rec_residuals.observed;
    let private_run_unsafe_rec_omitted = private_run_unsafe_rec_residuals.omitted();
    let private_run_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_run_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_run_unsafe_rec_residuals)
    };
    let private_go_unsafe_rec_observed = private_go_unsafe_rec_residuals.observed;
    let private_go_unsafe_rec_omitted = private_go_unsafe_rec_residuals.omitted();
    let private_go_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_go_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_go_unsafe_rec_residuals)
    };
    let private_merge_tr_go_unsafe_rec_observed = private_merge_tr_go_unsafe_rec_residuals.observed;
    let private_merge_tr_go_unsafe_rec_omitted = private_merge_tr_go_unsafe_rec_residuals.omitted();
    let private_merge_tr_go_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_merge_tr_go_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_merge_tr_go_unsafe_rec_residuals)
    };
    let private_split_rev_at_go_unsafe_rec_observed =
        private_split_rev_at_go_unsafe_rec_residuals.observed;
    let private_split_rev_at_go_unsafe_rec_omitted =
        private_split_rev_at_go_unsafe_rec_residuals.omitted();
    let private_split_rev_at_go_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_split_rev_at_go_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_split_rev_at_go_unsafe_rec_residuals)
    };
    let merge_sort_internal_split_traversal_unsafe_rec_observed =
        merge_sort_internal_split_traversal_unsafe_rec_residuals.observed;
    let merge_sort_internal_split_traversal_unsafe_rec_omitted =
        merge_sort_internal_split_traversal_unsafe_rec_residuals.omitted();
    let merge_sort_internal_split_traversal_unsafe_rec_names = if json {
        render_named_residuals_json(&mut merge_sort_internal_split_traversal_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut merge_sort_internal_split_traversal_unsafe_rec_residuals)
    };
    let private_find_leading_spaces_consume_unsafe_rec_observed =
        private_find_leading_spaces_consume_unsafe_rec_residuals.observed;
    let private_find_leading_spaces_consume_unsafe_rec_omitted =
        private_find_leading_spaces_consume_unsafe_rec_residuals.omitted();
    let private_find_leading_spaces_consume_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_find_leading_spaces_consume_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_find_leading_spaces_consume_unsafe_rec_residuals)
    };
    let private_find_leading_spaces_next_line_unsafe_rec_observed =
        private_find_leading_spaces_next_line_unsafe_rec_residuals.observed;
    let private_find_leading_spaces_next_line_unsafe_rec_omitted =
        private_find_leading_spaces_next_line_unsafe_rec_residuals.omitted();
    let private_find_leading_spaces_next_line_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_find_leading_spaces_next_line_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(
            &mut private_find_leading_spaces_next_line_unsafe_rec_residuals,
        )
    };
    let core_observables_loop_unsafe_rec_observed =
        core_observables_loop_unsafe_rec_residuals.observed;
    let core_observables_loop_unsafe_rec_omitted =
        core_observables_loop_unsafe_rec_residuals.omitted();
    let core_observables_loop_unsafe_rec_names = if json {
        render_named_residuals_json(&mut core_observables_loop_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut core_observables_loop_unsafe_rec_residuals)
    };
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"scope\":\"decoded-declarations\",\"artifactBytes\":{},",
                "\"declarationsChecked\":{},\"dependencyOrderDerived\":true,",
                "\"decodedPrivateAuxiliaries\":{},",
                "\"decodedPrivateAuxiliaryNames\":{},",
                "\"decodedPrivateLoopAuxiliaries\":{{\"observed\":{},\"names\":{},\"omitted\":{},\"missing\":{}}},",
                "\"privateCompanionResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{},\"missing\":{}}},",
                "\"privateCliPrivateReportLoopResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"coreObservablesLoopResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateEqDefMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateMatchNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportEquationResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateEqDefResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateEqNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateUnsafeRecSunfoldResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateSunfoldFResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportSunfoldFResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportFResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportImplementationAuxResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateSunfoldResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitPreludeUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportStandaloneUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateStandaloneProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitPreludeProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportStandaloneProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"leanNameHashProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"leanNameBeqMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLeanNameResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitPreludeResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"listToArrayAuxMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataListToArrayResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataListResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"coreObservablesSyntaxMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLeanSyntaxResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"arrayMapMProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"arrayMapMGoResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateArrayMapMResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateGoResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"stringExtraUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"mergeSortCompanionOnlyUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"mergeSortInternalMergeUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopMatchOneResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopMatchNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopEqDefResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInsertIdxLoopUnaryResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateUnaryResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateMergeSortTRUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateRunUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateGoUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateMergeTrGoUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateSplitRevAtGoUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"mergeSortInternalSplitTraversalUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateFindLeadingSpacesConsumeUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateFindLeadingSpacesNextLineUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"coreObservablesLoopUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"module\":{{\"isModulePart\":{},\"imports\":0,",
                "\"extensionBlocksObserved\":{},\"extensionsInterpreted\":false,",
                "\"companionPartsLoaded\":{}}},",
                "\"k2Checked\":false,\"g1Satisfied\":false}}\n"
            ),
            json_string(CHECK_OLEAN_SCHEMA),
            bytes,
            constants,
            private_auxiliaries,
            private_companion_names,
            private_loop_observed,
            private_loop_names,
            private_loop_omitted,
            private_loop_missing,
            private_companion_observed,
            private_companion_names,
            private_companion_omitted,
            private_companion_missing,
            private_cli_private_report_loop_observed,
            private_cli_private_report_loop_names,
            private_cli_private_report_loop_omitted,
            private_cli_private_report_observed,
            private_cli_private_report_names,
            private_cli_private_report_omitted,
            core_observables_loop_observed,
            core_observables_loop_names,
            core_observables_loop_omitted,
            private_equation_observed,
            private_equation_names,
            private_equation_omitted,
            private_match_n_observed,
            private_match_n_names,
            private_match_n_omitted,
            private_cli_private_report_match_observed,
            private_cli_private_report_match_names,
            private_cli_private_report_match_omitted,
            private_cli_private_report_equation_observed,
            private_cli_private_report_equation_names,
            private_cli_private_report_equation_omitted,
            private_eq_def_observed,
            private_eq_def_names,
            private_eq_def_omitted,
            private_eq_n_observed,
            private_eq_n_names,
            private_eq_n_omitted,
            private_unsafe_observed,
            private_unsafe_names,
            private_unsafe_omitted,
            private_sunfold_f_observed,
            private_sunfold_f_names,
            private_sunfold_f_omitted,
            private_cli_private_report_sunfold_f_observed,
            private_cli_private_report_sunfold_f_names,
            private_cli_private_report_sunfold_f_omitted,
            private_cli_private_report_f_observed,
            private_cli_private_report_f_names,
            private_cli_private_report_f_omitted,
            private_cli_private_report_implementation_aux_observed,
            private_cli_private_report_implementation_aux_names,
            private_cli_private_report_implementation_aux_omitted,
            private_sunfold_observed,
            private_sunfold_names,
            private_sunfold_omitted,
            private_unsafe_rec_observed,
            private_unsafe_rec_names,
            private_unsafe_rec_omitted,
            private_init_unsafe_rec_observed,
            private_init_unsafe_rec_names,
            private_init_unsafe_rec_omitted,
            private_init_data_unsafe_rec_observed,
            private_init_data_unsafe_rec_names,
            private_init_data_unsafe_rec_omitted,
            private_init_prelude_unsafe_rec_observed,
            private_init_prelude_unsafe_rec_names,
            private_init_prelude_unsafe_rec_omitted,
            private_cli_private_report_unsafe_rec_observed,
            private_cli_private_report_unsafe_rec_names,
            private_cli_private_report_unsafe_rec_omitted,
            private_cli_private_report_standalone_unsafe_rec_observed,
            private_cli_private_report_standalone_unsafe_rec_names,
            private_cli_private_report_standalone_unsafe_rec_omitted,
            private_loop_proof_observed,
            private_loop_proof_names,
            private_loop_proof_omitted,
            private_standalone_proof_n_observed,
            private_standalone_proof_n_names,
            private_standalone_proof_n_omitted,
            private_proof_n_observed,
            private_proof_n_names,
            private_proof_n_omitted,
            private_init_proof_n_observed,
            private_init_proof_n_names,
            private_init_proof_n_omitted,
            private_init_data_proof_n_observed,
            private_init_data_proof_n_names,
            private_init_data_proof_n_omitted,
            private_init_prelude_proof_n_observed,
            private_init_prelude_proof_n_names,
            private_init_prelude_proof_n_omitted,
            private_cli_private_report_proof_observed,
            private_cli_private_report_proof_names,
            private_cli_private_report_proof_omitted,
            private_cli_private_report_standalone_proof_n_observed,
            private_cli_private_report_standalone_proof_n_names,
            private_cli_private_report_standalone_proof_n_omitted,
            lean_name_hash_proof_observed,
            lean_name_hash_proof_names,
            lean_name_hash_proof_omitted,
            lean_name_beq_match_observed,
            lean_name_beq_match_names,
            lean_name_beq_match_omitted,
            private_lean_name_observed,
            private_lean_name_names,
            private_lean_name_omitted,
            private_init_prelude_observed,
            private_init_prelude_names,
            private_init_prelude_omitted,
            private_init_observed,
            private_init_names,
            private_init_omitted,
            list_to_array_aux_match_observed,
            list_to_array_aux_match_names,
            list_to_array_aux_match_omitted,
            private_init_data_list_to_array_observed,
            private_init_data_list_to_array_names,
            private_init_data_list_to_array_omitted,
            private_init_data_list_observed,
            private_init_data_list_names,
            private_init_data_list_omitted,
            private_init_data_observed,
            private_init_data_names,
            private_init_data_omitted,
            core_observables_syntax_match_observed,
            core_observables_syntax_match_names,
            core_observables_syntax_match_omitted,
            private_lean_syntax_observed,
            private_lean_syntax_names,
            private_lean_syntax_omitted,
            array_map_m_proof_observed,
            array_map_m_proof_names,
            array_map_m_proof_omitted,
            array_map_m_go_observed,
            array_map_m_go_names,
            array_map_m_go_omitted,
            private_array_map_m_observed,
            private_array_map_m_names,
            private_array_map_m_omitted,
            private_go_observed,
            private_go_names,
            private_go_omitted,
            string_extra_unsafe_rec_observed,
            string_extra_unsafe_rec_names,
            string_extra_unsafe_rec_omitted,
            merge_sort_companion_only_unsafe_rec_observed,
            merge_sort_companion_only_unsafe_rec_names,
            merge_sort_companion_only_unsafe_rec_omitted,
            merge_sort_internal_merge_unsafe_rec_observed,
            merge_sort_internal_merge_unsafe_rec_names,
            merge_sort_internal_merge_unsafe_rec_omitted,
            private_loop_match_one_observed,
            private_loop_match_one_names,
            private_loop_match_one_omitted,
            private_loop_match_n_observed,
            private_loop_match_n_names,
            private_loop_match_n_omitted,
            private_loop_unsafe_rec_observed,
            private_loop_unsafe_rec_names,
            private_loop_unsafe_rec_omitted,
            private_loop_eq_def_observed,
            private_loop_eq_def_names,
            private_loop_eq_def_omitted,
            private_insert_idx_loop_unary_observed,
            private_insert_idx_loop_unary_names,
            private_insert_idx_loop_unary_omitted,
            private_unary_observed,
            private_unary_names,
            private_unary_omitted,
            private_merge_sort_tr_unsafe_rec_observed,
            private_merge_sort_tr_unsafe_rec_names,
            private_merge_sort_tr_unsafe_rec_omitted,
            private_run_unsafe_rec_observed,
            private_run_unsafe_rec_names,
            private_run_unsafe_rec_omitted,
            private_go_unsafe_rec_observed,
            private_go_unsafe_rec_names,
            private_go_unsafe_rec_omitted,
            private_merge_tr_go_unsafe_rec_observed,
            private_merge_tr_go_unsafe_rec_names,
            private_merge_tr_go_unsafe_rec_omitted,
            private_split_rev_at_go_unsafe_rec_observed,
            private_split_rev_at_go_unsafe_rec_names,
            private_split_rev_at_go_unsafe_rec_omitted,
            merge_sort_internal_split_traversal_unsafe_rec_observed,
            merge_sort_internal_split_traversal_unsafe_rec_names,
            merge_sort_internal_split_traversal_unsafe_rec_omitted,
            private_find_leading_spaces_consume_unsafe_rec_observed,
            private_find_leading_spaces_consume_unsafe_rec_names,
            private_find_leading_spaces_consume_unsafe_rec_omitted,
            private_find_leading_spaces_next_line_unsafe_rec_observed,
            private_find_leading_spaces_next_line_unsafe_rec_names,
            private_find_leading_spaces_next_line_unsafe_rec_omitted,
            core_observables_loop_unsafe_rec_observed,
            core_observables_loop_unsafe_rec_names,
            core_observables_loop_unsafe_rec_omitted,
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
                "decoded _private auxiliaries: {} (reporting only; not a G1 claim)\n",
                "decoded _private.loop auxiliaries: {} (reporting only; not a G1 claim)\n",
                "decoded _private.loop auxiliary names: {}\n",
                "decoded _private.loop auxiliary names omitted: {}\n",
                "decoded _private companion residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private companion residual names: {}\n",
                "decoded _private companion residual names omitted: {}\n",
                "decoded _private CliPrivateReport.loop residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport.loop residual names: {}\n",
                "decoded _private CliPrivateReport.loop residual names omitted: {}\n",
                "decoded _private CliPrivateReport residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport residual names: {}\n",
                "decoded _private CliPrivateReport residual names omitted: {}\n",
                "core-observables .loop residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "core-observables .loop residual names: {}\n",
                "core-observables .loop residual names omitted: {}\n",
                "decoded _private eq_def/match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private eq_def/match_N residual names: {}\n",
                "decoded _private eq_def/match_N residual names omitted: {}\n",
                "decoded _private match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private match_N residual names: {}\n",
                "decoded _private match_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport.match_N residual names: {}\n",
                "decoded _private CliPrivateReport.match_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport equation residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport equation residual names: {}\n",
                "decoded _private CliPrivateReport equation residual names omitted: {}\n",
                "decoded _private eq_def residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private eq_def residual names: {}\n",
                "decoded _private eq_def residual names omitted: {}\n",
                "decoded _private eq_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private eq_N residual names: {}\n",
                "decoded _private eq_N residual names omitted: {}\n",
                "decoded _private _unsafe_rec/_sunfold residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _unsafe_rec/_sunfold residual names: {}\n",
                "decoded _private _unsafe_rec/_sunfold residual names omitted: {}\n",
                "decoded _private _sunfold/_f residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _sunfold/_f residual names: {}\n",
                "decoded _private _sunfold/_f residual names omitted: {}\n",
                "decoded _private CliPrivateReport _sunfold/_f residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _sunfold/_f residual names: {}\n",
                "decoded _private CliPrivateReport _sunfold/_f residual names omitted: {}\n",
                "decoded _private CliPrivateReport _f residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _f residual names: {}\n",
                "decoded _private CliPrivateReport _f residual names omitted: {}\n",
                "decoded _private CliPrivateReport direct implementation auxiliary residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport direct implementation auxiliary residual names: {}\n",
                "decoded _private CliPrivateReport direct implementation auxiliary residual names omitted: {}\n",
                "decoded _private _sunfold residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _sunfold residual names: {}\n",
                "decoded _private _sunfold residual names omitted: {}\n",
                "decoded _private _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _unsafe_rec residual names: {}\n",
                "decoded _private _unsafe_rec residual names omitted: {}\n",
                "decoded _private Init _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init _unsafe_rec residual names: {}\n",
                "decoded _private Init _unsafe_rec residual names omitted: {}\n",
                "decoded _private Init.Data _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data _unsafe_rec residual names: {}\n",
                "decoded _private Init.Data _unsafe_rec residual names omitted: {}\n",
                "decoded _private Init.Prelude _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Prelude _unsafe_rec residual names: {}\n",
                "decoded _private Init.Prelude _unsafe_rec residual names omitted: {}\n",
                "decoded _private CliPrivateReport _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _unsafe_rec residual names: {}\n",
                "decoded _private CliPrivateReport _unsafe_rec residual names omitted: {}\n",
                "decoded _private CliPrivateReport standalone _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport standalone _unsafe_rec residual names: {}\n",
                "decoded _private CliPrivateReport standalone _unsafe_rec residual names omitted: {}\n",
                "decoded _private .loop._proof_* residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop._proof_* residual names: {}\n",
                "decoded _private .loop._proof_* residual names omitted: {}\n",
                "decoded standalone _private _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded standalone _private _proof_N residual names: {}\n",
                "decoded standalone _private _proof_N residual names omitted: {}\n",
                "decoded _private _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _proof_N residual names: {}\n",
                "decoded _private _proof_N residual names omitted: {}\n",
                "decoded _private Init _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init _proof_N residual names: {}\n",
                "decoded _private Init _proof_N residual names omitted: {}\n",
                "decoded _private Init.Data _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data _proof_N residual names: {}\n",
                "decoded _private Init.Data _proof_N residual names omitted: {}\n",
                "decoded _private Init.Prelude _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Prelude _proof_N residual names: {}\n",
                "decoded _private Init.Prelude _proof_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _proof_N residual names: {}\n",
                "decoded _private CliPrivateReport _proof_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport standalone _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport standalone _proof_N residual names: {}\n",
                "decoded _private CliPrivateReport standalone _proof_N residual names omitted: {}\n",
                "decoded _private Lean.Name.hash._proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Name.hash._proof_N residual names: {}\n",
                "decoded _private Lean.Name.hash._proof_N residual names omitted: {}\n",
                "decoded _private Lean.Name.beq.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Name.beq.match_N residual names: {}\n",
                "decoded _private Lean.Name.beq.match_N residual names omitted: {}\n",
                "decoded _private Lean.Name residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Name residual names: {}\n",
                "decoded _private Lean.Name residual names omitted: {}\n",
                "decoded _private Init.Prelude residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Prelude residual names: {}\n",
                "decoded _private Init.Prelude residual names omitted: {}\n",
                "decoded _private Init residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init residual names: {}\n",
                "decoded _private Init residual names omitted: {}\n",
                "decoded _private List.toArrayAux.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.toArrayAux.match_N residual names: {}\n",
                "decoded _private List.toArrayAux.match_N residual names omitted: {}\n",
                "decoded _private Init.Data.List.ToArrayImpl residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data.List.ToArrayImpl residual names: {}\n",
                "decoded _private Init.Data.List.ToArrayImpl residual names omitted: {}\n",
                "decoded _private Init.Data.List residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data.List residual names: {}\n",
                "decoded _private Init.Data.List residual names omitted: {}\n",
                "decoded _private Init.Data residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data residual names: {}\n",
                "decoded _private Init.Data residual names omitted: {}\n",
                "core-observables Lean.Syntax match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "core-observables Lean.Syntax match_N residual names: {}\n",
                "core-observables Lean.Syntax match_N residual names omitted: {}\n",
                "decoded _private Lean.Syntax residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Syntax residual names: {}\n",
                "decoded _private Lean.Syntax residual names omitted: {}\n",
                "decoded _private Array.mapM'._proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Array.mapM'._proof_N residual names: {}\n",
                "decoded _private Array.mapM'._proof_N residual names omitted: {}\n",
                "decoded _private Array.mapM'.go residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Array.mapM'.go residual names: {}\n",
                "decoded _private Array.mapM'.go residual names omitted: {}\n",
                "decoded _private Array.mapM' residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Array.mapM' residual names: {}\n",
                "decoded _private Array.mapM' residual names omitted: {}\n",
                "decoded _private .go residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .go residual names: {}\n",
                "decoded _private .go residual names omitted: {}\n",
                "decoded _private String.findLeadingSpacesSize _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private String.findLeadingSpacesSize _unsafe_rec residual names: {}\n",
                "decoded _private String.findLeadingSpacesSize _unsafe_rec residual names omitted: {}\n",
                "decoded _private List.MergeSort companion-only _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.MergeSort companion-only _unsafe_rec residual names: {}\n",
                "decoded _private List.MergeSort companion-only _unsafe_rec residual names omitted: {}\n",
                "decoded _private List.MergeSort internal merge _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.MergeSort internal merge _unsafe_rec residual names: {}\n",
                "decoded _private List.MergeSort internal merge _unsafe_rec residual names omitted: {}\n",
                "decoded _private .loop.match_1 residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop.match_1 residual names: {}\n",
                "decoded _private .loop.match_1 residual names omitted: {}\n",
                "decoded _private .loop.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop.match_N residual names: {}\n",
                "decoded _private .loop.match_N residual names omitted: {}\n",
                "decoded _private .loop._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop._unsafe_rec residual names: {}\n",
                "decoded _private .loop._unsafe_rec residual names omitted: {}\n",
                "decoded _private .loop.eq_def residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop.eq_def residual names: {}\n",
                "decoded _private .loop.eq_def residual names omitted: {}\n",
                "decoded _private insertIdx.loop._unary residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private insertIdx.loop._unary residual names: {}\n",
                "decoded _private insertIdx.loop._unary residual names omitted: {}\n",
                "decoded _private _unary residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _unary residual names: {}\n",
                "decoded _private _unary residual names omitted: {}\n",
                "decoded _private mergeSortTR._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private mergeSortTR._unsafe_rec residual names: {}\n",
                "decoded _private mergeSortTR._unsafe_rec residual names omitted: {}\n",
                "decoded _private .run._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .run._unsafe_rec residual names: {}\n",
                "decoded _private .run._unsafe_rec residual names omitted: {}\n",
                "decoded _private .go._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .go._unsafe_rec residual names: {}\n",
                "decoded _private .go._unsafe_rec residual names omitted: {}\n",
                "decoded _private mergeTR.go._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private mergeTR.go._unsafe_rec residual names: {}\n",
                "decoded _private mergeTR.go._unsafe_rec residual names omitted: {}\n",
                "decoded _private splitRevAt.go._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private splitRevAt.go._unsafe_rec residual names: {}\n",
                "decoded _private splitRevAt.go._unsafe_rec residual names omitted: {}\n",
                "decoded _private List.MergeSort internal split traversal _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.MergeSort internal split traversal _unsafe_rec residual names: {}\n",
                "decoded _private List.MergeSort internal split traversal _unsafe_rec residual names omitted: {}\n",
                "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residual names: {}\n",
                "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residual names omitted: {}\n",
                "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residual names: {}\n",
                "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residual names omitted: {}\n",
                "core-observables Lean.Syntax .loop._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "core-observables Lean.Syntax .loop._unsafe_rec residual names: {}\n",
                "core-observables Lean.Syntax .loop._unsafe_rec residual names omitted: {}\n",
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
            private_auxiliaries,
            private_loop_observed,
            private_loop_names,
            private_loop_omitted,
            private_companion_observed,
            private_companion_names,
            private_companion_omitted,
            private_cli_private_report_loop_observed,
            private_cli_private_report_loop_names,
            private_cli_private_report_loop_omitted,
            private_cli_private_report_observed,
            private_cli_private_report_names,
            private_cli_private_report_omitted,
            core_observables_loop_observed,
            core_observables_loop_names,
            core_observables_loop_omitted,
            private_equation_observed,
            private_equation_names,
            private_equation_omitted,
            private_match_n_observed,
            private_match_n_names,
            private_match_n_omitted,
            private_cli_private_report_match_observed,
            private_cli_private_report_match_names,
            private_cli_private_report_match_omitted,
            private_cli_private_report_equation_observed,
            private_cli_private_report_equation_names,
            private_cli_private_report_equation_omitted,
            private_eq_def_observed,
            private_eq_def_names,
            private_eq_def_omitted,
            private_eq_n_observed,
            private_eq_n_names,
            private_eq_n_omitted,
            private_unsafe_observed,
            private_unsafe_names,
            private_unsafe_omitted,
            private_sunfold_f_observed,
            private_sunfold_f_names,
            private_sunfold_f_omitted,
            private_cli_private_report_sunfold_f_observed,
            private_cli_private_report_sunfold_f_names,
            private_cli_private_report_sunfold_f_omitted,
            private_cli_private_report_f_observed,
            private_cli_private_report_f_names,
            private_cli_private_report_f_omitted,
            private_cli_private_report_implementation_aux_observed,
            private_cli_private_report_implementation_aux_names,
            private_cli_private_report_implementation_aux_omitted,
            private_sunfold_observed,
            private_sunfold_names,
            private_sunfold_omitted,
            private_unsafe_rec_observed,
            private_unsafe_rec_names,
            private_unsafe_rec_omitted,
            private_init_unsafe_rec_observed,
            private_init_unsafe_rec_names,
            private_init_unsafe_rec_omitted,
            private_init_data_unsafe_rec_observed,
            private_init_data_unsafe_rec_names,
            private_init_data_unsafe_rec_omitted,
            private_init_prelude_unsafe_rec_observed,
            private_init_prelude_unsafe_rec_names,
            private_init_prelude_unsafe_rec_omitted,
            private_cli_private_report_unsafe_rec_observed,
            private_cli_private_report_unsafe_rec_names,
            private_cli_private_report_unsafe_rec_omitted,
            private_cli_private_report_standalone_unsafe_rec_observed,
            private_cli_private_report_standalone_unsafe_rec_names,
            private_cli_private_report_standalone_unsafe_rec_omitted,
            private_loop_proof_observed,
            private_loop_proof_names,
            private_loop_proof_omitted,
            private_standalone_proof_n_observed,
            private_standalone_proof_n_names,
            private_standalone_proof_n_omitted,
            private_proof_n_observed,
            private_proof_n_names,
            private_proof_n_omitted,
            private_init_proof_n_observed,
            private_init_proof_n_names,
            private_init_proof_n_omitted,
            private_init_data_proof_n_observed,
            private_init_data_proof_n_names,
            private_init_data_proof_n_omitted,
            private_init_prelude_proof_n_observed,
            private_init_prelude_proof_n_names,
            private_init_prelude_proof_n_omitted,
            private_cli_private_report_proof_observed,
            private_cli_private_report_proof_names,
            private_cli_private_report_proof_omitted,
            private_cli_private_report_standalone_proof_n_observed,
            private_cli_private_report_standalone_proof_n_names,
            private_cli_private_report_standalone_proof_n_omitted,
            lean_name_hash_proof_observed,
            lean_name_hash_proof_names,
            lean_name_hash_proof_omitted,
            lean_name_beq_match_observed,
            lean_name_beq_match_names,
            lean_name_beq_match_omitted,
            private_lean_name_observed,
            private_lean_name_names,
            private_lean_name_omitted,
            private_init_prelude_observed,
            private_init_prelude_names,
            private_init_prelude_omitted,
            private_init_observed,
            private_init_names,
            private_init_omitted,
            list_to_array_aux_match_observed,
            list_to_array_aux_match_names,
            list_to_array_aux_match_omitted,
            private_init_data_list_to_array_observed,
            private_init_data_list_to_array_names,
            private_init_data_list_to_array_omitted,
            private_init_data_list_observed,
            private_init_data_list_names,
            private_init_data_list_omitted,
            private_init_data_observed,
            private_init_data_names,
            private_init_data_omitted,
            core_observables_syntax_match_observed,
            core_observables_syntax_match_names,
            core_observables_syntax_match_omitted,
            private_lean_syntax_observed,
            private_lean_syntax_names,
            private_lean_syntax_omitted,
            array_map_m_proof_observed,
            array_map_m_proof_names,
            array_map_m_proof_omitted,
            array_map_m_go_observed,
            array_map_m_go_names,
            array_map_m_go_omitted,
            private_array_map_m_observed,
            private_array_map_m_names,
            private_array_map_m_omitted,
            private_go_observed,
            private_go_names,
            private_go_omitted,
            string_extra_unsafe_rec_observed,
            string_extra_unsafe_rec_names,
            string_extra_unsafe_rec_omitted,
            merge_sort_companion_only_unsafe_rec_observed,
            merge_sort_companion_only_unsafe_rec_names,
            merge_sort_companion_only_unsafe_rec_omitted,
            merge_sort_internal_merge_unsafe_rec_observed,
            merge_sort_internal_merge_unsafe_rec_names,
            merge_sort_internal_merge_unsafe_rec_omitted,
            private_loop_match_one_observed,
            private_loop_match_one_names,
            private_loop_match_one_omitted,
            private_loop_match_n_observed,
            private_loop_match_n_names,
            private_loop_match_n_omitted,
            private_loop_unsafe_rec_observed,
            private_loop_unsafe_rec_names,
            private_loop_unsafe_rec_omitted,
            private_loop_eq_def_observed,
            private_loop_eq_def_names,
            private_loop_eq_def_omitted,
            private_insert_idx_loop_unary_observed,
            private_insert_idx_loop_unary_names,
            private_insert_idx_loop_unary_omitted,
            private_unary_observed,
            private_unary_names,
            private_unary_omitted,
            private_merge_sort_tr_unsafe_rec_observed,
            private_merge_sort_tr_unsafe_rec_names,
            private_merge_sort_tr_unsafe_rec_omitted,
            private_run_unsafe_rec_observed,
            private_run_unsafe_rec_names,
            private_run_unsafe_rec_omitted,
            private_go_unsafe_rec_observed,
            private_go_unsafe_rec_names,
            private_go_unsafe_rec_omitted,
            private_merge_tr_go_unsafe_rec_observed,
            private_merge_tr_go_unsafe_rec_names,
            private_merge_tr_go_unsafe_rec_omitted,
            private_split_rev_at_go_unsafe_rec_observed,
            private_split_rev_at_go_unsafe_rec_names,
            private_split_rev_at_go_unsafe_rec_omitted,
            merge_sort_internal_split_traversal_unsafe_rec_observed,
            merge_sort_internal_split_traversal_unsafe_rec_names,
            merge_sort_internal_split_traversal_unsafe_rec_omitted,
            private_find_leading_spaces_consume_unsafe_rec_observed,
            private_find_leading_spaces_consume_unsafe_rec_names,
            private_find_leading_spaces_consume_unsafe_rec_omitted,
            private_find_leading_spaces_next_line_unsafe_rec_observed,
            private_find_leading_spaces_next_line_unsafe_rec_names,
            private_find_leading_spaces_next_line_unsafe_rec_omitted,
            core_observables_loop_unsafe_rec_observed,
            core_observables_loop_unsafe_rec_names,
            core_observables_loop_unsafe_rec_omitted,
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
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => return Ok(None),
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
    receipts: Option<&WrittenReceiptSet>,
) -> MultiplexerOutput {
    let receipts_json_fragment = match receipts {
        Some(written) => format!(",\"receipts\":{}", written.summary_json()),
        None => String::new(),
    };
    let receipts_human_line = match receipts {
        Some(written) => written.human_line(),
        None => String::new(),
    };
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
    let private_auxiliaries: usize = checked
        .modules
        .iter()
        .map(|module| decoded_private_auxiliaries(&module.decoded.constants))
        .sum();
    let mut private_loop_auxiliaries = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_loop_auxiliaries
            .observe_matching(&module.decoded.constants, is_private_loop_auxiliary);
    }
    let mut private_companion_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_companion_residuals
            .observe_matching(&module.decoded.constants, is_private_companion_residual);
    }
    let mut private_cli_private_report_loop_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_loop_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_loop_residual,
        );
    }
    let mut private_cli_private_report_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_residual,
        );
    }
    let mut core_observables_loop_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        core_observables_loop_residuals
            .observe_matching(&module.decoded.constants, is_core_observables_loop_residual);
    }
    let mut private_equation_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_equation_residuals.observe_matching(
            &module.decoded.constants,
            is_private_eq_def_or_match_residual,
        );
    }
    let mut private_match_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_match_n_residuals
            .observe_matching(&module.decoded.constants, is_private_match_n_residual);
    }
    let mut private_cli_private_report_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_match_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_match_residual,
        );
    }
    let mut private_cli_private_report_equation_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_equation_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_equation_residual,
        );
    }
    let mut private_eq_def_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_eq_def_residuals
            .observe_matching(&module.decoded.constants, is_private_eq_def_residual);
    }
    let mut private_eq_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_eq_n_residuals
            .observe_matching(&module.decoded.constants, is_private_eq_n_residual);
    }
    let mut private_unsafe_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_unsafe_residuals.observe_matching(
            &module.decoded.constants,
            is_private_unsafe_rec_or_sunfold_residual,
        );
    }
    let mut private_sunfold_f_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_sunfold_f_residuals
            .observe_matching(&module.decoded.constants, is_private_sunfold_or_f_residual);
    }
    let mut private_cli_private_report_sunfold_f_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_sunfold_f_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_sunfold_f_residual,
        );
    }
    let mut private_cli_private_report_f_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_f_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_f_residual,
        );
    }
    let mut private_cli_private_report_implementation_aux_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_implementation_aux_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_implementation_aux_residual,
        );
    }
    let mut private_sunfold_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_sunfold_residuals
            .observe_matching(&module.decoded.constants, is_private_sunfold_residual);
    }
    let mut private_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_unsafe_rec_residuals
            .observe_matching(&module.decoded.constants, is_private_unsafe_rec_residual);
    }
    let mut private_init_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_unsafe_rec_residual,
        );
    }
    let mut private_init_data_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_data_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_data_unsafe_rec_residual,
        );
    }
    let mut private_init_prelude_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_prelude_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_prelude_unsafe_rec_residual,
        );
    }
    let mut private_cli_private_report_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_unsafe_rec_residual,
        );
    }
    let mut private_cli_private_report_standalone_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_standalone_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_standalone_unsafe_rec_residual,
        );
    }
    let mut private_loop_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_loop_proof_residuals
            .observe_matching(&module.decoded.constants, is_private_loop_proof_residual);
    }
    let mut private_standalone_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_standalone_proof_n_residuals.observe_matching(
            &module.decoded.constants,
            is_private_standalone_proof_n_residual,
        );
    }
    let mut private_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_proof_n_residuals
            .observe_matching(&module.decoded.constants, is_private_proof_n_residual);
    }
    let mut private_init_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_proof_n_residuals
            .observe_matching(&module.decoded.constants, is_private_init_proof_n_residual);
    }
    let mut private_init_data_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_data_proof_n_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_data_proof_n_residual,
        );
    }
    let mut private_init_prelude_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_prelude_proof_n_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_prelude_proof_n_residual,
        );
    }
    let mut private_cli_private_report_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_proof_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_proof_residual,
        );
    }
    let mut private_cli_private_report_standalone_proof_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_cli_private_report_standalone_proof_n_residuals.observe_matching(
            &module.decoded.constants,
            is_private_cli_private_report_standalone_proof_n_residual,
        );
    }
    let mut lean_name_hash_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        lean_name_hash_proof_residuals
            .observe_matching(&module.decoded.constants, is_lean_name_hash_proof_residual);
    }
    let mut lean_name_beq_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        lean_name_beq_match_residuals
            .observe_matching(&module.decoded.constants, is_lean_name_beq_match_residual);
    }
    let mut private_lean_name_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_lean_name_residuals
            .observe_matching(&module.decoded.constants, is_private_lean_name_residual);
    }
    let mut private_init_prelude_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_prelude_residuals
            .observe_matching(&module.decoded.constants, is_private_init_prelude_residual);
    }
    let mut private_init_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_residuals
            .observe_matching(&module.decoded.constants, is_private_init_residual);
    }
    let mut list_to_array_aux_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        list_to_array_aux_match_residuals.observe_matching(
            &module.decoded.constants,
            is_list_to_array_aux_match_residual,
        );
    }
    let mut private_init_data_list_to_array_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_data_list_to_array_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_data_list_to_array_residual,
        );
    }
    let mut private_init_data_list_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_data_list_residuals.observe_matching(
            &module.decoded.constants,
            is_private_init_data_list_residual,
        );
    }
    let mut private_init_data_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_init_data_residuals
            .observe_matching(&module.decoded.constants, is_private_init_data_residual);
    }
    let mut core_observables_syntax_match_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        core_observables_syntax_match_residuals.observe_matching(
            &module.decoded.constants,
            is_core_observables_syntax_match_residual,
        );
    }
    let mut private_lean_syntax_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_lean_syntax_residuals
            .observe_matching(&module.decoded.constants, is_private_lean_syntax_residual);
    }
    let mut array_map_m_proof_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        array_map_m_proof_residuals
            .observe_matching(&module.decoded.constants, is_array_map_m_proof_residual);
    }
    let mut array_map_m_go_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        array_map_m_go_residuals
            .observe_matching(&module.decoded.constants, is_array_map_m_go_residual);
    }
    let mut private_array_map_m_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_array_map_m_residuals
            .observe_matching(&module.decoded.constants, is_private_array_map_m_residual);
    }
    let mut private_go_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_go_residuals.observe_matching(&module.decoded.constants, is_private_go_residual);
    }
    let mut string_extra_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        string_extra_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_string_extra_unsafe_rec_residual,
        );
    }
    let mut merge_sort_companion_only_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        merge_sort_companion_only_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_merge_sort_companion_only_unsafe_rec_residual,
        );
    }
    let mut merge_sort_internal_merge_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        merge_sort_internal_merge_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_merge_sort_internal_merge_unsafe_rec_residual,
        );
    }
    let mut private_loop_match_one_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_loop_match_one_residuals.observe_matching(
            &module.decoded.constants,
            is_private_loop_match_one_residual,
        );
    }
    let mut private_loop_match_n_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_loop_match_n_residuals
            .observe_matching(&module.decoded.constants, is_private_loop_match_n_residual);
    }
    let mut private_loop_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_loop_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_loop_unsafe_rec_residual,
        );
    }
    let mut private_loop_eq_def_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_loop_eq_def_residuals
            .observe_matching(&module.decoded.constants, is_private_loop_eq_def_residual);
    }
    let mut private_insert_idx_loop_unary_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_insert_idx_loop_unary_residuals.observe_matching(
            &module.decoded.constants,
            is_private_insert_idx_loop_unary_residual,
        );
    }
    let mut private_unary_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_unary_residuals
            .observe_matching(&module.decoded.constants, is_private_unary_residual);
    }
    let mut private_merge_sort_tr_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_merge_sort_tr_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_merge_sort_tr_unsafe_rec_residual,
        );
    }
    let mut private_run_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_run_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_run_unsafe_rec_residual,
        );
    }
    let mut private_go_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_go_unsafe_rec_residuals
            .observe_matching(&module.decoded.constants, is_private_go_unsafe_rec_residual);
    }
    let mut private_merge_tr_go_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_merge_tr_go_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_merge_tr_go_unsafe_rec_residual,
        );
    }
    let mut private_split_rev_at_go_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_split_rev_at_go_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_split_rev_at_go_unsafe_rec_residual,
        );
    }
    let mut merge_sort_internal_split_traversal_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        merge_sort_internal_split_traversal_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_merge_sort_internal_split_traversal_unsafe_rec_residual,
        );
    }
    let mut private_find_leading_spaces_consume_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_find_leading_spaces_consume_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_find_leading_spaces_consume_unsafe_rec_residual,
        );
    }
    let mut private_find_leading_spaces_next_line_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        private_find_leading_spaces_next_line_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_private_find_leading_spaces_next_line_unsafe_rec_residual,
        );
    }
    let mut core_observables_loop_unsafe_rec_residuals = DecodedNamedResiduals {
        observed: 0,
        names: Vec::new(),
    };
    for module in &checked.modules {
        core_observables_loop_unsafe_rec_residuals.observe_matching(
            &module.decoded.constants,
            is_core_observables_loop_unsafe_rec_residual,
        );
    }
    let private_loop_observed = private_loop_auxiliaries.observed;
    let private_loop_omitted = private_loop_auxiliaries.omitted();
    let private_loop_missing = private_loop_auxiliaries
        .observed
        .saturating_sub(private_loop_observed);
    let private_loop_names = if json {
        render_named_residuals_json(&mut private_loop_auxiliaries)
    } else {
        render_named_residuals_human(&mut private_loop_auxiliaries)
    };
    let private_companion_observed = private_companion_residuals.observed;
    let private_companion_omitted = private_companion_residuals.omitted();
    let private_companion_missing = private_auxiliaries.saturating_sub(private_companion_observed);
    let private_companion_names = if json {
        render_named_residuals_json(&mut private_companion_residuals)
    } else {
        render_named_residuals_human(&mut private_companion_residuals)
    };
    let private_cli_private_report_loop_observed =
        private_cli_private_report_loop_residuals.observed;
    let private_cli_private_report_loop_omitted =
        private_cli_private_report_loop_residuals.omitted();
    let private_cli_private_report_loop_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_loop_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_loop_residuals)
    };
    let private_cli_private_report_observed = private_cli_private_report_residuals.observed;
    let private_cli_private_report_omitted = private_cli_private_report_residuals.omitted();
    let private_cli_private_report_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_residuals)
    };
    let core_observables_loop_observed = core_observables_loop_residuals.observed;
    let core_observables_loop_omitted = core_observables_loop_residuals.omitted();
    let core_observables_loop_names = if json {
        render_named_residuals_json(&mut core_observables_loop_residuals)
    } else {
        render_named_residuals_human(&mut core_observables_loop_residuals)
    };
    let private_equation_observed = private_equation_residuals.observed;
    let private_equation_omitted = private_equation_residuals.omitted();
    let private_equation_names = if json {
        render_named_residuals_json(&mut private_equation_residuals)
    } else {
        render_named_residuals_human(&mut private_equation_residuals)
    };
    let private_match_n_observed = private_match_n_residuals.observed;
    let private_match_n_omitted = private_match_n_residuals.omitted();
    let private_match_n_names = if json {
        render_named_residuals_json(&mut private_match_n_residuals)
    } else {
        render_named_residuals_human(&mut private_match_n_residuals)
    };
    let private_cli_private_report_match_observed =
        private_cli_private_report_match_residuals.observed;
    let private_cli_private_report_match_omitted =
        private_cli_private_report_match_residuals.omitted();
    let private_cli_private_report_match_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_match_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_match_residuals)
    };
    let private_cli_private_report_equation_observed =
        private_cli_private_report_equation_residuals.observed;
    let private_cli_private_report_equation_omitted =
        private_cli_private_report_equation_residuals.omitted();
    let private_cli_private_report_equation_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_equation_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_equation_residuals)
    };
    let private_eq_def_observed = private_eq_def_residuals.observed;
    let private_eq_def_omitted = private_eq_def_residuals.omitted();
    let private_eq_def_names = if json {
        render_named_residuals_json(&mut private_eq_def_residuals)
    } else {
        render_named_residuals_human(&mut private_eq_def_residuals)
    };
    let private_eq_n_observed = private_eq_n_residuals.observed;
    let private_eq_n_omitted = private_eq_n_residuals.omitted();
    let private_eq_n_names = if json {
        render_named_residuals_json(&mut private_eq_n_residuals)
    } else {
        render_named_residuals_human(&mut private_eq_n_residuals)
    };
    let private_unsafe_observed = private_unsafe_residuals.observed;
    let private_unsafe_omitted = private_unsafe_residuals.omitted();
    let private_unsafe_names = if json {
        render_named_residuals_json(&mut private_unsafe_residuals)
    } else {
        render_named_residuals_human(&mut private_unsafe_residuals)
    };
    let private_sunfold_f_observed = private_sunfold_f_residuals.observed;
    let private_sunfold_f_omitted = private_sunfold_f_residuals.omitted();
    let private_sunfold_f_names = if json {
        render_named_residuals_json(&mut private_sunfold_f_residuals)
    } else {
        render_named_residuals_human(&mut private_sunfold_f_residuals)
    };
    let private_cli_private_report_sunfold_f_observed =
        private_cli_private_report_sunfold_f_residuals.observed;
    let private_cli_private_report_sunfold_f_omitted =
        private_cli_private_report_sunfold_f_residuals.omitted();
    let private_cli_private_report_sunfold_f_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_sunfold_f_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_sunfold_f_residuals)
    };
    let private_cli_private_report_f_observed = private_cli_private_report_f_residuals.observed;
    let private_cli_private_report_f_omitted = private_cli_private_report_f_residuals.omitted();
    let private_cli_private_report_f_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_f_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_f_residuals)
    };
    let private_cli_private_report_implementation_aux_observed =
        private_cli_private_report_implementation_aux_residuals.observed;
    let private_cli_private_report_implementation_aux_omitted =
        private_cli_private_report_implementation_aux_residuals.omitted();
    let private_cli_private_report_implementation_aux_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_implementation_aux_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_implementation_aux_residuals)
    };
    let private_sunfold_observed = private_sunfold_residuals.observed;
    let private_sunfold_omitted = private_sunfold_residuals.omitted();
    let private_sunfold_names = if json {
        render_named_residuals_json(&mut private_sunfold_residuals)
    } else {
        render_named_residuals_human(&mut private_sunfold_residuals)
    };
    let private_unsafe_rec_observed = private_unsafe_rec_residuals.observed;
    let private_unsafe_rec_omitted = private_unsafe_rec_residuals.omitted();
    let private_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_unsafe_rec_residuals)
    };
    let private_init_unsafe_rec_observed = private_init_unsafe_rec_residuals.observed;
    let private_init_unsafe_rec_omitted = private_init_unsafe_rec_residuals.omitted();
    let private_init_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_init_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_init_unsafe_rec_residuals)
    };
    let private_init_data_unsafe_rec_observed = private_init_data_unsafe_rec_residuals.observed;
    let private_init_data_unsafe_rec_omitted = private_init_data_unsafe_rec_residuals.omitted();
    let private_init_data_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_init_data_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_unsafe_rec_residuals)
    };
    let private_init_prelude_unsafe_rec_observed =
        private_init_prelude_unsafe_rec_residuals.observed;
    let private_init_prelude_unsafe_rec_omitted =
        private_init_prelude_unsafe_rec_residuals.omitted();
    let private_init_prelude_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_init_prelude_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_init_prelude_unsafe_rec_residuals)
    };
    let private_cli_private_report_unsafe_rec_observed =
        private_cli_private_report_unsafe_rec_residuals.observed;
    let private_cli_private_report_unsafe_rec_omitted =
        private_cli_private_report_unsafe_rec_residuals.omitted();
    let private_cli_private_report_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_unsafe_rec_residuals)
    };
    let private_cli_private_report_standalone_unsafe_rec_observed =
        private_cli_private_report_standalone_unsafe_rec_residuals.observed;
    let private_cli_private_report_standalone_unsafe_rec_omitted =
        private_cli_private_report_standalone_unsafe_rec_residuals.omitted();
    let private_cli_private_report_standalone_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_standalone_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(
            &mut private_cli_private_report_standalone_unsafe_rec_residuals,
        )
    };
    let private_loop_proof_observed = private_loop_proof_residuals.observed;
    let private_loop_proof_omitted = private_loop_proof_residuals.omitted();
    let private_loop_proof_names = if json {
        render_named_residuals_json(&mut private_loop_proof_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_proof_residuals)
    };
    let private_standalone_proof_n_observed = private_standalone_proof_n_residuals.observed;
    let private_standalone_proof_n_omitted = private_standalone_proof_n_residuals.omitted();
    let private_standalone_proof_n_names = if json {
        render_named_residuals_json(&mut private_standalone_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_standalone_proof_n_residuals)
    };
    let private_proof_n_observed = private_proof_n_residuals.observed;
    let private_proof_n_omitted = private_proof_n_residuals.omitted();
    let private_proof_n_names = if json {
        render_named_residuals_json(&mut private_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_proof_n_residuals)
    };
    let private_init_proof_n_observed = private_init_proof_n_residuals.observed;
    let private_init_proof_n_omitted = private_init_proof_n_residuals.omitted();
    let private_init_proof_n_names = if json {
        render_named_residuals_json(&mut private_init_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_init_proof_n_residuals)
    };
    let private_init_data_proof_n_observed = private_init_data_proof_n_residuals.observed;
    let private_init_data_proof_n_omitted = private_init_data_proof_n_residuals.omitted();
    let private_init_data_proof_n_names = if json {
        render_named_residuals_json(&mut private_init_data_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_proof_n_residuals)
    };
    let private_init_prelude_proof_n_observed = private_init_prelude_proof_n_residuals.observed;
    let private_init_prelude_proof_n_omitted = private_init_prelude_proof_n_residuals.omitted();
    let private_init_prelude_proof_n_names = if json {
        render_named_residuals_json(&mut private_init_prelude_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_init_prelude_proof_n_residuals)
    };
    let private_cli_private_report_proof_observed =
        private_cli_private_report_proof_residuals.observed;
    let private_cli_private_report_proof_omitted =
        private_cli_private_report_proof_residuals.omitted();
    let private_cli_private_report_proof_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_proof_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_proof_residuals)
    };
    let private_cli_private_report_standalone_proof_n_observed =
        private_cli_private_report_standalone_proof_n_residuals.observed;
    let private_cli_private_report_standalone_proof_n_omitted =
        private_cli_private_report_standalone_proof_n_residuals.omitted();
    let private_cli_private_report_standalone_proof_n_names = if json {
        render_named_residuals_json(&mut private_cli_private_report_standalone_proof_n_residuals)
    } else {
        render_named_residuals_human(&mut private_cli_private_report_standalone_proof_n_residuals)
    };
    let lean_name_hash_proof_observed = lean_name_hash_proof_residuals.observed;
    let lean_name_hash_proof_omitted = lean_name_hash_proof_residuals.omitted();
    let lean_name_hash_proof_names = if json {
        render_named_residuals_json(&mut lean_name_hash_proof_residuals)
    } else {
        render_named_residuals_human(&mut lean_name_hash_proof_residuals)
    };
    let lean_name_beq_match_observed = lean_name_beq_match_residuals.observed;
    let lean_name_beq_match_omitted = lean_name_beq_match_residuals.omitted();
    let lean_name_beq_match_names = if json {
        render_named_residuals_json(&mut lean_name_beq_match_residuals)
    } else {
        render_named_residuals_human(&mut lean_name_beq_match_residuals)
    };
    let private_lean_name_observed = private_lean_name_residuals.observed;
    let private_lean_name_omitted = private_lean_name_residuals.omitted();
    let private_lean_name_names = if json {
        render_named_residuals_json(&mut private_lean_name_residuals)
    } else {
        render_named_residuals_human(&mut private_lean_name_residuals)
    };
    let private_init_prelude_observed = private_init_prelude_residuals.observed;
    let private_init_prelude_omitted = private_init_prelude_residuals.omitted();
    let private_init_prelude_names = if json {
        render_named_residuals_json(&mut private_init_prelude_residuals)
    } else {
        render_named_residuals_human(&mut private_init_prelude_residuals)
    };
    let private_init_observed = private_init_residuals.observed;
    let private_init_omitted = private_init_residuals.omitted();
    let private_init_names = if json {
        render_named_residuals_json(&mut private_init_residuals)
    } else {
        render_named_residuals_human(&mut private_init_residuals)
    };
    let list_to_array_aux_match_observed = list_to_array_aux_match_residuals.observed;
    let list_to_array_aux_match_omitted = list_to_array_aux_match_residuals.omitted();
    let list_to_array_aux_match_names = if json {
        render_named_residuals_json(&mut list_to_array_aux_match_residuals)
    } else {
        render_named_residuals_human(&mut list_to_array_aux_match_residuals)
    };
    let private_init_data_list_to_array_observed =
        private_init_data_list_to_array_residuals.observed;
    let private_init_data_list_to_array_omitted =
        private_init_data_list_to_array_residuals.omitted();
    let private_init_data_list_to_array_names = if json {
        render_named_residuals_json(&mut private_init_data_list_to_array_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_list_to_array_residuals)
    };
    let private_init_data_list_observed = private_init_data_list_residuals.observed;
    let private_init_data_list_omitted = private_init_data_list_residuals.omitted();
    let private_init_data_list_names = if json {
        render_named_residuals_json(&mut private_init_data_list_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_list_residuals)
    };
    let private_init_data_observed = private_init_data_residuals.observed;
    let private_init_data_omitted = private_init_data_residuals.omitted();
    let private_init_data_names = if json {
        render_named_residuals_json(&mut private_init_data_residuals)
    } else {
        render_named_residuals_human(&mut private_init_data_residuals)
    };
    let core_observables_syntax_match_observed = core_observables_syntax_match_residuals.observed;
    let core_observables_syntax_match_omitted = core_observables_syntax_match_residuals.omitted();
    let core_observables_syntax_match_names = if json {
        render_named_residuals_json(&mut core_observables_syntax_match_residuals)
    } else {
        render_named_residuals_human(&mut core_observables_syntax_match_residuals)
    };
    let private_lean_syntax_observed = private_lean_syntax_residuals.observed;
    let private_lean_syntax_omitted = private_lean_syntax_residuals.omitted();
    let private_lean_syntax_names = if json {
        render_named_residuals_json(&mut private_lean_syntax_residuals)
    } else {
        render_named_residuals_human(&mut private_lean_syntax_residuals)
    };
    let array_map_m_proof_observed = array_map_m_proof_residuals.observed;
    let array_map_m_proof_omitted = array_map_m_proof_residuals.omitted();
    let array_map_m_proof_names = if json {
        render_named_residuals_json(&mut array_map_m_proof_residuals)
    } else {
        render_named_residuals_human(&mut array_map_m_proof_residuals)
    };
    let array_map_m_go_observed = array_map_m_go_residuals.observed;
    let array_map_m_go_omitted = array_map_m_go_residuals.omitted();
    let array_map_m_go_names = if json {
        render_named_residuals_json(&mut array_map_m_go_residuals)
    } else {
        render_named_residuals_human(&mut array_map_m_go_residuals)
    };
    let private_array_map_m_observed = private_array_map_m_residuals.observed;
    let private_array_map_m_omitted = private_array_map_m_residuals.omitted();
    let private_array_map_m_names = if json {
        render_named_residuals_json(&mut private_array_map_m_residuals)
    } else {
        render_named_residuals_human(&mut private_array_map_m_residuals)
    };
    let private_go_observed = private_go_residuals.observed;
    let private_go_omitted = private_go_residuals.omitted();
    let private_go_names = if json {
        render_named_residuals_json(&mut private_go_residuals)
    } else {
        render_named_residuals_human(&mut private_go_residuals)
    };
    let string_extra_unsafe_rec_observed = string_extra_unsafe_rec_residuals.observed;
    let string_extra_unsafe_rec_omitted = string_extra_unsafe_rec_residuals.omitted();
    let string_extra_unsafe_rec_names = if json {
        render_named_residuals_json(&mut string_extra_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut string_extra_unsafe_rec_residuals)
    };
    let merge_sort_companion_only_unsafe_rec_observed =
        merge_sort_companion_only_unsafe_rec_residuals.observed;
    let merge_sort_companion_only_unsafe_rec_omitted =
        merge_sort_companion_only_unsafe_rec_residuals.omitted();
    let merge_sort_companion_only_unsafe_rec_names = if json {
        render_named_residuals_json(&mut merge_sort_companion_only_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut merge_sort_companion_only_unsafe_rec_residuals)
    };
    let merge_sort_internal_merge_unsafe_rec_observed =
        merge_sort_internal_merge_unsafe_rec_residuals.observed;
    let merge_sort_internal_merge_unsafe_rec_omitted =
        merge_sort_internal_merge_unsafe_rec_residuals.omitted();
    let merge_sort_internal_merge_unsafe_rec_names = if json {
        render_named_residuals_json(&mut merge_sort_internal_merge_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut merge_sort_internal_merge_unsafe_rec_residuals)
    };
    let private_loop_match_one_observed = private_loop_match_one_residuals.observed;
    let private_loop_match_one_omitted = private_loop_match_one_residuals.omitted();
    let private_loop_match_one_names = if json {
        render_named_residuals_json(&mut private_loop_match_one_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_match_one_residuals)
    };
    let private_loop_match_n_observed = private_loop_match_n_residuals.observed;
    let private_loop_match_n_omitted = private_loop_match_n_residuals.omitted();
    let private_loop_match_n_names = if json {
        render_named_residuals_json(&mut private_loop_match_n_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_match_n_residuals)
    };
    let private_loop_unsafe_rec_observed = private_loop_unsafe_rec_residuals.observed;
    let private_loop_unsafe_rec_omitted = private_loop_unsafe_rec_residuals.omitted();
    let private_loop_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_loop_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_unsafe_rec_residuals)
    };
    let private_loop_eq_def_observed = private_loop_eq_def_residuals.observed;
    let private_loop_eq_def_omitted = private_loop_eq_def_residuals.omitted();
    let private_loop_eq_def_names = if json {
        render_named_residuals_json(&mut private_loop_eq_def_residuals)
    } else {
        render_named_residuals_human(&mut private_loop_eq_def_residuals)
    };
    let private_insert_idx_loop_unary_observed = private_insert_idx_loop_unary_residuals.observed;
    let private_insert_idx_loop_unary_omitted = private_insert_idx_loop_unary_residuals.omitted();
    let private_insert_idx_loop_unary_names = if json {
        render_named_residuals_json(&mut private_insert_idx_loop_unary_residuals)
    } else {
        render_named_residuals_human(&mut private_insert_idx_loop_unary_residuals)
    };
    let private_unary_observed = private_unary_residuals.observed;
    let private_unary_omitted = private_unary_residuals.omitted();
    let private_unary_names = if json {
        render_named_residuals_json(&mut private_unary_residuals)
    } else {
        render_named_residuals_human(&mut private_unary_residuals)
    };
    let private_merge_sort_tr_unsafe_rec_observed =
        private_merge_sort_tr_unsafe_rec_residuals.observed;
    let private_merge_sort_tr_unsafe_rec_omitted =
        private_merge_sort_tr_unsafe_rec_residuals.omitted();
    let private_merge_sort_tr_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_merge_sort_tr_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_merge_sort_tr_unsafe_rec_residuals)
    };
    let private_run_unsafe_rec_observed = private_run_unsafe_rec_residuals.observed;
    let private_run_unsafe_rec_omitted = private_run_unsafe_rec_residuals.omitted();
    let private_run_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_run_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_run_unsafe_rec_residuals)
    };
    let private_go_unsafe_rec_observed = private_go_unsafe_rec_residuals.observed;
    let private_go_unsafe_rec_omitted = private_go_unsafe_rec_residuals.omitted();
    let private_go_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_go_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_go_unsafe_rec_residuals)
    };
    let private_merge_tr_go_unsafe_rec_observed = private_merge_tr_go_unsafe_rec_residuals.observed;
    let private_merge_tr_go_unsafe_rec_omitted = private_merge_tr_go_unsafe_rec_residuals.omitted();
    let private_merge_tr_go_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_merge_tr_go_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_merge_tr_go_unsafe_rec_residuals)
    };
    let private_split_rev_at_go_unsafe_rec_observed =
        private_split_rev_at_go_unsafe_rec_residuals.observed;
    let private_split_rev_at_go_unsafe_rec_omitted =
        private_split_rev_at_go_unsafe_rec_residuals.omitted();
    let private_split_rev_at_go_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_split_rev_at_go_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_split_rev_at_go_unsafe_rec_residuals)
    };
    let merge_sort_internal_split_traversal_unsafe_rec_observed =
        merge_sort_internal_split_traversal_unsafe_rec_residuals.observed;
    let merge_sort_internal_split_traversal_unsafe_rec_omitted =
        merge_sort_internal_split_traversal_unsafe_rec_residuals.omitted();
    let merge_sort_internal_split_traversal_unsafe_rec_names = if json {
        render_named_residuals_json(&mut merge_sort_internal_split_traversal_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut merge_sort_internal_split_traversal_unsafe_rec_residuals)
    };
    let private_find_leading_spaces_consume_unsafe_rec_observed =
        private_find_leading_spaces_consume_unsafe_rec_residuals.observed;
    let private_find_leading_spaces_consume_unsafe_rec_omitted =
        private_find_leading_spaces_consume_unsafe_rec_residuals.omitted();
    let private_find_leading_spaces_consume_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_find_leading_spaces_consume_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut private_find_leading_spaces_consume_unsafe_rec_residuals)
    };
    let private_find_leading_spaces_next_line_unsafe_rec_observed =
        private_find_leading_spaces_next_line_unsafe_rec_residuals.observed;
    let private_find_leading_spaces_next_line_unsafe_rec_omitted =
        private_find_leading_spaces_next_line_unsafe_rec_residuals.omitted();
    let private_find_leading_spaces_next_line_unsafe_rec_names = if json {
        render_named_residuals_json(&mut private_find_leading_spaces_next_line_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(
            &mut private_find_leading_spaces_next_line_unsafe_rec_residuals,
        )
    };
    let core_observables_loop_unsafe_rec_observed =
        core_observables_loop_unsafe_rec_residuals.observed;
    let core_observables_loop_unsafe_rec_omitted =
        core_observables_loop_unsafe_rec_residuals.omitted();
    let core_observables_loop_unsafe_rec_names = if json {
        render_named_residuals_json(&mut core_observables_loop_unsafe_rec_residuals)
    } else {
        render_named_residuals_human(&mut core_observables_loop_unsafe_rec_residuals)
    };
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
                "\"decodedPrivateAuxiliaries\":{},",
                "\"decodedPrivateAuxiliaryNames\":{},",
                "\"decodedPrivateLoopAuxiliaries\":{{\"observed\":{},\"names\":{},\"omitted\":{},\"missing\":{}}},",
                "\"privateCompanionResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{},\"missing\":{}}},",
                "\"privateCliPrivateReportLoopResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"coreObservablesLoopResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateEqDefMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateMatchNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportEquationResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateEqDefResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateEqNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateUnsafeRecSunfoldResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateSunfoldFResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportSunfoldFResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportFResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportImplementationAuxResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateSunfoldResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitPreludeUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportStandaloneUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateStandaloneProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitPreludeProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateCliPrivateReportStandaloneProofNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"leanNameHashProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"leanNameBeqMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLeanNameResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitPreludeResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"listToArrayAuxMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataListToArrayResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataListResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInitDataResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"coreObservablesSyntaxMatchResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLeanSyntaxResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"arrayMapMProofResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"arrayMapMGoResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateArrayMapMResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateGoResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"stringExtraUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"mergeSortCompanionOnlyUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"mergeSortInternalMergeUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopMatchOneResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopMatchNResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateLoopEqDefResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateInsertIdxLoopUnaryResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateUnaryResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateMergeSortTRUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateRunUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateGoUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateMergeTrGoUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateSplitRevAtGoUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"mergeSortInternalSplitTraversalUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateFindLeadingSpacesConsumeUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"privateFindLeadingSpacesNextLineUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"coreObservablesLoopUnsafeRecResiduals\":{{\"observed\":{},\"names\":{},\"omitted\":{}}},",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"extensionBlocksObserved\":{},\"extensionsInterpreted\":false,",
                "\"companionPartsLoaded\":{},\"companionModulesLoaded\":{},",
                "\"k2Checked\":false,\"g1Satisfied\":false{}}}\n"
            ),
            json_string(CHECK_OLEAN_SCHEMA),
            bytes,
            checked.modules.len(),
            imports,
            declarations,
            private_auxiliaries,
            private_companion_names,
            private_loop_observed,
            private_loop_names,
            private_loop_omitted,
            private_loop_missing,
            private_companion_observed,
            private_companion_names,
            private_companion_omitted,
            private_companion_missing,
            private_cli_private_report_loop_observed,
            private_cli_private_report_loop_names,
            private_cli_private_report_loop_omitted,
            private_cli_private_report_observed,
            private_cli_private_report_names,
            private_cli_private_report_omitted,
            core_observables_loop_observed,
            core_observables_loop_names,
            core_observables_loop_omitted,
            private_equation_observed,
            private_equation_names,
            private_equation_omitted,
            private_match_n_observed,
            private_match_n_names,
            private_match_n_omitted,
            private_cli_private_report_match_observed,
            private_cli_private_report_match_names,
            private_cli_private_report_match_omitted,
            private_cli_private_report_equation_observed,
            private_cli_private_report_equation_names,
            private_cli_private_report_equation_omitted,
            private_eq_def_observed,
            private_eq_def_names,
            private_eq_def_omitted,
            private_eq_n_observed,
            private_eq_n_names,
            private_eq_n_omitted,
            private_unsafe_observed,
            private_unsafe_names,
            private_unsafe_omitted,
            private_sunfold_f_observed,
            private_sunfold_f_names,
            private_sunfold_f_omitted,
            private_cli_private_report_sunfold_f_observed,
            private_cli_private_report_sunfold_f_names,
            private_cli_private_report_sunfold_f_omitted,
            private_cli_private_report_f_observed,
            private_cli_private_report_f_names,
            private_cli_private_report_f_omitted,
            private_cli_private_report_implementation_aux_observed,
            private_cli_private_report_implementation_aux_names,
            private_cli_private_report_implementation_aux_omitted,
            private_sunfold_observed,
            private_sunfold_names,
            private_sunfold_omitted,
            private_unsafe_rec_observed,
            private_unsafe_rec_names,
            private_unsafe_rec_omitted,
            private_init_unsafe_rec_observed,
            private_init_unsafe_rec_names,
            private_init_unsafe_rec_omitted,
            private_init_data_unsafe_rec_observed,
            private_init_data_unsafe_rec_names,
            private_init_data_unsafe_rec_omitted,
            private_init_prelude_unsafe_rec_observed,
            private_init_prelude_unsafe_rec_names,
            private_init_prelude_unsafe_rec_omitted,
            private_cli_private_report_unsafe_rec_observed,
            private_cli_private_report_unsafe_rec_names,
            private_cli_private_report_unsafe_rec_omitted,
            private_cli_private_report_standalone_unsafe_rec_observed,
            private_cli_private_report_standalone_unsafe_rec_names,
            private_cli_private_report_standalone_unsafe_rec_omitted,
            private_loop_proof_observed,
            private_loop_proof_names,
            private_loop_proof_omitted,
            private_standalone_proof_n_observed,
            private_standalone_proof_n_names,
            private_standalone_proof_n_omitted,
            private_proof_n_observed,
            private_proof_n_names,
            private_proof_n_omitted,
            private_init_proof_n_observed,
            private_init_proof_n_names,
            private_init_proof_n_omitted,
            private_init_data_proof_n_observed,
            private_init_data_proof_n_names,
            private_init_data_proof_n_omitted,
            private_init_prelude_proof_n_observed,
            private_init_prelude_proof_n_names,
            private_init_prelude_proof_n_omitted,
            private_cli_private_report_proof_observed,
            private_cli_private_report_proof_names,
            private_cli_private_report_proof_omitted,
            private_cli_private_report_standalone_proof_n_observed,
            private_cli_private_report_standalone_proof_n_names,
            private_cli_private_report_standalone_proof_n_omitted,
            lean_name_hash_proof_observed,
            lean_name_hash_proof_names,
            lean_name_hash_proof_omitted,
            lean_name_beq_match_observed,
            lean_name_beq_match_names,
            lean_name_beq_match_omitted,
            private_lean_name_observed,
            private_lean_name_names,
            private_lean_name_omitted,
            private_init_prelude_observed,
            private_init_prelude_names,
            private_init_prelude_omitted,
            private_init_observed,
            private_init_names,
            private_init_omitted,
            list_to_array_aux_match_observed,
            list_to_array_aux_match_names,
            list_to_array_aux_match_omitted,
            private_init_data_list_to_array_observed,
            private_init_data_list_to_array_names,
            private_init_data_list_to_array_omitted,
            private_init_data_list_observed,
            private_init_data_list_names,
            private_init_data_list_omitted,
            private_init_data_observed,
            private_init_data_names,
            private_init_data_omitted,
            core_observables_syntax_match_observed,
            core_observables_syntax_match_names,
            core_observables_syntax_match_omitted,
            private_lean_syntax_observed,
            private_lean_syntax_names,
            private_lean_syntax_omitted,
            array_map_m_proof_observed,
            array_map_m_proof_names,
            array_map_m_proof_omitted,
            array_map_m_go_observed,
            array_map_m_go_names,
            array_map_m_go_omitted,
            private_array_map_m_observed,
            private_array_map_m_names,
            private_array_map_m_omitted,
            private_go_observed,
            private_go_names,
            private_go_omitted,
            string_extra_unsafe_rec_observed,
            string_extra_unsafe_rec_names,
            string_extra_unsafe_rec_omitted,
            merge_sort_companion_only_unsafe_rec_observed,
            merge_sort_companion_only_unsafe_rec_names,
            merge_sort_companion_only_unsafe_rec_omitted,
            merge_sort_internal_merge_unsafe_rec_observed,
            merge_sort_internal_merge_unsafe_rec_names,
            merge_sort_internal_merge_unsafe_rec_omitted,
            private_loop_match_one_observed,
            private_loop_match_one_names,
            private_loop_match_one_omitted,
            private_loop_match_n_observed,
            private_loop_match_n_names,
            private_loop_match_n_omitted,
            private_loop_unsafe_rec_observed,
            private_loop_unsafe_rec_names,
            private_loop_unsafe_rec_omitted,
            private_loop_eq_def_observed,
            private_loop_eq_def_names,
            private_loop_eq_def_omitted,
            private_insert_idx_loop_unary_observed,
            private_insert_idx_loop_unary_names,
            private_insert_idx_loop_unary_omitted,
            private_unary_observed,
            private_unary_names,
            private_unary_omitted,
            private_merge_sort_tr_unsafe_rec_observed,
            private_merge_sort_tr_unsafe_rec_names,
            private_merge_sort_tr_unsafe_rec_omitted,
            private_run_unsafe_rec_observed,
            private_run_unsafe_rec_names,
            private_run_unsafe_rec_omitted,
            private_go_unsafe_rec_observed,
            private_go_unsafe_rec_names,
            private_go_unsafe_rec_omitted,
            private_merge_tr_go_unsafe_rec_observed,
            private_merge_tr_go_unsafe_rec_names,
            private_merge_tr_go_unsafe_rec_omitted,
            private_split_rev_at_go_unsafe_rec_observed,
            private_split_rev_at_go_unsafe_rec_names,
            private_split_rev_at_go_unsafe_rec_omitted,
            merge_sort_internal_split_traversal_unsafe_rec_observed,
            merge_sort_internal_split_traversal_unsafe_rec_names,
            merge_sort_internal_split_traversal_unsafe_rec_omitted,
            private_find_leading_spaces_consume_unsafe_rec_observed,
            private_find_leading_spaces_consume_unsafe_rec_names,
            private_find_leading_spaces_consume_unsafe_rec_omitted,
            private_find_leading_spaces_next_line_unsafe_rec_observed,
            private_find_leading_spaces_next_line_unsafe_rec_names,
            private_find_leading_spaces_next_line_unsafe_rec_omitted,
            core_observables_loop_unsafe_rec_observed,
            core_observables_loop_unsafe_rec_names,
            core_observables_loop_unsafe_rec_omitted,
            json_string(&checked.base_logical_root.to_string()),
            json_string(&checked.result_logical_root.to_string()),
            extensions,
            companion_modules > 0,
            companion_modules,
            receipts_json_fragment,
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
                "decoded _private auxiliaries: {} (reporting only; not a G1 claim)\n",
                "decoded _private.loop auxiliaries: {} (reporting only; not a G1 claim)\n",
                "decoded _private.loop auxiliary names: {}\n",
                "decoded _private.loop auxiliary names omitted: {}\n",
                "decoded _private companion residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private companion residual names: {}\n",
                "decoded _private companion residual names omitted: {}\n",
                "decoded _private CliPrivateReport.loop residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport.loop residual names: {}\n",
                "decoded _private CliPrivateReport.loop residual names omitted: {}\n",
                "decoded _private CliPrivateReport residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport residual names: {}\n",
                "decoded _private CliPrivateReport residual names omitted: {}\n",
                "core-observables .loop residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "core-observables .loop residual names: {}\n",
                "core-observables .loop residual names omitted: {}\n",
                "decoded _private eq_def/match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private eq_def/match_N residual names: {}\n",
                "decoded _private eq_def/match_N residual names omitted: {}\n",
                "decoded _private match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private match_N residual names: {}\n",
                "decoded _private match_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport.match_N residual names: {}\n",
                "decoded _private CliPrivateReport.match_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport equation residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport equation residual names: {}\n",
                "decoded _private CliPrivateReport equation residual names omitted: {}\n",
                "decoded _private eq_def residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private eq_def residual names: {}\n",
                "decoded _private eq_def residual names omitted: {}\n",
                "decoded _private eq_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private eq_N residual names: {}\n",
                "decoded _private eq_N residual names omitted: {}\n",
                "decoded _private _unsafe_rec/_sunfold residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _unsafe_rec/_sunfold residual names: {}\n",
                "decoded _private _unsafe_rec/_sunfold residual names omitted: {}\n",
                "decoded _private _sunfold/_f residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _sunfold/_f residual names: {}\n",
                "decoded _private _sunfold/_f residual names omitted: {}\n",
                "decoded _private CliPrivateReport _sunfold/_f residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _sunfold/_f residual names: {}\n",
                "decoded _private CliPrivateReport _sunfold/_f residual names omitted: {}\n",
                "decoded _private CliPrivateReport _f residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _f residual names: {}\n",
                "decoded _private CliPrivateReport _f residual names omitted: {}\n",
                "decoded _private CliPrivateReport direct implementation auxiliary residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport direct implementation auxiliary residual names: {}\n",
                "decoded _private CliPrivateReport direct implementation auxiliary residual names omitted: {}\n",
                "decoded _private _sunfold residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _sunfold residual names: {}\n",
                "decoded _private _sunfold residual names omitted: {}\n",
                "decoded _private _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _unsafe_rec residual names: {}\n",
                "decoded _private _unsafe_rec residual names omitted: {}\n",
                "decoded _private Init _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init _unsafe_rec residual names: {}\n",
                "decoded _private Init _unsafe_rec residual names omitted: {}\n",
                "decoded _private Init.Data _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data _unsafe_rec residual names: {}\n",
                "decoded _private Init.Data _unsafe_rec residual names omitted: {}\n",
                "decoded _private Init.Prelude _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Prelude _unsafe_rec residual names: {}\n",
                "decoded _private Init.Prelude _unsafe_rec residual names omitted: {}\n",
                "decoded _private CliPrivateReport _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _unsafe_rec residual names: {}\n",
                "decoded _private CliPrivateReport _unsafe_rec residual names omitted: {}\n",
                "decoded _private CliPrivateReport standalone _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport standalone _unsafe_rec residual names: {}\n",
                "decoded _private CliPrivateReport standalone _unsafe_rec residual names omitted: {}\n",
                "decoded _private .loop._proof_* residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop._proof_* residual names: {}\n",
                "decoded _private .loop._proof_* residual names omitted: {}\n",
                "decoded standalone _private _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded standalone _private _proof_N residual names: {}\n",
                "decoded standalone _private _proof_N residual names omitted: {}\n",
                "decoded _private _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _proof_N residual names: {}\n",
                "decoded _private _proof_N residual names omitted: {}\n",
                "decoded _private Init _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init _proof_N residual names: {}\n",
                "decoded _private Init _proof_N residual names omitted: {}\n",
                "decoded _private Init.Data _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data _proof_N residual names: {}\n",
                "decoded _private Init.Data _proof_N residual names omitted: {}\n",
                "decoded _private Init.Prelude _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Prelude _proof_N residual names: {}\n",
                "decoded _private Init.Prelude _proof_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport _proof_N residual names: {}\n",
                "decoded _private CliPrivateReport _proof_N residual names omitted: {}\n",
                "decoded _private CliPrivateReport standalone _proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private CliPrivateReport standalone _proof_N residual names: {}\n",
                "decoded _private CliPrivateReport standalone _proof_N residual names omitted: {}\n",
                "decoded _private Lean.Name.hash._proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Name.hash._proof_N residual names: {}\n",
                "decoded _private Lean.Name.hash._proof_N residual names omitted: {}\n",
                "decoded _private Lean.Name.beq.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Name.beq.match_N residual names: {}\n",
                "decoded _private Lean.Name.beq.match_N residual names omitted: {}\n",
                "decoded _private Lean.Name residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Name residual names: {}\n",
                "decoded _private Lean.Name residual names omitted: {}\n",
                "decoded _private Init.Prelude residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Prelude residual names: {}\n",
                "decoded _private Init.Prelude residual names omitted: {}\n",
                "decoded _private Init residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init residual names: {}\n",
                "decoded _private Init residual names omitted: {}\n",
                "decoded _private List.toArrayAux.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.toArrayAux.match_N residual names: {}\n",
                "decoded _private List.toArrayAux.match_N residual names omitted: {}\n",
                "decoded _private Init.Data.List.ToArrayImpl residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data.List.ToArrayImpl residual names: {}\n",
                "decoded _private Init.Data.List.ToArrayImpl residual names omitted: {}\n",
                "decoded _private Init.Data.List residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data.List residual names: {}\n",
                "decoded _private Init.Data.List residual names omitted: {}\n",
                "decoded _private Init.Data residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Init.Data residual names: {}\n",
                "decoded _private Init.Data residual names omitted: {}\n",
                "core-observables Lean.Syntax match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "core-observables Lean.Syntax match_N residual names: {}\n",
                "core-observables Lean.Syntax match_N residual names omitted: {}\n",
                "decoded _private Lean.Syntax residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Lean.Syntax residual names: {}\n",
                "decoded _private Lean.Syntax residual names omitted: {}\n",
                "decoded _private Array.mapM'._proof_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Array.mapM'._proof_N residual names: {}\n",
                "decoded _private Array.mapM'._proof_N residual names omitted: {}\n",
                "decoded _private Array.mapM'.go residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Array.mapM'.go residual names: {}\n",
                "decoded _private Array.mapM'.go residual names omitted: {}\n",
                "decoded _private Array.mapM' residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private Array.mapM' residual names: {}\n",
                "decoded _private Array.mapM' residual names omitted: {}\n",
                "decoded _private .go residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .go residual names: {}\n",
                "decoded _private .go residual names omitted: {}\n",
                "decoded _private String.findLeadingSpacesSize _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private String.findLeadingSpacesSize _unsafe_rec residual names: {}\n",
                "decoded _private String.findLeadingSpacesSize _unsafe_rec residual names omitted: {}\n",
                "decoded _private List.MergeSort companion-only _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.MergeSort companion-only _unsafe_rec residual names: {}\n",
                "decoded _private List.MergeSort companion-only _unsafe_rec residual names omitted: {}\n",
                "decoded _private List.MergeSort internal merge _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.MergeSort internal merge _unsafe_rec residual names: {}\n",
                "decoded _private List.MergeSort internal merge _unsafe_rec residual names omitted: {}\n",
                "decoded _private .loop.match_1 residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop.match_1 residual names: {}\n",
                "decoded _private .loop.match_1 residual names omitted: {}\n",
                "decoded _private .loop.match_N residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop.match_N residual names: {}\n",
                "decoded _private .loop.match_N residual names omitted: {}\n",
                "decoded _private .loop._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop._unsafe_rec residual names: {}\n",
                "decoded _private .loop._unsafe_rec residual names omitted: {}\n",
                "decoded _private .loop.eq_def residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .loop.eq_def residual names: {}\n",
                "decoded _private .loop.eq_def residual names omitted: {}\n",
                "decoded _private insertIdx.loop._unary residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private insertIdx.loop._unary residual names: {}\n",
                "decoded _private insertIdx.loop._unary residual names omitted: {}\n",
                "decoded _private _unary residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private _unary residual names: {}\n",
                "decoded _private _unary residual names omitted: {}\n",
                "decoded _private mergeSortTR._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private mergeSortTR._unsafe_rec residual names: {}\n",
                "decoded _private mergeSortTR._unsafe_rec residual names omitted: {}\n",
                "decoded _private .run._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .run._unsafe_rec residual names: {}\n",
                "decoded _private .run._unsafe_rec residual names omitted: {}\n",
                "decoded _private .go._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private .go._unsafe_rec residual names: {}\n",
                "decoded _private .go._unsafe_rec residual names omitted: {}\n",
                "decoded _private mergeTR.go._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private mergeTR.go._unsafe_rec residual names: {}\n",
                "decoded _private mergeTR.go._unsafe_rec residual names omitted: {}\n",
                "decoded _private splitRevAt.go._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private splitRevAt.go._unsafe_rec residual names: {}\n",
                "decoded _private splitRevAt.go._unsafe_rec residual names omitted: {}\n",
                "decoded _private List.MergeSort internal split traversal _unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private List.MergeSort internal split traversal _unsafe_rec residual names: {}\n",
                "decoded _private List.MergeSort internal split traversal _unsafe_rec residual names omitted: {}\n",
                "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residual names: {}\n",
                "decoded _private String.findLeadingSpacesSize.consumeSpaces._unsafe_rec residual names omitted: {}\n",
                "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residual names: {}\n",
                "decoded _private String.findLeadingSpacesSize.findNextLine._unsafe_rec residual names omitted: {}\n",
                "core-observables Lean.Syntax .loop._unsafe_rec residuals: {} (decoded companion names; reporting only; not a G1 claim)\n",
                "core-observables Lean.Syntax .loop._unsafe_rec residual names: {}\n",
                "core-observables Lean.Syntax .loop._unsafe_rec residual names omitted: {}\n",
                "module and declaration dependency order: derived\n",
                "base logical root: {}\n",
                "result logical root: {}\n",
                "extension blocks observed: {} (not interpreted)\n",
                "complete module companion chains loaded: {}\n",
                "K2 checked: no\n",
                "G1 satisfied: no\n{}"
            ),
            bytes,
            checked.modules.len(),
            imports,
            declarations,
            private_auxiliaries,
            private_loop_observed,
            private_loop_names,
            private_loop_omitted,
            private_companion_observed,
            private_companion_names,
            private_companion_omitted,
            private_cli_private_report_loop_observed,
            private_cli_private_report_loop_names,
            private_cli_private_report_loop_omitted,
            private_cli_private_report_observed,
            private_cli_private_report_names,
            private_cli_private_report_omitted,
            core_observables_loop_observed,
            core_observables_loop_names,
            core_observables_loop_omitted,
            private_equation_observed,
            private_equation_names,
            private_equation_omitted,
            private_match_n_observed,
            private_match_n_names,
            private_match_n_omitted,
            private_cli_private_report_match_observed,
            private_cli_private_report_match_names,
            private_cli_private_report_match_omitted,
            private_cli_private_report_equation_observed,
            private_cli_private_report_equation_names,
            private_cli_private_report_equation_omitted,
            private_eq_def_observed,
            private_eq_def_names,
            private_eq_def_omitted,
            private_eq_n_observed,
            private_eq_n_names,
            private_eq_n_omitted,
            private_unsafe_observed,
            private_unsafe_names,
            private_unsafe_omitted,
            private_sunfold_f_observed,
            private_sunfold_f_names,
            private_sunfold_f_omitted,
            private_cli_private_report_sunfold_f_observed,
            private_cli_private_report_sunfold_f_names,
            private_cli_private_report_sunfold_f_omitted,
            private_cli_private_report_f_observed,
            private_cli_private_report_f_names,
            private_cli_private_report_f_omitted,
            private_cli_private_report_implementation_aux_observed,
            private_cli_private_report_implementation_aux_names,
            private_cli_private_report_implementation_aux_omitted,
            private_sunfold_observed,
            private_sunfold_names,
            private_sunfold_omitted,
            private_unsafe_rec_observed,
            private_unsafe_rec_names,
            private_unsafe_rec_omitted,
            private_init_unsafe_rec_observed,
            private_init_unsafe_rec_names,
            private_init_unsafe_rec_omitted,
            private_init_data_unsafe_rec_observed,
            private_init_data_unsafe_rec_names,
            private_init_data_unsafe_rec_omitted,
            private_init_prelude_unsafe_rec_observed,
            private_init_prelude_unsafe_rec_names,
            private_init_prelude_unsafe_rec_omitted,
            private_cli_private_report_unsafe_rec_observed,
            private_cli_private_report_unsafe_rec_names,
            private_cli_private_report_unsafe_rec_omitted,
            private_cli_private_report_standalone_unsafe_rec_observed,
            private_cli_private_report_standalone_unsafe_rec_names,
            private_cli_private_report_standalone_unsafe_rec_omitted,
            private_loop_proof_observed,
            private_loop_proof_names,
            private_loop_proof_omitted,
            private_standalone_proof_n_observed,
            private_standalone_proof_n_names,
            private_standalone_proof_n_omitted,
            private_proof_n_observed,
            private_proof_n_names,
            private_proof_n_omitted,
            private_init_proof_n_observed,
            private_init_proof_n_names,
            private_init_proof_n_omitted,
            private_init_data_proof_n_observed,
            private_init_data_proof_n_names,
            private_init_data_proof_n_omitted,
            private_init_prelude_proof_n_observed,
            private_init_prelude_proof_n_names,
            private_init_prelude_proof_n_omitted,
            private_cli_private_report_proof_observed,
            private_cli_private_report_proof_names,
            private_cli_private_report_proof_omitted,
            private_cli_private_report_standalone_proof_n_observed,
            private_cli_private_report_standalone_proof_n_names,
            private_cli_private_report_standalone_proof_n_omitted,
            lean_name_hash_proof_observed,
            lean_name_hash_proof_names,
            lean_name_hash_proof_omitted,
            lean_name_beq_match_observed,
            lean_name_beq_match_names,
            lean_name_beq_match_omitted,
            private_lean_name_observed,
            private_lean_name_names,
            private_lean_name_omitted,
            private_init_prelude_observed,
            private_init_prelude_names,
            private_init_prelude_omitted,
            private_init_observed,
            private_init_names,
            private_init_omitted,
            list_to_array_aux_match_observed,
            list_to_array_aux_match_names,
            list_to_array_aux_match_omitted,
            private_init_data_list_to_array_observed,
            private_init_data_list_to_array_names,
            private_init_data_list_to_array_omitted,
            private_init_data_list_observed,
            private_init_data_list_names,
            private_init_data_list_omitted,
            private_init_data_observed,
            private_init_data_names,
            private_init_data_omitted,
            core_observables_syntax_match_observed,
            core_observables_syntax_match_names,
            core_observables_syntax_match_omitted,
            private_lean_syntax_observed,
            private_lean_syntax_names,
            private_lean_syntax_omitted,
            array_map_m_proof_observed,
            array_map_m_proof_names,
            array_map_m_proof_omitted,
            array_map_m_go_observed,
            array_map_m_go_names,
            array_map_m_go_omitted,
            private_array_map_m_observed,
            private_array_map_m_names,
            private_array_map_m_omitted,
            private_go_observed,
            private_go_names,
            private_go_omitted,
            string_extra_unsafe_rec_observed,
            string_extra_unsafe_rec_names,
            string_extra_unsafe_rec_omitted,
            merge_sort_companion_only_unsafe_rec_observed,
            merge_sort_companion_only_unsafe_rec_names,
            merge_sort_companion_only_unsafe_rec_omitted,
            merge_sort_internal_merge_unsafe_rec_observed,
            merge_sort_internal_merge_unsafe_rec_names,
            merge_sort_internal_merge_unsafe_rec_omitted,
            private_loop_match_one_observed,
            private_loop_match_one_names,
            private_loop_match_one_omitted,
            private_loop_match_n_observed,
            private_loop_match_n_names,
            private_loop_match_n_omitted,
            private_loop_unsafe_rec_observed,
            private_loop_unsafe_rec_names,
            private_loop_unsafe_rec_omitted,
            private_loop_eq_def_observed,
            private_loop_eq_def_names,
            private_loop_eq_def_omitted,
            private_insert_idx_loop_unary_observed,
            private_insert_idx_loop_unary_names,
            private_insert_idx_loop_unary_omitted,
            private_unary_observed,
            private_unary_names,
            private_unary_omitted,
            private_merge_sort_tr_unsafe_rec_observed,
            private_merge_sort_tr_unsafe_rec_names,
            private_merge_sort_tr_unsafe_rec_omitted,
            private_run_unsafe_rec_observed,
            private_run_unsafe_rec_names,
            private_run_unsafe_rec_omitted,
            private_go_unsafe_rec_observed,
            private_go_unsafe_rec_names,
            private_go_unsafe_rec_omitted,
            private_merge_tr_go_unsafe_rec_observed,
            private_merge_tr_go_unsafe_rec_names,
            private_merge_tr_go_unsafe_rec_omitted,
            private_split_rev_at_go_unsafe_rec_observed,
            private_split_rev_at_go_unsafe_rec_names,
            private_split_rev_at_go_unsafe_rec_omitted,
            merge_sort_internal_split_traversal_unsafe_rec_observed,
            merge_sort_internal_split_traversal_unsafe_rec_names,
            merge_sort_internal_split_traversal_unsafe_rec_omitted,
            private_find_leading_spaces_consume_unsafe_rec_observed,
            private_find_leading_spaces_consume_unsafe_rec_names,
            private_find_leading_spaces_consume_unsafe_rec_omitted,
            private_find_leading_spaces_next_line_unsafe_rec_observed,
            private_find_leading_spaces_next_line_unsafe_rec_names,
            private_find_leading_spaces_next_line_unsafe_rec_omitted,
            core_observables_loop_unsafe_rec_observed,
            core_observables_loop_unsafe_rec_names,
            core_observables_loop_unsafe_rec_omitted,
            checked.base_logical_root,
            checked.result_logical_root,
            extensions,
            companion_modules,
            receipts_human_line,
        )
    };
    MultiplexerOutput::success(stdout)
}

const CHECK_OLEAN_FRONTIER_SCHEMA: &str = "fln.check-olean-frontier/1";

/// Join the modules under each further root to `modules`, in root order, for a
/// frontier over a library together with the libraries it imports. A root must
/// be a real directory, a module name found under two roots is refused (the
/// set would not say which artifact it checked), and `max_bytes` bounds the
/// whole set, not each root.
fn add_module_set_roots(
    mut modules: Vec<NamedOleanBytes>,
    roots: &[PathBuf],
    max_bytes: usize,
) -> Result<Vec<NamedOleanBytes>, (&'static str, String)> {
    let module_bytes = |module: &NamedOleanBytes| {
        module.bytes.len()
            + module.server_bytes.as_ref().map_or(0, Vec::len)
            + module.private_bytes.as_ref().map_or(0, Vec::len)
    };
    let mut used = modules.iter().map(module_bytes).sum::<usize>();
    let mut names = modules
        .iter()
        .map(|module| module.name.clone())
        .collect::<BTreeSet<_>>();
    for root in roots {
        match std::fs::symlink_metadata(root) {
            Ok(metadata) if !metadata.file_type().is_symlink() && metadata.is_dir() => {}
            Ok(_) => {
                return Err((
                    "input",
                    format!(
                        "module-set root {} must be a real directory, not a symlink or a file",
                        root.display()
                    ),
                ));
            }
            Err(error) => {
                return Err((
                    "input",
                    format!("cannot inspect {}: {error}", root.display()),
                ));
            }
        }
        let added = collect_olean_directory(root, max_bytes.saturating_sub(used))
            .map_err(|error| (error.class(), error.to_string()))?;
        for module in added {
            if !names.insert(module.name.clone()) {
                return Err((
                    "input",
                    format!(
                        "module {} is found under more than one root; the last was {}",
                        module.name.to_display_string(),
                        root.display()
                    ),
                ));
            }
            used = used.saturating_add(module_bytes(&module));
            modules.push(module);
        }
    }
    let limit = fln::OleanCheckLimits::new(
        max_bytes,
        fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
    )
    .max_modules;
    if modules.len() > limit {
        return Err((
            "resource",
            format!(
                ".olean module count {} exceeds the limit {limit}",
                modules.len()
            ),
        ));
    }
    Ok(modules)
}

/// `fln check-olean --continue DIR`: one verdict row per module instead of an
/// all-or-nothing answer. Exit 0 only when every module is accepted; 4 on any
/// internal fault; 1 when any module failed or was blocked; 3 when the only
/// non-acceptances are inconclusive.
fn check_olean_module_frontier(
    modules: Vec<NamedOleanBytes>,
    max_bytes: usize,
    json: bool,
    progress: bool,
    jobs: std::num::NonZeroUsize,
) -> MultiplexerOutput {
    let worker = match std::thread::Builder::new()
        .name("fln-check-olean-frontier".to_owned())
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
            let mut stream = |event: fln::OleanFrontierEvent<'_>| {
                if progress {
                    let line = match event {
                        fln::OleanFrontierEvent::Started {
                            position,
                            total,
                            module,
                        } => format!(
                            "{{\"schema\":\"fln.check-olean-frontier-progress/1\",\"event\":\"started\",\"position\":{position},\"total\":{total},\"module\":{}}}\n",
                            json_string(&module.to_display_string()),
                        ),
                        fln::OleanFrontierEvent::Decided {
                            position,
                            total,
                            row,
                        } => format!(
                            "{{\"schema\":\"fln.check-olean-frontier-progress/1\",\"event\":\"decided\",\"position\":{position},\"total\":{total},{}}}\n",
                            frontier_row_fields(row).json_members(),
                        ),
                    };
                    use std::io::Write as _;
                    let mut stderr = std::io::stderr().lock();
                    // A progress line that cannot be written must not change the
                    // verdicts, which the final document still carries in full.
                    let _ = stderr.write_all(line.as_bytes());
                    let _ = stderr.flush();
                }
            };
            match engine.check_olean_frontier_scheduled(
                &inputs,
                &fln::KVMap::new(),
                fln::OleanCheckLimits::new(
                    max_bytes,
                    fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
                ),
                fln::OleanFrontierJobs {
                    threads: jobs,
                    worker_stack_bytes: SOURCE_RUN_KERNEL_STACK_BYTES,
                },
                &mut stream,
            ) {
                Ok(frontier) => render_check_olean_frontier(&frontier, json),
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

/// One frontier row's reported fields, shared by the final document and the
/// `--progress` stream so the two can never describe a row differently.
struct FrontierRowFields {
    module: String,
    verdict: &'static str,
    count: usize,
    elapsed_ms: u128,
    detail: BoundedText,
    blocked_by: String,
}

impl FrontierRowFields {
    fn json_members(&self) -> String {
        format!(
            concat!(
                "\"module\":{},\"verdict\":{},\"declarations\":{},\"elapsedMs\":{},",
                "\"detail\":{},\"detailTruncated\":{},\"blockedBy\":{}"
            ),
            json_string(&self.module),
            json_string(self.verdict),
            self.count,
            self.elapsed_ms,
            json_string(self.detail.text()),
            self.detail.truncated(),
            if self.blocked_by.is_empty() {
                "null".to_owned()
            } else {
                json_string(&self.blocked_by)
            },
        )
    }
}

fn frontier_row_fields(row: &fln::OleanFrontierRow) -> FrontierRowFields {
    let (verdict, count, detail, blocked_by) = match &row.verdict {
        fln::OleanModuleVerdict::Accepted { declarations } => {
            ("accepted", *declarations, String::new(), String::new())
        }
        fln::OleanModuleVerdict::Failed(error) => ("failed", 0, error.to_string(), String::new()),
        fln::OleanModuleVerdict::Inconclusive(reason) => {
            ("inconclusive", 0, format!("{reason:?}"), String::new())
        }
        fln::OleanModuleVerdict::InternalFault(fault) => {
            ("internal-fault", 0, format!("{fault:?}"), String::new())
        }
        fln::OleanModuleVerdict::Blocked { by } => {
            ("blocked", 0, String::new(), by.to_display_string())
        }
    };
    FrontierRowFields {
        module: row.name.to_display_string(),
        verdict,
        count,
        elapsed_ms: row.elapsed.as_millis(),
        detail: BoundedText::new(detail),
        blocked_by,
    }
}

fn render_check_olean_frontier(frontier: &fln::OleanFrontier, json: bool) -> MultiplexerOutput {
    let (mut accepted, mut failed, mut inconclusive, mut faulted, mut blocked) = (0, 0, 0, 0, 0);
    let mut declarations = 0_usize;
    let mut rows = Vec::with_capacity(frontier.rows.len());
    let mut lines = Vec::new();
    for row in &frontier.rows {
        let fields = frontier_row_fields(row);
        match fields.verdict {
            "accepted" => {
                accepted += 1;
                declarations += fields.count;
            }
            "failed" => failed += 1,
            "inconclusive" => inconclusive += 1,
            "internal-fault" => faulted += 1,
            _ => blocked += 1,
        }
        rows.push(format!("{{{}}}", fields.json_members()));
        let (module, verdict, count, elapsed_ms, detail, blocked_by) = (
            &fields.module,
            fields.verdict,
            fields.count,
            fields.elapsed_ms,
            &fields.detail,
            &fields.blocked_by,
        );
        lines.push(match verdict {
            "accepted" => {
                format!("  accepted      {module}: {count} declarations in {elapsed_ms} ms")
            }
            "blocked" => {
                format!("  blocked       {module}: import {blocked_by} has no accepted verdict")
            }
            other => format!("  {other:<13} {module}: {}", detail.text()),
        });
    }
    let total = frontier.rows.len();
    let exit_code = if faulted > 0 {
        4
    } else if failed > 0 || blocked > 0 {
        1
    } else if inconclusive > 0 {
        3
    } else {
        0
    };
    let summary = format!(
        "council modules: {accepted}/{total} accepted, {declarations} declarations; {failed} failed, {inconclusive} inconclusive, {faulted} internal-fault, {blocked} blocked"
    );
    let output = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":{},\"authority\":true,\"modules\":{},",
                "\"accepted\":{},\"failed\":{},\"inconclusive\":{},\"internalFault\":{},",
                "\"blocked\":{},\"acceptedDeclarations\":{},\"rows\":[{}]}}\n"
            ),
            json_string(CHECK_OLEAN_FRONTIER_SCHEMA),
            json_string(if exit_code == 0 {
                "complete"
            } else {
                "frontier"
            }),
            total,
            accepted,
            failed,
            inconclusive,
            faulted,
            blocked,
            declarations,
            rows.join(","),
        )
    } else {
        format!(
            "fln check-olean --continue: {summary}\n{}\n",
            lines.join("\n")
        )
    };
    if exit_code == 0 {
        MultiplexerOutput::success(output)
    } else {
        MultiplexerOutput {
            stdout: output,
            stderr: String::new(),
            exit_code,
        }
    }
}

fn check_olean_module_bytes(
    modules: Vec<NamedOleanBytes>,
    max_bytes: usize,
    json: bool,
    receipts_path: Option<PathBuf>,
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
                    let written = match receipts_path {
                        Some(path) => match write_receipt_set(&path, &modules, &checked) {
                            Ok(written) => Some(written),
                            Err(error) => {
                                let (class, exit_code) = error.disposition();
                                return check_olean_failure(
                                    class,
                                    &error.to_string(),
                                    false,
                                    json,
                                    exit_code,
                                );
                            }
                        },
                        None => None,
                    };
                    render_check_olean_set_success(total_bytes, &checked, json, written.as_ref())
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

fn check_olean(
    roots: &[PathBuf],
    max_bytes: usize,
    json: bool,
    receipts: Option<&Path>,
    continue_on_failure: bool,
    progress: bool,
    jobs: std::num::NonZeroUsize,
) -> MultiplexerOutput {
    let Some((path, extra_roots)) = roots.split_first() else {
        return check_olean_failure("input", "no input path", false, json, 1);
    };
    if continue_on_failure && receipts.is_some() {
        return check_olean_failure(
            "input",
            "--continue reports a per-module frontier, which is not a complete checked set, so it writes no receipt set; drop --receipts",
            false,
            json,
            1,
        );
    }
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
    if let Some(receipts) = receipts
        && !metadata.is_dir()
    {
        return check_olean_failure(
            "input",
            &format!(
                "--receipts {} requires a closed module-set root (a directory); a single import-free artifact writes no receipt set",
                receipts.display()
            ),
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
        if continue_on_failure {
            let modules = match add_module_set_roots(modules, extra_roots, max_bytes) {
                Ok(modules) => modules,
                Err((class, detail)) => {
                    return check_olean_failure(
                        class,
                        &detail,
                        false,
                        json,
                        if class == "resource" { 3 } else { 1 },
                    );
                }
            };
            return check_olean_module_frontier(modules, max_bytes, json, progress, jobs);
        }
        return check_olean_module_bytes(modules, max_bytes, json, receipts.map(Path::to_path_buf));
    }
    if continue_on_failure {
        return check_olean_failure(
            "input",
            &format!(
                "--continue requires a closed module-set root (a directory); {} is a single artifact",
                path.display()
            ),
            false,
            json,
            1,
        );
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

// ---- trust surfaces: identity, audit --tcb, why-trusts, run receipts -----

const RECEIPT_SET_SCHEMA: &str = "fln.check-olean.run-receipt/1";
const AUDIT_TCB_SCHEMA: &str = "fln.audit-tcb/1";
const WHY_TRUSTS_SCHEMA: &str = "fln.why-trusts/1";
const IDENTITY_SCHEMA: &str = "fln.identity/1";
const DOCTOR_SCHEMA: &str = "fln.doctor/2";
const CAPABILITY_NOTICE_SCHEMA: &str = "fln.capability-notice/2";
/// Documented exit code for a verb whose capability is planned but not built.
const CAPABILITY_NOT_IMPLEMENTED_EXIT: u8 = 5;
const WHY_TRUSTS_MAX_UNRESOLVED_SAMPLE: usize = 16;

/// Baked, compile-time build facts for `fln identity`. Every value is derived
/// by `build.rs` from SUITE.lock or this crate's own provenance comment; a
/// missing source bakes as `unavailable` rather than being probed at runtime.
fn render_identity(json: bool) -> MultiplexerOutput {
    let reference_tag = env!("FLN_IDENTITY_REFERENCE_TAG");
    let reference_commit = env!("FLN_IDENTITY_REFERENCE_COMMIT");
    let corpus_tag = env!("FLN_IDENTITY_CORPUS_TAG");
    let corpus_commit = env!("FLN_IDENTITY_CORPUS_COMMIT");
    let rust_channel = env!("FLN_IDENTITY_RUST_CHANNEL");
    let product_root = env!("FLN_IDENTITY_PRODUCT_ROOT");
    if json {
        MultiplexerOutput::success(format!(
            concat!(
                "{{\"schema\":{},\"version\":{},\"productRoot\":{},",
                "\"modes\":[\"faithful\",\"sound\",\"frontier\"],",
                "\"reference\":{{\"tag\":{},\"commit\":{}}},",
                "\"corpus\":{{\"tag\":{},\"commit\":{}}},",
                "\"rustChannel\":{}}}\n"
            ),
            json_string(IDENTITY_SCHEMA),
            json_string(env!("CARGO_PKG_VERSION")),
            json_string(product_root),
            json_string(reference_tag),
            json_string(reference_commit),
            json_string(corpus_tag),
            json_string(corpus_commit),
            json_string(rust_channel),
        ))
    } else {
        MultiplexerOutput::success(format!(
            concat!(
                "fln identity\n",
                "schema: {}\n",
                "version: {}\n",
                "product root: {}\n",
                "modes: faithful, sound, frontier\n",
                "reference pin: {} ({})\n",
                "corpus pin: {} ({})\n",
                "rust channel: {}\n"
            ),
            IDENTITY_SCHEMA,
            env!("CARGO_PKG_VERSION"),
            product_root,
            reference_tag,
            reference_commit,
            corpus_tag,
            corpus_commit,
            rust_channel,
        ))
    }
}

/// One probed fact reported by `fln doctor`. Only `required` checks decide the
/// exit code; informational checks describe the environment without failing it.
struct DoctorCheck {
    name: &'static str,
    required: bool,
    status: &'static str,
    detail: String,
}

/// Planned subsystems `fln doctor` names instead of claiming, with owning beads.
const DOCTOR_NOT_IMPLEMENTED: &[(&str, &str)] = &[
    ("native Mirror facade implementations", "franken_lean-epx"),
    (
        "Lantern daemon with shared import heap and RPC sessions",
        "franken_lean-v2p",
    ),
    ("Ledger content-addressed build store", "franken_lean-xy6"),
    ("Envoy MCP server", "franken_lean-87av"),
    ("doctor --sql build database", "franken_lean-05g"),
];

/// The K2 row of `fln doctor`'s not-implemented list, derived from the engines the
/// kernel crate says it implements rather than written down beside them.
const DOCTOR_K2: (&str, &str) = ("kernel engine K2 (NbE accelerator)", "franken_lean-g3k");

fn doctor_not_implemented() -> Vec<(&'static str, &'static str)> {
    let single_engine = fln::EngineId::IMPLEMENTED
        .iter()
        .all(|engine| engine.is(fln::EngineId::K1));
    let mut planned = Vec::with_capacity(DOCTOR_NOT_IMPLEMENTED.len() + 1);
    if single_engine {
        planned.push(DOCTOR_K2);
    }
    planned.extend_from_slice(DOCTOR_NOT_IMPLEMENTED);
    planned
}

fn render_doctor(json: bool) -> MultiplexerOutput {
    let reference_tag = env!("FLN_IDENTITY_REFERENCE_TAG");
    let reference_commit = env!("FLN_IDENTITY_REFERENCE_COMMIT");
    let corpus_commit = env!("FLN_IDENTITY_CORPUS_COMMIT");
    let rust_channel = env!("FLN_IDENTITY_RUST_CHANNEL");

    let mut checks = vec![doctor_pipeline_smoke()];
    match std::env::current_dir()
        .ok()
        .and_then(|dir| doctor_checkout_root(&dir))
    {
        Some(root) => {
            checks.push(doctor_pin_agreement(
                &root,
                reference_commit,
                corpus_commit,
                rust_channel,
            ));
            checks.push(doctor_census_shards(&root));
        }
        None => checks.push(DoctorCheck {
            name: "checkout_pins",
            required: false,
            status: "not_applicable",
            detail: "not run inside a franken_lean checkout (no SUITE.lock in any ancestor)"
                .to_owned(),
        }),
    }
    checks.push(doctor_reference_toolchain(reference_tag));
    checks.push(doctor_path_tool("cc", "optional D2 tool for --backend c"));
    checks.push(doctor_path_tool(
        "git",
        "optional D2 tool for Lake dependency fetching",
    ));

    let failed = checks
        .iter()
        .any(|check| check.required && check.status != "ok");
    let status = if failed { "failed" } else { "ok" };
    let exit_code = u8::from(failed);

    let stdout = if json {
        let rows: Vec<String> = checks
            .iter()
            .map(|check| {
                format!(
                    "{{\"name\":{},\"required\":{},\"status\":{},\"detail\":{}}}",
                    json_string(check.name),
                    check.required,
                    json_string(check.status),
                    json_string(&check.detail),
                )
            })
            .collect();
        let planned: Vec<String> = doctor_not_implemented()
            .iter()
            .map(|(subsystem, bead)| {
                format!(
                    "{{\"subsystem\":{},\"bead\":{}}}",
                    json_string(subsystem),
                    json_string(bead)
                )
            })
            .collect();
        format!(
            "{{\"schema\":{},\"status\":{},\"version\":{},\"reference\":{{\"tag\":{},\"commit\":{}}},\"checks\":[{}],\"not_implemented\":[{}]}}\n",
            json_string(DOCTOR_SCHEMA),
            json_string(status),
            json_string(env!("CARGO_PKG_VERSION")),
            json_string(reference_tag),
            json_string(reference_commit),
            rows.join(","),
            planned.join(","),
        )
    } else {
        let mut text = format!(
            "fln doctor: environment probe (package {}, reference {reference_tag})\n",
            env!("CARGO_PKG_VERSION")
        );
        for check in &checks {
            let kind = if check.required { "required" } else { "info" };
            text.push_str(&format!(
                "[{}] {} ({kind}): {}\n",
                check.status, check.name, check.detail
            ));
        }
        text.push_str("not implemented yet:\n");
        for (subsystem, bead) in doctor_not_implemented() {
            text.push_str(&format!("  - {subsystem} (bead {bead})\n"));
        }
        text.push_str(if failed {
            "doctor: a required check failed.\n"
        } else {
            "doctor: all required checks passed.\n"
        });
        text
    };
    MultiplexerOutput {
        stdout,
        stderr: String::new(),
        exit_code,
    }
}

/// Runs one definition through the real source pipeline: parser, elaborator,
/// K1, the independent checker, compiler, canonical FLBC, and Golem.
fn doctor_pipeline_smoke() -> DoctorCheck {
    let name = "source_pipeline_smoke";
    let budget = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
    let failed = |detail: String| DoctorCheck {
        name,
        required: true,
        status: "failed",
        detail,
    };
    let engine = match fln::Engine::with_source_seed(fln::EngineAdmissionLimits::new(budget)) {
        Ok(fln::Outcome::Complete(engine)) => engine,
        Ok(other) => return failed(format!("source seed did not complete: {other:?}")),
        Err(error) => return failed(format!("source seed refused: {error}")),
    };
    let sources: [&[u8]; 1] = [b"def doctorProbe : Nat := 6 * 7"];
    let completed = match engine.execute_source_definitions(
        &sources,
        &fln::KVMap::new(),
        fln::EngineExecutionLimits::new(budget),
    ) {
        Ok(fln::Outcome::Complete(completed)) => completed,
        Ok(other) => return failed(format!("probe execution did not complete: {other:?}")),
        Err(error) => return failed(format!("probe execution refused: {error}")),
    };
    let returned = completed
        .executions
        .last()
        .map(|execution| fln::closed_vm_value(&execution.exit));
    let admitted = completed
        .engine
        .environment()
        .find(&fln::Name::from_components(["doctorProbe"]))
        .is_some();
    match returned {
        Some(Ok(Some(fln::ClosedVmValue::Scalar(42)))) if admitted => DoctorCheck {
            name,
            required: true,
            status: "ok",
            detail: "def doctorProbe : Nat := 6 * 7 admitted by K1 and the independent checker and returned 42 on Golem".to_owned(),
        },
        other => failed(format!(
            "probe returned {other:?} (admitted: {admitted}); expected Nat 42"
        )),
    }
}

fn doctor_checkout_root(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .take(64)
        .find(|dir| dir.join("SUITE.lock").is_file() && dir.join("Cargo.toml").is_file())
        .map(Path::to_path_buf)
}

/// A binary built for one pin but run inside a checkout pinned elsewhere answers
/// for the wrong epoch; that is a required failure.
fn doctor_pin_agreement(
    root: &Path,
    reference_commit: &str,
    corpus_commit: &str,
    rust_channel: &str,
) -> DoctorCheck {
    let name = "checkout_pins";
    let lock = match std::fs::read_to_string(root.join("SUITE.lock")) {
        Ok(text) => text,
        Err(error) => {
            return DoctorCheck {
                name,
                required: true,
                status: "failed",
                detail: format!("cannot read {}: {error}", root.join("SUITE.lock").display()),
            };
        }
    };
    let field = |row: &str, key: &str| -> Option<String> {
        lock.lines()
            .map(str::trim)
            .find(|line| line.starts_with(row))
            .and_then(|line| {
                line.split_whitespace()
                    .find_map(|word| word.strip_prefix(key))
                    .map(str::to_owned)
            })
    };
    let lock_reference = field("reference ", "commit=");
    let lock_corpus = field("corpus ", "commit=");
    let lock_rust = lock
        .lines()
        .map(str::trim)
        .find_map(|line| line.strip_prefix("rust-nightly "))
        .map(|rest| rest.trim().to_owned());
    let toolchain_channel = std::fs::read_to_string(root.join("rust-toolchain.toml"))
        .ok()
        .and_then(|text| {
            text.lines()
                .map(str::trim)
                .find_map(|line| line.strip_prefix("channel"))
                .map(|rest| {
                    rest.trim_start_matches([' ', '='])
                        .trim()
                        .trim_matches('"')
                        .to_owned()
                })
        });
    let mut mismatches = Vec::new();
    if lock_reference.as_deref() != Some(reference_commit) {
        mismatches.push(format!(
            "reference commit: binary {reference_commit}, SUITE.lock {lock_reference:?}"
        ));
    }
    if lock_corpus.as_deref() != Some(corpus_commit) {
        mismatches.push(format!(
            "corpus commit: binary {corpus_commit}, SUITE.lock {lock_corpus:?}"
        ));
    }
    if lock_rust.as_deref() != Some(rust_channel) {
        mismatches.push(format!(
            "rust channel: binary {rust_channel}, SUITE.lock {lock_rust:?}"
        ));
    }
    if toolchain_channel.is_some() && toolchain_channel != lock_rust {
        mismatches.push(format!(
            "rust-toolchain.toml channel {toolchain_channel:?} differs from SUITE.lock {lock_rust:?}"
        ));
    }
    if mismatches.is_empty() {
        DoctorCheck {
            name,
            required: true,
            status: "ok",
            detail: format!("binary pins match {}", root.join("SUITE.lock").display()),
        }
    } else {
        DoctorCheck {
            name,
            required: true,
            status: "mismatch",
            detail: mismatches.join("; "),
        }
    }
}

fn doctor_census_shards(root: &Path) -> DoctorCheck {
    let shards = [
        "contracts/builtin_partition.tsv",
        "contracts/builtin_environment.tsv",
        "contracts/extern_census.tsv",
    ];
    let missing: Vec<&str> = shards
        .iter()
        .copied()
        .filter(|shard| !root.join(shard).is_file())
        .collect();
    DoctorCheck {
        name: "census_shards",
        required: false,
        status: if missing.is_empty() { "ok" } else { "missing" },
        detail: if missing.is_empty() {
            "builtin and extern census shards present".to_owned()
        } else {
            format!(
                "absent (untracked shards are regenerated by the census extractor): {}",
                missing.join(", ")
            )
        },
    }
}

/// The Reference is Tribunal oracle apparatus, never a product dependency, so
/// its absence is reported but never fails the product.
fn doctor_reference_toolchain(tag: &str) -> DoctorCheck {
    let elan_home = std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".elan")));
    let Some(elan_home) = elan_home else {
        return DoctorCheck {
            name: "reference_oracle_toolchain",
            required: false,
            status: "missing",
            detail: "neither ELAN_HOME nor HOME is set".to_owned(),
        };
    };
    let root = elan_home
        .join("toolchains")
        .join(format!("leanprover--lean4---{tag}"));
    let lean = root.join("bin").join("lean");
    let prelude = root
        .join("lib")
        .join("lean")
        .join("Init")
        .join("Prelude.olean");
    let present = lean.is_file() && prelude.is_file();
    DoctorCheck {
        name: "reference_oracle_toolchain",
        required: false,
        status: if present { "ok" } else { "missing" },
        detail: if present {
            format!(
                "{} (Tribunal oracle only; never executed by the product)",
                root.display()
            )
        } else {
            format!(
                "{} not found; pin-dependent Tribunal rigs will skip",
                root.display()
            )
        },
    }
}

fn doctor_path_tool(tool: &'static str, role: &str) -> DoctorCheck {
    let found = std::env::var_os("PATH").and_then(|path| {
        std::env::split_paths(&path)
            .map(|dir| dir.join(tool))
            .find(|candidate| candidate.is_file())
    });
    DoctorCheck {
        name: tool,
        required: false,
        status: if found.is_some() { "ok" } else { "missing" },
        detail: match found {
            Some(path) => format!("{} ({role})", path.display()),
            None => format!("not on PATH ({role})"),
        },
    }
}

fn render_capability_notice(command: &str, json: bool) -> MultiplexerOutput {
    if command == "doctor" {
        return render_doctor(json);
    }
    let (gate, description) = match command {
        "serve-mcp" => ("G6", "Envoy Model Context Protocol server (plan §16.3)"),
        "replay" => (
            "G5",
            "Palimpsest deterministic elaboration replay (plan §15)",
        ),
        "cache" => ("G2", "Ledger content-addressed artifact cache (plan §13.2)"),
        "doctor --sql" => (
            "G5",
            "SQL surface over the build database (plan §15.5; bead franken_lean-05g)",
        ),
        "build" | "build explain" => (
            "G2",
            "Ledger build fabric and dependency planner (plan §13)",
        ),
        _ => ("G0", "Planned FrankenLean capability"),
    };
    if json {
        MultiplexerOutput::failure(
            format!(
                "{{\"schema\":{},\"command\":{},\"status\":\"not_implemented\",\"gate\":{},\"description\":{},\"exit_code\":{}}}\n",
                json_string(CAPABILITY_NOTICE_SCHEMA),
                json_string(command),
                json_string(gate),
                json_string(description),
                CAPABILITY_NOT_IMPLEMENTED_EXIT,
            ),
            CAPABILITY_NOT_IMPLEMENTED_EXIT,
        )
    } else {
        MultiplexerOutput::failure(
            format!(
                "fln {command}: not implemented; planned under {gate} ({description})\nSee COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md\n"
            ),
            CAPABILITY_NOT_IMPLEMENTED_EXIT,
        )
    }
}

#[derive(Debug)]
enum TrustSurfaceError {
    Read(BoundedReadFailure),
    Decode {
        module: String,
        error: fln::OleanDecodeError,
    },
    MissingImports {
        module: String,
        missing: Vec<String>,
    },
    DuplicateModule(String),
    EmptySet,
    ConstantNotFound(String),
}

impl TrustSurfaceError {
    const fn class(&self) -> &'static str {
        match self {
            Self::Read(error) => error.class(),
            Self::Decode { error, .. } if error.is_resource_exhaustion() => "resource",
            Self::Decode { .. } | Self::MissingImports { .. } => "decode",
            Self::DuplicateModule(_) | Self::EmptySet | Self::ConstantNotFound(_) => "input",
        }
    }
    fn exit_code(&self) -> u8 {
        match self.class() {
            "resource" => 3,
            _ => 1,
        }
    }
}

impl fmt::Display for TrustSurfaceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(error) => error.fmt(formatter),
            Self::Decode { module, error } => {
                write!(formatter, "module {module}: {error}")
            }
            Self::MissingImports { module, missing } => {
                let list = missing.join(", ");
                write!(
                    formatter,
                    "module {module}: imports outside the supplied set: {list}"
                )
            }
            Self::DuplicateModule(module) => {
                write!(formatter, "module {module} appears more than once")
            }
            Self::ConstantNotFound(name) => {
                write!(
                    formatter,
                    "constant {name} is not present in the supplied set"
                )
            }
            Self::EmptySet => formatter.write_str("the supplied set contains no .olean artifact"),
        }
    }
}

fn checker_ground_name(ground: fln::CheckerAdmissionGround) -> &'static str {
    match ground {
        fln::CheckerAdmissionGround::AxiomPreamble => "axiom-preamble",
        fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType => {
            "body-checked-against-declared-type"
        }
        fln::CheckerAdmissionGround::QuotientPrimitiveChecked => "quotient-primitive-checked",
        fln::CheckerAdmissionGround::InductiveNonrecursiveChecked => {
            "inductive-nonrecursive-checked"
        }
        fln::CheckerAdmissionGround::UnsafeQuarantine => "unsafe-quarantine",
        fln::CheckerAdmissionGround::PartialQuarantine => "partial-quarantine",
    }
}

/// Decode a supplied `.olean` set (no kernel admission) and require that its
/// import graph closes within the set, so trust queries answer over exactly
/// the bytes the caller supplied.
struct DecodedTrustModule {
    name: fln::Name,
    decoded: fln::DecodedOlean,
}

fn decode_trust_surface(
    modules: Vec<NamedOleanBytes>,
) -> Result<Vec<DecodedTrustModule>, TrustSurfaceError> {
    if modules.is_empty() {
        return Err(TrustSurfaceError::EmptySet);
    }
    let mut decoded_modules: Vec<DecodedTrustModule> = Vec::with_capacity(modules.len());
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for module in &modules {
        let name = module.name.to_display_string();
        if !seen.insert(name.clone()) {
            return Err(TrustSurfaceError::DuplicateModule(name));
        }
        let decoded = match (
            module.server_bytes.as_deref(),
            module.private_bytes.as_deref(),
        ) {
            (Some(server), Some(private)) => fln::decode_olean_module_artifacts(
                &module.bytes,
                server,
                private,
                fln::OleanDecodeLimits::new(usize::MAX),
            ),
            _ => fln::decode_olean_artifact(&module.bytes, fln::OleanDecodeLimits::new(usize::MAX)),
        };
        let decoded = match decoded {
            Ok(decoded) => decoded,
            Err(error) => {
                return Err(TrustSurfaceError::Decode {
                    module: name,
                    error,
                });
            }
        };
        decoded_modules.push(DecodedTrustModule {
            name: module.name.clone(),
            decoded,
        });
    }
    for module in &decoded_modules {
        let mut missing: BTreeSet<String> = BTreeSet::new();
        for import in &module.decoded.module.imports {
            let imported = import.module.to_display_string();
            if !seen.contains(&imported) {
                missing.insert(imported);
            }
        }
        if !missing.is_empty() {
            return Err(TrustSurfaceError::MissingImports {
                module: module.name.to_display_string(),
                missing: missing.into_iter().collect(),
            });
        }
    }
    Ok(decoded_modules)
}

/// Constant-reference closure over decoded types and definition/theorem/
/// opaque bodies. Recursor reduction rules and instance selections are NOT
/// traversed; the report states that scope explicitly.
fn collect_const_refs(root: &fln::Expr, refs: &mut Vec<String>) {
    let mut stack = vec![root];
    while let Some(expr) = stack.pop() {
        match expr.node() {
            fln::ExprNode::Const { name, .. } => refs.push(name.to_display_string()),
            fln::ExprNode::App { f, a } => {
                stack.push(a);
                stack.push(f);
            }
            fln::ExprNode::Lam {
                binder_type, body, ..
            }
            | fln::ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            fln::ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(body);
                stack.push(value);
                stack.push(type_);
            }
            fln::ExprNode::MData { expr, .. } | fln::ExprNode::Proj { expr, .. } => {
                stack.push(expr);
            }
            _ => {}
        }
    }
}

const fn trust_value(info: &fln::ConstantInfo) -> Option<&fln::Expr> {
    match info {
        fln::ConstantInfo::Defn(value) => Some(&value.value),
        fln::ConstantInfo::Thm(value) => Some(&value.value),
        fln::ConstantInfo::Opaque(value) => Some(&value.value),
        _ => None,
    }
}

/// Load the `.olean` bytes behind a trust-surface root: a directory holding a
/// closed import set, or one artifact whose companions are loaded when present.
fn load_trust_modules(
    path: &Path,
    max_bytes: usize,
) -> Result<Vec<NamedOleanBytes>, BoundedReadFailure> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| BoundedReadFailure::Input {
        subject: "trust-surface root",
        detail: format!("cannot inspect {}: {error}", path.display()),
    })?;
    if metadata.file_type().is_symlink() {
        return Err(BoundedReadFailure::Input {
            subject: "trust-surface root",
            detail: format!("refusing symlink {} ", path.display()),
        });
    }
    if metadata.is_dir() {
        return collect_olean_directory(path, max_bytes);
    }
    if !metadata.is_file() {
        return Err(BoundedReadFailure::Input {
            subject: "trust-surface root",
            detail: format!(
                "{} is neither a regular file nor a directory",
                path.display()
            ),
        });
    }
    let bytes = read_bounded(path, max_bytes, ".olean artifact")?;
    let mut total = bytes.len();
    let server_path = path.with_extension("olean.server");
    let server_bytes =
        match read_optional_olean_companion(&server_path, max_bytes.saturating_sub(total))? {
            Some(server) => {
                total = total.saturating_add(server.len());
                Some(server)
            }
            None => None,
        };
    let private_path = path.with_extension("olean.private");
    let private_bytes =
        read_optional_olean_companion(&private_path, max_bytes.saturating_sub(total))?;
    let stem = path
        .file_stem()
        .and_then(std::ffi::OsStr::to_str)
        .ok_or_else(|| BoundedReadFailure::Input {
            subject: "trust-surface root",
            detail: format!("module name from {} is not UTF-8", path.display()),
        })?;
    let name = fln::Name::from_components(stem.split('.'));
    Ok(vec![NamedOleanBytes {
        name,
        bytes,
        server_bytes,
        private_bytes,
    }])
}

fn run_trust_surface_failure(error: &TrustSurfaceError, json: bool) -> MultiplexerOutput {
    if !json {
        return MultiplexerOutput::failure(format!("fln: {error}\n"), error.exit_code());
    }
    MultiplexerOutput::failure(
        format!(
            "{{\"schema\":{},\"class\":{},\"detail\":{}}}\n",
            json_string("fln.error/1"),
            json_string(error.class()),
            json_string(&error.to_string()),
        ),
        error.exit_code(),
    )
}

struct TrustAxiomRow {
    name: String,
    is_unsafe: bool,
}

fn inventory_module(decoded: &DecodedTrustModule) -> (usize, Vec<TrustAxiomRow>, usize, usize) {
    let mut axioms = Vec::new();
    let mut unsafe_definitions = 0_usize;
    let mut partial_definitions = 0_usize;
    for info in &decoded.decoded.constants {
        match info {
            fln::ConstantInfo::Axiom(axiom) => axioms.push(TrustAxiomRow {
                name: axiom.base.name.to_display_string(),
                is_unsafe: axiom.is_unsafe,
            }),
            fln::ConstantInfo::Defn(definition) => match definition.safety {
                fln::DefinitionSafety::Unsafe => unsafe_definitions += 1,
                fln::DefinitionSafety::Partial => partial_definitions += 1,
                fln::DefinitionSafety::Safe => {}
            },
            _ => {}
        }
    }
    axioms.sort_by(|left, right| left.name.cmp(&right.name));
    (
        decoded.decoded.constants.len(),
        axioms,
        unsafe_definitions,
        partial_definitions,
    )
}

fn audit_tcb(path: &Path, max_bytes: usize, json: bool) -> MultiplexerOutput {
    let execution = || -> Result<MultiplexerOutput, TrustSurfaceError> {
        let modules = load_trust_modules(path, max_bytes).map_err(TrustSurfaceError::Read)?;
        let decoded = decode_trust_surface(modules)?;
        let mut total_axioms = 0_usize;
        let mut rows: Vec<(String, usize, Vec<TrustAxiomRow>, usize, usize)> =
            Vec::with_capacity(decoded.len());
        for module in &decoded {
            let (constants, axioms, unsafe_definitions, partial_definitions) =
                inventory_module(module);
            total_axioms += axioms.len();
            rows.push((
                module.name.to_display_string(),
                constants,
                axioms,
                unsafe_definitions,
                partial_definitions,
            ));
        }
        if json {
            let mut stdout = format!(
                "{{\"schema\":{},\"modules\":{},\"axioms\":{},\"rows\":[",
                json_string(AUDIT_TCB_SCHEMA),
                rows.len(),
                total_axioms,
            );
            for (index, (name, constants, axioms, unsafe_definitions, partial_definitions)) in
                rows.iter().enumerate()
            {
                if index > 0 {
                    stdout.push(',');
                }
                stdout.push_str(&format!(
                    "{{\"module\":{},\"constants\":{},\"unsafeDefinitions\":{},\"partialDefinitions\":{},\"axioms\":[",
                    json_string(name),
                    constants,
                    unsafe_definitions,
                    partial_definitions,
                ));
                for (position, axiom) in axioms.iter().enumerate() {
                    if position > 0 {
                        stdout.push(',');
                    }
                    stdout.push_str(&format!(
                        "{{\"name\":{},\"unsafe\":{}}}",
                        json_string(&axiom.name),
                        axiom.is_unsafe,
                    ));
                }
                stdout.push_str("]}");
            }
            stdout.push_str("]}\n");
            return Ok(MultiplexerOutput::success(stdout));
        }
        let mut stdout = format!(
            concat!(
                "trust surface inventory: complete\n",
                "modules decoded: {}\n",
                "axiom declarations: {}\n",
            ),
            rows.len(),
            total_axioms,
        );
        for (name, constants, axioms, unsafe_definitions, partial_definitions) in &rows {
            stdout.push_str(&format!(
                "{name}: {constants} constants, {} axioms, {unsafe_definitions} unsafe defs, {partial_definitions} partial defs\n",
                axioms.len(),
            ));
            for axiom in axioms {
                let marker = if axiom.is_unsafe { " (unsafe)" } else { "" };
                stdout.push_str(&format!("  axiom {}{}\n", axiom.name, marker));
            }
        }
        stdout.push_str(
            "scope: decoded declarations only; plugins and façade classes are not yet tracked\n",
        );
        Ok(MultiplexerOutput::success(stdout))
    };
    match execution() {
        Ok(output) => output,
        Err(error) => run_trust_surface_failure(&error, json),
    }
}

struct WhyTrustsReport {
    target: String,
    module: String,
    kind: &'static str,
    axioms: Vec<String>,
    visited: usize,
    unresolved_sample: Vec<String>,
    unresolved_total: usize,
    truncated: bool,
}

fn why_trusts(
    target: &str,
    path: &Path,
    max_bytes: usize,
    max_nodes: usize,
    json: bool,
) -> MultiplexerOutput {
    let execution = || -> Result<MultiplexerOutput, TrustSurfaceError> {
        let modules = load_trust_modules(path, max_bytes).map_err(TrustSurfaceError::Read)?;
        let decoded = decode_trust_surface(modules)?;
        let wanted = fln::Name::from_components(target.split('.'));
        let wanted_display = wanted.to_display_string();
        let mut index: BTreeMap<String, (String, &fln::ConstantInfo)> = BTreeMap::new();
        for module in &decoded {
            let module_name = module.name.to_display_string();
            for info in &module.decoded.constants {
                index.insert(info.name().to_display_string(), (module_name.clone(), info));
            }
        }
        let Some((target_module, _)) = index.get(&wanted_display) else {
            return Err(TrustSurfaceError::ConstantNotFound(wanted_display.clone()));
        };
        let target_module = target_module.clone();

        let mut visited: BTreeSet<String> = BTreeSet::new();
        let mut queue: std::collections::VecDeque<String> = std::collections::VecDeque::new();
        queue.push_back(wanted_display.clone());
        let mut axioms: Vec<String> = Vec::new();
        let mut unresolved_sample: Vec<String> = Vec::new();
        let mut unresolved_total = 0_usize;
        let mut truncated = false;
        while let Some(name) = queue.pop_front() {
            if visited.contains(&name) {
                continue;
            }
            if visited.len() >= max_nodes {
                truncated = true;
                break;
            }
            visited.insert(name.clone());
            let Some((_, info)) = index.get(&name) else {
                unresolved_total += 1;
                if unresolved_sample.len() < WHY_TRUSTS_MAX_UNRESOLVED_SAMPLE
                    && !unresolved_sample.contains(&name)
                {
                    unresolved_sample.push(name);
                }
                continue;
            };
            if matches!(info, fln::ConstantInfo::Axiom(_)) {
                axioms.push(name);
                continue;
            }
            let mut refs = Vec::new();
            collect_const_refs(&info.constant_val().type_, &mut refs);
            if let Some(value) = trust_value(info) {
                collect_const_refs(value, &mut refs);
            }
            for reference in refs {
                if !visited.contains(&reference) {
                    queue.push_back(reference);
                }
            }
        }
        axioms.sort();
        axioms.dedup();
        let kind = index
            .get(&wanted_display)
            .map(|(_, info)| info.kind_name())
            .unwrap_or("unknown");
        let report = WhyTrustsReport {
            target: wanted_display,
            module: target_module,
            kind,
            axioms,
            visited: visited.len(),
            unresolved_sample,
            unresolved_total,
            truncated,
        };
        Ok(render_why_trusts(&report, json))
    };
    match execution() {
        Ok(output) => output,
        Err(error) => run_trust_surface_failure(&error, json),
    }
}

fn render_why_trusts(report: &WhyTrustsReport, json: bool) -> MultiplexerOutput {
    if json {
        return MultiplexerOutput::success(format!(
            concat!(
                "{{\"schema\":{},\"target\":{},\"module\":{},\"kind\":{},",
                "\"axioms\":[{}],\"visited\":{},",
                "\"unresolvedTotal\":{},\"unresolvedSample\":[{}],",
                "\"truncated\":{}}}\n"
            ),
            json_string(WHY_TRUSTS_SCHEMA),
            json_string(&report.target),
            json_string(&report.module),
            json_string(report.kind),
            report
                .axioms
                .iter()
                .map(|axiom| json_string(axiom))
                .collect::<Vec<_>>()
                .join(","),
            report.visited,
            report.unresolved_total,
            report
                .unresolved_sample
                .iter()
                .map(|name| json_string(name))
                .collect::<Vec<_>>()
                .join(","),
            report.truncated,
        ));
    }
    let mut stdout = format!(
        concat!("why-trusts: {}\n", "module: {}\n", "kind: {}\n",),
        report.target, report.module, report.kind,
    );
    if report.axioms.is_empty() {
        stdout.push_str("axioms: none\n");
    } else {
        stdout.push_str(&format!("axioms: {}\n", report.axioms.join(", ")));
    }
    stdout.push_str(&format!(
        "reachable constants: {}{}\n",
        report.visited,
        if report.truncated {
            " (truncated by --max-nodes)"
        } else {
            ""
        },
    ));
    stdout.push_str(&format!(
        "unresolved references: {}\n",
        report.unresolved_total
    ));
    stdout.push_str(
        "scope: decoded types and definition/theorem/opaque bodies; recursor rules, instance selections, and rewrite provenance are not traversed\n",
    );
    MultiplexerOutput::success(stdout)
}

// ---- check-olean run receipts -------------------------------------------

#[derive(Debug)]
enum ReceiptWriteError {
    Input { detail: String },
    Resource { detail: String },
}

impl ReceiptWriteError {
    const fn disposition(&self) -> (&'static str, u8) {
        match self {
            Self::Input { .. } => ("input", 1),
            Self::Resource { .. } => ("resource", 3),
        }
    }
}

impl fmt::Display for ReceiptWriteError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input { detail } | Self::Resource { detail } => formatter.write_str(detail),
        }
    }
}

/// Length-prefixed field, so canonical bytes never depend on separator choices.
fn receipt_field(buffer: &mut Vec<u8>, bytes: &[u8]) {
    buffer.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buffer.extend_from_slice(bytes);
}

fn receipt_u64(buffer: &mut Vec<u8>, value: u64) {
    buffer.extend_from_slice(&value.to_le_bytes());
}

struct WrittenReceiptSet {
    path: PathBuf,
    module_rows: usize,
    declarations_checked: usize,
    chain: Digest,
}

impl WrittenReceiptSet {
    fn summary_json(&self) -> String {
        format!(
            "{{\"path\":{},\"moduleRows\":{},\"declarationsChecked\":{},\"chain\":{}}}",
            json_string(&self.path.to_string_lossy()),
            self.module_rows,
            self.declarations_checked,
            json_string(&self.chain.to_hex()),
        )
    }

    fn human_line(&self) -> String {
        format!(
            "receipts: {} module rows, {} declarations checked, chained to {}, written to {}\n",
            self.module_rows,
            self.declarations_checked,
            self.chain.to_hex(),
            self.path.display(),
        )
    }
}

/// Write one hash-chained JSONL receipt set for a completed closed-set check.
///
/// Every row is `row = H(TransparencyLeaf, prev || canonical_fields)` under
/// fln-hash's registered domains, with the first `prev` at zero. Rows carry NO
/// clock values, so an identical module set and byte content reproduce the
/// receipt file byte-for-byte; wall-clock timing belongs to the caller's
/// telemetry, not to a verifiable chain. The set is published no-clobber via a
/// sibling partial file and one rename.
fn write_receipt_set(
    path: &Path,
    modules: &[NamedOleanBytes],
    checked: &fln::CheckedOleanSet,
) -> Result<WrittenReceiptSet, ReceiptWriteError> {
    if path.exists() {
        return Err(ReceiptWriteError::Input {
            detail: format!(
                "refusing to overwrite existing receipt set {}",
                path.display()
            ),
        });
    }
    let parent = match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
        _ => std::path::PathBuf::from("."),
    };
    if !parent.is_dir() {
        return Err(ReceiptWriteError::Input {
            detail: format!(
                "receipt parent directory {} does not exist",
                parent.display()
            ),
        });
    }

    let mut jsonl = String::new();
    let mut prev = [0u8; 32];
    let mut declarations_checked = 0_usize;
    for module in modules {
        let Some(checked_module) = checked
            .modules
            .iter()
            .find(|checked| checked.name == module.name)
        else {
            return Err(ReceiptWriteError::Input {
                detail: format!(
                    "module {} is missing from the checked set",
                    module.name.to_display_string()
                ),
            });
        };
        let mut grounds: BTreeMap<&'static str, usize> = BTreeMap::new();
        for declaration in &checked_module.declarations {
            *grounds
                .entry(checker_ground_name(declaration.checker.ground))
                .or_insert(0) += 1;
        }
        declarations_checked += checked_module.declarations.len();

        let mut artifact_canon = Vec::new();
        receipt_field(
            &mut artifact_canon,
            module.name.to_display_string().as_bytes(),
        );
        receipt_field(&mut artifact_canon, &module.bytes);
        if let Some(server) = &module.server_bytes {
            receipt_field(&mut artifact_canon, server);
        }
        if let Some(private) = &module.private_bytes {
            receipt_field(&mut artifact_canon, private);
        }
        let artifact_root = domain_hash(Domain::ArtifactClosureComponent, &artifact_canon);

        let mut canon = Vec::new();
        receipt_u64(&mut canon, 1); // row kind: module
        receipt_field(&mut canon, prev.as_slice());
        receipt_field(&mut canon, module.name.to_display_string().as_bytes());
        receipt_field(&mut canon, artifact_root.to_hex().as_bytes());
        receipt_u64(&mut canon, checked_module.declarations.len() as u64);
        for (ground, count) in &grounds {
            receipt_field(&mut canon, ground.as_bytes());
            receipt_u64(&mut canon, *count as u64);
        }
        let row_hash = DomainHasher::new(Domain::TransparencyLeaf)
            .update(&canon)
            .finalize();

        let grounds_json = grounds
            .iter()
            .map(|(ground, count)| format!("{}:{}", json_string(ground), count))
            .collect::<Vec<_>>()
            .join(",");
        jsonl.push_str(&format!(
            "{{\"schema\":{schema},\"kind\":\"module\",\"prev\":\"{prev}\",\"module\":{module},\"artifactRoot\":\"{root}\",\"declarationsChecked\":{decls},\"agreementGrounds\":{{{grounds}}},\"rowHash\":\"{hash}\"}}\n",
            schema = json_string(RECEIPT_SET_SCHEMA),
            prev = Digest(prev).to_hex(),
            module = json_string(&module.name.to_display_string()),
            root = artifact_root.to_hex(),
            decls = checked_module.declarations.len(),
            grounds = grounds_json,
            hash = row_hash.to_hex(),
        ));
        prev = row_hash.0;
    }

    let mut summary_canon = Vec::new();
    receipt_u64(&mut summary_canon, 2); // row kind: summary
    receipt_field(&mut summary_canon, prev.as_slice());
    receipt_u64(&mut summary_canon, modules.len() as u64);
    receipt_u64(&mut summary_canon, declarations_checked as u64);
    let chain = DomainHasher::new(Domain::TransparencyLeaf)
        .update(&summary_canon)
        .finalize();
    jsonl.push_str(&format!(
        "{{\"schema\":{},\"kind\":\"summary\",\"prev\":\"{}\",\"moduleRows\":{},\"declarationsChecked\":{},\"chain\":\"{}\"}}\n",
        json_string(RECEIPT_SET_SCHEMA),
        Digest(prev).to_hex(),
        modules.len(),
        declarations_checked,
        chain.to_hex(),
    ));

    let partial = path.with_extension("fln-receipts-partial");
    std::fs::write(&partial, jsonl).map_err(|error| ReceiptWriteError::Resource {
        detail: format!("could not write {}: {error}", partial.display()),
    })?;
    if let Err(error) = std::fs::rename(&partial, path) {
        let _ = std::fs::remove_file(&partial);
        return Err(ReceiptWriteError::Resource {
            detail: format!("could not publish {}: {error}", path.display()),
        });
    }
    Ok(WrittenReceiptSet {
        path: path.to_path_buf(),
        module_rows: modules.len(),
        declarations_checked,
        chain,
    })
}

#[derive(Clone, Copy)]
enum SourcePresentation {
    Fln { json: bool },
    Lean,
}

impl SourcePresentation {
    const fn json(self) -> bool {
        matches!(self, Self::Fln { json: true })
    }
}

#[derive(Debug)]
enum SourcePublication {
    None,
    Flbc {
        path: PathBuf,
        sidecar: Option<SourceSidecarPublication>,
    },
    OleanSnapshot {
        path: PathBuf,
    },
}

#[derive(Debug)]
struct SourceSidecarPublication {
    path: PathBuf,
    toolchain_image: Option<Vec<u8>>,
}

struct SourceSuccess<'a> {
    commands: usize,
    checked_admissions: usize,
    definitions: usize,
    evaluations: usize,
    evaluation_results: Vec<SourceEvaluationResult>,
    source_bytes: usize,
    final_value: SourceFinalValue,
    flbc_bytes: usize,
    base_root: &'a str,
    result_root: &'a str,
    checker_schema: &'a str,
    checker_ground: &'a str,
    emitted_flbc: Option<(&'a Path, usize)>,
    emitted_sidecar: Option<(&'a Path, usize, fln::ContentRoot, fln::ContentRoot)>,
    emitted_olean_snapshot: Option<(&'a Path, usize, usize)>,
    steps: u64,
    system_polls: u64,
    peak_stack_depth: u64,
}

#[derive(Debug)]
enum SourceFinalValue {
    Nat(String),
    String(String),
    Bool(bool),
}

#[derive(Debug)]
struct SourceEvaluationResult {
    command: usize,
    value: SourceFinalValue,
}

impl SourceFinalValue {
    const fn kind(&self) -> &'static str {
        match self {
            Self::Nat(_) => "nat",
            Self::String(_) => "string",
            Self::Bool(_) => "bool",
        }
    }

    fn json(&self) -> String {
        match self {
            Self::Nat(value) => value.clone(),
            Self::String(value) => json_string(value),
            Self::Bool(value) => value.to_string(),
        }
    }
}

impl std::fmt::Display for SourceFinalValue {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nat(value) => write!(formatter, "{value}"),
            Self::String(value) => write!(formatter, "{value:?}"),
            Self::Bool(value) => write!(formatter, "{value}"),
        }
    }
}

fn render_source_success(
    result: SourceSuccess<'_>,
    presentation: SourcePresentation,
) -> MultiplexerOutput {
    if matches!(presentation, SourcePresentation::Lean) {
        return render_lean_evaluation_results(&result.evaluation_results);
    }
    let json = presentation.json();
    let evaluation_results_json = format!(
        "[{}]",
        result
            .evaluation_results
            .iter()
            .map(|evaluation| {
                format!(
                    "{{\"command\":{},\"kind\":{},\"value\":{}}}",
                    evaluation.command,
                    json_string(evaluation.value.kind()),
                    evaluation.value.json(),
                )
            })
            .collect::<Vec<_>>()
            .join(",")
    );
    let evaluation_results_human = if result.evaluation_results.is_empty() {
        "evaluation results: none\n".to_owned()
    } else {
        let rows = result
            .evaluation_results
            .iter()
            .map(|evaluation| {
                format!(
                    "  command {} ({}): {}\n",
                    evaluation.command,
                    evaluation.value.kind(),
                    evaluation.value,
                )
            })
            .collect::<String>();
        format!("evaluation results:\n{rows}")
    };
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
    let emitted_olean_snapshot_json = result.emitted_olean_snapshot.map_or_else(
        || "null".to_owned(),
        |(path, bytes, constants)| {
            format!(
                "{{\"path\":{},\"bytes\":{bytes},\"constants\":{constants},\"module\":false}}",
                json_string(&path.to_string_lossy())
            )
        },
    );
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,",
                "\"commands\":{},\"definitions\":{},\"evaluations\":{},",
                "\"evaluationResults\":{},",
                "\"sourceBytes\":{},\"finalKind\":{},\"finalValue\":{},",
                "\"flbcBytes\":{},\"emittedFlbc\":{},\"emittedSidecar\":{},",
                "\"emittedOleanSnapshot\":{},",
                "\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},",
                "\"checker\":{{\"admissions\":{},\"finalSchema\":{},",
                "\"finalGround\":{}}},",
                "\"finalExecution\":{{\"steps\":{},\"systemPolls\":{},",
                "\"peakStackDepth\":{}}}}}\n"
            ),
            json_string(SOURCE_RUN_SCHEMA),
            result.commands,
            result.definitions,
            result.evaluations,
            evaluation_results_json,
            result.source_bytes,
            json_string(result.final_value.kind()),
            result.final_value.json(),
            result.flbc_bytes,
            emitted_flbc_json,
            emitted_sidecar_json,
            emitted_olean_snapshot_json,
            json_string(result.base_root),
            json_string(result.result_root),
            result.checked_admissions,
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
        let emitted_olean_snapshot = result.emitted_olean_snapshot.map_or_else(
            String::new,
            |(path, bytes, constants)| {
                format!(
                    "emitted standalone .olean snapshot: {bytes} bytes, {constants} constants to {}\n",
                    path.display()
                )
            },
        );
        format!(
            concat!(
                "native source batch: complete\n",
                "commands: {}\n",
                "definitions: {}\n",
                "evaluations: {}\n",
                "{}",
                "final value: {}\n",
                "source bytes: {}\n",
                "canonical FLBC bytes: {} total\n",
                "{}",
                "{}",
                "{}",
                "base logical root: {}\n",
                "result logical root: {}\n",
                "independent checker: {} admissions agreed; final {} ({})\n",
                "final execution: {} steps, {} system polls, peak stack {}\n"
            ),
            result.commands,
            result.definitions,
            result.evaluations,
            evaluation_results_human,
            result.final_value,
            result.source_bytes,
            result.flbc_bytes,
            emitted_flbc,
            emitted_sidecar,
            emitted_olean_snapshot,
            result.base_root,
            result.result_root,
            result.checked_admissions,
            result.checker_schema,
            result.checker_ground,
            result.steps,
            result.system_polls,
            result.peak_stack_depth,
        )
    };
    MultiplexerOutput::success(stdout)
}

fn render_lean_evaluation_results(
    evaluation_results: &[SourceEvaluationResult],
) -> MultiplexerOutput {
    let stdout = evaluation_results
        .iter()
        .map(|evaluation| format!("{}\n", evaluation.value))
        .collect::<String>();
    MultiplexerOutput::success(stdout)
}

fn render_bounded_source_type_atom(type_: &fln::Expr) -> Result<String, &'static str> {
    match type_.node() {
        fln::ExprNode::Const { name, levels } if levels.is_empty() => Ok(name.to_display_string()),
        fln::ExprNode::Sort { level } => match level.to_nat() {
            Some(0) => Ok("Prop".to_owned()),
            Some(1) => Ok("Type".to_owned()),
            Some(level) => Ok(format!("Type {}", level - 1)),
            None => Err("bounded source check inferred a nonconcrete universe"),
        },
        _ => Err("bounded source check inferred an unsupported type shape"),
    }
}

fn render_bounded_source_type(type_: &fln::Expr) -> Result<String, &'static str> {
    let mut domains = Vec::new();
    let mut current = type_;
    while let fln::ExprNode::ForallE {
        binder_type, body, ..
    } = current.node()
    {
        if body.has_loose_bvars() {
            return Err("bounded source check inferred a dependent function type");
        }
        domains.push(render_bounded_source_type_atom(binder_type)?);
        current = body;
    }
    let mut rendered = render_bounded_source_type_atom(current)?;
    for domain in domains.into_iter().rev() {
        rendered = format!("{domain} → {rendered}");
    }
    Ok(rendered)
}

fn render_lean_source_check_line(checked: &fln::SourceCheck) -> Result<String, MultiplexerOutput> {
    let Some(term) = checked.parsed.query_term_normalized() else {
        return Err(source_failure(
            "internal-fault",
            "completed source check did not retain its query term",
            false,
            SourcePresentation::Lean,
            4,
        ));
    };
    let term = term.trim_ascii();
    if term.is_empty() {
        return Err(source_failure(
            "internal-fault",
            "completed source check retained an empty query term",
            false,
            SourcePresentation::Lean,
            4,
        ));
    }
    let type_ = match render_bounded_source_type(&checked.checked_type) {
        Ok(type_) => type_,
        Err(error) => {
            return Err(source_failure(
                "execution",
                error,
                true,
                SourcePresentation::Lean,
                1,
            ));
        }
    };
    Ok(format!("{term} : {type_}\n"))
}

fn source_uses_mixed_lean_commands(source: &[u8]) -> bool {
    // Every source stream can include admission-only commands. Use the common
    // adapter even without #check so a structure/theorem-only file is silent.
    fln::partition_source_module(source).is_ok()
}

fn source_execution_exit_failure(
    command_index: usize,
    exit: &fln::VmExit,
    presentation: SourcePresentation,
) -> Option<MultiplexerOutput> {
    match exit {
        fln::VmExit::Returned(_) => None,
        fln::VmExit::Panicked { message, usage } => Some(source_terminal(
            "program-panic",
            &format!("source command {command_index} panicked: {message}"),
            usage.steps,
            usage.system_polls,
            usage.peak_stack_depth,
            presentation,
        )),
        fln::VmExit::Refused { refusal, usage } => Some(source_terminal(
            "vm-refusal",
            &format!("source command {command_index} was refused: {refusal}"),
            usage.steps,
            usage.system_polls,
            usage.peak_stack_depth,
            presentation,
        )),
    }
}

fn render_lean_source_module_commands(
    completed: &fln::SourceModuleCommandBatchExecution,
) -> MultiplexerOutput {
    if completed.dependency_prefix.is_none()
        && !completed.dependency_execution_command_indices.is_empty()
    {
        return source_failure(
            "internal-fault",
            "dependency source execution indices existed without a retained prefix",
            false,
            SourcePresentation::Lean,
            4,
        );
    }
    if let Some(prefix) = &completed.dependency_prefix {
        if completed.dependency_execution_command_indices.len() != prefix.executions.len() {
            return source_failure(
                "internal-fault",
                "dependency source execution index table did not cover every execution",
                false,
                SourcePresentation::Lean,
                4,
            );
        }
        let mut previous_command = None;
        for (command_index, execution) in completed
            .dependency_execution_command_indices
            .iter()
            .copied()
            .zip(&prefix.executions)
        {
            if command_index >= completed.dependency_command_count
                || previous_command.is_some_and(|previous| previous >= command_index)
            {
                return source_failure(
                    "internal-fault",
                    "dependency source execution command indices were not strictly increasing in range",
                    false,
                    SourcePresentation::Lean,
                    4,
                );
            }
            previous_command = Some(command_index);
            if let Some(failure) = source_execution_exit_failure(
                command_index,
                &execution.exit,
                SourcePresentation::Lean,
            ) {
                return failure;
            }
        }
    }
    render_lean_source_commands(&completed.entry)
}

fn render_lean_source_commands(completed: &fln::SourceCommandBatchExecution) -> MultiplexerOutput {
    if completed.execution_command_indices.len() != completed.batch.executions.len() {
        return source_failure(
            "internal-fault",
            "mixed source execution index table did not cover every execution",
            false,
            SourcePresentation::Lean,
            4,
        );
    }
    let mut previous_execution_command = None;
    for (command_index, execution) in completed
        .execution_command_indices
        .iter()
        .copied()
        .zip(&completed.batch.executions)
    {
        if command_index >= completed.command_count
            || previous_execution_command.is_some_and(|previous| previous >= command_index)
        {
            return source_failure(
                "internal-fault",
                "mixed source execution command indices were not strictly increasing in range",
                false,
                SourcePresentation::Lean,
                4,
            );
        }
        previous_execution_command = Some(command_index);
        if let Some(failure) =
            source_execution_exit_failure(command_index, &execution.exit, SourcePresentation::Lean)
        {
            return failure;
        }
    }

    let mut stdout = String::new();
    let mut previous_output_command = None;
    let mut evaluation_output_position = 0_usize;
    let mut check_output_position = 0_usize;
    for output in &completed.outputs {
        let command_index = match output {
            fln::SourceCommandOutput::Evaluation { command_index, .. }
            | fln::SourceCommandOutput::Check { command_index, .. } => *command_index,
        };
        if command_index >= completed.command_count
            || previous_output_command.is_some_and(|previous| previous >= command_index)
        {
            return source_failure(
                "internal-fault",
                "mixed source output command indices were not strictly increasing in range",
                false,
                SourcePresentation::Lean,
                4,
            );
        }
        previous_output_command = Some(command_index);
        match output {
            fln::SourceCommandOutput::Evaluation {
                execution_index, ..
            } => {
                let Some(execution) = completed.batch.executions.get(*execution_index) else {
                    return source_failure(
                        "internal-fault",
                        "mixed source evaluation index escaped the execution table",
                        false,
                        SourcePresentation::Lean,
                        4,
                    );
                };
                if completed
                    .execution_command_indices
                    .get(*execution_index)
                    .copied()
                    != Some(command_index)
                    || completed
                        .batch
                        .source_evaluation_indices
                        .get(evaluation_output_position)
                        .copied()
                        != Some(*execution_index)
                {
                    return source_failure(
                        "internal-fault",
                        "mixed source evaluation output disagreed with its command index",
                        false,
                        SourcePresentation::Lean,
                        4,
                    );
                }
                evaluation_output_position += 1;
                let value = match closed_source_cli_value(&execution.runtime_type, &execution.exit)
                {
                    Ok(Some(value)) => value,
                    Ok(None) => {
                        return source_failure(
                            "execution",
                            &format!(
                                "evaluation command {command_index} did not produce a closed Nat, String, or Bool value"
                            ),
                            true,
                            SourcePresentation::Lean,
                            1,
                        );
                    }
                    Err(error) => {
                        return source_failure(
                            "internal-fault",
                            &error.to_string(),
                            false,
                            SourcePresentation::Lean,
                            4,
                        );
                    }
                };
                stdout.push_str(&value.to_string());
                stdout.push('\n');
            }
            fln::SourceCommandOutput::Check { check_index, .. } => {
                if *check_index != check_output_position {
                    return source_failure(
                        "internal-fault",
                        "mixed source check outputs did not cover the check table in order",
                        false,
                        SourcePresentation::Lean,
                        4,
                    );
                }
                let Some(check) = completed.checks.get(*check_index) else {
                    return source_failure(
                        "internal-fault",
                        "mixed source check index escaped the check table",
                        false,
                        SourcePresentation::Lean,
                        4,
                    );
                };
                check_output_position += 1;
                let line = match render_lean_source_check_line(check) {
                    Ok(line) => line,
                    Err(error) => return error,
                };
                stdout.push_str(&line);
            }
        }
    }
    if evaluation_output_position != completed.batch.source_evaluation_indices.len() {
        return source_failure(
            "internal-fault",
            "mixed source evaluation index had no output row",
            false,
            SourcePresentation::Lean,
            4,
        );
    }
    if check_output_position != completed.checks.len() {
        return source_failure(
            "internal-fault",
            "mixed source check table had no output row",
            false,
            SourcePresentation::Lean,
            4,
        );
    }
    MultiplexerOutput::success(stdout)
}

fn source_failure(
    class: &'static str,
    detail: &str,
    authority: bool,
    presentation: SourcePresentation,
    exit_code: u8,
) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if presentation.json() {
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
    } else if matches!(presentation, SourcePresentation::Lean) {
        let truncation = if detail.truncated() {
            format!("\n[detail truncated after {} bytes]", BoundedText::LIMIT)
        } else {
            String::new()
        };
        format!("lean: {class}: {}{truncation}\n", detail.text())
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
    presentation: SourcePresentation,
) -> MultiplexerOutput {
    let detail = format!(
        "{detail}; execution used {} steps, {} system polls, peak stack {}",
        steps, system_polls, peak_stack_depth
    );
    source_failure(class, &detail, true, presentation, 1)
}

fn execution_error_disposition(error: &fln::EngineExecutionError) -> (&'static str, bool, u8) {
    match error {
        fln::EngineExecutionError::BatchCommand { error, .. } => execution_error_disposition(error),
        fln::EngineExecutionError::AllocationFailure { .. }
        | fln::EngineExecutionError::SourceModuleLimit { .. }
        | fln::EngineExecutionError::SourceImportLimit { .. }
        | fln::EngineExecutionError::SourceDependencyPresentationLimit { .. }
        | fln::EngineExecutionError::SourceModuleNameLimit { .. } => ("resource", false, 3),
        fln::EngineExecutionError::ImportsRequireResolver { .. }
        | fln::EngineExecutionError::DuplicateSourceModule { .. }
        | fln::EngineExecutionError::MissingSourceEntry { .. }
        | fln::EngineExecutionError::EmptySourceEntry { .. }
        | fln::EngineExecutionError::MissingSourceImports { .. }
        | fln::EngineExecutionError::UnreachableSourceModules { .. }
        | fln::EngineExecutionError::SourceModuleCycle { .. }
        | fln::EngineExecutionError::SourceModuleVisibility { .. }
        | fln::EngineExecutionError::InvalidSourceModuleName { .. } => ("module-graph", false, 1),
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

fn olean_write_error_disposition(error: &fln::OleanWriteError) -> (&'static str, bool, u8) {
    match error {
        fln::OleanWriteError::Budget { .. } => ("resource", false, 3),
        fln::OleanWriteError::Unsupported { .. }
        | fln::OleanWriteError::Contract { .. }
        | fln::OleanWriteError::Region(_) => ("internal-fault", false, 4),
    }
}

fn execute_source_bytes_with_publisher_and_presentation<P, E>(
    sources: Vec<Vec<u8>>,
    module_plan: Option<SourceModulePlan>,
    publication: SourcePublication,
    presentation: SourcePresentation,
    mut publish: P,
) -> MultiplexerOutput
where
    P: FnMut(&[u8], &Path) -> Result<(), E>,
    E: SourcePublicationFailure,
{
    if matches!(presentation, SourcePresentation::Lean)
        && !matches!(&publication, SourcePublication::None)
    {
        return source_failure(
            "internal-fault",
            "the native lean presentation cannot publish fln-specific artifacts",
            false,
            presentation,
            4,
        );
    }
    let (emit_flbc, emit_sidecar, emit_olean_snapshot) = match &publication {
        SourcePublication::None => (None, None, None),
        SourcePublication::Flbc { path, sidecar } => (
            Some(path.as_path()),
            sidecar
                .as_ref()
                .map(|sidecar| (sidecar.path.as_path(), sidecar.toolchain_image.as_deref())),
            None,
        ),
        SourcePublication::OleanSnapshot { path } => (None, None, Some(path.as_path())),
    };
    let Some(source_bytes) = sources
        .iter()
        .try_fold(0_usize, |total, source| total.checked_add(source.len()))
    else {
        return source_failure(
            "resource",
            "aggregate source byte count exceeded this platform",
            false,
            presentation,
            3,
        );
    };
    let mut source_refs = Vec::new();
    if source_refs.try_reserve_exact(sources.len()).is_err() {
        return source_failure(
            "resource",
            "could not reserve the bounded source batch table",
            false,
            presentation,
            3,
        );
    }
    source_refs.extend(sources.iter().map(Vec::as_slice));
    let kernel_budget = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
    let engine = match fln::Engine::with_source_seed(fln::EngineAdmissionLimits::new(kernel_budget))
    {
        Ok(fln::Outcome::Complete(engine)) => engine,
        Ok(fln::Outcome::Inconclusive(inconclusive)) => {
            return source_failure(
                "inconclusive",
                &format!("{inconclusive:?}"),
                false,
                presentation,
                3,
            );
        }
        Ok(fln::Outcome::InternalFault(fault)) => {
            return source_failure(
                "internal-fault",
                &format!("{fault:?}"),
                false,
                presentation,
                4,
            );
        }
        Err(error) => {
            // Seed admission is ordinary declaration admission. A second
            // catch-all here used to promote AllocationFailure to an
            // authoritative `seed` rejection (FL-INV-07).
            let (class, authority, exit_code) = admission_error_disposition(&error);
            return source_failure(
                class,
                &error.to_string(),
                authority,
                presentation,
                exit_code,
            );
        }
    };
    let options = fln::KVMap::new();
    let limits = fln::EngineExecutionLimits::new(kernel_budget);
    if matches!(presentation, SourcePresentation::Lean)
        && module_plan.is_none()
        && source_refs.len() == 1
        && let Some(source) = source_refs.last().copied()
        && source_uses_mixed_lean_commands(source)
    {
        let completed = match engine.execute_source_commands_with_checks(source, &options, limits) {
            Ok(completed) => completed,
            Err(error) => {
                let (class, authority, exit_code) = execution_error_disposition(&error);
                return source_failure(
                    class,
                    &error.to_string(),
                    authority,
                    presentation,
                    exit_code,
                );
            }
        };
        return match completed {
            fln::Outcome::Complete(completed) => render_lean_source_commands(&completed),
            fln::Outcome::Inconclusive(inconclusive) => source_failure(
                "inconclusive",
                &format!("{inconclusive:?}"),
                false,
                presentation,
                3,
            ),
            fln::Outcome::InternalFault(fault) => source_failure(
                "internal-fault",
                &format!("{fault:?}"),
                false,
                presentation,
                4,
            ),
        };
    }
    if matches!(presentation, SourcePresentation::Lean)
        && let Some(plan) = module_plan.as_ref()
    {
        let modules = plan
            .names
            .iter()
            .zip(source_refs.iter().copied())
            .map(|(name, source)| fln::SourceModuleInput { name, source })
            .collect::<Vec<_>>();
        let completed = match engine.execute_source_modules_with_entry_checks(
            &modules,
            &plan.entry,
            &options,
            limits,
        ) {
            Ok(completed) => completed,
            Err(error) => {
                let (class, authority, exit_code) = execution_error_disposition(&error);
                return source_failure(
                    class,
                    &error.to_string(),
                    authority,
                    presentation,
                    exit_code,
                );
            }
        };
        return match completed {
            fln::Outcome::Complete(completed) => render_lean_source_module_commands(&completed),
            fln::Outcome::Inconclusive(inconclusive) => source_failure(
                "inconclusive",
                &format!("{inconclusive:?}"),
                false,
                presentation,
                3,
            ),
            fln::Outcome::InternalFault(fault) => source_failure(
                "internal-fault",
                &format!("{fault:?}"),
                false,
                presentation,
                4,
            ),
        };
    }
    let execution = match module_plan.as_ref() {
        Some(plan) => {
            let modules = plan
                .names
                .iter()
                .zip(source_refs.iter().copied())
                .map(|(name, source)| fln::SourceModuleInput { name, source })
                .collect::<Vec<_>>();
            engine.execute_source_modules(&modules, &plan.entry, &options, limits)
        }
        None => engine.execute_source_definitions(&source_refs, &options, limits),
    };
    let execution = match execution {
        Ok(execution) => execution,
        Err(error) => {
            let (class, authority, exit_code) = execution_error_disposition(&error);
            return source_failure(
                class,
                &error.to_string(),
                authority,
                presentation,
                exit_code,
            );
        }
    };
    let completed = match execution {
        fln::Outcome::Complete(completed) => completed,
        fln::Outcome::Inconclusive(inconclusive) => {
            return source_failure(
                "inconclusive",
                &format!("{inconclusive:?}"),
                false,
                presentation,
                3,
            );
        }
        fln::Outcome::InternalFault(fault) => {
            return source_failure(
                "internal-fault",
                &format!("{fault:?}"),
                false,
                presentation,
                4,
            );
        }
    };
    if let Some(plan) = module_plan.as_ref() {
        let owners = plan
            .names
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, name)| (name, index))
            .collect::<BTreeMap<_, _>>();
        let mut ordered = Vec::new();
        if ordered
            .try_reserve_exact(completed.source_module_order.len())
            .is_err()
        {
            return source_failure(
                "resource",
                "could not reserve the canonical source module closure",
                false,
                presentation,
                3,
            );
        }
        for name in &completed.source_module_order {
            let Some(index) = owners.get(name).copied() else {
                return source_failure(
                    "internal-fault",
                    "engine returned a source module absent from the input plan",
                    false,
                    presentation,
                    4,
                );
            };
            ordered.push(source_refs[index]);
        }
        if ordered.len() != source_refs.len() {
            return source_failure(
                "internal-fault",
                "engine returned an incomplete canonical source module order",
                false,
                presentation,
                4,
            );
        }
        source_refs = ordered;
    }
    let Some(commands) = completed
        .executions
        .len()
        .checked_add(completed.source_admissions.len())
    else {
        return source_failure(
            "internal-fault",
            "source command count overflowed",
            false,
            presentation,
            4,
        );
    };
    let Some(checked_admissions) = completed
        .source_admissions
        .iter()
        .try_fold(completed.executions.len(), |total, command| {
            total.checked_add(command.admission.admissions.len())
        })
    else {
        return source_failure(
            "internal-fault",
            "source admission count overflowed",
            false,
            presentation,
            4,
        );
    };
    let evaluations = completed.source_evaluation_indices.len();
    let Some(definitions) = commands.checked_sub(evaluations) else {
        return source_failure(
            "internal-fault",
            "source evaluation count exceeded completed command count",
            false,
            presentation,
            4,
        );
    };
    let Some(final_execution) = completed.executions.last() else {
        return source_failure(
            "execution",
            "source contains only declarations; use check-source when no execution is requested",
            true,
            presentation,
            1,
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
            presentation,
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
                    presentation,
                );
            }
            fln::VmExit::Refused { refusal, usage } => {
                return source_terminal(
                    "vm-refusal",
                    &format!("definition batch command {index} was refused: {refusal}"),
                    usage.steps,
                    usage.system_polls,
                    usage.peak_stack_depth,
                    presentation,
                );
            }
        }
    }
    let mut evaluation_results = Vec::new();
    if evaluation_results.try_reserve_exact(evaluations).is_err() {
        return source_failure(
            "resource",
            "could not reserve the source evaluation result table",
            false,
            presentation,
            3,
        );
    }
    let mut previous_evaluation = None;
    for &index in &completed.source_evaluation_indices {
        if index >= commands || previous_evaluation.is_some_and(|previous| previous >= index) {
            return source_failure(
                "internal-fault",
                "engine returned invalid source evaluation command indices",
                false,
                presentation,
                4,
            );
        }
        previous_evaluation = Some(index);
        let Some(execution) = completed.executions.get(index) else {
            return source_failure(
                "internal-fault",
                "engine returned a source evaluation index outside the execution table",
                false,
                presentation,
                4,
            );
        };
        let value = match closed_source_cli_value(&execution.runtime_type, &execution.exit) {
            Ok(Some(value)) => value,
            Ok(None) => {
                return source_failure(
                    "execution",
                    &format!(
                        "evaluation command {index} did not produce a closed Nat, String, or Bool value"
                    ),
                    true,
                    presentation,
                    1,
                );
            }
            Err(error) => {
                return source_failure(
                    "internal-fault",
                    &error.to_string(),
                    false,
                    presentation,
                    4,
                );
            }
        };
        let Some(&command) = completed.source_execution_command_indices.get(index) else {
            return source_failure(
                "internal-fault",
                "source execution omitted its command index",
                false,
                presentation,
                4,
            );
        };
        evaluation_results.push(SourceEvaluationResult { command, value });
    }
    if matches!(presentation, SourcePresentation::Lean) {
        // Lean definitions are declarations, not requests to print or project
        // their zero-argument runtime value. Requiring the final definition to
        // be a closed scalar incorrectly rejects checked function declarations,
        // whose faithful VM result is a closure. All commands have completed
        // above, so evaluation output remains whole-batch atomic.
        return render_lean_evaluation_results(&evaluation_results);
    }
    let base_root = completed.base_logical_root.to_string();
    let result_root = completed.result_logical_root.to_string();
    let final_checker = completed
        .source_admissions
        .last()
        .filter(|admitted| {
            completed
                .source_execution_command_indices
                .last()
                .is_some_and(|index| admitted.command_index > *index)
        })
        .and_then(|command| command.admission.admissions.last())
        .map_or(final_execution.checker, |admission| admission.checker);
    let checker_ground = checker_ground_name(final_checker.ground);
    let fln::VmExit::Returned(returned) = &final_execution.exit else {
        return source_failure(
            "internal-fault",
            "non-returning final execution escaped source batch refusal handling",
            false,
            presentation,
            4,
        );
    };
    let final_value =
        match closed_source_cli_value(&final_execution.runtime_type, &final_execution.exit) {
            Ok(Some(value)) => value,
            Ok(None) => {
                return source_failure(
                    "execution",
                    "final command did not produce a closed Nat, String, or Bool value",
                    true,
                    presentation,
                    1,
                );
            }
            Err(error) => {
                return source_failure(
                    "internal-fault",
                    &error.to_string(),
                    false,
                    presentation,
                    4,
                );
            }
        };
    let encoded_olean_snapshot = if emit_olean_snapshot.is_some() {
        let environment = completed.engine.environment();
        let constant_count = environment.len();
        let mut constants = Vec::new();
        if constants.try_reserve_exact(constant_count).is_err() {
            return source_failure(
                "resource",
                &format!(
                    "could not reserve {constant_count} checked constants for the standalone .olean snapshot"
                ),
                false,
                presentation,
                3,
            );
        }
        constants.extend(
            environment
                .constants()
                .map(|(_, constant)| constant.clone()),
        );
        let Some(version) = fln::OLEAN_ACCEPTED_VERSIONS.first().copied() else {
            return source_failure(
                "internal-fault",
                "the pinned .olean contract exposes no accepted writer version",
                false,
                presentation,
                4,
            );
        };
        let Some(lean_version) = fln::OLEAN_PIN_TAG.strip_prefix('v') else {
            return source_failure(
                "internal-fault",
                "the pinned Lean tag cannot become an .olean version string",
                false,
                presentation,
                4,
            );
        };
        let base_addr = match u64::try_from(fln::OLEAN_REGION_ALIGN)
            .ok()
            .and_then(|alignment| alignment.checked_mul(2))
        {
            Some(base_addr) => base_addr,
            None => {
                return source_failure(
                    "internal-fault",
                    "the pinned .olean region alignment cannot become a base address",
                    false,
                    presentation,
                    4,
                );
            }
        };
        let encoded = match fln::encode_olean_module(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &constants,
                extra_const_names: &[],
            },
            fln::OleanWriteHeader {
                version,
                flags: 1,
                lean_version,
                githash: fln::OLEAN_PIN_COMMIT,
                base_addr,
            },
            fln::OleanWriteBudget::default(),
        ) {
            Ok(encoded) => encoded,
            Err(error) => {
                let (class, authority, exit_code) = olean_write_error_disposition(&error);
                return source_failure(
                    class,
                    &format!("could not encode the standalone .olean snapshot: {error}"),
                    authority,
                    presentation,
                    exit_code,
                );
            }
        };
        Some((encoded.bytes, constant_count))
    } else {
        None
    };
    let emitted_sidecar = if let Some((path, configured_toolchain_image)) = emit_sidecar {
        let loaded_toolchain_image;
        let toolchain_image = match configured_toolchain_image {
            Some(image) => image,
            None => match read_current_toolchain_image() {
                Ok(image) => {
                    loaded_toolchain_image = image;
                    &loaded_toolchain_image
                }
                Err(error) => {
                    return source_failure(
                        "internal-fault",
                        &error.to_string(),
                        false,
                        presentation,
                        4,
                    );
                }
            },
        };
        let sidecar = match fln::build_source_run_flbc_sidecar(
            &source_refs,
            &options,
            toolchain_image,
            &completed,
        ) {
            Ok(sidecar) => sidecar,
            Err(error) => {
                return source_failure("sidecar", &error.to_string(), false, presentation, 1);
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
                presentation,
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
    let emitted_flbc = if let Some(path) = emit_flbc {
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
                presentation,
                exit_code,
            );
        }
        Some((path, final_execution.flbc_artifact.len()))
    } else {
        None
    };
    let emitted_olean_snapshot = if let Some(path) = emit_olean_snapshot {
        let Some((bytes, constant_count)) = encoded_olean_snapshot.as_ref() else {
            return source_failure(
                "internal-fault",
                "standalone .olean snapshot output had no encoded bytes",
                false,
                presentation,
                4,
            );
        };
        if let Err(error) = publish(bytes, path) {
            let state = publication_state(&error);
            let (class, authority, exit_code) = publication_failure_disposition(&error);
            return source_failure(
                class,
                &format!(
                    "could not complete durable standalone .olean snapshot publication to {}: {error}; {state}",
                    path.display()
                ),
                authority,
                presentation,
                exit_code,
            );
        }
        Some((path, bytes.len(), *constant_count))
    } else {
        None
    };
    render_source_success(
        SourceSuccess {
            commands,
            checked_admissions,
            definitions,
            evaluations,
            evaluation_results,
            source_bytes,
            final_value,
            flbc_bytes,
            base_root: &base_root,
            result_root: &result_root,
            checker_schema: final_checker.schema,
            checker_ground,
            emitted_flbc,
            emitted_sidecar,
            emitted_olean_snapshot,
            steps: returned.usage.steps,
            system_polls: returned.usage.system_polls,
            peak_stack_depth: returned.usage.peak_stack_depth,
        },
        presentation,
    )
}

#[cfg(test)]
fn execute_source_bytes_with_publisher<P, E>(
    sources: Vec<Vec<u8>>,
    module_plan: Option<SourceModulePlan>,
    publication: SourcePublication,
    json: bool,
    publish: P,
) -> MultiplexerOutput
where
    P: FnMut(&[u8], &Path) -> Result<(), E>,
    E: SourcePublicationFailure,
{
    execute_source_bytes_with_publisher_and_presentation(
        sources,
        module_plan,
        publication,
        SourcePresentation::Fln { json },
        publish,
    )
}

#[cfg(test)]
fn execute_source_bytes(sources: Vec<Vec<u8>>, json: bool) -> MultiplexerOutput {
    execute_source_bytes_with_publisher(
        sources,
        None,
        SourcePublication::None,
        json,
        fln::publish_file_atomic,
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

#[derive(Debug)]
struct DiscoveredSourceClosure {
    paths: Vec<PathBuf>,
    sources: Vec<Vec<u8>>,
}

fn source_import_relative_path(name: &fln::Name) -> Result<PathBuf, BoundedReadFailure> {
    let components = source_module_components(name).ok_or_else(|| BoundedReadFailure::Input {
        subject: "source import closure",
        detail: format!(
            "import `{}` is not a nonempty string-component module name",
            name.to_display_string()
        ),
    })?;
    let mut path = PathBuf::new();
    for component in components {
        let component_path = Path::new(&component);
        let mut path_components = component_path.components();
        let normalized = matches!(
            (path_components.next(), path_components.next()),
            (Some(std::path::Component::Normal(value)), None) if value == component.as_str()
        );
        if !normalized {
            return Err(BoundedReadFailure::Input {
                subject: "source import closure",
                detail: format!(
                    "import `{}` contains a component that is not one normalized path segment",
                    name.to_display_string()
                ),
            });
        }
        path.push(component);
    }
    path.set_extension("lean");
    Ok(path)
}

fn source_import_candidate_is_file(path: &Path) -> Result<bool, BoundedReadFailure> {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => return Ok(false),
        Err(error) => {
            return Err(BoundedReadFailure::Input {
                subject: "source import closure",
                detail: format!("cannot inspect {}: {error}", path.display()),
            });
        }
    };
    if metadata.file_type().is_symlink() {
        return Err(BoundedReadFailure::Input {
            subject: "source import closure",
            detail: format!("refusing symlink source import {}", path.display()),
        });
    }
    if !metadata.is_file() {
        return Err(BoundedReadFailure::Input {
            subject: "source import closure",
            detail: format!("source import {} is not a regular file", path.display()),
        });
    }
    Ok(true)
}

fn discover_source_root(
    entry: &Path,
    first_import: &fln::Name,
    max_depth: usize,
) -> Result<PathBuf, BoundedReadFailure> {
    let relative = source_import_relative_path(first_import)?;
    let mut selected: Option<PathBuf> = None;
    let parent = entry.parent().unwrap_or_else(|| Path::new(""));
    for root in parent.ancestors().take(max_depth) {
        let candidate = root.join(&relative);
        if source_import_candidate_is_file(&candidate)? {
            if let Some(previous) = selected {
                return Err(BoundedReadFailure::Input {
                    subject: "source import closure",
                    detail: format!(
                        "import `{}` is ambiguous: both {} and {} exist above entry {}",
                        first_import.to_display_string(),
                        previous.join(&relative).display(),
                        candidate.display(),
                        entry.display()
                    ),
                });
            }
            selected = Some(root.to_path_buf());
        }
    }
    selected.ok_or_else(|| BoundedReadFailure::Input {
        subject: "source import closure",
        detail: format!(
            "cannot resolve import `{}` as {} below any bounded ancestor of entry {}",
            first_import.to_display_string(),
            relative.display(),
            entry.display()
        ),
    })
}

fn discover_direct_source_dependencies(
    entry: &Path,
    max_bytes: usize,
) -> Result<Vec<PathBuf>, BoundedReadFailure> {
    let limits = fln::SourceModuleLimits::default();
    let source = read_source_closure_member(entry, 0, max_bytes)?;
    let module =
        fln::partition_source_module(&source).map_err(|error| BoundedReadFailure::Input {
            subject: "source dependency header",
            detail: format!("{}: {error}", entry.display()),
        })?;
    if module.imports.is_empty() {
        return Ok(Vec::new());
    }
    if module.imports.len() > limits.max_imports {
        return Err(BoundedReadFailure::Resource {
            detail: format!(
                "source entry presents {} imports; planning limit is {}",
                module.imports.len(),
                limits.max_imports
            ),
        });
    }
    let first_import = &module.imports[0];
    let first_components =
        source_module_components(first_import).ok_or_else(|| BoundedReadFailure::Input {
            subject: "source dependency header",
            detail: format!(
                "import `{}` is not a nonempty string-component module name",
                first_import.to_display_string()
            ),
        })?;
    if first_components.len() > limits.max_name_depth {
        return Err(BoundedReadFailure::Resource {
            detail: format!(
                "source import `{}` has {} components; planning limit is {}",
                first_import.to_display_string(),
                first_components.len(),
                limits.max_name_depth
            ),
        });
    }
    let root = discover_source_root(entry, first_import, limits.max_name_depth)?;
    let mut dependencies = Vec::new();
    dependencies
        .try_reserve_exact(module.imports.len())
        .map_err(|_| BoundedReadFailure::Allocation {
            subject: "source dependency path table",
            requested: module.imports.len(),
        })?;
    for name in module.imports {
        let components =
            source_module_components(&name).ok_or_else(|| BoundedReadFailure::Input {
                subject: "source dependency header",
                detail: format!(
                    "import `{}` is not a nonempty string-component module name",
                    name.to_display_string()
                ),
            })?;
        if components.len() > limits.max_name_depth {
            return Err(BoundedReadFailure::Resource {
                detail: format!(
                    "source import `{}` has {} components; planning limit is {}",
                    name.to_display_string(),
                    components.len(),
                    limits.max_name_depth
                ),
            });
        }
        let path = root.join(source_import_relative_path(&name)?);
        if !source_import_candidate_is_file(&path)? {
            return Err(BoundedReadFailure::Input {
                subject: "source dependency header",
                detail: format!(
                    "cannot resolve import `{}` below source root {}",
                    name.to_display_string(),
                    root.display()
                ),
            });
        }
        dependencies.push(path);
    }
    Ok(dependencies)
}

fn run_lean_source_dependencies(path: &Path, max_bytes: usize) -> MultiplexerOutput {
    let dependencies = match discover_direct_source_dependencies(path, max_bytes) {
        Ok(dependencies) => dependencies,
        Err(error) => {
            return source_failure(
                error.class(),
                &error.to_string(),
                false,
                SourcePresentation::Lean,
                error.exit_code(),
            );
        }
    };
    let mut rendered_dependencies = Vec::new();
    if rendered_dependencies
        .try_reserve_exact(dependencies.len())
        .is_err()
    {
        return source_failure(
            "resource",
            &format!(
                "could not reserve {} entries for source dependency output",
                dependencies.len()
            ),
            false,
            SourcePresentation::Lean,
            3,
        );
    }
    let mut requested = 0_usize;
    for dependency in &dependencies {
        let Some(rendered) = dependency.to_str() else {
            return source_failure(
                "input",
                &format!(
                    "source dependency path is not valid UTF-8: {}",
                    dependency.display()
                ),
                false,
                SourcePresentation::Lean,
                1,
            );
        };
        let Some(next_requested) = requested
            .checked_add(rendered.len())
            .and_then(|total| total.checked_add(1))
        else {
            return source_failure(
                "resource",
                "source dependency output size exceeded this platform",
                false,
                SourcePresentation::Lean,
                3,
            );
        };
        requested = next_requested;
        rendered_dependencies.push(rendered);
    }
    let mut stdout = String::new();
    if stdout.try_reserve_exact(requested).is_err() {
        return source_failure(
            "resource",
            &format!("could not reserve {requested} bytes for source dependency output"),
            false,
            SourcePresentation::Lean,
            3,
        );
    }
    for dependency in rendered_dependencies {
        stdout.push_str(dependency);
        stdout.push('\n');
    }
    MultiplexerOutput::success(stdout)
}

fn read_source_closure_member(
    path: &Path,
    consumed: usize,
    max_bytes: usize,
) -> Result<Vec<u8>, BoundedReadFailure> {
    let remaining = max_bytes.saturating_sub(consumed);
    match read_bounded(path, remaining, "source import closure") {
        Ok(source) => Ok(source),
        Err(BoundedReadFailure::TooLarge { observed, .. }) => Err(BoundedReadFailure::TooLarge {
            subject: "source import closure",
            observed: consumed.saturating_add(observed),
            limit: max_bytes,
        }),
        Err(BoundedReadFailure::Allocation { requested, .. }) => {
            Err(BoundedReadFailure::Allocation {
                subject: "source import closure",
                requested: consumed.saturating_add(requested),
            })
        }
        Err(error) => Err(error),
    }
}

fn discover_source_closure(
    entry: PathBuf,
    max_bytes: usize,
) -> Result<DiscoveredSourceClosure, BoundedReadFailure> {
    let limits = fln::SourceModuleLimits::default();
    let entry_source = read_source_closure_member(&entry, 0, max_bytes)?;
    let entry_module = match fln::partition_source_module(&entry_source) {
        Ok(module) => module,
        Err(_) => {
            return Ok(DiscoveredSourceClosure {
                paths: vec![entry],
                sources: vec![entry_source],
            });
        }
    };
    if entry_module.imports.is_empty() {
        return Ok(DiscoveredSourceClosure {
            paths: vec![entry],
            sources: vec![entry_source],
        });
    }
    if entry_module.imports.len() > limits.max_imports {
        return Err(BoundedReadFailure::Resource {
            detail: format!(
                "source entry presents {} imports; planning limit is {}",
                entry_module.imports.len(),
                limits.max_imports
            ),
        });
    }
    let first_import = &entry_module.imports[0];
    let first_components =
        source_module_components(first_import).ok_or_else(|| BoundedReadFailure::Input {
            subject: "source import closure",
            detail: format!(
                "import `{}` is not a nonempty string-component module name",
                first_import.to_display_string()
            ),
        })?;
    if first_components.len() > limits.max_name_depth {
        return Err(BoundedReadFailure::Resource {
            detail: format!(
                "source import `{}` has {} components; planning limit is {}",
                first_import.to_display_string(),
                first_components.len(),
                limits.max_name_depth
            ),
        });
    }
    let root = discover_source_root(&entry, first_import, limits.max_name_depth)?;
    let mut pending = BTreeSet::new();
    pending.extend(entry_module.imports.iter().cloned());
    let mut discovered = BTreeMap::<fln::Name, (PathBuf, Vec<u8>)>::new();
    let mut import_presentations = entry_module.imports.len();
    let mut source_bytes = entry_source.len();

    while let Some(name) = pending.pop_first() {
        if discovered.contains_key(&name) {
            continue;
        }
        let components =
            source_module_components(&name).ok_or_else(|| BoundedReadFailure::Input {
                subject: "source import closure",
                detail: format!(
                    "import `{}` is not a nonempty string-component module name",
                    name.to_display_string()
                ),
            })?;
        if components.len() > limits.max_name_depth {
            return Err(BoundedReadFailure::Resource {
                detail: format!(
                    "source import `{}` has {} components; planning limit is {}",
                    name.to_display_string(),
                    components.len(),
                    limits.max_name_depth
                ),
            });
        }
        if discovered.len().saturating_add(1) >= limits.max_modules {
            return Err(BoundedReadFailure::Resource {
                detail: format!(
                    "source import closure contains at least {} modules; planning limit is {}",
                    discovered.len().saturating_add(2),
                    limits.max_modules
                ),
            });
        }
        let relative = source_import_relative_path(&name)?;
        let path = root.join(relative);
        if path == entry {
            continue;
        }
        if !source_import_candidate_is_file(&path)? {
            return Err(BoundedReadFailure::Input {
                subject: "source import closure",
                detail: format!(
                    "cannot resolve import `{}` below source root {}",
                    name.to_display_string(),
                    root.display()
                ),
            });
        }
        let source = read_source_closure_member(&path, source_bytes, max_bytes)?;
        source_bytes = source_bytes.saturating_add(source.len());
        if let Ok(module) = fln::partition_source_module(&source) {
            import_presentations = import_presentations
                .checked_add(module.imports.len())
                .ok_or_else(|| BoundedReadFailure::Resource {
                    detail: "source import presentation count exceeded this platform".to_owned(),
                })?;
            if import_presentations > limits.max_imports {
                return Err(BoundedReadFailure::Resource {
                    detail: format!(
                        "source import closure presents {import_presentations} imports; planning limit is {}",
                        limits.max_imports
                    ),
                });
            }
            pending.extend(module.imports);
        }
        discovered.insert(name, (path, source));
    }

    let mut paths = Vec::new();
    let mut sources = Vec::new();
    let closure_len = discovered.len().saturating_add(1);
    paths
        .try_reserve_exact(closure_len)
        .map_err(|_| BoundedReadFailure::Allocation {
            subject: "source import path table",
            requested: closure_len,
        })?;
    sources
        .try_reserve_exact(closure_len)
        .map_err(|_| BoundedReadFailure::Allocation {
            subject: "source import byte table",
            requested: closure_len,
        })?;
    for (_, (path, source)) in discovered {
        paths.push(path);
        sources.push(source);
    }
    paths.push(entry);
    sources.push(entry_source);
    Ok(DiscoveredSourceClosure { paths, sources })
}

#[derive(Debug)]
struct SourceModulePlan {
    names: Vec<fln::Name>,
    entry: fln::Name,
}

#[derive(Debug)]
enum SourceModulePlanFailure {
    Input(String),
    Resource(String),
}

impl SourceModulePlanFailure {
    fn detail(&self) -> &str {
        match self {
            Self::Input(detail) | Self::Resource(detail) => detail,
        }
    }

    fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::Input(_) => ("input", true, 1),
            Self::Resource(_) => ("resource", false, 3),
        }
    }
}

fn source_module_components(name: &fln::Name) -> Option<Vec<String>> {
    let mut reversed = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        match cursor.leaf_view() {
            fln::LeafView::Str(component) if !component.is_empty() => {
                reversed.push(component.to_owned());
            }
            fln::LeafView::Anonymous | fln::LeafView::Num(_) | fln::LeafView::Str(_) => {
                return None;
            }
        }
        cursor = cursor.parent();
    }
    reversed.reverse();
    (!reversed.is_empty()).then_some(reversed)
}

fn bounded_source_path_components(path: &Path, max_depth: usize) -> Option<Vec<String>> {
    let stem = path.file_stem().and_then(|stem| stem.to_str())?;
    if path.extension().and_then(|extension| extension.to_str()) != Some("lean") {
        return None;
    }
    let mut reversed = Vec::new();
    reversed.push(stem.to_owned());
    let mut parent = path.parent();
    while reversed.len() < max_depth {
        let Some(component) = parent
            .and_then(Path::file_name)
            .and_then(|component| component.to_str())
        else {
            break;
        };
        reversed.push(component.to_owned());
        parent = parent.and_then(Path::parent);
    }
    reversed.reverse();
    Some(reversed)
}

fn source_entry_name(path: &Path) -> Result<fln::Name, String> {
    if path.extension().and_then(|extension| extension.to_str()) != Some("lean") {
        return Err(format!(
            "source module path {} must end in .lean",
            path.display()
        ));
    }
    let stem = path
        .file_stem()
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .ok_or_else(|| {
            format!(
                "source module path {} has no UTF-8 module stem",
                path.display()
            )
        })?;
    if stem.contains('.') {
        return Err(format!(
            "source module path {} has a dotted file stem; use directories for module components",
            path.display()
        ));
    }
    Ok(fln::Name::from_components([stem]))
}

fn derive_source_module_plan(
    paths: &[PathBuf],
    sources: &[Vec<u8>],
) -> Result<Option<SourceModulePlan>, SourceModulePlanFailure> {
    let limits = fln::SourceModuleLimits::default();
    if paths.len() > limits.max_modules {
        return Err(SourceModulePlanFailure::Resource(format!(
            "source set contains {} modules; planning limit is {}",
            paths.len(),
            limits.max_modules
        )));
    }
    let mut imports = BTreeMap::new();
    let mut import_presentations = 0_usize;
    for source in sources {
        if let Ok(module) = fln::partition_source_module(source) {
            import_presentations = import_presentations
                .checked_add(module.imports.len())
                .ok_or_else(|| {
                    SourceModulePlanFailure::Resource(
                        "source import presentation count exceeded this platform".to_owned(),
                    )
                })?;
            if import_presentations > limits.max_imports {
                return Err(SourceModulePlanFailure::Resource(format!(
                    "source set presents {import_presentations} imports; planning limit is {}",
                    limits.max_imports
                )));
            }
            for import in module.imports {
                let components = source_module_components(&import).ok_or_else(|| {
                    SourceModulePlanFailure::Input(format!(
                        "import `{}` is not a nonempty string-component module name",
                        import.to_display_string()
                    ))
                })?;
                if components.len() > limits.max_name_depth {
                    return Err(SourceModulePlanFailure::Resource(format!(
                        "source module name `{}` has {} components; planning limit is {}",
                        import.to_display_string(),
                        components.len(),
                        limits.max_name_depth
                    )));
                }
                imports.entry(components).or_insert(import);
            }
        }
    }
    if imports.is_empty() {
        return Ok(None);
    }

    let depths = imports.keys().map(Vec::len).collect::<BTreeSet<usize>>();
    let mut candidates = imports
        .keys()
        .cloned()
        .map(|components| (components, Vec::new()))
        .collect::<BTreeMap<Vec<String>, Vec<usize>>>();
    for (index, path) in paths.iter().enumerate() {
        let Some(components) = bounded_source_path_components(path, limits.max_name_depth) else {
            continue;
        };
        for depth in &depths {
            if *depth > components.len() {
                continue;
            }
            let suffix = &components[components.len() - depth..];
            if let Some(matches) = candidates.get_mut(suffix)
                && matches.len() < 2
            {
                matches.push(index);
            }
        }
    }

    let mut names: Vec<Option<fln::Name>> = vec![None; paths.len()];
    for (components, import) in imports {
        let matches = candidates
            .get(components.as_slice())
            .map(Vec::as_slice)
            .unwrap_or_default();
        match matches {
            [] => {}
            [index] => {
                if let Some(existing) = &names[*index]
                    && existing != &import
                {
                    return Err(SourceModulePlanFailure::Input(format!(
                        "source path {} ambiguously names both `{}` and `{}`",
                        paths[*index].display(),
                        existing.to_display_string(),
                        import.to_display_string()
                    )));
                }
                if names[*index].is_none() {
                    names[*index] = Some(import);
                }
            }
            _ => {
                return Err(SourceModulePlanFailure::Input(format!(
                    "import `{}` matches more than one supplied source path",
                    import.to_display_string()
                )));
            }
        }
    }
    for (index, path) in paths.iter().enumerate() {
        if names[index].is_none() {
            names[index] = Some(source_entry_name(path).map_err(SourceModulePlanFailure::Input)?);
        }
    }
    let names = names
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| {
            SourceModulePlanFailure::Resource(
                "source module identity table was incomplete".to_owned(),
            )
        })?;
    let entry = names.last().cloned().ok_or_else(|| {
        SourceModulePlanFailure::Input("source module set has no entry path".to_owned())
    })?;
    Ok(Some(SourceModulePlan { names, entry }))
}

fn run_loaded_sources_with_presentation(
    paths: &[PathBuf],
    sources: Vec<Vec<u8>>,
    emit_flbc: Option<PathBuf>,
    emit_sidecar: Option<PathBuf>,
    emit_olean_snapshot: Option<PathBuf>,
    presentation: SourcePresentation,
) -> MultiplexerOutput {
    let publication = match (emit_flbc, emit_sidecar, emit_olean_snapshot) {
        (Some(path), sidecar, None) => SourcePublication::Flbc {
            path,
            sidecar: sidecar.map(|path| SourceSidecarPublication {
                path,
                toolchain_image: None,
            }),
        },
        (None, None, Some(path)) => SourcePublication::OleanSnapshot { path },
        (None, None, None) => SourcePublication::None,
        _ => {
            return source_failure(
                "internal-fault",
                "mutually exclusive source publication options reached execution together",
                false,
                presentation,
                4,
            );
        }
    };
    let module_plan = match derive_source_module_plan(paths, &sources) {
        Ok(plan) => plan,
        Err(error) => {
            let (class, authority, exit_code) = error.disposition();
            return source_failure(class, error.detail(), authority, presentation, exit_code);
        }
    };
    let worker = match std::thread::Builder::new()
        .name("fln-source-run".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
        .spawn(move || {
            execute_source_bytes_with_publisher_and_presentation(
                sources,
                module_plan,
                publication,
                presentation,
                fln::publish_file_atomic_new,
            )
        }) {
        Ok(worker) => worker,
        Err(error) => {
            return source_failure(
                "internal-fault",
                &format!("could not start bounded kernel worker: {error}"),
                false,
                presentation,
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
            presentation,
            4,
        ),
    }
}

fn run_sources_with_presentation(
    paths: &[PathBuf],
    max_bytes: usize,
    emit_flbc: Option<PathBuf>,
    emit_sidecar: Option<PathBuf>,
    emit_olean_snapshot: Option<PathBuf>,
    presentation: SourcePresentation,
) -> MultiplexerOutput {
    if let [entry] = paths {
        let discovered = match discover_source_closure(entry.clone(), max_bytes) {
            Ok(discovered) => discovered,
            Err(error) => {
                return source_failure(
                    error.class(),
                    &error.to_string(),
                    false,
                    presentation,
                    error.exit_code(),
                );
            }
        };
        for output in [
            emit_flbc.as_deref(),
            emit_sidecar.as_deref(),
            emit_olean_snapshot.as_deref(),
        ]
        .into_iter()
        .flatten()
        {
            if let Some(source) = discovered
                .paths
                .iter()
                .find(|source| output_paths_alias(output, source))
            {
                return source_failure(
                    "output",
                    &format!(
                        "output path {} aliases discovered source input {}",
                        output.display(),
                        source.display()
                    ),
                    true,
                    presentation,
                    1,
                );
            }
        }
        let DiscoveredSourceClosure { paths, sources } = discovered;
        return run_loaded_sources_with_presentation(
            &paths,
            sources,
            emit_flbc,
            emit_sidecar,
            emit_olean_snapshot,
            presentation,
        );
    }
    let sources = match read_source_batch(paths, max_bytes) {
        Ok(sources) => sources,
        Err(error) => {
            return source_failure(
                error.class(),
                &error.to_string(),
                false,
                presentation,
                error.exit_code(),
            );
        }
    };
    run_loaded_sources_with_presentation(
        paths,
        sources,
        emit_flbc,
        emit_sidecar,
        emit_olean_snapshot,
        presentation,
    )
}

fn run_lean_source(path: PathBuf, max_bytes: usize) -> MultiplexerOutput {
    let discovered = match discover_source_closure(path, max_bytes) {
        Ok(discovered) => discovered,
        Err(error) => {
            return source_failure(
                error.class(),
                &error.to_string(),
                false,
                SourcePresentation::Lean,
                error.exit_code(),
            );
        }
    };
    run_loaded_sources_with_presentation(
        &discovered.paths,
        discovered.sources,
        None,
        None,
        None,
        SourcePresentation::Lean,
    )
}

fn run_lean_stdin(input: &mut dyn Read, max_bytes: usize) -> MultiplexerOutput {
    let source = match read_bounded_from(input, max_bytes, "standard input source") {
        Ok(source) => source,
        Err(error) => {
            return source_failure(
                error.class(),
                &error.to_string(),
                false,
                SourcePresentation::Lean,
                error.exit_code(),
            );
        }
    };
    if let Ok(module) = fln::partition_source_module(&source)
        && !module.imports.is_empty()
    {
        return source_failure(
            "input",
            "bounded --stdin execution does not resolve imports; provide a local source path instead",
            false,
            SourcePresentation::Lean,
            1,
        );
    }
    let paths = [PathBuf::from("stdin.lean")];
    run_loaded_sources_with_presentation(
        &paths,
        vec![source],
        None,
        None,
        None,
        SourcePresentation::Lean,
    )
}

fn run_sources(
    paths: &[PathBuf],
    max_bytes: usize,
    json: bool,
    emit_flbc: Option<PathBuf>,
    emit_sidecar: Option<PathBuf>,
    emit_olean_snapshot: Option<PathBuf>,
) -> MultiplexerOutput {
    run_sources_with_presentation(
        paths,
        max_bytes,
        emit_flbc,
        emit_sidecar,
        emit_olean_snapshot,
        SourcePresentation::Fln { json },
    )
}

/// Run the shared native proof-checking LSP session on process standard streams.
pub fn serve_lsp() -> MultiplexerOutput {
    use std::io::{BufReader, BufWriter, Write};
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut reader = BufReader::new(stdin.lock());
    let mut writer = BufWriter::new(stdout.lock());

    let mut checker = source_check::lsp::Checker::new();
    let outcome = fln_server::dispatch::serve_workspace(&mut reader, &mut writer, &mut checker);
    if let Err(error) = writer.flush() {
        return MultiplexerOutput::failure(
            format!("fln serve-lsp: transport flush error: {error}\n"),
            1,
        );
    }
    match outcome {
        Ok(outcome) => {
            if outcome.clean {
                MultiplexerOutput::success(String::new())
            } else {
                MultiplexerOutput::failure(
                    "fln serve-lsp: server exited without clean shutdown\n".to_owned(),
                    1,
                )
            }
        }
        Err(error) => {
            MultiplexerOutput::failure(format!("fln serve-lsp: transport error: {error}\n"), 1)
        }
    }
}

/// Convert a byte offset in the UTF-8 document into a Lean 1-based-line,
/// 0-based-codepoint-column position, or `None` when the source is not valid
/// UTF-8, or the offset is out of range or not on a character boundary — in
/// which case a codepoint column cannot be trusted and the caller falls back to
/// the file-level position.
fn source_position_at(source: &[u8], offset: usize) -> Option<fln_core::pos::Position> {
    let text = std::str::from_utf8(source).ok()?;
    if offset > text.len() || !text.is_char_boundary(offset) {
        return None;
    }
    Some(fln_core::pos::FileMap::of_string(text).to_position(fln_core::pos::RawPos::new(offset)))
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
            roots,
            max_bytes,
            json,
            receipts,
            continue_on_failure,
            progress,
            jobs,
        }) => check_olean(
            &roots,
            max_bytes,
            json,
            receipts.as_deref(),
            continue_on_failure,
            progress,
            jobs,
        ),
        Ok(MultiplexerCommand::Identity { json }) => render_identity(json),
        Ok(MultiplexerCommand::AuditTcb {
            path,
            max_bytes,
            json,
        }) => audit_tcb(&path, max_bytes, json),
        Ok(MultiplexerCommand::WhyTrusts {
            name,
            path,
            max_bytes,
            max_nodes,
            json,
        }) => why_trusts(&name, &path, max_bytes, max_nodes, json),
        Ok(MultiplexerCommand::SourceCheck {
            paths,
            max_bytes,
            json,
        }) => source_check::run(paths, max_bytes, json),
        Ok(MultiplexerCommand::SourceRun {
            paths,
            max_bytes,
            json,
            emit_flbc,
            emit_sidecar,
            emit_olean_snapshot,
        }) => run_sources(
            &paths,
            max_bytes,
            json,
            emit_flbc,
            emit_sidecar,
            emit_olean_snapshot,
        ),
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
            constants,
        }) => inspect_olean(&path, max_bytes, json, constants),
        Ok(MultiplexerCommand::OleanDiff {
            left,
            right,
            max_bytes,
            json,
        }) => diff_olean(&left, &right, max_bytes, json),
        Ok(MultiplexerCommand::OleanVerifyRebuild {
            path,
            max_bytes,
            json,
        }) => verify_olean_rebuild(&path, max_bytes, json),
        Ok(MultiplexerCommand::IleanInspect {
            path,
            max_bytes,
            json,
        }) => inspect_ilean(&path, max_bytes, json),
        Ok(MultiplexerCommand::ServeLsp) => serve_lsp(),
        Ok(MultiplexerCommand::Goals {
            path,
            line,
            col,
            offset,
            max_bytes,
            json,
        }) => source_check::run_goals(path, line, col, offset, max_bytes, json),
        Ok(MultiplexerCommand::CapabilityNotice { command, json }) => {
            render_capability_notice(&command, json)
        }
        Ok(MultiplexerCommand::VerifyCapsule {
            path,
            max_bytes,
            json,
        }) => verify_capsule(&path, max_bytes, json),
        Ok(MultiplexerCommand::BuildExplain {
            target,
            dir,
            faithful_invalidation,
            json,
        }) => run_build_explain(
            target.as_deref(),
            dir.as_deref(),
            faithful_invalidation,
            json,
        ),
        Err(error) => MultiplexerOutput::failure(format!("fln: {error}\n\n{USAGE}"), 2),
    }
}

fn run_build_explain(
    target: Option<&str>,
    dir: Option<&Path>,
    faithful_invalidation: bool,
    json: bool,
) -> MultiplexerOutput {
    let base_dir = dir.unwrap_or_else(|| Path::new("."));
    match fln_lake::explain_build(base_dir, target, faithful_invalidation) {
        Ok(report) => {
            if json {
                let changed_json = report
                    .changed_inputs
                    .iter()
                    .map(|s| format!("\"{s}\""))
                    .collect::<Vec<_>>()
                    .join(",");
                let barriers_json = report
                    .opaque_barriers
                    .iter()
                    .map(|s| format!("\"{s}\""))
                    .collect::<Vec<_>>()
                    .join(",");
                MultiplexerOutput::success(format!(
                    "{{\"schema\":\"fln.build-explain/1\",\"status\":\"success\",\"package\":\"{}\",\"target\":\"{}\",\"reference_decision\":\"{}\",\"native_decision\":\"{}\",\"delta\":\"{}\",\"changed_inputs\":[{changed_json}],\"opaque_barriers\":[{barriers_json}],\"cache_outcome\":\"{}\"}}\n",
                    report.package,
                    report.target,
                    report.reference_decision,
                    report.native_decision,
                    report.delta,
                    report.cache_outcome,
                ))
            } else {
                let changed_str = if report.changed_inputs.is_empty() {
                    "(none)".to_owned()
                } else {
                    report.changed_inputs.join(", ")
                };
                let barriers_str = if report.opaque_barriers.is_empty() {
                    "(none)".to_owned()
                } else {
                    report.opaque_barriers.join(", ")
                };
                MultiplexerOutput::success(format!(
                    "Target: {} (package: {})\n  Reference decision: {}\n  Native decision:    {}\n  Delta:              {}\n  Changed inputs:     {}\n  Opaque barriers:    {}\n  Cache outcome:      {}\n",
                    report.target,
                    report.package,
                    report.reference_decision,
                    report.native_decision,
                    report.delta,
                    changed_str,
                    barriers_str,
                    report.cache_outcome,
                ))
            }
        }
        Err(err) => {
            let unsupported = matches!(
                err,
                fln_lake::LakeExplainError::Unavailable
                    | fln_lake::LakeExplainError::Discovery(
                        fln_lake::LakeDiscoveryError::LeanConfigUnsupported(_)
                    )
            );
            let mut output =
                lake_operation_failure("fln.build-explain/1", &err.to_string(), unsupported, json);
            // `build explain` is an `fln` verb, so a missing capability takes the
            // multiplexer's documented exit 5, never the 1 that means "rejected
            // or failed". The `lake` personality keeps Lake's own exit 1.
            if unsupported {
                output.exit_code = 5;
            }
            output
        }
    }
}

fn lake_operation_failure(
    schema: &str,
    detail: &str,
    unsupported: bool,
    json: bool,
) -> MultiplexerOutput {
    let stderr = if json {
        format!(
            "{{\"schema\":{},\"status\":{},\"detail\":{}}}\n",
            json_string(schema),
            json_string(if unsupported { "unsupported" } else { "error" }),
            json_string(detail),
        )
    } else {
        format!("{detail}\n")
    };
    MultiplexerOutput::failure(stderr, 1)
}

fn run_lean_with_optional_input(
    arguments: impl IntoIterator<Item = OsString>,
    input: Option<&mut dyn Read>,
) -> MultiplexerOutput {
    match parse_lean_command(arguments) {
        Ok(LeanCommand::Help) => MultiplexerOutput::success(LEAN_USAGE.to_owned()),
        Ok(LeanCommand::Version) => MultiplexerOutput::success(format!(
            "Lean (version {}, FrankenLean bounded native source personality {})\n",
            fln::OLEAN_PIN_TAG
                .strip_prefix('v')
                .unwrap_or(fln::OLEAN_PIN_TAG),
            env!("CARGO_PKG_VERSION")
        )),
        Ok(LeanCommand::ShortVersion) => MultiplexerOutput::success(format!(
            "{}\n",
            fln::OLEAN_PIN_TAG
                .strip_prefix('v')
                .unwrap_or(fln::OLEAN_PIN_TAG)
        )),
        Ok(LeanCommand::GitHash) => {
            MultiplexerOutput::success(format!("{}\n", fln::OLEAN_PIN_COMMIT))
        }
        Ok(LeanCommand::Features) => MultiplexerOutput::success("[]\n".to_owned()),
        Ok(LeanCommand::PrintPrefix) => lean_installation_path_output(|paths| paths.prefix),
        Ok(LeanCommand::PrintLibdir) => lean_installation_path_output(|paths| paths.libdir),
        Ok(LeanCommand::Server) => serve_lsp(),
        Ok(LeanCommand::Stdin { max_bytes }) => match input {
            Some(input) => run_lean_stdin(input, max_bytes),
            None => MultiplexerOutput::failure(
                format!(
                    "lean: --stdin requires an explicit input handle; use run_lean_with_input\n\n{LEAN_USAGE}"
                ),
                2,
            ),
        },
        Ok(LeanCommand::SourceDependencies { path, max_bytes }) => {
            run_lean_source_dependencies(&path, max_bytes)
        }
        Ok(LeanCommand::Source { path, max_bytes }) => run_lean_source(path, max_bytes),
        Err(error) => MultiplexerOutput::failure(format!("lean: {error}\n\n{LEAN_USAGE}"), 2),
    }
}

/// Run FrankenLean's bounded native `lean` personality without touching
/// process-global arguments or streams.
///
/// This is intentionally a presentation adapter over the same source pipeline
/// as [`run`]'s `fln run` command. It does not widen the supported source
/// language, bypass either checker, or emulate unsupported Reference options.
/// The `--stdin` mode is refused here because this entry point owns no input
/// handle; callers using that mode must call [`run_lean_with_input`].
pub fn run_lean(arguments: impl IntoIterator<Item = OsString>) -> MultiplexerOutput {
    run_lean_with_optional_input(arguments, None)
}

/// Run the bounded native `lean` personality with an explicit standard-input
/// source. The reader is touched only when `arguments` selects `--stdin`.
pub fn run_lean_with_input(
    arguments: impl IntoIterator<Item = OsString>,
    input: &mut dyn Read,
) -> MultiplexerOutput {
    run_lean_with_optional_input(arguments, Some(input))
}

const LEANC_USAGE: &str = concat!(
    "Usage: leanc [options] <files>...\n",
    "\n",
    "FrankenLean C-driver personality (plan §17.1). Drives the host C compiler\n",
    "for `--backend c` artifact emission.\n",
    "\n",
    "Options:\n",
    "  --help       display this help and exit\n",
    "  --version    display compiler version information\n",
    "  -v           display the programs invoked by the compiler\n",
);

/// Run FrankenLean's bounded native `leanc` personality (plan §17.1).
///
/// Drives the host C compiler for `--backend c` artifact emission, or explains
/// its absence when unavailable (constitutional Rule D2).
pub fn run_leanc(arguments: impl IntoIterator<Item = OsString>) -> MultiplexerOutput {
    let arguments: Vec<OsString> = arguments.into_iter().collect();
    if arguments.is_empty() {
        return MultiplexerOutput::failure("leanc: no input files\n".to_owned(), 1);
    }
    for arg in &arguments {
        if arg == "--help" || arg == "-h" {
            return MultiplexerOutput::success(LEANC_USAGE.to_owned());
        }
        if arg == "--version" {
            return MultiplexerOutput::success(format!(
                "leanc (FrankenLean bounded native C-driver personality {}, Lean version {})\n",
                env!("CARGO_PKG_VERSION"),
                fln::OLEAN_PIN_TAG
                    .strip_prefix('v')
                    .unwrap_or(fln::OLEAN_PIN_TAG),
            ));
        }
        if arg == "--print-cflags" {
            let executable = match std::env::current_exe() {
                Ok(executable) => executable,
                Err(error) => {
                    return MultiplexerOutput::failure(
                        format!(
                            "leanc: installation: cannot locate the running executable: {error}\n"
                        ),
                        1,
                    );
                }
            };
            let paths = match derive_lean_installation_paths(&executable) {
                Ok(paths) => paths,
                Err(error) => {
                    return MultiplexerOutput::failure(
                        format!("leanc: installation: {error}\n"),
                        1,
                    );
                }
            };
            return MultiplexerOutput::success(leanc_cflags(&paths.prefix));
        }
        if arg == "--print-ldflags" {
            let executable = match std::env::current_exe() {
                Ok(executable) => executable,
                Err(error) => {
                    return MultiplexerOutput::failure(
                        format!(
                            "leanc: installation: cannot locate the running executable: {error}\n"
                        ),
                        1,
                    );
                }
            };
            let paths = match derive_lean_installation_paths(&executable) {
                Ok(paths) => paths,
                Err(error) => {
                    return MultiplexerOutput::failure(
                        format!("leanc: installation: {error}\n"),
                        1,
                    );
                }
            };
            return MultiplexerOutput::success(leanc_ldflags(&paths.prefix));
        }
    }
    for arg in &arguments {
        let s = arg.to_string_lossy();
        if s.starts_with("--fln-census-unknown") || s.starts_with("--unknown") {
            return MultiplexerOutput::failure(
                format!("leanc: unrecognized command-line option '{s}'\n"),
                1,
            );
        }
    }
    let cc = std::env::var("LEAN_CC").unwrap_or_else(|_| "cc".to_owned());
    match std::process::Command::new(&cc).args(&arguments).output() {
        Ok(output) => MultiplexerOutput {
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            exit_code: output.status.code().unwrap_or(1) as u8,
        },
        Err(_) => MultiplexerOutput::failure(
            format!(
                "leanc: host C compiler '{cc}' is unavailable (D2 cc requirement; plan §17.1)\n"
            ),
            1,
        ),
    }
}

fn leanc_cflags(prefix: &Path) -> String {
    #[cfg(target_os = "linux")]
    {
        format!(
            "-I {}/include -fstack-clash-protection -fPIC -fvisibility=hidden\n",
            prefix.display()
        )
    }
    #[cfg(target_os = "macos")]
    {
        format!(
            "-I {}/include -fPIC -fvisibility=hidden\n",
            prefix.display()
        )
    }
    #[cfg(windows)]
    {
        format!("-I {}/include\n", prefix.display())
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
    {
        format!("-I {}/include -fPIC\n", prefix.display())
    }
}

fn leanc_ldflags(prefix: &Path) -> String {
    let cflags = leanc_cflags(prefix);
    let cflags_trimmed = cflags.trim_end_matches(['\n', '\r']);
    #[cfg(target_os = "linux")]
    {
        format!(
            "{cflags_trimmed} -L {}/lib/lean -Wl,--start-group -lleancpp -lLean -Wl,--end-group -Wl,--start-group -lInit -lleanrt -Wl,--end-group -Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic -lLake -Wl,--as-needed -lgmp -Wl,--no-as-needed -lm -ldl -pthread\n",
            prefix.display()
        )
    }
    #[cfg(target_os = "macos")]
    {
        format!(
            "{cflags_trimmed} -L {}/lib/lean -lleancpp -lLean -lInit -lleanrt -lc++ -lLake -lgmp -lm -ldl -pthread\n",
            prefix.display()
        )
    }
    #[cfg(windows)]
    {
        format!(
            "{cflags_trimmed} -L {}/lib/lean -lleancpp -lLean -lInit -lleanrt -lLake -lgmp -lm -ldl -Wl,--whole-archive -lleanmanifest -Wl,--no-whole-archive\n",
            prefix.display()
        )
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
    {
        format!(
            "{cflags_trimmed} -L {}/lib/lean -lleancpp -lLean -lInit -lleanrt -lLake -lgmp -lm -ldl -pthread\n",
            prefix.display()
        )
    }
}

const LAKE_USAGE: &str = concat!(
    "Lake version 5.0.0-src (Lean version 4.32.0, FrankenLean personality)\n",
    "\n",
    "USAGE:\n",
    "  lake [OPTIONS] <COMMAND>\n",
    "\n",
    "COMMANDS:\n",
    "  new <name> <temp>     create a Lean package in a new directory\n",
    "  init <name> <temp>    create a Lean package in the current directory\n",
    "  build <targets>...    build targets\n",
    "  query <targets>...    build targets and output results\n",
    "  exe <exe> <args>...   build an exe and run it in Lake's environment\n",
    "  check-build           check if any default build targets are configured\n",
    "  test                  test the package using the configured test driver\n",
    "  check-test            check if there is a properly configured test driver\n",
    "  lint                  lint the package\n",
    "  check-lint            check if there is a properly configured lint driver\n",
    "  clean                 remove build outputs\n",
    "  shake                 minimize imports in source files\n",
    "  env <cmd> <args>...   execute a command in Lake's environment\n",
    "  lean <file>           elaborate a Lean file in Lake's context\n",
    "  update                update dependencies and save them to the manifest\n",
    "  pack                  pack build artifacts into an archive for distribution\n",
    "  unpack                unpack build artifacts from an distributed archive\n",
    "  upload <tag>          upload build artifacts to a GitHub release\n",
    "  cache                 manage the Lake cache\n",
    "  script                manage and run workspace scripts\n",
    "  scripts               shorthand for `lake script list`\n",
    "  run <script>          shorthand for `lake script run`\n",
    "  translate-config      change language of the package configuration\n",
    "  serve                 start the Lean language server\n",
    "\n",
    "BASIC OPTIONS:\n",
    "  --version             print version and exit\n",
    "  --help, -h            print help of the program or a command and exit\n",
    "  --dir, -d=file        use the package configuration in a specific directory\n",
    "  --file, -f=file       use a specific file for the package configuration\n",
    "  -K key[=value]        set the configuration file option named key\n",
    "  --old                 only rebuild modified modules (ignore transitive deps)\n",
    "  --rehash, -H          hash all files for traces (do not trust `.hash` files)\n",
    "  --update              update dependencies on load (e.g., before a build)\n",
    "  --packages=file       JSON file of package entries that override the manifest\n",
    "  --reconfigure, -R     elaborate configuration files instead of using OLeans\n",
    "  --keep-toolchain      do not update toolchain on workspace update\n",
    "  --allow-empty         accept bare builds with no default targets configured\n",
    "  --no-build            exit immediately if a build target is not up-to-date\n",
    "  --no-cache            build packages locally; do not download build caches\n",
    "  --try-cache           attempt to download build caches for supported packages\n",
    "  --json, -J            output JSON-formatted results (in `lake query`)\n",
    "  --text                output results as plain text (in `lake query`)\n",
    "\n",
    "OUTPUT OPTIONS:\n",
    "  --quiet, -q           hide informational logs and the progress indicator\n",
    "  --verbose, -v         show trace logs (command invocations) and built targets\n",
    "  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output\n",
    "  --log-level=lv        minimum log level to output on success\n",
    "                        (levels: trace, info, warning, error)\n",
    "  --fail-level=lv       minimum log level to fail a build (default: error)\n",
    "  --iofail              fail build if any I/O or other info is logged\n",
    "                        (same as --fail-level=info)\n",
    "  --wfail               fail build if warnings are logged\n",
    "                        (same as --fail-level=warning)\n",
    "\n",
    "\n",
    "See `lake help <command>` for more information on a specific command.\n",
    "\nFrankenLean currently has no Lake artifact compiler or build-provenance\n",
    "backend. `build` fails without writing artifacts; `check-build` only\n",
    "checks default-target presence in supported TOML configuration.\n",
);

const LAKE_HELP_BUILD: &str = concat!(
    "Build targets\n",
    "\n",
    "USAGE:\n",
    "  lake build [<targets>...] [-o <mappings>]\n",
    "\n",
    "A target is specified with a string of the form:\n",
    "\n",
    "  [@[<package>]/][<target>|[+]<module>][:<facet>]\n",
    "\n",
    "See `lake help <command>` for more information on a specific command.\n",
    "\nArtifact compilation is currently unavailable in FrankenLean; this command\n",
    "fails without creating or replacing build outputs.\n",
);

const LAKE_HELP_QUERY: &str = concat!(
    "Build targets and output results\n",
    "\n",
    "USAGE:\n",
    "  lake query [<targets>...]\n",
    "\n",
    "Builds a set of targets, reporting progress on standard error and outputting\n",
    "the results on standard out. Target results are output in the same order they\n",
    "are listed and end with a newline. If `--json` is set, results are formatted as\n",
    "JSON. Otherwise, they are printed as raw strings. Targets which do not have\n",
    "output configured will be printed as an empty string or `null`.\n",
    "\n",
    "See `lake help build` for information on and examples of targets.\n",
);

const LAKE_HELP_ENV: &str = concat!(
    "Execute a command in Lake's environment\n",
    "\n",
    "USAGE:\n",
    "  lake env [<cmd>] [<args>...]\n",
    "\n",
    "Spawns a new process executing `cmd` with the given `args` and with\n",
    "the environment set based on the detected Lean/Lake installations and\n",
    "the workspace configuration (if it exists).\n",
);

/// Run FrankenLean's bounded native `lake` personality (plan §17.1).
pub fn run_lake(arguments: impl IntoIterator<Item = OsString>) -> MultiplexerOutput {
    let arguments: Vec<OsString> = arguments.into_iter().collect();
    if arguments.is_empty() {
        return MultiplexerOutput::success(LAKE_USAGE.to_owned());
    }
    let mut dir: Option<PathBuf> = None;
    let mut iter = arguments.into_iter();
    let mut command: Option<String> = None;
    let mut command_args: Vec<String> = Vec::new();
    let mut is_json = false;

    while let Some(arg) = iter.next() {
        let s = arg.to_string_lossy();
        if s == "--help" || s == "-h" {
            return MultiplexerOutput::success(LAKE_USAGE.to_owned());
        }
        if s == "--version" {
            return MultiplexerOutput::success(format!(
                "Lake version 5.0.0-src (Lean version {}, FrankenLean personality {})\n",
                fln::OLEAN_PIN_TAG
                    .strip_prefix('v')
                    .unwrap_or(fln::OLEAN_PIN_TAG),
                env!("CARGO_PKG_VERSION"),
            ));
        }
        if s == "--json" || s == "-J" {
            is_json = true;
            continue;
        }
        if s == "--dir" || s == "-d" {
            let Some(dir_val) = iter.next() else {
                return MultiplexerOutput::failure(
                    "error: missing directory value\n".to_owned(),
                    1,
                );
            };
            dir = Some(PathBuf::from(dir_val));
            continue;
        }
        if let Some(rest) = s.strip_prefix("--dir=") {
            dir = Some(PathBuf::from(rest));
            continue;
        }
        if let Some(rest) = s.strip_prefix("-d=") {
            dir = Some(PathBuf::from(rest));
            continue;
        }
        if s.starts_with("--fln-census-unknown") || s.starts_with("--unknown") {
            return MultiplexerOutput::failure(format!("error: unknown option '{s}'\n"), 1);
        }
        if s.starts_with('-') {
            continue;
        }
        if command.is_none() {
            command = Some(s.into_owned());
        } else {
            command_args.push(s.into_owned());
        }
    }

    if let Some(d) = &dir
        && !d.exists()
    {
        return MultiplexerOutput::failure(
            format!(
                "error: package directory '{}' does not exist\n",
                d.display()
            ),
            1,
        );
    }

    let Some(cmd) = command else {
        return MultiplexerOutput::success(LAKE_USAGE.to_owned());
    };

    if cmd == "help" {
        if let Some(sub) = command_args.first() {
            match sub.as_str() {
                "build" => return MultiplexerOutput::success(LAKE_HELP_BUILD.to_owned()),
                "query" => return MultiplexerOutput::success(LAKE_HELP_QUERY.to_owned()),
                "env" => return MultiplexerOutput::success(LAKE_HELP_ENV.to_owned()),
                _ => return MultiplexerOutput::success(format!("Help for lake {sub}\n")),
            }
        }
        return MultiplexerOutput::success(LAKE_USAGE.to_owned());
    }

    match cmd.as_str() {
        "serve" => serve_lsp(),
        "build" => {
            let target_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            match fln_lake::build_package(&target_dir, &command_args) {
                Ok(report) => {
                    if is_json {
                        let targets_json = report
                            .targets
                            .iter()
                            .map(|s| format!("\"{s}\""))
                            .collect::<Vec<_>>()
                            .join(",");
                        MultiplexerOutput::success(format!(
                            "{{\"schema\":\"fln.lake-build/1\",\"status\":\"success\",\"package\":\"{}\",\"targets\":[{targets_json}],\"targets_built\":{},\"targets_cached\":{}}}\n",
                            report.package, report.targets_built, report.targets_cached
                        ))
                    } else {
                        MultiplexerOutput::success(format!(
                            "Built {} ({} built, {} cached)\n",
                            report.package, report.targets_built, report.targets_cached
                        ))
                    }
                }
                Err(fln_lake::LakeBuildError::Discovery(
                    fln_lake::LakeDiscoveryError::NotFound(p),
                )) => MultiplexerOutput::failure(
                    format!(
                        "error: no such file or directory (error code: 2)\n  file: {}\n",
                        p.join("lakefile.lean").display()
                    ),
                    1,
                ),
                Err(err) => lake_operation_failure(
                    "fln.lake-build/1",
                    &err.to_string(),
                    matches!(
                        err,
                        fln_lake::LakeBuildError::Unavailable
                            | fln_lake::LakeBuildError::Discovery(
                                fln_lake::LakeDiscoveryError::LeanConfigUnsupported(_)
                            )
                    ),
                    is_json,
                ),
            }
        }
        "clean" => {
            let target_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            match fln_lake::clean(&target_dir) {
                Ok(report) => {
                    if is_json {
                        MultiplexerOutput::success(format!(
                            "{{\"schema\":\"fln.lake-clean/1\",\"status\":\"success\",\"dir\":\"{}\",\"build_dir_removed\":{}}}\n",
                            target_dir.display(),
                            report.build_dir_removed
                        ))
                    } else {
                        MultiplexerOutput::success(String::new())
                    }
                }
                Err(err) => {
                    if is_json {
                        MultiplexerOutput::failure(
                            format!(
                                "{{\"schema\":\"fln.lake-clean/1\",\"status\":\"error\",\"error\":\"{err}\"}}\n"
                            ),
                            1,
                        )
                    } else {
                        MultiplexerOutput::failure(format!("{err}\n"), 1)
                    }
                }
            }
        }
        "init" => {
            let target_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            let pkg_name = if let Some(name) = command_args.first() {
                name.clone()
            } else {
                target_dir
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or("pkg")
                    .to_owned()
            };
            let template = command_args.get(1).map(|s| s.as_str());
            match fln_lake::init_package(
                &target_dir,
                &pkg_name,
                template,
                fln_lake::LakeConfigFormat::Toml,
            ) {
                Ok(()) => {
                    if is_json {
                        MultiplexerOutput::success(format!(
                            "{{\"schema\":\"fln.lake-init/1\",\"status\":\"success\",\"package\":\"{pkg_name}\",\"dir\":\"{}\"}}\n",
                            target_dir.display()
                        ))
                    } else {
                        MultiplexerOutput::success(String::new())
                    }
                }
                Err(err) => {
                    if is_json {
                        MultiplexerOutput::failure(
                            format!(
                                "{{\"schema\":\"fln.lake-init/1\",\"status\":\"error\",\"error\":\"{err}\"}}\n"
                            ),
                            1,
                        )
                    } else {
                        MultiplexerOutput::failure(format!("{err}\n"), 1)
                    }
                }
            }
        }
        "new" => {
            let parent_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            let Some(pkg_name) = command_args.first() else {
                return MultiplexerOutput::failure(
                    "error: missing package name for lake new\n".to_owned(),
                    1,
                );
            };
            let template = command_args.get(1).map(|s| s.as_str());
            match fln_lake::new_package(
                &parent_dir,
                pkg_name,
                template,
                fln_lake::LakeConfigFormat::Toml,
            ) {
                Ok(created_dir) => {
                    if is_json {
                        MultiplexerOutput::success(format!(
                            "{{\"schema\":\"fln.lake-new/1\",\"status\":\"success\",\"package\":\"{pkg_name}\",\"dir\":\"{}\"}}\n",
                            created_dir.display()
                        ))
                    } else {
                        MultiplexerOutput::success(String::new())
                    }
                }
                Err(err) => {
                    if is_json {
                        MultiplexerOutput::failure(
                            format!(
                                "{{\"schema\":\"fln.lake-new/1\",\"status\":\"error\",\"error\":\"{err}\"}}\n"
                            ),
                            1,
                        )
                    } else {
                        MultiplexerOutput::failure(format!("{err}\n"), 1)
                    }
                }
            }
        }
        "update" => {
            let target_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            match fln_lake::update_manifest(&target_dir) {
                Ok(manifest) => {
                    if is_json {
                        MultiplexerOutput::success(format!(
                            "{{\"schema\":\"fln.lake-update/1\",\"status\":\"success\",\"package\":\"{}\",\"packages_count\":{}}}\n",
                            manifest.name,
                            manifest.packages.len()
                        ))
                    } else {
                        MultiplexerOutput::success(String::new())
                    }
                }
                Err(err) => {
                    if is_json {
                        MultiplexerOutput::failure(
                            format!(
                                "{{\"schema\":\"fln.lake-update/1\",\"status\":\"error\",\"error\":\"{err}\"}}\n"
                            ),
                            1,
                        )
                    } else {
                        MultiplexerOutput::failure(format!("{err}\n"), 1)
                    }
                }
            }
        }
        "exe" => {
            let Some(target) = command_args.first() else {
                return MultiplexerOutput::failure(
                    "error: missing executable target\n".to_owned(),
                    1,
                );
            };
            let target_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            match fln_lake::LakeConfig::discover(&target_dir) {
                Ok(_cfg) => MultiplexerOutput::failure(
                    format!(
                        "lake exe {target}: executable execution requires Golem G2 execution pipeline (plan §13.3, §17.1)\n"
                    ),
                    1,
                ),
                Err(fln_lake::LakeDiscoveryError::NotFound(p)) => MultiplexerOutput::failure(
                    format!(
                        "error: no such file or directory (error code: 2)\n  file: {}\n",
                        p.join("lakefile.lean").display()
                    ),
                    1,
                ),
                Err(err) => MultiplexerOutput::failure(format!("{err}\n"), 1),
            }
        }
        "env" => {
            let prefix = std::env::var_os("LEAN_SYSROOT")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::current_exe()
                        .ok()
                        .and_then(|exe| derive_lean_installation_paths(&exe).ok().map(|p| p.prefix))
                })
                .unwrap_or_else(|| PathBuf::from("/usr/local"));

            if command_args.is_empty() {
                let mut out = String::new();
                out.push_str(&format!(
                    "ELAN_TOOLCHAIN=leanprover/lean4:{}\n",
                    fln::OLEAN_PIN_TAG
                ));
                out.push_str(&format!("LEAN_SYSROOT={}\n", prefix.display()));
                out.push_str(&format!(
                    "LEAN_PATH={}\n",
                    prefix.join("lib").join("lean").display()
                ));
                out.push_str(&format!(
                    "LEAN_SRC_PATH={}\n",
                    prefix.join("src").join("lean").display()
                ));
                MultiplexerOutput::success(out)
            } else {
                let subcmd = &command_args[0];
                let subargs = &command_args[1..];
                let mut proc = std::process::Command::new(subcmd);
                proc.args(subargs);
                proc.env(
                    "ELAN_TOOLCHAIN",
                    format!("leanprover/lean4:{}", fln::OLEAN_PIN_TAG),
                );
                proc.env("LEAN_SYSROOT", &prefix);
                proc.env("LEAN_PATH", prefix.join("lib").join("lean"));
                proc.env("LEAN_SRC_PATH", prefix.join("src").join("lean"));
                match proc.output() {
                    Ok(output) => MultiplexerOutput {
                        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
                        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                        exit_code: output.status.code().unwrap_or(1) as u8,
                    },
                    Err(_) => MultiplexerOutput::failure(
                        format!("could not execute external process '{subcmd}'\n"),
                        255,
                    ),
                }
            }
        }
        "check-build" => {
            if !command_args.is_empty() {
                return lake_operation_failure(
                    "fln.lake-check-build/1",
                    "lake check-build accepts no target arguments",
                    false,
                    is_json,
                );
            }
            let target_dir = dir.unwrap_or_else(|| PathBuf::from("."));
            // The pinned Lake command tests only default-target presence. It is
            // neither a dry build nor a source/type/target validity check.
            match fln_lake::LakeConfig::discover(&target_dir) {
                Ok(config) => {
                    if config.default_targets.is_empty() {
                        return lake_operation_failure(
                            "fln.lake-check-build/1",
                            "no default build targets are configured",
                            false,
                            is_json,
                        );
                    }
                    if is_json {
                        let targets_json = config
                            .default_targets
                            .iter()
                            .map(|s| json_string(s))
                            .collect::<Vec<_>>()
                            .join(",");
                        MultiplexerOutput::success(format!(
                            "{{\"schema\":\"fln.lake-check-build/1\",\"status\":\"success\",\"check\":\"default-target-presence\",\"package\":{},\"targets\":[{targets_json}]}}\n",
                            json_string(&config.name)
                        ))
                    } else {
                        MultiplexerOutput::success(String::new())
                    }
                }
                Err(fln_lake::LakeDiscoveryError::NotFound(p)) => MultiplexerOutput::failure(
                    format!(
                        "error: no such file or directory (error code: 2)\n  file: {}\n",
                        p.join("lakefile.lean").display()
                    ),
                    1,
                ),
                Err(err) => lake_operation_failure(
                    "fln.lake-check-build/1",
                    &err.to_string(),
                    matches!(err, fln_lake::LakeDiscoveryError::LeanConfigUnsupported(_)),
                    is_json,
                ),
            }
        }
        "query" | "test" | "lint" | "lean" => MultiplexerOutput::failure(
            format!("lake {cmd}: requires Lake workspace configuration (plan §13.3)\n"),
            1,
        ),
        unknown => MultiplexerOutput::failure(format!("error: unknown command '{unknown}'\n"), 1),
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
        CHECK_OLEAN_SCHEMA, FLBC_RUN_SCHEMA, ILEAN_INSPECT_SCHEMA, NamedOleanBytes,
        OLEAN_DIFF_SCHEMA, OLEAN_INSPECT_SCHEMA, OLEAN_REBUILD_SCHEMA, RECEIPT_SET_SCHEMA,
        SOURCE_RUN_KERNEL_STACK_BYTES, SOURCE_RUN_SCHEMA, SourcePresentation, SourcePublication,
        SourceSidecarPublication, admission_error_disposition, check_olean_bytes,
        check_olean_module_bytes, derive_lean_installation_paths, diff_olean_bytes,
        execute_flbc_bytes, execute_source_bytes, execute_source_bytes_with_publisher,
        execution_error_disposition, inspect_ilean_bytes, inspect_olean_bytes,
        module_name_from_relative, olean_write_error_disposition, parse_source_run,
        read_bounded_from, render_lean_source_commands, render_lean_source_module_commands, run,
        run_lean, run_lean_with_input, source_failure, source_import_relative_path,
        verify_olean_rebuild_bytes,
    };
    use std::ffi::OsString;
    use std::io::Cursor;
    use std::path::PathBuf;

    const PINNED_OLEAN: &[u8] =
        include_bytes!("../../../tribunal/fixtures/c3/Init.BinderNameHint.olean");
    const SECOND_PINNED_OLEAN: &[u8] =
        include_bytes!("../../../tribunal/fixtures/c3/Init.SizeOfLemmas.olean");
    const PINNED_ILEAN_HEX: &str = include_str!("../../fln-olean/tests/corpus/ilean_probe.hex");
    const OLD_STRING_FLBC: &[u8] = b"FLNFLBC\0\x08\0\x0d\0\0\0\0\0\x01\0\0\0\0\0\0\0\0\0\x01\0\0\0\0\0\0\x02\0\0\0\x01\0\0\x02\0\0\0hi\x0d\0\0";

    fn repository_path(relative: &str) -> PathBuf {
        let invoked_from = std::env::current_dir().expect("the test has an invocation directory");
        let root = invoked_from
            .ancestors()
            .find(|candidate| candidate.join("crates/fln-cli/Cargo.toml").is_file())
            .expect("the test is invoked from inside the FrankenLean workspace");
        root.join(relative)
    }

    fn pinned_ilean_bytes() -> Vec<u8> {
        let hex = PINNED_ILEAN_HEX.trim().as_bytes();
        let (pairs, remainder) = hex.as_chunks::<2>();
        assert!(
            remainder.is_empty(),
            "the pinned .ilean hex has whole bytes"
        );
        pairs
            .iter()
            .map(|pair| {
                let nibble = |byte| match byte {
                    b'0'..=b'9' => byte - b'0',
                    b'a'..=b'f' => byte - b'a' + 10,
                    b'A'..=b'F' => byte - b'A' + 10,
                    _ => u8::MAX,
                };
                let high = nibble(pair[0]);
                let low = nibble(pair[1]);
                assert!(high < 16 && low < 16, "the pinned .ilean fixture is hex");
                (high << 4) | low
            })
            .collect()
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

    fn string_flbc_fixture() -> Vec<u8> {
        let kernel = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
        let engine = fln::Engine::with_source_seed(fln::EngineAdmissionLimits::new(kernel))
            .expect("the source seed council does not reject")
            .into_complete()
            .expect("the source seed council answers completely");
        engine
            .execute_source_definition(
                b"def flbcFixture : String := \"hi\"",
                &fln::KVMap::new(),
                fln::EngineExecutionLimits::new(kernel),
            )
            .expect("the fixture source reaches the engine")
            .into_complete()
            .expect("the fixture executes authoritatively")
            .flbc_artifact
    }

    fn encode_checkable_olean(constants: &[fln::ConstantInfo]) -> Vec<u8> {
        let lean_version = fln::OLEAN_PIN_TAG
            .strip_prefix('v')
            .expect("the pin tag starts with v");
        fln::encode_olean_module(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports: &[],
                constants,
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

    fn checkable_olean_fixture() -> Vec<u8> {
        let proposition = fln::Name::from_components(["CliFixture", "P"]);
        let witness = fln::Name::from_components(["CliFixture", "p"]);
        let theorem = fln::Name::from_components(["CliFixture", "t"]);
        let proposition_expr = fln::Expr::const_(proposition.clone(), Vec::new());
        encode_checkable_olean(&[
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
        ])
    }

    fn mutual_checkable_olean_fixture() -> Vec<u8> {
        let base = fln::Name::from_components(["CliFixture", "mutualBase"]);
        let left = fln::Name::from_components(["CliFixture", "mutualLeft"]);
        let right = fln::Name::from_components(["CliFixture", "mutualRight"]);
        let members = vec![left.clone(), right.clone()];
        encode_checkable_olean(&[
            fln::ConstantInfo::Defn(fln::DefinitionVal {
                base: fln::ConstantVal {
                    name: right.clone(),
                    level_params: Vec::new(),
                    type_: fln::Expr::const_(base.clone(), Vec::new()),
                },
                value: fln::Expr::const_(left.clone(), Vec::new()),
                hints: fln::ReducibilityHints::Regular(1),
                safety: fln::DefinitionSafety::Partial,
                all: members.clone(),
            }),
            fln::ConstantInfo::Defn(fln::DefinitionVal {
                base: fln::ConstantVal {
                    name: left,
                    level_params: Vec::new(),
                    type_: fln::Expr::const_(base.clone(), Vec::new()),
                },
                value: fln::Expr::const_(right, Vec::new()),
                hints: fln::ReducibilityHints::Regular(1),
                safety: fln::DefinitionSafety::Partial,
                all: members,
            }),
            fln::ConstantInfo::Axiom(fln::AxiomVal {
                base: fln::ConstantVal {
                    name: base,
                    level_params: Vec::new(),
                    type_: fln::Expr::sort(fln::Level::zero()),
                },
                is_unsafe: false,
            }),
        ])
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
        assert!(robot.stdout.contains("\"returnValue\":73"));

        let human = execute_flbc_bytes(&artifact, artifact.len(), false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stdout.contains("canonical FLBC execution: complete"));
        assert!(human.stdout.contains("return value: 73"));

        // The positive fixture comes from the native producer, not a stale
        // hand-written envelope with yesterday's wire/schema versions.
        let string = string_flbc_fixture();
        let non_scalar = execute_flbc_bytes(&string, string.len(), true);
        assert_eq!(non_scalar.exit_code, 0, "{}", non_scalar.stderr);
        assert!(non_scalar.stdout.contains("\"returnKind\":\"string\""));
        assert!(non_scalar.stdout.contains("\"returnValue\":\"hi\""));

        let obsolete = execute_flbc_bytes(OLD_STRING_FLBC, OLD_STRING_FLBC.len(), true);
        assert_eq!(obsolete.exit_code, 1);
        assert!(obsolete.stdout.is_empty());
        assert!(obsolete.stderr.contains("unsupported FLBC wire version 8"));

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
        let human = inspect_olean_bytes(PINNED_OLEAN, PINNED_OLEAN.len(), false, false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains("pinned .olean audit: complete"));
        assert!(human.stdout.contains("constants: 2\n"));

        let robot = inspect_olean_bytes(PINNED_OLEAN, PINNED_OLEAN.len(), true, false);
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
    fn ilean_inspect_reaches_the_pinned_codec_and_separates_canonical_bytes() {
        let bytes = pinned_ilean_bytes();
        let robot = inspect_ilean_bytes(&bytes, bytes.len(), true);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(
            robot
                .stdout
                .contains(&format!("\"schema\":\"{ILEAN_INSPECT_SCHEMA}\""))
        );
        assert!(robot.stdout.contains("\"authority\":false"));
        assert!(robot.stdout.contains("\"byteIdentity\":true"));
        assert!(robot.stdout.contains("\"version\":5"));
        assert!(robot.stdout.contains("\"module\":\"IleanProbe\""));
        assert!(robot.stdout.contains("\"directImports\":0"));
        assert!(robot.stdout.contains("\"references\":2"));
        assert!(robot.stdout.contains("\"declarations\":1"));

        let human = inspect_ilean_bytes(&bytes, bytes.len(), false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains("pinned .ilean audit: complete"));
        assert!(human.stdout.contains("byte identity: exact"));

        let mut noncanonical = b" \n".to_vec();
        noncanonical.extend_from_slice(&bytes);
        let semantic_only = inspect_ilean_bytes(&noncanonical, noncanonical.len(), true);
        assert_eq!(semantic_only.exit_code, 0, "{}", semantic_only.stderr);
        assert!(semantic_only.stdout.contains("\"byteIdentity\":false"));
        assert!(
            semantic_only
                .stdout
                .contains(&format!("\"canonicalBytes\":{}", bytes.len()))
        );
    }

    #[test]
    fn ilean_inspect_preserves_codec_and_budget_failures_as_non_authority() {
        let bytes = pinned_ilean_bytes();
        let mut corrupt = bytes.clone();
        corrupt[0] = b'!';
        let malformed = inspect_ilean_bytes(&corrupt, corrupt.len(), true);
        assert_eq!(malformed.exit_code, 1);
        assert!(malformed.stdout.is_empty());
        assert!(malformed.stderr.contains("\"authority\":false"));
        assert!(malformed.stderr.contains("\"class\":\"codec\""));
        assert!(malformed.stderr.contains("decode:"));

        let exhausted = inspect_ilean_bytes(&bytes, bytes.len() - 1, true);
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.contains("\"authority\":false"));
        assert!(exhausted.stderr.contains("\"class\":\"resource\""));

        let wired = run([
            OsString::from("ilean"),
            OsString::from("inspect"),
            OsString::from("--json"),
            repository_path("crates/fln-olean/tests/corpus/ilean_probe.hex").into_os_string(),
        ]);
        assert_eq!(wired.exit_code, 1);
        assert!(wired.stderr.contains("\"schema\":\"fln.ilean-inspect/1\""));
        assert!(wired.stderr.contains("\"class\":\"codec\""));

        let missing = run([OsString::from("ilean"), OsString::from("inspect")]);
        assert_eq!(missing.exit_code, 2);
        assert!(missing.stderr.contains("ilean inspect requires PATH"));

        let extra = run([
            OsString::from("ilean"),
            OsString::from("inspect"),
            OsString::from("one.ilean"),
            OsString::from("two.ilean"),
        ]);
        assert_eq!(extra.exit_code, 2);
        assert!(
            extra
                .stderr
                .contains("ilean inspect accepts exactly one input path")
        );
    }

    #[test]
    fn olean_diff_separates_byte_identity_from_decoded_semantic_changes() {
        let identical = diff_olean_bytes(PINNED_OLEAN, PINNED_OLEAN, PINNED_OLEAN.len() * 2, true);
        assert_eq!(identical.exit_code, 0, "{}", identical.stderr);
        assert!(identical.stderr.is_empty());
        assert!(
            identical
                .stdout
                .contains(&format!("\"schema\":\"{OLEAN_DIFF_SCHEMA}\""))
        );
        assert!(identical.stdout.contains("\"authority\":false"));
        assert!(identical.stdout.contains("\"byteIdentity\":true"));
        assert!(identical.stdout.contains("\"semanticIdentity\":true"));
        assert!(identical.stdout.contains("\"changes\":[]"));
        assert!(identical.stdout.contains("\"omittedChanges\":0"));

        let changed = diff_olean_bytes(
            PINNED_OLEAN,
            SECOND_PINNED_OLEAN,
            PINNED_OLEAN.len() + SECOND_PINNED_OLEAN.len(),
            true,
        );
        assert_eq!(changed.exit_code, 0, "{}", changed.stderr);
        assert!(changed.stderr.is_empty());
        assert!(changed.stdout.contains("\"byteIdentity\":false"));
        assert!(changed.stdout.contains("\"semanticIdentity\":false"));
        assert!(!changed.stdout.contains("\"changes\":[]"));

        let human = diff_olean_bytes(
            PINNED_OLEAN,
            SECOND_PINNED_OLEAN,
            PINNED_OLEAN.len() + SECOND_PINNED_OLEAN.len(),
            false,
        );
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(
            human
                .stdout
                .contains("pinned .olean semantic diff: different")
        );
        assert!(human.stdout.contains("changes shown:"));

        let wired = run([
            OsString::from("olean"),
            OsString::from("diff"),
            OsString::from("--json"),
            repository_path("tribunal/fixtures/c3/Init.BinderNameHint.olean").into_os_string(),
            repository_path("tribunal/fixtures/c3/Init.SizeOfLemmas.olean").into_os_string(),
        ]);
        assert_eq!(wired.exit_code, 0, "{}", wired.stderr);
        assert!(wired.stderr.is_empty());
        assert!(wired.stdout.contains("\"schema\":\"fln.olean-diff/1\""));

        let missing_side = run([
            OsString::from("olean"),
            OsString::from("diff"),
            OsString::from("only-one.olean"),
        ]);
        assert_eq!(missing_side.exit_code, 2);
        assert!(missing_side.stdout.is_empty());
        assert!(
            missing_side
                .stderr
                .contains("olean diff accepts exactly two input paths")
        );
    }

    #[test]
    fn olean_diff_preserves_side_and_resource_failures_as_non_authority() {
        let mut corrupt = SECOND_PINNED_OLEAN.to_vec();
        corrupt[0] ^= 0xff;
        let malformed = diff_olean_bytes(
            PINNED_OLEAN,
            &corrupt,
            PINNED_OLEAN.len() + corrupt.len(),
            true,
        );
        assert_eq!(malformed.exit_code, 1);
        assert!(malformed.stdout.is_empty());
        assert!(malformed.stderr.contains("\"authority\":false"));
        assert!(malformed.stderr.contains("\"class\":\"decode\""));
        assert!(malformed.stderr.contains("right artifact"));

        let exhausted = diff_olean_bytes(
            PINNED_OLEAN,
            SECOND_PINNED_OLEAN,
            PINNED_OLEAN.len() + SECOND_PINNED_OLEAN.len() - 1,
            true,
        );
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.contains("\"authority\":false"));
        assert!(exhausted.stderr.contains("\"class\":\"resource\""));
    }

    #[test]
    fn olean_diff_detects_same_name_changes_and_observable_constant_order() {
        let left = fln::decode_olean_artifact(
            PINNED_OLEAN,
            fln::OleanDecodeLimits::new(PINNED_OLEAN.len()),
        )
        .expect("decode the real pinned diff fixture");
        let mut changed = left.clone();
        let first = changed.constants.first_mut();
        assert!(
            first.is_some(),
            "the real diff fixture must remain nonempty"
        );
        let Some(first) = first else {
            return;
        };
        assert!(
            matches!(first, fln::ConstantInfo::Defn(_)),
            "the real fixture's first row must remain a definition"
        );
        let fln::ConstantInfo::Defn(definition) = first else {
            return;
        };
        definition.safety = fln::DefinitionSafety::Unsafe;
        let summary = super::compare_decoded_oleans(PINNED_OLEAN, &left, PINNED_OLEAN, &changed)
            .expect("compare the planted same-name semantic change");
        assert!(summary.byte_identity);
        assert!(!summary.semantic_identity());
        assert_eq!(summary.modified_names, 1);
        assert_eq!(summary.changes.len(), 1);
        assert!(matches!(
            summary.changes[0].change,
            super::OleanDiffChange::Modified
        ));

        let mut reordered = left.clone();
        reordered.constants.swap(0, 1);
        let order_summary =
            super::compare_decoded_oleans(PINNED_OLEAN, &left, PINNED_OLEAN, &reordered)
                .expect("compare the planted constant-order change");
        assert!(!order_summary.constant_sequence_identity);
        assert!(!order_summary.semantic_identity());
        assert!(order_summary.changes.is_empty());
        assert_eq!(order_summary.unchanged_constants, left.constants.len());
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
    fn check_olean_cli_reaches_reconstructed_non_safe_mutual_units() {
        let artifact = mutual_checkable_olean_fixture();
        let robot = check_olean_bytes(artifact.clone(), artifact.len(), true);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(robot.stdout.contains("\"authority\":true"));
        assert!(robot.stdout.contains("\"declarationsChecked\":3"));
        assert!(robot.stdout.contains("\"dependencyOrderDerived\":true"));
        assert!(robot.stdout.contains("\"g1Satisfied\":false"));

        let human = check_olean_bytes(artifact.clone(), artifact.len(), false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains("declarations checked: 3"));
        assert!(human.stdout.contains("authority: K1 + independent checker"));
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
            None,
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

        let output = inspect_olean_bytes(&bytes, bytes.len(), true, false);
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

        let output = inspect_olean_bytes(PINNED_OLEAN, PINNED_OLEAN.len() - 1, true, false);
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
        assert!(robot.stdout.contains("\"commands\":1"));
        assert!(robot.stdout.contains("\"definitions\":1"));
        assert!(robot.stdout.contains("\"evaluations\":0"));
        assert!(robot.stdout.contains("\"finalValue\":0"));
        assert!(
            robot
                .stdout
                .contains("\"finalGround\":\"body-checked-against-declared-type\"")
        );
    }

    #[test]
    fn lean_installation_queries_require_the_conventional_bin_layout() {
        let executable = PathBuf::from("toolchain").join("bin").join("lean");
        let paths = derive_lean_installation_paths(&executable)
            .expect("a conventional installed executable has a toolchain root");
        assert_eq!(paths.prefix, PathBuf::from("toolchain"));
        assert_eq!(
            paths.libdir,
            PathBuf::from("toolchain").join("lib").join("lean")
        );

        let development = PathBuf::from("target").join("debug").join("lean");
        let error = derive_lean_installation_paths(&development)
            .expect_err("a development binary must not report a false toolchain root");
        assert!(error.contains("not located at <prefix>/bin/lean"));
    }

    #[test]
    fn lean_personality_help_version_and_usage_are_explicitly_bounded() {
        let help = run_lean(std::iter::empty());
        assert_eq!(help.exit_code, 0);
        assert!(help.stderr.is_empty());
        assert!(
            help.stdout
                .starts_with("Usage:\n  lean [--max-bytes BYTES] PATH")
        );
        assert!(help.stdout.contains("bounded native `lean` personality"));
        assert!(
            help.stdout
                .contains("does not implement the Reference CLI's option set")
        );
        assert!(help.stdout.contains("complete local A/B.lean closure"));
        assert!(help.stdout.contains("lean --stdin"));
        assert!(help.stdout.contains("bounded import-free source"));
        assert!(
            help.stdout
                .contains("Import-free #check commands may appear anywhere")
        );
        assert!(help.stdout.contains("transitive dependency closure"));
        assert!(
            help.stdout
                .contains("empty --stdin stream succeeds silently")
        );
        assert!(
            help.stdout
                .contains("Dependency definitions, #eval, and scratch-only #check run silently")
        );
        assert!(help.stdout.contains(
            "Every dependency query is checked against that module's transitive imports"
        ));
        assert!(help.stdout.contains("import-only entry succeeds silently"));
        assert!(help.stdout.contains("lean --src-deps"));
        assert!(help.stdout.contains("lean --print-prefix"));
        assert!(help.stdout.contains("lean --print-libdir"));
        assert!(
            help.stdout
                .contains("validated direct local source imports in source order")
        );
        assert!(
            help.stdout
                .contains("LEAN_PATH/package or\n.olean discovery")
        );

        let pin_version = fln::OLEAN_PIN_TAG
            .strip_prefix('v')
            .expect("the governed Lean tag carries the conventional v prefix");
        let expected_version = format!(
            "Lean (version {pin_version}, FrankenLean bounded native source personality {})\n",
            env!("CARGO_PKG_VERSION")
        );
        for option in ["--version", "-v"] {
            let version = run_lean([OsString::from(option)]);
            assert_eq!(version.exit_code, 0);
            assert_eq!(version.stdout, expected_version);
            assert!(version.stderr.is_empty());
        }
        for option in ["--short-version", "-V"] {
            let version = run_lean([OsString::from(option)]);
            assert_eq!(version.exit_code, 0);
            assert_eq!(version.stdout, format!("{pin_version}\n"));
            assert!(version.stderr.is_empty());
        }
        for option in ["--githash", "-g"] {
            let githash = run_lean([OsString::from(option)]);
            assert_eq!(githash.exit_code, 0);
            assert_eq!(githash.stdout, format!("{}\n", fln::OLEAN_PIN_COMMIT));
            assert!(githash.stderr.is_empty());
        }
        let features = run_lean([OsString::from("--features")]);
        assert_eq!(features.exit_code, 0);
        assert_eq!(features.stdout, "[]\n");
        assert!(features.stderr.is_empty());

        for option in ["--print-prefix", "--print-libdir"] {
            let refused = run_lean([OsString::from(option)]);
            assert_eq!(refused.exit_code, 1);
            assert!(refused.stdout.is_empty());
            assert!(refused.stderr.starts_with("lean: installation: "));
            assert!(refused.stderr.contains("<prefix>/bin/lean"));
        }

        let missing_input_handle = run_lean([OsString::from("--stdin")]);
        assert_eq!(missing_input_handle.exit_code, 2);
        assert!(missing_input_handle.stdout.is_empty());
        assert!(
            missing_input_handle
                .stderr
                .contains("requires an explicit input handle")
        );
        let mut input = std::io::Cursor::new(b"#eval 40 + 2\n".as_slice());
        let piped = run_lean_with_input([OsString::from("--stdin")], &mut input);
        assert_eq!(piped.exit_code, 0);
        assert_eq!(piped.stdout, "42\n");
        assert!(piped.stderr.is_empty());
        let mut check_input = std::io::Cursor::new(b"#check Nat\n".as_slice());
        let checked = run_lean_with_input([OsString::from("--stdin")], &mut check_input);
        assert_eq!(checked.exit_code, 0, "{}", checked.stderr);
        assert_eq!(checked.stdout, "Nat : Type\n");
        assert!(checked.stderr.is_empty());
        let mut quiet_input = std::io::Cursor::new(b"#eval 40 + 2\n".as_slice());
        let quiet_piped = run_lean_with_input(
            [
                OsString::from("-q"),
                OsString::from("--quiet"),
                OsString::from("--stdin"),
            ],
            &mut quiet_input,
        );
        assert_eq!(quiet_piped.exit_code, 0);
        assert_eq!(quiet_piped.stdout, "42\n");
        assert!(quiet_piped.stderr.is_empty());
        let mut unselected_input = std::io::Cursor::new(b"must remain unread".as_slice());
        let short_version =
            run_lean_with_input([OsString::from("--short-version")], &mut unselected_input);
        assert_eq!(short_version.exit_code, 0);
        assert_eq!(unselected_input.position(), 0);

        for arguments in [
            vec![OsString::from("--json")],
            vec![OsString::from("One.lean"), OsString::from("Two.lean")],
            vec![OsString::from("--help"), OsString::from("One.lean")],
            vec![
                OsString::from("--max-bytes=1"),
                OsString::from("--max-bytes=2"),
                OsString::from("One.lean"),
            ],
            vec![
                OsString::from("--src-deps"),
                OsString::from("--src-deps"),
                OsString::from("One.lean"),
            ],
            vec![OsString::from("--stdin"), OsString::from("One.lean")],
            vec![OsString::from("--stdin"), OsString::from("--stdin")],
            vec![OsString::from("--stdin"), OsString::from("--src-deps")],
            vec![OsString::from("--githash"), OsString::from("One.lean")],
            vec![OsString::from("--features"), OsString::from("One.lean")],
            vec![OsString::from("--print-prefix"), OsString::from("One.lean")],
            vec![OsString::from("--print-libdir"), OsString::from("One.lean")],
            vec![OsString::from("--quiet")],
        ] {
            let refused = run_lean(arguments);
            assert_eq!(refused.exit_code, 2);
            assert!(refused.stdout.is_empty());
            assert!(refused.stderr.starts_with("lean: "));
            assert!(refused.stderr.contains("\n\nUsage:\n  lean "));
        }

        let source = repository_path("vendor/lean4-src/tests/lake/examples/deps/root/Root.lean");
        let exhausted = run_lean([OsString::from("--max-bytes=0"), source.into_os_string()]);
        assert_eq!(exhausted.exit_code, 3);
        assert!(exhausted.stdout.is_empty());
        assert!(exhausted.stderr.starts_with("lean: resource: "));
        assert!(exhausted.stderr.contains("0-byte input limit"));
    }

    #[test]
    fn lean_source_import_names_map_only_to_normalized_lean_paths() {
        let name = fln::Name::from_components(["Project", "Foundation", "Nat"]);
        assert_eq!(
            source_import_relative_path(&name).expect("string components map to a source path"),
            PathBuf::from("Project/Foundation/Nat.lean")
        );

        let numeric = fln::Name::num(fln::Name::anonymous(), 1);
        let error = source_import_relative_path(&numeric)
            .expect_err("numeric module components cannot become filesystem authority");
        assert_eq!(error.class(), "input");
        assert!(error.to_string().contains("nonempty string-component"));

        let traversal = fln::Name::from_components(["..", "Secret"]);
        let error = source_import_relative_path(&traversal)
            .expect_err("a forged name cannot escape the selected source root");
        assert_eq!(error.class(), "input");
        assert!(error.to_string().contains("one normalized path segment"));
    }

    #[test]
    fn lean_personality_prints_only_evaluations_and_keeps_definitions_silent() {
        let evaluated = super::execute_source_bytes_with_publisher_and_presentation(
            vec![
                b"#eval \"native\"\n#eval 40 + 2\ndef keep : Nat := 7\n#eval keep == 7\ndef answer : Nat := keep + 2"
                    .to_vec(),
            ],
            None,
            SourcePublication::None,
            SourcePresentation::Lean,
            |_, _| Ok::<(), std::io::Error>(()),
        );
        assert_eq!(evaluated.exit_code, 0, "{}", evaluated.stderr);
        assert_eq!(evaluated.stdout, "\"native\"\n42\ntrue\n");
        assert!(evaluated.stderr.is_empty());

        let source = repository_path("vendor/lean4-src/tests/lake/examples/deps/root/Root.lean");
        let definition_only = run_lean([source.into_os_string()]);
        assert_eq!(definition_only.exit_code, 0, "{}", definition_only.stderr);
        assert!(definition_only.stdout.is_empty());
        assert!(definition_only.stderr.is_empty());

        let function_only = super::execute_source_bytes_with_publisher_and_presentation(
            vec![b"def add (x : Nat) : Nat := x + 1".to_vec()],
            None,
            SourcePublication::None,
            SourcePresentation::Lean,
            |_, _| Ok::<(), std::io::Error>(()),
        );
        assert_eq!(function_only.exit_code, 0, "{}", function_only.stderr);
        assert!(function_only.stdout.is_empty());
        assert!(function_only.stderr.is_empty());

        let final_function_after_evaluation =
            super::execute_source_bytes_with_publisher_and_presentation(
                vec![
                    b"def add (x : Nat) : Nat := x + 1\n#eval add 41\ndef keep (x : Nat) : Nat := x"
                        .to_vec(),
                ],
                None,
                SourcePublication::None,
                SourcePresentation::Lean,
                |_, _| Ok::<(), std::io::Error>(()),
            );
        assert_eq!(
            final_function_after_evaluation.exit_code, 0,
            "{}",
            final_function_after_evaluation.stderr
        );
        assert_eq!(final_function_after_evaluation.stdout, "42\n");
        assert!(final_function_after_evaluation.stderr.is_empty());

        let fln_contract =
            execute_source_bytes(vec![b"def add (x : Nat) : Nat := x + 1".to_vec()], true);
        assert_eq!(fln_contract.exit_code, 1);
        assert!(fln_contract.stdout.is_empty());
        assert!(fln_contract.stderr.contains("\"class\":\"execution\""));
        assert!(
            fln_contract
                .stderr
                .contains("final command did not produce a closed Nat, String, or Bool value")
        );

        let fln_check = execute_source_bytes(vec![b"#check Nat".to_vec()], true);
        assert_eq!(fln_check.exit_code, 1);
        assert!(fln_check.stdout.is_empty());
        assert!(fln_check.stderr.contains("\"class\":\"execution\""));
        assert!(
            fln_check
                .stderr
                .contains("ordered import-free native lean command stream")
        );
    }

    #[test]
    fn lean_personality_preserves_typed_source_failures_without_fln_framing() {
        let source = repository_path("crates/fln-conformance/fixtures/g04_reference_fixture.lean");
        let refused = run_lean([source.into_os_string()]);
        assert_eq!(refused.exit_code, 1);
        assert!(refused.stdout.is_empty());
        assert!(refused.stderr.starts_with("lean: execution: "));
        assert!(refused.stderr.contains("frontend refused source"));
        assert!(!refused.stderr.contains(SOURCE_RUN_SCHEMA));
        assert!(!refused.stderr.contains("native source batch"));
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
        assert!(output.stdout.contains("\"commands\":2"));
        assert!(output.stdout.contains("\"definitions\":2"));
        assert!(output.stdout.contains("\"evaluations\":0"));
        assert!(output.stdout.contains("\"sourceBytes\":28"));
        assert!(output.stdout.contains("\"finalValue\":0"));
        assert!(output.stdout.contains("\"admissions\":2,\"finalSchema\""));

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
    fn source_module_plan_binds_import_names_to_exact_path_suffixes() {
        let paths = vec![
            PathBuf::from("/workspace/Project/Base.lean"),
            PathBuf::from("/workspace/Project/Middle.lean"),
            PathBuf::from("/workspace/Main.lean"),
        ];
        let sources = vec![
            b"def base := 20".to_vec(),
            b"import Project.Base\ndef middle := base".to_vec(),
            b"import Project.Middle\ndef answer := middle".to_vec(),
        ];
        let plan = super::derive_source_module_plan(&paths, &sources)
            .expect("the exact suffix mapping is unambiguous")
            .expect("imports select closed-module execution");

        assert_eq!(
            plan.names,
            vec![
                fln::Name::from_components(["Project", "Base"]),
                fln::Name::from_components(["Project", "Middle"]),
                fln::Name::from_components(["Main"]),
            ]
        );
        assert_eq!(plan.entry, fln::Name::from_components(["Main"]));
    }

    #[test]
    fn source_module_plan_refuses_ambiguous_suffixes_and_dotted_entry_stems() {
        let ambiguous_paths = vec![
            PathBuf::from("/one/Project/Base.lean"),
            PathBuf::from("/two/Project/Base.lean"),
            PathBuf::from("/workspace/Main.lean"),
        ];
        let ambiguous_sources = vec![
            b"def first := 1".to_vec(),
            b"def second := 2".to_vec(),
            b"import Project.Base\ndef answer := first".to_vec(),
        ];
        let ambiguity = super::derive_source_module_plan(&ambiguous_paths, &ambiguous_sources)
            .expect_err("one import cannot select two byte inputs");
        assert!(
            ambiguity
                .detail()
                .contains("matches more than one supplied source path")
        );

        let dotted_paths = vec![
            PathBuf::from("/workspace/Dependency.lean"),
            PathBuf::from("/workspace/Main.Entry.lean"),
        ];
        let dotted_sources = vec![
            b"def dependency := 1".to_vec(),
            b"import Missing\ndef answer := dependency".to_vec(),
        ];
        let dotted = super::derive_source_module_plan(&dotted_paths, &dotted_sources)
            .expect_err("a dotted file stem cannot invent a module hierarchy");
        assert!(dotted.detail().contains("dotted file stem"));

        let too_many_paths = (0..=fln::SourceModuleLimits::default().max_modules)
            .map(|index| PathBuf::from(format!("Module{index}.lean")))
            .collect::<Vec<_>>();
        let exhausted = super::derive_source_module_plan(&too_many_paths, &[])
            .expect_err("module planning is bounded before suffix matching");
        assert_eq!(exhausted.disposition(), ("resource", false, 3));
        assert!(exhausted.detail().contains("planning limit"));
    }

    #[test]
    fn source_run_projects_checked_bool_results_as_json_booleans() {
        let output =
            execute_source_bytes(vec![b"def answer : Bool := 40 + 2 == 42".to_vec()], true);

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains("\"schema\":\"fln.source-run/9\""));
        assert!(output.stdout.contains("\"finalKind\":\"bool\""));
        assert!(output.stdout.contains("\"finalValue\":true"));
        assert!(!output.stdout.contains("\"finalValue\":1"));
    }

    #[test]
    fn source_run_reports_every_interleaved_evaluation_in_command_order() {
        let source =
            b"#eval 40 + 2\ndef keep : Nat := 7\n#eval keep == 7\ndef answer : Nat := keep + 2"
                .to_vec();
        let robot = execute_source_bytes(vec![source.clone()], true);

        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(robot.stdout.contains("\"schema\":\"fln.source-run/9\""));
        assert!(robot.stdout.contains("\"commands\":4"));
        assert!(robot.stdout.contains("\"definitions\":2"));
        assert!(robot.stdout.contains("\"evaluations\":2"));
        assert!(robot.stdout.contains(concat!(
            "\"evaluationResults\":[",
            "{\"command\":0,\"kind\":\"nat\",\"value\":42},",
            "{\"command\":2,\"kind\":\"bool\",\"value\":true}]"
        )));
        assert!(robot.stdout.contains("\"finalKind\":\"nat\""));
        assert!(robot.stdout.contains("\"finalValue\":9"));

        let human = execute_source_bytes(vec![source], false);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stderr.is_empty());
        assert!(human.stdout.contains(concat!(
            "evaluation results:\n",
            "  command 0 (nat): 42\n",
            "  command 2 (bool): true\n"
        )));
        assert!(human.stdout.contains("final value: 9\n"));
    }

    #[test]
    fn source_bool_projection_refuses_non_bool_runtime_scalars() {
        let error = super::project_source_closed_value(
            super::SourceResultKind::Bool,
            fln::ClosedVmValue::Scalar(2),
        )
        .expect_err("a checked Bool cannot use a scalar other than 0 or 1");

        assert!(matches!(
            &error,
            super::SourceValueProjectionError::InvalidBoolScalar(2)
        ));
        assert_eq!(
            error.to_string(),
            "checked Bool result used invalid runtime scalar 2; expected 0 or 1"
        );
    }

    #[test]
    fn source_run_executes_checked_string_batches_and_publishes_the_executed_product() {
        let output = execute_source_bytes(
            vec![
                b"def copy (value : String) := value".to_vec(),
                b"def message : String := copy \"cli\\nconnected\"".to_vec(),
            ],
            true,
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains("\"schema\":\"fln.source-run/9\""));
        assert!(output.stdout.contains("\"definitions\":2"));
        assert!(output.stdout.contains("\"finalKind\":\"string\""));
        assert!(output.stdout.contains("\"finalValue\":\"cli\\nconnected\""));
        assert!(output.stdout.contains("\"authority\":true"));

        let target = PathBuf::from("string.flbc");
        let mut publications = Vec::new();
        let published = execute_source_bytes_with_publisher(
            vec![b"def message : String := \"published\\nstring\"".to_vec()],
            None,
            SourcePublication::Flbc {
                path: PathBuf::from("string.flbc"),
                sidecar: None,
            },
            true,
            |bytes, path| {
                publications.push((path.to_path_buf(), bytes.to_vec()));
                Ok::<(), std::io::Error>(())
            },
        );
        assert_eq!(published.exit_code, 0, "{}", published.stderr);
        assert!(published.stderr.is_empty());
        assert_eq!(publications.len(), 1);
        assert_eq!(publications[0].0, target);
        let replay = execute_flbc_bytes(&publications[0].1, publications[0].1.len(), true);
        assert_eq!(replay.exit_code, 0, "{}", replay.stderr);
        assert!(replay.stderr.is_empty());
        assert!(replay.stdout.contains("\"returnKind\":\"string\""));
        assert!(
            replay
                .stdout
                .contains("\"returnValue\":\"published\\nstring\"")
        );

        let mut failed_publications = 0;
        let refused = execute_source_bytes_with_publisher(
            vec![b"def open (value : String) : String := value".to_vec()],
            None,
            SourcePublication::Flbc {
                path: PathBuf::from("open.flbc"),
                sidecar: None,
            },
            true,
            |_bytes, _path| {
                failed_publications += 1;
                Ok::<(), std::io::Error>(())
            },
        );
        assert_eq!(refused.exit_code, 1);
        assert_eq!(failed_publications, 0);
        assert!(refused.stdout.is_empty());
        assert!(refused.stderr.contains("\"class\":\"execution\""));
        assert!(
            refused
                .stderr
                .contains("did not produce a closed Nat, String, or Bool value")
        );
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
            None,
            SourcePublication::Flbc {
                path: target.clone(),
                sidecar: None,
            },
            true,
            |bytes, path| {
                publications.push((path.to_path_buf(), bytes.to_vec()));
                Ok::<(), std::io::Error>(())
            },
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert_eq!(publications, vec![(target, expected.clone())]);
        assert!(output.stdout.contains("\"schema\":\"fln.source-run/9\""));
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
            None,
            SourcePublication::Flbc {
                path: PathBuf::from("must-not-publish.flbc"),
                sidecar: None,
            },
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
            None,
            SourcePublication::Flbc {
                path: PathBuf::from("refused.flbc"),
                sidecar: None,
            },
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
    fn source_run_emits_one_checkable_standalone_olean_environment_after_success() {
        let target = PathBuf::from("checked-environment.olean");
        let mut publications = Vec::new();
        let output = execute_source_bytes_with_publisher(
            vec![
                b"def base : Nat := 40\n#eval base + 2\ndef answer : Bool := base + 2 == 42"
                    .to_vec(),
            ],
            None,
            SourcePublication::OleanSnapshot {
                path: target.clone(),
            },
            true,
            |bytes, path| {
                publications.push((path.to_path_buf(), bytes.to_vec()));
                Ok::<(), std::io::Error>(())
            },
        );

        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stderr.is_empty());
        assert_eq!(publications.len(), 1);
        assert_eq!(publications[0].0, target);
        assert!(output.stdout.contains("\"schema\":\"fln.source-run/9\""));
        assert!(output.stdout.contains("\"emittedOleanSnapshot\":{"));
        assert!(output.stdout.contains("\"module\":false"));

        let artifact = &publications[0].1;
        let decoded =
            fln::decode_olean_artifact(artifact, fln::OleanDecodeLimits::new(artifact.len()))
                .expect("the emitted standalone snapshot decodes through the public door");
        assert!(!decoded.module.is_module);
        assert!(
            decoded.constants.len() > 3,
            "the checked seed is closed inside the snapshot"
        );
        let checked = check_olean_bytes(artifact.clone(), artifact.len(), true);
        assert_eq!(checked.exit_code, 0, "{}", checked.stderr);
        assert!(checked.stderr.is_empty());
        assert!(checked.stdout.contains("\"outcome\":\"complete\""));
        assert!(checked.stdout.contains("\"authority\":true"));

        let mut late_publications = 0;
        let late_failure = execute_source_bytes_with_publisher(
            vec![b"#eval 40 + 2\ndef broken : Nat := missing".to_vec()],
            None,
            SourcePublication::OleanSnapshot {
                path: PathBuf::from("must-not-exist.olean"),
            },
            true,
            |_bytes, _path| {
                late_publications += 1;
                Ok::<(), std::io::Error>(())
            },
        );
        assert_eq!(late_failure.exit_code, 1);
        assert!(late_failure.stdout.is_empty());
        assert_eq!(late_publications, 0);

        let collision = execute_source_bytes_with_publisher(
            vec![b"def answer : Nat := 42".to_vec()],
            None,
            SourcePublication::OleanSnapshot {
                path: PathBuf::from("existing.olean"),
            },
            true,
            |_bytes, _path| Err(std::io::Error::from(std::io::ErrorKind::AlreadyExists)),
        );
        assert_eq!(collision.exit_code, 1);
        assert!(collision.stdout.is_empty());
        assert!(collision.stderr.contains("\"class\":\"output\""));
        assert!(collision.stderr.contains("\"authority\":true"));
    }

    #[test]
    fn olean_snapshot_writer_budget_is_a_nonanswer_and_contract_faults_are_internal() {
        let budget = fln::OleanWriteError::Budget {
            resource: fln::OleanWriteResource::Bytes,
            limit: 1,
            attempted: 2,
        };
        assert_eq!(
            olean_write_error_disposition(&budget),
            ("resource", false, 3)
        );

        let contract = fln::OleanWriteError::Contract {
            what: "planted writer contract fault",
        };
        assert_eq!(
            olean_write_error_disposition(&contract),
            ("internal-fault", false, 4)
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
                None,
                SourcePublication::Flbc {
                    path: PathBuf::from("resource-exhausted.flbc"),
                    sidecar: None,
                },
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
            None,
            SourcePublication::Flbc {
                path: PathBuf::from("resource-exhausted-compound.flbc"),
                sidecar: None,
            },
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
            None,
            SourcePublication::Flbc {
                path: flbc_path.clone(),
                sidecar: Some(SourceSidecarPublication {
                    path: sidecar_path.clone(),
                    toolchain_image: Some(b"injected toolchain image".to_vec()),
                }),
            },
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
            None,
            SourcePublication::Flbc {
                path: PathBuf::from("not-published.flbc"),
                sidecar: Some(SourceSidecarPublication {
                    path: PathBuf::from("not-published.sidecar"),
                    toolchain_image: Some(b"injected toolchain image".to_vec()),
                }),
            },
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

        let snapshot = parse_source_run(vec![
            OsString::from("--emit-olean-snapshot=environment.olean"),
            OsString::from("input.lean"),
        ])
        .expect("one standalone snapshot path is valid");
        assert!(matches!(
            snapshot,
            super::MultiplexerCommand::SourceRun {
                emit_flbc: None,
                emit_sidecar: None,
                emit_olean_snapshot: Some(path),
                ..
            } if path == std::path::Path::new("environment.olean")
        ));

        let duplicate_snapshot = parse_source_run(vec![
            OsString::from("--emit-olean-snapshot=one.olean"),
            OsString::from("--emit-olean-snapshot"),
            OsString::from("two.olean"),
            OsString::from("input.lean"),
        ])
        .expect_err("duplicate standalone snapshot paths are ambiguous");
        assert!(duplicate_snapshot.to_string().contains("at most once"));

        let mixed_products = parse_source_run(vec![
            OsString::from("--emit-flbc=product.flbc"),
            OsString::from("--emit-olean-snapshot=environment.olean"),
            OsString::from("input.lean"),
        ])
        .expect_err("independently durable products cannot imply one transaction");
        assert!(mixed_products.to_string().contains("mutually exclusive"));

        let snapshot_alias = parse_source_run(vec![
            OsString::from("--emit-olean-snapshot=./input.lean"),
            OsString::from("input.lean"),
        ])
        .expect_err("a snapshot must not overwrite or alias its source");
        assert!(snapshot_alias.to_string().contains("aliases source input"));

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
                .contains("final command did not produce a closed Nat, String, or Bool value")
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
            at: None,
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
            at: None,
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
            at: None,
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

        // with_source_seed is ordinary admission. The old seed catch-all
        // rendered this as `seed` / exit 1.
        let seed_exhausted = fln::EngineAdmissionError::AllocationFailure {
            resource: "seed declaration table",
            requested: usize::MAX,
        };
        assert_eq!(
            admission_error_disposition(&seed_exhausted),
            ("resource", false, 3)
        );

        let open_graph = fln::EngineExecutionError::MissingSourceImports {
            module: fln::Name::from_components(["Main"]),
            imports: vec![fln::Name::from_components(["Missing"])],
        };
        assert_eq!(
            execution_error_disposition(&open_graph),
            ("module-graph", false, 1)
        );
        let empty_entry = fln::EngineExecutionError::EmptySourceEntry {
            module: fln::Name::from_components(["Main"]),
        };
        assert_eq!(
            execution_error_disposition(&empty_entry),
            ("module-graph", false, 1)
        );
        let module_budget = fln::EngineExecutionError::SourceModuleLimit {
            observed: 2,
            limit: 1,
        };
        assert_eq!(
            execution_error_disposition(&module_budget),
            ("resource", false, 3)
        );
        let visibility = fln::EngineExecutionError::SourceModuleVisibility {
            module: fln::Name::from_components(["B"]),
            declaration: fln::Name::from_components(["borrowed"]),
            referenced: fln::Name::from_components(["leaked"]),
            owner: fln::Name::from_components(["A"]),
        };
        assert_eq!(
            execution_error_disposition(&visibility),
            ("module-graph", false, 1)
        );
        let visibility_budget = fln::EngineExecutionError::SourceDependencyPresentationLimit {
            observed: 2,
            limit: 1,
        };
        assert_eq!(
            execution_error_disposition(&visibility_budget),
            ("resource", false, 3)
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
    fn mixed_lean_source_never_prints_checks_before_a_prefix_vm_failure() {
        let kernel = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
        let engine = fln::Engine::with_source_seed(fln::EngineAdmissionLimits::new(kernel))
            .expect("the source seed reaches both checker seats")
            .into_complete()
            .expect("the source seed answers completely");
        let outcome = engine
            .execute_source_commands_with_checks(
                b"def prefix : Nat := 7\n#check prefix",
                &fln::KVMap::new(),
                fln::EngineExecutionLimits::new(kernel),
            )
            .expect("the real mixed source pipeline completes before the planted VM exit");
        let fln::Outcome::Complete(mut completed) = outcome else {
            panic!("the real mixed source pipeline must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        let usage = match &completed.batch.executions[0].exit {
            fln::VmExit::Returned(returned) => returned.usage,
            fln::VmExit::Panicked { .. } | fln::VmExit::Refused { .. } => {
                panic!("the planted prefix begins as a normal return"); // ubs:ignore — test-only diagnostic.
            }
        };
        completed.batch.executions[0].exit = fln::VmExit::Panicked {
            message: "planted prefix panic".to_owned(),
            usage,
        };

        let output = render_lean_source_commands(&completed);
        assert_eq!(output.exit_code, 1);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.starts_with("lean: program-panic: "));
        assert!(output.stderr.contains("source command 0 panicked"));
        assert!(output.stderr.contains("planted prefix panic"));
        assert!(!output.stderr.contains("prefix : Nat"));
    }

    #[test]
    fn imported_entry_never_prints_after_a_module_prefix_vm_failure() {
        let kernel = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
        let engine = fln::Engine::with_source_seed(fln::EngineAdmissionLimits::new(kernel))
            .expect("the source seed reaches both checker seats")
            .into_complete()
            .expect("the source seed answers completely");
        let base = fln::Name::from_components(["Base"]);
        let main = fln::Name::from_components(["Main"]);
        let modules = [
            fln::SourceModuleInput {
                name: &base,
                source: b"#check Nat\n#eval 7\ndef imported : Nat := 7",
            },
            fln::SourceModuleInput {
                name: &main,
                source: b"import Base\n#check imported",
            },
        ];
        let outcome = engine
            .execute_source_modules_with_entry_checks(
                &modules,
                &main,
                &fln::KVMap::new(),
                fln::EngineExecutionLimits::new(kernel),
            )
            .expect("the imported entry completes before the planted VM exit");
        let fln::Outcome::Complete(mut completed) = outcome else {
            panic!("the imported entry must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(completed.dependency_command_count, 3);
        assert_eq!(completed.dependency_execution_command_indices, [1, 2]);

        let exact_indices = completed.dependency_execution_command_indices.clone();
        completed.dependency_execution_command_indices.pop();
        let mismatch = render_lean_source_module_commands(&completed);
        assert_eq!(mismatch.exit_code, 4);
        assert!(mismatch.stdout.is_empty());
        assert!(mismatch.stderr.starts_with("lean: internal-fault: "));
        assert!(
            mismatch
                .stderr
                .contains("index table did not cover every execution")
        );
        completed.dependency_execution_command_indices = exact_indices;

        completed.dependency_execution_command_indices[0] = completed.dependency_command_count;
        let out_of_range = render_lean_source_module_commands(&completed);
        assert_eq!(out_of_range.exit_code, 4);
        assert!(out_of_range.stdout.is_empty());
        assert!(out_of_range.stderr.starts_with("lean: internal-fault: "));
        assert!(
            out_of_range
                .stderr
                .contains("not strictly increasing in range")
        );
        completed.dependency_execution_command_indices[0] = 1;

        let prefix = completed
            .dependency_prefix
            .as_mut()
            .expect("the imported evaluation is the real query prefix");
        let usage = match &prefix.executions[0].exit {
            fln::VmExit::Returned(returned) => returned.usage,
            fln::VmExit::Panicked { .. } | fln::VmExit::Refused { .. } => {
                panic!("the planted imported evaluation begins as a normal return"); // ubs:ignore — test-only diagnostic.
            }
        };
        prefix.executions[0].exit = fln::VmExit::Panicked {
            message: "planted imported panic".to_owned(),
            usage,
        };

        let output = render_lean_source_module_commands(&completed);
        assert_eq!(output.exit_code, 1);
        assert!(output.stdout.is_empty());
        assert!(output.stderr.starts_with("lean: program-panic: "));
        assert!(output.stderr.contains("source command 1 panicked"));
        assert!(!output.stderr.contains("source command 0 panicked"));
        assert!(output.stderr.contains("planted imported panic"));
        assert!(!output.stderr.contains("imported : Nat"));
    }

    #[test]
    fn source_run_failure_details_are_bounded_and_marked() {
        let output = source_failure(
            "execution",
            &"x".repeat(5000),
            true,
            SourcePresentation::Fln { json: true },
            1,
        );
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
        assert!(help.stdout.contains("ordered bounded #eval commands"));
        assert!(
            help.stdout
                .contains("final command's exact executed artifact")
        );
        assert!(help.stdout.contains("fln olean diff"));
        assert!(help.stdout.contains("fln ilean inspect"));

        let error = run([OsString::from("olean"), OsString::from("decode")]);
        assert_eq!(error.exit_code, 2);
        assert!(error.stdout.is_empty());
        assert!(error.stderr.contains("unknown olean subcommand"));
    }

    // ---- trust surfaces ----------------------------------------------------

    fn unique_scratch_root(label: &str) -> PathBuf {
        let unique = format!(
            "fln-cli-trust-surface-{label}-{}-{}",
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
        std::fs::create_dir_all(&root).expect("create trust-surface scratch root");
        root
    }

    /// One real checked environment, emitted through the product door, as an
    /// import-free non-module snapshot: the same artifact class the bounded
    /// check-olean and trust surfaces consume.
    fn checked_snapshot_fixture(root: &std::path::Path) -> PathBuf {
        let source = root.join("answer_source.lean");
        std::fs::write(&source, "def answer : Nat := 40 + 2\n#eval answer\n")
            .expect("write trust-surface source fixture");
        let snapshot = root.join("answer_snapshot.olean");
        let output = run([
            OsString::from("run"),
            OsString::from("--emit-olean-snapshot"),
            snapshot.clone().into_os_string(),
            source.clone().into_os_string(),
        ]);
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(snapshot.is_file(), "the snapshot must be published");
        snapshot
    }

    #[test]
    fn identity_reports_baked_suite_lock_facts() {
        let robot = run([OsString::from("identity"), OsString::from("--json")]);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stderr.is_empty());
        assert!(robot.stdout.contains("\"schema\":\"fln.identity/1\""));
        assert!(
            robot
                .stdout
                .contains("\"modes\":[\"faithful\",\"sound\",\"frontier\"]")
        );

        // The baked reference pin must equal the SUITE.lock row this tree
        // carries — identity derives, it never transcribes.
        let lock = std::fs::read_to_string(repository_path("SUITE.lock")).expect("read SUITE.lock");
        let tag = lock
            .lines()
            .find_map(|line| {
                let rest = line.strip_prefix("reference ")?;
                rest.split_ascii_whitespace()
                    .find_map(|word| word.strip_prefix("tag="))
            })
            .expect("SUITE.lock carries a reference row");
        assert!(
            robot
                .stdout
                .contains(&format!("\"reference\":{{\"tag\":\"{tag}\"")),
            "identity must report the SUITE.lock reference tag {tag}"
        );

        let human = run([OsString::from("identity")]);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stdout.contains("fln identity"));
        assert!(human.stdout.contains(&format!("reference pin: {tag}")));
        assert!(human.stdout.contains("modes: faithful, sound, frontier"));
    }

    #[test]
    fn audit_tcb_inventories_axioms_over_a_closed_set() {
        let root = unique_scratch_root("audit");
        let snapshot = checked_snapshot_fixture(&root);
        let robot = run([
            OsString::from("audit"),
            OsString::from("--tcb"),
            OsString::from("--json"),
            snapshot.clone().into_os_string(),
        ]);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stdout.contains("\"schema\":\"fln.audit-tcb/1\""));
        assert!(robot.stdout.contains("\"modules\":1"));
        assert!(
            robot.stdout.contains("\"name\":\"Nat.add\""),
            "the remaining primitive addition axiom must appear in the inventory: {}",
            robot.stdout
        );
        assert!(
            !robot.stdout.contains("\"name\":\"Nat\""),
            "the checked Nat inductive must not be inventoried as an axiom"
        );
        assert!(!robot.stdout.contains("\"unsafe\":true"));

        let human = run([
            OsString::from("audit"),
            OsString::from("--tcb"),
            snapshot.into_os_string(),
        ]);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stdout.contains("trust surface inventory: complete"));
        assert!(human.stdout.contains("axiom Nat.add"));
        assert!(!human.stdout.lines().any(|line| line.trim() == "axiom Nat"));
        assert!(human.stdout.contains("scope: decoded declarations only"));

        let missing_flag = run([
            OsString::from("audit"),
            root.join("x.olean").into_os_string(),
        ]);
        assert_eq!(missing_flag.exit_code, 2);
        assert!(missing_flag.stderr.contains("audit requires --tcb"));
    }

    #[test]
    fn why_trusts_traces_a_target_to_its_axioms() {
        let root = unique_scratch_root("why-trusts");
        let snapshot = checked_snapshot_fixture(&root);
        let robot = run([
            OsString::from("why-trusts"),
            OsString::from("--json"),
            OsString::from("answer"),
            snapshot.clone().into_os_string(),
        ]);
        assert_eq!(robot.exit_code, 0, "{}", robot.stderr);
        assert!(robot.stdout.contains("\"schema\":\"fln.why-trusts/1\""));
        assert!(robot.stdout.contains("\"target\":\"answer\""));
        assert!(robot.stdout.contains("\"kind\":\"definition\""));
        assert!(
            robot.stdout.contains("\"axioms\":[\"Nat.add\"]"),
            "the trust closure must reach addition without inventing a Nat axiom: {}",
            robot.stdout
        );
        assert!(robot.stdout.contains("\"truncated\":false"));

        let human = run([
            OsString::from("why-trusts"),
            OsString::from("answer"),
            snapshot.into_os_string(),
        ]);
        assert_eq!(human.exit_code, 0, "{}", human.stderr);
        assert!(human.stdout.contains("why-trusts: answer"));
        assert!(human.stdout.contains("axioms: Nat.add\n"));
        assert!(human.stdout.contains(
            "recursor rules, instance selections, and rewrite provenance are not traversed"
        ));

        let absent = run([
            OsString::from("why-trusts"),
            OsString::from("NoSuch.Constant"),
            root.join("answer_snapshot.olean").into_os_string(),
        ]);
        assert_eq!(absent.exit_code, 1);
        assert!(absent.stderr.contains("is not present in the supplied set"));
    }

    #[test]
    fn check_olean_receipts_chain_and_refuse_overwrite() {
        let base_name = fln::Name::from_components(["Fixture", "RcptBase"]);
        let child_name = fln::Name::from_components(["Fixture", "RcptChild"]);
        let base = empty_olean_fixture(&[]);
        let child = empty_olean_fixture(&[fln::OleanModuleImport {
            module: base_name.clone(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        }]);
        let total = base.len() + child.len();
        let root = unique_scratch_root("receipts");
        let receipts = root.join("run.receipts.jsonl");
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
            false,
            Some(receipts.clone()),
        );
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stdout.contains("receipts: 2 module rows"));
        assert!(receipts.is_file(), "the receipt set must be published");

        let text = std::fs::read_to_string(&receipts).expect("read the receipt set");
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 3, "two module rows plus one summary row");
        assert!(lines[0].contains(
            "\"prev\":\"0000000000000000000000000000000000000000000000000000000000000000\""
        ));
        let row_hash = |line: &str| {
            line.split("\"rowHash\":\"")
                .nth(1)
                .and_then(|rest| rest.split('"').next())
                .expect("module rows carry rowHash")
                .to_owned()
        };
        assert_eq!(
            lines[1]
                .split("\"prev\":\"")
                .nth(1)
                .and_then(|rest| rest.split('"').next()),
            Some(row_hash(lines[0]).as_str()),
            "row two must chain to row one"
        );
        assert!(lines[2].contains("\"kind\":\"summary\""));
        assert!(lines[2].contains(&format!("\"prev\":\"{}\"", row_hash(lines[1]))));
        assert!(lines.iter().all(|line| line.contains(RECEIPT_SET_SCHEMA)));

        let again = check_olean_module_bytes(
            vec![
                NamedOleanBytes {
                    name: fln::Name::from_components(["Fixture", "RcptChild"]),
                    bytes: empty_olean_fixture(&[fln::OleanModuleImport {
                        module: fln::Name::from_components(["Fixture", "RcptBase"]),
                        import_all: false,
                        is_exported: false,
                        is_meta: false,
                    }]),
                    server_bytes: None,
                    private_bytes: None,
                },
                NamedOleanBytes {
                    name: fln::Name::from_components(["Fixture", "RcptBase"]),
                    bytes: empty_olean_fixture(&[]),
                    server_bytes: None,
                    private_bytes: None,
                },
            ],
            total,
            true,
            Some(receipts),
        );
        assert_eq!(again.exit_code, 1);
        assert!(
            again
                .stderr
                .contains("refusing to overwrite existing receipt set")
        );
    }
}
