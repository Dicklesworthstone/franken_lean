//! A named-module auditor: capture exactly the transitive artifact closure, then
//! send every declaration through the existing K1/independent-checker council.
//! No source elaboration, upstream process, import cache, or trusted-import bypass.
use fln::{
    Budget, Engine, Environment, KVMap, LeafView, Name, OleanCheckLimits, OleanModuleInput, Outcome,
};
use fln_cli::MultiplexerOutput;
use fln_server::json_string as quote;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::io::Read;
use std::num::NonZeroUsize;
use std::path::{Component, Path, PathBuf};

const STACK_BYTES: usize = 64 * 1024 * 1024;
const DEFAULT_BYTES: usize = 256 * 1024 * 1024;
const MAX_ROOTS: usize = 64;
const MAX_NAME_BYTES: usize = 16 * 1024;
const MAX_NAME_DEPTH: usize = 128;
pub(super) const HELP: &str = "Usage: fln check-module [--json] [--jobs N] [--max-bytes BYTES] MODULE ROOT...\n\nCheck one compiled module and every transitive import through K1 and the\nindependent checker. ROOTs are explicit .olean search directories; no\nambient LEAN_PATH, source files, cache records or upstream executables are used.\nOnly the requested closure is read, not unrelated artifacts under those roots.\nAmbiguous modules and traversed symlinks are refused. All companion parts\ncome from the same root. --max-bytes bounds the captured closure together\n(default 256 MiB); --jobs is 1..64 (default 1).\n\nThe fln.check-module/1 report names every checked module and the content\nhashes of its captured parts. Success is declaration checking relative to\nthe artifacts' axioms, not validation of the axioms or execution of extensions.\nIt is not a whole-library, source-elaboration or full Lean compatibility claim.\n\nExit: 0 complete; 1 failed; 2 usage; 3 inconclusive/resource; 4 internal fault.\n";

struct Config {
    module: Name,
    roots: Vec<PathBuf>,
    max_bytes: usize,
    jobs: NonZeroUsize,
    json: bool,
}
struct Failure {
    code: u8,
    class: &'static str,
    detail: String,
}
type Result<T> = std::result::Result<T, Failure>;
impl Failure {
    fn new(code: u8, class: &'static str, detail: impl Into<String>) -> Self {
        Self {
            code,
            class,
            detail: detail.into(),
        }
    }
    fn input(detail: impl Into<String>) -> Self {
        Self::new(1, "input", detail)
    }
    fn resource(detail: impl Into<String>) -> Self {
        Self::new(3, "resource", detail)
    }
    fn usage(detail: impl Into<String>) -> Self {
        Self::new(2, "usage", detail)
    }
    fn io(path: &Path, error: std::io::Error) -> Self {
        Self::input(format!("{}: {error}", path.display()))
    }
    fn render(self, json: bool) -> MultiplexerOutput {
        let detail = fln_core::outcome::BoundedText::new(self.detail);
        let outcome = match self.code {
            2 => "usage-error",
            3 => "inconclusive",
            4 => "internal-fault",
            _ => "failed",
        };
        let (stdout, stderr) = if json {
            (
                format!(
                    "{{\"schema\":\"fln.check-module/1\",\"outcome\":{},\"authority\":false,\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n",
                    quote(outcome),
                    quote(self.class),
                    quote(detail.text()),
                    detail.truncated()
                ),
                String::new(),
            )
        } else {
            (
                String::new(),
                format!("fln check-module: {}: {}\n", self.class, detail.text()),
            )
        };
        MultiplexerOutput {
            stdout,
            stderr,
            exit_code: self.code,
        }
    }
}

fn decimal(value: &OsString, flag: &str) -> Result<usize> {
    let value = value
        .to_str()
        .filter(|s| !s.is_empty() && s.bytes().all(|c| c.is_ascii_digit()))
        .ok_or_else(|| Failure::usage(format!("{flag} requires a decimal nonnegative integer")))?;
    value
        .parse()
        .map_err(|_| Failure::usage(format!("{flag} exceeds this platform's integer range")))
}
fn parse(arguments: Vec<OsString>) -> Result<Config> {
    let mut json = false;
    let mut max_bytes = None;
    let mut jobs = None;
    let mut positional = Vec::new();
    let mut options = true;
    let mut args = arguments.into_iter();
    while let Some(argument) = args.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && argument == "--json" {
            if json {
                return Err(Failure::usage("--json may be supplied only once"));
            }
            json = true;
            continue;
        }
        let text = argument.to_str().unwrap_or("");
        if options && (text == "--max-bytes" || text.starts_with("--max-bytes=")) {
            if max_bytes.is_some() {
                return Err(Failure::usage("--max-bytes may be supplied only once"));
            }
            let value = match text.strip_prefix("--max-bytes=") {
                Some(s) => OsString::from(s),
                None => args
                    .next()
                    .ok_or_else(|| Failure::usage("--max-bytes requires a value"))?,
            };
            max_bytes = Some(decimal(&value, "--max-bytes")?);
            continue;
        }
        if options && (text == "--jobs" || text.starts_with("--jobs=")) {
            if jobs.is_some() {
                return Err(Failure::usage("--jobs may be supplied only once"));
            }
            let value = match text.strip_prefix("--jobs=") {
                Some(s) => OsString::from(s),
                None => args
                    .next()
                    .ok_or_else(|| Failure::usage("--jobs requires a value"))?,
            };
            let n = decimal(&value, "--jobs")?;
            if !(1..=64).contains(&n) {
                return Err(Failure::usage("--jobs must be in 1..64"));
            }
            jobs = NonZeroUsize::new(n);
            continue;
        }
        if options && argument.as_encoded_bytes().first() == Some(&b'-') {
            return Err(Failure::usage(format!(
                "unknown option {}",
                argument.to_string_lossy()
            )));
        }
        if positional.len() > MAX_ROOTS {
            return Err(Failure::usage("at most 64 search roots are permitted"));
        }
        positional.push(argument);
    }
    if positional.len() < 2 {
        return Err(Failure::usage(
            "a dotted module name and at least one search root are required",
        ));
    }
    let text = positional[0]
        .to_str()
        .filter(|s| !s.is_empty() && s.len() <= MAX_NAME_BYTES)
        .ok_or_else(|| Failure::usage("module name must be nonempty UTF-8 within 16 KiB"))?;
    let module = Name::from_components(text.split('.'));
    module_path(&module).map_err(|e| Failure::usage(e.detail))?;
    Ok(Config {
        module,
        roots: positional.into_iter().skip(1).map(PathBuf::from).collect(),
        max_bytes: max_bytes.unwrap_or(DEFAULT_BYTES),
        jobs: jobs.unwrap_or(NonZeroUsize::MIN),
        json,
    })
}

fn module_path(name: &Name) -> Result<PathBuf> {
    let mut names = Vec::new();
    let mut cursor = name.clone();
    let mut bytes = 0usize;
    while !cursor.is_anonymous() {
        if names.len() >= MAX_NAME_DEPTH {
            return Err(Failure::resource("module name exceeds 128 components"));
        }
        let LeafView::Str(part) = cursor.leaf_view() else {
            return Err(Failure::input("module names require textual components"));
        };
        bytes = bytes
            .checked_add(part.len())
            .filter(|n| *n <= MAX_NAME_BYTES)
            .ok_or_else(|| Failure::resource("module name exceeds 16 KiB"))?;
        let mut path_parts = Path::new(part).components();
        if part.is_empty()
            || part.ends_with(['.', ' '])
            || part.chars().any(|c| {
                c.is_control() || matches!(c, '/' | '\\' | ':' | '<' | '>' | '"' | '|' | '?' | '*')
            })
            || !matches!(path_parts.next(), Some(Component::Normal(_)))
            || path_parts.next().is_some()
        {
            return Err(Failure::input(
                "module name contains an unsafe filesystem component",
            ));
        }
        names.push(part.to_owned());
        cursor = cursor.parent();
    }
    if names.is_empty() {
        return Err(Failure::input("anonymous module names are not files"));
    }
    names.reverse();
    let mut path = names.iter().collect::<PathBuf>();
    // Append, rather than replacing a suffix in a quoted imported component.
    let mut filename = path
        .file_name()
        .ok_or_else(|| Failure::input("module has no filename"))?
        .to_os_string();
    filename.push(".olean");
    path.set_file_name(filename);
    Ok(path)
}

fn roots(paths: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let mut result = BTreeSet::new();
    for path in paths {
        let metadata = std::fs::symlink_metadata(path).map_err(|e| Failure::io(path, e))?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(Failure::input(format!(
                "search root {} must be a real directory",
                path.display()
            )));
        }
        let canonical = path.canonicalize().map_err(|e| Failure::io(path, e))?;
        if !result.insert(canonical) {
            return Err(Failure::input("the same search root was supplied twice"));
        }
    }
    Ok(result.into_iter().collect())
}

/// Inspect every component below the selected root, including absent ancestors.
fn present(root: &Path, relative: &Path) -> Result<Option<PathBuf>> {
    let mut path = root.to_path_buf();
    let count = relative.components().count();
    for (index, component) in relative.components().enumerate() {
        let Component::Normal(component) = component else {
            return Err(Failure::input("module path is not relative"));
        };
        path.push(component);
        let metadata = match std::fs::symlink_metadata(&path) {
            Ok(m) => m,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(Failure::io(&path, e)),
        };
        if metadata.file_type().is_symlink() {
            return Err(Failure::input(format!(
                "refusing symlink {}",
                path.display()
            )));
        }
        if index + 1 < count && !metadata.is_dir() {
            return Err(Failure::input(format!(
                "{} is not a directory",
                path.display()
            )));
        }
        if index + 1 == count && !metadata.is_file() {
            return Err(Failure::input(format!(
                "{} is not a regular artifact",
                path.display()
            )));
        }
    }
    Ok(Some(path))
}

struct Module {
    name: Name,
    parts: [Option<Vec<u8>>; 3],
}
impl Module {
    fn input(&self) -> OleanModuleInput<'_> {
        OleanModuleInput {
            name: &self.name,
            artifact: self.parts[0].as_deref().expect("captured public part"),
            server_artifact: self.parts[1].as_deref(),
            private_artifact: self.parts[2].as_deref(),
        }
    }
}
fn capture_file(path: &Path, remaining: usize) -> Result<Vec<u8>> {
    let file = std::fs::File::open(path).map_err(|e| Failure::io(path, e))?;
    let metadata = file.metadata().map_err(|e| Failure::io(path, e))?;
    if !metadata.is_file() {
        return Err(Failure::input(format!(
            "{} is not a regular artifact",
            path.display()
        )));
    }
    if metadata.len() > remaining as u64 {
        return Err(Failure::resource(format!(
            "{} exceeds the remaining closure byte budget ({remaining})",
            path.display()
        )));
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(metadata.len() as usize)
        .map_err(|_| Failure::resource("could not allocate artifact buffer"))?;
    file.take((remaining as u64).saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|e| Failure::io(path, e))?;
    if bytes.len() > remaining {
        return Err(Failure::resource(
            "artifact grew beyond the closure byte budget",
        ));
    }
    Ok(bytes)
}
fn capture(config: &Config, search: &[PathBuf]) -> Result<(Vec<Module>, usize)> {
    let mut pending = BTreeSet::from([config.module.clone()]);
    let mut loaded = BTreeMap::new();
    let mut used = 0usize;
    let limits = OleanCheckLimits::new(config.max_bytes, Budget::for_stack_bytes(STACK_BYTES));
    while let Some(name) = pending.pop_first() {
        if loaded.contains_key(&name) {
            continue;
        }
        let relative = module_path(&name)?;
        let label = name.to_display_string();
        let mut selected = None;
        for root in search {
            let paths = [
                present(root, &relative)?,
                present(root, &relative.with_extension("olean.server"))?,
                present(root, &relative.with_extension("olean.private"))?,
            ];
            if paths[0].is_none() && (paths[1].is_some() || paths[2].is_some()) {
                return Err(Failure::input(format!(
                    "{} has orphan companion parts under {}",
                    label,
                    root.display()
                )));
            }
            if paths[0].is_some() && selected.replace(paths).is_some() {
                return Err(Failure::input(format!(
                    "module {label} occurs under multiple search roots"
                )));
            }
        }
        let paths = selected.ok_or_else(|| {
            Failure::input(format!(
                "module {label} is absent from the explicit search roots"
            ))
        })?;
        if paths[1].is_some() != paths[2].is_some() {
            return Err(Failure::input(format!(
                "module {label} requires both .olean.server and .olean.private companions"
            )));
        }
        let mut parts: [Option<Vec<u8>>; 3] = Default::default();
        for (slot, path) in parts.iter_mut().zip(paths) {
            if let Some(path) = path {
                let bytes = capture_file(&path, config.max_bytes.saturating_sub(used))?;
                used = used
                    .checked_add(bytes.len())
                    .ok_or_else(|| Failure::resource("closure byte accounting overflow"))?;
                *slot = Some(bytes);
            }
        }
        let imports =
            fln::olean_module_imports(parts[0].as_deref().expect("public part"), limits.decode)
                .map_err(|e| {
                    Failure::new(
                        if e.is_resource_exhaustion() { 3 } else { 1 },
                        "decode",
                        format!("{label}: {e}"),
                    )
                })?;
        loaded.insert(name.clone(), Module { name, parts });
        for dependency in imports {
            if !loaded.contains_key(&dependency) {
                pending.insert(dependency);
            }
            if loaded.len().saturating_add(pending.len()) > limits.max_modules {
                return Err(Failure::resource(
                    "module closure exceeds the module count budget",
                ));
            }
        }
    }
    Ok((loaded.into_values().collect(), used))
}

fn checking_failure(error: fln::OleanCheckError) -> Failure {
    use fln::{EngineAdmissionError as A, OleanCheckError as E};
    fn admission(error: &A) -> (u8, &'static str) {
        match error {
            A::BatchDeclaration { error, .. } => admission(error),
            A::CouncilNoAnswer { .. } | A::CouncilHalted { .. } => (3, "inconclusive"),
            A::AllocationFailure { .. } => (3, "resource"),
            A::CheckerBridge { .. } | A::UnexpectedPublication { .. } => (4, "internal-fault"),
            A::KernelRejected { .. } => (1, "kernel-rejection"),
            _ => (1, "admission"),
        }
    }
    let (code, class) = match &error {
        E::Admission(error) => admission(error),
        E::Decode(error) | E::ModuleDecode { error, .. } if error.is_resource_exhaustion() => {
            (3, "resource")
        }
        E::ModuleLimit { .. }
        | E::TotalBytesLimit { .. }
        | E::DeclarationLimit { .. }
        | E::DependencyPresentationLimit { .. }
        | E::AllocationFailure { .. }
        | E::HostMemory { .. } => (3, "resource"),
        E::InternalInvariant { .. } => (4, "internal-fault"),
        E::IndependentReadingDiffers { .. } => (3, "inconclusive"),
        _ => (1, "check"),
    };
    Failure::new(code, class, error.to_string())
}

fn check(config: Config) -> Result<MultiplexerOutput> {
    let search = roots(&config.roots)?;
    let (modules, bytes) = capture(&config, &search)?;
    let inputs: Vec<_> = modules.iter().map(Module::input).collect();
    let checked = Engine::from_environment(Environment::new())
        .check_olean_modules_scheduled(
            &inputs,
            &KVMap::new(),
            OleanCheckLimits::new(config.max_bytes, Budget::for_stack_bytes(STACK_BYTES)),
            fln::OleanFrontierJobs {
                threads: config.jobs,
                worker_stack_bytes: STACK_BYTES,
            },
            None,
        )
        .map_err(checking_failure)?;
    let checked = match checked {
        Outcome::Complete(checked) => checked,
        Outcome::Inconclusive(reason) => {
            return Err(Failure::new(3, "inconclusive", format!("{reason:?}")));
        }
        Outcome::InternalFault(fault) => {
            return Err(Failure::new(4, "internal-fault", format!("{fault:?}")));
        }
    };
    if checked.modules.len() != modules.len()
        || checked
            .modules
            .iter()
            .map(|m| &m.name)
            .collect::<BTreeSet<_>>()
            != modules.iter().map(|m| &m.name).collect::<BTreeSet<_>>()
    {
        return Err(Failure::new(
            4,
            "internal-fault",
            "council result does not cover the requested module closure",
        ));
    }
    let declarations: usize = checked.modules.iter().map(|m| m.declarations.len()).sum();
    let axioms = checked
        .engine
        .environment()
        .constants()
        .filter(|(_, c)| matches!(c, fln::ConstantInfo::Axiom(_)))
        .count();
    let stdout = if config.json {
        let mut rows = Vec::new();
        for module in &checked.modules {
            let captured = modules
                .binary_search_by(|m| m.name.cmp(&module.name))
                .ok()
                .map(|index| &modules[index])
                .ok_or_else(|| {
                    Failure::new(
                        4,
                        "internal-fault",
                        "checked module has no captured artifact",
                    )
                })?;
            let hashes: Vec<_> = captured
                .parts
                .iter()
                .map(|p| {
                    p.as_ref().map_or_else(
                        || "null".to_owned(),
                        |p| quote(&fln::artifact_byte_hash(p).to_hex()),
                    )
                })
                .collect();
            rows.push(format!("{{\"module\":{},\"declarations\":{},\"publicHash\":{},\"serverHash\":{},\"privateHash\":{}}}",quote(&module.name.to_display_string()),module.declarations.len(),hashes[0],hashes[1],hashes[2]));
        }
        format!(
            "{{\"schema\":\"fln.check-module/1\",\"outcome\":\"complete\",\"authority\":true,\"requestedModule\":{},\"scope\":\"transitive-import-closure\",\"trust\":\"recheck\",\"checkers\":[\"k1\",\"independent\"],\"moduleCount\":{},\"declarations\":{declarations},\"axiomDeclarations\":{axioms},\"artifactBytes\":{bytes},\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},\"executed\":false,\"extensionsInterpreted\":false,\"modules\":[{}]}}\n",
            quote(&config.module.to_display_string()),
            modules.len(),
            quote(&checked.base_logical_root.0.to_hex()),
            quote(&checked.result_logical_root.0.to_hex()),
            rows.join(",")
        )
    } else {
        format!(
            "Checked {} and its complete import closure: {} modules, {declarations} declarations, {bytes} captured artifact bytes.\nK1 and the independent checker agreed; {axioms} axiom declarations are assumptions, not proved facts.\nNo code executed; no environment extensions interpreted. Unrelated modules were not checked.\n",
            config.module.to_display_string(),
            modules.len()
        )
    };
    Ok(MultiplexerOutput {
        stdout,
        stderr: String::new(),
        exit_code: 0,
    })
}

pub(super) fn run(arguments: Vec<OsString>) -> MultiplexerOutput {
    if arguments
        .iter()
        .take_while(|arg| *arg != "--")
        .any(|arg| arg == "--help" || arg == "-h")
    {
        return MultiplexerOutput {
            stdout: HELP.to_owned(),
            stderr: String::new(),
            exit_code: 0,
        };
    }
    let json = arguments
        .iter()
        .take_while(|arg| *arg != "--")
        .any(|arg| arg == "--json");
    let config = match parse(arguments) {
        Ok(c) => c,
        Err(e) => return e.render(json),
    };
    let worker = std::thread::Builder::new()
        .name("fln-check-module".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || check(config));
    match worker {
        Ok(worker) => match worker.join() {
            Ok(Ok(output)) => output,
            Ok(Err(error)) => error.render(json),
            Err(_) => Failure::new(
                4,
                "internal-fault",
                "module checking worker panicked; no result is authoritative",
            )
            .render(json),
        },
        Err(error) => Failure::new(
            3,
            "resource",
            format!("could not start bounded checking worker: {error}"),
        )
        .render(json),
    }
}

/// The standalone front doors share this routing; the embeddable council remains
/// the authority. Language-server transport keeps its existing binary adapter.
pub(super) fn dispatch(arguments: Vec<OsString>) -> MultiplexerOutput {
    let mut arguments = arguments.into_iter();
    let first = arguments.next();
    if first.as_deref() == Some(std::ffi::OsStr::new("check-module")) {
        return run(arguments.collect());
    }
    let help = first.as_deref().is_some_and(|s| s == "--help" || s == "-h");
    let mut output = fln_cli::run(first.into_iter().chain(arguments));
    if help && output.exit_code == 0 {
        output.stdout.push_str("\nNamed-module auditing:\n");
        output.stdout.push_str(HELP);
    }
    output
}
