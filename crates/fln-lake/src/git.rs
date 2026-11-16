//! Bounded Git jobs for Lake's optional dependency-fetching capability.
//!
//! Every job has an isolated home, disabled hooks and ambient Git configuration,
//! separate bounded output captures, a deadline, and an owned process group.
//! A clone remains private until its requested revision has resolved to a commit
//! and its detached HEAD has been checked. Failed jobs are retained for diagnosis;
//! they never become package checkouts.

use super::{LakeFetchError, manifest_quote};
use fln_hash::domain::{Digest, Domain, DomainHasher, hash};
use fln_unsafe_abi::process::ProcessGroupChild;
use std::ffi::OsString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

const MAX_OUTPUT: u64 = 1024 * 1024;
const MAX_EXECUTABLE: u64 = 64 * 1024 * 1024;
const MAX_INDEX: u64 = 64 * 1024 * 1024;
const MAX_ARGUMENT: usize = 16 * 1024;
const DEADLINE: Duration = Duration::from_secs(120);
static NEXT_JOB: AtomicU64 = AtomicU64::new(0);

fn io_error(error: io::Error) -> LakeFetchError {
    LakeFetchError::Io(error.to_string())
}

fn invalid(detail: impl Into<String>) -> LakeFetchError {
    LakeFetchError::InvalidInput(detail.into())
}

fn resource(detail: impl Into<String>) -> LakeFetchError {
    LakeFetchError::Resource(detail.into())
}

fn private_directory(path: &Path) -> io::Result<()> {
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(path)
}

/// Inspect before normalizing: a symlink followed by ".." is not a safe parent.
fn directory(path: &Path, create: bool) -> Result<PathBuf, LakeFetchError> {
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir().map_err(io_error)?.join(path)
    };
    if absolute.components().count() > 128 {
        return Err(resource("Git package path exceeds 128 components"));
    }
    let mut cursor = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::CurDir => continue,
            Component::ParentDir => {
                cursor.pop();
            }
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                cursor.push(component.as_os_str());
            }
        }
        match fs::symlink_metadata(&cursor) {
            Ok(metadata) if metadata.is_dir() && !metadata.file_type().is_symlink() => {}
            Ok(_) => {
                return Err(invalid(format!(
                    "Git package parent is not a real directory (refusing symlink): {}",
                    cursor.display()
                )));
            }
            Err(error) if create && error.kind() == io::ErrorKind::NotFound => {
                private_directory(&cursor).map_err(io_error)?;
            }
            Err(error) => return Err(io_error(error)),
        }
    }
    fs::canonicalize(cursor).map_err(io_error)
}

fn new_job(parent: &Path) -> Result<PathBuf, LakeFetchError> {
    for _ in 0..64 {
        let path = parent.join(format!(
            ".fln-git-{}-{}",
            std::process::id(),
            NEXT_JOB.fetch_add(1, Ordering::Relaxed)
        ));
        match private_directory(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(io_error(error)),
        }
    }
    Err(resource("could not reserve a private Git job directory"))
}

fn create_capture(path: &Path) -> Result<File, LakeFetchError> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    options.open(path).map_err(io_error)
}

fn read_bounded(path: &Path, bound: u64) -> Result<Vec<u8>, LakeFetchError> {
    let metadata = fs::symlink_metadata(path).map_err(io_error)?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(invalid("Git input is not a regular nonsymlink file"));
    }
    let file = File::open(path).map_err(io_error)?;
    if !file.metadata().map_err(io_error)?.is_file() {
        return Err(invalid("Git input is not a regular file"));
    }
    let mut bytes = Vec::new();
    file.take(bound + 1)
        .read_to_end(&mut bytes)
        .map_err(io_error)?;
    if bytes.len() as u64 > bound {
        return Err(resource(format!("Git input exceeds {bound} bytes")));
    }
    Ok(bytes)
}

fn capture_prefix(path: &Path) -> Result<(Vec<u8>, u64), LakeFetchError> {
    let metadata = fs::symlink_metadata(path).map_err(io_error)?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(invalid("Git output capture is not a regular nonsymlink file"));
    }
    let file = File::open(path).map_err(io_error)?;
    let metadata = file.metadata().map_err(io_error)?;
    if !metadata.is_file() {
        return Err(invalid("Git output capture is not a regular file"));
    }
    let length = metadata.len();
    let mut bytes = Vec::new();
    file.take(MAX_OUTPUT)
        .read_to_end(&mut bytes)
        .map_err(io_error)?;
    Ok((bytes, length))
}

fn executable_digest(path: &Path) -> Result<Digest, LakeFetchError> {
    let file = File::open(path).map_err(io_error)?;
    let metadata = file.metadata().map_err(io_error)?;
    if !metadata.is_file() || metadata.len() > MAX_EXECUTABLE {
        return Err(resource(
            "Git executable is not a regular file within 64 MiB",
        ));
    }
    let mut hasher = DomainHasher::new(Domain::ArtifactProduct);
    let mut reader = file.take(MAX_EXECUTABLE + 1);
    let mut buffer = [0u8; 16 * 1024];
    let mut bytes = 0u64;
    loop {
        let count = reader.read(&mut buffer).map_err(io_error)?;
        if count == 0 {
            break;
        }
        bytes += count as u64;
        if bytes > MAX_EXECUTABLE {
            return Err(resource("Git executable grew beyond 64 MiB"));
        }
        hasher.update(&buffer[..count]);
    }
    Ok(hasher.finalize())
}

pub(super) fn executable() -> Result<PathBuf, LakeFetchError> {
    if !cfg!(any(target_os = "linux", target_os = "macos")) {
        return Err(LakeFetchError::CapabilityDenied(
            "Git dependency fetching needs supported process-group cancellation; materialize the locked package manually on this platform".to_owned(),
        ));
    }
    let search = std::env::var_os("PATH").unwrap_or_default();
    for parent in std::env::split_paths(&search) {
        let candidate = parent.join("git");
        if !candidate.is_file() {
            continue;
        }
        let candidate = fs::canonicalize(candidate).map_err(io_error)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if fs::metadata(&candidate)
                .map_err(io_error)?
                .permissions()
                .mode()
                & 0o111
                == 0
            {
                continue;
            }
        }
        return Ok(candidate);
    }
    Err(LakeFetchError::CapabilityDenied(
        "external tool git is unavailable; install Git or materialize the locked package manually (D2)".to_owned(),
    ))
}

fn redacted(text: &str) -> String {
    if let Some((scheme, address)) = text.split_once("://") {
        let address = address.split(['?', '#']).next().unwrap_or(address);
        let boundary = address.find('/').unwrap_or(address.len());
        let (authority, path) = address.split_at(boundary);
        let authority = authority
            .rsplit_once('@')
            .map_or(authority, |(_, host)| host);
        return format!("{scheme}://{authority}{path}");
    }
    text.to_owned()
}

struct Runner {
    executable: PathBuf,
    digest: Digest,
    job: PathBuf,
    sequence: usize,
    deadline: Duration,
}

impl Runner {
    fn new(job: PathBuf) -> Result<Self, LakeFetchError> {
        let executable = executable()?;
        let digest = executable_digest(&executable)?;
        private_directory(&job.join("home")).map_err(io_error)?;
        private_directory(&job.join("hooks")).map_err(io_error)?;
        create_capture(&job.join("config"))?;
        Ok(Self {
            executable,
            digest,
            job,
            sequence: 0,
            deadline: DEADLINE,
        })
    }

    fn run(
        &mut self,
        cwd: &Path,
        label: &str,
        arguments: &[OsString],
    ) -> Result<Vec<u8>, LakeFetchError> {
        self.run_with_index(cwd, label, arguments, None)
    }

    fn run_with_index(
        &mut self,
        cwd: &Path,
        label: &str,
        arguments: &[OsString],
        input_index: Option<&Path>,
    ) -> Result<Vec<u8>, LakeFetchError> {
        if arguments.len() > 128
            || arguments
                .iter()
                .any(|argument| argument.len() > MAX_ARGUMENT)
        {
            return Err(resource("Git argument budget exceeded"));
        }
        if arguments.iter().any(|argument| argument.to_str().is_none()) {
            return Err(invalid(
                "Git arguments must be UTF-8 for exact job provenance",
            ));
        }
        if executable_digest(&self.executable)? != self.digest {
            return Err(invalid(
                "Git executable changed during dependency resolution",
            ));
        }
        let input_index_digest = input_index
            .map(|path| {
                read_bounded(path, MAX_INDEX)
                    .map(|bytes| hash(Domain::ArtifactProduct, &bytes).to_hex())
            })
            .transpose()?;
        let index = self.sequence;
        self.sequence += 1;
        let stdout_path = self.job.join(format!("{index}.stdout"));
        let stderr_path = self.job.join(format!("{index}.stderr"));
        let stdout = create_capture(&stdout_path)?;
        let stderr = create_capture(&stderr_path)?;
        let mut command = Command::new(&self.executable);
        command
            .current_dir(cwd)
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("HOME", self.job.join("home"))
            .env("XDG_CONFIG_HOME", self.job.join("home"))
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", self.job.join("config"))
            .env("GIT_TERMINAL_PROMPT", "0")
            .env("GIT_OPTIONAL_LOCKS", "0")
            .env("GIT_ALLOW_PROTOCOL", "file:http:https")
            .env("GIT_CEILING_DIRECTORIES", &self.job)
            .env("LC_ALL", "C")
            .args(["-c", "credential.helper=", "-c", "core.fsmonitor=false"])
            .arg("-c")
            .arg(format!("core.hooksPath={}", self.job.join("hooks").display()))
            .args(["-c", "gc.auto=0", "-c", "maintenance.auto=false"])
            .args(["-c", "submodule.recurse=false"])
            .args([
                "-c",
                "http.userAgent=franken_lean-agent (+https://github.com/Dicklesworthstone/franken_lean)",
            ])
            .args(arguments)
            .stdin(Stdio::null())
            .stdout(Stdio::from(stdout))
            .stderr(Stdio::from(stderr));
        if let Some(index) = input_index {
            command.env("GIT_INDEX_FILE", index);
        }
        // Preserve explicit proxy routing without recording credential-bearing values.
        for key in [
            "HTTP_PROXY",
            "HTTPS_PROXY",
            "ALL_PROXY",
            "NO_PROXY",
            "http_proxy",
            "https_proxy",
            "all_proxy",
            "no_proxy",
        ] {
            if let Some(value) = std::env::var_os(key) {
                command.env(key, value);
            }
        }
        let started = Instant::now();
        let mut child = ProcessGroupChild::spawn(&mut command).map_err(|error| {
            if error.kind() == io::ErrorKind::Unsupported {
                LakeFetchError::CapabilityDenied(error.to_string())
            } else {
                io_error(error)
            }
        })?;
        let pid = child.id();
        let mut stopped = None;
        let status = loop {
            let size = fs::metadata(&stdout_path).map_err(io_error)?.len()
                + fs::metadata(&stderr_path).map_err(io_error)?.len();
            if size > MAX_OUTPUT || started.elapsed() >= self.deadline {
                stopped = Some(if size > MAX_OUTPUT {
                    "output-limit"
                } else {
                    "deadline"
                });
                break child.terminate().map_err(io_error)?;
            }
            if let Some(status) = child.try_wait().map_err(io_error)? {
                break status;
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        let (stdout, stdout_bytes) = capture_prefix(&stdout_path)?;
        let (stderr, stderr_bytes) = capture_prefix(&stderr_path)?;
        if stdout_bytes.saturating_add(stderr_bytes) > MAX_OUTPUT {
            stopped = Some("output-limit");
        }
        let args = arguments
            .iter()
            .map(|argument| manifest_quote(&redacted(&argument.to_string_lossy())))
            .collect::<Vec<_>>()
            .join(",");
        let receipt = format!(
            "{{\"schema\":\"fln.git-job/1\",\"command\":{},\"executable\":{},\"executable_digest\":{},\"argv\":[{args}],\"input_index_digest\":{},\"pid\":{pid},\"exit\":{},\"stop\":{},\"stdout_bytes\":{stdout_bytes},\"stderr_bytes\":{stderr_bytes},\"stdout_hashed_bytes\":{},\"stderr_hashed_bytes\":{},\"stdout_prefix_digest\":{},\"stderr_prefix_digest\":{}}}\n",
            manifest_quote(label),
            manifest_quote(&self.executable.to_string_lossy()),
            manifest_quote(&self.digest.to_hex()),
            input_index_digest.as_deref().map_or("null".to_owned(), manifest_quote),
            status.code().map_or("null".to_owned(), |code| code.to_string()),
            stopped.map_or("null".to_owned(), manifest_quote),
            stdout.len(),
            stderr.len(),
            manifest_quote(&hash(Domain::OperationalMeta, &stdout).to_hex()),
            manifest_quote(&hash(Domain::OperationalMeta, &stderr).to_hex()),
        );
        create_capture(&self.job.join(format!("{index}.receipt.json")))?
            .write_all(receipt.as_bytes())
            .map_err(io_error)?;
        if let Some(reason) = stopped {
            return Err(resource(format!(
                "Git {label} stopped at its {reason}; receipt: {}",
                self.job.display()
            )));
        }
        if !status.success() {
            let mut detail = String::from_utf8_lossy(&stderr).into_owned();
            for argument in arguments {
                let argument = argument.to_string_lossy();
                if argument.contains("://") {
                    detail = detail.replace(argument.as_ref(), &redacted(&argument));
                }
            }
            return Err(LakeFetchError::GitFailed {
                command: label.to_owned(),
                stderr: detail,
            });
        }
        if executable_digest(&self.executable)? != self.digest {
            return Err(invalid("Git executable changed while a dependency job ran"));
        }
        Ok(stdout)
    }

    fn text(&mut self, cwd: &Path, label: &str, args: &[&str]) -> Result<String, LakeFetchError> {
        let args: Vec<_> = args.iter().map(OsString::from).collect();
        String::from_utf8(self.run(cwd, label, &args)?)
            .map(|text| text.trim_end_matches(['\r', '\n']).to_owned())
            .map_err(|_| invalid("Git returned non-UTF-8 revision metadata"))
    }
}

pub(super) fn package_directory(name: &str) -> Result<String, LakeFetchError> {
    if name.len() > MAX_ARGUMENT {
        return Err(resource("Git package name exceeds its byte budget"));
    }
    let mut rendered = String::new();
    let mut quoted = false;
    for character in name.chars() {
        match character {
            '«' if !quoted => quoted = true,
            '»' if quoted => quoted = false,
            '«' | '»' => return Err(invalid("invalid quoted Git package name")),
            _ => rendered.push(character),
        }
    }
    if quoted
        || rendered.is_empty()
        || matches!(rendered.as_str(), "." | "..")
        || rendered.contains(['/', '\\'])
        || rendered.chars().any(char::is_control)
        || rendered.starts_with(".fln-")
    {
        return Err(invalid(
            "Git package name is not a single safe directory component",
        ));
    }
    Ok(rendered)
}

pub(super) fn full_revision(revision: &str) -> bool {
    matches!(revision.len(), 40 | 64) && revision.bytes().all(|byte| byte.is_ascii_hexdigit())
}

pub(super) fn source_url(cwd: &Path, url: &str) -> Result<OsString, LakeFetchError> {
    if url.is_empty() || url.len() > MAX_ARGUMENT || url.chars().any(char::is_control) {
        return Err(invalid("empty, oversized or control-bearing Git URL"));
    }
    if url.starts_with("https://") || url.starts_with("http://") {
        return Ok(url.into());
    }
    if url.contains("://") || url.contains("::") || url.contains('@') && url.contains(':') {
        return Err(LakeFetchError::CapabilityDenied(
            "Git fetching supports HTTP(S) and local repository paths; other transport helpers require a separate capability".to_owned(),
        ));
    }
    let path = if Path::new(url).is_absolute() {
        PathBuf::from(url)
    } else {
        cwd.join(url)
    };
    // Canonicalization also turns a leading "-" into an ordinary absolute operand.
    Ok(directory(&path, false)?.into_os_string())
}

pub(super) struct Prepared {
    pub directory: PathBuf,
    pub destination: PathBuf,
    pub revision: String,
}

struct PreviousCheckout {
    revision: String,
    recovery: PathBuf,
    moved: bool,
}

struct PendingCheckout {
    stage: PathBuf,
    destination: PathBuf,
    revision: String,
    previous: Option<PreviousCheckout>,
    installed: bool,
}

pub(super) struct Transaction {
    packages: PathBuf,
    runner: Runner,
    pending: Vec<PendingCheckout>,
    reused: Vec<(PathBuf, String)>,
    committed: bool,
}

fn checkout_revision(checkout: &Path) -> Result<String, LakeFetchError> {
    let git = directory(&checkout.join(".git"), false)?;
    let bytes = read_bounded(&git.join("HEAD"), 4096)?;
    let revision = std::str::from_utf8(&bytes)
        .map_err(|_| invalid("existing Git HEAD is not UTF-8"))?
        .trim();
    if !full_revision(revision) {
        return Err(invalid(
            "existing Git checkout must have a full detached HEAD; no files were changed",
        ));
    }
    Ok(revision.to_owned())
}

/// Compare the old worktree using the new clone's isolated config and index.
/// Reading the existing checkout's Git config could execute filters or helpers.
fn check_existing_worktree(
    runner: &mut Runner,
    stage: &Path,
    destination: &Path,
    old_revision: &str,
    new_revision: &str,
) -> Result<(), LakeFetchError> {
    if checkout_revision(destination)? != old_revision {
        return Err(invalid(
            "existing Git HEAD changed during dependency resolution",
        ));
    }
    // The existing index can contain staged edits absent from the worktree.
    // Copy its bounded bytes into the private job and let Git read that index
    // with the fresh clone's config, never the old checkout's config. A split
    // index whose shared file is unavailable fails without changing either tree.
    let index = read_bounded(&destination.join(".git/index"), MAX_INDEX)?;
    let private_index = runner.job.join(format!("old-index-{}", runner.sequence));
    create_capture(&private_index)?
        .write_all(&index)
        .map_err(io_error)?;
    let prefix = vec![
        OsString::from("--git-dir"),
        stage.join(".git").into_os_string(),
        OsString::from("--work-tree"),
        destination.to_path_buf().into_os_string(),
    ];
    let mut cached_args = prefix.clone();
    cached_args.extend(
        [
            "diff-index",
            "--cached",
            "--raw",
            "--no-ext-diff",
            "--no-textconv",
            old_revision,
            "--",
        ]
        .iter()
        .map(OsString::from),
    );
    if !runner
        .run_with_index(
            stage,
            "check-existing-index",
            &cached_args,
            Some(&private_index),
        )?
        .is_empty()
    {
        return Err(invalid(
            "existing Git checkout has staged changes; no files were changed",
        ));
    }
    runner.text(stage, "index-old-tree", &["read-tree", old_revision])?;
    let entries = runner.text(stage, "inspect-old-tree", &["ls-files", "--stage"])?;
    if entries.lines().any(|line| line.starts_with("160000 ")) {
        return Err(LakeFetchError::CapabilityDenied(
            "replacing a checkout containing Git submodules requires explicit submodule support"
                .to_owned(),
        ));
    }
    let mut refresh_args = prefix.clone();
    refresh_args.extend(
        ["update-index", "--really-refresh"]
            .iter()
            .map(OsString::from),
    );
    match runner.run(stage, "refresh-old-worktree", &refresh_args) {
        Ok(_) => {}
        Err(LakeFetchError::GitFailed { .. }) => {
            return Err(invalid(
                "existing Git checkout has modified files; no files were changed",
            ));
        }
        Err(error) => return Err(error),
    }
    // diff-files compares the old index directly with the old worktree. Status
    // would also compare that index with the fresh clone's newer HEAD and would
    // incorrectly reject every revision change as staged modifications.
    let mut worktree_args = prefix.clone();
    worktree_args.extend(
        ["diff-files", "--raw", "--no-ext-diff", "--no-textconv", "--"]
            .iter()
            .map(OsString::from),
    );
    let mut other_args = prefix.clone();
    other_args.extend(
        ["ls-files", "--others", "--exclude-standard"]
            .iter()
            .map(OsString::from),
    );
    let mut ignored_args = prefix;
    ignored_args.extend(
        ["ls-files", "--others", "--ignored", "--exclude-standard"]
            .iter()
            .map(OsString::from),
    );
    let changed = !runner
        .run(stage, "check-existing-worktree", &worktree_args)?
        .is_empty();
    let untracked = !runner
        .run(stage, "check-existing-untracked", &other_args)?
        .is_empty();
    let ignored = !runner
        .run(stage, "check-existing-ignored", &ignored_args)?
        .is_empty();
    runner.text(stage, "restore-new-index", &["read-tree", new_revision])?;
    if changed || untracked || ignored {
        return Err(invalid(
            "existing Git checkout has modified, untracked, or ignored files; no files were changed",
        ));
    }
    Ok(())
}

impl Transaction {
    pub fn new(packages: &Path) -> Result<Self, LakeFetchError> {
        let packages = directory(packages, true)?;
        let runner = Runner::new(new_job(&packages)?)?;
        Ok(Self {
            packages,
            runner,
            pending: Vec::new(),
            reused: Vec::new(),
            committed: false,
        })
    }

    pub fn prepare(
        &mut self,
        name: &str,
        url: &str,
        revision: Option<&str>,
        cwd: &Path,
    ) -> Result<Prepared, LakeFetchError> {
        self.prepare_inner(name, url, revision, cwd, false)
    }

    pub fn prepare_update(
        &mut self,
        name: &str,
        url: &str,
        revision: Option<&str>,
        cwd: &Path,
    ) -> Result<Prepared, LakeFetchError> {
        self.prepare_inner(name, url, revision, cwd, true)
    }

    fn prepare_inner(
        &mut self,
        name: &str,
        url: &str,
        revision: Option<&str>,
        cwd: &Path,
        replace_clean: bool,
    ) -> Result<Prepared, LakeFetchError> {
        let component = package_directory(name)?;
        let destination = self.packages.join(component);
        if self
            .pending
            .iter()
            .any(|pending| pending.destination == destination)
            || self.reused.iter().any(|(path, _)| path == &destination)
        {
            return Err(invalid("Git package was selected twice"));
        }
        let url = source_url(cwd, url)?;
        let revision = revision.unwrap_or("HEAD");
        if revision.is_empty()
            || revision.starts_with('-')
            || revision.len() > MAX_ARGUMENT
            || revision.chars().any(char::is_control)
        {
            return Err(invalid("invalid Git revision selector"));
        }
        let stage = self
            .runner
            .job
            .join(format!("checkout-{}", self.runner.sequence));
        let args = vec![
            OsString::from("clone"),
            OsString::from("--quiet"),
            OsString::from("--no-checkout"),
            OsString::from("--no-hardlinks"),
            OsString::from("--template="),
            OsString::from("--"),
            url,
            stage.clone().into_os_string(),
        ];
        // Clone outside any workspace repository so its local configuration
        // cannot add include files, filters, or transport rewrites.
        let job = self.runner.job.clone();
        self.runner.run(&job, "clone", &args)?;
        let resolved = self.runner.text(
            &stage,
            "resolve-commit",
            &[
                "rev-parse",
                "--verify",
                "--end-of-options",
                &format!("{revision}^{{commit}}"),
            ],
        );
        let commit = match resolved {
            Err(LakeFetchError::GitFailed { .. }) => self.runner.text(
                &stage,
                "resolve-remote-branch",
                &[
                    "rev-parse",
                    "--verify",
                    "--end-of-options",
                    &format!("refs/remotes/origin/{revision}^{{commit}}"),
                ],
            )?,
            other => other?,
        };
        if !full_revision(&commit) || full_revision(revision) && !commit.eq_ignore_ascii_case(revision) {
            return Err(invalid(
                "Git did not resolve the requested revision to its full commit",
            ));
        }
        self.runner.text(
            &stage,
            "checkout",
            &["checkout", "--quiet", "--detach", &commit, "--"],
        )?;
        if self
            .runner
            .text(&stage, "verify-head", &["rev-parse", "--verify", "HEAD"])?
            != commit
        {
            return Err(invalid(
                "detached Git HEAD differs from its resolved commit",
            ));
        }
        let previous = match fs::symlink_metadata(&destination) {
            Ok(metadata) if metadata.is_dir() && !metadata.file_type().is_symlink() => {
                let old_revision = checkout_revision(&destination)?;
                if old_revision == commit {
                    self.reused.push((destination.clone(), commit.clone()));
                    return Ok(Prepared {
                        directory: destination.clone(),
                        destination,
                        revision: commit,
                    });
                }
                if !replace_clean {
                    return Err(invalid(
                        "existing Git checkout is not at the requested detached commit; no files were changed",
                    ));
                }
                check_existing_worktree(
                    &mut self.runner,
                    &stage,
                    &destination,
                    &old_revision,
                    &commit,
                )?;
                Some(PreviousCheckout {
                    revision: old_revision,
                    recovery: self.runner.job.join(format!("previous-{}", self.pending.len())),
                    moved: false,
                })
            }
            Ok(_) => return Err(invalid("Git package destination is not a real directory")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => None,
            Err(error) => return Err(io_error(error)),
        };
        self.pending.push(PendingCheckout {
            stage: stage.clone(),
            destination: destination.clone(),
            revision: commit.clone(),
            previous,
            installed: false,
        });
        Ok(Prepared {
            directory: stage,
            destination,
            revision: commit,
        })
    }

    pub fn promote(&mut self) -> Result<(), LakeFetchError> {
        for (destination, revision) in &self.reused {
            if checkout_revision(destination)? != *revision {
                return Err(invalid("reused Git HEAD changed during dependency resolution"));
            }
        }
        for pending in &self.pending {
            directory(
                pending.destination.parent().expect("package has a parent"),
                false,
            )?;
            if checkout_revision(&pending.stage)? != pending.revision {
                return Err(invalid("staged Git HEAD changed during dependency resolution"));
            }
            if let Some(previous) = &pending.previous {
                check_existing_worktree(
                    &mut self.runner,
                    &pending.stage,
                    &pending.destination,
                    &previous.revision,
                    &pending.revision,
                )?;
            } else {
                match fs::symlink_metadata(&pending.destination) {
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => return Err(io_error(error)),
                    Ok(_) => {
                        return Err(invalid(
                            "Git destination appeared during dependency resolution",
                        ));
                    }
                }
            }
        }
        for pending in &mut self.pending {
            if let Some(previous) = &mut pending.previous {
                fs::rename(&pending.destination, &previous.recovery).map_err(io_error)?;
                previous.moved = true;
            }
            fs::rename(&pending.stage, &pending.destination).map_err(io_error)?;
            pending.installed = true;
        }
        Ok(())
    }

    /// Translate a final package location to the private checkout while resolving.
    pub fn materialized_directory(&self, path: &Path) -> PathBuf {
        for pending in &self.pending {
            if let Ok(relative) = path.strip_prefix(&pending.destination) {
                return pending.stage.join(relative);
            }
        }
        path.to_path_buf()
    }

    /// Keep private staging names out of path entries written to the manifest.
    pub fn published_directory(&self, path: &Path) -> PathBuf {
        for pending in &self.pending {
            if let Ok(relative) = path.strip_prefix(&pending.stage) {
                return pending.destination.join(relative);
            }
        }
        path.to_path_buf()
    }

    pub fn rollback(&mut self) -> Result<(), LakeFetchError> {
        for pending in self.pending.iter_mut().rev() {
            if pending.installed {
                fs::rename(&pending.destination, &pending.stage).map_err(|error| {
                    LakeFetchError::Io(format!(
                        "cannot roll back {} to private recovery {}: {error}",
                        pending.destination.display(),
                        pending.stage.display(),
                    ))
                })?;
                pending.installed = false;
            }
            if let Some(previous) = &mut pending.previous
                && previous.moved
            {
                fs::rename(&previous.recovery, &pending.destination).map_err(|error| {
                    LakeFetchError::Io(format!(
                        "cannot restore previous checkout {} from {}: {error}",
                        pending.destination.display(),
                        previous.recovery.display(),
                    ))
                })?;
                previous.moved = false;
            }
        }
        Ok(())
    }

    pub fn commit(&mut self) {
        self.committed = true;
    }
}

impl Drop for Transaction {
    fn drop(&mut self) {
        if !self.committed {
            // Normal error paths report rollback errors explicitly. Drop remains
            // a final best-effort recovery for an unwinding caller.
            let _ = self.rollback();
        }
    }
}

pub(super) fn fetch(
    packages: &Path,
    name: &str,
    url: &str,
    revision: Option<&str>,
) -> Result<PathBuf, LakeFetchError> {
    let cwd = std::env::current_dir().map_err(io_error)?;
    let mut transaction = Transaction::new(packages)?;
    let prepared = transaction.prepare(name, url, revision, &cwd)?;
    if !full_revision(&prepared.revision) || !prepared.directory.is_dir() {
        return Err(invalid("prepared Git checkout lost its verified identity"));
    }
    if let Err(error) = transaction.promote() {
        if let Err(rollback) = transaction.rollback() {
            return Err(LakeFetchError::Io(format!(
                "{error}; checkout rollback also failed: {rollback}",
            )));
        }
        return Err(error);
    }
    transaction.commit();
    Ok(prepared.destination)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(label: &str) -> (PathBuf, Runner) {
        let parent = fs::canonicalize(std::env::temp_dir()).unwrap().join(format!(
            "fln-git-test-{label}-{}-{}",
            std::process::id(),
            NEXT_JOB.fetch_add(1, Ordering::Relaxed)
        ));
        private_directory(&parent).unwrap();
        let runner = Runner::new(new_job(&parent).unwrap()).unwrap();
        (parent, runner)
    }

    fn repository(root: &Path, runner: &mut Runner) -> (PathBuf, String) {
        let repo = root.join("source");
        private_directory(&repo).unwrap();
        runner
            .text(&repo, "fixture-init", &["init", "--quiet"])
            .unwrap();
        fs::write(repo.join("lakefile.toml"), "name = \"dependency\"\n").unwrap();
        fs::write(repo.join("value.txt"), "original\n").unwrap();
        runner.text(&repo, "fixture-add", &["add", "."]).unwrap();
        runner
            .text(
                &repo,
                "fixture-commit",
                &[
                    "-c",
                    "user.name=Lake Test",
                    "-c",
                    "user.email=lake-test@example.invalid",
                    "commit",
                    "--quiet",
                    "-m",
                    "fixture",
                ],
            )
            .unwrap();
        let commit = runner
            .text(&repo, "fixture-head", &["rev-parse", "HEAD"])
            .unwrap();
        runner
            .text(&repo, "fixture-tag", &["tag", "release"])
            .unwrap();
        (repo, commit)
    }

    #[test]
    fn real_git_fetch_resolves_tags_and_preserves_existing_work() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("fetch");
        let (repo, commit) = repository(&root, &mut runner);
        let packages = root.join("packages");
        let checkout = fetch(
            &packages,
            "dependency",
            repo.to_str().unwrap(),
            Some("release"),
        )
        .unwrap();
        assert_eq!(
            read_bounded(&checkout.join(".git/HEAD"), 4096).unwrap(),
            format!("{commit}\n").as_bytes()
        );
        assert_eq!(
            fs::read_to_string(checkout.join("value.txt")).unwrap(),
            "original\n"
        );
        fs::write(checkout.join("value.txt"), "local edit\n").unwrap();
        assert_eq!(
            fetch(&packages, "dependency", repo.to_str().unwrap(), Some(&commit)).unwrap(),
            checkout,
        );
        assert_eq!(
            fs::read_to_string(checkout.join("value.txt")).unwrap(),
            "local edit\n"
        );
        assert!(fetch(&packages, "dependency", repo.to_str().unwrap(), Some("missing")).is_err());
        assert_eq!(
            fs::read_to_string(checkout.join("value.txt")).unwrap(),
            "local edit\n"
        );
        assert!(fs::read_dir(&packages).unwrap().any(|entry| {
            entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".fln-git-")
        }));
    }

    #[test]
    fn missing_revision_and_invalid_names_never_publish_checkouts() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("invalid");
        let (repo, _) = repository(&root, &mut runner);
        let packages = root.join("packages");
        assert!(fetch(&packages, "dependency", repo.to_str().unwrap(), Some("missing")).is_err());
        assert!(!packages.join("dependency").exists());
        for name in ["../escape", "a/b", "«../escape»", ".fln-git-reserved", "a\\b"] {
            assert!(fetch(&packages, name, repo.to_str().unwrap(), Some("release")).is_err());
        }
        assert!(!root.join("escape").exists());
        assert!(fetch(&packages, "safe", repo.to_str().unwrap(), Some("--orphan")).is_err());
        assert!(!packages.join("safe").exists());
    }

    #[test]
    fn publication_rollback_retains_private_checkouts_and_old_files() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("rollback");
        let (repo, _) = repository(&root, &mut runner);
        let packages = root.join("packages");
        let destination;
        let stage;
        {
            let mut transaction = Transaction::new(&packages).unwrap();
            let prepared = transaction
                .prepare("dependency", repo.to_str().unwrap(), Some("release"), &root)
                .unwrap();
            destination = prepared.destination;
            stage = prepared.directory;
            assert!(!destination.exists());
            transaction.promote().unwrap();
            assert!(destination.is_dir());
            // No commit: simulate failure of the subsequent manifest publication.
        }
        assert!(!destination.exists());
        assert_eq!(
            fs::read_to_string(stage.join("value.txt")).unwrap(),
            "original\n"
        );
    }

    #[test]
    fn deadline_and_output_budgets_stop_real_git_jobs() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("budgets");
        let (repo, _) = repository(&root, &mut runner);
        runner.deadline = Duration::ZERO;
        assert!(matches!(
            runner.text(&repo, "deadline", &["status", "--porcelain"]),
            Err(LakeFetchError::Resource(_))
        ));
        runner.deadline = DEADLINE;
        fs::write(repo.join("large.txt"), vec![b'x'; MAX_OUTPUT as usize + 1]).unwrap();
        runner
            .text(&repo, "fixture-add-large", &["add", "large.txt"])
            .unwrap();
        runner
            .text(
                &repo,
                "fixture-commit-large",
                &[
                    "-c",
                    "user.name=Lake Test",
                    "-c",
                    "user.email=lake-test@example.invalid",
                    "commit",
                    "--quiet",
                    "-m",
                    "large",
                ],
            )
            .unwrap();
        assert!(matches!(
            runner.text(&repo, "output-budget", &["show", "HEAD:large.txt"]),
            Err(LakeFetchError::Resource(_))
        ));
        assert_eq!(
            runner
                .text(&repo, "recovery", &["rev-parse", "--is-inside-work-tree"])
                .unwrap(),
            "true"
        );
    }
    fn commit_all(repo: &Path, runner: &mut Runner) -> String {
        runner.text(repo, "fixture-add", &["add", "."]).unwrap();
        runner
            .text(
                repo,
                "fixture-commit",
                &[
                    "-c",
                    "user.name=Lake Test",
                    "-c",
                    "user.email=lake-test@example.invalid",
                    "commit",
                    "--quiet",
                    "-m",
                    "next",
                ],
            )
            .unwrap();
        runner
            .text(repo, "fixture-head", &["rev-parse", "HEAD"])
            .unwrap()
    }

    fn root_package(root: &Path, contents: &str) -> PathBuf {
        let project = root.join("project");
        private_directory(&project).unwrap();
        fs::write(project.join("lakefile.toml"), contents).unwrap();
        project
    }

    #[test]
    fn update_materializes_git_subdirectories_and_internal_path_dependencies() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("update-subdir");
        let (repo, _) = repository(&root, &mut runner);
        private_directory(&repo.join("sub")).unwrap();
        private_directory(&repo.join("sub/leaf")).unwrap();
        fs::write(
            repo.join("sub/lakefile.toml"),
            "name = \"dependency\"\n[[require]]\nname = \"leaf\"\npath = \"leaf\"\n",
        )
        .unwrap();
        fs::write(repo.join("sub/leaf/lakefile.toml"), "name = \"leaf\"\n").unwrap();
        let commit = commit_all(&repo, &mut runner);
        runner.text(&repo, "fixture-tag", &["tag", "stable"]).unwrap();
        let project = root_package(
            &root,
            &format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\nrev = \"stable\"\nsubDir = \"sub\"\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        );
        let manifest = crate::update_manifest(&project).unwrap();
        assert_eq!(manifest.packages.len(), 2);
        let dependency = &manifest.packages[0];
        assert_eq!(dependency.entry_type, "git");
        assert_eq!(dependency.rev.as_deref(), Some(commit.as_str()));
        assert_eq!(dependency.input_rev.as_deref(), Some("stable"));
        assert_eq!(dependency.subdir.as_deref(), Some("sub"));
        assert!(dependency.dir.is_none());
        assert_eq!(
            manifest.packages[1].dir.as_deref(),
            Some(Path::new(".lake/packages/dependency/sub/leaf"))
        );
        let checkout = project.join(".lake/packages/dependency");
        assert_eq!(
            fs::read_to_string(checkout.join(".git/HEAD")).unwrap(),
            format!("{commit}\n")
        );
        assert!(checkout.join("sub/leaf/lakefile.toml").is_file());
        let bytes = fs::read_to_string(project.join("lake-manifest.json")).unwrap();
        assert!(!bytes.contains(".fln-git-"));
        let reloaded = crate::Manifest::parse_json(&bytes).unwrap();
        assert_eq!(reloaded.packages, manifest.packages);
        let repeated = crate::update_manifest(&project).unwrap();
        assert_eq!(repeated.packages, manifest.packages);
    }

    #[test]
    fn update_keeps_old_manifest_and_all_public_checkouts_on_resolution_failure() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("update-failure");
        let (repo, _) = repository(&root, &mut runner);
        let source = manifest_quote(repo.to_str().unwrap());
        let project = root_package(
            &root,
            &format!(
                "name = \"root\"\n[[require]]\nname = \"bad\"\ngit = {source}\nrev = \"missing\"\n[[require]]\nname = \"good\"\ngit = {source}\nrev = \"release\"\n",
            ),
        );
        crate::Manifest::new("previous").save_to_dir(&project).unwrap();
        let before = fs::read(project.join("lake-manifest.json")).unwrap();
        let error = crate::update_manifest(&project).unwrap_err();
        assert!(error.to_string().contains("bad"), "{error}");
        assert_eq!(
            fs::read(project.join("lake-manifest.json")).unwrap(),
            before
        );
        assert!(!project.join(".lake/packages/good").exists());
        assert!(!project.join(".lake/packages/bad").exists());
        assert_eq!(
            fs::read_to_string(repo.join("value.txt")).unwrap(),
            "original\n"
        );
    }

    #[test]
    fn update_rechecks_inputs_after_checked_git_configuration_loading() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("update-input-race");
        let (repo, _) = repository(&root, &mut runner);
        fs::write(repo.join("lakefile.lean"), "import Lake\n").unwrap();
        commit_all(&repo, &mut runner);
        let project = root_package(
            &root,
            &format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        );
        crate::Manifest::new("previous").save_to_dir(&project).unwrap();
        let before = fs::read(project.join("lake-manifest.json")).unwrap();
        let error = crate::update_manifest_with_lean::<crate::LakeUpdateError>(
            &project,
            |_, bytes| {
                assert_eq!(bytes, b"import Lake\n");
                fs::write(project.join("lakefile.toml"), "name = \"changed\"\n").unwrap();
                let mut config = crate::LakeConfig::parse_toml("name = \"dependency\"\n").unwrap();
                config.format = crate::LakeConfigFormat::Lean;
                Ok(config)
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("changed during"), "{error}");
        assert_eq!(
            fs::read(project.join("lake-manifest.json")).unwrap(),
            before
        );
        assert!(!project.join(".lake/packages/dependency").exists());
        assert_eq!(
            fs::read_to_string(project.join("lakefile.toml")).unwrap(),
            "name = \"changed\"\n"
        );
    }

    #[test]
    fn inherited_git_commits_are_immutable_and_direct_requirements_win() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("update-locks");
        let (repo, old_commit) = repository(&root, &mut runner);
        fs::write(repo.join("value.txt"), "new upstream\n").unwrap();
        let new_commit = commit_all(&repo, &mut runner);
        runner.text(&repo, "fixture-tag", &["tag", "latest"]).unwrap();
        let holder = root.join("holder");
        private_directory(&holder).unwrap();
        fs::write(
            holder.join("lakefile.toml"),
            format!(
                "name = \"holder\"\n[[require]]\nname = \"dependency\"\ngit = {}\nrev = \"latest\"\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        )
        .unwrap();
        let mut inherited = crate::Manifest::new("holder");
        inherited.packages.push(crate::ManifestPackageEntry {
            name: "dependency".to_owned(),
            scope: String::new(),
            entry_type: "git".to_owned(),
            dir: None,
            url: Some(repo.to_str().unwrap().to_owned()),
            rev: Some(old_commit.clone()),
            input_rev: Some("release".to_owned()),
            subdir: None,
            inherited: false,
            config_file: "lakefile.toml".to_owned(),
            manifest_file: Some(PathBuf::from("lake-manifest.json")),
        });
        inherited.save_to_dir(&holder).unwrap();
        let project = root_package(
            &root,
            "name = \"root\"\n[[require]]\nname = \"holder\"\npath = \"../holder\"\n",
        );
        let manifest = crate::update_manifest(&project).unwrap();
        let locked = manifest
            .packages
            .iter()
            .find(|entry| entry.name == "dependency")
            .unwrap();
        assert_eq!(locked.rev.as_deref(), Some(old_commit.as_str()));
        assert!(locked.inherited);
        assert_eq!(
            fs::read_to_string(project.join(".lake/packages/dependency/value.txt")).unwrap(),
            "original\n"
        );
        // A different workspace avoids changing a preexisting checkout while
        // proving that an inherited lock cannot override a direct requirement.
        let second = root.join("direct");
        private_directory(&second).unwrap();
        fs::write(
            second.join("lakefile.toml"),
            format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\nrev = \"latest\"\n[[require]]\nname = \"holder\"\npath = \"../holder\"\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        )
        .unwrap();
        let manifest = crate::update_manifest(&second).unwrap();
        let direct = manifest
            .packages
            .iter()
            .find(|entry| entry.name == "dependency")
            .unwrap();
        assert_eq!(direct.rev.as_deref(), Some(new_commit.as_str()));
        assert!(!direct.inherited);
    }

    #[cfg(unix)]
    #[test]
    fn update_rejects_symlinked_package_parents_and_checkout_configuration() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        use std::os::unix::fs::symlink;

        let (root, mut runner) = fixture("update-symlink");
        let (repo, _) = repository(&root, &mut runner);
        fs::rename(repo.join("lakefile.toml"), repo.join("actual.toml")).unwrap();
        symlink("actual.toml", repo.join("lakefile.toml")).unwrap();
        commit_all(&repo, &mut runner);
        let project = root_package(
            &root,
            &format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        );
        let error = crate::update_manifest(&project).unwrap_err();
        assert!(error.to_string().contains("symlink"), "{error}");
        assert!(!project.join("lake-manifest.json").exists());
        assert!(!project.join(".lake/packages/dependency").exists());

        let other = root.join("unsafe-parent");
        private_directory(&other).unwrap();
        fs::write(
            other.join("lakefile.toml"),
            fs::read(project.join("lakefile.toml")).unwrap(),
        )
        .unwrap();
        symlink(&root, other.join(".lake")).unwrap();
        let error = crate::update_manifest(&other).unwrap_err();
        assert!(error.to_string().contains("symlink"), "{error}");
        assert!(!other.join("lake-manifest.json").exists());
        assert!(!root.join("packages").exists());
    }
    #[test]
    fn update_replaces_clean_revisions_and_preserves_dirty_checkout_and_manifest() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("update-revisions");
        let (repo, old_commit) = repository(&root, &mut runner);
        let project = root_package(
            &root,
            &format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\nrev = \"release\"\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        );
        crate::update_manifest(&project).unwrap();
        let checkout = project.join(".lake/packages/dependency");
        let git_config = checkout.join(".git/config");
        let config = fs::read_to_string(&git_config).unwrap();
        // An ambient helper in the old checkout must not be consulted while
        // deciding whether replacement is safe.
        fs::write(
            &git_config,
            format!("{config}\n[core]\n\tfsmonitor = definitely-missing-fsmonitor\n"),
        )
        .unwrap();
        fs::write(repo.join("value.txt"), "next release\n").unwrap();
        let new_commit = commit_all(&repo, &mut runner);
        runner.text(&repo, "fixture-tag", &["tag", "next"]).unwrap();
        fs::write(
            project.join("lakefile.toml"),
            format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\nrev = \"next\"\n",
                manifest_quote(repo.to_str().unwrap()),
            ),
        )
        .unwrap();
        let manifest = crate::update_manifest(&project).unwrap();
        assert_eq!(
            manifest.packages[0].rev.as_deref(),
            Some(new_commit.as_str())
        );
        assert_eq!(
            fs::read_to_string(checkout.join("value.txt")).unwrap(),
            "next release\n"
        );
        assert_eq!(checkout_revision(&checkout).unwrap(), new_commit);
        let before = fs::read(project.join("lake-manifest.json")).unwrap();
        fs::write(checkout.join("value.txt"), "user edit\n").unwrap();
        fs::write(
            project.join("lakefile.toml"),
            format!(
                "name = \"root\"\n[[require]]\nname = \"dependency\"\ngit = {}\nrev = {}\n",
                manifest_quote(repo.to_str().unwrap()),
                manifest_quote(&old_commit),
            ),
        )
        .unwrap();
        let error = crate::update_manifest(&project).unwrap_err();
        assert!(error.to_string().contains("modified"), "{error}");
        assert_eq!(
            fs::read(project.join("lake-manifest.json")).unwrap(),
            before
        );
        assert_eq!(
            fs::read_to_string(checkout.join("value.txt")).unwrap(),
            "user edit\n"
        );
        assert_eq!(checkout_revision(&checkout).unwrap(), new_commit);
    }

    #[test]
    fn replacing_checkout_rolls_back_and_detects_edits_before_publication() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("replace-rollback");
        let (repo, old_commit) = repository(&root, &mut runner);
        let packages = root.join("packages");
        let checkout = fetch(
            &packages,
            "dependency",
            repo.to_str().unwrap(),
            Some("release"),
        )
        .unwrap();
        fs::write(repo.join("value.txt"), "new tree\n").unwrap();
        let new_commit = commit_all(&repo, &mut runner);
        {
            let mut transaction = Transaction::new(&packages).unwrap();
            transaction
                .prepare_update(
                    "dependency",
                    repo.to_str().unwrap(),
                    Some(&new_commit),
                    &root,
                )
                .unwrap();
            transaction.promote().unwrap();
            assert_eq!(checkout_revision(&checkout).unwrap(), new_commit);
            transaction.rollback().unwrap();
            assert_eq!(checkout_revision(&checkout).unwrap(), old_commit);
            assert_eq!(
                fs::read_to_string(checkout.join("value.txt")).unwrap(),
                "original\n"
            );
        }
        let mut transaction = Transaction::new(&packages).unwrap();
        transaction
            .prepare_update(
                "dependency",
                repo.to_str().unwrap(),
                Some(&new_commit),
                &root,
            )
            .unwrap();
        fs::write(checkout.join("late.txt"), "edit after preparation\n").unwrap();
        let error = transaction.promote().unwrap_err();
        assert!(error.to_string().contains("untracked"), "{error}");
        transaction.rollback().unwrap();
        assert_eq!(checkout_revision(&checkout).unwrap(), old_commit);
        assert_eq!(
            fs::read_to_string(checkout.join("late.txt")).unwrap(),
            "edit after preparation\n"
        );
    }
    #[test]
    fn replacement_refuses_staged_only_changes_without_touching_the_existing_index() {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return;
        }
        let (root, mut runner) = fixture("replace-staged");
        let (repo, old_commit) = repository(&root, &mut runner);
        let packages = root.join("packages");
        let checkout = fetch(
            &packages,
            "dependency",
            repo.to_str().unwrap(),
            Some("release"),
        )
        .unwrap();
        fs::write(repo.join("value.txt"), "new release\n").unwrap();
        let next = commit_all(&repo, &mut runner);
        fs::write(checkout.join("value.txt"), "staged edit\n").unwrap();
        runner
            .text(&checkout, "fixture-stage-edit", &["add", "value.txt"])
            .unwrap();
        fs::write(checkout.join("value.txt"), "original\n").unwrap();
        let original_index = fs::read(checkout.join(".git/index")).unwrap();
        let mut transaction = Transaction::new(&packages).unwrap();
        let error = match transaction.prepare_update(
            "dependency",
            repo.to_str().unwrap(),
            Some(&next),
            &root,
        ) {
            Ok(_) => panic!("staged-only edit must prevent replacement"),
            Err(error) => error,
        };
        assert!(error.to_string().contains("staged"), "{error}");
        assert_eq!(checkout_revision(&checkout).unwrap(), old_commit);
        assert_eq!(
            fs::read(checkout.join(".git/index")).unwrap(),
            original_index
        );
        assert_eq!(
            fs::read_to_string(checkout.join("value.txt")).unwrap(),
            "original\n"
        );
    }
}
