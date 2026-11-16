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
                    "Git package parent is not a real directory: {}",
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
        let address = address.split_once('@').map_or(address, |(_, rest)| rest);
        let address = address.split(['?', '#']).next().unwrap_or(address);
        return format!("{scheme}://{address}");
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
        if arguments.len() > 128
            || arguments
                .iter()
                .any(|argument| argument.len() > MAX_ARGUMENT)
        {
            return Err(resource("Git argument budget exceeded"));
        }
        if executable_digest(&self.executable)? != self.digest {
            return Err(invalid(
                "Git executable changed during dependency resolution",
            ));
        }
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
        let capture = |path: &Path| match read_bounded(path, MAX_OUTPUT) {
            Ok(bytes) => Ok(Some(bytes)),
            Err(LakeFetchError::Resource(_)) => Ok(None),
            Err(error) => Err(error),
        };
        let (stdout, stderr) = match (capture(&stdout_path)?, capture(&stderr_path)?) {
            (Some(stdout), Some(stderr))
                if (stdout.len() + stderr.len()) as u64 <= MAX_OUTPUT =>
            {
                (stdout, stderr)
            }
            _ => {
                stopped = Some("output-limit");
                (Vec::new(), Vec::new())
            }
        };
        let args = arguments
            .iter()
            .map(|argument| manifest_quote(&redacted(&argument.to_string_lossy())))
            .collect::<Vec<_>>()
            .join(",");
        let receipt = format!(
            "{{\"schema\":\"fln.git-job/1\",\"command\":{},\"executable\":{},\"executable_digest\":{},\"argv\":[{args}],\"pid\":{pid},\"exit\":{},\"stop\":{},\"stdout_digest\":{},\"stderr_digest\":{}}}\n",
            manifest_quote(label),
            manifest_quote(&self.executable.to_string_lossy()),
            manifest_quote(&self.digest.to_hex()),
            status.code().map_or("null".to_owned(), |code| code.to_string()),
            stopped.map_or("null".to_owned(), manifest_quote),
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

fn source_url(cwd: &Path, url: &str) -> Result<OsString, LakeFetchError> {
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

pub(super) struct Transaction {
    packages: PathBuf,
    runner: Runner,
    pending: Vec<(PathBuf, PathBuf)>,
    promoted: usize,
    committed: bool,
}

impl Transaction {
    pub fn new(packages: &Path) -> Result<Self, LakeFetchError> {
        let packages = directory(packages, true)?;
        let runner = Runner::new(new_job(&packages)?)?;
        Ok(Self {
            packages,
            runner,
            pending: Vec::new(),
            promoted: 0,
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
        let component = package_directory(name)?;
        let destination = self.packages.join(component);
        if self.pending.iter().any(|(_, path)| path == &destination) {
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
        self.runner.run(&self.packages, "clone", &args)?;
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
        if self.runner.text(&stage, "verify-head", &["rev-parse", "--verify", "HEAD"])? != commit {
            return Err(invalid("detached Git HEAD differs from its resolved commit"));
        }
        // A preexisting checkout is never changed by a fetch. Transactional
        // manifest updates handle revision replacements separately.
        match fs::symlink_metadata(&destination) {
            Ok(metadata) if metadata.is_dir() && !metadata.file_type().is_symlink() => {
                let git = directory(&destination.join(".git"), false)?;
                let head = read_bounded(&git.join("HEAD"), 4096)?;
                if std::str::from_utf8(&head).ok().map(str::trim) != Some(commit.as_str()) {
                    return Err(invalid(
                        "existing Git checkout is not at the requested detached commit; no files were changed",
                    ));
                }
                return Ok(Prepared {
                    directory: destination.clone(),
                    destination,
                    revision: commit,
                });
            }
            Ok(_) => return Err(invalid("Git package destination is not a real directory")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(io_error(error)),
        }
        self.pending.push((stage.clone(), destination.clone()));
        Ok(Prepared {
            directory: stage,
            destination,
            revision: commit,
        })
    }

    pub fn promote(&mut self) -> Result<(), LakeFetchError> {
        for (_, destination) in &self.pending {
            match fs::symlink_metadata(destination) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(io_error(error)),
                Ok(_) => {
                    return Err(invalid(
                        "Git destination appeared during dependency resolution",
                    ));
                }
            }
            directory(destination.parent().expect("package has a parent"), false)?;
        }
        for (stage, destination) in &self.pending {
            fs::rename(stage, destination).map_err(io_error)?;
            self.promoted += 1;
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
            for (stage, destination) in self.pending[..self.promoted].iter().rev() {
                // Preserve partial work privately if later publication fails.
                let _ = fs::rename(destination, stage);
            }
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
    transaction.promote()?;
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
}
