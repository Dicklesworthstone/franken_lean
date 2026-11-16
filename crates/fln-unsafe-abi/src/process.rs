//! Owned process groups for optional external-tool jobs (plan D2).
//!
//! A group is established by the OS before the executable starts. Completion
//! is observed without reaping its leader, remaining group members are killed,
//! and only then is the leader reaped. Retaining that leader prevents its PID
//! from being recycled between observation and cancellation.
//!
//! This owner requires the process's normal SIGCHLD disposition and exclusive
//! responsibility for reaping its child. An embedder must not install automatic
//! child reaping or concurrently wait for this child outside the owner. An
//! observed loss of ownership permanently refuses further numeric-PID signals.
//!
//! The caller owns argument, environment, input/output and deadline policy.
//! This boundary does not trust the external tool or sandbox descendants that
//! deliberately leave their process group. Only Linux and macOS are supported;
//! other platforms refuse before starting the command.

use std::io;
use std::process::{Child, Command, ExitStatus};

/// Exclusive ownership of a child and its cancellation process group.
///
/// The inner `Child` is never exposed. Every completion path cancels remaining
/// group members before reaping the leader; Drop also cancels unfinished jobs.
pub struct ProcessGroupChild {
    child: Child,
    status: Option<ExitStatus>,
    // A terminal failure also revokes permission to signal a numeric PID.
    // In particular, ECHILD must never turn into a later Drop-time kill.
    failure: Option<io::Error>,
}

impl ProcessGroupChild {
    /// Start a command in its own process group, without a shell.
    pub fn spawn(command: &mut Command) -> io::Result<Self> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
            let child = command.spawn()?;
            Ok(Self {
                child,
                status: None,
                failure: None,
            })
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            let _ = command;
            Err(unsupported())
        }
    }

    /// The group leader's process identifier, for provenance only.
    pub fn id(&self) -> u32 {
        self.child.id()
    }

    /// Poll without reaping, then cancel descendants before collecting status.
    pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        if let Some(error) = &self.failure {
            return Err(copy_error(error));
        }
        if let Some(status) = self.status {
            return Ok(Some(status));
        }
        if !self.observe_exit(true)? {
            return Ok(None);
        }
        self.finish(true).map(Some)
    }

    /// Wait for completion, cancel descendants, and retain the leader's status.
    ///
    /// Deadline-governed callers should poll `try_wait` and call `terminate`
    /// on expiry rather than use this blocking operation.
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        if let Some(error) = &self.failure {
            return Err(copy_error(error));
        }
        if let Some(status) = self.status {
            return Ok(status);
        }
        // Match Child::wait: close an owned stdin pipe before waiting for EOF.
        drop(self.child.stdin.take());
        self.observe_exit(false)?;
        self.finish(true)
    }

    /// Kill a still-owned process group and reap its leader.
    ///
    /// This is idempotent after successful completion. A failed group signal
    /// remains an error even if killing only the leader succeeds. Ownership
    /// failures are retained and never followed by a numeric-PID signal.
    pub fn terminate(&mut self) -> io::Result<ExitStatus> {
        if let Some(error) = &self.failure {
            return Err(copy_error(error));
        }
        if let Some(status) = self.status {
            return Ok(status);
        }
        let exited = self.observe_exit(true)?;
        self.finish(exited)
    }

    fn observe_exit(&mut self, nonblocking: bool) -> io::Result<bool> {
        match observe_exit(self.child.id(), nonblocking) {
            Ok(exited) => Ok(exited),
            Err(error) => {
                self.failure = Some(copy_error(&error));
                Err(error)
            }
        }
    }

    // Called only after waitid confirmed ownership without reaping. The caller
    // must keep exclusive reaper ownership through the final Child::wait.
    fn finish(&mut self, already_exited: bool) -> io::Result<ExitStatus> {
        let group_error = signal_group(self.child.id()).err();
        if !already_exited {
            // Also settle the owned leader if it left its original group.
            // Its PID remains reserved until the wait below.
            if let Err(kill_error) = self.child.kill() {
                match self.observe_exit(true) {
                    Ok(true) => {}
                    Ok(false) => return Err(group_error.unwrap_or(kill_error)),
                    Err(_) => {
                        let error = group_error.unwrap_or(kill_error);
                        self.failure = Some(copy_error(&error));
                        return Err(error);
                    }
                }
            }
        }
        let status = match self.child.wait() {
            Ok(status) => status,
            Err(wait_error) => {
                let error = group_error.unwrap_or(wait_error);
                self.failure = Some(copy_error(&error));
                return Err(error);
            }
        };
        self.status = Some(status);
        if let Some(error) = group_error {
            self.failure = Some(copy_error(&error));
            Err(error)
        } else {
            Ok(status)
        }
    }
}

impl Drop for ProcessGroupChild {
    fn drop(&mut self) {
        if self.status.is_none() && self.failure.is_none() {
            let _ = self.terminate();
        }
    }
}

fn copy_error(error: &io::Error) -> io::Error {
    match error.raw_os_error() {
        Some(code) => io::Error::from_raw_os_error(code),
        None => io::Error::new(error.kind(), error.to_string()),
    }
}

// Only the first C int (si_signo) is inspected. This initialized, overallocated
// storage has sufficient size/alignment for the supported siginfo_t layouts:
// Linux: 128 bytes, at most 8-byte alignment; Darwin: 104 bytes/8-byte alignment
// on 64-bit targets (smaller on 32-bit targets). No pointer or union member is
// interpreted. Primary ABI definitions:
// https://github.com/torvalds/linux/blob/v6.18/include/uapi/asm-generic/siginfo.h
// https://github.com/apple-oss-distributions/xnu/blob/main/bsd/sys/signal.h
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[repr(C, align(8))]
struct SiginfoStorage {
    signo: i32,
    rest: [u8; 124],
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
const _: [(); 128] = [(); std::mem::size_of::<SiginfoStorage>()];
#[cfg(any(target_os = "linux", target_os = "macos"))]
const _: [(); 8] = [(); std::mem::align_of::<SiginfoStorage>()];

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn observe_exit(id: u32, nonblocking: bool) -> io::Result<bool> {
    checked_pid(id)?;
    // Constants from Linux include/uapi/linux/wait.h and XNU bsd/sys/wait.h.
    // WNOWAIT keeps the exited leader waitable: do not substitute Child::try_wait.
    const P_PID: i32 = 1;
    const WEXITED: i32 = 4;
    const WNOHANG: i32 = 1;
    #[cfg(target_os = "linux")]
    const WNOWAIT: i32 = 0x0100_0000;
    #[cfg(target_os = "macos")]
    const WNOWAIT: i32 = 0x20;
    let options = WEXITED | WNOWAIT | if nonblocking { WNOHANG } else { 0 };
    loop {
        let mut info = SiginfoStorage {
            signo: 0,
            rest: [0; 124],
        };
        // UNSAFE-LEDGER: FLN-UL-0671
        #[allow(unsafe_code)]
        let result = {
            unsafe extern "C" {
                fn waitid(kind: i32, id: u32, info: *mut SiginfoStorage, options: i32) -> i32;
            }
            // SAFETY: the supported ABI writes at most 128 bytes aligned to at
            // most 8. The entire live buffer is initialized and writable. P_PID
            // selects only our positive child PID; WNOWAIT never reaps it.
            unsafe { waitid(P_PID, id, &mut info, options) }
        };
        if result == 0 {
            if info.signo != 0 {
                return Ok(true);
            }
            if nonblocking {
                return Ok(false);
            }
            return Err(io::Error::other(
                "blocking child observation returned no completion",
            ));
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn checked_pid(id: u32) -> io::Result<i32> {
    i32::try_from(id)
        .ok()
        .filter(|id| *id > 0)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "invalid child process id"))
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn signal_group(id: u32) -> io::Result<()> {
    let id = checked_pid(id)?;
    // Both supported platforms define SIGKILL=9 and ESRCH=3. A group with no
    // remaining members needs no signal, but its leader is still reaped below.
    // UNSAFE-LEDGER: FLN-UL-0670
    #[allow(unsafe_code)]
    let result = {
        unsafe extern "C" {
            fn kill(pid: i32, signal: i32) -> i32;
        }
        // SAFETY: kill accepts integers and no pointers. Its caller just
        // confirmed exclusive ownership with waitid(WNOWAIT); absent an
        // external reaper, the unreaped leader prevents numeric PID reuse.
        unsafe { kill(-id, 9) }
    };
    if result == 0 {
        Ok(())
    } else {
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(3) {
            Ok(())
        } else {
            Err(error)
        }
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn unsupported() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "external-tool process-group cancellation is unavailable on this platform",
    )
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn observe_exit(_id: u32, _nonblocking: bool) -> io::Result<bool> {
    Err(unsupported())
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn signal_group(_id: u32) -> io::Result<()> {
    Err(unsupported())
}

#[cfg(test)]
mod tests {
    #![forbid(unsafe_code)]

    use super::*;
    use std::path::{Path, PathBuf};
    use std::process::Stdio;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{Duration, Instant};

    static NEXT: AtomicU64 = AtomicU64::new(0);

    fn directory() -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "fln-process-group-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).expect("private process test directory");
        path
    }

    fn fixture_command(root: &Path, mode: &str) -> Command {
        let mut command = Command::new(std::env::current_exe().expect("test executable"));
        command
            .args(["--exact", "process::tests::child_fixture", "--nocapture"])
            .env("FLN_PROCESS_GROUP_FIXTURE", mode)
            .env("FLN_PROCESS_GROUP_FIXTURE_ROOT", root)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        command
    }

    fn await_file(path: &Path) {
        let deadline = Instant::now() + Duration::from_secs(10);
        while !path.is_file() {
            assert!(
                Instant::now() < deadline,
                "child did not create {}",
                path.display()
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn child_fixture() {
        let Ok(mode) = std::env::var("FLN_PROCESS_GROUP_FIXTURE") else {
            return;
        };
        let root = PathBuf::from(std::env::var_os("FLN_PROCESS_GROUP_FIXTURE_ROOT").unwrap());
        if mode == "exit" {
            std::process::exit(17);
        }
        if mode == "parent" || mode == "exited-parent" {
            // The normal tool child inherits the group. The exited-parent
            // fixture intentionally leaves a live descendant behind.
            let mut descendant = fixture_command(&root, "descendant").spawn().unwrap();
            std::fs::write(root.join("parent.pid"), std::process::id().to_string()).unwrap();
            if mode == "exited-parent" {
                await_file(&root.join("descendant.pid"));
                std::process::exit(23);
            }
            let _ = descendant.wait();
        } else {
            std::fs::write(
                root.join(format!("{mode}.pid")),
                std::process::id().to_string(),
            )
            .unwrap();
            std::thread::sleep(Duration::from_secs(30));
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn completion_is_retained_and_repeated_termination_does_not_signal() {
        let root = directory();
        let mut child = ProcessGroupChild::spawn(&mut fixture_command(&root, "exit")).unwrap();
        let status = child.wait().unwrap();
        assert_eq!(status.code(), Some(17));
        assert_eq!(child.try_wait().unwrap(), Some(status));
        assert_eq!(child.terminate().unwrap(), status);
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn cancellation_reaps_the_owned_leader() {
        use std::os::unix::process::ExitStatusExt;
        let root = directory();
        let mut child = ProcessGroupChild::spawn(&mut fixture_command(&root, "parent")).unwrap();
        await_file(&root.join("parent.pid"));
        await_file(&root.join("descendant.pid"));
        assert!(child.try_wait().unwrap().is_none());
        let status = child.terminate().unwrap();
        assert_eq!(status.signal(), Some(9));
        assert_eq!(child.try_wait().unwrap(), Some(status));
        #[cfg(target_os = "linux")]
        assert_descendant_stopped(&root);
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn lost_reaper_ownership_permanently_refuses_signals() {
        let root = directory();
        let mut child = ProcessGroupChild::spawn(&mut fixture_command(&root, "exit")).unwrap();
        // Simulate an embedder violating the exclusive-reaper contract. The
        // public API exposes no Child, but a process-wide waitpid can do this.
        assert_eq!(child.child.wait().unwrap().code(), Some(17));
        assert!(child.try_wait().is_err());
        assert!(child.terminate().is_err());
        assert!(child.wait().is_err());
        drop(child);
    }

    #[cfg(target_os = "linux")]
    fn assert_descendant_stopped(root: &Path) {
        let pid = std::fs::read_to_string(root.join("descendant.pid")).unwrap();
        let path = PathBuf::from(format!("/proc/{}/stat", pid.trim()));
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            match std::fs::read_to_string(&path) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => return,
                Ok(stat)
                    if stat
                        .rsplit_once(") ")
                        .is_some_and(|(_, tail)| tail.starts_with('Z')) =>
                {
                    return;
                }
                Ok(_) => {}
                Err(error) => panic!("cannot inspect descendant: {error}"),
            }
            assert!(
                Instant::now() < deadline,
                "tool descendant survived group cancellation"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn completed_leader_cannot_leave_a_live_descendant() {
        let root = directory();
        let mut child =
            ProcessGroupChild::spawn(&mut fixture_command(&root, "exited-parent")).unwrap();
        await_file(&root.join("descendant.pid"));
        let deadline = Instant::now() + Duration::from_secs(10);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            assert!(Instant::now() < deadline, "group leader did not exit");
            std::thread::sleep(Duration::from_millis(10));
        };
        assert_eq!(status.code(), Some(23));
        assert_descendant_stopped(&root);
        assert_eq!(child.terminate().unwrap(), status);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn blocking_wait_cleans_an_exited_leaders_descendants() {
        let root = directory();
        let mut child =
            ProcessGroupChild::spawn(&mut fixture_command(&root, "exited-parent")).unwrap();
        assert_eq!(child.wait().unwrap().code(), Some(23));
        assert_descendant_stopped(&root);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn dropping_an_unfinished_job_cancels_its_descendants() {
        let root = directory();
        let child = ProcessGroupChild::spawn(&mut fixture_command(&root, "parent")).unwrap();
        await_file(&root.join("parent.pid"));
        await_file(&root.join("descendant.pid"));
        drop(child);
        assert_descendant_stopped(&root);
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    #[test]
    fn unsupported_platform_refuses_before_executing() {
        let root = directory();
        let error = ProcessGroupChild::spawn(&mut fixture_command(&root, "parent"))
            .err()
            .expect("no unsupported process-group launch");
        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
        assert!(!root.join("parent.pid").exists());
    }
}
