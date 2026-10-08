//! Shared bounded I/O for the native IR analysis commands.

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;

pub type Result<T> = std::result::Result<T, (u8, String)>;

pub fn number(args: &mut impl Iterator<Item = OsString>, flag: &str) -> Result<u64> {
    args.next()
        .and_then(|arg| arg.to_str().and_then(|s| s.parse().ok()))
        .ok_or_else(|| (2, format!("{flag} requires a nonnegative integer")))
}

pub fn host_size(value: u64, flag: &str) -> Result<usize> {
    usize::try_from(value).map_err(|_| (2, format!("{flag} exceeds the host size range")))
}

pub fn write_stdout(bytes: &[u8]) -> Result<()> {
    let mut stdout = io::stdout().lock();
    stdout.write_all(bytes)
        .and_then(|()| stdout.flush())
        .map_err(|error| (5, format!("stdout: {error}")))
}

/// Actual bytes, not merely the pre-open metadata estimate, are bounded.
/// Caller-selected paths are not a sandbox against concurrent path replacement.
pub fn read_file(path: &Path, cap: usize) -> Result<Vec<u8>> {
    let failure = |error: io::Error| (5, format!("{path:?}: {error}"));
    let metadata = std::fs::metadata(path).map_err(failure)?;
    if !metadata.is_file() {
        return Err((5, format!("{path:?}: a regular file is required")));
    }
    if metadata.len() > cap as u64 {
        return Err((5, format!("{path:?}: input byte budget exhausted")));
    }
    let mut file = File::open(path).map_err(failure)?;
    if !file.metadata().map_err(failure)?.is_file() {
        return Err((5, format!("{path:?}: a regular file is required")));
    }
    let mut bytes = Vec::new();
    let mut buffer = [0u8; 16 * 1024];
    loop {
        let count = match file.read(&mut buffer) {
            Ok(0) => return Ok(bytes),
            Ok(count) => count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(failure(error)),
        };
        if bytes.len().checked_add(count).is_none_or(|size| size > cap) {
            return Err((5, format!("{path:?}: input byte budget exhausted")));
        }
        bytes.try_reserve(count)
            .map_err(|_| (5, format!("{path:?}: input allocation refused")))?;
        bytes.extend_from_slice(&buffer[..count]);
    }
}
