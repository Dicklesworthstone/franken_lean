//! Native, read-only validation of a supplied IR file closure.
#![forbid(unsafe_code)]

use fln_olean::ir_files::{IrFileLimits, check_ir_files, ir_graph_dot};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

const HELP: &str = "Usage: fln-ir-check [OPTIONS] [--] FILE.ir...\n\n\
Validate all supplied IR declarations, then optionally emit a static DOT graph.\n\
Include the complete declaration closure: missing callees are errors, not stubs.\n\
No Reference implementation, initializer, or external tool is executed.\n\n\
  --dot                    Write the validated static graph to stdout\n\
  --max-files N            Maximum number of supplied files\n\
  --max-file-bytes N       Maximum actual bytes read from any file\n\
  --max-total-bytes N      Maximum actual bytes read across all files\n\
  --max-payload-bytes N    Maximum expanded captured payload bytes in total\n\
  --max-output-bytes N     Maximum DOT output bytes (default 67108864)\n\
  --max-work N             Structural validation work allowance\n\
  --help                   Show this help\n\n\
Exit codes: 0 structurally valid, 1 malformed/unclosed IR, 2 usage,\n\
5 unavailable input, unsupported container capability, resource limit, or I/O.\n\
DOT records direct fap/pap calls only and reports the unresolved ap count.\n\
Structural validity does not establish typing, ownership, or execution safety.\n";

type Result<T> = std::result::Result<T, (u8, String)>;

fn number(args: &mut impl Iterator<Item = OsString>, flag: &str) -> Result<u64> {
    args.next().and_then(|arg| arg.to_str().and_then(|s| s.parse().ok()))
        .ok_or_else(|| (2, format!("{flag} requires a nonnegative integer")))
}

fn host_size(value: u64, flag: &str) -> Result<usize> {
    usize::try_from(value).map_err(|_| (2, format!("{flag} exceeds the host size range")))
}

fn write_stdout(text: &str) -> Result<()> {
    let mut stdout = io::stdout().lock();
    stdout.write_all(text.as_bytes()).and_then(|()| stdout.flush())
        .map_err(|error| (5, format!("stdout: {error}")))
}

fn run() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let mut limits = IrFileLimits::default();
    let mut dot = false;
    let mut max_output = 64 * 1024 * 1024;
    let mut paths = Vec::new();
    let mut positional = false;
    while let Some(arg) = args.next() {
        if positional {
            paths.push(PathBuf::from(arg));
            continue;
        }
        match arg.to_str() {
            Some("--") => positional = true,
            Some("--help" | "-h") => return write_stdout(HELP),
            Some("--dot") => dot = true,
            Some("--max-files") => {
                limits.max_files = host_size(number(&mut args, "--max-files")?, "--max-files")?;
            }
            Some("--max-file-bytes") => {
                limits.max_file_bytes = number(&mut args, "--max-file-bytes")?;
            }
            Some("--max-total-bytes") => {
                limits.max_total_bytes = number(&mut args, "--max-total-bytes")?;
            }
            Some("--max-payload-bytes") => {
                limits.max_payload_bytes = host_size(
                    number(&mut args, "--max-payload-bytes")?, "--max-payload-bytes",
                )?;
            }
            Some("--max-output-bytes") => {
                max_output = host_size(
                    number(&mut args, "--max-output-bytes")?, "--max-output-bytes",
                )?;
            }
            Some("--max-work") => {
                limits.validation.max_work = number(&mut args, "--max-work")?;
            }
            Some(flag) if flag.starts_with('-') => {
                return Err((2, format!("unknown option {flag:?}; use -- before a filename beginning with '-'")));
            }
            _ => paths.push(PathBuf::from(arg)),
        }
    }
    if paths.is_empty() {
        return Err((2, "at least one IR file is required; use --help for usage".into()));
    }
    let result = check_ir_files(&paths, &BTreeMap::new(), limits)
        .map_err(|error| (if error.is_inconclusive() { 5 } else { 1 }, error.to_string()))?;
    let summary = result.checked.summary();
    let message = format!(
        "IR structurally valid: {} files, {} declarations, {} externs, {} direct edges, {} unresolved closure calls; {} input bytes, {} captured payload bytes\n",
        summary.modules, summary.declarations, summary.extern_declarations,
        result.checked.graph().edge_count(), summary.dynamic_calls,
        result.input_bytes, result.captured_payload_bytes,
    );
    if dot {
        // Construct the complete bounded report before publishing a single byte.
        let output = ir_graph_dot(&result.checked, max_output)
            .map_err(|error| (5, error.to_string()))?;
        write_stdout(&output)?;
        io::stderr().lock().write_all(message.as_bytes())
            .map_err(|error| (5, format!("stderr: {error}")))?;
        Ok(())
    } else {
        write_stdout(&message)
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err((code, message)) => {
            let _ = writeln!(io::stderr().lock(), "fln-ir-check: {message}");
            ExitCode::from(code)
        }
    }
}
