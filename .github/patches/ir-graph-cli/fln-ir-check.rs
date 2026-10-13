//! Native validation and reusable graph export for a supplied IR file closure.
#![forbid(unsafe_code)]

mod ir_support;

use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir_archive::{CensusPartition, parse_name_key, snapshot_graph};
use fln_olean::ir_files::{
    IrFileLimits, check_ir_files, check_ir_files_with_types, ir_graph_dot,
};
use ir_support::{Result, host_size, number, read_file, write_stdout};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

const HELP: &str = "Usage: fln-ir-check [OPTIONS] [--] FILE.ir...\n\n\
Check structure and expression representations in an explicit declaration closure.\n\
No Reference implementation, initializer, or external tool is executed.\n\n\
  --dot                    Write a static DOT diagnostic graph to stdout\n\
  --archive                Write a reusable binary graph snapshot to stdout\n\
  --partition FILE         Join exact keys from the generated census partition\n\
  --user-key KEY           Explicit user symbol in census-key syntax (repeatable)\n\
  --strict-classes         Refuse archive export if any symbol is unclassified\n\
  --structural-only        Skip expression representation checks (diagnostic mode)\n\
  --max-files N            Maximum number of supplied files\n\
  --max-file-bytes N       Maximum actual bytes read from any IR file\n\
  --max-total-bytes N      Maximum actual bytes read across IR files\n\
  --max-payload-bytes N    Maximum expanded captured payload bytes in total\n\
  --max-output-bytes N     Maximum output bytes (default 67108864)\n\
  --max-partition-bytes N  Maximum census input bytes (default 268435456)\n\
  --max-graph-nodes N      Maximum archive nodes and census rows\n\
  --max-graph-edges N      Maximum archive edges\n\
  --max-work N             Shared structural and representation work allowance\n\
  --help                   Show this help\n\n\
--dot and --archive are mutually exclusive. Census/user options require --archive.\n\
Missing callees are errors, not stubs. Unknown census keys stay unclassified;\n\
compiler suffixes and namespaces do not implicitly authorize classifications.\n\
Exit codes: 0 requested checks passed, 1 malformed/unclosed IR or census,\n\
2 usage, 5 unavailable input, unsupported capability, resource limit, or I/O.\n\
Snapshots carry static calls only and confer no typing/ownership/execution authority.\n";

fn run() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let mut limits = IrFileLimits::default();
    let mut archive_limits = GraphArchiveLimits::default();
    let mut dot = false;
    let mut archive = false;
    let mut structural_only = false;
    let mut strict_classes = false;
    let mut partition_path = None;
    let mut explicit_users = BTreeSet::new();
    let mut max_partition_bytes = 256 * 1024 * 1024;
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
            Some("--help" | "-h") => return write_stdout(HELP.as_bytes()),
            Some("--dot") => dot = true,
            Some("--archive") => archive = true,
            Some("--strict-classes") => strict_classes = true,
            Some("--structural-only") => structural_only = true,
            Some("--partition") => {
                if partition_path.is_some() { return Err((2, "--partition may be supplied only once".into())); }
                partition_path = Some(PathBuf::from(args.next().ok_or_else(|| (2, "--partition requires a filename".into()))?));
            }
            Some("--user-key") => {
                let key = args.next().ok_or_else(|| (2, "--user-key requires a census name key".into()))?;
                let key = key.to_str().ok_or_else(|| (2, "a name key must be UTF-8".into()))?;
                let name = parse_name_key(key, 1 << 20, 10_000).map_err(|error| (2, error.to_string()))?;
                explicit_users.insert(name);
            }
            Some("--max-files") => limits.max_files = host_size(number(&mut args, "--max-files")?, "--max-files")?,
            Some("--max-file-bytes") => limits.max_file_bytes = number(&mut args, "--max-file-bytes")?,
            Some("--max-total-bytes") => limits.max_total_bytes = number(&mut args, "--max-total-bytes")?,
            Some("--max-payload-bytes") => {
                limits.max_payload_bytes = host_size(number(&mut args, "--max-payload-bytes")?, "--max-payload-bytes")?;
            }
            Some("--max-output-bytes") => {
                max_output = host_size(number(&mut args, "--max-output-bytes")?, "--max-output-bytes")?;
            }
            Some("--max-partition-bytes") => {
                max_partition_bytes = host_size(number(&mut args, "--max-partition-bytes")?, "--max-partition-bytes")?;
            }
            Some("--max-graph-nodes") => {
                archive_limits.max_nodes = host_size(number(&mut args, "--max-graph-nodes")?, "--max-graph-nodes")?;
            }
            Some("--max-graph-edges") => {
                archive_limits.max_edges = host_size(number(&mut args, "--max-graph-edges")?, "--max-graph-edges")?;
            }
            Some("--max-work") => limits.validation.max_work = number(&mut args, "--max-work")?,
            Some(flag) if flag.starts_with('-') => {
                return Err((2, format!("unknown option {flag:?}; use -- before a filename beginning with '-'")));
            }
            _ => paths.push(PathBuf::from(arg)),
        }
    }
    if dot && archive { return Err((2, "--dot and --archive are mutually exclusive".into())); }
    if !archive && (partition_path.is_some() || !explicit_users.is_empty() || strict_classes) {
        return Err((2, "classification options require --archive".into()));
    }
    if paths.is_empty() { return Err((2, "at least one IR file is required; use --help for usage".into())); }
    archive_limits.max_bytes = max_output;
    // A bad/oversized census is refused before spending work on IR validation.
    let partition = if let Some(path) = partition_path {
        let bytes = read_file(&path, max_partition_bytes)?;
        let text = std::str::from_utf8(&bytes).map_err(|_| (1, "partition is not UTF-8".into()))?;
        Some(CensusPartition::parse(text, GraphArchiveLimits { max_bytes: max_partition_bytes, ..archive_limits })
            .map_err(|error| (if error.is_resource() { 5 } else { 1 }, error.to_string()))?)
    } else { None };
    let result = if structural_only {
        check_ir_files(&paths, &BTreeMap::new(), limits)
    } else {
        check_ir_files_with_types(&paths, &BTreeMap::new(), limits)
    }.map_err(|error| (if error.is_inconclusive() { 5 } else { 1 }, error.to_string()))?;
    let summary = result.checked.summary();
    let mut message = format!(
        "IR structurally valid: {} files, {} declarations, {} externs, {} direct edges, {} unresolved closure calls; {} input bytes, {} captured payload bytes\n",
        summary.modules, summary.declarations, summary.extern_declarations,
        result.checked.graph().edge_count(), summary.dynamic_calls,
        result.input_bytes, result.captured_payload_bytes,
    );
    match result.representation {
        Some(types) => message.push_str(&format!(
            "IR expression representations checked: {} expressions, {} type nodes; {} cumulative validation work\n",
            types.expressions, types.type_nodes, types.work,
        )),
        None => message.push_str("IR expression representations: NOT CHECKED (structural-only)\n"),
    }
    let output = if archive {
        let snapshot = snapshot_graph(&result.checked, partition.as_ref(), &explicit_users, archive_limits)
            .map_err(|error| (if error.is_resource() { 5 } else { 1 }, error.to_string()))?;
        if strict_classes && snapshot.unclassified_count() != 0 {
            return Err((1, format!("{} symbols remain unclassified", snapshot.unclassified_count())));
        }
        let encoded = snapshot.encode(archive_limits)
            .map_err(|error| (if error.is_resource() { 5 } else { 1 }, error.to_string()))?;
        message.push_str(&format!("IR graph archive digest: {}; {} unclassified symbols\n", encoded.digest, snapshot.unclassified_count()));
        Some(encoded.bytes)
    } else if dot {
        Some(ir_graph_dot(&result.checked, max_output).map_err(|error| (5, error.to_string()))?.into_bytes())
    } else { None };
    match output {
        Some(bytes) => {
            // No graph byte is published until ALL requested checks and output
            // limits have succeeded. Downstream I/O can still interrupt a write.
            write_stdout(&bytes)?;
            io::stderr().lock().write_all(message.as_bytes())
                .map_err(|error| (5, format!("stderr: {error}")))?;
            Ok(())
        }
        None => write_stdout(message.as_bytes()),
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
