//! Query a saved IR graph without opening or executing the original IR files.
#![forbid(unsafe_code)]

mod ir_support;

use fln_core::name::Name;
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::ir_graph::{GraphArchiveLimits, GraphClass, GraphKind, GraphSnapshot};
use fln_olean::ir_archive::parse_name_key;
use ir_support::{Result, host_size, number, read_file, write_stdout};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

const HELP: &str = "Usage: fln-ir-graph [OPTIONS] SNAPSHOT\n\n\
Verify and query a canonical static IR graph. No original IR files are needed.\n\n\
  --root NAME              Reach from a plain dot-separated name (repeatable)\n\
  --root-key KEY           Reach from an exact census-format name key\n\
  --native-boundary        Reach, but do not traverse, toolchain/unclassified nodes\n\
  --list                   List all nodes when no roots were specified\n\
  --expect-digest HEX      Require a separately trusted 64-digit payload digest\n\
  --max-input-bytes N      Maximum snapshot bytes (default 536870912)\n\
  --max-output-bytes N     Maximum report bytes (default 8388608)\n\
  --max-nodes N            Maximum nodes\n\
  --max-edges N            Maximum edges\n\
  --max-work N             Reachability work allowance (default 64000000)\n\
  --help                   Show this help\n\n\
Without roots or --list, print a summary. Rows are TSV with escaped display names;\n\
use --root-key for numeric components or dots within a single component.\n\
All results are static analysis data, not execution permissions or kernel receipts.\n\
The indirect-call count is for the WHOLE archive, not only reached nodes.\n\
Exit codes: 0 completed, 1 malformed/mismatched archive or unknown root,\n\
2 usage, 5 unavailable input, resource limit, or I/O.\n";

fn digest_arg(text: &str) -> Result<Digest> {
    if text.len() != 64 || !text.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err((2, "--expect-digest requires exactly 64 hexadecimal digits".into()));
    }
    let mut result = [0u8;32];
    for (index, byte) in result.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[index*2..index*2+2],16)
            .map_err(|_| (2,"invalid digest".into()))?;
    }
    Ok(Digest(result))
}

fn append(report: &mut String, text: &str, cap: usize) -> Result<()> {
    if report.len().checked_add(text.len()).is_none_or(|size|size > cap) {
        return Err((5,"report byte budget exhausted".into()));
    }
    report.try_reserve(text.len()).map_err(|_| (5,"report allocation refused".into()))?;
    report.push_str(text);
    Ok(())
}

fn run() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let mut limits = GraphArchiveLimits::default();
    let mut output_cap = 8*1024*1024;
    let mut max_work = 64_000_000;
    let mut roots = Vec::new();
    let mut native_boundary = false;
    let mut list = false;
    let mut expected = None;
    let mut path = None;
    let mut positional = false;
    while let Some(arg) = args.next() {
        if !positional {
            match arg.to_str() {
                Some("--") => { positional = true; continue; }
                Some("--help" | "-h") => return write_stdout(HELP.as_bytes()),
                Some("--native-boundary") => { native_boundary = true; continue; }
                Some("--list") => { list = true; continue; }
                Some("--root" | "--root-key") => {
                    let exact = arg == "--root-key";
                    let root = args.next().ok_or_else(|| (2,"root option requires a name".into()))?;
                    let root = root.to_str().ok_or_else(|| (2,"a root name must be UTF-8".into()))?;
                    if root.len() > 1 << 20 { return Err((2,"root name is too large".into())); }
                    roots.push(if exact {
                        parse_name_key(root,1<<20,10_000).map_err(|error| (2,error.to_string()))?
                    } else {
                        if root.is_empty() || root.split('.').any(str::is_empty) {
                            return Err((2,"--root requires nonempty dot-separated components; use --root-key for exact names".into()));
                        }
                        Name::from_components(root.split('.'))
                    });
                    continue;
                }
                Some("--expect-digest") => {
                    if expected.is_some() { return Err((2,"--expect-digest may be supplied only once".into())); }
                    let value = args.next().ok_or_else(|| (2,"missing expected digest".into()))?;
                    expected = Some(digest_arg(value.to_str().ok_or_else(|| (2,"digest must be UTF-8".into()))?)?);
                    continue;
                }
                Some("--max-input-bytes") => {
                    limits.max_bytes = host_size(number(&mut args,"--max-input-bytes")?,"--max-input-bytes")?;
                    continue;
                }
                Some("--max-output-bytes") => {
                    output_cap = host_size(number(&mut args,"--max-output-bytes")?,"--max-output-bytes")?;
                    continue;
                }
                Some("--max-nodes") => {
                    limits.max_nodes = host_size(number(&mut args,"--max-nodes")?,"--max-nodes")?;
                    continue;
                }
                Some("--max-edges") => {
                    limits.max_edges = host_size(number(&mut args,"--max-edges")?,"--max-edges")?;
                    continue;
                }
                Some("--max-work") => { max_work = number(&mut args,"--max-work")?; continue; }
                Some(flag) if flag.starts_with('-') => return Err((2,format!("unknown option {flag:?}"))),
                _ => {}
            }
        }
        if path.replace(PathBuf::from(arg)).is_some() { return Err((2,"exactly one snapshot is required".into())); }
    }
    let path = path.ok_or_else(|| (2,"a snapshot filename is required".into()))?;
    if native_boundary && roots.is_empty() { return Err((2,"--native-boundary requires at least one root".into())); }
    if roots.len() > limits.max_nodes { return Err((5,"root count exceeds node allowance".into())); }
    let bytes = read_file(&path,limits.max_bytes)?;
    let graph = GraphSnapshot::decode(&bytes,limits)
        .map_err(|error| (if error.is_resource() {5} else {1},error.to_string()))?;
    // Successful decoding has already checked the minimum size and trailer.
    let digest = hash(Domain::IrCallGraph,&bytes[..bytes.len()-32]);
    if expected.is_some_and(|expected|expected != digest) {
        return Err((1,"archive does not match the supplied expected digest".into()));
    }
    let reached = if roots.is_empty() { None } else {
        Some(graph.reach(&roots,|node| {
            !native_boundary || !matches!(node.class,GraphClass::ToolchainApi|GraphClass::Unclassified)
        },max_work).map_err(|error| (if error.is_resource() {5} else {1},error.to_string()))?)
    };
    let mut report = String::new();
    append(&mut report,&format!(
        "digest\t{digest}\nnodes\t{}\nedges\t{}\nunclassified\t{}\nindirect_calls_whole_archive\t{}\n",
        graph.nodes().len(),graph.edge_count(),graph.unclassified_count(),graph.dynamic_calls(),
    ),output_cap)?;
    if let Some(reached) = &reached { append(&mut report,&format!("reached\t{}\n",reached.len()),output_cap)?; }
    if list || reached.is_some() {
        append(&mut report,"node\tid\tkind\tclass\tname\n",output_cap)?;
        for (id,node) in graph.nodes().iter().enumerate() {
            if reached.as_ref().is_some_and(|set|set.binary_search(&(id as u32)).is_err()) { continue; }
            let kind = match node.kind {
                GraphKind::Function => "function", GraphKind::Extern => "extern", GraphKind::SignatureOnly => "signature-only",
            };
            append(&mut report,&format!("node\t{id}\t{kind}\t{}\t{:?}\n",node.class.as_str(),node.name.to_display_string()),output_cap)?;
        }
    }
    // Fully verify, query and size the report before publishing any output.
    write_stdout(report.as_bytes())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err((code,message)) => {
            let _ = writeln!(io::stderr().lock(),"fln-ir-graph: {message}");
            ExitCode::from(code)
        }
    }
}
