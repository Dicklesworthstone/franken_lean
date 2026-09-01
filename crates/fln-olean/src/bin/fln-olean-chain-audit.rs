#![forbid(unsafe_code)]

use std::env;
use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fln_olean::decl::{
    ChainLimits, ConstantOrigin, chain_extra_const_names, decode_chain_constants_from_parts,
};
use fln_olean::region::OleanView;

const SCHEMA: &str = "fln.olean-chain-audit/1";
const DEFAULT_MAX_BYTES: usize = 64 * 1024 * 1024;
const USAGE: &str = "usage: fln-olean-chain-audit [--json] [--declarations] [--max-bytes N] EXPORTED.olean EXPORTED.olean.server EXPORTED.olean.private";

#[derive(Debug, Clone, PartialEq, Eq)]
struct Args {
    exported: PathBuf,
    server: PathBuf,
    private: PathBuf,
    max_bytes: usize,
    json: bool,
    declarations: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DeclarationRow {
    position: usize,
    name: String,
    kind: &'static str,
    origin: ConstantOrigin,
    strengthened: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AuditSummary {
    exported_bytes: usize,
    server_bytes: usize,
    private_bytes: usize,
    total_bytes: usize,
    max_bytes: usize,
    constants: usize,
    exported_constants: usize,
    private_only_constants: usize,
    strengthened_constants: usize,
    extra_const_names: usize,
    declarations: Vec<DeclarationRow>,
}

fn main() -> ExitCode {
    let args = match parse_args(env::args_os().skip(1)) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("fln-olean-chain-audit: {error}");
            return ExitCode::from(2);
        }
    };

    match audit(&args) {
        Ok(summary) => {
            if args.json {
                println!("{}", render_json(&args, &summary));
            } else {
                print_human(&args, &summary);
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            if args.json {
                eprintln!("{}", render_error_json(&error));
            } else {
                eprintln!("fln-olean-chain-audit: {error}");
            }
            ExitCode::from(3)
        }
    }
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Args, String> {
    let mut arguments = arguments.into_iter();
    let mut max_bytes = DEFAULT_MAX_BYTES;
    let mut json = false;
    let mut declarations = false;
    let mut paths = Vec::new();

    while let Some(argument) = arguments.next() {
        match argument.to_str() {
            Some("--json") => json = true,
            Some("--declarations") => declarations = true,
            Some("--max-bytes") => {
                let value = arguments
                    .next()
                    .ok_or_else(|| format!("--max-bytes requires a value; {USAGE}"))?;
                let value = value
                    .into_string()
                    .map_err(|_| "--max-bytes is not valid UTF-8".to_owned())?;
                max_bytes = value
                    .parse::<usize>()
                    .map_err(|_| format!("invalid --max-bytes value {value:?}"))?;
                if max_bytes == 0 {
                    return Err("--max-bytes must be greater than zero".to_owned());
                }
            }
            Some("-h" | "--help") => return Err(USAGE.to_owned()),
            Some(flag) if flag.starts_with('-') => {
                return Err(format!("unknown option {flag:?}; {USAGE}"));
            }
            Some(_) => paths.push(PathBuf::from(argument)),
            None => paths.push(PathBuf::from(argument)),
        }
    }

    let [exported, server, private]: [PathBuf; 3] = paths.try_into().map_err(|paths: Vec<_>| {
        format!(
            "expected exactly three artifact paths, observed {}; {USAGE}",
            paths.len()
        )
    })?;
    Ok(Args {
        exported,
        server,
        private,
        max_bytes,
        json,
        declarations,
    })
}

fn audit(args: &Args) -> Result<AuditSummary, String> {
    let exported_bytes = file_len(&args.exported)?;
    let server_bytes = file_len(&args.server)?;
    let private_bytes = file_len(&args.private)?;
    let total_bytes = checked_total([exported_bytes, server_bytes, private_bytes])?;
    if total_bytes > args.max_bytes {
        return Err(format!(
            "chain is {total_bytes} bytes, over the {}-byte ceiling; no artifact bytes were read",
            args.max_bytes
        ));
    }

    let exported = read_exact(&args.exported, exported_bytes)?;
    let server = read_exact(&args.server, server_bytes)?;
    let private = read_exact(&args.private, private_bytes)?;
    let limits = ChainLimits::new(args.max_bytes);
    let chain = decode_chain_constants_from_parts(&exported, &server, &private, limits)
        .map_err(|error| format!("decode chain: {error}"))?;

    let exported_view = OleanView::parse(&exported)
        .map_err(|error| format!("parse exported part for extraConstNames: {error}"))?;
    let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .map_err(|error| format!("parse private part for extraConstNames: {error}"))?;
    let extra_const_names = chain_extra_const_names(&exported_view, &private_view, limits.graph)
        .map_err(|error| format!("decode chain extraConstNames: {error}"))?;

    let exported_constants = chain
        .origins
        .iter()
        .filter(|origin| **origin == ConstantOrigin::Exported)
        .count();
    let private_only_constants = chain
        .origins
        .iter()
        .filter(|origin| **origin == ConstantOrigin::PrivateOnly)
        .count();
    let strengthened_constants = chain.strengthened_by_the_companion().count();
    let declarations = if args.declarations {
        chain
            .constants
            .iter()
            .zip(&chain.origins)
            .enumerate()
            .map(|(position, (constant, origin))| DeclarationRow {
                position,
                name: constant.name().to_display_string(),
                kind: constant.kind_name(),
                origin: *origin,
                strengthened: chain.was_exported_as_axiom(constant.name()),
            })
            .collect()
    } else {
        Vec::new()
    };

    Ok(AuditSummary {
        exported_bytes,
        server_bytes,
        private_bytes,
        total_bytes,
        max_bytes: args.max_bytes,
        constants: chain.constants.len(),
        exported_constants,
        private_only_constants,
        strengthened_constants,
        extra_const_names: extra_const_names.len(),
        declarations,
    })
}

fn file_len(path: &Path) -> Result<usize, String> {
    let metadata = fs::metadata(path)
        .map_err(|error| format!("stat {}: {error}", path.display()))?;
    if !metadata.is_file() {
        return Err(format!("{} is not a regular file", path.display()));
    }
    usize::try_from(metadata.len())
        .map_err(|_| format!("{} is too large for this platform", path.display()))
}

fn checked_total(lengths: [usize; 3]) -> Result<usize, String> {
    lengths
        .into_iter()
        .try_fold(0usize, usize::checked_add)
        .ok_or_else(|| "chain byte count overflowed usize".to_owned())
}

fn read_exact(path: &Path, expected: usize) -> Result<Vec<u8>, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    if bytes.len() != expected {
        return Err(format!(
            "{} changed while it was being audited: metadata reported {expected} bytes, read {}",
            path.display(),
            bytes.len()
        ));
    }
    Ok(bytes)
}

fn print_human(args: &Args, summary: &AuditSummary) {
    println!("FrankenLean .olean chain audit");
    println!("  exported: {} ({} bytes)", args.exported.display(), summary.exported_bytes);
    println!("  server:   {} ({} bytes)", args.server.display(), summary.server_bytes);
    println!("  private:  {} ({} bytes)", args.private.display(), summary.private_bytes);
    println!("  total:    {} / {} bytes", summary.total_bytes, summary.max_bytes);
    println!("  constants: {}", summary.constants);
    println!("    exported:     {}", summary.exported_constants);
    println!("    private-only: {}", summary.private_only_constants);
    println!("    strengthened: {}", summary.strengthened_constants);
    println!("  extraConstNames union: {}", summary.extra_const_names);
    if !summary.declarations.is_empty() {
        println!("  declarations:");
        for row in &summary.declarations {
            let origin = match row.origin {
                ConstantOrigin::Exported => "exported",
                ConstantOrigin::PrivateOnly => "private-only",
            };
            let strengthened = if row.strengthened { " strengthened" } else { "" };
            println!(
                "    {:>6} {:<12} {:<11} {}{}",
                row.position, row.kind, origin, row.name, strengthened
            );
        }
    }
}

fn render_json(args: &Args, summary: &AuditSummary) -> String {
    let mut output = String::new();
    write!(
        output,
        "{{\"schema\":\"{SCHEMA}\",\"status\":\"complete\",\"artifacts\":{{\"exported\":{},\"server\":{},\"private\":{}}},\"bytes\":{{\"exported\":{},\"server\":{},\"private\":{},\"total\":{},\"limit\":{}}},\"constants\":{{\"total\":{},\"exported\":{},\"private_only\":{},\"strengthened\":{}}},\"extra_const_names\":{},\"declarations\":[",
        json_string(&args.exported.to_string_lossy()),
        json_string(&args.server.to_string_lossy()),
        json_string(&args.private.to_string_lossy()),
        summary.exported_bytes,
        summary.server_bytes,
        summary.private_bytes,
        summary.total_bytes,
        summary.max_bytes,
        summary.constants,
        summary.exported_constants,
        summary.private_only_constants,
        summary.strengthened_constants,
        summary.extra_const_names,
    )
    .expect("writing to a String cannot fail");
    for (index, row) in summary.declarations.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        let origin = match row.origin {
            ConstantOrigin::Exported => "exported",
            ConstantOrigin::PrivateOnly => "private_only",
        };
        write!(
            output,
            "{{\"position\":{},\"name\":{},\"kind\":{},\"origin\":{},\"strengthened\":{}}}",
            row.position,
            json_string(&row.name),
            json_string(row.kind),
            json_string(origin),
            row.strengthened,
        )
        .expect("writing to a String cannot fail");
    }
    output.push_str("]}");
    output
}

fn render_error_json(error: &str) -> String {
    format!(
        "{{\"schema\":\"{SCHEMA}\",\"status\":\"error\",\"error\":{}}}",
        json_string(error)
    )
}

fn json_string(value: &str) -> String {
    let mut output = String::with_capacity(value.len().saturating_add(2));
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                write!(output, "\\u{:04x}", u32::from(character))
                    .expect("writing to a String cannot fail");
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_three_paths_and_options() {
        let args = parse_args(
            [
                "--json",
                "--declarations",
                "--max-bytes",
                "1234",
                "a.olean",
                "a.olean.server",
                "a.olean.private",
            ]
            .into_iter()
            .map(OsString::from),
        )
        .unwrap();
        assert!(args.json);
        assert!(args.declarations);
        assert_eq!(args.max_bytes, 1234);
        assert_eq!(args.exported, PathBuf::from("a.olean"));
    }

    #[test]
    fn rejects_the_wrong_number_of_paths_and_zero_ceiling() {
        assert!(parse_args([OsString::from("a.olean")]).is_err());
        assert!(
            parse_args(
                ["--max-bytes", "0", "a", "b", "c"]
                    .into_iter()
                    .map(OsString::from)
            )
            .is_err()
        );
    }

    #[test]
    fn byte_totals_are_checked() {
        assert_eq!(checked_total([1, 2, 3]).unwrap(), 6);
        assert!(checked_total([usize::MAX, 1, 0]).is_err());
    }

    #[test]
    fn json_escaping_is_canonical() {
        assert_eq!(json_string("a\n\"β"), "\"a\\n\\\"β\"");
        let error = render_error_json("bad\nartifact");
        assert!(error.contains("\"status\":\"error\""));
        assert!(error.contains("bad\\nartifact"));
    }
}
