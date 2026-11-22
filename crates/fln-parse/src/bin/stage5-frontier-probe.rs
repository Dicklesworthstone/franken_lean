//! Stage 5 pure generated registry parser frontier probe (`franken_lean-z8j.1.10`).
//!
//! Runs `reference_builtin_interpreter().parse_module_with_file_grammar(...)`
//! (pin-extracted builtin combinators + `FileGrammar` `ParserDescr` + dynamic
//! `WithOpen`/`WithOpenDecl` + `doc.verso` + file-local `syntax`/`notation`)
//! over all 1,075 vendored `Init` + `Std` files (71,015 commands) and compares
//! header + every command losslessly against `~/.cache/fln/pin-syntax`.
//!
//! Usage:
//!   stage5-frontier-probe <workspace-root> [--filter <substr>] [--dump-diff <max>]
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::builtin_interpreter::{DEFAULT_STEP_BUDGET, reference_builtin_interpreter};
use fln_syntax::pin_syntax::{self, cache_root, fnv1a};
use fln_syntax::source::{SourceInfo, SourceText};
use fln_syntax::tree::Syntax;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

const SOURCES: &str = "vendor/lean4-src/src";
const MANIFEST: &str = "crates/fln-syntax/tests/corpus/pin_syntax_manifest.tsv";
const PRODUCER: &str = "scripts/extract/dump_command_syntax.lean";

fn pin_commit(root: &Path) -> String {
    let lock = std::fs::read_to_string(root.join("SUITE.lock")).expect("read SUITE.lock");
    lock.lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .expect("SUITE.lock names the reference commit")
        .to_owned()
}

fn first_position(root: &Syntax) -> Option<usize> {
    let mut stack = vec![root];
    while let Some(syntax) = stack.pop() {
        match syntax {
            Syntax::Atom {
                info: SourceInfo::Original { pos, .. },
                ..
            }
            | Syntax::Ident {
                info: SourceInfo::Original { pos, .. },
                ..
            } => return Some(pos.0),
            Syntax::Node { args, .. } => stack.extend(args.iter().rev()),
            _ => {}
        }
    }
    None
}

fn kind_of(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "<missing>".to_owned(),
        Syntax::Atom { val, .. } => format!("{val:?}"),
        Syntax::Ident { val, .. } => format!("`{}", val.to_display_string()),
        Syntax::Node { kind, .. } => kind.to_display_string(),
    }
}

fn leaf_span(info: &SourceInfo) -> Option<(usize, usize)> {
    match info {
        SourceInfo::Original { pos, end_pos, .. } => Some((pos.0, end_pos.0)),
        _ => None,
    }
}

/// Exact comparison matching `crates/fln-parse/tests/pin_syntax_frontier.rs::compare`:
/// `Ok(None)` identical, `Ok(Some(detail))` same shape with misplaced leaf,
/// `Err((pin_kind, ours_kind, path))` structural mismatch at first differing node.
fn compare(pin: &Syntax, ours: &Syntax) -> Result<Option<String>, (String, String)> {
    let mut misplaced = None;
    let mut stack = vec![(pin, ours)];
    let mut place = |pin_leaf: &Syntax, a: &SourceInfo, b: &SourceInfo| {
        let (theirs, mine) = (leaf_span(a), leaf_span(b));
        if misplaced.is_none() && theirs != mine {
            misplaced = Some(format!(
                "{} pin {theirs:?} ours {mine:?}",
                kind_of(pin_leaf)
            ));
        }
    };
    while let Some((pin, ours)) = stack.pop() {
        match (pin, ours) {
            (Syntax::Missing, Syntax::Missing) => {}
            (Syntax::Atom { info: a, val: x }, Syntax::Atom { info: b, val: y }) if x == y => {
                place(pin, a, b);
            }
            (
                Syntax::Ident {
                    info: a, val: x, ..
                },
                Syntax::Ident {
                    info: b, val: y, ..
                },
            ) if x == y => {
                place(pin, a, b);
            }
            (
                Syntax::Node {
                    kind: k, args: xs, ..
                },
                Syntax::Node {
                    kind: l, args: ys, ..
                },
            ) if k == l && xs.len() == ys.len() => {
                stack.extend(xs.iter().zip(ys).rev());
            }
            (pin, ours) => return Err((kind_of(pin), kind_of(ours))),
        }
    }
    Ok(misplaced)
}

fn fmt_tree(stx: &Syntax, depth: usize, max_depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    if depth > max_depth {
        out.push_str(&format!("{indent}...\n"));
        return;
    }
    match stx {
        Syntax::Missing => out.push_str(&format!("{indent}M\n")),
        Syntax::Atom { info, val } => {
            out.push_str(&format!("{indent}A {val:?} {:?}\n", leaf_span(info)));
        }
        Syntax::Ident { info, val, .. } => {
            out.push_str(&format!(
                "{indent}I `{}` {:?}\n",
                val.to_display_string(),
                leaf_span(info)
            ));
        }
        Syntax::Node { kind, args, .. } => {
            out.push_str(&format!(
                "{indent}N {} ({})\n",
                kind.to_display_string(),
                args.len()
            ));
            for arg in args {
                fmt_tree(arg, depth + 1, max_depth, out);
            }
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let root = args
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::current_dir().expect("cwd"));
    let mut filter: Option<String> = None;
    let mut dump_diff_limit: usize = 0;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--filter" => filter = args.next(),
            "--dump-diff" => {
                dump_diff_limit = args.next().and_then(|s| s.parse().ok()).unwrap_or(5);
            }
            other => {
                eprintln!("unknown argument: {other}");
                std::process::exit(2);
            }
        }
    }

    let producer = format!(
        "{:016x}",
        fnv1a(&std::fs::read(root.join(PRODUCER)).expect("read the producer"))
    );
    let cache = cache_root()
        .expect("cache_root available")
        .join(pin_commit(&root))
        .join(&producer);
    let manifest = std::fs::read_to_string(root.join(MANIFEST)).expect("read manifest");
    let files: Vec<&str> = manifest
        .lines()
        .filter(|line| !line.starts_with('#'))
        .filter_map(|line| line.split('\t').next())
        .filter(|file| filter.as_ref().is_none_or(|f| file.contains(f.as_str())))
        .collect();

    let interp = reference_builtin_interpreter();
    let t0 = Instant::now();
    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut worst_files: Vec<(usize, usize, String)> = Vec::new();
    let mut identical_headers = 0usize;
    let mut identical_files = 0usize;
    let mut identical_nonempty_files = 0usize;
    let mut nonempty_files = 0usize;
    let mut files_with_errors = 0usize;
    let mut total_errors = 0usize;
    let mut budget_exhausted_files = 0usize;
    let mut total_cmds = 0usize;
    let mut dumped_diffs = 0usize;

    for file in &files {
        let source_bytes = std::fs::read(root.join(SOURCES).join(file)).expect("read source");
        let dump_path = cache.join(format!("{:016x}.dump", fnv1a(&source_bytes)));
        let dump = std::fs::read_to_string(&dump_path)
            .unwrap_or_else(|e| panic!("missing cached dump for {file} at {dump_path:?}: {e}"));
        let trees = pin_syntax::read(&dump, &source_bytes).expect("cached dump reads");
        let source = SourceText::from_utf8(&source_bytes).expect("utf-8 source");
        let module = file
            .strip_suffix(".lean")
            .map(|path| Name::from_components(path.split('/')));
        let parsed = interp.parse_module_with_file_grammar(&source, module, DEFAULT_STEP_BUDGET);

        let header_ok = compare(&trees.header, &parsed.header) == Ok(None);
        if header_ok {
            identical_headers += 1;
        }
        if !parsed.errors.is_empty() {
            files_with_errors += 1;
            total_errors += parsed.errors.len();
        }
        if parsed.budget_exhausted {
            budget_exhausted_files += 1;
        }

        let pin_cmds: Vec<&Syntax> = trees
            .commands
            .iter()
            .filter(|tree| {
                !matches!(
                    tree,
                    Syntax::Node { kind, .. } if kind.to_display_string() == "Lean.Parser.Command.eoi"
                )
            })
            .collect();
        let mut ours_by_start: BTreeMap<usize, &Syntax> = BTreeMap::new();
        for cmd in &parsed.commands {
            if matches!(
                cmd,
                Syntax::Node { kind, .. } if kind.to_display_string() == "Lean.Parser.Command.eoi"
            ) {
                continue;
            }
            if let Some(pos) = first_position(cmd) {
                ours_by_start.entry(pos).or_insert(cmd);
            }
        }

        let mut file_bad = 0usize;
        for pin in &pin_cmds {
            total_cmds += 1;
            let Some(start) = first_position(pin) else {
                file_bad += 1;
                *histogram
                    .entry("boundary:pin-no-pos".to_owned())
                    .or_default() += 1;
                continue;
            };
            let Some(ours) = ours_by_start.get(&start) else {
                file_bad += 1;
                let class = if parsed.budget_exhausted {
                    "boundary:budget".to_owned()
                } else if !parsed.errors.is_empty() {
                    "boundary:after-error".to_owned()
                } else {
                    "boundary:missing".to_owned()
                };
                let shown = examples.entry(class.clone()).or_default();
                if shown.len() < 3 {
                    let first_err = parsed
                        .errors
                        .first()
                        .map(|e| format!("err@{} {:?} exp={:?}", e.pos, e.unexpected, e.expected))
                        .unwrap_or_default();
                    let snippet = source
                        .as_str()
                        .get(start..source.len_bytes().min(start + 60))
                        .unwrap_or("")
                        .lines()
                        .next()
                        .unwrap_or("");
                    shown.push(format!("{file}@{start} {snippet:?} {first_err}"));
                }
                *histogram.entry(class).or_default() += 1;
                continue;
            };
            match compare(pin, ours) {
                Ok(None) => {
                    *histogram.entry("identical".to_owned()).or_default() += 1;
                }
                Ok(Some(leaf)) => {
                    file_bad += 1;
                    let class = "positions".to_owned();
                    let shown = examples.entry(class.clone()).or_default();
                    if shown.len() < 3 {
                        shown.push(format!("{file}@{start} {leaf}"));
                    }
                    *histogram.entry(class).or_default() += 1;
                }
                Err((pin_k, ours_k)) => {
                    file_bad += 1;
                    let class = format!("tree:{pin_k} vs {ours_k}");
                    let shown = examples.entry(class.clone()).or_default();
                    if shown.len() < 3 {
                        let snippet = source
                            .as_str()
                            .get(start..source.len_bytes().min(start + 60))
                            .unwrap_or("")
                            .lines()
                            .next()
                            .unwrap_or("");
                        shown.push(format!("{file}@{start} {snippet:?}"));
                    }
                    *histogram.entry(class).or_default() += 1;
                    if dumped_diffs < dump_diff_limit {
                        dumped_diffs += 1;
                        let mut p = String::new();
                        let mut o = String::new();
                        fmt_tree(pin, 0, 8, &mut p);
                        fmt_tree(ours, 0, 8, &mut o);
                        println!(
                            "--- DIFF #{dumped_diffs} {file}@{start} ({pin_k} vs {ours_k}) ---"
                        );
                        println!("PIN:\n{p}OURS:\n{o}");
                    }
                }
            }
        }
        if header_ok && file_bad == 0 {
            identical_files += 1;
        }
        if !pin_cmds.is_empty() {
            nonempty_files += 1;
            if file_bad == 0 {
                identical_nonempty_files += 1;
            }
        }
        if file_bad > 0 {
            worst_files.push((file_bad, pin_cmds.len(), (*file).to_owned()));
        }
    }

    let identical = histogram.get("identical").copied().unwrap_or(0);
    let mut rows: Vec<_> = histogram.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    println!(
        "STAGE 5 GENERATED REGISTRY FRONTIER ({:.2}s): {identical}/{total_cmds} ({:.2}%) commands identical; \
         {identical_files}/{} files wholly identical ({identical_nonempty_files}/{nonempty_files} non-empty); \
         headers {identical_headers}/{}; \
         files_with_errors={files_with_errors} total_errors={total_errors} budget_exhausted={budget_exhausted_files}",
        t0.elapsed().as_secs_f64(),
        (identical as f64) * 100.0 / (total_cmds.max(1) as f64),
        files.len(),
        files.len(),
    );
    for (class, count) in rows.iter().take(40) {
        let ex = examples
            .get(*class)
            .map(|v| v.join(" | "))
            .unwrap_or_default();
        println!("  {count:>6}  {class}  [{ex}]");
    }
    worst_files.sort_by(|a, b| b.0.cmp(&a.0).then(a.2.cmp(&b.2)));
    println!("TOP 25 FILES BY NON-IDENTICAL COMMANDS:");
    for (bad, total, file) in worst_files.iter().take(25) {
        println!("  {bad:>4}/{total:<4}  {file}");
    }
}
