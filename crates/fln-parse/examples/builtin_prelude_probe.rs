//! Step 3 probe for `fln-generated-builtin-grammar-spike-kcvj`:
//! parses `Init/Prelude.lean` with `BuiltinInterpreter` and compares the header
//! and all 775 commands losslessly (exact `Syntax` equality including `SourceInfo`)
//! against the pinned `dump_command_syntax.lean --lossless` oracle dump.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::builtin_interpreter::{first_syntax_diff, reference_builtin_interpreter};
use fln_syntax::pin_syntax;
use fln_syntax::source::{BytePos, SourceText};
use std::collections::BTreeMap;
use std::process::ExitCode;
use std::time::Instant;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: builtin_prelude_probe <Prelude.lean> <oracle.txt>");
        return ExitCode::from(2);
    }
    let prelude_path = &args[0];
    let oracle_path = &args[1];

    let src_bytes = match std::fs::read(prelude_path) {
        Ok(b) => b,
        Err(err) => {
            eprintln!("failed to read {prelude_path}: {err}");
            return ExitCode::from(2);
        }
    };
    let oracle_text = match std::fs::read_to_string(oracle_path) {
        Ok(s) => s,
        Err(err) => {
            eprintln!("failed to read {oracle_path}: {err}");
            return ExitCode::from(2);
        }
    };
    let oracle = match pin_syntax::read(&oracle_text, &src_bytes) {
        Ok(o) => o,
        Err(err) => {
            eprintln!("failed to read oracle dump: {err}");
            return ExitCode::from(2);
        }
    };
    let src = match SourceText::from_utf8(&src_bytes) {
        Ok(s) => s,
        Err(err) => {
            eprintln!("non-UTF-8 prelude: {err}");
            return ExitCode::from(2);
        }
    };

    let t0 = Instant::now();
    let interp = reference_builtin_interpreter();
    let compile_elapsed = t0.elapsed();
    let t1 = Instant::now();
    let parsed = interp.parse_module(&src, 500_000_000);
    let parse_elapsed = t1.elapsed();

    let header_exact = parsed.header == oracle.header;
    let paired = parsed.commands.len().min(oracle.commands.len());
    let mut exact_cmds = 0usize;
    let mut exact_kinds = 0usize;
    let mut first_diffs: Vec<String> = Vec::new();
    let mut diff_classes: BTreeMap<String, usize> = BTreeMap::new();
    for i in 0..paired {
        if parsed.commands[i] == oracle.commands[i] {
            exact_cmds += 1;
            exact_kinds += 1;
        } else {
            if parsed.commands[i].kind() == oracle.commands[i].kind() {
                exact_kinds += 1;
            }
            let diff = first_syntax_diff(&parsed.commands[i], &oracle.commands[i])
                .unwrap_or_else(|| "unknown".to_owned());
            let class_key = diff
                .split_once(':')
                .map_or_else(|| diff.clone(), |(p, _)| p.to_owned());
            *diff_classes.entry(class_key).or_default() += 1;
            if first_diffs.len() < 25 {
                let line = oracle.commands[i]
                    .info()
                    .pos(false)
                    .map_or(0, |p| src.line_of(p) + 1);
                first_diffs.push(format!("CMD {i} (line ~{line}): {diff}"));
            }
        }
    }

    let printed_dump = pin_syntax::print(
        &pin_syntax::PinTrees {
            header: parsed.header.clone(),
            commands: parsed.commands.clone(),
            messages: Vec::new(),
        },
        &src_bytes,
    );
    let dump_byte_identical = printed_dump.as_deref() == Ok(oracle_text.as_str());

    let pct = 100.0 * (exact_cmds as f64) / (oracle.commands.len().max(1) as f64);
    println!(
        "PRELUDE LOSSLESS ORACLE: defs={} cats={} compile={:.3}s parse={:.3}s \
         header_exact={header_exact} parsed_cmds={} oracle_cmds={} \
         exact_cmds={exact_cmds}/{} ({pct:.2}%) exact_kinds={exact_kinds}/{} \
         dump_byte_identical={dump_byte_identical} errors={} steps={} budget_exhausted={}",
        interp.def_count(),
        interp.category_count(),
        compile_elapsed.as_secs_f64(),
        parse_elapsed.as_secs_f64(),
        parsed.commands.len(),
        oracle.commands.len(),
        oracle.commands.len(),
        oracle.commands.len(),
        parsed.errors.len(),
        parsed.steps_used,
        parsed.budget_exhausted,
    );
    if !header_exact {
        println!(
            "HEADER DIFF: {:?}",
            first_syntax_diff(&parsed.header, &oracle.header)
        );
    }
    for e in parsed.errors.iter().take(20) {
        let line = src.line_of(BytePos(e.pos.min(src.len_bytes()))) + 1;
        println!(
            "  PARSE ERR line {line} byte {}: unexpected={:?} expected={:?}",
            e.pos, e.unexpected, e.expected
        );
    }
    for d in &first_diffs {
        println!("  DIFF: {d}");
    }
    if !diff_classes.is_empty() {
        let mut sorted: Vec<(usize, &String)> = diff_classes.iter().map(|(k, v)| (*v, k)).collect();
        sorted.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
        println!("=== TOP DIFF CLASSES ===");
        for (cnt, cls) in sorted.into_iter().take(20) {
            println!("  {cnt:>4}  {cls}");
        }
    }
    for cat in ["command", "term", "tactic", "level", "doElem", "attr"] {
        if let Some((li, lu, ti, tu)) = interp.category_summary(&Name::from_components([cat])) {
            println!(
                "  cat {cat:<8}: lead_idx={li} lead_unidx={lu} trail_idx={ti} trail_unidx={tu}"
            );
        }
    }
    if header_exact && pct >= 90.0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
