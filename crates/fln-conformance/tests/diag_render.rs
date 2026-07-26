//! Faithful-renderer goldens against REAL Reference diagnostics (bead fln-rk6):
//! every single-line frame in the epoch lab's D1 transcripts is parsed into a typed
//! [`Diagnostic`] and re-rendered by fln-core's faithful renderer — the output must
//! be byte-identical to what the pinned binary printed. The frame is exact-class
//! evidence; message bodies pass through verbatim (their producers are later
//! subsystems, each proven at its own bead).

#![forbid(unsafe_code)]

use std::path::Path;

use fln_core::diag::{Diagnostic, Epoch, ErrorValue, RenderMode, Severity, render_cli};
use fln_core::name::Name;
use fln_core::pos::Position;

fn workspace_root() -> &'static Path {
    static ROOT: std::sync::OnceLock<std::path::PathBuf> = std::sync::OnceLock::new();
    ROOT.get_or_init(|| fln_conformance::checked_workspace_root!())
        .as_path()
}

/// Parse one Reference CLI frame line: `{path}:{line}:{col}: error: {msg}` or
/// `{path}:{line}:{col}: error({name}): {msg}` (warning likewise). Returns `None`
/// for non-frame lines (continuations, plain output).
fn parse_frame(line: &str) -> Option<Diagnostic> {
    let mut parts = line.splitn(5, ':');
    let file_name = parts.next()?.to_string();
    let line_no: usize = parts.next()?.parse().ok()?;
    let col_no: usize = parts.next()?.parse().ok()?;
    let label = parts.next()?;
    let message = parts.next()?.strip_prefix(' ')?.to_string();
    let label = label.strip_prefix(' ')?;
    let (severity, name_part) = match label.strip_prefix("error") {
        Some(rest) => (Severity::Error, rest),
        None => (Severity::Warning, label.strip_prefix("warning")?),
    };
    let error_name = if name_part.is_empty() {
        None
    } else {
        let inner = name_part.strip_prefix('(')?.strip_suffix(')')?;
        Some(Name::from_components(inner.split('.')))
    };
    Some(Diagnostic {
        file_name,
        pos: Position {
            line: line_no,
            column: col_no,
        },
        end_pos: None,
        severity,
        error_name,
        caption: String::new(),
        value: ErrorValue::SyntaxFailure { message },
    })
}

/// The epoch-lab directory. `FLN_EPOCH_LAB_DIR` (repo-relative) exists solely so the
/// E2E harness can point the goldens at a seeded-corruption copy; the default is the
/// published lab and CI never overrides it.
fn epoch_lab_dir() -> String {
    std::env::var("FLN_EPOCH_LAB_DIR").unwrap_or_else(|_| "tribunal/epochs/v4.32.0".to_string())
}

#[test]
fn faithful_renderer_reproduces_real_reference_frames_byte_for_byte() {
    let root = workspace_root();
    let lab = epoch_lab_dir();
    let manifest = std::fs::read_to_string(root.join(format!("{lab}/MANIFEST.txt")))
        .expect("epoch lab published");
    let d1_files: Vec<&str> = manifest
        .lines()
        .filter(|l| l.starts_with("d1 ") || l.starts_with("d1-quirk "))
        .map(|l| l.split_whitespace().nth(1).expect("d1 row has a file"))
        .collect();
    assert!(!d1_files.is_empty(), "the D1 corpus exists");

    let mut goldens = 0usize;
    let mut failures: Vec<String> = Vec::new();
    for file in &d1_files {
        let transcript =
            std::fs::read_to_string(root.join(format!("{lab}/transcripts/{file}.stdout")))
                .expect("transcript exists");
        let lines: Vec<&str> = transcript.lines().collect();
        for (i, line) in lines.iter().enumerate() {
            let Some(diag) = parse_frame(line) else {
                continue;
            };
            // Only single-line messages golden cleanly: the next line must be
            // another frame or EOF, otherwise this frame owns continuation lines.
            let next_is_boundary = lines
                .get(i + 1)
                .is_none_or(|next| parse_frame(next).is_some());
            if !next_is_boundary {
                continue;
            }
            goldens += 1;
            let rendered = render_cli(&diag, RenderMode::Faithful, Epoch::V4_32_0);
            let expected = format!("{line}\n");
            if rendered != expected {
                failures.push(format!(
                    "{file}: ours   `{}`\n{file}: oracle `{}`",
                    rendered.trim_end(),
                    expected.trim_end()
                ));
            }
        }
    }
    assert!(
        goldens >= 6,
        "expected at least 6 golden frames across the D1 corpus, found {goldens}"
    );
    assert!(
        failures.is_empty(),
        "{} frame mismatch(es) against the pinned binary:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn the_frame_parser_itself_is_exercised_by_the_labeled_form() {
    // 1707.lean carries the `error(lean.unknownIdentifier)` label — prove the
    // labeled path is part of the golden corpus, not dead code.
    let d = parse_frame("vendor/x.lean:1:9: error(lean.unknownIdentifier): Unknown identifier `c`")
        .expect("labeled frame parses");
    assert_eq!(
        d.error_name.as_ref().map(Name::to_display_string),
        Some("lean.unknownIdentifier".to_string())
    );
    assert_eq!(
        render_cli(&d, RenderMode::Faithful, Epoch::V4_32_0),
        "vendor/x.lean:1:9: error(lean.unknownIdentifier): Unknown identifier `c`\n"
    );
    // Continuation lines are not frames.
    assert!(parse_frame("  expected ':='").is_none());
}
