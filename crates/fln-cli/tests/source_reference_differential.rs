//! Source-pipeline Reference differential (bead franken_lean-z8j.1.5).
//!
//! Every Lean source fixture this repository presents as Lean is judged by the
//! pinned Reference `lean` (Tribunal oracle, D8 capacity 1) and by FrankenLean's
//! two source front doors (`lean` and `fln check-source`). The observed
//! acceptance and `#eval`/`#check` output must match the checked-in ledger row
//! for that file, and every divergence must carry a class naming why it exists.
//! An unclassified divergence, a changed outcome, or a stale row fails, so the
//! ledger shrinks as divergences are fixed and cannot silently grow.
//!
//! FrankenLean's outcome is `accept` when its drop-in `lean` exits 0,
//! `check-only` when only `fln check-source` does, and `reject` otherwise. The
//! dangerous direction is accepting source the Reference rejects, whichever
//! door does it.
//! Output is compared only when the Reference and FrankenLean's `lean` both
//! accept: the Reference's `--json` information messages, in order, must equal
//! FrankenLean's stdout lines. Reference warnings (linters) are not compared.
//!
//! Without the pinned Reference toolchain the test prints a typed SKIP; set
//! `FLN_REQUIRE_REFERENCE=1` in any job that installs the pin so absence fails.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const LEDGER: &str = "crates/fln-cli/tests/fixtures/reference_differential.tsv";
const LADDER: &str = "crates/fln-cli/tests/fixtures/source_ladder";
const WORKERS: usize = 8;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Observed {
    reference: &'static str,
    frankenlean: &'static str,
    output: &'static str,
    reference_first_error: String,
}

#[derive(Debug, Clone)]
struct LedgerRow {
    reference: String,
    frankenlean: String,
    output: String,
    class: String,
    note: String,
}

fn reference_lean(root: &Path) -> Result<PathBuf, String> {
    let lock = std::fs::read_to_string(root.join("SUITE.lock"))
        .map_err(|error| format!("cannot read SUITE.lock: {error}"))?;
    let tag = lock
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|word| word.strip_prefix("tag="))
        })
        .ok_or("SUITE.lock has no reference tag")?
        .to_owned();
    let elan = std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".elan")))
        .ok_or("neither ELAN_HOME nor HOME is set")?;
    let lean = elan
        .join("toolchains")
        .join(format!("leanprover--lean4---{tag}"))
        .join("bin")
        .join("lean");
    if lean.is_file() {
        Ok(lean)
    } else {
        Err(format!(
            "pinned Reference lean not found at {}",
            lean.display()
        ))
    }
}

/// Decode the JSON string value of `key` in one flat JSON object line.
fn json_string_field(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\":\"");
    let start = line.find(&needle)? + needle.len();
    let mut out = String::new();
    let mut chars = line[start..].chars();
    while let Some(ch) = chars.next() {
        match ch {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                'b' => out.push('\u{8}'),
                'f' => out.push('\u{c}'),
                'u' => {
                    let code: String = chars.by_ref().take(4).collect();
                    let mut value = u32::from_str_radix(&code, 16).ok()?;
                    if (0xD800..0xDC00).contains(&value) {
                        if chars.next()? != '\\' || chars.next()? != 'u' {
                            return None;
                        }
                        let low: String = chars.by_ref().take(4).collect();
                        let low = u32::from_str_radix(&low, 16).ok()?;
                        value = 0x10000 + ((value - 0xD800) << 10) + (low - 0xDC00);
                    }
                    out.push(char::from_u32(value)?);
                }
                other => out.push(other),
            },
            other => out.push(other),
        }
    }
    None
}

fn observe(reference: &Path, file: &Path) -> Observed {
    let reference_run = Command::new(reference)
        .arg("--json")
        .arg(file)
        .output()
        .expect("run pinned Reference lean");
    let reference_json = String::from_utf8_lossy(&reference_run.stdout);
    let mut information = Vec::new();
    let mut first_error = String::new();
    for line in reference_json.lines().filter(|line| line.starts_with('{')) {
        let severity = json_string_field(line, "severity").unwrap_or_default();
        let data = json_string_field(line, "data").unwrap_or_default();
        if severity == "information" {
            information.push(data);
        } else if severity == "error" && first_error.is_empty() {
            let line_no = line
                .split("\"pos\":{")
                .nth(1)
                .and_then(|pos| pos.split("\"line\":").nth(1))
                .and_then(|rest| rest.split(|c: char| !c.is_ascii_digit()).next())
                .unwrap_or("?");
            first_error = format!("{}: {}", line_no, data.lines().next().unwrap_or_default());
        }
    }
    let reference_accepts = reference_run.status.success();

    let lean_run = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(file)
        .output()
        .expect("run FrankenLean lean");
    let check_run = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(file)
        .output()
        .expect("run fln check-source");
    let frankenlean = if lean_run.status.success() {
        "accept"
    } else if check_run.status.success() {
        "check-only"
    } else {
        "reject"
    };

    let output = if reference_accepts && lean_run.status.success() {
        let mut expected = information.join("\n");
        if !expected.is_empty() {
            expected.push('\n');
        }
        if String::from_utf8_lossy(&lean_run.stdout) == expected {
            "match"
        } else {
            "differ"
        }
    } else {
        "n/a"
    };
    Observed {
        reference: if reference_accepts {
            "accept"
        } else {
            "reject"
        },
        frankenlean,
        output,
        reference_first_error: first_error,
    }
}

fn corpus(root: &Path) -> Vec<String> {
    let mut files = Vec::new();
    for dir in ["examples", LADDER] {
        let entries = std::fs::read_dir(root.join(dir)).expect("read corpus directory");
        for entry in entries {
            let path = entry.expect("corpus entry").path();
            if path.extension().and_then(|ext| ext.to_str()) == Some("lean") {
                let relative = path.strip_prefix(root).expect("corpus under root");
                files.push(relative.to_string_lossy().into_owned());
            }
        }
    }
    files.sort();
    files
}

fn load_ledger(root: &Path) -> BTreeMap<String, LedgerRow> {
    let text = std::fs::read_to_string(root.join(LEDGER)).expect("read differential ledger");
    let mut rows = BTreeMap::new();
    for (number, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        assert_eq!(
            fields.len(),
            6,
            "{LEDGER}:{}: expected 6 tab-separated fields",
            number + 1
        );
        let previous = rows.insert(
            fields[0].to_owned(),
            LedgerRow {
                reference: fields[1].to_owned(),
                frankenlean: fields[2].to_owned(),
                output: fields[3].to_owned(),
                class: fields[4].to_owned(),
                note: fields[5].to_owned(),
            },
        );
        assert!(
            previous.is_none(),
            "{LEDGER}: duplicate row for {}",
            fields[0]
        );
    }
    rows
}

/// The class a row may carry for its observed outcome.
fn class_is_valid(observed: &Observed, row: &LedgerRow) -> bool {
    match (observed.reference, observed.frankenlean, observed.output) {
        ("accept", "accept", "match") | ("reject", "reject", _) => row.class == "agree",
        ("accept", "accept", _) => row.class == "output-defect" && !row.note.is_empty(),
        // The drop-in `lean` door refuses Reference-accepted source (possibly
        // while the checker door accepts it): a capability gap, not a false accept.
        ("accept", "check-only" | "reject", _) => row.class == "unsupported",
        ("reject", "accept" | "check-only", _) => {
            matches!(
                row.class.as_str(),
                "fln-defect" | "missing-prelude" | "behavior-note" | "oracle-investigation"
            ) && !row.note.is_empty()
        }
        _ => false,
    }
}

#[test]
fn every_source_fixture_matches_its_reference_differential_ledger_row() {
    let root = fln_core::checked_workspace_root!();
    let reference = match reference_lean(&root) {
        Ok(reference) => reference,
        Err(reason) => {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "FLN_REQUIRE_REFERENCE is set but {reason}"
            );
            eprintln!("SKIP source_reference_differential: {reason}");
            return;
        }
    };
    let files = corpus(&root);
    assert!(
        files.len() >= 100,
        "corpus scan found only {} files; a broken scan is not a clean corpus",
        files.len()
    );

    let next = AtomicUsize::new(0);
    let observed = Mutex::new(BTreeMap::new());
    std::thread::scope(|scope| {
        for _ in 0..WORKERS {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(file) = files.get(index) else { break };
                    let result = observe(&reference, &root.join(file));
                    observed.lock().unwrap().insert(file.clone(), result);
                }
            });
        }
    });
    let observed = observed.into_inner().unwrap();

    let ledger = load_ledger(&root);
    let mut problems = Vec::new();
    for (file, seen) in &observed {
        let proposed = format!(
            "{file}\t{}\t{}\t{}\tCLASS\t{}",
            seen.reference, seen.frankenlean, seen.output, seen.reference_first_error
        );
        match ledger.get(file) {
            None => problems.push(format!("no ledger row; observed: {proposed}")),
            Some(row) => {
                if row.reference != seen.reference
                    || row.frankenlean != seen.frankenlean
                    || row.output != seen.output
                {
                    problems.push(format!(
                        "outcome changed (ledger {} / {} / {}); observed: {proposed}",
                        row.reference, row.frankenlean, row.output
                    ));
                } else if !class_is_valid(seen, row) {
                    problems.push(format!(
                        "class `{}` is not valid for this outcome; observed: {proposed}",
                        row.class
                    ));
                }
            }
        }
    }
    for file in ledger.keys() {
        if !observed.contains_key(file) {
            problems.push(format!("stale ledger row for {file}: no such corpus file"));
        }
    }
    let divergent = observed
        .values()
        .filter(|seen| seen.reference == "reject" && seen.frankenlean != "reject")
        .count();
    eprintln!(
        "source_reference_differential: {} files, {divergent} accepted by FrankenLean but rejected by the Reference",
        observed.len()
    );
    assert!(
        problems.is_empty(),
        "{} ledger problem(s) in {LEDGER}:\n{}",
        problems.len(),
        problems.join("\n")
    );
}

#[test]
fn json_string_field_decodes_escapes_and_surrogate_pairs() {
    let line = r#"{"data":"a\"b\\c\ndé😀","severity":"information"}"#;
    assert_eq!(
        json_string_field(line, "data").as_deref(),
        Some("a\"b\\c\nd\u{e9}\u{1F600}")
    );
    assert_eq!(
        json_string_field(line, "severity").as_deref(),
        Some("information")
    );
    assert_eq!(json_string_field(line, "missing"), None);
}

#[test]
fn class_rules_refuse_an_unclassified_false_acceptance() {
    let observed = Observed {
        reference: "reject",
        frankenlean: "accept",
        output: "n/a",
        reference_first_error: "3: Type mismatch".to_owned(),
    };
    let row = |class: &str, note: &str| LedgerRow {
        reference: "reject".to_owned(),
        frankenlean: "accept".to_owned(),
        output: "n/a".to_owned(),
        class: class.to_owned(),
        note: note.to_owned(),
    };
    assert!(!class_is_valid(&observed, &row("agree", "")));
    assert!(!class_is_valid(&observed, &row("fln-defect", "")));
    assert!(class_is_valid(
        &observed,
        &row("fln-defect", "bead franken_lean-z8j.1.6.3")
    ));
}

/// The seed-dialect freeze, held without the pin (bead fln-ew20): every file
/// this repository presents as Lean has a ledger row, and a row that does not
/// `agree` with the Reference must be one of `DIVERGENCE_ALLOWANCE`. Whether
/// each row still describes the real outcome is the pinned rig's job above.
fn freeze_problems(
    files: &[String],
    ledger: &BTreeMap<String, LedgerRow>,
    allowance: &[&str],
) -> Vec<String> {
    let allowed: std::collections::BTreeSet<&str> = allowance.iter().copied().collect();
    let mut problems = Vec::new();
    for file in files {
        match ledger.get(file) {
            None => problems.push(format!(
                "{file}: no ledger row; derive it with the pinned rig, and a new example must agree"
            )),
            Some(row) if row.class != "agree" && !allowed.contains(file.as_str()) => {
                problems.push(format!(
                    "{file}: class `{}` is outside the frozen divergence allowance; a new or changed \
                     example must agree with the Reference",
                    row.class
                ));
            }
            Some(_) => {}
        }
    }
    problems
}

#[test]
fn every_corpus_file_has_a_row_and_no_new_divergence_is_admitted() {
    let root = fln_core::checked_workspace_root!();
    let files = corpus(&root);
    let ledger = load_ledger(&root);
    assert!(
        files.len() >= 100 && ledger.len() >= 100,
        "corpus {} files, ledger {} rows: a broken scan is not a clean corpus",
        files.len(),
        ledger.len()
    );
    let problems = freeze_problems(&files, &ledger, DIVERGENCE_ALLOWANCE);
    assert!(
        problems.is_empty(),
        "{} freeze problem(s) in {LEDGER}:\n{}",
        problems.len(),
        problems.join("\n")
    );
}

#[test]
fn the_freeze_refuses_unledgered_or_newly_divergent_files_and_admits_a_repair() {
    let row = |class: &str| LedgerRow {
        reference: "accept".to_owned(),
        frankenlean: "accept".to_owned(),
        output: "match".to_owned(),
        class: class.to_owned(),
        note: String::new(),
    };
    let files: Vec<String> = ["a.lean", "b.lean", "c.lean"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    let mut ledger = BTreeMap::from([
        ("a.lean".to_owned(), row("agree")),
        ("b.lean".to_owned(), row("fln-defect")),
    ]);
    // `c.lean` has no row, and `b.lean` diverges without an allowance entry.
    let problems = freeze_problems(&files, &ledger, &[]);
    assert_eq!(problems.len(), 2, "{problems:?}");
    assert!(
        problems[0].starts_with("b.lean: class `fln-defect`"),
        "{problems:?}"
    );
    assert!(
        problems[1].starts_with("c.lean: no ledger row"),
        "{problems:?}"
    );
    // An allowed divergence passes; a missing row still does not.
    ledger.insert("c.lean".to_owned(), row("agree"));
    assert!(freeze_problems(&files, &ledger, &["b.lean"]).is_empty());
    assert_eq!(freeze_problems(&files, &ledger, &[]).len(), 1);
    // A repaired row agrees, so its entry can be deleted.
    ledger.insert("b.lean".to_owned(), row("agree"));
    assert!(freeze_problems(&files, &ledger, &[]).is_empty());
}

/// Rows that did not agree with the Reference when the freeze was enforced
/// (fln-ew20, measured at 022c8ce3). One-way: delete an entry once its row
/// agrees; never add one.
const DIVERGENCE_ALLOWANCE: &[&str] = &[
    "crates/fln-cli/tests/fixtures/source_ladder/induction_rw.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/inductive_equation_compiler.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/init_lemma_reference.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/io_main.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/omega_and_simp.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/option_do_notation.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/string_interpolation.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/structure_instance_anonymous_constructor.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/theorem_rfl_numerals.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/typeclass_polymorphic_fold.lean",
    "crates/fln-cli/tests/fixtures/source_ladder/user_notation.lean",
    "examples/native_closure_data.lean",
    "examples/native_constrained_matching.lean",
    "examples/native_constrained_recursion.lean",
    "examples/native_constructor_equalities.lean",
    "examples/native_constructor_equality.lean",
    "examples/native_constructor_tactics.lean",
    "examples/native_context_generalization.lean",
    "examples/native_decidable_cases.lean",
    "examples/native_decision_proofs.lean",
    "examples/native_default_simp.lean",
    "examples/native_dependent_indices.lean",
    "examples/native_do.lean",
    "examples/native_empty_elimination.lean",
    "examples/native_equality_transport.lean",
    "examples/native_equations.lean",
    "examples/native_expression_elimination.lean",
    "examples/native_function_children.lean",
    "examples/native_goal_control.lean",
    "examples/native_heterogeneous_equality.lean",
    "examples/native_index_refinement.lean",
    "examples/native_indexed.lean",
    "examples/native_indexed_elimination.lean",
    "examples/native_indexed_function_children.lean",
    "examples/native_indexed_vectors.lean",
    "examples/native_induction.lean",
    "examples/native_induction_specialization.lean",
    "examples/native_instance_attributes.lean",
    "examples/native_interleaved_specialization.lean",
    "examples/native_local_proofs.lean",
    "examples/native_logical_rewriting.lean",
    "examples/native_matrix_recursion.lean",
    "examples/native_mutual_data.lean",
    "examples/native_mutual_folds.lean",
    "examples/native_mutual_function_children.lean",
    "examples/native_mutual_groups.lean",
    "examples/native_mutual_indexed.lean",
    "examples/native_option_decide.lean",
    "examples/native_parameterized_recursion.lean",
    "examples/native_pattern_matching.lean",
    "examples/native_pattern_matrices.lean",
    "examples/native_proposition_conditionals.lean",
    "examples/native_quotients.lean",
    "examples/native_record_values.lean",
    "examples/native_records.lean",
    "examples/native_recursion.lean",
    "examples/native_refinement.lean",
    "examples/native_scoped_instances.lean",
    "examples/native_scopes.lean",
    "examples/native_section_inductives.lean",
    "examples/native_section_records.lean",
    "examples/native_simp_all.lean",
    "examples/native_simp_hypotheses.lean",
    "examples/native_simpa.lean",
    "examples/native_simplification.lean",
    "examples/native_tactic_repetition.lean",
];
