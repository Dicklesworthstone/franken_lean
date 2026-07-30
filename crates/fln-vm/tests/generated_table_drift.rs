//! `generated_table_drift` — the mutation battery against the committed extern
//! row contract artifacts (bead `franken_lean-pw6t`).
//!
//! Every cell plants exactly one fault against the REAL committed contract and
//! requires the load to refuse it **for the intended reason**: a green that
//! cannot name its law is not a kill. The suite re-implements the hash framing
//! independently (a one-sided drift has nowhere to hide) and carries a
//! `reseal()` helper, so a mutated contract can be made structurally valid
//! everywhere except the targeted fault — including the deepest cell, a fully
//! resealed fake, which parses cleanly and must die at the projection zip.

#![forbid(unsafe_code)]

use fln_vm::extern_row::{CONTRACT_ROOT_DOMAIN, ROW_FIELD_ORDER, parse_fields};
use fln_vm::load::{embedded_contract_text, load, load_embedded, parse};

// --- the independent hash reimplementation -------------------------------------
// A third copy of the framing law exists so that a one-sided bug in generator
// or consumer cannot agree with itself. If all three disagree, the cell that
// compares them fails.

fn fnv(payload: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in payload {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn framed(domain: &str, fields: &[&str]) -> String {
    let mut payload = Vec::new();
    for field in std::iter::once(domain).chain(fields.iter().copied()) {
        payload.extend_from_slice(&(field.len() as u64).to_le_bytes());
        payload.extend_from_slice(field.as_bytes());
    }
    fnv(&payload)
}

/// Recompute the terminal contract-root over the placeholder form of the
/// projection line — the two-pass law, re-derived here rather than trusted.
fn contract_root_of(lines: &[String]) -> String {
    framed(
        CONTRACT_ROOT_DOMAIN,
        &lines.iter().map(String::as_str).collect::<Vec<_>>(),
    )
}

fn lines_of(text: &str) -> Vec<String> {
    text.split_terminator('\n').map(str::to_string).collect()
}

fn join(lines: &[String]) -> String {
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

fn root_line_index(lines: &[String]) -> usize {
    lines
        .iter()
        .rposition(|line| line.starts_with("contract-root "))
        .expect("the real contract carries a terminal contract-root")
}

/// Replace the terminal contract-root with a freshly computed one, so the
/// mutation is structurally valid except for the targeted fault. The two-pass
/// law applies: the projection line carries the placeholder during hashing and
/// the fresh root after.
fn reseal(lines: &mut [String]) {
    let index = root_line_index(lines);
    for line in lines[..index].iter_mut() {
        if line.starts_with("projection ") {
            let pos = line
                .rfind("template-root=")
                .expect("projection carries template-root");
            *line = format!(
                "{}template-root=fnv1a64:EXTERN_ROW_CONTRACT_ROOT",
                &line[..pos]
            );
        }
    }
    let root = contract_root_of(&lines[..index]);
    for line in lines[..index].iter_mut() {
        if line.starts_with("projection ") {
            *line = line.replace("fnv1a64:EXTERN_ROW_CONTRACT_ROOT", &root);
        }
    }
    lines[index] = format!("contract-root {root}");
}

fn mutate_first_row(lines: &mut [String], mutate: impl Fn(&mut String)) {
    let index = lines
        .iter()
        .position(|line| line.starts_with("row "))
        .expect("the real contract carries rows");
    mutate(&mut lines[index]);
}

// --- control --------------------------------------------------------------------

#[test]
fn control_the_committed_contract_loads_clean() {
    let contract = load_embedded().expect("the committed contract must load");
    assert_eq!(contract.rows.len(), 954);
    assert_eq!(contract.schema, "fln-extern-row-contract/1");
    assert_eq!(contract.name, "ExternRowContractV1");
    let first = contract.row("extern:Array.emptyWithCapacity");
    assert!(first.is_some(), "a spot row resolves by stable id");
    assert_eq!(first.map(|row| row.arity), Some(2));
}

// --- the battery ------------------------------------------------------------------

#[test]
fn mutant_a_corrupted_contract_root_is_caught() {
    // Corrupt the root consistently on both sides (the root row and the
    // projection's template-root), so the mutation survives the projection law
    // and must die at the recompute. The single-side corruption is the
    // projection law's cell in extern_schema_fuzz.
    let mut lines = lines_of(embedded_contract_text());
    let index = root_line_index(&lines);
    let corrupt = |line: &str| -> String {
        let hash_pos = line
            .find("fnv1a64:")
            .expect("fnv1a64-framed")
            + "fnv1a64:".len();
        let digit_pos = line[hash_pos..]
            .find(|c: char| c.is_ascii_hexdigit())
            .expect("hex digits present")
            + hash_pos;
        let old = line.as_bytes()[digit_pos] as char;
        let replacement = if old == 'a' { 'b' } else { 'a' };
        let mut out = line.to_string();
        out.replace_range(digit_pos..digit_pos + 1, &replacement.to_string());
        out
    };
    lines[index] = corrupt(&lines[index]);
    let projection_index = lines
        .iter()
        .position(|line| line.starts_with("projection "))
        .expect("projection line present");
    lines[projection_index] = corrupt(&lines[projection_index]);
    let error = load(&join(&lines)).expect_err("a corrupted root must refuse");
    assert!(
        error.message().contains("does not recompute"),
        "expected the root law to name itself, got: {}",
        error.message()
    );
}

#[test]
fn mutant_an_omitted_row_moves_the_population() {
    let mut lines = lines_of(embedded_contract_text());
    let index = lines
        .iter()
        .position(|line| line.starts_with("row "))
        .unwrap();
    lines.remove(index);
    reseal(&mut lines);
    let error = load(&join(&lines)).expect_err("an omitted row must refuse");
    assert!(
        error.message().contains("954") || error.message().contains("row-count"),
        "expected the population law, got: {}",
        error.message()
    );
}

#[test]
fn mutant_a_duplicated_row_is_caught() {
    let mut lines = lines_of(embedded_contract_text());
    let index = lines
        .iter()
        .position(|line| line.starts_with("row "))
        .unwrap();
    let row = lines[index].clone();
    lines.insert(index, row);
    reseal(&mut lines);
    let error = load(&join(&lines)).expect_err("a duplicated row must refuse");
    assert!(
        error.message().contains("sorted and unique") || error.message().contains("row-count"),
        "expected the uniqueness or population law, got: {}",
        error.message()
    );
}

#[test]
fn mutant_a_noncanonical_escape_is_caught() {
    let mut lines = lines_of(embedded_contract_text());
    mutate_first_row(&mut lines, |row| {
        let replaced = row.replacen("%3B", "%3b", 1);
        assert_ne!(&replaced, row, "the first row must carry a %3B to mutate");
        *row = replaced;
    });
    reseal(&mut lines);
    let error = load(&join(&lines)).expect_err("a noncanonical escape must refuse");
    assert!(
        error.message().contains("canonically percent-encoded"),
        "expected the canonical-codec law, got: {}",
        error.message()
    );
}

#[test]
fn mutant_a_schema_version_mix_is_caught() {
    let mut lines = lines_of(embedded_contract_text());
    lines[0] = "schema fln-extern-row-contract/2".to_string();
    reseal(&mut lines);
    let error = load(&join(&lines)).expect_err("a schema mix must refuse");
    assert!(
        error.message().contains("fln-extern-row-contract/1"),
        "expected the schema law, got: {}",
        error.message()
    );
}

#[test]
fn mutant_a_moved_observation_platform_is_caught() {
    let mut lines = lines_of(embedded_contract_text());
    lines[6] = "observation-platform windows-x86_64".to_string();
    reseal(&mut lines);
    let error = load(&join(&lines)).expect_err("a moved platform must refuse");
    assert!(
        error.message().contains("linux-x86_64"),
        "expected the platform law, got: {}",
        error.message()
    );
}

#[test]
fn mutant_a_field_edit_without_reseal_dies_at_the_row_root() {
    let mut lines = lines_of(embedded_contract_text());
    mutate_first_row(&mut lines, |row| {
        assert!(row.contains(" arity=2 "), "the first row carries arity=2");
        *row = row.replacen(" arity=2 ", " arity=3 ", 1);
    });
    // Note the absence of reseal(): the row-root no longer matches the fields.
    let error = load(&join(&lines)).expect_err("an unresealed field edit must refuse");
    assert!(
        error.message().contains("recomputes"),
        "expected the row-root law, got: {}",
        error.message()
    );
}

#[test]
fn mutant_a_fully_resealed_fake_dies_at_the_projection_zip() {
    // The deepest cell: mutate a field, reseal the row-root AND the
    // contract-root with the independent reimplementation, so the fake is
    // structurally valid at every stage that reads it alone. It must die at the
    // generated-projection stage, because the committed Rust table does not
    // carry the lie.
    let mut lines = lines_of(embedded_contract_text());
    mutate_first_row(&mut lines, |row| {
        *row = row.replacen(" arity=2 ", " arity=99 ", 1);
        // Reseal the row itself: recompute the row-root from the mutated fields.
        let fields =
            parse_fields(row.strip_prefix("row ").expect("row prefix")).expect("fields parse");
        let root_fields: Vec<&str> = ROW_FIELD_ORDER
            .iter()
            .take(ROW_FIELD_ORDER.len() - 1)
            .map(|key| fields[*key].as_str())
            .collect();
        let new_root = framed(fln_vm::extern_row::ROW_ROOT_DOMAIN, &root_fields);
        *row = row
            .split_ascii_whitespace()
            .map(|token| {
                if token.starts_with("row-root=") {
                    format!("row-root={new_root}")
                } else {
                    token.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join(" ");
    });
    reseal(&mut lines);
    let text = join(&lines);
    let parsed = parse(&text).expect("a fully resealed fake parses: its laws hold");
    let error = fln_vm::load::validate_generated_projection(&parsed)
        .expect_err("the projection zip must catch the lie the roots cannot");
    assert!(
        error.message().contains("carries root") || error.message().contains("diverges"),
        "expected the projection law to name the divergence, got: {}",
        error.message()
    );
}

#[test]
fn mutant_an_empty_contract_is_refused_vacuously_not_parsed() {
    let error = parse("").expect_err("an empty contract must refuse");
    assert!(
        error.message().contains("final newline") || error.message().contains("short"),
        "expected the vacuity law, got: {}",
        error.message()
    );
}
