//! The stdlib frontier coverage ratchet (bead `franken_lean-z8j.1.16`, criterion 3): a
//! fresh frontier that loses coverage against the retained receipt fails, and an addition
//! is reported as an improvement.
//!
//! No frontier is run here. The control is the retained receipt itself; every plant is a
//! synthetic variant of it rendered back into a self-consistent document, so each one is
//! caught by the comparison and not merely by the reader refusing a broken file.
#![forbid(unsafe_code)]

use std::io::Write;
use std::process::{Command, Stdio};

use fln_conformance::stdlib_frontier::{
    FrontierError, FrontierRow, RETAINED_RECEIPT, compare, parse,
};

fn receipt_text() -> String {
    let root = fln_conformance::checked_workspace_root!();
    std::fs::read_to_string(root.join(RETAINED_RECEIPT)).unwrap_or_else(|error| {
        panic!("the retained receipt {RETAINED_RECEIPT} must be readable: {error}")
    })
}

fn receipt() -> fln_conformance::stdlib_frontier::Frontier {
    parse(&receipt_text()).expect("the retained receipt is a self-consistent frontier")
}

/// A module the receipt accepts, chosen by name so the plant is reproducible.
const PLANT: &str = "Init.Data.List.Basic";

fn planted_row(frontier: &mut fln_conformance::stdlib_frontier::Frontier) -> &mut FrontierRow {
    frontier
        .rows
        .iter_mut()
        .find(|row| row.module == PLANT)
        .unwrap_or_else(|| panic!("{PLANT} must be in the receipt for the plants to mean anything"))
}

#[test]
fn the_retained_receipt_reads_back_and_compares_clean_with_itself() {
    let receipt = receipt();
    // Anti-vacuity: the numbers the receipt states, recomputed from its rows by the reader.
    assert_eq!(receipt.rows.len(), 2433);
    assert_eq!(
        receipt
            .rows
            .iter()
            .filter(|row| row.verdict == "accepted")
            .count(),
        2433
    );
    assert_eq!(receipt.accepted_declarations, 215_136);
    assert!(receipt.authority);
    assert_eq!(receipt.outcome, "complete");

    let comparison = compare(&receipt, &receipt);
    assert!(!comparison.dropped(), "{}", comparison.render());
    assert!(!comparison.improved(), "{}", comparison.render());
    assert!(comparison.render().ends_with("verdict: no coverage drop\n"));

    // The renderer round-trips: what a plant is built with reads back to the same rows.
    let again = parse(&receipt.to_json()).expect("a rendered frontier reads back");
    assert_eq!(again.rows, receipt.rows);
}

#[test]
fn a_module_no_longer_accepted_is_a_drop() {
    let receipt = receipt();
    let mut current = receipt.clone();
    let row = planted_row(&mut current);
    row.verdict = "inconclusive".to_owned();
    row.declarations = 0;
    row.detail = "planted resource stop".to_owned();
    let current = parse(&current.to_json()).expect("the plant is a self-consistent frontier");

    let comparison = compare(&receipt, &current);
    assert!(comparison.dropped(), "{}", comparison.render());
    assert_eq!(
        comparison.no_longer_accepted,
        [(
            PLANT.to_owned(),
            "inconclusive".to_owned(),
            "planted resource stop".to_owned()
        )]
    );
    assert!(comparison.lost.is_empty() && comparison.count_changed.is_empty());
    assert!(
        comparison
            .render()
            .contains(&format!("DROP no longer accepted: {PLANT}"))
    );
}

#[test]
fn a_lost_module_is_a_drop() {
    let receipt = receipt();
    let mut current = receipt.clone();
    current.rows.retain(|row| row.module != PLANT);
    let current = parse(&current.to_json()).expect("the plant is a self-consistent frontier");

    let comparison = compare(&receipt, &current);
    assert!(comparison.dropped(), "{}", comparison.render());
    assert_eq!(comparison.lost, [PLANT.to_owned()]);
    assert!(comparison.no_longer_accepted.is_empty() && comparison.count_changed.is_empty());
}

#[test]
fn a_declaration_count_change_is_a_drop_in_either_direction() {
    let receipt = receipt();
    let before = receipt
        .rows
        .iter()
        .find(|row| row.module == PLANT)
        .map(|row| row.declarations)
        .expect("the plant module is in the receipt");
    for after in [before - 1, before + 1] {
        let mut current = receipt.clone();
        planted_row(&mut current).declarations = after;
        let current = parse(&current.to_json()).expect("the plant is a self-consistent frontier");

        let comparison = compare(&receipt, &current);
        assert!(comparison.dropped(), "{}", comparison.render());
        assert_eq!(
            comparison.count_changed,
            [(PLANT.to_owned(), before, after)]
        );
        assert!(comparison.lost.is_empty() && comparison.no_longer_accepted.is_empty());
    }
}

#[test]
fn additions_and_new_acceptances_are_improvements_not_drops() {
    let full = receipt();
    // A receipt in which the plant module had not been accepted, against today's run.
    let mut older = full.clone();
    let row = planted_row(&mut older);
    row.verdict = "blocked".to_owned();
    row.declarations = 0;
    let older = parse(&older.to_json()).expect("the variant is a self-consistent frontier");
    // Today's run also has a module the receipt never saw.
    let mut current = full.clone();
    current.rows.push(FrontierRow {
        module: "Planted.NewModule".to_owned(),
        verdict: "accepted".to_owned(),
        declarations: 3,
        detail: String::new(),
    });
    let current = parse(&current.to_json()).expect("the variant is a self-consistent frontier");

    let comparison = compare(&older, &current);
    assert!(!comparison.dropped(), "{}", comparison.render());
    assert!(comparison.improved());
    assert_eq!(
        comparison.newly_accepted,
        [(PLANT.to_owned(), "blocked".to_owned())]
    );
    assert_eq!(
        comparison.added,
        [("Planted.NewModule".to_owned(), "accepted".to_owned())]
    );
    assert!(
        comparison
            .render()
            .ends_with("verdict: no coverage drop; coverage improved\n")
    );
}

#[test]
fn a_document_that_disagrees_with_itself_is_refused_not_compared() {
    let text = receipt_text();
    // The summary says one module fewer was accepted than the rows show.
    let inconsistent = text.replacen("\"accepted\":2433,", "\"accepted\":2432,", 1);
    assert_ne!(inconsistent, text, "the plant site must exist");
    assert!(matches!(
        parse(&inconsistent),
        Err(FrontierError::Inconsistent(_))
    ));

    // A truncated file, a duplicated row, an unknown verdict, the wrong schema.
    assert!(matches!(
        parse(text.get(..text.len() / 2).expect("the receipt is ASCII")),
        Err(FrontierError::Syntax { .. })
    ));
    let mut doubled = receipt();
    let first = doubled.rows[0].clone();
    doubled.rows.push(first);
    assert!(matches!(
        parse(&doubled.to_json()),
        Err(FrontierError::Inconsistent(_))
    ));
    let mut unknown = receipt();
    unknown.rows[0].verdict = "maybe".to_owned();
    assert!(matches!(
        parse(&unknown.to_json()),
        Err(FrontierError::Shape(_))
    ));
    assert!(matches!(
        parse(&text.replacen(
            "fln.check-olean-frontier/1",
            "fln.check-olean-frontier/9",
            1
        )),
        Err(FrontierError::Shape(_))
    ));
    // An empty frontier is a broken run.
    let mut empty = receipt();
    empty.rows.clear();
    assert!(matches!(
        parse(&empty.to_json()),
        Err(FrontierError::Inconsistent(_))
    ));
}

/// The installed command: exit 0 on the receipt itself, 1 naming a planted drop, 2 on a
/// document it cannot compare. The current frontier arrives on stdin, as from a pipe.
#[test]
fn the_ratchet_command_exits_by_coverage() {
    let root = fln_conformance::checked_workspace_root!();
    let run = |stdin: String| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_stdlib-frontier-ratchet"))
            .arg("--receipt")
            .arg(root.join(RETAINED_RECEIPT))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("the ratchet binary runs");
        child
            .stdin
            .take()
            .expect("stdin is piped")
            .write_all(stdin.as_bytes())
            .expect("the frontier is written to stdin");
        let output = child.wait_with_output().expect("the ratchet finishes");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };

    let (code, stdout, stderr) = run(receipt_text());
    assert_eq!(code, Some(0), "{stdout}{stderr}");
    assert!(stdout.ends_with("verdict: no coverage drop\n"), "{stdout}");

    let mut dropped = receipt();
    dropped.rows.retain(|row| row.module != PLANT);
    let (code, stdout, stderr) = run(dropped.to_json());
    assert_eq!(code, Some(1), "{stdout}{stderr}");
    assert!(
        stdout.contains(&format!("DROP lost module: {PLANT}")),
        "{stdout}"
    );
    assert!(stdout.ends_with("verdict: COVERAGE DROPPED\n"), "{stdout}");

    let (code, stdout, stderr) = run("{\"schema\":".to_owned());
    assert_eq!(code, Some(2), "{stdout}{stderr}");
    assert!(
        stdout.is_empty() && stderr.contains("current frontier"),
        "{stderr}"
    );
}
