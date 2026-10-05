//! The TCB inventory, re-measured on every run (bead `franken_lean-z8j.1.17`; plan §8.1:
//! the dependency closure is "generated from the actual graph into the TCB inventory every CI
//! run").
//!
//! Cargo builds the `tcb-probe` binary from this tree before this test runs. The probe
//! references nothing but `fln_kernel::check`, so the `fln_*` functions the linker kept in it
//! are the ones reachable from the kernel's one authority. This test reads them back, compares
//! them with the checked-in disclosure `crates/fln-conformance/evidence/tcb_inventory.txt` in
//! both directions, and holds the code outside `fln-kernel` to the budget that file declares.
//! A function that enters or leaves the trust base therefore cannot land without its author
//! regenerating the disclosure, and the diff names it. The comparison covers the item sets and
//! the counts they determine, not symbol counts, which differ between build configurations of
//! the same tree (they are printed instead).
//!
//! What the measurement does and does not establish is stated on
//! `fln_conformance::tcb_inventory`.
//!
//! Environment:
//! * `FLN_TCB_INVENTORY_WRITE=1` rewrites the disclosure from this measurement, keeping its
//!   `budget` line (`FLN_TCB_INVENTORY_BUDGET=<n>` supplies one when the file has none).
//! * `FLN_TCB_INVENTORY_DUMP=<path>` writes one tab-separated row per function symbol:
//!   mangled name, demangled name, item, defining crate.
#![forbid(unsafe_code)]

use fln_conformance::tcb_inventory::{self, Inventory};
use std::collections::BTreeSet;

const DISCLOSURE: &str = "crates/fln-conformance/evidence/tcb_inventory.txt";

fn probe_symbols() -> Vec<String> {
    let probe = env!("CARGO_BIN_EXE_tcb-probe");
    let bytes = std::fs::read(probe)
        .unwrap_or_else(|error| panic!("cannot read the tcb-probe binary {probe}: {error}"));
    tcb_inventory::elf_function_symbols(&bytes)
        .unwrap_or_else(|error| panic!("cannot read function symbols from {probe}: {error}"))
}

fn dump(symbols: &[String], path: &str) {
    let mut rows = String::new();
    for symbol in symbols {
        let row = match tcb_inventory::demangle_v0(symbol) {
            Ok(d) => format!("{symbol}\t{}\t{}\t{}\n", d.full, d.item, d.crate_name),
            Err(error) => format!("{symbol}\t-\t-\t{error}\n"),
        };
        rows.push_str(&row);
    }
    std::fs::write(path, rows).unwrap_or_else(|error| panic!("cannot write {path}: {error}"));
}

/// Item lines of a disclosure, for a readable diff.
fn item_lines(text: &str) -> BTreeSet<&str> {
    text.lines()
        .filter(|line| line.starts_with("item "))
        .collect()
}

#[test]
fn the_tcb_inventory_matches_what_check_links() {
    // The measurement is defined at the dev profile: with optimization on, inlined functions
    // leave the symbol table and the count would describe the optimizer, not the call graph.
    if !cfg!(debug_assertions) {
        panic!(
            "the TCB inventory is measured at the dev profile (opt-level 0, no inlining); this \
             test binary was built without debug assertions, so the probe was likely optimized"
        );
    }
    let root = fln_conformance::checked_workspace_root!();
    let symbols = probe_symbols();
    if let Some(path) = std::env::var_os("FLN_TCB_INVENTORY_DUMP") {
        dump(&symbols, &path.to_string_lossy());
    }
    let measured: Inventory = tcb_inventory::inventory(&symbols)
        .unwrap_or_else(|error| panic!("the probe's symbols do not all demangle: {error}"));

    // Anti-vacuity: a broken reader or classifier that loses the workspace's functions must
    // fail here rather than report a small, clean inventory.
    let has = |crate_name: &str, prefix: &str| {
        measured
            .items
            .get(crate_name)
            .is_some_and(|items| items.iter().any(|item| item.starts_with(prefix)))
    };
    assert!(
        has("fln_kernel", "fln_kernel::check"),
        "the root itself was not found"
    );
    for (crate_name, prefix) in [
        ("fln_core", "<fln_core::level::Level>::"),
        ("fln_core", "<fln_core::expr::Expr>::"),
        ("fln_env", "<fln_env::pmap::"),
    ] {
        assert!(
            has(crate_name, prefix),
            "no {crate_name} item under {prefix}: the kernel calls into it, so a measurement \
             without it is a broken scan"
        );
    }
    assert!(
        measured.other_symbols > 0,
        "no toolchain symbols: a broken scan"
    );

    let path = root.join(DISCLOSURE);
    let existing = std::fs::read_to_string(&path).unwrap_or_default();
    let budget = tcb_inventory::declared_budget(&existing)
        .or_else(|| {
            std::env::var("FLN_TCB_INVENTORY_BUDGET")
                .ok()
                .and_then(|value| value.parse().ok())
        })
        .unwrap_or_else(|| {
            panic!(
                "{DISCLOSURE} declares no `budget adjacent-items<=N` line; set \
                 FLN_TCB_INVENTORY_BUDGET with FLN_TCB_INVENTORY_WRITE=1 to declare one"
            )
        });
    let rendered = tcb_inventory::render(&measured, budget);
    if std::env::var_os("FLN_TCB_INVENTORY_WRITE").is_some() {
        std::fs::write(&path, &rendered)
            .unwrap_or_else(|error| panic!("cannot write {}: {error}", path.display()));
    }
    let disclosed = std::fs::read_to_string(&path).unwrap_or_default();

    println!(
        "tcb-inventory: root fln_kernel::check; {} items ({} outside fln_kernel, budget {budget}); {}",
        measured.item_count(),
        measured.adjacent_item_count(),
        measured
            .items
            .iter()
            .map(|(crate_name, items)| format!("{crate_name}={}", items.len()))
            .collect::<Vec<_>>()
            .join(" "),
    );
    // Logged, never compared: these depend on the build's codegen partitioning.
    println!(
        "tcb-inventory: linked symbols in this build: {}",
        measured.symbol_summary()
    );
    if disclosed != rendered {
        let now = item_lines(&rendered);
        let then = item_lines(&disclosed);
        let entered: Vec<&str> = now.difference(&then).copied().collect();
        let left: Vec<&str> = then.difference(&now).copied().collect();
        panic!(
            "{DISCLOSURE} no longer describes what fln_kernel::check links.\n\
             entered the trust base ({}):\n  {}\nleft it ({}):\n  {}\n\
             If the change is intended, regenerate with\n  \
             FLN_TCB_INVENTORY_WRITE=1 cargo test -p fln-conformance --test tcb_inventory\n\
             and say so in the commit: the disclosure is how a reviewer sees the trust base move.",
            entered.len(),
            entered.join("\n  "),
            left.len(),
            left.join("\n  "),
        );
    }
    assert!(
        measured.adjacent_item_count() <= budget,
        "{} functions outside fln_kernel are reachable from check, over the declared budget of \
         {budget} in {DISCLOSURE}",
        measured.adjacent_item_count()
    );
}
