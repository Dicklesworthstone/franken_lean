//! The independent checker's `.olean` input path does not reach the primary's decoder
//! (bead `franken_lean-z8j.1.14`), measured per run by the linker.
//!
//! `fln_kernel::check` and `fln-checker` once judged the same declarations because both
//! were fed `fln-olean`'s decode: the checker received `fln-core` terms re-encoded into its
//! wire format, so a decoder defect reached both seats identically. The checker now reads
//! the artifact's bytes itself (`fln_checker::olean`) and the council compares the two
//! readings. That comparison is only worth something while the checker's reading is built
//! by code that cannot call the primary's decoder or construct its terms.
//!
//! "Cannot call" is a call-graph property, so it is measured from a call graph rather than
//! from source text: `checker-reader-probe` references nothing but
//! `fln::independent_reading`, and the linker keeps exactly the functions reachable from it
//! (the method `tests/tcb_inventory.rs` uses for `fln_kernel::check`). Every `fln_*` function
//! it kept must belong to the checker's own crate, to `fln_hash`'s hashing, or to the one
//! `fln` function that hands the bytes over.
#![forbid(unsafe_code)]

use fln_conformance::tcb_inventory;

/// Workspace crates whose functions the probe may contain, and why.
///
/// `fln_libm` is the one entry that is not on the reading path. `fln-unsafe-abi` exports the
/// C math symbols (`libm_symbols.rs`, `export_name = "fabs"` and so on) and the linker keeps
/// every exported symbol, with its callees, in any binary that links `fln`. A function kept
/// that way can only add a refusal here, never hide one, so permitting it is safe; it is
/// IEEE arithmetic and constructs no term.
const PERMITTED: [(&str, &str); 4] = [
    (
        "fln",
        "only `independent_reading` itself, which hands the bytes over",
    ),
    (
        "fln_checker",
        "the checker's own reader, terms and reading digest",
    ),
    (
        "fln_hash",
        "the domain-separated hash the reading digest is computed with",
    ),
    (
        "fln_libm",
        "kept by fln-unsafe-abi's exported C math symbols, not reached from the root",
    ),
];

/// The `fln_hash` modules that may be reached: hashing, never `canon`'s readers, which
/// construct `fln-core` terms.
const PERMITTED_HASH_MODULES: [&str; 2] = ["fln_hash::domain", "fln_hash::blake3"];

#[test]
fn the_checker_reading_path_reaches_nothing_of_the_primary_decoder() {
    if !cfg!(debug_assertions) {
        panic!(
            "the reachability measurement is defined at the dev profile (no inlining); this \
             test binary was built without debug assertions, so the probe was likely optimized"
        );
    }
    let probe = env!("CARGO_BIN_EXE_checker-reader-probe");
    let bytes = std::fs::read(probe)
        .unwrap_or_else(|error| panic!("cannot read the checker-reader-probe {probe}: {error}"));
    let symbols = tcb_inventory::elf_function_symbols(&bytes)
        .unwrap_or_else(|error| panic!("cannot read function symbols from {probe}: {error}"));
    let measured = tcb_inventory::inventory(&symbols)
        .unwrap_or_else(|error| panic!("the probe's symbols do not all demangle: {error}"));

    println!(
        "checker-reader-closure: root fln::independent_reading; {} items; {}",
        measured.item_count(),
        measured
            .items
            .iter()
            .map(|(crate_name, items)| format!("{crate_name}={}", items.len()))
            .collect::<Vec<_>>()
            .join(" "),
    );

    // Anti-vacuity: the root, the reader, the term builder and the digest must all be
    // present, or a broken scan would report an empty, clean closure.
    let has = |crate_name: &str, needle: &str| {
        measured
            .items
            .get(crate_name)
            .is_some_and(|items| items.iter().any(|item| item.contains(needle)))
    };
    for (crate_name, needle) in [
        ("fln", "fln::independent_reading"),
        ("fln_checker", "fln_checker::olean::read_constants"),
        ("fln_checker", "<fln_checker::olean::OleanReader>::expr"),
        ("fln_checker", "<fln_checker::olean::OleanReader>::constant"),
        ("fln_checker", "fln_checker::reading::expr_digest"),
        (
            "fln_checker",
            "<fln_checker::environment::ConstantEntry>::reading_digest",
        ),
        ("fln_hash", "fln_hash::domain"),
    ] {
        assert!(
            has(crate_name, needle),
            "no {crate_name} item matching `{needle}` is reachable: the probe no longer roots \
             at the reading path, or the symbol reader lost it — a broken scan, not a clean \
             one. {crate_name} items reached: {:?}",
            measured.items.get(crate_name)
        );
    }
    assert!(
        measured.other_symbols > 0,
        "no toolchain symbols: a broken scan"
    );

    let mut refused = Vec::new();
    for (crate_name, items) in &measured.items {
        let Some(_) = PERMITTED.iter().find(|(name, _)| name == crate_name) else {
            for item in items {
                refused.push(format!("{crate_name}: {item}"));
            }
            continue;
        };
        for item in items {
            let permitted = match crate_name.as_str() {
                "fln" => item.starts_with("fln::independent_reading"),
                "fln_hash" => PERMITTED_HASH_MODULES
                    .iter()
                    .any(|module| item.contains(&format!("{module}::"))),
                _ => true,
            };
            if !permitted {
                refused.push(format!("{crate_name}: {item}"));
            }
        }
    }

    assert!(
        refused.is_empty(),
        "the independent checker's .olean input path reaches {} function(s) outside its own \
         decoder; a reading built through any of them can share a defect with the primary \
         decode, which is what the council comparison exists to catch:\n  {}\npermitted: {}",
        refused.len(),
        refused.join("\n  "),
        PERMITTED
            .iter()
            .map(|(name, why)| format!("{name} ({why})"))
            .collect::<Vec<_>>()
            .join("; "),
    );
}
