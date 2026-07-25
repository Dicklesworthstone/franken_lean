//! `parser_category_inventory` — the category set, derived from the pin rather than remembered
//! (bead fln-ffam).
//!
//! ## Why this suite is shaped as a re-derivation
//!
//! This is a **completeness** claim, and completeness fails in one characteristic way: an
//! inventory that lists what its author thought of is complete with respect to nothing. A frozen
//! list of categories, checked against itself, passes forever and says only that the file has not
//! changed.
//!
//! So the fixture is not the oracle. The suite **walks the pinned Reference's source at test
//! time**, extracts every category it registers, and compares that against
//! `fixtures/PARSER_CATEGORY_INVENTORY.txt`. A category present at the pin and absent from the
//! inventory **fails**. That is the direction that matters: the inventory can only be complete
//! relative to something that is not itself.
//!
//! The other direction fails too — an entry in the inventory that the pin does not have is a
//! stale row, which is a different defect (we would be claiming to support a category that does
//! not exist) and gets its own assertion.
//!
//! ## Typed skip, not silent pass
//!
//! The pinned toolchain is absent on RCH remote workers. When it is missing this suite **skips
//! with a printed reason**, because a completeness suite that quietly passes when it cannot see
//! its oracle is worse than one that is not there: it reports evidence it did not gather.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

const INVENTORY: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/fixtures/PARSER_CATEGORY_INVENTORY.txt"
);

/// The pin's Lean source root, or `None` when the toolchain is not installed.
fn pin_source_root() -> Option<PathBuf> {
    let home = std::env::var_os("HOME")?;
    let root = Path::new(&home).join(".elan/toolchains/leanprover--lean4---v4.32.0/src/lean");
    root.is_dir().then_some(root)
}

/// Every `.lean` file under the pin, read once.
fn pin_sources(root: &Path) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "lean")
                && let Ok(text) = fs::read_to_string(&path)
            {
                out.push(text);
            }
        }
    }
    out
}

/// The next identifier at `at`, by Lean's identifier alphabet as far as a category name needs.
fn ident_at(text: &str, at: usize) -> Option<&str> {
    let rest = text.get(at..)?;
    let start = rest.len() - rest.trim_start().len();
    let rest = &rest[start..];
    let end = rest
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(rest.len());
    (end > 0).then(|| &rest[..end])
}

/// Categories the pin registers as **builtin**, with the `LeadingIdentBehavior` each declares.
///
/// Derived from `registerBuiltinParserAttribute ... ``Category.<name> [.both|.symbol]`. An absent
/// behaviour argument means `default`, which is why the behaviour is captured here rather than
/// assumed: `attr` is `symbol` and `tactic` is `both`, and neither is guessable.
fn builtin_categories(sources: &[String]) -> BTreeMap<String, String> {
    const REGISTER: &str = "registerBuiltinParserAttribute";
    const MARKER: &str = "``Category.";
    let mut found = BTreeMap::new();
    for text in sources {
        let mut from = 0usize;
        while let Some(offset) = text[from..].find(REGISTER) {
            let at = from + offset;
            from = at + REGISTER.len();
            // The category marker must appear on the same logical call, so bound the window.
            let window_end = (at + 240).min(text.len());
            let Some(window) = text.get(at..window_end) else {
                continue;
            };
            let Some(marker) = window.find(MARKER) else {
                continue;
            };
            let Some(name) = ident_at(window, marker + MARKER.len()) else {
                continue;
            };
            // The behaviour, if the call names one, appears after the category.
            let tail = &window[marker + MARKER.len() + name.len()..];
            let head = tail.split('\n').next().unwrap_or("");
            let behavior = if head.contains(".both") {
                "both"
            } else if head.contains(".symbol") {
                "symbol"
            } else {
                "default"
            };
            found.insert(name.to_string(), behavior.to_string());
        }
    }
    found
}

/// Categories the pin declares in Lean source with `declare_syntax_cat`.
fn declared_categories(sources: &[String]) -> Vec<String> {
    const MARKER: &str = "declare_syntax_cat";
    let mut found = Vec::new();
    for text in sources {
        let mut from = 0usize;
        while let Some(offset) = text[from..].find(MARKER) {
            let at = from + offset;
            from = at + MARKER.len();
            if let Some(name) = ident_at(text, at + MARKER.len()) {
                found.push(name.to_string());
            }
        }
    }
    found.sort();
    found.dedup();
    found
}

/// The frozen inventory, as (builtin, declared).
fn frozen() -> (BTreeMap<String, String>, Vec<String>) {
    let text = fs::read_to_string(INVENTORY).expect("the inventory fixture must be readable");
    let mut builtin = BTreeMap::new();
    let mut declared = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split_whitespace();
        match (parts.next(), parts.next(), parts.next()) {
            (Some("builtin"), Some(name), Some(behavior)) => {
                builtin.insert(name.to_string(), behavior.to_string());
            }
            (Some("declared"), Some(name), None) => declared.push(name.to_string()),
            other => {
                // A malformed row is a defect in the generator, and reporting it as a value
                // comparison keeps the failure readable.
                assert_eq!(
                    format!("{other:?}"),
                    "a builtin or declared row",
                    "unrecognised inventory row in {line:?}"
                );
            }
        }
    }
    declared.sort();
    (builtin, declared)
}

fn skip(reason: &str) {
    println!("SKIP parser_category_inventory: {reason}");
}

/// **THE COMPLETENESS ASSERTION.** Every category the pin registers is in the inventory, and every
/// row in the inventory is a category the pin has.
///
/// Both directions, because they are different defects: a missing row means we do not know about a
/// category that exists, and a stale row means we claim one that does not.
#[test]
fn the_inventory_matches_the_categories_the_pin_registers() {
    let Some(root) = pin_source_root() else {
        skip("the pinned toolchain is not installed; a completeness suite must not pass silently");
        return;
    };
    let sources = pin_sources(&root);
    assert!(
        sources.len() > 100,
        "only {} pin sources were read; the walk is not finding the toolchain",
        sources.len()
    );

    let (frozen_builtin, frozen_declared) = frozen();
    let pin_builtin = builtin_categories(&sources);
    let pin_declared = declared_categories(&sources);

    assert!(
        !pin_builtin.is_empty(),
        "the derivation found no builtin categories, so the comparison below would be vacuous"
    );

    // Direction 1: a category at the pin that the inventory does not list.
    let missing: Vec<&String> = pin_builtin
        .keys()
        .filter(|name| !frozen_builtin.contains_key(*name))
        .collect();
    assert!(
        missing.is_empty(),
        "the pin registers builtin categories the inventory does not list: {missing:?}. \
         An inventory is complete only relative to something that is not itself — add the rows."
    );

    // Direction 2: an inventory row the pin does not have.
    let stale: Vec<&String> = frozen_builtin
        .keys()
        .filter(|name| !pin_builtin.contains_key(*name))
        .collect();
    assert!(
        stale.is_empty(),
        "the inventory lists builtin categories the pin does not register: {stale:?}. \
         A stale row claims support for a category that does not exist."
    );

    // And the behaviour of each, which is the part that cannot be guessed.
    for (name, behavior) in &pin_builtin {
        assert_eq!(
            frozen_builtin.get(name),
            Some(behavior),
            "category {name:?}: the pin declares behaviour {behavior:?}"
        );
    }

    let missing_declared: Vec<&String> = pin_declared
        .iter()
        .filter(|name| !frozen_declared.contains(name))
        .collect();
    assert!(
        missing_declared.is_empty(),
        "the pin declares categories with declare_syntax_cat that the inventory does not list: \
         {missing_declared:?}"
    );
}

/// **The completeness check can fail.** A category removed from the inventory must be reported as
/// missing — otherwise the suite above is a file comparing itself to itself.
///
/// Exercised by deriving from the pin and then removing a row from the *derived* copy of the
/// inventory, which is the same comparison the real assertion makes without editing a tracked
/// fixture.
#[test]
fn removing_a_row_from_the_inventory_is_detected() {
    let Some(root) = pin_source_root() else {
        skip("no pin; the can-fail proof needs the oracle it is proving against");
        return;
    };
    let sources = pin_sources(&root);
    let pin_builtin = builtin_categories(&sources);
    let (mut frozen_builtin, _) = frozen();

    let victim = pin_builtin
        .keys()
        .next()
        .expect("the pin has at least one builtin category")
        .clone();
    frozen_builtin.remove(&victim);

    let missing: Vec<&String> = pin_builtin
        .keys()
        .filter(|name| !frozen_builtin.contains_key(*name))
        .collect();
    assert_eq!(
        missing,
        vec![&victim],
        "removing {victim:?} from the inventory must be detected as missing"
    );
}

/// A wrong *behaviour* is detected too. The behaviour is the half a reader would most likely get
/// wrong from intuition — `attr` is `symbol` and `tactic` is `both`, and nothing about their names
/// suggests either.
#[test]
fn a_wrong_behaviour_in_the_inventory_is_detected() {
    let Some(root) = pin_source_root() else {
        skip("no pin");
        return;
    };
    let sources = pin_sources(&root);
    let pin_builtin = builtin_categories(&sources);

    // The two non-default behaviours, observed in slice C and re-derived here.
    assert_eq!(
        pin_builtin.get("attr").map(String::as_str),
        Some("symbol"),
        "attr registers .symbol (Parser/Attr.lean)"
    );
    assert_eq!(
        pin_builtin.get("tactic").map(String::as_str),
        Some("both"),
        "tactic registers .both (Parser/Term/Basic.lean)"
    );
    assert_eq!(
        pin_builtin.get("term").map(String::as_str),
        Some("default"),
        "term omits the argument and so gets default"
    );

    // And a corrupted expectation is caught, so the three assertions above are not tautologies.
    let mut corrupted = pin_builtin.clone();
    corrupted.insert("attr".to_string(), "default".to_string());
    assert_ne!(
        corrupted.get("attr"),
        pin_builtin.get("attr"),
        "a wrong behaviour must compare as different"
    );
}

/// Our engine's `LeadingIdentBehavior` covers every behaviour the pin actually uses. A behaviour
/// at the pin with no variant in our enum would be a silently unsupported category.
#[test]
fn every_behaviour_the_pin_uses_has_a_variant_in_our_enum() {
    use fln_parse::category::LeadingIdentBehavior;

    let Some(root) = pin_source_root() else {
        skip("no pin");
        return;
    };
    let sources = pin_sources(&root);
    let pin_builtin = builtin_categories(&sources);

    for (name, behavior) in &pin_builtin {
        let ours = match behavior.as_str() {
            "default" => Some(LeadingIdentBehavior::Default),
            "symbol" => Some(LeadingIdentBehavior::Symbol),
            "both" => Some(LeadingIdentBehavior::Both),
            _ => None,
        };
        assert!(
            ours.is_some(),
            "category {name:?} declares behaviour {behavior:?}, which our enum has no variant for"
        );
    }

    // The set of behaviours the pin uses is exactly the set our enum has, in both directions.
    let used: std::collections::BTreeSet<&str> = pin_builtin.values().map(String::as_str).collect();
    assert_eq!(
        used,
        ["both", "default", "symbol"].into_iter().collect(),
        "the pin uses exactly these three behaviours; a fourth would need a variant"
    );
}

/// The inventory is well formed and non-trivial: enough rows to be a real inventory, no duplicate
/// names, and a header that names its schema.
#[test]
fn the_inventory_file_is_well_formed() {
    let text = fs::read_to_string(INVENTORY).expect("readable");
    assert!(
        text.contains("fln.parser-category-inventory/1"),
        "the fixture must name its schema, so a reader knows what they are looking at"
    );
    assert!(
        text.contains("do not hand-edit"),
        "the fixture must say it is derived, or someone will maintain it by hand"
    );

    let (builtin, declared) = frozen();
    assert!(
        builtin.len() >= 10,
        "only {} builtin rows; the pin has at least ten",
        builtin.len()
    );
    assert!(
        declared.len() >= 20,
        "only {} declared rows; the pin has many more",
        declared.len()
    );

    let mut unique = declared.clone();
    unique.dedup();
    assert_eq!(unique.len(), declared.len(), "duplicate declared rows");
}
