//! The durable-format registry join (bead franken_lean-rps, requirement b; plan §7.3
//! and Appendix B: **every durable format specified once**).
//!
//! `fln_hash::canon::SCHEMA_REGISTRY` is the program's inventory of durable formats.
//! Its in-crate laws — unique, well-shaped names, and fln-hash's own rows joined
//! against the real constants — live beside it in `canon.rs`. What it cannot do from
//! there is check the *other* owners: the crate map (§21) points dependency edges
//! strictly downward, and fln-hash sits below fln-env and fln-verdict, so it can never
//! import their constants to compare them.
//!
//! So this test reads their sources instead, and joins **in both directions**:
//!
//! * a `SchemaId` constant that no row registers is an unregistered durable format —
//!   the exact drift the requirement exists to stop (a format ships, nothing publishes
//!   its identity, and the conformance corpus has nothing to be a projection of);
//! * a row whose constant has vanished or moved is a stale row, which is how a registry
//!   quietly becomes fiction.
//!
//! Textual scanning is the honest tool here, not a shortcut: reading a lower crate's
//! source is the only direction the layering allows, and it is what an auditor does.
//! The scanner is held to the same standard as the registry — the planted cases below
//! drive the exact function the join uses, because a mutation harness that exercises a
//! subset of the production contract can report a false green (the lesson from this
//! bead's earlier fixture-plant round).

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

use fln_hash::canon::{SCHEMA_REGISTRY, SchemaOwner};

/// One `const <IDENT>: SchemaId = SchemaId { name: …, version: … };` declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DeclaredSchema {
    /// The Rust constant's name, for diagnosis.
    constant: String,
    name: String,
    /// The `version` field verbatim — a literal or a named constant.
    version: String,
}

/// Walk from just past an opening `{` to its match, returning the body's length.
fn matching_brace(rest: &str) -> Option<usize> {
    let mut depth = 1usize;
    for (idx, ch) in rest.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

/// The verbatim text of one field in a struct-literal body.
fn field(body: &str, key: &str) -> Option<String> {
    let at = body.find(&format!("{key}:"))?;
    let rest = &body[at + key.len() + 1..];
    let end = rest.find(',').unwrap_or(rest.len());
    Some(rest[..end].trim().to_string())
}

/// Every durable format *declared* in one source file.
///
/// A declaration is a named constant — `const X: SchemaId = SchemaId { … }` — and
/// deliberately not any `SchemaId { … }` literal. That distinction is load-bearing:
/// `SCHEMA_REGISTRY` itself contains inline `SchemaId` literals for the formats other
/// crates own, and those are *references* to identities declared elsewhere. Counting
/// them as declarations would make fln-hash appear to declare fln-verdict's formats.
fn declared_schemas(source: &str) -> Vec<DeclaredSchema> {
    const NEEDLE: &str = ": SchemaId = SchemaId {";
    let mut declarations = Vec::new();
    let mut cursor = 0usize;
    while let Some(offset) = source[cursor..].find(NEEDLE) {
        let start = cursor + offset;
        let body_start = start + NEEDLE.len();
        cursor = body_start;
        // The constant's identifier sits between the preceding `const` and the `:`.
        let constant = source[..start]
            .rsplit_once("const ")
            .map(|(_, ident)| ident.trim().to_string())
            .unwrap_or_default();
        let Some(len) = matching_brace(&source[body_start..]) else {
            continue;
        };
        let body = &source[body_start..body_start + len];
        let (Some(quoted), Some(version)) = (field(body, "name"), field(body, "version")) else {
            continue;
        };
        let Some(name) = quoted
            .strip_prefix('"')
            .and_then(|rest| rest.strip_suffix('"'))
        else {
            continue;
        };
        declarations.push(DeclaredSchema {
            constant,
            name: name.to_string(),
            version,
        });
    }
    declarations
}

/// Resolve a `version` field to a number: either a literal, or a `const IDENT: u16 = N;`
/// in the same file (fln-verdict versions its three formats together through
/// `VERDICT_SCHEMA_VERSION`, so a scanner that only read literals would see nothing).
fn resolve_version(source: &str, text: &str) -> Option<u16> {
    if let Ok(literal) = text.parse::<u16>() {
        return Some(literal);
    }
    let declaration = format!("const {text}: u16 = ");
    let at = source.find(&declaration)?;
    let rest = &source[at + declaration.len()..];
    let end = rest.find(';')?;
    rest[..end].trim().parse().ok()
}

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

/// The (name, version) pairs one owner's declaration file actually declares.
fn declared_in(source: &str) -> Vec<(String, u16)> {
    let mut pairs: Vec<(String, u16)> = declared_schemas(source)
        .into_iter()
        .map(|declared| {
            let version = resolve_version(source, &declared.version).unwrap_or_else(|| {
                panic!(
                    "cannot resolve the version of `{}` (`{}`) to a number; the registry \
                     join needs a literal or a `const … : u16 = N;` in the same file",
                    declared.constant, declared.version
                )
            });
            (declared.name, version)
        })
        .collect();
    pairs.sort();
    pairs
}

fn registered_for(owner: SchemaOwner) -> Vec<(String, u16)> {
    let mut rows: Vec<(String, u16)> = SCHEMA_REGISTRY
        .iter()
        .filter(|row| row.owner == owner)
        .map(|row| (row.id.name.to_string(), row.id.version))
        .collect();
    rows.sort();
    rows
}

#[test]
fn the_registry_and_every_declaration_file_agree_in_both_directions() {
    let workspace = workspace_root();
    for owner in SchemaOwner::ALL {
        let path: PathBuf = workspace.join(owner.declaration_file());
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));

        let declared = declared_in(&source);
        let registered = registered_for(owner);

        let unregistered: Vec<&(String, u16)> = declared
            .iter()
            .filter(|pair| !registered.contains(pair))
            .collect();
        assert!(
            unregistered.is_empty(),
            "{} declares durable formats that SCHEMA_REGISTRY does not carry: {unregistered:?}\n\
             \n\
             A durable format needs a registry row — that is requirement (b) of bead \
             franken_lean-rps and Appendix B's \"specified once\". Add a SchemaRow to \
             SCHEMA_REGISTRY in crates/fln-hash/src/canon.rs with the owner, the exact \
             name and version, and one line saying what it serializes. If the version \
             moved, move it in the row too: a version bump that lands on one side only \
             is a decoder that accepts bytes it no longer understands.",
            owner.crate_name()
        );

        let stale: Vec<&(String, u16)> = registered
            .iter()
            .filter(|pair| !declared.contains(pair))
            .collect();
        assert!(
            stale.is_empty(),
            "SCHEMA_REGISTRY carries rows for {} that {} no longer declares: {stale:?}\n\
             \n\
             Either the constant was renamed, removed, or version-bumped, or the format \
             moved to another file — in which case update SchemaOwner::declaration_file. \
             A row whose codec has vanished is how a registry becomes fiction.",
            owner.crate_name(),
            owner.declaration_file()
        );

        // Redundant given the two directions above, but it is the statement that fails
        // most legibly when both sets move at once.
        assert_eq!(declared, registered, "{} join", owner.crate_name());
    }
}

#[test]
fn the_scanner_finds_real_declarations_and_ignores_references() {
    // The three shapes that occur in the tree, including fln-verdict's shared version
    // constant and a doc comment between the declarations.
    let source = "\
pub const VERDICT_SCHEMA_VERSION: u16 = 7;

/// A doc comment mentioning SchemaId in prose.
pub const CNF_SCHEMA: SchemaId = SchemaId {
    name: \"fln.verdict.cnf\",
    version: VERDICT_SCHEMA_VERSION,
};
pub const SCHEMA_EXPR: SchemaId = SchemaId {
    name: \"fln.canon.expr\",
    version: 1,
};
";
    let declared = declared_schemas(source);
    assert_eq!(declared.len(), 2, "{declared:?}");
    assert_eq!(declared[0].constant, "CNF_SCHEMA");
    assert_eq!(declared[0].name, "fln.verdict.cnf");
    assert_eq!(
        resolve_version(source, &declared[0].version),
        Some(7),
        "a named version constant must resolve, or fln-verdict's three formats vanish \
         from the join"
    );
    assert_eq!(declared[1].constant, "SCHEMA_EXPR");
    assert_eq!(resolve_version(source, &declared[1].version), Some(1));

    // The type definition is not a declaration.
    assert!(declared_schemas("pub struct SchemaId {\n    name: &'static str,\n}\n").is_empty());

    // An inline literal is a REFERENCE, not a declaration. This is exactly the shape
    // SCHEMA_REGISTRY uses for the formats other crates own; counting it would make
    // fln-hash look like the declarer of every format in the program.
    let reference = "\
pub const SCHEMA_REGISTRY: [SchemaRow; 1] = [SchemaRow {
    id: SchemaId {
        name: \"fln.env.module-provenance\",
        version: 1,
    },
    owner: SchemaOwner::Env,
    covers: \"the manifest\",
}];
";
    assert!(
        declared_schemas(reference).is_empty(),
        "an inline SchemaId inside the registry table is a reference to a format \
         declared elsewhere, not a declaration"
    );
}

#[test]
fn the_join_catches_an_unregistered_format_a_stale_row_and_a_version_drift() {
    // Plants run against the REAL declaration file through the REAL scanner, so they
    // cannot pass by exercising a weaker path than the join does. The checked-in
    // sources are never mutated; the plants edit in-memory copies.
    let workspace = workspace_root();
    let path = workspace.join(SchemaOwner::Hash.declaration_file());
    let source = fs::read_to_string(&path).expect("fln-hash canon.rs is readable");
    let baseline = declared_in(&source);
    let registered = registered_for(SchemaOwner::Hash);
    assert_eq!(baseline, registered, "control: the live join is clean");

    // 1. An unregistered format: a new constant nobody added a row for.
    let planted = format!(
        "{source}\npub const SCHEMA_SNEAK: SchemaId = SchemaId {{\n    name: \"fln.canon.sneak\",\n    version: 1,\n}};\n"
    );
    let with_sneak = declared_in(&planted);
    assert!(
        with_sneak.contains(&("fln.canon.sneak".to_string(), 1)),
        "the scanner missed a planted declaration, so the unregistered-format direction \
         of the join proves nothing"
    );
    assert!(
        with_sneak.iter().any(|pair| !registered.contains(pair)),
        "a planted unregistered format must show up as unregistered"
    );

    // 2. A stale row: the constant for a registered format is gone.
    let removed = source.replacen("fln.canon.expr", "fln.canon.expr-renamed", 1);
    let after_rename = declared_in(&removed);
    assert!(
        registered.iter().any(|pair| !after_rename.contains(pair)),
        "renaming a declared schema must surface as a stale registry row"
    );

    // 3. A version drift on one side only — the case that would leave a decoder
    // accepting bytes it no longer understands.
    let drifted = source.replacen(
        "name: \"fln.canon.expr\",\n    version: 1,",
        "name: \"fln.canon.expr\",\n    version: 2,",
        1,
    );
    let after_drift = declared_in(&drifted);
    assert!(
        after_drift.contains(&("fln.canon.expr".to_string(), 2)),
        "the version-drift plant did not apply — check the constant's formatting"
    );
    assert!(
        !registered.contains(&("fln.canon.expr".to_string(), 2)),
        "a bumped version must not match the registry's row"
    );
}
