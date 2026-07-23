//! Parser for `ci/BOUNDARY_API.txt` — the reviewed public-API allowlist of the
//! unsafe boundary crates (D3 law b, bead fln-lld slice 2).
//!
//! The no-admission export covenant's type-aware half: every bare-`pub` item
//! a boundary crate exposes must be classified here — its kind, its surface
//! type, the evidence backing its soundness, and the explicit argument for
//! why it cannot launder into kernel admission. `tools/structure-guard`
//! enforces both directions (undeclared items and stale rows fail CI) plus
//! the post-expansion subset rule, so there is no unclassified public item —
//! matching the per-symbol status taxonomy the plan requires for the C ABI
//! census (§6.5), applied to the Rust surface.

use std::fs;
use std::path::Path;

#[derive(Debug)]
pub struct ApiRow {
    pub id: String,
    /// Workspace-relative path ('/'-separated) of the file declaring the item.
    pub path: String,
    /// Item kind: `fn`, `struct`, `enum`, `const`, `static`, `type`, `mod`,
    /// `use` (re-export), or `field`.
    pub kind: String,
    /// The item's name (for `use` re-exports: the exported name).
    pub name: String,
}

#[derive(Debug, Default)]
pub struct BoundaryApi {
    pub rows: Vec<ApiRow>,
}

const KINDS: &[&str] = &[
    "fn", "struct", "enum", "union", "trait", "type", "mod", "const", "static", "use", "field",
];

fn valid_id(s: &str) -> bool {
    s.strip_prefix("FLN-BX-")
        .is_some_and(|d| !d.is_empty() && d.len() <= 6 && d.chars().all(|c| c.is_ascii_digit()))
}

pub fn parse(text: &str) -> Result<BoundaryApi, String> {
    let mut api = BoundaryApi::default();
    let mut saw_schema = false;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        let err = |msg: &str| format!("BOUNDARY_API.txt:{lineno}: {msg}");
        if !saw_schema {
            if line == "schema fln-boundary-api/1" {
                saw_schema = true;
                continue;
            }
            return Err(err("first directive must be `schema fln-boundary-api/1`"));
        }
        let Some(rest) = line.strip_prefix("row ") else {
            return Err(err(
                "expected `row <id> | <path> | <kind> <name> | <surface type> | <evidence> | <no-admission>`",
            ));
        };
        let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
        if fields.len() != 6 {
            return Err(err("row must have exactly six '|'-separated fields"));
        }
        if !valid_id(fields[0]) {
            return Err(err("row id must match FLN-BX-NNNN"));
        }
        if fields.iter().any(|f| f.is_empty()) {
            return Err(err("every field must be non-empty"));
        }
        let mut item = fields[2].split_whitespace();
        let (Some(kind), Some(name), None) = (item.next(), item.next(), item.next()) else {
            return Err(err("third field must be exactly `<kind> <name>`"));
        };
        if !KINDS.contains(&kind) {
            return Err(err(&format!(
                "unknown item kind `{kind}` (expected one of {KINDS:?})"
            )));
        }
        if api.rows.iter().any(|r| r.id == fields[0]) {
            return Err(err("duplicate row id"));
        }
        if api
            .rows
            .iter()
            .any(|r| r.path == fields[1] && r.name == name && r.kind == kind)
        {
            return Err(err("duplicate (path, kind, name) row"));
        }
        api.rows.push(ApiRow {
            id: fields[0].to_string(),
            path: fields[1].to_string(),
            kind: kind.to_string(),
            name: name.to_string(),
        });
    }
    if !saw_schema {
        return Err("BOUNDARY_API.txt: missing schema line".to_string());
    }
    Ok(api)
}

/// Load the file if present. `Ok(None)` when absent — legal only while no
/// boundary crate exposes any public item (the caller enforces that).
pub fn load(root: &Path, rel: &str) -> Result<Option<BoundaryApi>, String> {
    let path = root.join(rel);
    if !path.is_file() {
        return Ok(None);
    }
    let text = fs::read_to_string(&path).map_err(|error| format!("cannot read {rel}: {error}"))?;
    parse(&text).map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_rows_and_rejects_bad_shapes() {
        let ok = "schema fln-boundary-api/1\n\
                  row FLN-BX-0001 | crates/fln-unsafe-abi/src/handle.rs | struct Obj | opaque owned handle | tests.rs suite | linear ownership, no kernel types nameable\n\
                  row FLN-BX-0002 | crates/fln-unsafe-abi/src/lib.rs | use Header | re-export of rc::Header | layout suite | plain-int header view\n";
        let api = parse(ok).expect("parses");
        assert_eq!(api.rows.len(), 2);
        assert_eq!(api.rows[0].kind, "struct");
        assert_eq!(api.rows[0].name, "Obj");
        assert_eq!(api.rows[1].kind, "use");

        assert!(parse("schema fln-boundary-api/1\nrow BAD | a | fn f | t | e | n\n").is_err());
        assert!(
            parse("schema fln-boundary-api/1\nrow FLN-BX-1 | a | weird f | t | e | n\n").is_err()
        );
        assert!(parse("schema fln-boundary-api/1\nrow FLN-BX-1 | a | fn | t | e | n\n").is_err());
        assert!(parse("row FLN-BX-1 | a | fn f | t | e | n\n").is_err());
        let dup = "schema fln-boundary-api/1\n\
                   row FLN-BX-1 | a | fn f | t | e | n\nrow FLN-BX-2 | a | fn f | t | e | n\n";
        assert!(parse(dup).is_err());
    }
}
