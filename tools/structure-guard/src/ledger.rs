//! Parser for `ci/UNSAFE_LEDGER.txt` and the scanner for `#[allow(unsafe_code)]` sites.

use std::fs;
use std::path::Path;

#[derive(Debug)]
pub struct LedgerRow {
    pub id: String,
    /// Workspace-relative path ('/'-separated) of the file containing the site.
    pub path: String,
}

#[derive(Debug, Default)]
pub struct Ledger {
    pub rows: Vec<LedgerRow>,
}

fn valid_id(s: &str) -> bool {
    s.strip_prefix("FLN-UL-")
        .is_some_and(|d| !d.is_empty() && d.len() <= 6 && d.chars().all(|c| c.is_ascii_digit()))
}

pub fn parse(text: &str) -> Result<Ledger, String> {
    let mut ledger = Ledger::default();
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
        let err = |msg: &str| format!("UNSAFE_LEDGER.txt:{lineno}: {msg}");

        if !saw_schema {
            if line == "schema fln-unsafe-ledger/1" {
                saw_schema = true;
                continue;
            }
            return Err(err("first directive must be `schema fln-unsafe-ledger/1`"));
        }
        let Some(rest) = line.strip_prefix("row ") else {
            return Err(err("expected `row <id> | <path> | ... ` (six fields)"));
        };
        let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
        if fields.len() != 6 {
            return Err(err("row must have exactly six '|'-separated fields"));
        }
        if !valid_id(fields[0]) {
            return Err(err("row id must match FLN-UL-NNNN"));
        }
        if fields.iter().any(|f| f.is_empty()) {
            return Err(err("every ledger field must be non-empty"));
        }
        if ledger.rows.iter().any(|r| r.id == fields[0]) {
            return Err(err("duplicate ledger row id"));
        }
        ledger.rows.push(LedgerRow {
            id: fields[0].to_string(),
            path: fields[1].to_string(),
        });
    }

    if !saw_schema {
        return Err("UNSAFE_LEDGER.txt: missing schema line".to_string());
    }
    Ok(ledger)
}

/// One lint-level attribute that can lower `unsafe_code`: `allow`, `warn`, or `expect`.
#[derive(Debug)]
pub struct AllowSite {
    /// Workspace-relative path, '/'-separated.
    pub path: String,
    pub line: usize,
    /// Only canonical, ledgered `allow` is admissible. The other levels are retained
    /// so the caller can report their attempt to lower the boundary root's `deny`.
    pub level: &'static str,
    /// Ledger id from the `// UNSAFE-LEDGER: FLN-UL-NNNN` marker, if present on the
    /// same line or the nearest non-empty line above.
    pub id: Option<String>,
    /// Inner attributes apply to an entire crate/module and are never a narrowly scoped
    /// unsafe allowance.
    pub inner: bool,
}

fn marker_id(line: &str) -> Option<String> {
    // Markers are deliberately comment-only. This prevents a string literal containing
    // `UNSAFE-LEDGER:` from authorizing a real allow attribute below it.
    let comment = line.trim_start().strip_prefix("//")?.trim_start();
    let rest = comment.strip_prefix("UNSAFE-LEDGER:")?.trim();
    let id: String = rest
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '-')
        .collect();
    let trailing = &rest[id.len()..];
    if id.is_empty() || !trailing.trim().is_empty() {
        None
    } else {
        Some(id)
    }
}

#[derive(Debug, Clone)]
struct Lexeme {
    text: String,
    line: usize,
    delimiter_depth: usize,
}

#[derive(Debug)]
struct Attribute {
    line: usize,
    inner: bool,
    delimiter_depth: usize,
    lexemes: Vec<Lexeme>,
}

fn raw_string_end(bytes: &[u8], start: usize) -> Option<(usize, usize)> {
    let mut cursor = start;
    if bytes.get(cursor) == Some(&b'b') || bytes.get(cursor) == Some(&b'c') {
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'r') {
        return None;
    }
    cursor += 1;
    let hashes_start = cursor;
    while bytes.get(cursor) == Some(&b'#') {
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'"') {
        return None;
    }
    Some((cursor + 1, cursor - hashes_start))
}

fn rust_lexemes(text: &str) -> Vec<Lexeme> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut cursor = 0;
    let mut line = 1;
    let mut delimiter_depth = 0_usize;
    while cursor < bytes.len() {
        let byte = bytes[cursor];
        if byte == b'\n' {
            line += 1;
            cursor += 1;
            continue;
        }
        if byte.is_ascii_whitespace() {
            cursor += 1;
            continue;
        }
        if bytes.get(cursor..cursor + 2) == Some(b"//") {
            cursor += 2;
            while cursor < bytes.len() && bytes[cursor] != b'\n' {
                cursor += 1;
            }
            continue;
        }
        if bytes.get(cursor..cursor + 2) == Some(b"/*") {
            cursor += 2;
            let mut depth = 1_u32;
            while cursor < bytes.len() && depth != 0 {
                if bytes[cursor] == b'\n' {
                    line += 1;
                    cursor += 1;
                } else if bytes.get(cursor..cursor + 2) == Some(b"/*") {
                    depth += 1;
                    cursor += 2;
                } else if bytes.get(cursor..cursor + 2) == Some(b"*/") {
                    depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
            continue;
        }
        if let Some((mut end, hashes)) = raw_string_end(bytes, cursor) {
            while end < bytes.len() {
                if bytes[end] == b'\n' {
                    line += 1;
                }
                if bytes[end] == b'"'
                    && bytes
                        .get(end + 1..end + 1 + hashes)
                        .is_some_and(|tail| tail.iter().all(|value| *value == b'#'))
                {
                    end += 1 + hashes;
                    break;
                }
                end += 1;
            }
            cursor = end;
            continue;
        }
        if byte == b'"' {
            cursor += 1;
            let mut escaped = false;
            while cursor < bytes.len() {
                let current = bytes[cursor];
                if current == b'\n' {
                    line += 1;
                }
                cursor += 1;
                if escaped {
                    escaped = false;
                } else if current == b'\\' {
                    escaped = true;
                } else if current == b'"' {
                    break;
                }
            }
            continue;
        }
        if byte == b'\'' {
            // Skip a character literal when a closing quote is nearby. A Rust lifetime
            // has no closing quote and is tokenized as punctuation + identifier instead.
            let mut end = cursor + 1;
            let mut escaped = false;
            let mut closed = false;
            while end < bytes.len() && end <= cursor + 8 && bytes[end] != b'\n' {
                let current = bytes[end];
                end += 1;
                if escaped {
                    escaped = false;
                } else if current == b'\\' {
                    escaped = true;
                } else if current == b'\'' {
                    closed = true;
                    break;
                }
            }
            if closed {
                cursor = end;
                continue;
            }
        }
        if bytes.get(cursor..cursor + 2) == Some(b"r#")
            && bytes
                .get(cursor + 2)
                .is_some_and(|next| next.is_ascii_alphabetic() || *next == b'_')
        {
            let start = cursor;
            cursor += 3;
            while cursor < bytes.len()
                && (bytes[cursor].is_ascii_alphanumeric() || bytes[cursor] == b'_')
            {
                cursor += 1;
            }
            out.push(Lexeme {
                text: text[start..cursor].to_string(),
                line,
                delimiter_depth,
            });
            continue;
        }
        if byte.is_ascii_alphabetic() || byte == b'_' {
            let start = cursor;
            cursor += 1;
            while cursor < bytes.len()
                && (bytes[cursor].is_ascii_alphanumeric() || bytes[cursor] == b'_')
            {
                cursor += 1;
            }
            out.push(Lexeme {
                text: text[start..cursor].to_string(),
                line,
                delimiter_depth,
            });
            continue;
        }
        out.push(Lexeme {
            text: (byte as char).to_string(),
            line,
            delimiter_depth,
        });
        match byte {
            b'(' | b'[' | b'{' => delimiter_depth = delimiter_depth.saturating_add(1),
            b')' | b']' | b'}' => delimiter_depth = delimiter_depth.saturating_sub(1),
            _ => {}
        }
        cursor += 1;
    }
    out
}

fn attributes(text: &str) -> Vec<Attribute> {
    let lexemes = rust_lexemes(text);
    let mut out = Vec::new();
    let mut cursor = 0;
    while cursor < lexemes.len() {
        if lexemes[cursor].text != "#" {
            cursor += 1;
            continue;
        }
        let line = lexemes[cursor].line;
        let delimiter_depth = lexemes[cursor].delimiter_depth;
        let mut next = cursor + 1;
        let inner = lexemes.get(next).is_some_and(|lexeme| lexeme.text == "!");
        if inner {
            next += 1;
        }
        if !lexemes.get(next).is_some_and(|lexeme| lexeme.text == "[") {
            cursor += 1;
            continue;
        }
        next += 1;
        let body_start = next;
        let mut depth = 1_u32;
        while next < lexemes.len() && depth != 0 {
            match lexemes[next].text.as_str() {
                "[" => depth += 1,
                "]" => depth -= 1,
                _ => {}
            }
            next += 1;
        }
        if depth == 0 {
            out.push(Attribute {
                line,
                inner,
                delimiter_depth,
                lexemes: lexemes[body_start..next - 1].to_vec(),
            });
            cursor = next;
        } else {
            break;
        }
    }
    out
}

fn attribute_contains_lint_call(attribute: &Attribute, level: &str, lint: &str) -> bool {
    attribute.lexemes.windows(2).enumerate().any(|(idx, pair)| {
        pair[0].text == level
            && pair[1].text == "("
            && attribute.lexemes[idx + 2..]
                .iter()
                .take_while(|lexeme| lexeme.text != ")")
                .any(|lexeme| lexeme.text == lint)
    })
}

fn attribute_sets_lint_directly(attribute: &Attribute, level: &str, lint: &str) -> bool {
    attribute
        .lexemes
        .first()
        .is_some_and(|lexeme| lexeme.text == level)
        && attribute
            .lexemes
            .get(1)
            .is_some_and(|lexeme| lexeme.text == "(")
        && attribute.lexemes[2..]
            .iter()
            .take_while(|lexeme| lexeme.text != ")")
            .any(|lexeme| lexeme.text == lint)
}

#[derive(Debug, Default)]
pub struct LintPosture {
    pub forbid_unsafe: bool,
    pub deny_unsafe: bool,
}

pub fn lint_posture(text: &str) -> LintPosture {
    let mut posture = LintPosture::default();
    for attribute in attributes(text)
        .into_iter()
        .filter(|attribute| attribute.inner && attribute.delimiter_depth == 0)
    {
        // A nested lint inside `cfg_attr` is conditional and may be inactive. Only an
        // unconditional crate-level `forbid`/`deny` establishes the D3 root posture.
        posture.forbid_unsafe |= attribute_sets_lint_directly(&attribute, "forbid", "unsafe_code");
        posture.deny_unsafe |= attribute_sets_lint_directly(&attribute, "deny", "unsafe_code");
    }
    posture
}

#[derive(Debug)]
pub struct ExportSite {
    pub line: usize,
    pub detail: &'static str,
}

#[derive(Debug)]
pub struct LocatedExportSite {
    pub path: String,
    pub line: usize,
    pub detail: &'static str,
}

pub fn source_escape_sites(text: &str) -> Vec<ExportSite> {
    let lexemes = rust_lexemes(text);
    let mut sites = Vec::new();
    for pair in lexemes.windows(2) {
        if pair[0].text == "include" && pair[1].text == "!" {
            sites.push(ExportSite {
                line: pair[0].line,
                detail: "source inclusion can hide authoritative code",
            });
        }
    }
    for attribute in attributes(text) {
        if attribute
            .lexemes
            .windows(2)
            .any(|pair| pair[0].text == "path" && pair[1].text == "=")
        {
            sites.push(ExportSite {
                line: attribute.line,
                detail: "path-based or conditional path module can hide authoritative code",
            });
        }
    }
    sites.sort_by_key(|site| (site.line, site.detail));
    sites.dedup_by_key(|site| (site.line, site.detail));
    sites
}

/// D3 law (b) export rule for boundary crates: no symbol export of any kind
/// and no macro definition (they mint expansion surface other crates could
/// invoke). Bare-`pub` Rust items are no longer flagged here unconditionally:
/// since slice 2 of bead fln-lld they are matched item-by-item against the
/// reviewed `ci/BOUNDARY_API.txt` allowlist ([`public_item_sites`] +
/// `boundary_api`), with both directions (undeclared item, stale row)
/// failing in `checks.rs`. Macro INVOCATIONS are verified by the expansion
/// covenant ([`expanded_surface_violations`] + [`expanded_public_items`]
/// over `-Zunpretty=expanded` output).
pub fn external_export_sites(text: &str) -> Vec<ExportSite> {
    let lexemes = rust_lexemes(text);
    let mut sites = source_escape_sites(text);
    for (idx, lexeme) in lexemes.iter().enumerate() {
        let declarative_definition = lexeme.text == "macro_rules"
            && lexemes.get(idx + 1).is_some_and(|next| next.text == "!");
        // Macros 2.0: `macro name { .. }` — `macro` here is a keyword only when
        // NOT part of `macro_rules!` and not a path segment; the next lexeme is
        // the macro's name (an identifier, never `!` or `_rules`).
        let macro_two_definition = lexeme.text == "macro"
            && lexemes.get(idx + 1).is_some_and(|next| {
                next.text != "!"
                    && next
                        .text
                        .chars()
                        .next()
                        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
            });
        if declarative_definition || macro_two_definition {
            sites.push(ExportSite {
                line: lexeme.line,
                detail: "macro definition in a boundary crate",
            });
        }
    }
    for attribute in attributes(text) {
        for (name, detail) in [
            ("macro_export", "exported macro"),
            ("no_mangle", "unmangled symbol export"),
            ("export_name", "named symbol export"),
        ] {
            if attribute.lexemes.iter().any(|lexeme| lexeme.text == name) {
                sites.push(ExportSite {
                    line: attribute.line,
                    detail,
                });
            }
        }
    }
    sites.sort_by_key(|site| (site.line, site.detail));
    sites.dedup_by_key(|site| (site.line, site.detail));
    sites
}

/// Lines containing macro invocations (`name!(..)` / `name![..]` / `name!{..}`),
/// excluding `include!` (a source-escape finding) and macro definitions (an
/// export finding). Any such line makes the boundary crate subject to the
/// expansion covenant.
pub fn macro_invocation_lines(text: &str) -> Vec<usize> {
    let lexemes = rust_lexemes(text);
    let mut lines = Vec::new();
    for (idx, lexeme) in lexemes.iter().enumerate() {
        let macro_invocation = lexeme.text == "!"
            && idx > 0
            && lexemes[idx - 1].text != "include"
            && lexemes[idx - 1].text != "macro_rules"
            && lexemes
                .get(idx + 1)
                .is_some_and(|next| matches!(next.text.as_str(), "(" | "[" | "{"))
            && lexemes[idx - 1]
                .text
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_alphabetic() || first == '_');
        if macro_invocation {
            lines.push(lexeme.line);
        }
    }
    lines.dedup();
    lines
}

/// The expansion covenant's surface scan (bead fln-lld): run over the FULLY
/// EXPANDED crate text (`rustc -Zunpretty=expanded`, one run per compiled
/// cfg), where nothing can hide behind a macro any more. In expanded form a
/// boundary crate must still contain no
/// `macro_export`/`no_mangle`/`export_name` attribute and no `global_asm!`
/// (which can define symbols below the attribute layer). Bare-`pub` items in
/// the expanded surface are checked separately by the subset rule
/// ([`expanded_public_items`] ⊆ declared source items, `checks.rs`).
/// D1 closes the macro universe to `std`'s own macros (no proc-macro or
/// third-party macro can even be named), so post-expansion text scanning is
/// sound: whatever a macro synthesized is literal text here.
pub fn expanded_surface_violations(expanded: &str) -> Vec<ExportSite> {
    let lexemes = rust_lexemes(expanded);
    let mut sites = Vec::new();
    for (idx, lexeme) in lexemes.iter().enumerate() {
        if lexeme.text == "global_asm" && lexemes.get(idx + 1).is_some_and(|next| next.text == "!")
        {
            sites.push(ExportSite {
                line: lexeme.line,
                detail: "global_asm in expanded surface",
            });
        }
    }
    for attribute in attributes(expanded) {
        for (name, detail) in [
            ("macro_export", "exported macro in expanded surface"),
            ("no_mangle", "unmangled symbol export in expanded surface"),
            ("export_name", "named symbol export in expanded surface"),
        ] {
            if attribute.lexemes.iter().any(|lexeme| lexeme.text == name) {
                sites.push(ExportSite {
                    line: attribute.line,
                    detail,
                });
            }
        }
    }
    sites.sort_by_key(|site| (site.line, site.detail));
    sites.dedup_by_key(|site| (site.line, site.detail));
    sites
}

/// Count `allow(unsafe_code)` attributes in a text (source or expanded).
/// The expansion covenant requires: expanded count <= ledgered source count —
/// a macro that synthesized an extra allowance would push the expanded count
/// above the number of marker-carrying source sites.
pub fn count_allow_unsafe_attributes(text: &str) -> usize {
    attributes(text)
        .iter()
        .filter(|attribute| attribute_sets_lint_directly(attribute, "allow", "unsafe_code"))
        .count()
}

/// One bare-`pub` item found in boundary-crate source (or expanded output).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PubItem {
    pub line: usize,
    /// `fn`/`struct`/`enum`/`union`/`trait`/`type`/`mod`/`const`/`static`/
    /// `use`/`field` — or `unknown` when the shape after `pub` is not
    /// recognized (fail closed: the caller reports it).
    pub kind: String,
    pub name: String,
}

/// Extract every bare-`pub` item declaration. Deliberately strict: modifiers
/// (`unsafe`, `async`, `extern "C"`, `const fn`) are understood; `pub use`
/// must export exactly one leaf (`pub use path::Item;` or `… as Alias;` —
/// grouped re-exports come back as `unknown` and fail closed); a struct
/// field `pub name: T` is kind `field`. Anything else after `pub` is
/// `unknown`, which the caller must treat as a violation, never a skip.
pub fn public_item_sites(text: &str) -> Vec<PubItem> {
    let lexemes = rust_lexemes(text);
    let mut items = Vec::new();
    let is_ident = |t: &str| {
        t.chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
    };
    for (idx, lexeme) in lexemes.iter().enumerate() {
        if lexeme.text != "pub" || lexemes.get(idx + 1).is_some_and(|next| next.text == "(") {
            continue;
        }
        let mut j = idx + 1;
        // Skip declaration modifiers. String literals (the ABI string in
        // `extern "C"`) are not lexemes, so `extern` is directly followed by
        // the item keyword.
        while lexemes
            .get(j)
            .is_some_and(|l| matches!(l.text.as_str(), "unsafe" | "async" | "extern"))
        {
            j += 1;
        }
        let unknown = |line| PubItem {
            line,
            kind: "unknown".to_string(),
            name: "?".to_string(),
        };
        let Some(head) = lexemes.get(j) else {
            items.push(unknown(lexeme.line));
            continue;
        };
        let item = match head.text.as_str() {
            "const" => {
                // `pub const fn name` vs `pub const NAME: T`.
                match (lexemes.get(j + 1), lexemes.get(j + 2)) {
                    (Some(next), _) if next.text == "fn" => lexemes.get(j + 2).map(|n| PubItem {
                        line: lexeme.line,
                        kind: "fn".to_string(),
                        name: n.text.clone(),
                    }),
                    (Some(name), _) if is_ident(&name.text) => Some(PubItem {
                        line: lexeme.line,
                        kind: "const".to_string(),
                        name: name.text.clone(),
                    }),
                    _ => None,
                }
            }
            "fn" | "struct" | "enum" | "union" | "trait" | "type" | "mod" | "static" => lexemes
                .get(j + 1)
                .filter(|n| is_ident(&n.text))
                .map(|n| PubItem {
                    line: lexeme.line,
                    kind: head.text.clone(),
                    name: n.text.clone(),
                }),
            "use" => {
                // Walk to the terminating `;`, rejecting grouped/glob forms.
                let mut k = j + 1;
                let mut last_ident: Option<String> = None;
                let mut clean = true;
                while let Some(l) = lexemes.get(k) {
                    match l.text.as_str() {
                        ";" => break,
                        "{" | "}" | "*" | "," => {
                            clean = false;
                            break;
                        }
                        t if is_ident(t) => last_ident = Some(t.to_string()),
                        "::" | ":" | "as" => {}
                        _ => {}
                    }
                    k += 1;
                }
                if clean {
                    last_ident.map(|name| PubItem {
                        line: lexeme.line,
                        kind: "use".to_string(),
                        name,
                    })
                } else {
                    None
                }
            }
            name if is_ident(name) && lexemes.get(j + 1).is_some_and(|n| n.text == ":") => {
                Some(PubItem {
                    line: lexeme.line,
                    kind: "field".to_string(),
                    name: name.to_string(),
                })
            }
            _ => None,
        };
        items.push(item.unwrap_or_else(|| unknown(lexeme.line)));
    }
    items
}

/// [`public_item_sites`] over expanded output — the covenant's subset rule:
/// every (kind, name) here must exist in the declared source item set, or a
/// macro synthesized a new public item.
pub fn expanded_public_items(expanded: &str) -> Vec<PubItem> {
    public_item_sites(expanded)
}

/// Kernel-admission token tripwire (D3 law b defense-in-depth): the boundary
/// crates cannot even DEPEND on the trust base (FLN-STRUCT-008), so these
/// identifiers appearing anywhere in boundary source or expanded output is
/// unconditionally a finding — cheap string-level insurance against a
/// laundering surface being prepared before the dependency edge exists.
pub fn admission_token_sites(text: &str) -> Vec<ExportSite> {
    let mut sites = Vec::new();
    for lexeme in rust_lexemes(text) {
        if matches!(
            lexeme.text.as_str(),
            "fln_kernel" | "fln_checker" | "CheckedExpr"
        ) {
            sites.push(ExportSite {
                line: lexeme.line,
                detail: "kernel-admission token in boundary code",
            });
        }
    }
    sites.dedup_by_key(|site| site.line);
    sites
}

pub fn scan_external_exports(
    dir: &Path,
    rel_prefix: &str,
    out: &mut Vec<LocatedExportSite>,
) -> Result<(), String> {
    let metadata = fs::symlink_metadata(dir)
        .map_err(|error| format!("cannot inspect directory {rel_prefix}: {error}"))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(());
    }
    let entries = fs::read_dir(dir)
        .map_err(|error| format!("cannot read directory {rel_prefix}: {error}"))?;
    let mut entries: Vec<_> = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read directory {rel_prefix}: {error}"))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let name = entry.file_name().to_string_lossy().into_owned();
        let rel = format!("{rel_prefix}/{name}");
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {rel}: {error}"))?;
        if file_type.is_symlink() {
            continue;
        }
        if file_type.is_dir() {
            scan_external_exports(&path, &rel, out)?;
        } else if file_type.is_file() && name.ends_with(".rs") {
            let text =
                fs::read_to_string(&path).map_err(|error| format!("cannot read {rel}: {error}"))?;
            out.extend(
                external_export_sites(&text)
                    .into_iter()
                    .map(|site| LocatedExportSite {
                        path: rel.clone(),
                        line: site.line,
                        detail: site.detail,
                    }),
            );
        }
    }
    Ok(())
}

/// Recursively scan every `.rs` file under `dir` for allow-sites. `rel_prefix` is the
/// workspace-relative path of `dir`.
pub fn scan_allow_sites(
    dir: &Path,
    rel_prefix: &str,
    out: &mut Vec<AllowSite>,
) -> Result<(), String> {
    let metadata = fs::symlink_metadata(dir)
        .map_err(|error| format!("cannot inspect directory {rel_prefix}: {error}"))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(());
    }
    let entries =
        fs::read_dir(dir).map_err(|e| format!("cannot read directory {rel_prefix}: {e}"))?;
    let mut entries: Vec<_> = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("cannot read directory {rel_prefix}: {e}"))?;
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let name = entry.file_name().to_string_lossy().into_owned();
        let rel = format!("{rel_prefix}/{name}");
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {rel}: {error}"))?;
        if file_type.is_symlink() {
            continue;
        }
        if file_type.is_dir() {
            scan_allow_sites(&path, &rel, out)?;
        } else if file_type.is_file() && name.ends_with(".rs") {
            let text = fs::read_to_string(&path).map_err(|e| format!("cannot read {rel}: {e}"))?;
            let lines: Vec<&str> = text.lines().collect();
            for attribute in attributes(&text) {
                for level in ["allow", "warn", "expect"] {
                    if !attribute_contains_lint_call(&attribute, level, "unsafe_code") {
                        continue;
                    }
                    let i = attribute.line.saturating_sub(1);
                    let mut id = None;
                    // The marker must be the nearest preceding non-empty, comment-only line.
                    for above in lines[..i].iter().rev() {
                        if above.trim().is_empty() {
                            continue;
                        }
                        id = marker_id(above);
                        break;
                    }
                    out.push(AllowSite {
                        path: rel.clone(),
                        line: attribute.line,
                        level,
                        id,
                        inner: attribute.inner,
                    });
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_empty_ledger() {
        let l = parse("schema fln-unsafe-ledger/1\n# none\n").expect("parses");
        assert!(l.rows.is_empty());
    }

    #[test]
    fn parses_row_and_rejects_bad_rows() {
        let ok = "schema fln-unsafe-ledger/1\n\
                  row FLN-UL-0001 | crates/fln-unsafe-abi/src/lib.rs | layout law | rig T-1 | safe copy | no admission\n";
        let l = parse(ok).expect("parses");
        assert_eq!(l.rows.len(), 1);
        assert_eq!(l.rows[0].id, "FLN-UL-0001");

        assert!(parse("schema fln-unsafe-ledger/1\nrow BAD-1 | a | b | c | d | e\n").is_err());
        assert!(parse("schema fln-unsafe-ledger/1\nrow FLN-UL-1 | a | b | c | d\n").is_err());
        assert!(parse("schema fln-unsafe-ledger/1\nrow FLN-UL-1 | a |  | c | d | e\n").is_err());
        let dup = "schema fln-unsafe-ledger/1\n\
                   row FLN-UL-1 | a | b | c | d | e\nrow FLN-UL-1 | a | b | c | d | e\n";
        assert!(parse(dup).is_err());
    }

    #[test]
    fn marker_extraction() {
        assert_eq!(
            marker_id("// UNSAFE-LEDGER: FLN-UL-0042"),
            Some("FLN-UL-0042".to_string())
        );
        assert_eq!(marker_id("// UNSAFE-LEDGER: FLN-UL-0042 layout"), None);
        assert_eq!(marker_id("no marker here"), None);
        assert_eq!(
            marker_id("let fake = \"// UNSAFE-LEDGER: FLN-UL-1\";"),
            None
        );
    }

    #[test]
    fn lexer_ignores_comments_and_strings_but_finds_attribute_variants() {
        let text = r##"
/* #![forbid(unsafe_code)] */
const FAKE: &str = r#"#![forbid(unsafe_code)] #[allow(unsafe_code)]"#;
#![deny(unsafe_code)]
#[allow ( unsafe_code, dead_code )]
fn one() {}
#[cfg_attr(any(), allow(unsafe_code))]
fn two() {}
"##;
        let posture = lint_posture(text);
        assert!(!posture.forbid_unsafe);
        assert!(posture.deny_unsafe);
        let allows: Vec<_> = attributes(text)
            .into_iter()
            .filter(|attribute| attribute_contains_lint_call(attribute, "allow", "unsafe_code"))
            .collect();
        assert_eq!(allows.len(), 2);
    }

    #[test]
    fn conditional_cfg_attr_cannot_spoof_root_lint_posture() {
        let ordinary = lint_posture("#![cfg_attr(any(), forbid(unsafe_code))]\n");
        assert!(!ordinary.forbid_unsafe);
        assert!(!ordinary.deny_unsafe);

        let boundary = lint_posture("#![cfg_attr(any(), deny(unsafe_code))]\n");
        assert!(!boundary.forbid_unsafe);
        assert!(!boundary.deny_unsafe);

        let unconditional =
            lint_posture("#![forbid(unsafe_code, warnings)]\n#![deny(unsafe_code, unused)]\n");
        assert!(unconditional.forbid_unsafe);
        assert!(unconditional.deny_unsafe);
    }

    #[test]
    fn nested_or_macro_attributes_cannot_spoof_crate_root_posture() {
        let nested = lint_posture("mod decoy { #![forbid(unsafe_code)] }\n");
        assert!(!nested.forbid_unsafe);
        assert!(!nested.deny_unsafe);

        let macro_body = lint_posture("macro_rules! decoy { () => { #![deny(unsafe_code)] } }\n");
        assert!(!macro_body.forbid_unsafe);
        assert!(!macro_body.deny_unsafe);
    }

    #[test]
    fn conservative_export_scan_allows_restricted_visibility_only() {
        assert!(external_export_sites("pub(crate) fn local() {}\n").is_empty());
        assert!(external_export_sites("fn private(r#pub: u8) {}\n").is_empty());
        // Bare-pub items are the BOUNDARY_API allowlist's job now (matched in
        // checks.rs via public_item_sites); export attributes stay textual.
        let sites = external_export_sites(
            "pub fn outward() {}\n#[unsafe(no_mangle)]\nextern \"C\" fn symbol() {}\n",
        );
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].detail, "unmangled symbol export");
        assert_eq!(
            external_export_sites("include!(\"outside.inc\");\n").len(),
            1
        );
        assert_eq!(
            external_export_sites("#[path = \"outside.rs\"] mod outside;\n").len(),
            1
        );
        // Macro DEFINITIONS stay textually banned (they mint expansion surface)…
        assert_eq!(
            external_export_sites("macro_rules! hidden { () => {} }\n").len(),
            1
        );
        assert_eq!(
            external_export_sites("macro hidden2 { () => {} }\n").len(),
            1
        );
        // …but macro INVOCATIONS are the expansion covenant's job now
        // (FLN-STRUCT-025), not a textual finding.
        assert!(external_export_sites("hidden_policy!(allow, unsafe_code);\n").is_empty());
        assert_eq!(
            macro_invocation_lines("assert!(x);\nhidden_policy!(y);\n"),
            vec![1, 2]
        );
        assert!(macro_invocation_lines("include!(\"f.rs\");\n").is_empty());
        assert!(macro_invocation_lines("macro_rules! m { () => {} }\n").is_empty());
    }

    /// Seeded expansion-covenant defects (bead fln-lld): each laundering shape
    /// a macro could synthesize must be caught by the post-expansion scan.
    #[test]
    fn expansion_covenant_kills_seeded_defects() {
        // Macro-generated bare-pub exports (incl. generic / associated-type
        // shapes) are caught by the SUBSET rule: expanded_public_items must
        // all exist in the declared source set (checks.rs). The extractor
        // must therefore classify them.
        assert_eq!(
            public_item_sites("pub fn launder() {}\n"),
            vec![PubItem {
                line: 1,
                kind: "fn".into(),
                name: "launder".into()
            }]
        );
        assert_eq!(
            public_item_sites("pub fn generic<T: Trait>(x: T) -> T::Out { x.out() }\n"),
            vec![PubItem {
                line: 1,
                kind: "fn".into(),
                name: "generic".into()
            }]
        );
        assert_eq!(
            public_item_sites("pub struct Laundered(pub(crate) u8);\n"),
            vec![PubItem {
                line: 1,
                kind: "struct".into(),
                name: "Laundered".into()
            }]
        );
        // Modifier chains, consts, fields, and single-leaf re-exports.
        assert_eq!(
            public_item_sites("pub unsafe extern \"C\" fn s() {}\n"),
            vec![PubItem {
                line: 1,
                kind: "fn".into(),
                name: "s".into()
            }]
        );
        assert_eq!(
            public_item_sites("pub const fn cf() {}\npub const K: usize = 1;\n"),
            vec![
                PubItem {
                    line: 1,
                    kind: "fn".into(),
                    name: "cf".into()
                },
                PubItem {
                    line: 2,
                    kind: "const".into(),
                    name: "K".into()
                }
            ]
        );
        assert_eq!(
            public_item_sites("struct H { pub rc: i32 }\n"),
            vec![PubItem {
                line: 1,
                kind: "field".into(),
                name: "rc".into()
            }]
        );
        assert_eq!(
            public_item_sites("pub use rc::Header;\npub use shadow::enable as shadow_enable;\n"),
            vec![
                PubItem {
                    line: 1,
                    kind: "use".into(),
                    name: "Header".into()
                },
                PubItem {
                    line: 2,
                    kind: "use".into(),
                    name: "shadow_enable".into()
                }
            ]
        );
        // Grouped/glob re-exports cannot be classified — fail closed.
        assert_eq!(public_item_sites("pub use m::{a, b};\n")[0].kind, "unknown");
        assert_eq!(public_item_sites("pub use m::*;\n")[0].kind, "unknown");
        // pub(crate) is not an export.
        assert!(public_item_sites("pub(crate) fn local() {}\n").is_empty());
        // Kernel-admission token tripwire.
        assert_eq!(
            admission_token_sites("fn f() { let x = fln_kernel::check; }\n").len(),
            1
        );
        assert_eq!(admission_token_sites("type T = CheckedExpr;\n").len(), 1);
        assert!(admission_token_sites("fn clean() {}\n").is_empty());
        // Macro-generated symbol exports.
        assert_eq!(
            expanded_surface_violations("#[no_mangle]\nextern \"C\" fn s() {}\n").len(),
            1
        );
        assert_eq!(
            expanded_surface_violations("#[unsafe(export_name = \"lean_x\")]\nfn s() {}\n").len(),
            1
        );
        assert_eq!(
            expanded_surface_violations("#[macro_export]\nmacro_rules! m { () => {} }\n").len(),
            1
        );
        // Symbol definition below the attribute layer.
        assert_eq!(
            expanded_surface_violations("::core::arch::global_asm!(\".globl lean_x\");\n").len(),
            1
        );
        // The clean expanded shape: restricted visibility, impls, expressions.
        assert!(
            expanded_surface_violations(
                "pub(crate) fn f() {}\nimpl Drop for X { fn drop(&mut self) {} }\n"
            )
            .is_empty()
        );
    }

    /// Seeded allowance-synthesis defect: a macro that expands to an extra
    /// `#[allow(unsafe_code)]` pushes the expanded count above the ledgered
    /// source count.
    #[test]
    fn expansion_covenant_counts_synthesized_allowances() {
        let source = "// UNSAFE-LEDGER: FLN-UL-0001\n#[allow(unsafe_code)]\nfn site() {}\n";
        assert_eq!(count_allow_unsafe_attributes(source), 1);
        let expanded_honest = "#[allow(unsafe_code)]\nfn site() {}\n";
        assert_eq!(count_allow_unsafe_attributes(expanded_honest), 1);
        let expanded_laundered =
            "#[allow(unsafe_code)]\nfn site() {}\n#[allow(unsafe_code)]\nfn synthesized() {}\n";
        assert_eq!(count_allow_unsafe_attributes(expanded_laundered), 2);
        // Umbrella allows count too — an inner attribute smuggled via expansion
        // is still a count increase.
        assert_eq!(
            count_allow_unsafe_attributes("#![allow(unsafe_code)]\nfn f() {}\n"),
            1
        );
        // Unrelated lints do not count.
        assert_eq!(
            count_allow_unsafe_attributes("#[allow(dead_code)]\nfn f() {}\n"),
            0
        );
    }

    #[test]
    fn conditional_path_attribute_is_a_source_escape() {
        let sites = source_escape_sites(
            "#[cfg_attr(not(any()), path = \"../outside.rs\")]\nmod outside;\n",
        );
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].line, 1);
        assert!(sites[0].detail.contains("conditional path"));
    }
}
