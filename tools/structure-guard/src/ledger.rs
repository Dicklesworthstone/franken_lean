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
    /// Ledger id from the `// UNSAFE-LEDGER: FLN-UL-NNNN` marker, taken from the nearest
    /// non-empty line *above* the attribute. A marker trailing on the attribute's own
    /// line does not authorise it: the scan is deliberately one-directional so that the
    /// authorising comment always precedes what it authorises.
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
    offset: usize,
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
                offset: start,
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
                offset: start,
                delimiter_depth,
            });
            continue;
        }
        out.push(Lexeme {
            text: (byte as char).to_string(),
            line,
            offset: cursor,
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

/// The source prefix compiled into an ordinary (non-test) build.
///
/// Unit tests in the kernel need private access, so its three large test modules live at the
/// ends of their production files. They are not part of the release TCB and must not consume
/// the kernel's 12 KLOC covenant or its generated-authority inventory. This exclusion is
/// intentionally much narrower than a general `cfg` evaluator: only an exact, top-level
/// `#[cfg(test)] mod tests { ... }` that owns the lexical tail is removed. A nested module, a
/// string/comment decoy, a compound predicate, or any later production token keeps the whole
/// file in the governed release closure.
pub fn release_authority_source(text: &str) -> &str {
    const SPELLING: [(&str, usize); 10] = [
        ("#", 0),
        ("[", 0),
        ("cfg", 1),
        ("(", 1),
        ("test", 2),
        (")", 2),
        ("]", 1),
        ("mod", 0),
        ("tests", 0),
        ("{", 0),
    ];
    let lexemes = rust_lexemes(text);
    for start in 0..lexemes.len() {
        let Some(candidate) = lexemes.get(start..start + SPELLING.len()) else {
            break;
        };
        if !candidate
            .iter()
            .zip(SPELLING)
            .all(|(lexeme, (spelling, depth))| {
                lexeme.text == spelling && lexeme.delimiter_depth == depth
            })
        {
            continue;
        }
        let closing = lexemes
            .iter()
            .enumerate()
            .skip(start + SPELLING.len())
            .find(|(_, lexeme)| lexeme.text == "}" && lexeme.delimiter_depth == 1);
        if closing.is_some_and(|(index, _)| index + 1 == lexemes.len()) {
            return &text[..candidate[0].offset];
        }
    }
    text
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct NamedMacroSite {
    pub line: usize,
    pub name: String,
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
pub fn macro_definition_sites(text: &str) -> Vec<ExportSite> {
    let lexemes = rust_lexemes(text);
    let mut sites = Vec::new();
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
    sites.sort_by_key(|site| (site.line, site.detail));
    sites.dedup_by_key(|site| (site.line, site.detail));
    sites
}

pub fn external_export_sites(text: &str) -> Vec<ExportSite> {
    let mut sites = source_escape_sites(text);
    sites.extend(macro_definition_sites(text));
    for attribute in attributes(text) {
        for (name, detail) in [
            ("macro_export", "exported macro"),
            ("no_mangle", "unmangled symbol export"),
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

/// One `export_name` attribute site. Since bead franken_lean-83r these are no
/// longer unconditionally forbidden: they are the C-ABI export covenant's
/// subject (FLN-STRUCT-026) — admissible only in `fln-unsafe-abi`, only with
/// a parseable symbol string, and only when that symbol has an implemented
/// row in `ci/ABI_EXPORT_STATUS.txt`. `no_mangle` stays forbidden outright:
/// every export must name its symbol explicitly so the covenant can join it.
#[derive(Debug)]
pub struct ExportNameSite {
    pub line: usize,
    /// The symbol string, when it can be extracted exactly from the site's
    /// source line. `None` fails closed at the covenant layer.
    pub symbol: Option<String>,
}

/// Extract `export_name = "<symbol>"` from one source line. The main lexer
/// deliberately drops string literals (so strings can never authorize
/// anything), so the symbol is recovered by a targeted scan of the
/// attribute's own line; anything unextractable stays `None` (fail closed).
fn extract_export_symbol(line: &str) -> Option<String> {
    let idx = line.find("export_name")?;
    let rest = line[idx + "export_name".len()..].trim_start();
    let rest = rest.strip_prefix('=')?.trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"')?;
    let symbol = &rest[..end];
    let valid = !symbol.is_empty()
        && symbol
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && symbol
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_');
    valid.then(|| symbol.to_string())
}

/// Every attribute carrying an `export_name` lexeme, with its symbol when
/// exactly one is recoverable from the attribute's line. Works on source and
/// on `-Zunpretty=expanded` output (doc comments cannot leak in: the lexer
/// drops string literals, so `export_name` inside a `#[doc = "…"]` body is
/// never a lexeme).
pub fn export_name_attr_sites(text: &str) -> Vec<ExportNameSite> {
    let lines: Vec<&str> = text.lines().collect();
    let mut out = Vec::new();
    for attribute in attributes(text) {
        if attribute
            .lexemes
            .iter()
            .any(|lexeme| lexeme.text == "export_name")
        {
            let symbol = lines
                .get(attribute.line.saturating_sub(1))
                .copied()
                .and_then(extract_export_symbol);
            out.push(ExportNameSite {
                line: attribute.line,
                symbol,
            });
        }
    }
    out
}

/// Lines containing macro invocations (`name!(..)` / `name![..]` / `name!{..}`),
/// excluding `include!` (a source-escape finding) and macro definitions (an
/// export finding). Any such line makes the boundary crate subject to the
/// expansion covenant.
fn is_rust_keyword(text: &str) -> bool {
    matches!(
        text,
        "Self"
            | "abstract"
            | "as"
            | "async"
            | "await"
            | "become"
            | "box"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "do"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "final"
            | "fn"
            | "for"
            | "gen"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "macro"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "override"
            | "priv"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "try"
            | "type"
            | "typeof"
            | "union"
            | "unsafe"
            | "unsized"
            | "use"
            | "virtual"
            | "where"
            | "while"
            | "yield"
    )
}

/// Every occurrence of a `wanted` identifier, as a lexeme rather than as text.
///
/// Lexing rather than substring-matching is the whole point here: the file that
/// *defines* an independence boundary necessarily names every symbol the
/// boundary forbids, in prose. `rust_lexemes` discards line comments, block
/// comments and string literals, so a doc comment that says "never call
/// `is_equiv`" does not report itself as a violation.
pub fn identifier_sites(text: &str, wanted: &[&str]) -> Vec<NamedMacroSite> {
    let mut sites: Vec<NamedMacroSite> = rust_lexemes(text)
        .into_iter()
        .filter(|lexeme| wanted.contains(&lexeme.text.as_str()))
        .map(|lexeme| NamedMacroSite {
            line: lexeme.line,
            name: lexeme.text,
        })
        .collect();
    sites.sort_by(|left, right| (&left.name, left.line).cmp(&(&right.name, right.line)));
    sites.dedup();
    sites
}

/// One `.name(..)` method call, carrying the argument count that distinguishes
/// same-named methods on different types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodCallSite {
    pub line: usize,
    pub name: String,
    /// `None` when the call shape could not be resolved — a turbofish, or a
    /// parenthesis that never closes in this file.
    ///
    /// A caller must treat `None` as a FINDING, never as an absence. A guard that
    /// silently skips the call sites it cannot parse is a guard with a hole in
    /// exactly the shape of whatever it failed to parse.
    pub arity: Option<usize>,
}

/// Every `.name(..)` call of a `wanted` method, as lexemes rather than as text.
///
/// # Arity is part of the identity
///
/// This exists beside [`identifier_sites`] for one reason: **a method name is not
/// injective over methods.** `fln_env::Environment::add_decl` takes one argument and
/// `fln_hash::LogicalRootBuilder::add_decl` takes two, they are unrelated methods on
/// unrelated types, and both are called from a single file this guard must scan
/// (`crates/fln-conformance/tests/metamorphic_laws.rs`, lines 134 and 170). Matching the
/// bare name conflates them and reports fifteen fln-hash call sites as violations of a
/// rule about fln-env.
///
/// Crate-scoping does not rescue a name match, which is the part worth knowing before
/// reaching for the simpler primitive: the two methods coexist inside a crate the rule
/// legitimately scans, so the collision survives every scoping strategy and has to be
/// discriminated directly.
///
/// That defect is a recorded, recurring shape in this tree — a projection used as an
/// identity without checking it separates the values that must be told apart. See
/// `franken_lean-f6br` (a display-form name encoding collided in a census witness) and
/// `bf9ef450` (the same encoding reused as an intern key). This is the third instance,
/// caught before it shipped rather than after.
///
/// Lexing rather than substring-matching is inherited from [`identifier_sites`] and
/// matters for the same reason: a doc comment or string literal naming the forbidden
/// method must not report itself. `fln-verdict` already guards this very method by
/// asserting its own source lacks the text, using a split literal to avoid self-matching.
pub fn method_call_sites(text: &str, wanted: &[&str]) -> Vec<MethodCallSite> {
    let lexemes = rust_lexemes(text);
    let mut sites = Vec::new();
    for (idx, lexeme) in lexemes.iter().enumerate() {
        if !wanted.contains(&lexeme.text.as_str()) {
            continue;
        }
        // A method CALL, not a definition or an import: the name must be preceded by a
        // field-access dot. `fn add_decl`, `use x::add_decl` and `Self::add_decl` are all
        // correctly outside this rule's subject.
        if idx == 0 || lexemes[idx - 1].text != "." {
            continue;
        }
        sites.push(MethodCallSite {
            line: lexeme.line,
            name: lexeme.text.clone(),
            arity: call_arity(&lexemes, idx),
        });
    }
    sites.sort_by(|left, right| (&left.name, left.line).cmp(&(&right.name, right.line)));
    sites.dedup();
    sites
}

/// Arguments passed at `lexemes[name_idx]`'s call, or `None` if the shape is unresolved.
///
/// Depth bookkeeping follows `rust_lexemes`: an opening delimiter is recorded at the
/// depth OUTSIDE it and a closing delimiter at the depth INSIDE it, so for a call opening
/// at depth `d` the arguments and the matching `)` all sit at `d + 1`. Counting only
/// commas at that exact depth is what keeps a nested call's arguments — or a closure body,
/// or an array literal — from being counted as this call's.
fn call_arity(lexemes: &[Lexeme], name_idx: usize) -> Option<usize> {
    let open = lexemes.get(name_idx + 1)?;
    if open.text != "(" {
        // A turbofish or anything else between the name and its arguments. Unresolved
        // rather than zero: see `MethodCallSite::arity`.
        return None;
    }
    let inner = open.delimiter_depth + 1;
    let mut commas = 0_usize;
    let mut saw_argument_token = false;
    let mut last_was_comma = false;
    for lexeme in &lexemes[name_idx + 2..] {
        if lexeme.delimiter_depth == inner && lexeme.text == ")" {
            if !saw_argument_token {
                return Some(0);
            }
            // A trailing comma closes an argument already counted, so a multi-line call
            // does not report one argument more than it passes.
            return Some(if last_was_comma { commas } else { commas + 1 });
        }
        saw_argument_token = true;
        last_was_comma = lexeme.delimiter_depth == inner && lexeme.text == ",";
        if last_was_comma {
            commas += 1;
        }
    }
    None
}

pub fn macro_invocations(text: &str) -> Vec<NamedMacroSite> {
    let lexemes = rust_lexemes(text);
    let mut sites = Vec::new();
    for (idx, lexeme) in lexemes.iter().enumerate() {
        let macro_invocation = lexeme.text == "!"
            && idx > 0
            && lexemes[idx - 1].text != "include"
            && lexemes[idx - 1].text != "macro_rules"
            && !is_rust_keyword(&lexemes[idx - 1].text)
            && lexemes
                .get(idx + 1)
                .is_some_and(|next| matches!(next.text.as_str(), "(" | "[" | "{"))
            && lexemes[idx - 1]
                .text
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_alphabetic() || first == '_');
        if macro_invocation {
            sites.push(NamedMacroSite {
                line: lexeme.line,
                name: lexemes[idx - 1].text.clone(),
            });
        }
    }
    sites.sort_by(|left, right| (&left.name, left.line).cmp(&(&right.name, right.line)));
    sites.dedup();
    sites
}

pub fn macro_invocation_lines(text: &str) -> Vec<usize> {
    let mut lines: Vec<usize> = macro_invocations(text)
        .into_iter()
        .map(|site| site.line)
        .collect();
    lines.sort_unstable();
    lines.dedup();
    lines
}

/// Attribute macros and derive macros are generated authority too. Return their
/// source callsites so the kernel covenant can admit only a reviewed compiler-builtin
/// set while still charging every invocation line to the source LOC covenant.
pub fn attribute_invocations(text: &str) -> Vec<NamedMacroSite> {
    let mut sites = Vec::new();
    for attribute in attributes(text) {
        if let Some(name) = attribute.lexemes.first() {
            sites.push(NamedMacroSite {
                line: attribute.line,
                name: name.text.clone(),
            });
        }
    }
    sites.sort_by(|left, right| (&left.name, left.line).cmp(&(&right.name, right.line)));
    sites.dedup();
    sites
}

pub fn derive_macro_invocations(text: &str) -> Vec<NamedMacroSite> {
    let mut sites = Vec::new();
    for attribute in attributes(text) {
        if !attribute
            .lexemes
            .first()
            .is_some_and(|lexeme| lexeme.text == "derive")
        {
            continue;
        }
        for lexeme in attribute.lexemes.iter().skip(1) {
            if lexeme
                .text
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
            {
                sites.push(NamedMacroSite {
                    line: attribute.line,
                    name: lexeme.text.clone(),
                });
            }
        }
    }
    sites.sort_by(|left, right| (&left.name, left.line).cmp(&(&right.name, right.line)));
    sites.dedup();
    sites
}

/// The expansion covenant's surface scan (bead fln-lld): run over the FULLY
/// EXPANDED crate text (`rustc -Zunpretty=expanded`, one run per compiled
/// cfg), where nothing can hide behind a macro any more. In expanded form a
/// boundary crate must still contain no `macro_export`/`no_mangle` attribute
/// and no `global_asm!` (which can define symbols below the attribute
/// layer); an `export_name` attribute is admissible only when its symbol is
/// in `allowed_exports` — the declared, status-rowed C export set (bead
/// franken_lean-83r) — so a macro cannot synthesize an undeclared symbol
/// export. Bare-`pub` items in the expanded surface are checked separately
/// by the subset rule ([`expanded_public_items`] ⊆ declared source items,
/// `checks.rs`). D1 closes the macro universe to `std`'s own macros (no
/// proc-macro or third-party macro can even be named), so post-expansion
/// text scanning is sound: whatever a macro synthesized is literal text here.
pub fn expanded_surface_violations(
    expanded: &str,
    allowed_exports: &std::collections::BTreeSet<String>,
) -> Vec<ExportSite> {
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
        ] {
            if attribute.lexemes.iter().any(|lexeme| lexeme.text == name) {
                sites.push(ExportSite {
                    line: attribute.line,
                    detail,
                });
            }
        }
    }
    for site in export_name_attr_sites(expanded) {
        let admitted = site
            .symbol
            .as_ref()
            .is_some_and(|symbol| allowed_exports.contains(symbol));
        if !admitted {
            sites.push(ExportSite {
                line: site.line,
                detail: "export_name in expanded surface outside the declared C export set",
            });
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
    /// For `fn` items: the return type recovered from the item's own lexemes,
    /// whitespace removed. `None` means the signature declares no `->`.
    ///
    /// This exists so `ci/BOUNDARY_API.txt`'s declared surface type can be
    /// compared against the real signature. Every no-admission argument in
    /// that file of the form "value copy" or "plain-int snapshot" is a claim
    /// about *this* type, and until bead
    /// `fln-boundary-api-no-admission-argument-discarded-ez07` the declared
    /// type was parsed and thrown away, so a row could declare anything.
    pub ret: Option<String>,
    /// For `fn` items: a type parameter **in scope at the item** — its own or
    /// an enclosing `impl`/`trait` block's — that the return type names.
    ///
    /// This is the laundering signature D3 law (b) is about, and it is the one
    /// case the *dependency* law cannot carry. `pub fn forge<T>() -> T` names
    /// no kernel type, so `FLN-STRUCT-008` permits it and the admission-token
    /// tripwire sees nothing; the **caller** picks `T`, and can pick a checked
    /// declaration. What is laundered is the caller's own choice, from a crate
    /// that never has to name it.
    pub ret_type_param: Option<String>,
}

/// The pieces of a `pub fn` signature that D3 law (b) reasons about, recovered
/// from lexemes. Whitespace is dropped (the lexer already drops comments and
/// string literals) so [`Self::ret`] compares against a `ci/BOUNDARY_API.txt`
/// surface type written in source form.
#[derive(Debug, Default)]
struct FnSignature {
    /// The declared return type, or `None` when the signature has no `->`.
    ret: Option<String>,
    /// The identifier lexemes of the return type. Membership is tested against
    /// these rather than against [`Self::ret`] as a substring, because `Tally`
    /// contains `T` and is not a type parameter.
    ret_idents: Vec<String>,
    /// The type-parameter names the `fn` itself binds.
    type_params: Vec<String>,
}

/// The type-parameter names bound by the generic list opening at `open`, plus
/// the index just past its closing `>`.
///
/// Lifetimes and const parameters are excluded: neither can name a declaration,
/// so neither is a laundering vector. `None` when `open` is not a `<` or the
/// list never closes — the callers treat that as "recovered nothing", which
/// leaves the return type unrecoverable too and so fails closed downstream.
fn generic_type_params(lexemes: &[Lexeme], open: usize) -> Option<(Vec<String>, usize)> {
    if lexemes.get(open)?.text != "<" {
        return None;
    }
    let mut names = Vec::new();
    let mut angle = 0_usize;
    let mut at_group_start = false;
    let mut k = open;
    loop {
        let l = lexemes.get(k)?;
        match l.text.as_str() {
            // `->` inside a bound (`F: Fn(u8) -> u8`) is two lexemes, and its
            // `>` must not be read as closing the generic list.
            "-" if lexemes.get(k + 1).is_some_and(|n| n.text == ">") => {
                at_group_start = false;
                k += 2;
                continue;
            }
            "<" => {
                angle += 1;
                at_group_start = angle == 1;
            }
            ">" => {
                angle -= 1;
                if angle == 0 {
                    return Some((names, k + 1));
                }
                at_group_start = false;
            }
            "," if angle == 1 => at_group_start = true,
            text => {
                if at_group_start {
                    at_group_start = false;
                    // A lifetime is `'` + identifier, so the `'` lands here and
                    // consumes the group; `const N: usize` is consumed by its
                    // `const`. Only a type parameter's own name is recorded.
                    if text != "const"
                        && text
                            .chars()
                            .next()
                            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    {
                        names.push(text.to_string());
                    }
                }
            }
        }
        k += 1;
    }
}

/// The type parameters an `impl`/`trait` header binds at `open`, or none when
/// that position holds no generic list.
fn scope_params(lexemes: &[Lexeme], open: usize) -> Vec<String> {
    generic_type_params(lexemes, open).map_or_else(Vec::new, |(names, _)| names)
}

/// Recover a `fn`'s signature from the lexeme at `name_idx` (the item's name).
///
/// `base_depth` is the delimiter depth of the item's own `pub`, so methods
/// inside an `impl` block work unchanged. Anything unrecoverable — unbalanced
/// generics, a parameter list that never closes — yields an empty return,
/// which the covenant treats as a mismatch against any declared return and
/// refuses. Failing closed is deliberate: an unparseable signature must not
/// read as "declares nothing".
fn fn_signature(lexemes: &[Lexeme], name_idx: usize, base_depth: usize) -> FnSignature {
    let mut signature = FnSignature::default();
    let mut k = name_idx + 1;
    // Generic parameters. `->` cannot precede the parameter list, so the list
    // is walked before the arrow is looked for.
    if lexemes.get(k).is_some_and(|l| l.text == "<") {
        let Some((params, next)) = generic_type_params(lexemes, k) else {
            return signature;
        };
        signature.type_params = params;
        k = next;
    }
    // The parameter list, matched by depth rather than by counting, because
    // the lexer already tracks `()[]{}`.
    if lexemes.get(k).map(|l| (l.text.as_str(), l.delimiter_depth)) != Some(("(", base_depth)) {
        return signature;
    }
    k += 1;
    loop {
        let Some(l) = lexemes.get(k) else {
            return signature;
        };
        k += 1;
        if l.text == ")" && l.delimiter_depth == base_depth + 1 {
            break;
        }
    }
    // `->` is two lexemes: the lexer emits punctuation one byte at a time.
    if !(lexemes.get(k).is_some_and(|l| l.text == "-")
        && lexemes.get(k + 1).is_some_and(|l| l.text == ">"))
    {
        return signature;
    }
    k += 2;
    let mut out = String::new();
    while let Some(l) = lexemes.get(k) {
        if l.delimiter_depth == base_depth && matches!(l.text.as_str(), "{" | ";" | "where") {
            break;
        }
        if l.text
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        {
            signature.ret_idents.push(l.text.clone());
        }
        out.push_str(&l.text);
        k += 1;
    }
    signature.ret = (!out.is_empty()).then_some(out);
    signature
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
    // Type parameters bound by an enclosing `impl` or `trait` block are in
    // scope for the `pub fn`s inside it, and a caller chooses them exactly as
    // it chooses a function's own: `impl<T> Abi<T> { pub fn get(&self) -> T }`
    // is `pub fn get<T>() -> T` written one level up. Tracked as a stack keyed
    // by the block's interior delimiter depth.
    let mut scopes: Vec<(usize, Vec<String>)> = Vec::new();
    let mut pending_scope: Option<Vec<String>> = None;
    for (idx, lexeme) in lexemes.iter().enumerate() {
        while scopes
            .last()
            .is_some_and(|(interior, _)| *interior > lexeme.delimiter_depth)
        {
            scopes.pop();
        }
        match lexeme.text.as_str() {
            // Only the BINDER position counts. `impl<T> Foo<T>` binds at
            // `impl`+1 and `trait Name<T>` at `trait`+2; the `<T>` of
            // `impl Foo<T>` is a *use* of a type already in scope, and reading
            // it as a binder would make `impl Foo<u8>` put `u8` in scope and
            // redden every `-> u8` inside.
            "impl" => pending_scope = Some(scope_params(&lexemes, idx + 1)),
            "trait" => pending_scope = Some(scope_params(&lexemes, idx + 2)),
            "{" => {
                if let Some(params) = pending_scope.take() {
                    scopes.push((lexeme.delimiter_depth + 1, params));
                }
            }
            ";" => pending_scope = None,
            _ => {}
        }
        if lexeme.text != "pub" || lexemes.get(idx + 1).is_some_and(|next| next.text == "(") {
            continue;
        }
        let in_scope: Vec<&str> = scopes
            .iter()
            .flat_map(|(_, params)| params.iter().map(String::as_str))
            .collect();
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
            ret: None,
            ret_type_param: None,
        };
        let fn_item = |name: &Lexeme, name_idx: usize| {
            let signature = fn_signature(&lexemes, name_idx, lexeme.delimiter_depth);
            PubItem {
                line: lexeme.line,
                kind: "fn".to_string(),
                name: name.text.clone(),
                ret_type_param: signature
                    .type_params
                    .iter()
                    .map(String::as_str)
                    .chain(in_scope.iter().copied())
                    .find(|param| signature.ret_idents.iter().any(|ident| ident == param))
                    .map(str::to_string),
                ret: signature.ret,
            }
        };
        let Some(head) = lexemes.get(j) else {
            items.push(unknown(lexeme.line));
            continue;
        };
        let item = match head.text.as_str() {
            "const" => {
                // `pub const fn name` vs `pub const NAME: T`.
                match (lexemes.get(j + 1), lexemes.get(j + 2)) {
                    (Some(next), _) if next.text == "fn" => {
                        lexemes.get(j + 2).map(|n| fn_item(n, j + 2))
                    }
                    (Some(name), _) if is_ident(&name.text) => Some(PubItem {
                        line: lexeme.line,
                        kind: "const".to_string(),
                        name: name.text.clone(),
                        ret: None,
                        ret_type_param: None,
                    }),
                    _ => None,
                }
            }
            "fn" => lexemes
                .get(j + 1)
                .filter(|n| is_ident(&n.text))
                .map(|n| fn_item(n, j + 1)),
            "struct" | "enum" | "union" | "trait" | "type" | "mod" | "static" => lexemes
                .get(j + 1)
                .filter(|n| is_ident(&n.text))
                .map(|n| PubItem {
                    line: lexeme.line,
                    kind: head.text.clone(),
                    name: n.text.clone(),
                    ret: None,
                    ret_type_param: None,
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
                        ret: None,
                        ret_type_param: None,
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
                    ret: None,
                    ret_type_param: None,
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
/// The identifiers [`admission_token_sites`] trips on, sorted.
///
/// **Every entry must name something that exists** — a needle naming nothing can never fire,
/// and a tripwire that cannot fire reports healthy for the same reason a working one does.
/// Until bead `franken_lean-admission-tripwire-needles-unbound-en9q` this list carried
/// `CheckedExpr`, the *expression* typestate of plan §8.2b, which is unimplemented and exists
/// nowhere in the workspace; meanwhile the capability types that DO exist were unnamed. So the
/// only bare needle here could not match, and the ones that could were absent.
///
/// `the_admission_tripwire_names_what_the_kernel_actually_exports`
/// (`tests/real_workspace.rs`) binds this list to `crates/fln-kernel/src/capability.rs` in
/// both directions: a needle naming nothing fails, and a capability type named by no needle
/// fails. Neither direction can be satisfied by editing this list alone.
///
/// Published-result types are deliberately absent — see
/// [`ADMISSION_TOKEN_EXCLUSIONS`].
pub const ADMISSION_TOKENS: &[&str] = &[
    "Admitted",
    "CheckedDecl",
    "Reviewable",
    "fln_checker",
    "fln_kernel",
];

/// Capability-module types deliberately NOT tripwired, each with the reason it is safe.
///
/// A declared, shrinking allowance rather than a silent omission: the binding test requires
/// every `pub` type in the capability module to be either tripwired or listed here, so a new
/// type forces a decision instead of defaulting to uncovered, and a row naming a type that no
/// longer exists fails rather than accumulating.
pub const ADMISSION_TOKEN_EXCLUSIONS: &[(&str, &str)] = &[
    (
        "Published",
        "an outcome REPORT of a publication attempt, not a right to perform one: its arms are \
         Committed, DuplicateName, and BlockCommitted, and none contains the private CheckedDecl \
         seal. It is also a generic identifier, so tripwiring it would buy no admission coverage \
         while adding real false-positive risk in boundary code.",
    ),
    (
        "BlockPublication",
        "the immutable RESULT of an already committed checked block: it carries only the final \
         Environment and published names, never CheckedDecl, Reviewable, or the private seal \
         required to publish another declaration. Receiving it can observe and extend the \
         ordinary environment only through a new kernel admission.",
    ),
];

pub fn admission_token_sites(text: &str) -> Vec<ExportSite> {
    let mut sites = Vec::new();
    for lexeme in rust_lexemes(text) {
        if ADMISSION_TOKENS.contains(&lexeme.text.as_str()) {
            sites.push(ExportSite {
                line: lexeme.line,
                detail: "kernel-admission token in boundary code",
            });
        }
    }
    sites.dedup_by_key(|site| site.line);
    sites
}

/// Recursively collect `#[unsafe(export_name)]`-class sites under `dir`.
///
/// As with [`scan_allow_sites`], a file that cannot be decoded as UTF-8 is appended to
/// `unreadable` and skipped so the caller can report it as an inconclusive input instead
/// of aborting the whole run.
pub fn scan_external_exports(
    dir: &Path,
    rel_prefix: &str,
    out: &mut Vec<LocatedExportSite>,
    unreadable: &mut Vec<String>,
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
            scan_external_exports(&path, &rel, out, unreadable)?;
        } else if file_type.is_file() && name.ends_with(".rs") {
            let Ok(text) = fs::read_to_string(&path) else {
                unreadable.push(rel.clone());
                continue;
            };
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
///
/// A file that cannot be decoded as UTF-8 is appended to `unreadable` and skipped rather
/// than aborting the scan: the caller turns each entry into a typed finding, so an
/// undecodable file inside a boundary crate leaves the run inconclusive instead of either
/// suppressing every other finding or silently passing the ledger discipline.
pub fn scan_allow_sites(
    dir: &Path,
    rel_prefix: &str,
    out: &mut Vec<AllowSite>,
    unreadable: &mut Vec<String>,
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
            scan_allow_sites(&path, &rel, out, unreadable)?;
        } else if file_type.is_file() && name.ends_with(".rs") {
            let Ok(text) = fs::read_to_string(&path) else {
                unreadable.push(rel.clone());
                continue;
            };
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
    fn release_authority_excludes_only_an_exact_top_level_test_tail() {
        let production = "fn release() {}\n";
        let test_tail = "#[cfg(test)]\nmod tests {\n    #[test]\n    fn private_probe() { assert_eq!(1, 1); }\n}\n";
        let source = format!("{production}{test_tail}");
        assert_eq!(release_authority_source(&source), production);

        let trailing_release = format!("{source}fn hidden_after_tests() {{}}\n");
        assert_eq!(
            release_authority_source(&trailing_release),
            trailing_release,
            "a test module that does not own the lexical tail cannot hide later authority"
        );

        let nested = format!("mod outer {{\n{test_tail}}}\n");
        assert_eq!(release_authority_source(&nested), nested);

        let compound = "fn release() {}\n#[cfg(all(test, feature = \"probe\"))]\nmod tests {}\n";
        assert_eq!(release_authority_source(compound), compound);

        let decoy = "const DECOY: &str = \"#[cfg(test)] mod tests { assert_eq!(1, 1); }\";\n";
        assert_eq!(release_authority_source(decoy), decoy);
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
        assert_eq!(
            macro_invocations("assert!(x);\nhidden_policy!(y);\n"),
            vec![
                NamedMacroSite {
                    line: 1,
                    name: "assert".to_string(),
                },
                NamedMacroSite {
                    line: 2,
                    name: "hidden_policy".to_string(),
                },
            ]
        );
        assert!(macro_invocation_lines("include!(\"f.rs\");\n").is_empty());
        assert!(macro_invocation_lines("macro_rules! m { () => {} }\n").is_empty());
        assert_eq!(
            macro_invocations("if !(matches!(x, Y)) {}\n"),
            vec![NamedMacroSite {
                line: 1,
                name: "matches".to_string(),
            }]
        );
        assert_eq!(
            macro_definition_sites("macro_rules! m { () => {} }\n").len(),
            1
        );
        assert_eq!(
            attribute_invocations(
                "#![forbid(unsafe_code)]\n#[cfg(test)]\n#[derive(Debug, Clone)]\nstruct S;\n"
            ),
            vec![
                NamedMacroSite {
                    line: 2,
                    name: "cfg".to_string(),
                },
                NamedMacroSite {
                    line: 3,
                    name: "derive".to_string(),
                },
                NamedMacroSite {
                    line: 1,
                    name: "forbid".to_string(),
                },
            ]
        );
        assert_eq!(
            derive_macro_invocations("#[derive(Debug, Clone)]\nstruct S;\n"),
            vec![
                NamedMacroSite {
                    line: 1,
                    name: "Clone".to_string(),
                },
                NamedMacroSite {
                    line: 1,
                    name: "Debug".to_string(),
                },
            ]
        );
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
                name: "launder".into(),
                ret: None,
                ret_type_param: None
            }]
        );
        // An associated type of a caller-chosen parameter is still the caller's
        // choice: it can pick `T` so that `T::Out` is a checked declaration.
        assert_eq!(
            public_item_sites("pub fn generic<T: Trait>(x: T) -> T::Out { x.out() }\n"),
            vec![PubItem {
                line: 1,
                kind: "fn".into(),
                name: "generic".into(),
                ret: Some("T::Out".into()),
                ret_type_param: Some("T".into())
            }]
        );
        assert_eq!(
            public_item_sites("pub struct Laundered(pub(crate) u8);\n"),
            vec![PubItem {
                line: 1,
                kind: "struct".into(),
                name: "Laundered".into(),
                ret: None,
                ret_type_param: None
            }]
        );
        // Modifier chains, consts, fields, and single-leaf re-exports.
        assert_eq!(
            public_item_sites("pub unsafe extern \"C\" fn s() {}\n"),
            vec![PubItem {
                line: 1,
                kind: "fn".into(),
                name: "s".into(),
                ret: None,
                ret_type_param: None
            }]
        );
        assert_eq!(
            public_item_sites("pub const fn cf() {}\npub const K: usize = 1;\n"),
            vec![
                PubItem {
                    line: 1,
                    kind: "fn".into(),
                    name: "cf".into(),
                    ret: None,
                    ret_type_param: None
                },
                PubItem {
                    line: 2,
                    kind: "const".into(),
                    name: "K".into(),
                    ret: None,
                    ret_type_param: None
                }
            ]
        );
        assert_eq!(
            public_item_sites("struct H { pub rc: i32 }\n"),
            vec![PubItem {
                line: 1,
                kind: "field".into(),
                name: "rc".into(),
                ret: None,
                ret_type_param: None
            }]
        );
        assert_eq!(
            public_item_sites("pub use rc::Header;\npub use shadow::enable as shadow_enable;\n"),
            vec![
                PubItem {
                    line: 1,
                    kind: "use".into(),
                    name: "Header".into(),
                    ret: None,
                    ret_type_param: None
                },
                PubItem {
                    line: 2,
                    kind: "use".into(),
                    name: "shadow_enable".into(),
                    ret: None,
                    ret_type_param: None
                }
            ]
        );
        // Scope. A lifetime and a const parameter bind nothing launderable; an
        // enclosing `impl<T>` binds exactly as the fn's own list does; and
        // `impl Foo<u8>` is a USE of `u8`, not a binder, so `-> u8` stays clean.
        let param = |src: &str| public_item_sites(src)[0].ret_type_param.clone();
        assert_eq!(
            param("pub fn f<'a, const N: usize>(x: &'a [u8; N]) -> u8 { 0 }\n"),
            None
        );
        assert_eq!(param("pub fn f<T>(x: T) -> Tally { 0 }\n"), None);
        assert_eq!(
            param("pub fn f<T>(x: T) -> Vec<T> { vec![x] }\n"),
            Some("T".into())
        );
        assert_eq!(
            param("impl<T> Holder<T> { pub fn get(&self) -> T { todo!() } }\n"),
            Some("T".into())
        );
        assert_eq!(
            param("impl Holder<u8> { pub fn get(&self) -> u8 { 0 } }\n"),
            None
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
        // A LIVE capability type, not a planned one: `CheckedDecl` is declared in
        // crates/fln-kernel/src/capability.rs, so this needle can actually fire on real
        // boundary source. The previous version of this assertion used `CheckedExpr`, which
        // exists nowhere in the workspace — a self-consistent test of a needle that could
        // never match anything (bead franken_lean-admission-tripwire-needles-unbound-en9q).
        assert_eq!(admission_token_sites("type T = CheckedDecl;\n").len(), 1);
        assert_eq!(admission_token_sites("fn f(r: Reviewable) {}\n").len(), 1);
        assert_eq!(
            admission_token_sites("fn f() -> Admitted { todo!() }\n").len(),
            1
        );
        // The excluded type stays untripwired, and this fails if someone adds it silently.
        assert!(admission_token_sites("fn f() -> Published { todo!() }\n").is_empty());
        assert!(admission_token_sites("fn clean() {}\n").is_empty());
        // Macro-generated symbol exports.
        let none: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let lean_x: std::collections::BTreeSet<String> =
            std::iter::once("lean_x".to_string()).collect();
        assert_eq!(
            expanded_surface_violations("#[no_mangle]\nextern \"C\" fn s() {}\n", &none).len(),
            1
        );
        // export_name: undeclared symbol fails; a declared symbol is admitted
        // (the C export covenant, FLN-STRUCT-026); a declared symbol under a
        // no_mangle attr still fails (exports must name their symbol).
        assert_eq!(
            expanded_surface_violations("#[unsafe(export_name = \"lean_x\")]\nfn s() {}\n", &none)
                .len(),
            1
        );
        assert!(
            expanded_surface_violations(
                "#[unsafe(export_name = \"lean_x\")]\nfn s() {}\n",
                &lean_x
            )
            .is_empty()
        );
        // Unextractable symbol (split across lines) fails closed even when
        // some symbol is declared.
        assert_eq!(
            expanded_surface_violations(
                "#[unsafe(export_name =\n\"lean_x\")]\nfn s() {}\n",
                &lean_x
            )
            .len(),
            1
        );
        assert_eq!(
            expanded_surface_violations("#[macro_export]\nmacro_rules! m { () => {} }\n", &none)
                .len(),
            1
        );
        // Symbol definition below the attribute layer.
        assert_eq!(
            expanded_surface_violations("::core::arch::global_asm!(\".globl lean_x\");\n", &none)
                .len(),
            1
        );
        // The clean expanded shape: restricted visibility, impls, expressions.
        assert!(
            expanded_surface_violations(
                "pub(crate) fn f() {}\nimpl Drop for X { fn drop(&mut self) {} }\n",
                &none
            )
            .is_empty()
        );
        // A doc string mentioning export_name never counts (strings are
        // dropped by the lexer), and the extractor parses real sites.
        assert!(
            expanded_surface_violations(
                "#[doc = \"use export_name = \\\"x\\\" here\"]\nfn d() {}\n",
                &none
            )
            .is_empty()
        );
        let sites = export_name_attr_sites("#[unsafe(export_name = \"lean_y\")]\nfn s() {}\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].symbol.as_deref(), Some("lean_y"));
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
