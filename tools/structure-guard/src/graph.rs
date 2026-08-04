//! Parser and model for `ci/WORKSPACE_GRAPH.txt` (grammar documented in that file).

use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CrateKind {
    Ordinary,
    UnsafeBoundary,
    Tool,
}

impl CrateKind {
    pub fn as_str(self) -> &'static str {
        match self {
            CrateKind::Ordinary => "ordinary",
            CrateKind::UnsafeBoundary => "unsafe-boundary",
            CrateKind::Tool => "tool",
        }
    }
}

#[derive(Debug, Clone)]
pub struct CrateDecl {
    pub name: String,
    /// Layering rank; `None` for tool crates, which sit outside the product layering.
    pub rank: Option<u32>,
    pub kind: CrateKind,
}

/// Exact crate name, or a prefix pattern when it ends with `*` (e.g. `fln-unsafe-*`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern(String);

impl Pattern {
    pub fn new(s: &str) -> Pattern {
        Pattern(s.to_string())
    }

    pub fn matches(&self, name: &str) -> bool {
        match self.0.strip_suffix('*') {
            Some(prefix) => name.starts_with(prefix),
            None => name == self.0,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Default)]
pub struct GraphFile {
    pub crates: BTreeMap<String, CrateDecl>,
    pub edges: Vec<(String, String)>,
    /// `prohibit A ->* B`: no transitive dependency path from A-matching to B-matching.
    pub prohibits: Vec<(Pattern, Pattern)>,
    /// `allow-direct C = a, b`: exhaustive allowlist over ALL direct deps of C.
    pub allow_direct: BTreeMap<String, Vec<String>>,
    /// `covenant C max-loc=N`: line-count covenant over `crates/C/src/**/*.rs`.
    pub covenants: BTreeMap<String, usize>,
    /// `suite-dep P`: external package allowed (path-only) under the closed universe.
    pub suite_deps: Vec<String>,
}

fn valid_name(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
}

fn valid_pattern(s: &str) -> bool {
    match s.strip_suffix('*') {
        Some(prefix) => valid_name(prefix),
        None => valid_name(s),
    }
}

pub fn parse(text: &str) -> Result<GraphFile, String> {
    let mut g = GraphFile::default();
    let mut saw_schema = false;
    let mut edges = BTreeSet::new();
    let mut prohibits = BTreeSet::new();
    let mut suite_deps = BTreeSet::new();

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
        let err = |msg: &str| format!("WORKSPACE_GRAPH.txt:{lineno}: {msg}: `{line}`");

        if !saw_schema {
            if line == "schema fln-workspace-graph/1" {
                saw_schema = true;
                continue;
            }
            return Err(err(
                "first directive must be `schema fln-workspace-graph/1`",
            ));
        }

        let tokens: Vec<&str> = line.split_whitespace().collect();
        match tokens[0] {
            "crate" => {
                if tokens.len() < 3 {
                    return Err(err("expected `crate <name> [rank=<n>] kind=<kind>`"));
                }
                let name = tokens[1];
                if !valid_name(name) {
                    return Err(err("invalid crate name"));
                }
                let mut rank: Option<u32> = None;
                let mut kind: Option<CrateKind> = None;
                for kv in &tokens[2..] {
                    if let Some(v) = kv.strip_prefix("rank=") {
                        if rank.is_some() {
                            return Err(err("duplicate rank attribute"));
                        }
                        rank = Some(
                            v.parse::<u32>()
                                .map_err(|_| err("rank must be a non-negative integer"))?,
                        );
                    } else if let Some(v) = kv.strip_prefix("kind=") {
                        if kind.is_some() {
                            return Err(err("duplicate kind attribute"));
                        }
                        kind = Some(match v {
                            "ordinary" => CrateKind::Ordinary,
                            "unsafe-boundary" => CrateKind::UnsafeBoundary,
                            "tool" => CrateKind::Tool,
                            _ => return Err(err("kind must be ordinary|unsafe-boundary|tool")),
                        });
                    } else {
                        return Err(err("unknown crate attribute"));
                    }
                }
                let kind = kind.ok_or_else(|| err("missing kind="))?;
                match (kind, rank) {
                    (CrateKind::Tool, Some(_)) => {
                        return Err(err("tool crates carry no rank"));
                    }
                    (CrateKind::Tool, None) => {}
                    (_, None) => return Err(err("product crates require rank=")),
                    (_, Some(_)) => {}
                }
                if g.crates
                    .insert(
                        name.to_string(),
                        CrateDecl {
                            name: name.to_string(),
                            rank,
                            kind,
                        },
                    )
                    .is_some()
                {
                    return Err(err("duplicate crate declaration"));
                }
            }
            "edge" => {
                if tokens.len() != 4 || tokens[2] != "->" {
                    return Err(err("expected `edge <from> -> <to>`"));
                }
                if !valid_name(tokens[1]) || !valid_name(tokens[3]) {
                    return Err(err("edge endpoints must be valid crate names"));
                }
                let edge = (tokens[1].to_string(), tokens[3].to_string());
                if !edges.insert(edge.clone()) {
                    return Err(err("duplicate edge declaration"));
                }
                g.edges.push(edge);
            }
            "prohibit" => {
                if tokens.len() != 4 || tokens[2] != "->*" {
                    return Err(err("expected `prohibit <pat> ->* <pat>`"));
                }
                if !valid_pattern(tokens[1]) || !valid_pattern(tokens[3]) {
                    return Err(err(
                        "prohibition endpoints must be valid exact or suffix-* patterns",
                    ));
                }
                if !prohibits.insert((tokens[1].to_string(), tokens[3].to_string())) {
                    return Err(err("duplicate prohibition declaration"));
                }
                g.prohibits
                    .push((Pattern::new(tokens[1]), Pattern::new(tokens[3])));
            }
            "allow-direct" => {
                // allow-direct <crate> = a, b, c   (list may be empty)
                let rest = line
                    .strip_prefix("allow-direct")
                    .expect("directive matched")
                    .trim();
                let (name, list) = rest
                    .split_once('=')
                    .ok_or_else(|| err("expected `allow-direct <crate> = <deps>`"))?;
                let name = name.trim();
                if !valid_name(name) {
                    return Err(err("invalid crate name"));
                }
                // The empty allowlist is expressed by an empty right-hand side and by
                // nothing else. Filtering empty fields out would silently normalise a
                // leading, doubled, or trailing comma, so the reviewed text and the
                // parsed covenant could disagree about what was acknowledged.
                let deps: Vec<String> = if list.trim().is_empty() {
                    Vec::new()
                } else {
                    let fields: Vec<&str> = list.split(',').map(str::trim).collect();
                    if fields.iter().any(|field| field.is_empty()) {
                        return Err(err(
                            "allow-direct list has an empty entry; leading, doubled, and trailing commas are not accepted (write `= ` for the empty allowlist)",
                        ));
                    }
                    fields.iter().map(|field| field.to_string()).collect()
                };
                if deps.iter().any(|dep| !valid_name(dep)) {
                    return Err(err("allow-direct entries must be valid crate names"));
                }
                if deps.iter().collect::<BTreeSet<_>>().len() != deps.len() {
                    return Err(err("duplicate allow-direct entry"));
                }
                if g.allow_direct.insert(name.to_string(), deps).is_some() {
                    return Err(err("duplicate allow-direct declaration"));
                }
            }
            "covenant" => {
                if tokens.len() != 3 || !valid_name(tokens[1]) {
                    return Err(err("expected `covenant <crate> max-loc=<n>`"));
                }
                let limit = tokens[2]
                    .strip_prefix("max-loc=")
                    .and_then(|v| v.parse::<usize>().ok())
                    .ok_or_else(|| err("expected max-loc=<n>"))?;
                if g.covenants.insert(tokens[1].to_string(), limit).is_some() {
                    return Err(err("duplicate covenant"));
                }
            }
            "suite-dep" => {
                if tokens.len() != 2 || !valid_name(tokens[1]) {
                    return Err(err("expected `suite-dep <package>`"));
                }
                if !suite_deps.insert(tokens[1].to_string()) {
                    return Err(err("duplicate suite-dep declaration"));
                }
                g.suite_deps.push(tokens[1].to_string());
            }
            _ => return Err(err("unknown directive")),
        }
    }

    if !saw_schema {
        return Err("WORKSPACE_GRAPH.txt: missing schema line".to_string());
    }
    Ok(g)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pattern_exact_and_prefix() {
        assert!(Pattern::new("fln-kernel").matches("fln-kernel"));
        assert!(!Pattern::new("fln-kernel").matches("fln-kernel2"));
        assert!(Pattern::new("fln-unsafe-*").matches("fln-unsafe-abi"));
        assert!(!Pattern::new("fln-unsafe-*").matches("fln-rt"));
    }

    #[test]
    fn parses_minimal_file() {
        let g = parse(
            "schema fln-workspace-graph/1\n\
             crate fln-core rank=0 kind=ordinary\n\
             crate structure-guard kind=tool\n\
             edge fln-rt -> fln-core\n\
             prohibit fln-unsafe-* ->* fln-kernel\n\
             allow-direct fln-kernel = fln-core, fln-hash\n\
             covenant fln-kernel max-loc=12000\n\
             suite-dep asupersync\n",
        )
        .expect("parses");
        assert_eq!(g.crates.len(), 2);
        assert_eq!(g.edges, vec![("fln-rt".into(), "fln-core".into())]);
        assert_eq!(g.prohibits.len(), 1);
        assert_eq!(g.allow_direct["fln-kernel"], vec!["fln-core", "fln-hash"]);
        assert_eq!(g.covenants["fln-kernel"], 12000);
        assert_eq!(g.suite_deps, vec!["asupersync"]);
    }

    #[test]
    fn rejects_missing_schema_and_unknown_directives() {
        assert!(parse("crate x rank=0 kind=ordinary\n").is_err());
        assert!(parse("schema fln-workspace-graph/1\nfrobnicate x\n").is_err());
        assert!(parse("schema fln-workspace-graph/1\ncrate t kind=tool rank=3\n").is_err());
        assert!(parse("schema fln-workspace-graph/1\ncrate x kind=ordinary\n").is_err());
        let dup = "schema fln-workspace-graph/1\n\
                   crate a rank=0 kind=ordinary\ncrate a rank=1 kind=ordinary\n";
        assert!(parse(dup).is_err());
    }

    #[test]
    fn rejects_ambiguous_or_malformed_graph_directives() {
        let schema = "schema fln-workspace-graph/1\n";
        for directive in [
            "crate a rank=0 rank=1 kind=ordinary",
            "crate a rank=0 kind=ordinary kind=ordinary",
            "edge bad/name -> good",
            "edge good -> bad/name",
            "prohibit * ->* good",
            "prohibit good*bad ->* good",
            "allow-direct good = valid, bad/name",
            "allow-direct good = same, same",
            "covenant bad/name max-loc=1",
        ] {
            assert!(
                parse(&format!("{schema}{directive}\n")).is_err(),
                "accepted {directive}"
            );
        }

        for duplicated in [
            "edge a -> b\nedge a -> b",
            "prohibit a ->* b\nprohibit a ->* b",
            "suite-dep asupersync\nsuite-dep asupersync",
        ] {
            assert!(
                parse(&format!("{schema}{duplicated}\n")).is_err(),
                "accepted duplicate directives: {duplicated}"
            );
        }
    }

    #[test]
    fn comments_and_empty_allowlists() {
        let g = parse(
            "# leading comment\nschema fln-workspace-graph/1\n\
             crate a rank=0 kind=ordinary # trailing\n\
             allow-direct a =\n",
        )
        .expect("parses");
        assert!(g.allow_direct["a"].is_empty());
    }

    /// An empty field inside an `allow-direct` list is ambiguous reviewed text: the
    /// covenant is exhaustive, so a comma that acknowledges nothing must fail the parse
    /// rather than be normalised away.
    #[test]
    fn rejects_empty_allow_direct_entries_but_keeps_the_empty_list() {
        let schema = "schema fln-workspace-graph/1\ncrate a rank=0 kind=ordinary\n";
        for ambiguous in [
            "allow-direct a = , b",    // leading comma
            "allow-direct a = b,, c",  // doubled comma
            "allow-direct a = b,",     // trailing comma
            "allow-direct a = ,",      // comma-only list
            "allow-direct a = b, , c", // whitespace-only field
            "allow-direct a = ,,",     // repeated empty fields
        ] {
            assert!(
                parse(&format!("{schema}{ambiguous}\n")).is_err(),
                "accepted ambiguous allow-direct list: {ambiguous}"
            );
        }

        // Recovery: the legal forms still parse, and whitespace around real entries is
        // still insignificant.
        let empty = parse(&format!("{schema}allow-direct a =   \n")).expect("empty list parses");
        assert!(empty.allow_direct["a"].is_empty());
        let listed =
            parse(&format!("{schema}allow-direct a =  b ,  c \n")).expect("spaced list parses");
        assert_eq!(listed.allow_direct["a"], vec!["b", "c"]);
    }
}
