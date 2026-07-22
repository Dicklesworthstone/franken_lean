//! Minimal parser for this workspace's constrained Cargo.toml style.
//!
//! The guard does not embed a general TOML parser (the universe is closed, D1); it
//! parses exactly the uniform manifest shape the workspace uses and reports anything
//! else as a finding rather than guessing. Supported: `[package]` with `name`/`edition`,
//! the three dependency sections with single-line entries, and `[features]`. Custom
//! target roots, build scripts, renamed packages, and inherited dependencies are rejected:
//! every one of those shapes can make Cargo compile a graph different from the one the
//! structural guard inspected.

use std::collections::BTreeSet;

#[derive(Debug)]
pub struct Dep {
    pub name: String,
    /// Section the dependency was declared in (`dependencies`, `dev-dependencies`,
    /// `build-dependencies`). All sections are held to the same closed-universe rule
    /// until SUITE.lock introduces per-policy tracking (D1).
    pub section: String,
    /// Exact path from a `path = "..."` key. `None` means a registry/version form.
    pub path: Option<String>,
}

#[derive(Debug)]
pub struct Manifest {
    pub name: String,
    pub edition: String,
    pub deps: Vec<Dep>,
}

const DEP_SECTIONS: [&str; 3] = ["dependencies", "dev-dependencies", "build-dependencies"];

fn unquote(v: &str) -> Option<&str> {
    let inner = v.strip_prefix('"')?.strip_suffix('"')?;
    // The current manifest contract deliberately has no TOML escape processing. Failing
    // closed is safer than comparing an unexpanded path against the filesystem.
    (!inner.contains('\\')).then_some(inner)
}

fn strip_comment(raw: &str) -> Result<&str, &'static str> {
    let mut quoted = false;
    let mut escaped = false;
    for (idx, ch) in raw.char_indices() {
        if quoted {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                quoted = false;
            }
        } else if ch == '"' {
            quoted = true;
        } else if ch == '#' {
            return Ok(&raw[..idx]);
        }
    }
    if quoted {
        Err("unterminated quoted string")
    } else {
        Ok(raw)
    }
}

fn split_table_fields(inner: &str) -> Result<Vec<&str>, &'static str> {
    let mut fields = Vec::new();
    let mut start = 0;
    let mut quoted = false;
    let mut escaped = false;
    let mut square_depth = 0_u32;
    for (idx, ch) in inner.char_indices() {
        if quoted {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                quoted = false;
            }
            continue;
        }
        match ch {
            '"' => quoted = true,
            '[' => square_depth = square_depth.saturating_add(1),
            ']' => {
                square_depth = square_depth
                    .checked_sub(1)
                    .ok_or("unbalanced dependency array")?;
            }
            ',' if square_depth == 0 => {
                fields.push(inner[start..idx].trim());
                start = idx + ch.len_utf8();
            }
            '{' | '}' => return Err("nested dependency tables are not supported"),
            _ => {}
        }
    }
    if quoted || square_depth != 0 {
        return Err("unterminated dependency value");
    }
    fields.push(inner[start..].trim());
    Ok(fields)
}

fn string_array(value: &str) -> Result<Vec<String>, &'static str> {
    let inner = value
        .strip_prefix('[')
        .and_then(|v| v.strip_suffix(']'))
        .ok_or("value must be a one-line array")?;
    let fields = split_table_fields(inner)?;
    let mut values = Vec::new();
    let mut seen = BTreeSet::new();
    for (idx, field) in fields.iter().enumerate() {
        if field.is_empty() {
            if idx + 1 == fields.len() {
                continue; // TOML permits one trailing comma.
            }
            return Err("array contains an empty element");
        }
        let value = unquote(field).ok_or("array entries must be quoted strings")?;
        if value.is_empty() {
            return Err("array entries must be non-empty strings");
        }
        if !seen.insert(value) {
            return Err("array contains a duplicate entry");
        }
        values.push(value.to_string());
    }
    Ok(values)
}

fn dependency_path(value: &str) -> Result<Option<String>, &'static str> {
    if unquote(value).is_some() {
        return Ok(None);
    }
    let Some(inner) = value.strip_prefix('{').and_then(|v| v.strip_suffix('}')) else {
        return Err("dependency must be a quoted version or one-line inline table");
    };
    let mut path: Option<String> = None;
    let mut seen = BTreeSet::new();
    for field in split_table_fields(inner)? {
        if field.is_empty() {
            continue;
        }
        let (key, raw_value) = field
            .split_once('=')
            .ok_or("dependency table field must be `key = value`")?;
        let key = key.trim();
        if !seen.insert(key) {
            return Err("duplicate dependency table key");
        }
        match key {
            "path" => {
                path = Some(
                    unquote(raw_value.trim())
                        .ok_or("dependency path must be an unescaped quoted string")?
                        .to_string(),
                );
            }
            // These keys alter compilation but not the package source identity. Parse
            // their complete constrained shapes so malformed TOML cannot be accepted by
            // the guard and interpreted differently by Cargo.
            "features" => {
                string_array(raw_value.trim())?;
            }
            "default-features" | "optional" => match raw_value.trim() {
                "true" | "false" => {}
                _ => return Err("dependency boolean must be exactly true or false"),
            },
            // Renames and alternate sources defeat name-based graph comparison.
            "package" | "git" | "registry" | "version" | "workspace" | "branch" | "tag" | "rev" => {
                return Err("renamed, inherited, registry, or git dependencies are forbidden");
            }
            _ => return Err("unsupported dependency table key"),
        }
    }
    Ok(path)
}

pub fn parse_workspace_members(text: &str, display_path: &str) -> Result<Vec<String>, String> {
    let mut in_workspace = false;
    let mut saw_workspace = false;
    let mut members: Option<Vec<String>> = None;
    let mut resolver: Option<String> = None;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = strip_comment(raw)
            .map_err(|message| format!("{display_path}:{lineno}: {message}"))?
            .trim();
        if line.is_empty() {
            continue;
        }
        let err = |msg: &str| format!("{display_path}:{lineno}: {msg}: `{line}`");
        if line.starts_with('[') {
            if line != "[workspace]" {
                return Err(err(
                    "only the constrained `[workspace]` root section is supported",
                ));
            }
            if saw_workspace {
                return Err(err("duplicate `[workspace]` section"));
            }
            saw_workspace = true;
            in_workspace = true;
            continue;
        }
        if !in_workspace {
            return Err(err("content before `[workspace]`"));
        }
        let (key, value) = line
            .split_once('=')
            .ok_or_else(|| err("expected `key = value`"))?;
        match key.trim() {
            "resolver" => {
                if resolver.is_some() {
                    return Err(err("duplicate workspace.resolver key"));
                }
                resolver = Some(
                    unquote(value.trim())
                        .ok_or_else(|| err("resolver must be a quoted string"))?
                        .to_string(),
                );
            }
            "members" => {
                if members.is_some() {
                    return Err(err("duplicate workspace.members key"));
                }
                members = Some(string_array(value.trim()).map_err(&err)?);
            }
            _ => return Err(err("unsupported root workspace key")),
        }
    }
    if resolver.as_deref() != Some("3") {
        return Err(format!(
            "{display_path}: workspace resolver must be exactly `3`"
        ));
    }
    members.ok_or_else(|| format!("{display_path}: missing workspace.members"))
}

pub fn parse(text: &str, display_path: &str) -> Result<Manifest, String> {
    let mut name: Option<String> = None;
    let mut edition: Option<String> = None;
    let mut deps: Vec<Dep> = Vec::new();
    let mut section: Option<String> = None;
    let mut seen_sections = BTreeSet::new();
    let mut package_keys = BTreeSet::new();
    let mut dependency_keys = BTreeSet::new();
    let mut feature_keys = BTreeSet::new();

    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = strip_comment(raw)
            .map_err(|message| format!("{display_path}:{lineno}: {message}"))?
            .trim();
        if line.is_empty() {
            continue;
        }
        let err = |msg: &str| format!("{display_path}:{lineno}: {msg}: `{line}`");

        if line.starts_with('[') {
            if line.starts_with("[[") {
                return Err(err("custom Cargo targets are not supported"));
            }
            let inner = line
                .strip_prefix('[')
                .and_then(|v| v.strip_suffix(']'))
                .ok_or_else(|| err("malformed section header"))?
                .to_string();
            let known =
                inner == "package" || DEP_SECTIONS.contains(&inner.as_str()) || inner == "features";
            if !known {
                // Anything unrecognized that could smuggle dependencies (target-specific
                // tables, patch/replace) is rejected, not skipped.
                return Err(err("unsupported manifest section"));
            }
            if !seen_sections.insert(inner.clone()) {
                return Err(err("duplicate manifest section"));
            }
            section = Some(inner);
            continue;
        }

        match section.as_deref() {
            Some("package") => {
                if let Some((k, v)) = line.split_once('=') {
                    let (k, v) = (k.trim(), v.trim());
                    if !package_keys.insert(k.to_string()) {
                        return Err(err("duplicate package key"));
                    }
                    match k {
                        "name" => {
                            name = Some(
                                unquote(v)
                                    .ok_or_else(|| err("name must be a quoted string"))?
                                    .to_string(),
                            );
                        }
                        "edition" => {
                            edition = Some(
                                unquote(v)
                                    .ok_or_else(|| err("edition must be a quoted string"))?
                                    .to_string(),
                            );
                        }
                        "build" | "autobins" | "autolib" | "autoexamples" | "autotests"
                        | "autobenches" | "links" => {
                            return Err(err("custom targets and build scripts are forbidden"));
                        }
                        _ => {} // version, license, publish, …
                    }
                } else {
                    return Err(err("expected `key = value`"));
                }
            }
            Some(s) if DEP_SECTIONS.contains(&s) => {
                let (key, value) = line
                    .split_once('=')
                    .ok_or_else(|| err("expected `<dep> = <spec>`"))?;
                let dep_name = key.trim().to_string();
                if dep_name.is_empty()
                    || !dep_name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
                {
                    return Err(err("invalid dependency name"));
                }
                if !dependency_keys.insert((s.to_string(), dep_name.clone())) {
                    return Err(err("duplicate dependency key in section"));
                }
                let value = value.trim();
                let path = dependency_path(value).map_err(&err)?;
                deps.push(Dep {
                    name: dep_name,
                    section: s.to_string(),
                    path,
                });
            }
            Some("features") => {
                let (key, value) = line
                    .split_once('=')
                    .ok_or_else(|| err("expected `<feature> = [<entries>]`"))?;
                let feature = key.trim();
                if feature.is_empty()
                    || !feature
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
                {
                    return Err(err("invalid feature name"));
                }
                if !feature_keys.insert(feature.to_string()) {
                    return Err(err("duplicate feature key"));
                }
                string_array(value.trim()).map_err(&err)?;
            }
            Some(_) => return Err(err("unsupported manifest content")),
            None => return Err(err("content before any section header")),
        }
    }

    Ok(Manifest {
        name: name.ok_or_else(|| format!("{display_path}: missing package.name"))?,
        edition: edition.ok_or_else(|| format!("{display_path}: missing package.edition"))?,
        deps,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const OK: &str = "[package]\nname = \"fln-core\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[dependencies]\n";

    #[test]
    fn parses_stub_manifest() {
        let m = parse(OK, "t").expect("parses");
        assert_eq!(m.name, "fln-core");
        assert_eq!(m.edition, "2024");
        assert!(m.deps.is_empty());
    }

    #[test]
    fn parses_path_and_version_deps() {
        let text = format!(
            "{OK}fln-core = {{ path = \"../fln-core\" }}\nserde = \"1\"\n\n[dev-dependencies]\nfln-hash = {{ path = \"../fln-hash\" }}\n"
        );
        let m = parse(&text, "t").expect("parses");
        assert_eq!(m.deps.len(), 3);
        assert_eq!(m.deps[0].path.as_deref(), Some("../fln-core"));
        assert!(m.deps[1].path.is_none());
        assert_eq!(m.deps[2].section, "dev-dependencies");
    }

    #[test]
    fn rejects_unknown_sections_and_workspace_inheritance() {
        assert!(parse("[patch.crates-io]\nx = \"1\"\n", "t").is_err());
        assert!(parse("[target.'cfg(unix)'.dependencies]\nlibc = \"1\"\n", "t").is_err());
        let ws = format!("{OK}serde.workspace = true\n");
        assert!(parse(&ws, "t").is_err());
    }

    #[test]
    fn features_section_is_validated_without_creating_dependency_edges() {
        let text = format!("{OK}\n[features]\niron = []\nfrontier = [\"iron\", \"dep:fln-jit\"]\n");
        let m = parse(&text, "t").expect("parses");
        assert!(m.deps.is_empty());

        let malformed = format!("{OK}\n[features]\niron = [\"ok\",, \"bad\"]\n");
        assert!(parse(&malformed, "t").is_err());
        let duplicate = format!("{OK}\n[features]\niron = [\"same\", \"same\"]\n");
        assert!(parse(&duplicate, "t").is_err());
    }

    #[test]
    fn dependency_path_is_a_key_not_a_substring() {
        let fake = format!("{OK}asupersync = {{ features = [\"pathfinder\"] }}\n");
        let parsed = parse(&fake, "t").expect("supported feature list parses");
        assert!(parsed.deps[0].path.is_none());

        let renamed = format!("{OK}fln-core = {{ package = \"serde\", path = \"../fln-core\" }}\n");
        assert!(parse(&renamed, "t").is_err());
        let dotted = format!("{OK}fln-core.path = \"../fln-core\"\n");
        assert!(parse(&dotted, "t").is_err());

        let typed = format!(
            "{OK}fln-core = {{ path = \"../fln-core\", optional = true, default-features = false, features = [\"one\", \"two\"] }}\n"
        );
        assert!(parse(&typed, "t").is_ok());
        let malformed_bool =
            format!("{OK}fln-core = {{ path = \"../fln-core\", optional = \"yes\" }}\n");
        assert!(parse(&malformed_bool, "t").is_err());
        let duplicate_feature = format!(
            "{OK}fln-core = {{ path = \"../fln-core\", features = [\"same\", \"same\"] }}\n"
        );
        assert!(parse(&duplicate_feature, "t").is_err());
    }

    #[test]
    fn rejects_custom_target_roots_and_build_scripts() {
        let custom_lib = format!("{OK}\n[lib]\npath = \"elsewhere.rs\"\n");
        assert!(parse(&custom_lib, "t").is_err());
        let build_script = OK.replace(
            "edition = \"2024\"",
            "edition = \"2024\"\nbuild = \"build.rs\"",
        );
        assert!(parse(&build_script, "t").is_err());
    }

    #[test]
    fn parses_constrained_root_workspace() {
        let root = "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n";
        assert_eq!(
            parse_workspace_members(root, "Cargo.toml").expect("parses"),
            vec!["crates/*", "tools/*"]
        );
        assert!(parse_workspace_members(
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/fln-core\"]\nexclude = [\"crates/rogue\"]\n",
            "Cargo.toml"
        )
        .is_err());
    }

    #[test]
    fn rejects_ambiguous_duplicate_workspace_shape() {
        for root in [
            "[workspace]\nresolver = \"3\"\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n",
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\nmembers = [\"crates/*\", \"tools/*\"]\n",
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\", \"crates/*\"]\n",
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n[workspace]\n",
        ] {
            assert!(parse_workspace_members(root, "Cargo.toml").is_err());
        }
    }

    #[test]
    fn rejects_ambiguous_duplicate_package_dependency_and_feature_shape() {
        let duplicate_name = OK.replace(
            "name = \"fln-core\"",
            "name = \"fln-core\"\nname = \"fln-core\"",
        );
        assert!(parse(&duplicate_name, "t").is_err());

        let duplicate_package = format!("{OK}\n[package]\nversion = \"0.0.0\"\n");
        assert!(parse(&duplicate_package, "t").is_err());

        let duplicate_dep =
            format!("{OK}fln-hash = \"1\"\nfln-hash = {{ path = \"../fln-hash\" }}\n");
        assert!(parse(&duplicate_dep, "t").is_err());

        let duplicate_dep_section = format!("{OK}\n[dependencies]\n");
        assert!(parse(&duplicate_dep_section, "t").is_err());

        let duplicate_feature = format!("{OK}\n[features]\niron = []\niron = []\n");
        assert!(parse(&duplicate_feature, "t").is_err());
    }
}
