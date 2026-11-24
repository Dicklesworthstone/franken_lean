//! Batch dependency discovery for `lean --deps-json`.
//! The pinned `Lean.Elab.ParseImportsFast` used for this API has its own
//! grammar: it reads keyword prefixes, stops at documentation comments, and
//! accepts `public import all` for discovery. No declaration is elaborated.
use super::{MultiplexerOutput, json_string, read_bounded, read_bounded_from};
use fln_core::name::Name;
use fln_core::name::identifier::{is_id_first, is_id_rest, to_identifier_string};
use std::io::Read;
use std::path::{Path, PathBuf};

pub(super) const MAX_FILES: usize = 65_536;
const MAX_OUTPUT_BYTES: usize = 64 * 1024 * 1024;
const MAX_PATH_LIST_BYTES: usize = 16 * 1024 * 1024;

struct Header<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> Header<'a> {
    fn rest(&self) -> &'a str {
        &self.source[self.offset..]
    }

    fn trivia(&mut self) -> Result<(), &'static str> {
        loop {
            let rest = self.rest();
            if rest.starts_with('\t') {
                return Err("tabs are not allowed; please configure your editor to expand them");
            }
            if rest.starts_with([' ', '\r', '\n']) {
                self.offset += 1;
            } else if rest.starts_with("--") {
                self.offset += rest.find('\n').unwrap_or(rest.len());
            } else if rest.starts_with("/-") && !rest.starts_with("/--") && !rest.starts_with("/-!")
            {
                self.offset += 2;
                let mut depth = 1;
                while depth > 0 {
                    let rest = self.rest();
                    let Some(index) = rest.find(['-', '/']) else {
                        self.offset = self.source.len();
                        return Err("unterminated comment");
                    };
                    self.offset += index;
                    if self.rest().starts_with("-/") {
                        self.offset += 2;
                        depth -= 1;
                    } else if self.rest().starts_with("/-") {
                        self.offset += 2;
                        depth += 1;
                    } else {
                        self.offset += 1;
                    }
                }
            } else {
                return Ok(());
            }
        }
    }

    fn keyword(&mut self, keyword: &str) -> Result<bool, &'static str> {
        if self.rest().starts_with(keyword) {
            self.offset += keyword.len();
            self.trivia()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn module_name(&mut self) -> Result<String, &'static str> {
        let mut name = Name::anonymous();
        let mut depth = 0usize;
        loop {
            let rest = self.rest();
            let Some(first) = rest.chars().next() else {
                return Err("unexpected end of input");
            };
            let component = if let Some(escaped) = rest.strip_prefix('«') {
                let Some(end) = escaped.find('»') else {
                    self.offset = self.source.len();
                    return Err("unterminated identifier escape");
                };
                self.offset += '«'.len_utf8() + end + '»'.len_utf8();
                &escaped[..end]
            } else if is_id_first(first) {
                let end = rest.find(|c| !is_id_rest(c)).unwrap_or(rest.len());
                self.offset += end;
                &rest[..end]
            } else {
                return Err("expected identifier");
            };
            depth += 1;
            if depth > fln::SourceModuleLimits::default().max_name_depth {
                return Err("module name exceeds the component limit");
            }
            name = Name::str(name, component);
            if !self
                .rest()
                .strip_prefix('.')
                .and_then(|tail| tail.chars().next())
                .is_some_and(|c| c == '«' || is_id_first(c))
            {
                break;
            }
            self.offset += 1;
        }
        to_identifier_string(&name, MAX_OUTPUT_BYTES)
            .map_err(|_| "module name exceeds the output limit")
    }

    fn scan(&mut self) -> Result<String, &'static str> {
        self.trivia()?;
        let is_module = self.keyword("module")?;
        let mut imports = Vec::new();
        if !self.keyword("prelude")? {
            imports.push(import("Init", false, true, false));
            imports.push(import("Init", false, true, true));
        }
        let mut size = 0usize;
        loop {
            let start = self.offset;
            // `public? meta? import` is atomic in the fast parser: failure
            // before this prefix is complete starts the command body.
            let prefix = (|| {
                let public = self.keyword("public")?;
                let meta = self.keyword("meta")?;
                Ok::<_, &'static str>((public, meta, self.keyword("import")?))
            })();
            let Ok((public, meta, true)) = prefix else {
                break;
            };
            let all = self.keyword("all")?;
            let module = self.module_name()?;
            self.trivia()?;
            if !is_module && (public || meta || all) {
                self.offset = start;
                return Err("cannot use 'public', 'meta', or 'all' without 'module'");
            }
            let row = import(&module, all, public || !is_module, meta);
            size += row.len() + 1;
            if size > MAX_OUTPUT_BYTES {
                return Err("module imports exceed the output limit");
            }
            imports.push(row);
        }
        Ok(format!(
            r#"{{"imports":[{}],"isModule":{is_module}}}"#,
            imports.join(",")
        ))
    }
}

fn import(module: &str, all: bool, exported: bool, meta: bool) -> String {
    format!(
        r#"{{"importAll":{all},"isExported":{exported},"isMeta":{meta},"module":{}}}"#,
        json_string(module)
    )
}

fn result(path: &Path, max_bytes: usize) -> Result<String, String> {
    let bytes = read_bounded(path, max_bytes, "dependency source").map_err(|e| e.to_string())?;
    let source =
        std::str::from_utf8(&bytes).map_err(|_| format!("{}: invalid UTF-8", path.display()))?;
    let mut header = Header { source, offset: 0 };
    header.scan().map_err(|error| {
        let prefix = &source[..header.offset];
        let line = 1 + prefix.bytes().filter(|byte| *byte == b'\n').count();
        let column = prefix
            .rsplit('\n')
            .next()
            .unwrap_or_default()
            .chars()
            .count();
        format!("{}:{line}:{column}: {error}", path.display())
    })
}

pub(super) fn run(
    mut paths: Vec<PathBuf>,
    stdin: bool,
    input: Option<&mut dyn Read>,
    max_bytes: usize,
) -> MultiplexerOutput {
    if stdin {
        let Some(input) = input else {
            return MultiplexerOutput::failure(
                "lean: --stdin requires an input handle\n".into(),
                2,
            );
        };
        let bytes = match read_bounded_from(input, MAX_PATH_LIST_BYTES, "dependency path list") {
            Ok(bytes) => bytes,
            Err(e) => return MultiplexerOutput::failure(format!("lean: {e}\n"), e.exit_code()),
        };
        let Ok(list) = std::str::from_utf8(&bytes) else {
            return MultiplexerOutput::failure(
                "lean: dependency path list is not UTF-8\n".into(),
                1,
            );
        };
        paths = list
            .lines()
            .take(MAX_FILES + 1)
            .map(PathBuf::from)
            .collect();
    }
    if paths.len() > MAX_FILES {
        return MultiplexerOutput::failure("lean: too many dependency source paths\n".into(), 3);
    }
    let mut output = String::from("{\"imports\":[");
    for (index, path) in paths.iter().enumerate() {
        let row = match result(path, max_bytes) {
            Ok(header) => format!(r#"{{"errors":[],"result":{header}}}"#),
            Err(error) => format!(r#"{{"errors":[{}]}}"#, json_string(&error)),
        };
        if output.len().saturating_add(row.len() + 4) > MAX_OUTPUT_BYTES {
            return MultiplexerOutput::failure(
                "lean: dependency batch exceeds the output limit\n".into(),
                3,
            );
        }
        if index > 0 {
            output.push(',');
        }
        output.push_str(&row);
    }
    output.push_str("]}\n");
    MultiplexerOutput::success(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(source: &str) -> Result<String, &'static str> {
        Header { source, offset: 0 }.scan()
    }

    #[test]
    fn batch_dependency_headers_preserve_the_pins_import_phases_and_order() {
        let rows = [
            import("Init", false, true, false),
            import("Init", false, true, true),
            import("A.«B.C»", true, true, true),
            import("A", false, false, false),
            import("A", false, false, false),
        ];
        let source = "-- comment\r\nmodule /- x /- y -/ z -/\npublic meta import all A.«B.C»\nimport A import A\ndef unfinished := \"";
        assert_eq!(
            scan(source).unwrap(),
            format!(r#"{{"imports":[{}],"isModule":true}}"#, rows.join(","))
        );
        assert_eq!(
            scan("prelude\n/-! Docs -/\nimport Ignored").unwrap(),
            r#"{"imports":[],"isModule":false}"#
        );
        assert_eq!(
            scan("public import A"),
            Err("cannot use 'public', 'meta', or 'all' without 'module'")
        );
        assert_eq!(scan("import «oops"), Err("unterminated identifier escape"));
    }

    #[test]
    fn batch_dependency_headers_use_filename_lines_and_keep_per_file_failures() {
        let file = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../vendor/lean4-src/src/Init/Prelude.lean");
        let path = file.to_str().unwrap();
        let missing = file.with_extension("missing");
        let argv = [
            path.into(),
            missing.clone().into_os_string(),
            path.into(),
            "--src-deps".into(),
            "--deps-json".into(),
        ];
        let output = crate::run_lean(argv);
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        let ok = r#"{"errors":[],"result":{"imports":[],"isModule":true}}"#;
        assert_eq!(output.stdout.matches(ok).count(), 2, "{}", output.stdout);
        assert!(output.stdout.contains(&format!(r#"{ok},{{"errors":["#)));
        let lines = format!("{path}\r\n{}\n{path}", missing.display());
        let stdin = crate::run_lean_with_input(
            [
                "--stdin".into(),
                "ignored-when-reading-filenames-from-stdin".into(),
                "--deps-json".into(),
            ],
            &mut lines.as_bytes(),
        );
        assert_eq!(stdin.stdout, output.stdout);
        assert_eq!(stdin.exit_code, 0);
        assert_ne!(crate::run_lean(["-N".into()]).exit_code, 0);
        assert_eq!(
            crate::run_lean(["--deps-json".into()]).stdout,
            "{\"imports\":[]}\n"
        );
    }
}
