//! The pin syntax corpus (bead `fln-pin-syntax-corpus-7b5b`): the pinned frontend's lossless
//! command trees for every vendored `Init` and `Std` source file, read back by Vellum.
//!
//! The trees come from the stock pin running `scripts/extract/dump_command_syntax.lean
//! --lossless`, which processes each file exactly as `lean FILE` would. They are cached outside
//! the repository, at `$FLN_PIN_SYNTAX_CACHE`, else `$XDG_CACHE_HOME/fln/pin-syntax`, else
//! `$HOME/.cache/fln/pin-syntax`, under `<pin commit>/<producer digest>/<source digest>.dump`, so a
//! changed source, producer or pin never reads a stale dump.
//!
//! Checked in is only `corpus/pin_syntax_manifest.tsv`: per file, the digest of its bytes, its
//! command and message counts, and the digest of its dump (FNV-1a 64, as the upstream suite
//! oracle uses: this guards against drift, not against an adversary). Only
//! `pin_syntax_corpus_against_the_pin` writes it, behind `FLN_PIN_SYNTAX_WRITE=1`, running nothing
//! but the pinned binary. A digest mismatch is drift, never a reason to regenerate.
//!
//! Per commit, without the pin, `every_vendored_init_and_std_source_has_its_manifest_row` holds
//! the population, the source digests and the producer; the reader's own unit tests
//! (`fln_syntax::pin_syntax`) hold the round trip and its refusals on planted dumps. The pinned
//! lane checks every dump against the manifest and asserts `print(read(dump)) == dump` over the
//! whole corpus.
#![forbid(unsafe_code)]

use fln_syntax::pin_syntax::{self, SCHEMA, cache_root, fnv1a};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const SOURCES: &str = "vendor/lean4-src/src";
const MANIFEST: &str = "crates/fln-syntax/tests/corpus/pin_syntax_manifest.tsv";
const PRODUCER: &str = "scripts/extract/dump_command_syntax.lean";
const WORKERS: usize = 8;

fn workspace_root() -> PathBuf {
    // The tree this run was launched from, refused if the binary was compiled in
    // another checkout (bead fln-cross-tree-baked-root-k60n).
    fln_core::checked_workspace_root!()
}

/// The pin's tag and commit, from `SUITE.lock`'s `reference leanprover/lean4` line.
fn pin(root: &Path) -> (String, String) {
    let lock = std::fs::read_to_string(root.join("SUITE.lock")).expect("read SUITE.lock");
    let line = lock
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .expect("SUITE.lock names the reference");
    let field = |key: &str| {
        line.split_whitespace()
            .find_map(|part| part.strip_prefix(key))
            .expect("the reference line carries the field")
            .to_owned()
    };
    (field("tag="), field("commit="))
}

/// Every `.lean` file under `Init/` and `Std/`, and the two root modules, relative to `SOURCES`.
fn population(root: &Path) -> Vec<String> {
    let base = root.join(SOURCES);
    let mut files = Vec::new();
    let mut pending = vec![base.join("Init"), base.join("Std")];
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory).expect("read a source directory") {
            let path = entry.expect("a source entry").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|ext| ext == "lean") {
                files.push(
                    path.strip_prefix(&base)
                        .expect("under the sources")
                        .to_string_lossy()
                        .into_owned(),
                );
            }
        }
    }
    for module in ["Init.lean", "Std.lean"] {
        if base.join(module).is_file() {
            files.push(module.to_owned());
        }
    }
    files.sort();
    files
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    source: u64,
    commands: usize,
    messages: usize,
    dump: u64,
}

/// The manifest: the producer digest its header names, and its rows by file.
fn read_manifest(text: &str) -> Result<(String, BTreeMap<String, Row>), String> {
    let mut producer = None;
    let mut rows = BTreeMap::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("# schema ") {
            let parts: Vec<_> = rest.split(' ').collect();
            match parts.as_slice() {
                [schema, "producer", digest] if *schema == SCHEMA => {
                    producer = Some((*digest).to_owned())
                }
                _ => return Err(format!("a bad schema line: {line}")),
            }
            continue;
        }
        if line.starts_with('#') {
            continue;
        }
        let fields: Vec<_> = line.split('\t').collect();
        let [file, source, commands, messages, dump] = fields.as_slice() else {
            return Err(format!("a malformed row: {line}"));
        };
        let hex = |field: &str| {
            u64::from_str_radix(field, 16)
                .ok()
                .filter(|_| field.len() == 16)
                .ok_or_else(|| format!("a bad digest in: {line}"))
        };
        let count = |field: &str| field.parse().map_err(|_| format!("a bad count in: {line}"));
        let row = Row {
            source: hex(source)?,
            commands: count(commands)?,
            messages: count(messages)?,
            dump: hex(dump)?,
        };
        if rows.insert((*file).to_owned(), row).is_some() {
            return Err(format!("a duplicate row for {file}"));
        }
    }
    Ok((producer.ok_or("the manifest names no producer")?, rows))
}

fn producer_digest(root: &Path) -> String {
    format!(
        "{:016x}",
        fnv1a(&std::fs::read(root.join(PRODUCER)).expect("read the producer"))
    )
}

#[test]
fn every_vendored_init_and_std_source_has_its_manifest_row() {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join(MANIFEST)).expect("read the manifest");
    let (producer, rows) = read_manifest(&text).expect("a well-formed manifest");
    assert_eq!(
        producer,
        producer_digest(&root),
        "the dump producer changed since the manifest was written: run the pinned lane with \
         FLN_PIN_SYNTAX_WRITE=1"
    );
    let files = population(&root);
    assert!(
        files.len() > 1000,
        "a scan this small is broken: {}",
        files.len()
    );
    let mut problems = Vec::new();
    for file in &files {
        let bytes = std::fs::read(root.join(SOURCES).join(file)).expect("read a source");
        match rows.get(file) {
            None => problems.push(format!("{file}: no manifest row")),
            Some(row) if row.source != fnv1a(&bytes) => {
                problems.push(format!("{file}: the vendored bytes changed since its row"))
            }
            Some(_) => {}
        }
    }
    for file in rows.keys() {
        if files.binary_search(file).is_err() {
            problems.push(format!("{file}: a row without a source file"));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn a_malformed_manifest_is_refused() {
    let good = format!(
        "# schema {SCHEMA} producer 0123456789abcdef\nInit.lean\t0123456789abcdef\t3\t0\tfedcba9876543210\n"
    );
    assert!(read_manifest(&good).is_ok());
    for bad in [
        good.replace("producer", "maker"),
        good.replace("\t3\t", "\tthree\t"),
        good.replace("fedcba9876543210", "fedcba"),
        format!("{good}Init.lean\t0123456789abcdef\t3\t0\tfedcba9876543210\n"),
        good.lines().skip(1).collect::<Vec<_>>().join("\n"),
    ] {
        assert!(read_manifest(&bad).is_err(), "{bad}");
    }
}

/// The dump of `file`, from the cache or, when absent, from the pin (then cached).
fn dump_of(
    root: &Path,
    toolchain: &Path,
    cache: &Path,
    file: &str,
    source: &[u8],
) -> Result<String, String> {
    let path = cache.join(format!("{:016x}.dump", fnv1a(source)));
    if let Ok(text) = std::fs::read_to_string(&path) {
        return Ok(text);
    }
    let output = Command::new(toolchain.join("bin/lean"))
        .arg("--run")
        .arg(root.join(PRODUCER))
        .arg(root.join(SOURCES).join(file))
        .arg(toolchain)
        .arg("--lossless")
        .output()
        .map_err(|error| format!("{file}: could not run the pin: {error}"))?;
    let text = String::from_utf8(output.stdout).map_err(|_| format!("{file}: non-UTF-8 dump"))?;
    if !output.status.success() || !text.ends_with('\n') {
        return Err(format!(
            "{file}: the pin's dump failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let temporary = path.with_extension(format!("tmp{}", std::process::id()));
    std::fs::write(&temporary, &text).map_err(|error| format!("{file}: {error}"))?;
    std::fs::rename(&temporary, &path).map_err(|error| format!("{file}: {error}"))?;
    Ok(text)
}

#[ignore = "cost: the pinned frontend over 1,077 Init and Std files (minutes) on first use; an on-demand pin-gated lane (bead fln-pin-syntax-corpus-7b5b); FLN_PIN_SYNTAX_WRITE=1 makes it the manifest's only writer"]
#[test]
fn pin_syntax_corpus_against_the_pin() {
    let root = workspace_root();
    let (tag, commit) = pin(&root);
    let toolchain = std::env::var_os("HOME")
        .map(|home| PathBuf::from(home).join(format!(".elan/toolchains/leanprover--lean4---{tag}")))
        .filter(|toolchain| toolchain.join("bin/lean").is_file());
    let Some(toolchain) = toolchain else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned toolchain is absent"
        );
        eprintln!("SKIP pin_syntax_corpus: the pinned toolchain is absent");
        return;
    };
    let producer = producer_digest(&root);
    let cache = cache_root()
        .expect("a cache directory")
        .join(&commit)
        .join(&producer);
    std::fs::create_dir_all(&cache).expect("create the cache");
    let files = population(&root);
    let next = AtomicUsize::new(0);
    let results = Mutex::new(BTreeMap::new());
    std::thread::scope(|scope| {
        for _ in 0..WORKERS {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(file) = files.get(index) else { break };
                    let source = std::fs::read(root.join(SOURCES).join(file)).expect("read");
                    let result =
                        dump_of(&root, &toolchain, &cache, file, &source).and_then(|dump| {
                            // Each tree is checked on a thread whose stack is not the host's main
                            // one; the reader and printer use explicit stacks.
                            let trees = pin_syntax::read(&dump, &source)
                                .map_err(|error| format!("{file}: {error}"))?;
                            let printed = pin_syntax::print(&trees, &source)
                                .map_err(|error| format!("{file}: {error}"))?;
                            if printed != dump {
                                return Err(format!(
                                    "{file}: print(read(dump)) differs from the dump"
                                ));
                            }
                            Ok(Row {
                                source: fnv1a(&source),
                                commands: trees.commands.len(),
                                messages: trees.messages.len(),
                                dump: fnv1a(dump.as_bytes()),
                            })
                        });
                    results
                        .lock()
                        .expect("results")
                        .insert(file.clone(), result);
                }
            });
        }
    });
    let results = results.into_inner().expect("results");
    let mut problems: Vec<String> = results
        .values()
        .filter_map(|result| result.as_ref().err().cloned())
        .collect();
    let rows: BTreeMap<String, Row> = results
        .into_iter()
        .filter_map(|(file, result)| result.ok().map(|row| (file, row)))
        .collect();
    let commands: usize = rows.values().map(|row| row.commands).sum();
    eprintln!(
        "pin_syntax_corpus: {} files, {commands} commands round-tripped at {commit} (producer {producer})",
        rows.len()
    );
    if std::env::var_os("FLN_PIN_SYNTAX_WRITE").is_some() {
        assert!(problems.is_empty(), "{}", problems.join("\n"));
        let mut text = format!(
            "# Pin syntax corpus manifest (bead fln-pin-syntax-corpus-7b5b): per vendored Init and Std file, the pinned frontend's lossless dump.\n\
             # Written only by pin_syntax_corpus_against_the_pin with FLN_PIN_SYNTAX_WRITE=1, from the pin {tag} ({commit}); never by hand.\n\
             # schema {SCHEMA} producer {producer}\n\
             # file\tsource_fnv1a\tcommands\tmessages\tdump_fnv1a\n"
        );
        for (file, row) in &rows {
            text.push_str(&format!(
                "{file}\t{:016x}\t{}\t{}\t{:016x}\n",
                row.source, row.commands, row.messages, row.dump
            ));
        }
        std::fs::write(root.join(MANIFEST), text).expect("write the manifest");
        return;
    }
    let text = std::fs::read_to_string(root.join(MANIFEST)).expect("read the manifest");
    let (recorded_producer, recorded) = read_manifest(&text).expect("a well-formed manifest");
    if recorded_producer != producer {
        problems.push("the manifest names another producer".to_owned());
    }
    for (file, row) in &rows {
        if recorded.get(file) != Some(row) {
            problems.push(format!(
                "{file}: the pin's dump no longer matches its manifest row; re-record only for a \
                 pin, vendor or producer change"
            ));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}
