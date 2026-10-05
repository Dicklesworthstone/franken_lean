#![forbid(unsafe_code)]
//! `fln check-olean --continue --progress` killed while a module is still in the
//! council keeps every row that already exists (bead
//! `fln-frontier-oom-abort-w9dx`, "survive a crash").
//!
//! The `decided` lines leave in frontier order, so a row decided early waits
//! behind any slower module before it, and a crash in that window used to lose
//! it. The `settled` line is written the moment the row exists. The run here holds
//! the pinned `Init.Prelude` (seconds in the council) at position 1 and a module
//! whose artifact cannot decode, which is decided at once, at position 2. The
//! process is killed as soon as that module's `settled` line arrives, before any
//! `decided` line can: the verdict must already be on the stream.
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn copy_module(lib: &Path, module: &str, to: &Path, as_module: &str, corrupt: bool) {
    let from = lib.join(module.replace('.', "/"));
    let target = to.join(as_module.replace('.', "/"));
    std::fs::create_dir_all(target.parent().expect("a module path has a parent"))
        .expect("create the fixture's module directory");
    for extension in ["olean", "olean.server", "olean.private"] {
        let mut bytes = std::fs::read(from.with_extension(extension))
            .unwrap_or_else(|error| panic!("read {module}.{extension}: {error}"));
        if corrupt && extension == "olean" {
            // The header stays valid; the object region does not decode.
            let middle = bytes.len() / 2;
            bytes[middle] ^= 0xFF;
            bytes[middle + 1] ^= 0xFF;
        }
        std::fs::write(target.with_extension(extension), bytes)
            .unwrap_or_else(|error| panic!("write {as_module}.{extension}: {error}"));
    }
}

#[test]
fn a_run_killed_with_a_module_in_the_council_keeps_every_settled_row() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("check_olean_progress_crash");
    copy_module(&lib, "Init.Prelude", &dir, "Init.Prelude", false);
    copy_module(&lib, "Init.Coe", &dir, "Zzz.Corrupt", true);

    let mut child = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-olean", "--continue", "--progress", "--jobs", "2"])
        .arg(&dir)
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn fln check-olean");
    let stderr = BufReader::new(child.stderr.take().expect("piped stderr"));
    let mut seen: Vec<String> = Vec::new();
    let mut killed = false;
    let settled_corrupt =
        |line: &String| line.contains("\"event\":\"settled\"") && line.contains("Zzz.Corrupt");
    let prelude_started = |line: &String| {
        line.contains("\"event\":\"started\"")
            && line.contains("\"position\":1,")
            && line.contains("Init.Prelude")
    };
    for line in stderr.lines() {
        seen.push(line.expect("a progress line"));
        // Kill once the corrupt row has settled and Init.Prelude is in the council.
        if seen.iter().any(settled_corrupt) && seen.iter().any(prelude_started) {
            child
                .kill()
                .expect("kill the run with Init.Prelude in the council");
            killed = true;
            break;
        }
    }
    let status = child.wait().expect("reap the killed run");
    assert!(
        killed,
        "the run ended before the corrupt row settled with Init.Prelude in the council: {seen:#?}"
    );
    assert!(
        !status.success(),
        "the run was killed, not finished: {status:?}"
    );
    // Init.Prelude, at position 1, was still in the council, so no `decided`
    // line could have carried the corrupt module's verdict yet.
    assert!(
        !seen
            .iter()
            .any(|line| line.contains("\"event\":\"decided\"")),
        "nothing was decided before the kill: {seen:#?}"
    );
    let settled = seen
        .iter()
        .find(|line| settled_corrupt(line))
        .expect("the corrupt row settled");
    assert!(
        settled.starts_with("{\"schema\":\"fln.check-olean-frontier-progress/2\",\"event\":\"settled\",\"position\":2,\"total\":2,"),
        "the corrupt module settles at its frontier position: {settled}"
    );
    assert!(
        settled.contains("\"verdict\":\"failed\""),
        "the settled row carries the module's verdict: {settled}"
    );
}
