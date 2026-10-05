//! The `reuse-verified` import posture at the real front doors (bead `fln-uyuz`):
//! `fln check-source` and `lake build` over the pinned Reference's own `.olean`
//! files, with the real on-disk record store and the real binary as checker.
//! Nothing here is mocked: every refusal is planted in real bytes on disk.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// A scratch directory removed when the test passes.
struct Scratch(PathBuf);
impl Scratch {
    fn new(tag: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-import-reuse-{tag}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) -> PathBuf {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, bytes).unwrap();
        path
    }
    fn files(&self, relative: &str) -> Vec<String> {
        let mut names: Vec<String> = std::fs::read_dir(self.0.join(relative))
            .map(|entries| {
                entries
                    .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
                    .collect()
            })
            .unwrap_or_default();
        names.sort();
        names
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
}

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("HOME").map(PathBuf::from).map(|home| {
        home.join(".elan/toolchains")
            .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
            .join("lib/lean")
    });
    let present = lib
        .as_ref()
        .is_some_and(|lib| lib.join("Init/Prelude.olean").is_file());
    assert!(
        present || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    if std::env::var_os("LEAN_PATH").is_some() {
        return None;
    }
    lib.filter(|_| present)
}

/// The value of a JSON string member `"name":"…"`, the first one in `text`.
fn member<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    let start = text.find(&format!("\"{name}\":\""))? + name.len() + 4;
    let end = text[start..].find('"')? + start;
    Some(&text[start..end])
}

/// The report with its `"oleanImports":{…}` object removed: everything that must not
/// depend on how the imports were obtained.
fn without_imports(text: &str) -> String {
    let start = text
        .find(",\"oleanImports\":{")
        .expect("an oleanImports object");
    let end = text[start..].find('}').expect("its end") + start + 1;
    format!("{}{}", &text[..start], &text[end..])
}

struct Run {
    output: Output,
    seconds: f64,
}
impl Run {
    fn stdout(&self) -> String {
        assert!(self.output.status.success(), "{:?}", self.output);
        String::from_utf8(self.output.stdout.clone()).unwrap()
    }
}

fn check_source(binary: &Path, entry: &Path, store: &Path, extra: &[&str]) -> Run {
    check_source_with(binary, entry, store, extra, None)
}

fn check_source_with(
    binary: &Path,
    entry: &Path,
    store: &Path,
    extra: &[&str],
    lean_path: Option<&Path>,
) -> Run {
    let mut command = Command::new(binary);
    command
        .args(["check-source", "--json"])
        .args(extra)
        .arg(entry)
        .env("FLN_IMPORT_REUSE_DIR", store);
    if let Some(lean_path) = lean_path {
        command.env("LEAN_PATH", lean_path);
    }
    let started = Instant::now();
    let output = command.output().expect("run fln check-source");
    Run {
        output,
        seconds: started.elapsed().as_secs_f64(),
    }
}

const PRELUDE_SOURCE: &str = "prelude\nimport Init.Prelude\ntheorem keep (P : Prop) (h : P) : P := h\ntheorem use_nat (n : Nat) : n = n := rfl\n";

/// The positive half at `check-source`: the first run admits the real `Init.Prelude`
/// closure through the council and records it; the second rebuilds it from the
/// record, says so with the same closure key, and reports everything else identically.
#[test]
fn check_source_reuses_its_recorded_prelude_closure_and_says_so() {
    let Some(_) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    };
    let scratch = Scratch::new("check-source");
    let entry = scratch.write("src/Main.lean", PRELUDE_SOURCE);
    let store = scratch.0.join("records");
    let fln = Path::new(env!("CARGO_BIN_EXE_fln"));

    let first = check_source(fln, &entry, &store, &[]);
    let first_out = first.stdout();
    assert!(
        first_out.contains(
            "\"oleanImports\":{\"trust\":\"reuse-verified\",\"admission\":\"council\",\"closureKey\":\""
        ),
        "{first_out}"
    );
    assert_eq!(member(&first_out, "record"), Some("absent"), "{first_out}");
    assert_eq!(
        member(&first_out, "recordWrite"),
        Some("stored"),
        "{first_out}"
    );
    let key = member(&first_out, "closureKey").unwrap().to_owned();
    assert_eq!(scratch.files("records"), [format!("{key}.record")]);

    let second = check_source(fln, &entry, &store, &[]);
    let second_out = second.stdout();
    assert!(
        second_out.contains(&format!(
            "\"oleanImports\":{{\"trust\":\"reuse-verified\",\"admission\":\"reused\",\"closureKey\":\"{key}\",\"record\":\"hit\",\"modules\":1,\"declarations\":2314}}"
        )),
        "{second_out}"
    );
    assert_eq!(without_imports(&first_out), without_imports(&second_out));
    assert!(second_out.contains("\"theorems\":2"), "{second_out}");
    eprintln!(
        "check-source Init.Prelude: council {:.2} s, reuse-verified {:.2} s",
        first.seconds, second.seconds
    );

    // `--import-posture recheck` admits again, names no key or record, and never
    // writes the store.
    let recheck = check_source(fln, &entry, &store, &["--import-posture", "recheck"]);
    let recheck_out = recheck.stdout();
    assert!(
        recheck_out.contains(
            "\"oleanImports\":{\"trust\":\"recheck\",\"admission\":\"council\",\"modules\":1,"
        ),
        "{recheck_out}"
    );
    assert_eq!(without_imports(&first_out), without_imports(&recheck_out));
    assert_eq!(scratch.files("records"), [format!("{key}.record")]);
}

/// The planted negatives at `check-source`, on a private copy of the real Prelude:
///
/// * one changed byte (inside a docstring, so every declaration is unchanged and only
///   the key can tell) misses the record and the council admits again;
/// * a different checker binary (the same executable with bytes appended, so a
///   different identity) misses too, and a record of the first binary planted under
///   the second binary's key is refused as another checker's.
#[test]
fn a_changed_olean_byte_or_another_checker_forces_readmission() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    };
    let scratch = Scratch::new("negatives");
    let entry = scratch.write("src/Main.lean", PRELUDE_SOURCE);
    let store = scratch.0.join("records");
    let search = scratch.0.join("lib");
    let parts = ["olean", "olean.server", "olean.private"];
    let original: Vec<Vec<u8>> = parts
        .iter()
        .map(|part| std::fs::read(lib.join("Init/Prelude").with_extension(part)).unwrap())
        .collect();
    let install = |bytes: &[Vec<u8>]| {
        for (part, bytes) in parts.iter().zip(bytes) {
            scratch.write(&format!("lib/Init/Prelude.{part}"), bytes);
        }
    };
    install(&original);
    let fln = PathBuf::from(env!("CARGO_BIN_EXE_fln"));
    let run = |binary: &Path| check_source_with(binary, &entry, &store, &[], Some(&search));

    let first = run(&fln).stdout();
    assert_eq!(member(&first, "admission"), Some("council"), "{first}");
    assert_eq!(member(&first, "recordWrite"), Some("stored"), "{first}");
    let key = member(&first, "closureKey").unwrap().to_owned();
    assert_eq!(member(&run(&fln).stdout(), "record"), Some("hit"));

    // One byte of the server part's `id` docstring.
    let mut changed = original.clone();
    let needle = b"The identity function";
    let at = changed[1]
        .windows(needle.len())
        .position(|window| window == needle)
        .expect("the Prelude's `id` docstring")
        + needle.len()
        - 1;
    changed[1][at] = b'X';
    install(&changed);
    let flipped = run(&fln).stdout();
    assert_eq!(member(&flipped, "admission"), Some("council"), "{flipped}");
    assert_eq!(member(&flipped, "record"), Some("absent"), "{flipped}");
    assert_ne!(
        member(&flipped, "closureKey"),
        Some(key.as_str()),
        "{flipped}"
    );
    // The declarations did not change, so the council's roots are the original ones:
    // the key, not a root, is what refused the record.
    assert_eq!(without_imports(&first), without_imports(&flipped));
    install(&original);

    // Another checker identity: the same program with bytes appended.
    // `fs::copy` carries the executable bits; the appended bytes change only the identity.
    let other = scratch.0.join("bin/fln-other");
    std::fs::create_dir_all(other.parent().unwrap()).unwrap();
    std::fs::copy(&fln, &other).unwrap();
    std::io::Write::write_all(
        &mut std::fs::OpenOptions::new()
            .append(true)
            .open(&other)
            .unwrap(),
        b"\0fln-uyuz another checker identity\0",
    )
    .unwrap();
    let elsewhere = run(&other).stdout();
    assert_eq!(member(&elsewhere, "record"), Some("absent"), "{elsewhere}");
    assert_eq!(
        member(&elsewhere, "admission"),
        Some("council"),
        "{elsewhere}"
    );
    let other_key = member(&elsewhere, "closureKey").unwrap().to_owned();
    assert_ne!(other_key, key);

    // The first binary's record, planted where the second binary looks.
    std::fs::copy(
        store.join(format!("{key}.record")),
        store.join(format!("{other_key}.record")),
    )
    .unwrap();
    let planted = run(&other).stdout();
    assert_eq!(
        member(&planted, "record"),
        Some("refused:checker-identity"),
        "{planted}"
    );
    assert_eq!(member(&planted, "admission"), Some("council"), "{planted}");
    assert_eq!(member(&planted, "recordWrite"), Some("stored"), "{planted}");
    assert_eq!(member(&run(&other).stdout(), "record"), Some("hit"));
}

/// `lake build` takes the same posture for the external closure it imports, and its
/// report names it per closure.
#[test]
fn lake_build_reuses_its_recorded_import_closure_and_says_so() {
    let Some(_) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    };
    let scratch = Scratch::new("lake");
    scratch.write(
        "pkg/lakefile.toml",
        "name = \"reuse\"\n[[lean_lib]]\nname = \"Lib\"\nroots = [\"Lib\"]\n",
    );
    scratch.write("pkg/Lib.lean", PRELUDE_SOURCE);
    let store = scratch.0.join("records");
    let build = || {
        let started = Instant::now();
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(scratch.0.join("pkg"))
            .args(["--json", "build", "+Lib:olean"])
            .env("FLN_IMPORT_REUSE_DIR", &store)
            .output()
            .unwrap();
        Run {
            output,
            seconds: started.elapsed().as_secs_f64(),
        }
    };
    let first = build();
    let first_out = first.stdout();
    assert!(
        first_out.contains("\"import_posture\":\"reuse-verified\",\"imports\":[{\"trust\":\"reuse-verified\",\"admission\":\"council\",\"closureKey\":\""),
        "{first_out}"
    );
    assert_eq!(
        member(&first_out, "recordWrite"),
        Some("stored"),
        "{first_out}"
    );
    let key = member(&first_out, "closureKey").unwrap().to_owned();
    let artifact = scratch.0.join("pkg/.lake/build/lib/lean/Lib.olean");
    let first_artifact = std::fs::read(&artifact).unwrap();

    let second = build();
    let second_out = second.stdout();
    assert!(
        second_out.contains(&format!(
            "\"imports\":[{{\"trust\":\"reuse-verified\",\"admission\":\"reused\",\"closureKey\":\"{key}\",\"record\":\"hit\"}}]"
        )),
        "{second_out}"
    );
    assert_eq!(
        std::fs::read(&artifact).unwrap(),
        first_artifact,
        "the module built against the reused closure is byte-identical"
    );
    eprintln!(
        "lake build over Init.Prelude: council {:.2} s, reuse-verified {:.2} s",
        first.seconds, second.seconds
    );
}

/// The G1 door has no posture: `check-olean` refuses the option outright and reports
/// `recheck`, and `trust-producer` is refused at the doors that do take one.
#[test]
fn check_olean_has_no_posture_and_trust_producer_is_refused() {
    let fln = env!("CARGO_BIN_EXE_fln");
    let refused = Command::new(fln)
        .args([
            "check-olean",
            "--json",
            "--import-posture",
            "reuse-verified",
            "x.olean",
        ])
        .output()
        .unwrap();
    assert!(!refused.status.success(), "{refused:?}");
    let message = String::from_utf8_lossy(&refused.stderr).into_owned()
        + &String::from_utf8_lossy(&refused.stdout);
    assert!(message.contains("--import-posture"), "{message}");

    let producer = Command::new(fln)
        .args([
            "check-source",
            "--import-posture",
            "trust-producer",
            "x.lean",
        ])
        .output()
        .unwrap();
    assert!(!producer.status.success(), "{producer:?}");
    let message = String::from_utf8_lossy(&producer.stderr).into_owned();
    assert!(
        message.contains("trust-producer") && message.contains("not implemented"),
        "{message}"
    );

    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    };
    let scratch = Scratch::new("check-olean");
    let store = scratch.0.join("records");
    let checked = Command::new(fln)
        .args(["check-olean", "--json"])
        .arg(lib.join("Init/Prelude.olean"))
        .env("FLN_IMPORT_REUSE_DIR", &store)
        .output()
        .unwrap();
    let out = String::from_utf8(checked.stdout.clone()).unwrap();
    assert!(checked.status.success(), "{checked:?}");
    assert!(
        out.contains("\"outcome\":\"complete\",\"authority\":true,\"trust\":\"recheck\","),
        "{out}"
    );
    assert!(
        !store.exists(),
        "check-olean must not touch the record store"
    );
}
