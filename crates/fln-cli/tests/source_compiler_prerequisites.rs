//! The installed Lean front door must compile ordinary definitions even when
//! the source never evaluates them. Reference controls use the fixed pin.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

const PIN: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";
const POLY: &str = "universe u\ndef ident (A : Type u) (x : A) : A := x\n";
const ENUM: &str = "inductive E where\n | a\n | b\n";
const MARKERS: &str = "axiom lcAny : Type\naxiom lcErased : Type\n";

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "fln-compiler-prerequisites-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn source(&self, label: &str, source: &str) -> PathBuf {
        let path = self.0.join(format!("{label}.lean"));
        std::fs::write(&path, source).unwrap();
        path
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn reference() -> Option<&'static Path> {
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    REFERENCE
        .get_or_init(|| {
            let binary = std::env::var_os("FLN_REFERENCE_LEAN")
                .map(PathBuf::from)
                .or_else(|| {
                    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from)?;
                    Some(library.parent()?.parent()?.join("bin/lean"))
                })
                .filter(|path| path.is_file());
            assert!(
                binary.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "set FLN_REFERENCE_LEAN or FLN_REFERENCE_LIB to the pinned Reference",
            );
            if let Some(binary) = &binary {
                let hash = Command::new(binary).arg("--githash").output().unwrap();
                assert!(hash.status.success(), "{hash:?}");
                assert_eq!(String::from_utf8(hash.stdout).unwrap().trim(), PIN);
            }
            binary
        })
        .as_deref()
}

fn run(binary: &Path, source: &Path) -> Output {
    Command::new(binary)
        .arg(source)
        .env_remove("LEAN_PATH")
        .env("FLN_IMPORT_REUSE_DIR", source.parent().unwrap().join("records"))
        .output()
        .unwrap()
}

fn assert_result(output: &Output, code: i32, marker: Option<&str>, source: &str) {
    assert_eq!(output.status.code(), Some(code), "{source}\n{output:?}");
    if let Some(marker) = marker {
        let diagnostic = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        assert!(diagnostic.contains("Unknown constant"), "{source}\n{diagnostic}");
        assert!(diagnostic.contains(marker), "{source}\n{diagnostic}");
    }
}

#[test]
fn prelude_compiler_signatures_match_the_pinned_acceptance_controls() {
    let directory = Directory::new();
    let cases = [
        ("poly", format!("prelude\n{POLY}"), 1, Some("lcAny")),
        (
            "any_only",
            format!("prelude\naxiom lcAny : Type\n{POLY}"),
            1,
            Some("lcErased"),
        ),
        (
            "erased_only",
            format!("prelude\naxiom lcErased : Type\n{POLY}"),
            1,
            Some("lcAny"),
        ),
        ("both", format!("prelude\n{MARKERS}{POLY}"), 0, None),
        (
            "extern_missing",
            "prelude\nuniverse u\n@[extern \"poly_ext\"] axiom ext (A : Type u) (x : A) : A\n".to_owned(),
            1,
            Some("lcErased"),
        ),
        (
            "extern_markers",
            format!("prelude\n{MARKERS}universe u\n@[extern \"poly_ext\"] axiom ext (A : Type u) (x : A) : A\n"),
            0,
            None,
        ),
        (
            "noncomputable",
            "prelude\nuniverse u\nnoncomputable def ident (A : Type u) (x : A) : A := x\n".to_owned(),
            0,
            None,
        ),
        (
            "noncomputable_section",
            format!("prelude\nnoncomputable section\n{POLY}end\n"),
            0,
            None,
        ),
        (
            "public_noncomputable_section",
            "module\nprelude\nuniverse u\nnoncomputable section\npublic def ident (A : Type u) (x : A) : A := x\nend\n".to_owned(),
            0,
            None,
        ),
        (
            "proof",
            "prelude\ntheorem ident (P : Prop) (x : P) : P := x\n".to_owned(),
            0,
            None,
        ),
        (
            "type",
            "prelude\ndef ident (A : Type) : Type := A\n".to_owned(),
            0,
            None,
        ),
        (
            "concrete",
            format!("prelude\n{ENUM}def ident (e : E) : E := e\n"),
            0,
            None,
        ),
        (
            "unused_type",
            format!("prelude\n{ENUM}def f (A : Type) : E := E.a\n"),
            1,
            Some("lcErased"),
        ),
        (
            "abstract",
            format!("prelude\n{ENUM}axiom A : Type\ndef f (a : A) : E := E.a\n"),
            1,
            Some("lcAny"),
        ),
        (
            "proof_parameter",
            format!("prelude\n{ENUM}axiom P : Prop\ndef f (p : P) : E := E.a\n"),
            1,
            Some("lcErased"),
        ),
        (
            "typeformer_parameter",
            format!("prelude\n{ENUM}def f (g : E → Type) : E := E.a\n"),
            1,
            Some("lcErased"),
        ),
        (
            "ignored_polymorphic",
            format!("prelude\n{ENUM}universe u\ndef f (A : Type u) (x : A) : E := E.a\n"),
            1,
            Some("lcErased"),
        ),
        (
            "nested",
            format!("prelude\n{ENUM}axiom A : Type\ndef f (g : E → A) (e : E) : E := e\n"),
            0,
            None,
        ),
        (
            "body_erased",
            format!("prelude\n{ENUM}def f : E := (fun (A : Type) (x : A) => E.a) E E.a\n"),
            0,
            None,
        ),
        (
            "module",
            "module\nprelude\nuniverse u\npublic def ident (A : Type u) (x : A) : A := x\n".to_owned(),
            1,
            Some("lcAny"),
        ),
    ];
    for (label, source, code, marker) in cases {
        let path = directory.source(label, &source);
        assert_result(
            &run(Path::new(env!("CARGO_BIN_EXE_lean")), &path),
            code,
            marker,
            &source,
        );
        if let Some(reference) = reference() {
            assert_result(&run(reference, &path), code, marker, &source);
        }
    }
}

#[test]
fn a_failed_compilation_publishes_no_requested_artifact() {
    let directory = Directory::new();
    let source = directory.source("Failed", &format!("prelude\n{POLY}"));
    let artifact = directory.0.join("Failed.olean");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("-o")
        .arg(&artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert_result(&output, 1, Some("lcAny"), POLY);
    assert!(!artifact.exists(), "{output:?}");
    assert!(!directory.0.join("Failed.olean.server").exists());
    assert!(!directory.0.join("Failed.olean.private").exists());
}

#[test]
fn a_real_prelude_import_supplies_compiler_markers() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required",
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return;
    };
    assert!(library.join("Init/Prelude.olean").is_file());
    let directory = Directory::new();
    let source = directory.source("Imported", &format!("prelude\nimport Init.Prelude\n{POLY}"));
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&source)
        .env("LEAN_PATH", &library)
        .env("FLN_IMPORT_REUSE_DIR", directory.0.join("records"))
        .output()
        .unwrap();
    assert_result(&output, 0, None, POLY);
}

#[test]
fn unsupported_postponement_stops_before_a_compiler_marker_verdict() {
    let directory = Directory::new();
    let source = directory.source(
        "Postponed",
        "module\nprelude\nset_option compiler.postponeCompile true\nuniverse u\npublic def ident (A : Type u) (x : A) : A := x\n",
    );
    let output = run(Path::new(env!("CARGO_BIN_EXE_lean")), &source);
    assert!(!output.status.success(), "{output:?}");
    let diagnostic = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(diagnostic.contains("compiler.postponeCompile"), "{diagnostic}");
    assert!(!diagnostic.contains("Unknown constant"), "{diagnostic}");
    // The native option remains unsupported. The pin accepts this declaration
    // while postponing compilation, so it must not become a marker rejection.
    if let Some(reference) = reference() {
        assert_result(&run(reference, &source), 0, None, "postponed declaration");
    }
}
