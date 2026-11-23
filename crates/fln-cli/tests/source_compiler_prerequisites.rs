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
        .arg("-j1")
        .arg(source)
        .env_remove("LEAN_PATH")
        .env(
            "FLN_IMPORT_REUSE_DIR",
            source.parent().unwrap().join("records"),
        )
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
        assert!(
            diagnostic.contains("Unknown constant"),
            "{source}\n{diagnostic}"
        );
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
            "irreducible_alias",
            format!("prelude\n{ENUM}@[irreducible] def Data : Type := E\ndef ident (x : Data) : Data := x\n"),
            0,
            None,
        ),
        (
            "unsafe_alias",
            format!("prelude\n{ENUM}unsafe def Data : Type := E\nunsafe def ident (x : Data) : Data := x\n"),
            0,
            None,
        ),
        (
            "unsafe_callback_alias",
            format!("prelude\n{ENUM}unsafe def Callback : Type := E → E\nunsafe def ignore (f : Callback) : E := E.a\n"),
            0,
            None,
        ),
        (
            "unsafe_returned_callback_alias",
            format!("prelude\n{ENUM}unsafe def Callback : Type := E → E\nunsafe def ident (f : Callback) : Callback := f\n"),
            0,
            None,
        ),
        (
            "unsafe_generic_alias",
            format!("prelude\n{ENUM}universe u\nunsafe def Carrier (A : Type u) : Type u := A\nunsafe def ident (x : Carrier E) : Carrier E := x\n"),
            0,
            None,
        ),
        (
            "unsafe_proposition_alias",
            format!("prelude\n{ENUM}axiom Q : Prop\nunsafe def P : Prop := Q\nunsafe def ident (p : P) : P := p\n"),
            0,
            None,
        ),
        (
            "unsafe_predicate_alias",
            format!("prelude\n{ENUM}axiom Q : Prop\nunsafe def Predicate : E → Prop := fun _ => Q\nunsafe def ident (e : E) (p : Predicate e) : Predicate e := p\n"),
            0,
            None,
        ),
        (
            "unsafe_typeformer_alias",
            format!("prelude\n{ENUM}unsafe def Predicate : Type 1 := E → Type\nunsafe def ignore (p : Predicate) : E := E.a\n"),
            1,
            Some("lcErased"),
        ),
        (
            "unsafe_typeformer_alias_erased",
            format!("prelude\n{ENUM}axiom lcErased : Type\nunsafe def Predicate : Type 1 := E → Type\nunsafe def ignore (p : Predicate) : E := E.a\n"),
            0,
            None,
        ),
        (
            "unsafe_abstract_alias",
            format!("prelude\n{ENUM}axiom A : Type\nunsafe def Data : Type := A\nunsafe def ident (x : Data) : Data := x\n"),
            1,
            Some("lcAny"),
        ),
        (
            "unsafe_abstract_alias_any",
            format!("prelude\n{ENUM}axiom lcAny : Type\naxiom A : Type\nunsafe def Data : Type := A\nunsafe def ident (x : Data) : Data := x\n"),
            0,
            None,
        ),
        (
            "opaque_alias",
            format!("prelude\n{ENUM}opaque Data : Type := E\ndef ident (x : Data) : Data := x\n"),
            1,
            Some("lcAny"),
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
fn macro_inline_runtime_dependencies_match_the_pin() {
    let directory = Directory::new();
    let cases = [
        ("deferred", "@[macro_inline] def f : E := value\n", 0),
        ("ordinary", "def f : E := value\n", 1),
        (
            "called",
            "@[macro_inline] def f : E := value\ndef g : E := f\n",
            1,
        ),
        (
            "enabled_last",
            "@[noinline, macro_inline] def f : E := value\n",
            0,
        ),
        (
            "disabled_last",
            "@[macro_inline, noinline] def f : E := value\n",
            1,
        ),
        (
            "discarded_argument",
            "@[macro_inline] def discard (_ : E) : E := E.a\ndef use : E := discard value\n",
            0,
        ),
        (
            "used_argument",
            "@[macro_inline] def keep (x : E) : E := x\ndef use : E := keep value\n",
            1,
        ),
    ];
    for (label, declaration, code) in cases {
        let source = format!("prelude\n{ENUM}axiom value : E\n{declaration}");
        let path = directory.source(label, &source);
        for binary in std::iter::once(Path::new(env!("CARGO_BIN_EXE_lean"))).chain(reference()) {
            let output = run(binary, &path);
            assert_result(&output, code, None, &source);
            if code != 0 {
                let diagnostic = format!(
                    "{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                );
                assert!(
                    diagnostic.contains("noncomputable"),
                    "{source}\n{diagnostic}"
                );
                assert!(diagnostic.contains("value"), "{source}\n{diagnostic}");
            }
        }
    }
}

#[test]
fn macro_inline_recursors_and_erased_arguments_match_the_pin() {
    let directory = Directory::new();
    let base = "prelude\ninductive N where | zero | succ (n : N)\n";
    let recursor = "N.rec (motive := fun _ => N) N.zero (fun _ ih => ih) n";
    let fold = format!("@[macro_inline] def fold (n : N) : N := {recursor}\n");
    let cases = [
        ("standalone", fold.clone(), None),
        (
            "called",
            format!("{fold}def use (n : N) : N := fold n\n"),
            Some("does not support recursor"),
        ),
        (
            "discarded_outer",
            format!("{fold}@[macro_inline] def discard (_ : N) : N := N.zero\ndef use (n : N) : N := discard (fold n)\n"),
            None,
        ),
        (
            "discarded_inner",
            format!("@[macro_inline] def discard (_ : N) : N := N.zero\n@[macro_inline] def fold (n : N) : N := discard ({recursor})\ndef use (n : N) : N := fold n\n"),
            None,
        ),
        (
            "proof_only",
            format!("{fold}def Proof (n : N) : Prop := (P : N → Prop) → P (fold n) → P (fold n)\n"),
            None,
        ),
        (
            "argument_provenance",
            format!("@[macro_inline] def keep (x : N) : N := x\n@[macro_inline] def fold (n : N) : N := keep ({recursor})\ndef use (n : N) : N := fold n\n"),
            Some("does not support recursor"),
        ),
        (
            "auxiliary",
            "@[macro_inline] def fold (n : N) : N := N.recOn (motive := fun _ => N) n N.zero (fun _ ih => ih)\ndef use (n : N) : N := fold n\n".to_owned(),
            Some("Failed to find LCNF signature"),
        ),
    ];
    for (label, declaration, diagnostic) in cases {
        let source = format!("{base}{declaration}");
        let path = directory.source(label, &source);
        for binary in std::iter::once(Path::new(env!("CARGO_BIN_EXE_lean"))).chain(reference()) {
            let output = run(binary, &path);
            assert_result(&output, i32::from(diagnostic.is_some()), None, &source);
            if let Some(expected) = diagnostic {
                let message = format!(
                    "{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                );
                assert!(message.contains(expected), "{source}\n{message}");
                assert!(message.contains("N.rec"), "{source}\n{message}");
            }
        }
    }
}

#[test]
fn macro_inline_generated_matches_do_not_inherit_discarded_recursors() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required",
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return;
    };
    let reference = reference().expect("the imported Prelude controls require the pinned oracle");
    let directory = Directory::new();
    let base = "prelude\nimport Init.Prelude\ninductive MacroChoice where | first | second\n@[macro_inline] def macroMatch (_ignored : MacroChoice) (e : MacroChoice) : MacroChoice :=\n match e with\n | .first => .second\n | .second => .first\n";
    let recursor =
        "MacroChoice.rec (motive := fun _ => MacroChoice) MacroChoice.first MacroChoice.second e";
    for (label, caller) in [
        (
            "generated",
            "def macroCaller (e : MacroChoice) : MacroChoice := macroMatch e e\n".to_owned(),
        ),
        (
            "discarded",
            format!(
                "@[macro_inline] def macroExplicit (e : MacroChoice) : MacroChoice := macroMatch ({recursor}) e\ndef macroCaller (e : MacroChoice) : MacroChoice := macroExplicit e\n"
            ),
        ),
    ] {
        let source = format!("{base}{caller}");
        let path = directory.source(label, &source);
        for binary in [Path::new(env!("CARGO_BIN_EXE_lean")), reference] {
            let output = Command::new(binary)
                .arg("-j1")
                .arg(&path)
                .env("LEAN_PATH", &library)
                .env("FLN_IMPORT_REUSE_DIR", directory.0.join("records"))
                .output()
                .unwrap();
            assert_result(&output, 0, None, &source);
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
    assert!(
        diagnostic.contains("compiler.postponeCompile"),
        "{diagnostic}"
    );
    assert!(!diagnostic.contains("Unknown constant"), "{diagnostic}");
    // The native option remains unsupported. The pin accepts this declaration
    // while postponing compilation, so it must not become a marker rejection.
    if let Some(reference) = reference() {
        assert_result(&run(reference, &source), 0, None, "postponed declaration");
    }
}
