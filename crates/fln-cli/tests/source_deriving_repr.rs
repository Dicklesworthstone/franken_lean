//! Installed source checking and execution of recursive/indexed Repr printers.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Data/Repr.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference Repr library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference Repr library absent");
    }
    lib
}

fn invoke(verb: &str, source: &Path, lib: &Path, work: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([verb, "--json", "--jobs=1"])
        .arg(source)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", work.join("imports"))
        .output()
        .expect("run the installed native source command")
}

fn completed(output: &Output) -> &str {
    assert!(
        output.status.success(),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(output.stderr.is_empty());
    let json = std::str::from_utf8(&output.stdout).unwrap();
    assert!(json.contains("\"outcome\":\"complete\""), "{json}");
    json
}

#[test]
fn installed_recursive_and_indexed_printers_check_execute_and_recover() {
    let Some(lib) = pinned_lib() else { return };
    let work = std::env::temp_dir().join(format!(
        "fln-derived-repr-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&work).unwrap();
    let source = work.join("Main.lean");
    let definitions = "prelude\nimport Init.Data.Repr\n\
        inductive Chain (A : Type) where\n\
          | nil\n  | cons (head : A) (tail : Chain A)\n\
        deriving Repr\n\
        inductive Vec (A : Type) : Nat -> Type where\n\
          | nil : Vec A 0\n\
          | cons {n : Nat} (head : A) (tail : Vec A n) : Vec A (n + 1)\n\
        deriving Repr\n\
        def chainPrinter : Repr (Chain Nat) := inferInstance\n\
        def vecPrinter {n : Nat} : Repr (Vec Nat n) := inferInstance\n";
    std::fs::write(&source, definitions).unwrap();
    completed(&invoke("check-source", &source, &lib, &work));

    let program = format!(
        "{definitions}\n\
         #eval reprStr (Chain.cons 7 (Chain.cons 9 Chain.nil))\n\
         #eval reprStr (Vec.cons 7 Vec.nil)\n"
    );
    for suffix in [
        "",
        "inductive Bad where\n | leaf\n | node (child : Bad)\nderiving Repr, UnknownHandler\n",
        "",
    ] {
        std::fs::write(&source, format!("{program}{suffix}")).unwrap();
        let output = invoke("run", &source, &lib, &work);
        if suffix.is_empty() {
            let json = completed(&output);
            for value in [
                "Chain.cons 7 (Chain.cons 9 (Chain.nil))",
                "Vec.cons 7 (Vec.nil)",
            ] {
                assert!(
                    json.contains(&format!("\"kind\":\"string\",\"value\":\"{value}\"")),
                    "{json}",
                );
            }
        } else {
            assert!(!output.status.success());
            assert!(
                output.stdout.is_empty(),
                "earlier evaluations escaped the failed batch"
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("unsupported deriving handler"), "{stderr}");
        }
    }
}
