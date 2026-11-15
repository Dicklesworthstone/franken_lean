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

#[test]
fn installed_direct_record_evaluations_use_checked_printers_without_changing_raw_scalars() {
    let Some(lib) = pinned_lib() else { return };
    let work = std::env::temp_dir().join(format!(
        "fln-direct-repr-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&work).unwrap();
    let source = work.join("Main.lean");
    let prefix = "prelude\nimport Init.Data.Repr\nimport Init.Data.ToString.Basic\n\
        structure Point where\n  x : Nat\n  y : Nat\n  deriving Repr\n\
        structure Label where\n  text : String\n\
        instance : ToString Label := ⟨fun value => value.text⟩\n";
    let program = format!(
        "{prefix}\n\
        #eval Point.mk 3 4\n\
        #eval [Point.mk 3 4, Point.mk 5 6]\n\
        #eval Label.mk \"label\"\n\
        #eval (42 : Nat)\n\
        #eval \"raw string\"\n\
        #eval ([1, 2] : List Nat)\n"
    );
    std::fs::write(&source, &program).unwrap();
    let output = invoke("run", &source, &lib, &work);
    let report = completed(&output);
    for expected in [
        "\"kind\":\"format\",\"value\":\"{ x := 3, y := 4 }\"",
        "\"kind\":\"format\",\"value\":\"[{ x := 3, y := 4 }, { x := 5, y := 6 }]\"",
        "\"kind\":\"format\",\"value\":\"label\"",
        "\"kind\":\"nat\",\"value\":42",
        "\"kind\":\"string\",\"value\":\"raw string\"",
        "\"kind\":\"list\",\"value\":[1,2]",
    ] {
        assert!(report.contains(expected), "missing {expected}: {report}");
    }
    // A constructor's runtime tag is not a scalar result or a printer. Failure
    // must withhold the entire report, including preceding valid evaluations.
    std::fs::write(
        &source,
        format!("{program}\nstructure Bare where\n  value : Nat\nset_option eval.derive.repr false in\n#eval Bare.mk 7\n"),
    )
    .unwrap();
    let failed = invoke("run", &source, &lib, &work);
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(
        String::from_utf8_lossy(&failed.stderr).contains("could not synthesize a Repr or ToString"),
        "{failed:?}"
    );
    std::fs::write(&source, program).unwrap();
    let recovered_output = invoke("run", &source, &lib, &work);
    let recovered = completed(&recovered_output);
    // Import-cache hit/miss evidence differs; the checked source world and
    // complete ordered evaluation results must remain exactly the same.
    assert_eq!(
        recovered
            .split_once("\"declarationLogicalRoot\":")
            .unwrap()
            .1,
        report.split_once("\"declarationLogicalRoot\":").unwrap().1
    );
}

#[test]
fn automatic_eval_repr_matches_the_pin_and_stays_private() {
    let Some(lib) = pinned_lib() else { return };
    let reference = lib
        .parent()
        .and_then(Path::parent)
        .unwrap()
        .join("bin/lean");
    if !reference.is_file() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference executable is required",
        );
        eprintln!("SKIP: pinned Reference executable absent");
        return;
    }
    let work = std::env::temp_dir().join(format!(
        "fln-automatic-eval-repr-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&work).unwrap();
    let header = "prelude\nimport Init.Data.Repr\nimport Init.Data.ToString.Basic\n";
    let definitions = r#"
structure AutoPoint where
  x : Nat
  y : Nat
inductive AutoChain (A : Type) where
  | nil
  | cons (head : A) (tail : AutoChain A)
inductive AutoVec (A : Type) : Nat → Type where
  | nil : AutoVec A 0
  | cons {n : Nat} (head : A) (tail : AutoVec A n) : AutoVec A (n + 1)
inductive StringOnly where | mk
instance : ToString StringOnly where
  toString _ := "existing printer wins"
"#;
    let source = work.join("Accepted.lean");
    std::fs::write(
        &source,
        format!(
            "{header}{definitions}\n\
             #eval AutoPoint.mk 3 4\n\
             #eval AutoChain.cons 1 (AutoChain.cons 2 AutoChain.nil)\n\
             #eval AutoVec.cons 7 AutoVec.nil\n\
             #eval StringOnly.mk\n\
             #eval AutoPoint.mk 5 6\n"
        ),
    )
    .unwrap();
    let pin = Command::new(&reference)
        .arg("--threads=1")
        .arg(&source)
        .output()
        .unwrap();
    assert!(pin.status.success(), "{pin:?}");
    let run = |source: &Path| {
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg("--threads=1")
            .arg(source)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", work.join("imports"))
            .output()
            .unwrap()
    };
    let ours = run(&source);
    assert!(ours.status.success(), "{ours:?}");
    assert_eq!(ours.stdout, pin.stdout);
    assert_eq!(ours.stderr, pin.stderr);

    // These failures distinguish a private one-shot fallback from installing
    // a global instance, deriving every reachable field, or ignoring opt-out.
    for (index, body) in [
        "inductive PrivateRepr where | mk\n#eval PrivateRepr.mk\n#synth Repr PrivateRepr",
        "structure Disabled where\n  value : Nat\nset_option eval.derive.repr false in\n#eval Disabled.mk 7",
        "inductive NoFieldPrinter where | mk\nstructure Outer where\n  value : NoFieldPrinter\n#eval Outer.mk NoFieldPrinter.mk",
    ]
    .iter()
    .enumerate()
    {
        let source = work.join(format!("Refused{index}.lean"));
        std::fs::write(&source, format!("{header}{body}\n")).unwrap();
        let pin = Command::new(&reference)
            .arg("--threads=1")
            .arg(&source)
            .output()
            .unwrap();
        assert_eq!(pin.status.code(), Some(1), "{body}: {pin:?}");
        let ours = run(&source);
        // MissingPrinter retains the native capability classification (5),
        // while a failed #synth is an elaboration failure (1). The pin uses 1
        // for both; neither door may publish earlier evaluation output.
        let expected_exit = if index == 0 { 1 } else { 5 };
        assert_eq!(ours.status.code(), Some(expected_exit), "{body}: {ours:?}");
        assert!(ours.stdout.is_empty(), "{body}: {ours:?}");
        let diagnostic = String::from_utf8_lossy(&ours.stderr);
        if index == 0 {
            assert!(diagnostic.contains("Repr"), "{body}: {ours:?}");
        } else {
            assert!(
                diagnostic.contains("could not synthesize a Repr or ToString instance"),
                "{body}: {ours:?}",
            );
        }
    }
}
