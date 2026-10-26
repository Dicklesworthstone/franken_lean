//! An application whose result type is the output parameter of one of its own instance
//! arguments does not propagate its expected type into that result: the pin's
//! `resultIsOutParamSupport` (vendored `Lean/Elab/App.lean`, `addImplicitArg`, `finalize`). The
//! instance determines the output, default instances run when it is still unknown, and only then
//! is the result compared with the expected type or coerced to it. `getElem bs n : Option Bool`
//! is `some (getElem bs n)`; unifying `?Elem := Option Bool` first asked for an instance no
//! declaration provides. Under `@` the support is off, and the pin refuses.
//!
//! Through the drop-in `lean` over `prelude` with `Init.Data.Int.Basic`, `Init.Data.Array.Basic`
//! and `Init.Data.Option.Coe`. Every program here was run through the pinned `lean` v4.32.0 with
//! the same header first (2026-10-24), and is compared with the pinned binary again when present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const HEADER: &str = "prelude\nimport Init.Data.Int.Basic\nimport Init.Data.Array.Basic\nimport Init.Data.Option.Coe\n";

/// The upstream `tests/elab/forOutParamIssue.lean` class, its applications at an expected type
/// the output must be coerced to, through a named argument, and in `App.lean`'s own example
/// (`let x := getElem xs 0`, whose `0` defaults to `Nat` before `x` is used); the core
/// `HAdd`/`HMul` outputs (defaults, then `↑`); and `GetElem`'s three-argument notation.
const ACCEPTED: &str = "namespace Ex
class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  getElem (xs : Cont) (i : Idx) : Elem
export GetElem (getElem)
instance : GetElem (Array α) Nat α where
  getElem xs i := xs[i]'sorry
def c5 (bs : Array Bool) (n : Nat) : Option Bool := getElem bs n
#print c5
def c8 (bs : Array Bool) (n : Nat) : Bool := getElem bs n
#print c8
def named (bs : Array Bool) (n : Nat) : Option Bool := getElem (xs := bs) n
#print named
opaque f : Option Bool → Bool
opaque g : Bool → Bool
def bad (xs : Array Bool) : Bool :=
  let x := getElem xs 0
  f x && g x
end Ex
def h1 : Int := HAdd.hAdd 1 2
#print h1
def h2 (a b : Nat) : Int := HAdd.hAdd a b
#print h2
def h4 (a b : Nat) : Nat := HMul.hMul a b
#print h4
def idx (bs : Array Bool) (n : Nat) (h : n < bs.size) : Option Bool := bs[n]'h
#print idx
def h7 (xs : List Nat) (n : Nat) : Option Nat := getElem? xs n
#print h7
";

/// The pinned `lean`'s stdout for `HEADER` + `ACCEPTED`.
const ACCEPTED_EXPECTED: &str = "accepted.lean:9:0: warning: declaration uses `sorry`
def Ex.c5 : Array Bool → Nat → Option Bool :=
fun bs n => some (getElem bs n)
def Ex.c8 : Array Bool → Nat → Bool :=
fun bs n => getElem bs n
def Ex.named : Array Bool → Nat → Option Bool :=
fun bs n => some (getElem bs n)
def h1 : Int :=
↑(1 + 2)
def h2 : Nat → Nat → Int :=
fun a b => ↑(a + b)
def h4 : Nat → Nat → Nat :=
fun a b => a * b
def idx : (bs : Array Bool) → (n : Nat) → n < bs.size → Option Bool :=
fun bs n h => some (getElem bs n h)
def h7 : List Nat → Nat → Option Nat :=
fun xs n => getElem? xs n
";

/// `@` turns the support off: the expected type reaches the output first, and no
/// `GetElem (Array Bool) Nat (Option Bool) _` instance exists.
const EXPLICIT: &str = "example (bs : Array Bool) (n : Nat) (h : n < bs.size) : Option Bool :=
  @GetElem.getElem _ _ _ _ _ bs n h
";

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
        .filter(|lib| lib.join("Init/Core.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-outparam-results-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// This crate's `lean` on `HEADER` + `program`, and the pinned `lean` when it is present.
fn runs(lib: &Path, root: &Path, name: &str, program: &str) -> (Output, Option<Output>) {
    let entry = format!("{name}.lean");
    std::fs::write(root.join(&entry), format!("{HEADER}{program}")).unwrap();
    let run = |binary: &Path| {
        Command::new(binary)
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run lean")
    };
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    (
        run(Path::new(env!("CARGO_BIN_EXE_lean"))),
        pinned.as_deref().map(run),
    )
}

#[test]
fn an_instance_output_result_is_synthesized_before_it_meets_the_expected_type() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let (ours, pinned) = runs(&lib, &root, "accepted", ACCEPTED);
    if let Some(pinned) = pinned {
        assert_eq!(pinned.status.code(), Some(0), "the pin refuses it");
        assert_eq!(
            String::from_utf8_lossy(&pinned.stdout),
            ACCEPTED_EXPECTED,
            "the pin moved"
        );
    }
    assert_eq!(
        ours.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&ours.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&ours.stdout), ACCEPTED_EXPECTED);
}

#[test]
fn an_explicit_application_propagates_its_expected_type_and_is_refused() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let (ours, pinned) = runs(&lib, &root, "explicit", EXPLICIT);
    if let Some(pinned) = pinned {
        assert_eq!(pinned.status.code(), Some(1), "the pin accepts it");
    }
    assert_ne!(ours.status.code(), Some(0), "accepted {EXPLICIT}");
}
