//! `native_decide` and `decide +native` (vendored `src/Lean/Elab/Tactic/Decide.lean:57-100,
//! 186-189`, `src/Lean/Meta/Native.lean`), through the drop-in `lean` over `prelude` files. The
//! decision is compiled and run on this engine's own VM; on `true` the axiom
//! `<decl>._native.<tactic>.ax_…` is admitted before the declaration citing it, so `#print
//! axioms` lists it under the pin's name. Every program here was run through the pinned `lean`
//! v4.32.0 first (2026-10-23); the verdicts below are its verdicts, and each program runs through
//! the pinned binary again in the test when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const TACTICS: &str = "prelude\nimport Init.Tactics\n";

/// Accepted by the pin and here, printing exactly what the pin prints.
const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        "theorem_and_its_axiom",
        "theorem t1 : 2 + 2 = 4 := by native_decide\n#print axioms t1\n#print t1\n",
        "'t1' depends on axioms: [t1._native.native_decide.ax_1_1]\ntheorem t1 : 2 + 2 = 4 :=\n\
         of_decide_eq_true t1._native.native_decide.ax_1_1\n",
    ),
    (
        "decide_native",
        "theorem t3 : 2 + 2 = 4 := by decide +native\n#print axioms t3\n",
        "'t3' depends on axioms: [t3._native.decide.ax_1_1]\n",
    ),
    (
        "one_axiom_per_goal",
        "theorem e10 : (1 = 1) ∧ (2 = 2) := by constructor <;> native_decide\n#print axioms e10\n",
        "'e10' depends on axioms: [e10._native.native_decide.ax_1_1, \
         e10._native.native_decide.ax_1_2]\n",
    ),
    // Backtracking restores the environment but not the name generator, and every axiom
    // `addDecl` checks asynchronously advances it (`Lean/CoreM.lean:407-410`,
    // `Lean/AddDecl.lean:167-169`).
    (
        "backtracking_keeps_the_index",
        "theorem g1 : 3 = 3 := by\n  first | (native_decide; fail) | (native_decide; fail) | \
         native_decide\n#print axioms g1\ntheorem g5 : 3 = 3 := by\n  first | (decide +native; \
         fail) | native_decide\n#print axioms g5\ntheorem g6 : 3 = 3 := by\n  have h : 2 = 2 := by \
         native_decide\n  native_decide\n#print axioms g6\n",
        "'g1' depends on axioms: [g1._native.native_decide.ax_1_3]\n'g5' depends on axioms: \
         [g5._native.native_decide.ax_1_2]\n'g6' depends on axioms: \
         [g6._native.native_decide.ax_1_1, g6._native.native_decide.ax_1_2]\n",
    ),
    // Only a theorem elaborated asynchronously names its axioms in a forked generator.
    (
        "definitions_namespaces_and_sync_theorems",
        "def d1 : 1 = 1 := by native_decide\n#print axioms d1\nnamespace N\ntheorem a5 : 1 = 1 := \
         by native_decide\nend N\n#print axioms N.a5\nset_option Elab.async false in\ntheorem e5 : \
         1 = 1 := by native_decide\n#print axioms e5\n",
        "definitions_namespaces_and_sync_theorems.lean:3:0: warning: Definition `d1` is a \
         proposition; use `theorem` instead of `def`\n\nNote: This linter can be disabled with \
         `set_option linter.defProp false`\n'd1' depends on axioms: [d1._native.native_decide.ax_1]\n\
         'N.a5' depends on axioms: [N.a5._native.native_decide.ax_1_1]\n'e5' depends on axioms: \
         [e5._native.native_decide.ax_1]\n",
    ),
    (
        "instance_defined_in_the_file",
        "inductive Color where\n  | red | green\ndef Color.isRed : Color → Bool\n  | .red => true\n  \
         | .green => false\ndef Good (c : Color) : Prop := c.isRed = true\ninstance (c : Color) : \
         Decidable (Good c) := decEq c.isRed true\ntheorem goodRed : Good .red := by \
         native_decide\n#print axioms goodRed\nexample : ¬ Good .green := by native_decide\n",
        "'goodRed' depends on axioms: [goodRed._native.native_decide.ax_1_1]\n",
    ),
    // A false example under a guard expecting the pin's message, and `first` taking the next
    // alternative after a false or open decision.
    (
        "guarded_false_and_fallbacks",
        "/--\nerror: Tactic `native_decide` evaluated that the proposition\n  2 + 2 = 5\nis \
         false\n-/\n#guard_msgs in\nexample : 2 + 2 = 5 := by native_decide\nexample (p : Prop) \
         [Decidable p] (h : p) : p := by\n  first | native_decide | exact h\nexample : 2 + 2 = 4 := \
         by\n  first | (native_decide; fail) | native_decide\n",
        "",
    ),
];

/// Accepted by the pin and here over a larger import, printing exactly what the pin prints.
const ACCEPTED_IMPORTS: &[(&str, &str, &str, &str)] = &[
    (
        "list_range",
        "prelude\nimport Init.Data.List.Basic\n",
        "theorem r : (List.range 100).length = 100 := by native_decide\n#print axioms r\n",
        "'r' depends on axioms: [r._native.native_decide.ax_1_1]\n",
    ),
    (
        "uint8_arithmetic",
        "prelude\nimport Init.Data.UInt.Basic\n",
        "theorem u : (-1 : UInt8) = 255 := by native_decide\n#print axioms u\nexample : \
         (200 : UInt8) + 100 = 44 := by native_decide\n",
        "'u' depends on axioms: [u._native.native_decide.ax_1_1]\n",
    ),
];

/// Rejected by the pin and here, with the pin's words (its first line).
const REJECTED: &[(&str, &str, &str)] = &[
    (
        "false",
        "example : 2 + 2 = 5 := by native_decide\n",
        "Tactic `native_decide` evaluated that the proposition",
    ),
    (
        "decide_native_false",
        "example : 2 + 2 = 5 := by decide +native\n",
        "Tactic `decide` evaluated that the proposition",
    ),
    (
        "free_variable",
        "example (n : Nat) : n + 0 = n := by native_decide\n",
        "Expected type must not contain free variables",
    ),
    // The instance is the local one, so the decision mentions a local.
    (
        "local_instance",
        "example [inst : Decidable (1 = 1)] : 1 = 1 := by native_decide\n",
        "Tactic `native_decide` failed: Cannot native decide proposition with free variables",
    ),
];

/// Accepted by the pin; a typed non-answer here (exit 5), never a verdict.
const REFUSED: &[(&str, &str, &str, &str)] = &[
    // `Array.map` runs code this engine's compiler does not cover.
    (
        "outside_the_compiled_subset",
        "prelude\nimport Init.Data.Array.Basic\n",
        "theorem a : (#[1, 2, 3].map (· + 1)).size = 3 := by native_decide\n",
        "native evaluation is not supported here",
    ),
    // An instance's route does not carry the axiom to admission.
    (
        "instance_route",
        TACTICS,
        "instance : Inhabited (PLift (2 = 2)) := ⟨⟨by native_decide⟩⟩\n",
        "native evaluation is not available here",
    ),
    // An executed definition's record has no place for an axiom before it.
    (
        "compiled_definition",
        TACTICS,
        "def d2 : Fin 10 := ⟨3, by native_decide⟩\n",
        "`native_decide` in a definition this engine compiles",
    ),
];

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
        .filter(|lib| lib.join("Init/Tactics.olean").is_file());
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
        "fln-native-decide-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// Exit code, stdout and stderr of `binary` on `<name>.lean`, run from `root`.
fn run(binary: &Path, lib: &Path, root: &Path, name: &str) -> (Option<i32>, String, String) {
    let output = Command::new(binary)
        .arg(format!("{name}.lean"))
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .env("LEAN_BACKTRACE", "0")
        .output()
        .expect("run lean");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// This crate's `lean` on `header` + `program`, and the pinned `lean` when it is installed.
#[allow(clippy::type_complexity)]
fn check(
    lib: &Path,
    root: &Path,
    name: &str,
    header: &str,
    program: &str,
) -> ((Option<i32>, String, String), Option<(Option<i32>, String)>) {
    std::fs::write(
        root.join(format!("{name}.lean")),
        format!("{header}{program}"),
    )
    .unwrap();
    let ours = run(Path::new(env!("CARGO_BIN_EXE_lean")), lib, root, name);
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|lean| {
            let (code, stdout, _) = run(&lean, lib, root, name);
            (code, stdout)
        });
    (ours, pinned)
}

#[test]
fn native_decide_matches_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so each import closure is admitted once for every program.
    let root = workspace();
    let accepted = ACCEPTED
        .iter()
        .map(|&(name, program, expected)| (name, TACTICS, program, expected))
        .chain(ACCEPTED_IMPORTS.iter().copied());
    for (name, header, program, expected) in accepted {
        let ((code, stdout, stderr), pinned) = check(&lib, &root, name, header, program);
        assert_eq!(code, Some(0), "{name}: {program}\n{stderr}");
        assert_eq!(stdout, expected, "{name}: {program}");
        if let Some((code, stdout)) = pinned {
            assert_eq!(code, Some(0), "{name}: the pinned lean rejects it");
            assert_eq!(stdout, expected, "{name}: the pinned lean prints otherwise");
        }
    }
    for &(name, program, message) in REJECTED {
        let ((code, stdout, stderr), pinned) = check(&lib, &root, name, TACTICS, program);
        assert_eq!(code, Some(1), "{name}: {program}\n{stdout}{stderr}");
        assert!(
            stderr.contains(message),
            "{name}: not the pin's refusal\n{stderr}"
        );
        if let Some((code, stdout)) = pinned {
            assert_eq!(code, Some(1), "{name}: the pinned lean accepts it");
            assert!(stdout.contains(message), "{name}: the pin says\n{stdout}");
        }
    }
    for &(name, header, program, message) in REFUSED {
        let ((code, _, stderr), pinned) = check(&lib, &root, name, header, program);
        assert_eq!(code, Some(5), "{name}: not a typed non-answer\n{stderr}");
        assert!(stderr.contains(message), "{name}: {stderr}");
        if let Some((code, _)) = pinned {
            assert_eq!(code, Some(0), "{name}: the pinned lean rejects it");
        }
    }
}

/// An instance that panics while it is evaluated: the pin prints the message and continues with
/// the `Inhabited` default, `isTrue`, so the proof stands (vendored
/// `tests/elab/decideNativePanic.lean`). Both accept; this engine's VM does not print the panic
/// message, which only the pin's stdout shows.
#[test]
fn a_panicking_evaluation_continues_with_the_default_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let program = "inductive ItsTrue2 : Prop\n  | mk\ninstance : Inhabited (Decidable ItsTrue2) := \
                   ⟨isTrue .mk⟩\ninstance : Decidable ItsTrue2 := panic \"oh no\"\nexample : \
                   ItsTrue2 := by native_decide\n";
    let ((code, stdout, stderr), pinned) = check(&lib, &root, "panicking", TACTICS, program);
    assert_eq!(code, Some(0), "{stdout}{stderr}");
    if let Some((code, stdout)) = pinned {
        assert_eq!(code, Some(0), "the pinned lean rejects it");
        assert_eq!(stdout, "oh no\n");
    }
}
