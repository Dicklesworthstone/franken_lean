//! The nine held-out ordinary programs that stopped at the `String` field projection (bead
//! `fln-ingress-string-field-projection-funz`), through the installed drop-in `lean` against the
//! pinned v4.32.0 `lean`, each with its implicit whole `Init`.
//!
//! In the pin these programs run the String externs (`lean_string_utf8_get`, `_set`,
//! `_get_fast`, `lean_string_get_byte_fast`, `lean_string_data`, ...). Where FrankenLean had no
//! native row it compiled the extern's logical body, which reaches `String.toByteArray`'s
//! `self.1`, a projection of a type with no constructor layout at runtime. Each program here
//! must now either print exactly what the pin prints, or stop at a different, typed refusal
//! with no wrong output first. [`MATCHING`] names the programs that agree with the pin
//! byte for byte; a program leaving that list is a regression.
//!
//! The programs and the pin's outputs were recorded on 2026-10-26 by running the pinned `lean`
//! on each file from the file's own directory; the live pin is compared with that record again.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

struct Probe {
    file: &'static str,
    source: &'static str,
    /// The pinned `lean`'s stdout, which carries its messages; it exits 0 on all nine.
    expected: &'static str,
}

const PROBES: [Probe; 9] = [
    Probe {
        file: "p02_strings.lean",
        source: "def greet (name : String) : String := s!\"Hello, {name}!\"\n\
                 #eval greet \"Lean\"\n\
                 #eval \"abc\".length + \"de\".length\n\
                 #eval \"a,b,c\".splitOn \",\"\n",
        expected: "\"Hello, Lean!\"\n5\n[\"a\", \"b\", \"c\"]\n",
    },
    Probe {
        file: "p17_char.lean",
        source: "def caesar (shift : Nat) (s : String) : String :=\n  \
                 s.map fun c =>\n    \
                 if c.isLower then Char.ofNat ((c.toNat - 'a'.toNat + shift) % 26 + 'a'.toNat) else c\n\
                 \n\
                 #eval caesar 3 \"hello world\"\n",
        expected: "\"khoor zruog\"\n",
    },
    Probe {
        file: "p46_string_ops.lean",
        source: "#eval \"Lean\".toUpper\n\
                 #eval \", \".intercalate [\"x\", \"y\", \"z\"]\n\
                 #eval \"  pad  \".trim\n\
                 #eval \"hello\".toList.reverse.asString\n\
                 #eval \"42\".toNat?\n",
        expected: "\"LEAN\"\n\
                   \"x, y, z\"\n\
                   p46_string_ops.lean:3:16: warning: `String.trim` has been deprecated: Use \
                   `String.trimAscii` instead\n\
                   \n\
                   Note: The updated constant has a different type:\n  \
                   String \u{2192} String.Slice\n\
                   instead of\n  \
                   String \u{2192} String\n\
                   \"pad\"\n\
                   p46_string_ops.lean:4:29: warning: `List.asString` has been deprecated: Use \
                   `String.ofList` instead\n\
                   \n\
                   Note: The updated constant is in a different namespace. Dot notation may need \
                   to be changed (e.g., from `x.asString` to `String.ofList x`).\n\
                   \"olleh\"\n\
                   some 42\n",
    },
    Probe {
        file: "p47_char_list.lean",
        source: "def countVowels (s : String) : Nat :=\n  \
                 (s.toList.filter (fun c => c \u{2208} ['a', 'e', 'i', 'o', 'u'])).length\n\
                 \n\
                 #eval countVowels \"programming language\"\n",
        expected: "7\n",
    },
    Probe {
        file: "p53_string_iter.lean",
        source: "def isPalindrome (s : String) : Bool :=\n  \
                 let cs := s.toList.filter Char.isAlpha |>.map Char.toLower\n  \
                 cs == cs.reverse\n\
                 \n\
                 #eval isPalindrome \"A man, a plan, a canal: Panama\"\n\
                 #eval isPalindrome \"Lean\"\n",
        expected: "true\nfalse\n",
    },
    Probe {
        file: "q37_string_join.lean",
        source: "#eval \", \".intercalate [\"a\", \"b\", \"c\"]\n\
                 #eval String.join [\"x\", \"y\", \"z\"]\n\
                 #eval \"hello world\".splitOn \" \"\n",
        expected: "\"a, b, c\"\n\"xyz\"\n[\"hello\", \"world\"]\n",
    },
    Probe {
        file: "q38_char_ops.lean",
        source: "#eval 'a'.toUpper\n\
                 #eval \"Lean\".toList.map Char.toNat\n\
                 #eval \"abc\".toList.reverse\n",
        expected: "'A'\n[76, 101, 97, 110]\n['c', 'b', 'a']\n",
    },
    Probe {
        file: "r02_string_split.lean",
        source: "#eval \"alpha beta  gamma\".splitOn \" \"\n\
                 #eval (\"a-b-c\".splitOn \"-\").length\n\
                 #eval \"Hello\".toUpper ++ \"!\"\n",
        expected: "[\"alpha\", \"beta\", \"\", \"gamma\"]\n3\n\"HELLO!\"\n",
    },
    Probe {
        file: "r36_try_catch.lean",
        source: "def risky (n : Nat) : IO Nat := do\n  \
                 if n == 0 then throw (IO.userError \"zero!\") else pure (100 / n)\n\
                 def safe (n : Nat) : IO String := do\n  \
                 try\n    \
                 let v \u{2190} risky n\n    \
                 return s!\"ok {v}\"\n  \
                 catch e => return s!\"caught {e}\"\n\
                 #eval safe 4\n\
                 #eval safe 0\n",
        expected: "\"ok 25\"\n\"caught zero!\"\n",
    },
];

/// The programs whose complete stdout and exit code agree with the pin, measured on 2026-10-27
/// with a release `lean` warmed on the whole pinned Init. The ninth, `p46_string_ops.lean`,
/// stops at its last command (`"42".toNat?`, through `String.Slice`'s iterator `fold`) with the
/// typed ingress node-limit refusal, before printing.
const MATCHING: &[&str] = &[
    "p02_strings.lean",
    "p17_char.lean",
    "p47_char_list.lean",
    "p53_string_iter.lean",
    "q37_string_join.lean",
    "q38_char_ops.lean",
    "r02_string_split.lean",
    "r36_try_catch.lean",
];

/// The refusal these programs used to stop at; none may stop there again.
const PROJECTION_REFUSAL: &str = "structure projection `String` field 0";

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
        .filter(|lib| lib.join("Init.olean").is_file());
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
        "fln-string-extern-probes-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn run(
    program: &Path,
    root: &Path,
    file: &str,
    lib: &Path,
    records: &Path,
) -> (i32, String, String) {
    let output = Command::new(program)
        .current_dir(root)
        .arg(file)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", records)
        .output()
        .unwrap();
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
#[ignore = "whole pinned Init admission; required scheduled Reference release lane"]
fn string_extern_probe_programs_agree_with_the_pin_or_refuse_typed() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let reference = lib.parent().unwrap().parent().unwrap().join("bin/lean");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success(), "{version:?}");
    assert_eq!(
        String::from_utf8_lossy(&version.stdout).trim(),
        fln::OLEAN_PIN_COMMIT
    );
    let root = workspace();
    let records = root.join("records");
    std::fs::create_dir(&records).unwrap();
    let mut agreeing = Vec::new();
    for probe in &PROBES {
        std::fs::write(root.join(probe.file), probe.source).unwrap();
        let (code, stdout, stderr) = run(&reference, &root, probe.file, &lib, &records);
        assert_eq!(
            (code, stdout.as_str()),
            (0, probe.expected),
            "{}: {stderr}",
            probe.file
        );
        let (code, stdout, stderr) = run(
            Path::new(env!("CARGO_BIN_EXE_lean")),
            &root,
            probe.file,
            &lib,
            &records,
        );
        eprintln!(
            "string extern probe {}: exit {code}, {}",
            probe.file,
            if code == 0 && stdout == probe.expected {
                "matches the pin".to_owned()
            } else {
                format!("stderr {}", stderr.trim())
            }
        );
        // Soundness first: an accepted program prints exactly the pin's output, and a refused
        // one printed nothing the pin did not print before refusing.
        if code == 0 {
            assert_eq!(
                stdout, probe.expected,
                "{}: accepted with other output",
                probe.file
            );
            agreeing.push(probe.file);
        } else {
            assert!(
                probe.expected.starts_with(&stdout),
                "{}: refused after printing other output: {stdout}",
                probe.file
            );
            assert!(
                !stderr.contains(PROJECTION_REFUSAL),
                "{}: still stops at the String projection: {stderr}",
                probe.file
            );
        }
        assert_eq!(
            std::fs::read_to_string(root.join(probe.file)).unwrap(),
            probe.source
        );
    }
    assert_eq!(agreeing, MATCHING, "the programs that agree with the pin");
}
