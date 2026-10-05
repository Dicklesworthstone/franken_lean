//! An `.olean` part whose fixed header is not the pinned toolchain's is refused by
//! every installed door that claims a pinned artifact (bead `fln-fur.1`): `fln
//! check-olean`, `fln olean inspect` and `.olean` imports. The pinned loader
//! refuses such a file as an "incompatible header" (module.cpp:488-497).
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-olean-header-pin-{}-{}",
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
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn logged(command: &mut Command) -> Output {
    let output = command.output().unwrap();
    eprintln!(
        "argv: {:?}\nexit: {:?}\nstdout: {}\nstderr: {}",
        command,
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn fln(scratch: &Scratch, arguments: &[&str], search: Option<&Path>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    command
        .args(arguments)
        .env("FLN_IMPORT_REUSE_DIR", scratch.0.join("records"));
    if let Some(search) = search {
        command.env("LEAN_PATH", search);
    }
    logged(&mut command)
}

/// A one-definition `prelude` module built by the installed `lake`: its pinned
/// header is the writer's, and nothing else about it matters here.
fn built(scratch: &Scratch) -> Vec<u8> {
    scratch.write(
        "producer/lakefile.toml",
        "name = \"producer\"\n[[lean_lib]]\nname = \"Ext\"\n",
    );
    scratch.write(
        "producer/Ext/A.lean",
        "prelude\ndef Ext.A (P : Prop) (h : P) : P := h\n",
    );
    let output = logged(
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(scratch.0.join("producer"))
            .args(["build", "+Ext.A:olean"])
            .env("LEAN_PATH", scratch.0.join("no-imports"))
            .env("FLN_IMPORT_REUSE_DIR", scratch.0.join("records")),
    );
    assert!(output.status.success(), "{output:?}");
    std::fs::read(scratch.0.join("producer/.lake/build/lib/lean/Ext/A.olean")).unwrap()
}

/// `(case, field, offset, byte)`: the header field each edit lands in. Offsets are
/// the generated contract's: flags 6, lean_version 7..40, githash 40..80.
const FORGERIES: [(&str, &str, usize, u8); 5] = [
    ("flags cleared", "flags", 6, 0x00),
    ("Lean 5.32.0", "lean_version", 7, b'5'),
    ("lean_version padding", "lean_version", 7 + 20, 0x07),
    ("another commit", "githash", 40, b'9'),
    ("githash last byte", "githash", 79, b'0'),
];

#[test]
fn every_door_refuses_a_header_the_pin_did_not_write_and_names_the_field() {
    let scratch = Scratch::new();
    let original = built(&scratch);
    let path = scratch.write("pinned/Ext/A.olean", &original);
    let path = path.to_str().unwrap();
    assert!(fln(&scratch, &["check-olean", path], None).status.success());
    let inspected = fln(&scratch, &["olean", "inspect", path], None);
    assert!(inspected.status.success());
    assert!(String::from_utf8_lossy(&inspected.stdout).contains("pinned .olean audit: complete"));
    scratch.write(
        "consumer/Use.lean",
        "prelude\nimport Ext.A\ntheorem Use.again (P : Prop) (h : P) : P := Ext.A P h\n",
    );
    let consumer = scratch.0.join("consumer/Use.lean");
    let consumer = consumer.to_str().unwrap();
    let import = |search: &Path| {
        fln(
            &scratch,
            &["check-source", "--import-posture", "recheck", consumer],
            Some(search),
        )
    };
    assert!(import(&scratch.0.join("pinned")).status.success());

    for (case, field, offset, byte) in FORGERIES {
        let mut forged = original.clone();
        assert_ne!(forged[offset], byte, "{case}: the edit must change a byte");
        forged[offset] = byte;
        let directory = scratch.0.join(format!("forged-{offset}"));
        let path = scratch.write(&format!("forged-{offset}/Ext/A.olean"), &forged);
        let path = path.to_str().unwrap();
        let named = format!("header field `{field}`");
        for (door, output) in [
            ("check-olean", fln(&scratch, &["check-olean", path], None)),
            (
                "olean inspect",
                fln(&scratch, &["olean", "inspect", path], None),
            ),
            ("import", import(&directory)),
        ] {
            assert!(!output.status.success(), "{case} via {door}: {output:?}");
            let text = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(
                text.contains("incompatible .olean header") && text.contains(&named),
                "{case} via {door}: {text}"
            );
            assert!(
                !text.contains("audit: complete"),
                "{case} via {door}: {text}"
            );
        }
    }
}

/// A module-system chain is held part by part: a companion's header is refused under
/// its own name even when the exported part is the pin's.
#[test]
fn a_companion_part_the_pin_did_not_write_is_refused_by_name() {
    let Some(home) = std::env::var_os("HOME") else {
        return;
    };
    let lib = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    if !lib.join("Init/Prelude.olean").is_file() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    }
    let scratch = Scratch::new();
    for suffix in ["olean.server", "olean.private"] {
        let mut path = None;
        for part in ["olean", "olean.server", "olean.private"] {
            let mut bytes = std::fs::read(lib.join(format!("Init/Prelude.{part}"))).unwrap();
            if part == suffix {
                bytes[40] ^= 0x01;
            }
            let written = scratch.write(&format!("{suffix}/Init/Prelude.{part}"), &bytes);
            if part == "olean" {
                path = Some(written);
            }
        }
        let path = path.unwrap();
        let output = fln(&scratch, &["check-olean", path.to_str().unwrap()], None);
        assert!(!output.status.success(), "{suffix}: {output:?}");
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(
            error.contains(&format!("incompatible .{suffix} header"))
                && error.contains("header field `githash`"),
            "{suffix}: {error}"
        );
    }
}
