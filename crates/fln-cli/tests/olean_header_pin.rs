//! An `.olean` part whose fixed header is not the pinned toolchain's is refused by
//! every installed door that claims a pinned artifact (bead `fln-fur.1`): `fln
//! check-olean`, `fln olean inspect`, `fln olean verify-rebuild` (one file, and
//! every part of a module-system chain) and `.olean` imports. The pinned loader
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
    let rebuilt = fln(&scratch, &["olean", "verify-rebuild", path], None);
    assert!(rebuilt.status.success(), "{rebuilt:?}");
    assert!(
        String::from_utf8_lossy(&rebuilt.stdout).contains("pinned .olean rebuild audit: complete")
    );
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
            (
                "olean verify-rebuild",
                fln(&scratch, &["olean", "verify-rebuild", path], None),
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

/// `olean verify-rebuild` over a module-system chain holds every part's header to
/// the pin, naming the part, whichever part PATH names. The committed `Init/Prelude`
/// chain is the pin's own bytes (held by `cli_personalities_and_verbs`'s
/// `olean_verify_rebuild_chain_fixture_is_the_pinned_init_prelude`), so this needs no
/// installed Reference. The rebuild re-derives a header from its parsed fields, so a
/// forged `flags`, `lean_version` or `githash` used to verify as complete.
#[test]
fn verify_rebuild_holds_every_part_of_a_chain_to_the_pin() {
    const PARTS: [&str; 3] = [".olean", ".olean.server", ".olean.private"];
    let fixtures =
        fln_core::checked_workspace_root!().join("crates/fln-conformance/fixtures/tag_attributes");
    let chain = PARTS.map(|part| {
        let suffix = part.strip_prefix(".olean").unwrap();
        std::fs::read(fixtures.join(format!("prelude.olean{suffix}"))).unwrap()
    });
    let scratch = Scratch::new();
    let write_chain = |directory: &str, parts: &[Vec<u8>; 3]| -> [PathBuf; 3] {
        std::array::from_fn(|index| {
            let suffix = PARTS[index].strip_prefix(".olean").unwrap();
            scratch.write(&format!("{directory}/Prelude.olean{suffix}"), &parts[index])
        })
    };
    let verify = |path: &Path, json: bool| {
        let mut arguments = vec!["olean", "verify-rebuild"];
        if json {
            arguments.push("--json");
        }
        arguments.push(path.to_str().unwrap());
        fln(&scratch, &arguments, None)
    };

    let pinned = write_chain("pinned", &chain);
    for path in &pinned {
        let output = verify(path, false);
        assert!(output.status.success(), "{}: {output:?}", path.display());
        assert!(
            String::from_utf8_lossy(&output.stdout)
                .contains("pinned .olean rebuild audit: complete")
        );
    }

    for (index, part) in PARTS.into_iter().enumerate() {
        for (case, field, offset, byte) in FORGERIES {
            let mut parts = chain.clone();
            assert_ne!(
                parts[index][offset], byte,
                "{case}: the edit must change a byte"
            );
            parts[index][offset] = byte;
            let paths = write_chain(&format!("forged{part}-{offset}"), &parts);
            // Human, from the forged part itself; robot, from the exported part.
            let human = verify(&paths[index], false);
            let robot = verify(&paths[0], true);
            for (form, output) in [("human", &human), ("robot", &robot)] {
                assert_eq!(
                    output.status.code(),
                    Some(1),
                    "{part} {case} {form}: {output:?}"
                );
                assert!(
                    !String::from_utf8_lossy(&output.stdout).contains("audit: complete"),
                    "{part} {case} {form}: {output:?}"
                );
            }
            let human = String::from_utf8_lossy(&human.stderr);
            assert!(
                human.starts_with(&format!(
                    "fln olean verify-rebuild: header: incompatible {part} header: \
                     header field `{field}`"
                )),
                "{part} {case}: {human}"
            );
            let robot = String::from_utf8_lossy(&robot.stderr);
            assert!(
                robot.contains("\"class\":\"header\"")
                    && robot.contains(&format!("\"part\":\"{part}\""))
                    && robot.contains(&format!("header field `{field}`")),
                "{part} {case}: {robot}"
            );
        }

        // The format `version` byte (offset 5) is the envelope's, not the pin
        // check's: the pin writes 2 and the pinned loader also accepts 3. Either
        // other value is still refused, naming the part, before anything verifies.
        for byte in [3, 4] {
            let mut parts = chain.clone();
            assert_eq!(parts[index][5], 2, "the pin writes format version 2");
            parts[index][5] = byte;
            let paths = write_chain(&format!("version{part}-{byte}"), &parts);
            let output = verify(&paths[index], false);
            assert_eq!(
                output.status.code(),
                Some(1),
                "{part} version {byte}: {output:?}"
            );
            assert!(
                output.stdout.is_empty(),
                "{part} version {byte}: {output:?}"
            );
            assert!(
                String::from_utf8_lossy(&output.stderr).starts_with(&format!(
                    "fln olean verify-rebuild: rebuild: {part} rebuild: "
                )),
                "{part} version {byte}: {output:?}"
            );
        }
    }
}
