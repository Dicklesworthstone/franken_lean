//! Installed named-module checking must audit the imports, not merely locate them.
#![forbid(unsafe_code)]
use fln::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr, Level,
    Name, TheoremVal,
};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture {
    dir: PathBuf,
    first: PathBuf,
    second: PathBuf,
    base: Vec<u8>,
    mid: Vec<u8>,
    top: Vec<u8>,
}
fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), Vec::new())
}
fn type_p() -> Expr {
    Expr::forall_e(name("x"), constant("P"), constant("P"), BinderInfo::Default)
}
fn definition(valid: bool) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("idP"),
            level_params: Vec::new(),
            type_: type_p(),
        },
        value: if valid {
            Expr::lam(
                name("x"),
                constant("P"),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            )
        } else {
            Expr::sort(Level::zero())
        },
        hints: fln::ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("idP")],
    })
}
fn encode(imports: &[&str], constants: &[ConstantInfo], module: bool) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|n| fln::OleanModuleImport {
            module: name(n),
            import_all: true,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    fln::encode_olean_module(
        fln::OleanModuleWriteInput {
            is_module: module,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: 0x10000000,
        },
        fln::OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
}
fn write(root: &Path, relative: &str, bytes: impl AsRef<[u8]>) -> PathBuf {
    let path = root.join(relative);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, bytes).unwrap();
    path
}
impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "fln-check-module-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let first = dir.join("first");
        let second = dir.join("second");
        let base = encode(
            &[],
            &[ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name("P"),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                is_unsafe: false,
            })],
            false,
        );
        let mid = encode(&["Lib.Base"], &[definition(true)], false);
        let top = encode(
            &["Lib.Middle"],
            &[ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: name("identity"),
                    level_params: Vec::new(),
                    type_: type_p(),
                },
                value: constant("idP"),
                all: vec![name("identity")],
            })],
            false,
        );
        write(&first, "Lib/Base.olean", &base);
        write(&second, "Lib/Middle.olean", &mid);
        write(&second, "Lib/Top.olean", &top);
        Self {
            dir,
            first,
            second,
            base,
            mid,
            top,
        }
    }
    fn command(&self, extra: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-module", "--json"])
            .args(extra)
            .arg("Lib.Top")
            .arg(&self.first)
            .arg(&self.second)
            .env("LEAN_PATH", self.dir.join("irrelevant-ambient-root"))
            .env("FLN_IMPORT_REUSE_DIR", self.dir.join("must-not-be-written"))
            .output()
            .unwrap()
    }
    fn original(&self) {
        assert_eq!(
            std::fs::read(self.first.join("Lib/Base.olean")).unwrap(),
            self.base
        );
        assert_eq!(
            std::fs::read(self.second.join("Lib/Middle.olean")).unwrap(),
            self.mid
        );
        assert_eq!(
            std::fs::read(self.second.join("Lib/Top.olean")).unwrap(),
            self.top
        );
        assert!(!self.dir.join("must-not-be-written").exists());
    }
}
fn success(out: Output) -> String {
    assert!(out.status.success(), "{out:?}");
    assert!(out.stderr.is_empty(), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    assert!(text.contains("\"authority\":true"), "{text}");
    text
}
fn refusal(out: Output, code: i32) -> String {
    assert_eq!(out.status.code(), Some(code), "{out:?}");
    assert!(out.stderr.is_empty(), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    assert!(text.contains("\"authority\":false"), "{text}");
    text
}
#[test]
fn checks_a_transitive_multi_root_closure_with_identical_serial_and_parallel_answers() {
    let f = Fixture::new();
    let serial = success(f.command(&["--jobs", "1"]));
    let parallel = success(f.command(&["--jobs=4"]));
    assert_eq!(serial, parallel);
    for text in [
        "\"requestedModule\":\"Lib.Top\"",
        "\"moduleCount\":3",
        "\"declarations\":3",
        "\"axiomDeclarations\":1",
        "\"trust\":\"recheck\"",
        "\"executed\":false",
    ] {
        assert!(serial.contains(text), "{serial}");
    }
    for (module, bytes) in [
        ("Lib.Base", &f.base),
        ("Lib.Middle", &f.mid),
        ("Lib.Top", &f.top),
    ] {
        assert!(serial.contains(&format!("\"module\":\"{module}\"")));
        assert!(serial.contains(&fln::artifact_byte_hash(bytes).to_hex()));
    }
    f.original();
}
#[test]
fn unrelated_corrupt_artifacts_do_not_poison_the_requested_closure() {
    let f = Fixture::new();
    write(&f.first, "Unrelated/Corrupt.olean", b"not an olean");
    success(f.command(&[]));
    f.original();
}
#[test]
fn imports_are_rechecked_instead_of_trusted() {
    let f = Fixture::new();
    write(
        &f.second,
        "Lib/Middle.olean",
        encode(&["Lib.Base"], &[definition(false)], false),
    );
    for jobs in ["1", "4"] {
        let text = refusal(f.command(&["--jobs", jobs]), 1);
        assert!(text.contains("kernel-rejection"), "{text}");
    }
}
#[test]
fn missing_transitive_import_is_not_replaced_with_source_or_ambient_imports() {
    let f = Fixture::new();
    write(
        &f.second,
        "Lib/Middle.olean",
        encode(&["Absent"], &[definition(true)], false),
    );
    write(&f.first, "Absent.lean", b"prelude\naxiom P : Prop\n");
    let text = refusal(f.command(&[]), 1);
    assert!(text.contains("Absent"), "{text}");
}
#[test]
fn dependency_cycles_are_rejected_by_the_native_module_graph() {
    let f = Fixture::new();
    write(&f.first, "Lib/Base.olean", encode(&["Lib.Top"], &[], false));
    let text = refusal(f.command(&[]), 1);
    assert!(text.to_lowercase().contains("cycle"), "{text}");
}
#[test]
fn identical_duplicate_modules_and_duplicate_roots_are_refused() {
    let f = Fixture::new();
    write(&f.second, "Lib/Base.olean", &f.base);
    assert!(refusal(f.command(&[]), 1).contains("multiple search roots"));
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-module", "--json", "Lib.Base"])
        .arg(&f.first)
        .arg(&f.first)
        .output()
        .unwrap();
    assert!(refusal(out, 1).contains("same search root"));
}
#[test]
fn the_combined_capture_budget_is_not_reset_for_each_import() {
    let f = Fixture::new();
    let bytes = f.base.len() + f.mid.len() + f.top.len();
    success(f.command(&["--max-bytes", &bytes.to_string()]));
    for size in [0, bytes - 1] {
        assert!(refusal(f.command(&["--max-bytes", &size.to_string()]), 3).contains("resource"));
    }
}
#[test]
fn incomplete_and_cross_root_companion_chains_never_get_a_verdict() {
    let f = Fixture::new();
    write(&f.second, "Lib/Top.olean", encode(&[], &[], true));
    let text = refusal(f.command(&[]), 1);
    assert!(
        text.contains("missing .olean.server and .olean.private"),
        "{text}"
    );
    write(&f.first, "Lib/Top.olean.server", encode(&[], &[], true));
    assert!(refusal(f.command(&[]), 1).contains("orphan companion"));
}
#[test]
fn incompatible_artifact_epoch_is_refused_before_any_success() {
    let f = Fixture::new();
    let mut bytes = f.base.clone();
    bytes[7] = b'9';
    write(&f.first, "Lib/Base.olean", bytes);
    let text = refusal(f.command(&[]), 1);
    assert!(text.contains("decode"), "{text}");
}
#[cfg(unix)]
#[test]
fn directory_and_artifact_symlinks_cannot_escape_explicit_roots() {
    use std::os::unix::fs::symlink;
    let f = Fixture::new();
    let linked = f.dir.join("linked");
    std::fs::create_dir(&linked).unwrap();
    symlink(f.first.join("Lib"), linked.join("Lib")).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-module", "--json", "Lib.Base"])
        .arg(&linked)
        .output()
        .unwrap();
    assert!(refusal(out, 1).contains("symlink"));
    let direct = f.dir.join("direct");
    std::fs::create_dir_all(direct.join("Lib")).unwrap();
    symlink(
        f.first.join("Lib/Base.olean"),
        direct.join("Lib/Base.olean"),
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-module", "--json", "Lib.Base"])
        .arg(&direct)
        .output()
        .unwrap();
    assert!(refusal(out, 1).contains("symlink"));
}
#[test]
fn bad_cli_arguments_fail_without_claiming_a_check() {
    for args in [
        vec![],
        vec!["--jobs=0", "X", "root"],
        vec!["--jobs=65", "X", "root"],
        vec!["--max-bytes=-1", "X", "root"],
        vec!["../X", "root"],
        vec!["X..Y", "root"],
        vec!["/X", "root"],
        vec!["--jobs=1", "--jobs=2", "X", "root"],
        vec!["--max-bytes=1", "--max-bytes=2", "X", "root"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-module", "--json"])
            .args(args)
            .output()
            .unwrap();
        refusal(out, 2);
    }
    let help = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-module", "--help"])
        .output()
        .unwrap();
    assert!(help.status.success());
    assert!(
        String::from_utf8(help.stdout)
            .unwrap()
            .contains("transitive import")
    );
}
#[test]
fn actual_native_lake_output_is_accepted_without_replaying_source() {
    let f = Fixture::new();
    let project = f.dir.join("project");
    write(
        &project,
        "lakefile.toml",
        "name = \"audit\"\n[[lean_lib]]\nname = \"Demo\"\n",
    );
    write(
        &project,
        "Demo/Base.lean",
        "prelude\ndef Demo.id (P : Prop) (h : P) : P := h\n",
    );
    write(
        &project,
        "Demo.lean",
        "prelude\nimport Demo.Base\ntheorem Demo.identity (P : Prop) (h : P) : P := Demo.id P h\n",
    );
    let out = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&project)
        .args(["build", "+Demo:olean"])
        .env("LEAN_PATH", f.dir.join("no-imports"))
        .env("FLN_IMPORT_REUSE_DIR", f.dir.join("native-build-cache"))
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    write(
        &project,
        "Demo.lean",
        "this source is now deliberately invalid",
    );
    let checked = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-module", "--json", "Demo"])
        .arg(project.join(".lake/build/lib/lean"))
        .output()
        .unwrap();
    let text = success(checked);
    assert!(text.contains("\"moduleCount\":2"), "{text}");
    assert!(text.contains("\"axiomDeclarations\":0"), "{text}");
}
