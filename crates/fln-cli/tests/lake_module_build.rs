//! Installed Lake module builds, real codec inspection and downstream imports.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Package(PathBuf);
impl Package {
    fn new(config: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-lake-modules-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        let package = Self(path);
        package.write("lakefile.toml", config);
        package
    }
    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    fn build(&self, targets: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&self.0)
            .args(["--json", "build"])
            .args(targets)
            .env("LEAN_PATH", self.0.join("no-imports"))
            // A store of the package's own, never the user's (bead `franken_lean-z8j.1.1`).
            .env("FLN_IMPORT_REUSE_DIR", self.0.join(".records"))
            .output()
            .unwrap()
    }
    fn artifact(&self, module: &str) -> PathBuf {
        self.0
            .join(".lake/build/lib/lean")
            .join(format!("{}.olean", module.replace('.', "/")))
    }
}
impl Drop for Package {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const CONFIG: &str = "name = \"checked\"\ndefaultTargets = [\"Library\"]\n[[lean_lib]]\nname = \"Library\"\nroots = [\"Lib\"]\n";
const BASE: &str = "prelude\ndef Lib.identity (A : Type) (a : A) : A := a\n";
const TOP: &str = "prelude\nimport Lib.Base\ndef Lib.again (A : Type) (a : A) : A := Lib.identity A a\ntheorem Lib.proof (P : Prop) (h : P) : P := h\n";
const MODULE_BASE: &str = "module\nprelude\npublic inductive Token where\n | left\n | right\nprivate def hidden (x : Token) : Token := x\n@[expose] public def identity (x : Token) : Token := x\nprivate theorem localProof (P : Prop) (h : P) : P := h\npublic theorem keep (P : Prop) (h : P) : P := localProof P h\n";
const MODULE_TOP: &str = "module\nprelude\npublic import Lib.Base\npublic theorem forwards (P : Prop) (h : P) : P := keep P h\n";
const FAMILY_PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

fn success(output: &Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    String::from_utf8(output.stdout.clone()).unwrap()
}
fn failure(output: &Output) -> String {
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    String::from_utf8(output.stderr.clone()).unwrap()
}
fn inspect(path: &Path) -> String {
    success(
        &Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["olean", "inspect", "--constants"])
            .arg(path)
            .output()
            .unwrap(),
    )
}
fn library() -> Package {
    let package = Package::new(CONFIG);
    package.write("Lib/Base.lean", BASE);
    package.write("Lib/Top.lean", TOP);
    package
}

fn module_library() -> Package {
    let package = Package::new(CONFIG);
    package.write("Lib/Base.lean", MODULE_BASE);
    package.write("Lib/Top.lean", MODULE_TOP);
    package
}

#[test]
fn unsupported_ir_facet_preserves_the_previous_admission_artifacts() {
    let package = module_library();
    success(&package.build(&["+Lib.Top:olean"]));
    let previous: Vec<_> = ["Lib.Base", "Lib.Top"]
        .into_iter()
        .map(|name| family_bytes(&package, name))
        .collect();
    let report = failure(&package.build(&["+Lib.Top:ir"]));
    assert!(report.contains("source export carrier"), "{report}");
    for (name, original) in ["Lib.Base", "Lib.Top"].into_iter().zip(previous) {
        assert_eq!(family_bytes(&package, name), original);
        assert!(!package.artifact(name).with_extension("ir").exists());
    }
    assert!(
        !package
            .0
            .join(".lake/build/lib/lean/.fln-olean-build.lock")
            .exists()
    );
}

#[test]
fn legacy_nat_modules_refuse_unusable_standalone_ir_without_replacing_artifacts() {
    let package = Package::new(CONFIG);
    package.write(
        "Lib/Top.lean",
        concat!(
            "prelude\n",
            "inductive Nat where | zero | succ (n : Nat)\n",
            "def Lib.answer : Nat := Nat.zero\n",
        ),
    );
    success(&package.build(&["+Lib.Top:olean"]));
    let artifact = package.artifact("Lib.Top");
    let previous = std::fs::read(&artifact).unwrap();
    let snapshot = package.0.join(".lake/build/fln-build.snapshot");
    let previous_snapshot = std::fs::read(&snapshot).unwrap();
    let report = failure(&package.build(&["+Lib.Top:ir"]));
    assert!(
        report.contains("standalone IR requires a module-system file"),
        "{report}"
    );
    assert_eq!(std::fs::read(&artifact).unwrap(), previous);
    assert_eq!(std::fs::read(&snapshot).unwrap(), previous_snapshot);
    assert!(!artifact.with_extension("ir").exists());
    assert!(
        !package
            .0
            .join(".lake/build/lib/lean/.fln-olean-build.lock")
            .exists()
    );
}

#[test]
fn native_ir_facets_build_dependencies_and_execute_in_the_pinned_reference() {
    let Some(reference) = pinned_family_reference() else {
        return;
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| reference.parent().unwrap().join("../lib/lean"));
    let package = Package::new(CONFIG);
    package.write(
        "Lib/Base.lean",
        concat!(
            "module\nprelude\npublic import Init.Notation\n",
            "@[expose] public def Lib.choose (b : Bool) (x y : Nat) : Nat := if b then x else y\n",
            "public def Lib.answer : Nat := 42\n",
        ),
    );
    package.write(
        "Lib/Top.lean",
        concat!(
            "module\nprelude\npublic import Lib.Base\n",
            "@[expose] public def Lib.increment (n : Nat) : Nat := Nat.add n 1\n",
            "@[expose] public def Lib.selection : Nat := Lib.choose true 41 6\n",
        ),
    );
    let build = || {
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&package.0)
            .args(["--json", "build", "+Lib.Top:ir", "+Lib.Base:olean"])
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", package.0.join(".records"))
            .output()
            .unwrap()
    };
    let report = success(&build());
    assert!(report.contains("\"modules_built\":2"), "{report}");
    assert!(report.contains("\"facet\":\"ir\""), "{report}");
    assert!(report.contains("\"executable_modules\":2"), "{report}");
    let mut originals = Vec::new();
    for name in ["Lib.Base", "Lib.Top"] {
        let path = package.artifact(name).with_extension("ir");
        assert!(report.contains(&path.display().to_string()), "{report}");
        let bytes = std::fs::read(&path).unwrap();
        let view = fln_olean::region::OleanView::parse(&bytes).unwrap();
        let blocks = view
            .extension_payloads(fln_olean::region::WalkBudget::default(), 16 << 20)
            .unwrap();
        let ir =
            fln_olean::ir::decode_ir(&blocks, fln_olean::ir::IrDecodeLimits::default()).unwrap();
        assert!(!ir.decls.is_empty());
        assert!(ir.initializers.is_empty());
        originals.push(bytes);
    }
    // Re-encoding a checked cache hit must replace the entire family, including
    // executable code, without treating disk IR as checked compiler input.
    success(&build());
    for (name, original) in ["Lib.Base", "Lib.Top"].into_iter().zip(&originals) {
        assert_eq!(
            &std::fs::read(package.artifact(name).with_extension("ir")).unwrap(),
            original
        );
    }
    package.write(
        "Consumer.lean",
        concat!(
            "import Lib.Top\n",
            "#eval Lib.answer\n",
            "#eval Lib.choose true 41 6\n",
            "#eval Lib.choose false 41 6\n",
            "#eval Lib.increment 41\n",
            "#eval Lib.selection\n",
        ),
    );
    let output = Command::new(&reference)
        .arg(package.0.join("Consumer.lean"))
        .current_dir(&package.0)
        .env("LEAN_PATH", package.0.join(".lake/build/lib/lean"))
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "42\n41\n6\n42\n41\n"
    );
    // Runtime lookup prevents `[expose]` companion bodies from being inlined
    // into the consumer. The interpreter must load these exact emitted IR
    // functions, including the Boolean source ABI and both case arms.
    package.write(
        "Runtime.lean",
        concat!(
            "import Lean\n",
            "unsafe def main : IO Unit := do\n",
            "  Lean.enableInitializersExecution\n",
            "  let env ← Lean.importModules #[{ module := `Lib.Top, isMeta := true }] {} (loadExts := true)\n",
            "  match env.evalConst Nat {} `Lib.answer (checkMeta := false) with\n",
            "  | .ok answer => IO.println answer\n",
            "  | .error message => throw (IO.userError message)\n",
            "  match env.evalConst (Bool → Nat → Nat → Nat) {} `Lib.choose (checkMeta := false),\n",
            "        env.evalConst (Nat → Nat) {} `Lib.increment (checkMeta := false) with\n",
            "  | .ok choose, .ok increment =>\n",
            "    IO.println (choose true 41 6)\n",
            "    IO.println (choose false 41 6)\n",
            "    IO.println (increment 41)\n",
            "  | .error message, _ => throw (IO.userError message)\n",
            "  | _, .error message => throw (IO.userError message)\n",
        ),
    );
    let interpret = || {
        let output = Command::new(&reference)
            .args(["--run", "Runtime.lean"])
            .current_dir(&package.0)
            .env("LEAN_PATH", package.0.join(".lake/build/lib/lean"))
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        String::from_utf8(output.stdout).unwrap()
    };
    assert_eq!(interpret(), "42\n41\n6\n42\n");

    // Change only the source-facing entry, preserving its checked logical
    // companion and every internal helper. Direct lookup must observe 99.
    use fln_olean::ir::write::{IrWriteInput, IrWriteLimits, encode_ir};
    use fln_olean::ir::{IrArg, IrBody, IrDecl, IrExpr, IrLit, IrNat, IrStmt, IrTerminal};
    use fln_olean::write::{ModuleWriteInput, OleanWriteHeader};
    let original = &originals[1];
    let view = fln_olean::region::OleanView::parse(original).unwrap();
    let metadata = view
        .module_data(fln_olean::region::WalkBudget::default())
        .unwrap();
    let blocks = view
        .extension_payloads(fln_olean::region::WalkBudget::default(), 16 << 20)
        .unwrap();
    let mut ir = fln_olean::ir::decode_ir(&blocks, Default::default()).unwrap();
    let exported = ir
        .decls
        .iter_mut()
        .find(|declaration| declaration.name().to_display_string() == "Lib.increment")
        .unwrap();
    let IrDecl::Function {
        params,
        result,
        body,
        ..
    } = exported
    else {
        panic!("compiled source function")
    };
    assert_eq!(params.len(), 1);
    assert!(!params[0].borrow);
    let returned = params[0].x + 1;
    *body = IrBody {
        stmts: vec![
            IrStmt::Dec {
                x: params[0].x,
                n: 1,
                checked: true,
                persistent: false,
            },
            IrStmt::VDecl {
                x: returned,
                ty: result.clone(),
                expr: IrExpr::Lit(IrLit::Num(IrNat::Small(99))),
            },
        ],
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(returned))),
    };
    let extra_names = view
        .extra_const_names(fln_olean::region::WalkBudget::default())
        .unwrap();
    let mutant = encode_ir(
        IrWriteInput {
            module: ModuleWriteInput {
                is_module: metadata.is_module,
                imports: &metadata.imports,
                constants: &[],
                extra_const_names: &extra_names,
            },
            declarations: &ir.decls,
            initializers: &ir.initializers,
            additional_extensions: &[],
        },
        OleanWriteHeader {
            version: view.header.version,
            flags: view.header.flags,
            lean_version: &view.header.lean_version,
            githash: &view.header.githash,
            base_addr: view.header.base_addr,
        },
        IrWriteLimits::default(),
    )
    .unwrap();
    let output_ir = package.artifact("Lib.Top").with_extension("ir");
    std::fs::write(&output_ir, &mutant.bytes).unwrap();
    assert_eq!(interpret(), "42\n41\n6\n99\n");
    std::fs::write(output_ir, original).unwrap();
    // Imported HAdd carries a runtime dictionary; explicit Nat.add has the
    // supported primitive ABI. Refusing that still-unsupported dictionary and
    // a later source error must preserve every last-good output and snapshot.
    let families: Vec<_> = ["Lib.Base", "Lib.Top"]
        .into_iter()
        .map(|name| family_bytes(&package, name))
        .collect();
    let snapshot = package.0.join(".lake/build/fln-build.snapshot");
    let previous_snapshot = std::fs::read(&snapshot).unwrap();
    for (source, unsupported_dictionary) in [
        (
            "module\nprelude\npublic import Lib.Base\npublic def Lib.increment (n : Nat) : Nat := n + 1\n",
            true,
        ),
        (
            "module\nprelude\npublic import Lib.Base\npublic def bad : Nat := true\n",
            false,
        ),
    ] {
        package.write("Lib/Top.lean", source);
        let failed = build();
        assert!(!failed.status.success(), "{failed:?}");
        if unsupported_dictionary {
            let report = failure(&failed);
            assert!(
                report.contains("internal decision constructor layout"),
                "{report}"
            );
            assert!(report.contains("\"class\":\"unsupported\""), "{report}");
        }
        for (index, name) in ["Lib.Base", "Lib.Top"].into_iter().enumerate() {
            assert_eq!(family_bytes(&package, name), families[index]);
            assert_eq!(
                std::fs::read(package.artifact(name).with_extension("ir")).unwrap(),
                originals[index]
            );
        }
        assert_eq!(std::fs::read(&snapshot).unwrap(), previous_snapshot);
    }
}

#[test]
fn opaque_module_ir_preserves_opacity_and_executes_in_the_pinned_reference() {
    let Some(reference) = pinned_family_reference() else {
        return;
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| reference.parent().unwrap().join("../lib/lean"));
    let package = Package::new(CONFIG);
    let source = concat!(
        "module\nprelude\npublic import Init.Notation\n",
        "public opaque Lib.answer : Nat := 42\n",
        "public opaque Lib.choose (b : Bool) (x y : Nat) : Nat := if b then x else y\n",
    );
    package.write("Lib/Top.lean", source);
    let build = || {
        Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&package.0)
            .args(["--json", "build", "+Lib.Top:ir"])
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", package.0.join(".records"))
            .output()
            .unwrap()
    };
    let report = success(&build());
    assert!(report.contains("\"executable_modules\":1"), "{report}");
    let artifact = package.artifact("Lib.Top");
    let ir_path = artifact.with_extension("ir");
    let logical = family_bytes(&package, "Lib.Top");
    let executable = std::fs::read(&ir_path).unwrap();
    let snapshot = package.0.join(".lake/build/fln-build.snapshot");
    success(&build());
    assert_eq!(family_bytes(&package, "Lib.Top"), logical);
    assert_eq!(std::fs::read(&ir_path).unwrap(), executable);
    let previous_snapshot = std::fs::read(&snapshot).unwrap();

    // An opaque declaration cannot be inlined from its logical public body.
    // This consumer therefore needs the exact executable companion we emitted.
    let consumer = Package::new("name = \"opaque_consumer\"\n");
    consumer.write(
        "Consumer.lean",
        concat!(
            "import Lib.Top\n",
            "#eval Lib.answer\n",
            "#eval Lib.choose true 17 23\n",
            "#eval Lib.choose false 17 23\n",
        ),
    );
    let import_paths = [package.0.join(".lake/build/lib/lean"), lib.clone()];
    let search = std::env::join_paths(import_paths).unwrap();
    let output = Command::new(&reference)
        .arg(consumer.0.join("Consumer.lean"))
        .current_dir(&consumer.0)
        .env("LEAN_PATH", &search)
        .output()
        .unwrap();
    assert_eq!(success(&output), "42\n17\n23\n");

    // Both logical readers must still refuse unfolding the opaque body. The
    // reflexive control separates opacity from a broken import or tactic path.
    for (index, (body, accepted)) in [
        ("example : Lib.answer = Lib.answer := by rfl", true),
        ("example : Lib.answer = 42 := by rfl", false),
    ]
    .into_iter()
    .enumerate()
    {
        let file = consumer.0.join(format!("Opacity{index}.lean"));
        std::fs::write(
            &file,
            format!("prelude\nimport Init.Core\nimport Lib.Top\n{body}\n"),
        )
        .unwrap();
        let native = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "--import-posture", "recheck"])
            .arg(&file)
            .current_dir(&consumer.0)
            .env("LEAN_PATH", &search)
            .env("FLN_IMPORT_REUSE_DIR", consumer.0.join(".records"))
            .output()
            .unwrap();
        assert_eq!(
            native.status.code(),
            Some(if accepted { 0 } else { 1 }),
            "native opacity control: {native:?}"
        );
        let pinned = Command::new(&reference)
            .arg(&file)
            .current_dir(&consumer.0)
            .env("LEAN_PATH", &search)
            .output()
            .unwrap();
        assert_eq!(
            pinned.status.success(),
            accepted,
            "pinned opacity control: {pinned:?}"
        );
    }

    // Unsafe opaque syntax is currently refused by the frontend. A supported
    // unsafe definition reaches the separate IR safety boundary. Neither
    // refusal may replace the last-good safe opaque artifact family.
    for (declaration, diagnostic) in [
        (
            "public unsafe opaque Lib.unsafeValue : Nat := 9",
            "expected unsafe def, abbrev, or data instance without partial",
        ),
        (
            "public unsafe def Lib.unsafeValue : Nat := 9",
            "unsafe or partial source export",
        ),
    ] {
        package.write("Lib/Top.lean", format!("{source}{declaration}\n"));
        let refused = failure(&build());
        assert!(refused.contains(diagnostic), "{refused}");
        assert_eq!(family_bytes(&package, "Lib.Top"), logical);
        assert_eq!(std::fs::read(&ir_path).unwrap(), executable);
        assert_eq!(std::fs::read(&snapshot).unwrap(), previous_snapshot);
    }
}

fn family_bytes(package: &Package, module: &str) -> Vec<Vec<u8>> {
    FAMILY_PARTS
        .iter()
        .map(|part| std::fs::read(package.artifact(module).with_extension(part)).unwrap())
        .collect()
}

#[test]
fn module_families_build_rebuild_and_reimport_with_public_visibility() {
    let package = module_library();
    let targets = ["+Lib.Top:olean", "+Lib.Base:olean"];
    let report = success(&package.build(&targets));
    assert!(report.contains("\"modules_built\":2"), "{report}");
    for module in ["Lib.Base", "Lib.Top"] {
        for part in FAMILY_PARTS {
            let path = package.artifact(module).with_extension(part);
            assert!(path.is_file(), "{}", path.display());
            assert!(report.contains(&path.display().to_string()), "{report}");
        }
        assert!(!package.artifact(module).with_extension("ir").exists());
    }
    let original = family_bytes(&package, "Lib.Base");
    success(&package.build(&targets));
    assert_eq!(family_bytes(&package, "Lib.Base"), original);
    for part in FAMILY_PARTS {
        std::fs::write(package.artifact("Lib.Base").with_extension(part), b"forged").unwrap();
    }
    success(&package.build(&targets));
    assert_eq!(family_bytes(&package, "Lib.Base"), original);

    // Separate packages and processes consume only the published artifact search
    // path. No source fallback can accidentally make the companions unnecessary.
    let client = Package::new("name = \"consumer\"\n[[lean_lib]]\nname = \"Consumer\"\n");
    client.write(
        "Consumer.lean",
        "module\nprelude\npublic import Lib.Top\npublic theorem consumerProof (P : Prop) (h : P) : P := forwards P h\n",
    );
    let library = package.0.join(".lake/build/lib/lean");
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&client.0)
        .args(["--json", "build", "+Consumer:olean"])
        .env("LEAN_PATH", &library)
        .env("FLN_IMPORT_REUSE_DIR", client.0.join(".records"))
        .output()
        .unwrap();
    success(&output);
    assert_eq!(family_bytes(&client, "Consumer").len(), 3);
    let search = std::env::join_paths([client.0.join(".lake/build/lib/lean"), library]).unwrap();
    let probes = Package::new("name = \"probes\"\n");
    let cases = [
        (
            "theorem use (P : Token -> Prop) (x : Token) (h : P x) : P (identity x) := h\ntheorem useProof (P : Prop) (h : P) : P := consumerProof P h",
            true,
        ),
        (
            "theorem wrong (P : Token -> Prop) (h : P Token.left) : P (identity Token.right) := h",
            false,
        ),
        ("def stolen (x : Token) : Token := hidden x", false),
        (
            "theorem stolen (P : Prop) (h : P) : P := localProof P h",
            false,
        ),
    ];
    let reference = pinned_family_reference();
    for (index, (body, accepted)) in cases.into_iter().enumerate() {
        let file = format!("Probe{index}.lean");
        probes.write(&file, format!("module\nprelude\nimport Consumer\n{body}\n"));
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "--import-posture", "recheck"])
            .arg(probes.0.join(&file))
            .current_dir(&probes.0)
            .env("LEAN_PATH", &search)
            .env("FLN_IMPORT_REUSE_DIR", probes.0.join(".records"))
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(if accepted { 0 } else { 1 }),
            "{file}: {output:?}"
        );
        if let Some(binary) = &reference {
            let output = Command::new(binary)
                .arg(probes.0.join(&file))
                .current_dir(&probes.0)
                .env("LEAN_PATH", &search)
                .output()
                .unwrap();
            assert_eq!(
                output.status.success(),
                accepted,
                "pinned Reference {file}: {output:?}"
            );
        }
    }
}

fn pinned_family_reference() -> Option<PathBuf> {
    let row = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .unwrap();
    let field = |key: &str| {
        row.split_whitespace()
            .find_map(|word| word.strip_prefix(key))
            .unwrap()
    };
    let binary = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("FLN_REFERENCE_LIB")
                .map(|lib| PathBuf::from(lib).join("../../bin/lean"))
        })
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", field("tag=")))
                    .join("bin/lean")
            })
        })
        .filter(|binary| binary.is_file());
    let Some(binary) = binary else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required"
        );
        eprintln!("SKIP: pinned Reference absent; native artifact reimports still run");
        return None;
    };
    let output = Command::new(&binary).arg("--githash").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        field("commit=")
    );
    Some(binary)
}

#[test]
fn module_family_failures_preserve_all_previous_parts_and_ir() {
    let package = library();
    success(&package.build(&["+Lib.Top:olean"]));
    assert!(
        !package
            .artifact("Lib.Base")
            .with_extension("olean.private")
            .exists()
    );
    package.write("Lib/Base.lean", MODULE_BASE);
    package.write("Lib/Top.lean", MODULE_TOP);
    success(&package.build(&["+Lib.Top:olean"]));
    let base = family_bytes(&package, "Lib.Base");
    let top = family_bytes(&package, "Lib.Top");
    package.write(
        "Lib/Bad.lean",
        "module\nprelude\npublic theorem bad (P Q : Prop) (h : P) : Q := h\n",
    );
    failure(&package.build(&["+Lib.Top:olean", "+Lib.Bad:olean"]));
    assert_eq!(family_bytes(&package, "Lib.Base"), base);
    assert_eq!(family_bytes(&package, "Lib.Top"), top);
    for part in FAMILY_PARTS {
        assert!(!package.artifact("Lib.Bad").with_extension(part).exists());
    }
    package.write(
        "Lib/Base.lean",
        "prelude\ndef replacement (P : Prop) (h : P) : P := h\n",
    );
    assert!(failure(&package.build(&["+Lib.Base:olean"])).contains("coordinated replacement"));
    assert_eq!(family_bytes(&package, "Lib.Base"), base);
    package.write("Lib/Base.lean", MODULE_BASE);
    let ir = package.artifact("Lib.Base").with_extension("ir");
    std::fs::write(&ir, b"existing executable IR").unwrap();
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("coordinated replacement"));
    assert_eq!(std::fs::read(ir).unwrap(), b"existing executable IR");
    assert_eq!(family_bytes(&package, "Lib.Base"), base);
    assert_eq!(family_bytes(&package, "Lib.Top"), top);
}

#[test]
fn module_family_preflight_checks_every_companion_before_replacing_any_module() {
    let package = module_library();
    for part in FAMILY_PARTS {
        package.write(
            &format!(".lake/build/lib/lean/Lib/Base.{part}"),
            format!("previous {part}"),
        );
    }
    let previous = family_bytes(&package, "Lib.Base");
    std::fs::create_dir_all(package.artifact("Lib.Top").with_extension("olean.private")).unwrap();
    let error = failure(&package.build(&["+Lib.Top:olean"]));
    assert!(error.contains("not a regular file"), "{error}");
    assert_eq!(family_bytes(&package, "Lib.Base"), previous);
    assert!(!package.artifact("Lib.Top").exists());
    assert!(
        !package
            .artifact("Lib.Top")
            .with_extension("olean.server")
            .exists()
    );
}

#[cfg(unix)]
#[test]
fn dangling_ir_and_companion_symlinks_cannot_bypass_family_preflight() {
    for part in ["ir", "olean.server", "olean.private"] {
        let package = module_library();
        package.write(
            ".lake/build/lib/lean/Lib/Base.olean",
            "previous public root",
        );
        std::os::unix::fs::symlink(
            package.0.join("absent"),
            package.artifact("Lib.Base").with_extension(part),
        )
        .unwrap();
        assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("symlink"));
        assert_eq!(
            std::fs::read(package.artifact("Lib.Base")).unwrap(),
            b"previous public root"
        );
        assert!(!package.artifact("Lib.Top").exists());
    }
}

#[test]
fn builds_real_module_closure_and_downstream_source_imports_it() {
    let package = library();
    let report = success(&package.build(&["+Lib.Top:olean"]));
    assert!(report.contains("\"modules_built\":2"), "{report}");
    assert!(report.contains("\"modules_cached\":0"), "{report}");
    let base = inspect(&package.artifact("Lib.Base"));
    let top = inspect(&package.artifact("Lib.Top"));
    assert!(base.contains("Lib.identity"), "{base}");
    assert!(top.contains("Lib.again"), "{top}");
    assert!(
        !top.contains("Lib.identity"),
        "imported declarations were duplicated: {top}"
    );

    let consumer = Package::new("name = \"consumer\"\n[[lean_lib]]\nname = \"Consumer\"\n");
    consumer.write(
        "Consumer.lean",
        "prelude\nimport Consumer.Helper\ndef downstream (A : Type) (a : A) : A := Consumer.forward A a\n",
    );
    consumer.write(
        "Consumer/Helper.lean",
        "prelude\nimport Lib.Top\ndef Consumer.forward (A : Type) (a : A) : A := Lib.again A a\n",
    );
    let out = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&consumer.0)
        .args(["--json", "build", "+Consumer:olean"])
        .env("LEAN_PATH", package.0.join(".lake/build/lib/lean"))
        .env("FLN_IMPORT_REUSE_DIR", consumer.0.join(".records"))
        .output()
        .unwrap();
    success(&out);
    assert!(inspect(&consumer.artifact("Consumer")).contains("downstream"));
    assert!(inspect(&consumer.artifact("Consumer.Helper")).contains("Consumer.forward"));

    let client = Package::new("name = \"client\"\n");
    client.write(
        "Use.lean",
        "prelude\nimport Consumer\ntheorem imported (P : Prop) (h : P) : P := Lib.proof P h\n",
    );
    let search = std::env::join_paths([
        consumer.0.join(".lake/build/lib/lean"),
        package.0.join(".lake/build/lib/lean"),
    ])
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--import-posture", "recheck"])
        .arg(client.0.join("Use.lean"))
        .env("LEAN_PATH", search)
        .output()
        .unwrap();
    let report = success(&out);
    assert!(
        report.contains("\"trust\":\"recheck\",\"admission\":\"council\""),
        "{report}"
    );
}

#[test]
fn rebuilds_changed_bytes_and_never_trusts_forged_or_stale_outputs() {
    let package = library();
    package.write(
        ".lake/build/lib/lean/Lib/Base.olean",
        "fln-olean-artifact:Lib.Base",
    );
    success(&package.build(&["Lib.Top:olean"]));
    let original = std::fs::read(package.artifact("Lib.Base")).unwrap();
    let source_modified = std::fs::metadata(package.0.join("Lib/Base.lean"))
        .unwrap()
        .modified()
        .unwrap();
    success(&package.build(&["Lib.Top:olean"]));
    assert_eq!(
        std::fs::read(package.artifact("Lib.Base")).unwrap(),
        original
    );
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.second (A : Type) (a : A) : A := a\n"),
    );
    std::fs::File::options()
        .write(true)
        .open(package.0.join("Lib/Base.lean"))
        .unwrap()
        .set_times(std::fs::FileTimes::new().set_modified(source_modified))
        .unwrap();
    success(&package.build(&["Lib.Top:olean"]));
    assert_ne!(
        std::fs::read(package.artifact("Lib.Base")).unwrap(),
        original
    );
    assert!(inspect(&package.artifact("Lib.Base")).contains("Lib.second"));
}

#[test]
fn source_failure_and_multiple_target_failure_preserve_every_previous_artifact() {
    let package = library();
    success(&package.build(&["+Lib.Top:olean"]));
    let base = std::fs::read(package.artifact("Lib.Base")).unwrap();
    let top = std::fs::read(package.artifact("Lib.Top")).unwrap();
    for invalid in [
        "this is not Lean (((",
        "theorem falseProof (P : Prop) : P := by rfl",
    ] {
        package.write("Lib/Base.lean", format!("prelude\n{invalid}\n"));
        let error = failure(&package.build(&["+Lib.Top:olean"]));
        assert!(error.contains("Lib.Base"), "{error}");
        assert_eq!(std::fs::read(package.artifact("Lib.Base")).unwrap(), base);
        assert_eq!(std::fs::read(package.artifact("Lib.Top")).unwrap(), top);
    }
    package.write(
        "Lib/Base.lean",
        format!("{BASE}def Lib.newValue (A : Type) (a : A) : A := a\n"),
    );
    package.write("Lib/Bad.lean", "prelude\ninvalid !!!\n");
    failure(&package.build(&["+Lib.Top:olean", "+Lib.Bad:olean"]));
    assert_eq!(std::fs::read(package.artifact("Lib.Base")).unwrap(), base);
    assert!(!package.artifact("Lib.Bad").exists());
    success(&package.build(&["+Lib.Top:olean"]));
}

#[test]
fn respects_declared_roots_directories_and_does_not_check_unrelated_source() {
    let package = Package::new(
        "name = \"dirs\"\nsrcDir = \"src\"\nbuildDir = \"products\"\n[[lean_lib]]\nname = \"OtherName\"\nroots = [\"Lib\"]\nsrcDir = \"proofs\"\n",
    );
    package.write("src/proofs/Lib/Base.lean", BASE);
    package.write("src/proofs/Lib/Top.lean", TOP);
    package.write("src/proofs/Lib/Unrelated.lean", "garbage !!!");
    success(&package.build(&["+Lib.Top:olean"]));
    assert!(package.0.join("products/lib/lean/Lib/Top.olean").is_file());
    assert!(
        !package
            .0
            .join("products/lib/lean/Lib/Unrelated.olean")
            .exists()
    );
    let error = failure(&package.build(&["+Outside:olean"]));
    assert!(error.contains("declared lean_lib"), "{error}");
}

#[test]
fn refuses_incomplete_facets_unhandled_settings_and_missing_implicit_init() {
    let package = library();
    for args in [
        vec![],
        vec!["Library"],
        vec!["+Lib.Top:c"],
        vec!["+Lib.Top:olean", "--no-build"],
    ] {
        let error = failure(&package.build(&args));
        assert!(error.contains("unavailable"), "{error}");
        assert!(!package.0.join(".lake").exists());
    }
    // TOML defaults name declared targets, not CLI module/facet expressions.
    package.write(
        "lakefile.toml",
        CONFIG.replace("[\"Library\"]", "[\"+Lib.Top:olean\"]"),
    );
    failure(&package.build(&[]));
    assert!(!package.0.join(".lake").exists());
    package.write("lakefile.toml", CONFIG);
    package.write("Lib/Base.lean", "def plain (A : Type) (a : A) : A := a\n");
    let error = failure(&package.build(&["+Lib.Base:olean"]));
    assert!(
        error.contains("Init") && error.contains("search path"),
        "{error}"
    );
    assert!(!package.0.join(".lake").exists());
    for setting in [
        "globs = [\"Lib.*\"]",
        "precompileModules = true",
        "moreLeanArgs = [\"-DautoImplicit=false\"]",
    ] {
        package.write("lakefile.toml", format!("{CONFIG}{setting}\n"));
        let error = failure(&package.build(&["+Lib.Top:olean"]));
        assert!(error.contains("unsupported"), "{error}");
        assert!(!package.0.join(".lake").exists());
    }
}

#[test]
fn cycles_leaked_sibling_declarations_and_resource_overflow_never_publish() {
    let package = library();
    package.write("Lib/Base.lean", "prelude\nimport Lib.Top\n");
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("cycle"));
    package.write("Lib/Base.lean", BASE);
    package.write(
        "Lib/Sibling.lean",
        "prelude\ndef leak (A : Type) (a : A) : A := Lib.identity A a\n",
    );
    package.write(
        "Lib/Top.lean",
        "prelude\nimport Lib.Base\nimport Lib.Sibling\n",
    );
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("Lib.Sibling"));
    package.write("Lib/Base.lean", vec![b' '; 1024 * 1024 + 1]);
    let exhausted = package.build(&["+Lib.Base:olean"]);
    assert_eq!(exhausted.status.code(), Some(3), "{exhausted:?}");
    assert!(exhausted.stdout.is_empty(), "{exhausted:?}");
    let error = String::from_utf8(exhausted.stderr).unwrap();
    assert!(error.contains("\"status\":\"inconclusive\""), "{error}");
    assert!(error.contains("\"class\":\"resource\""), "{error}");
    assert!(error.contains("\"authority\":false"), "{error}");
    assert!(!package.0.join(".lake").exists());
}

#[test]
fn output_preflight_refuses_bad_destinations_before_replacing_any_artifact() {
    let package = library();
    package.write(".lake/build/lib/lean/Lib/Base.olean", "previous artifact");
    std::fs::create_dir_all(package.artifact("Lib.Top")).unwrap();
    let error = failure(&package.build(&["+Lib.Top:olean"]));
    assert!(error.contains("not a regular file"), "{error}");
    assert_eq!(
        std::fs::read(package.artifact("Lib.Base")).unwrap(),
        b"previous artifact"
    );
}

#[cfg(unix)]
#[test]
fn symlinked_sources_and_output_directories_are_refused() {
    let package = Package::new(CONFIG);
    let outside = Package::new(CONFIG);
    outside.write("Base.lean", BASE);
    std::fs::create_dir_all(package.0.join("Lib")).unwrap();
    std::os::unix::fs::symlink(outside.0.join("Base.lean"), package.0.join("Lib/Base.lean"))
        .unwrap();
    let error = failure(&package.build(&["+Lib.Base:olean"]));
    assert!(error.contains("symlink"), "{error}");
    assert!(!package.0.join(".lake").exists());

    let package = library();
    std::fs::create_dir_all(package.0.join(".lake/build/lib")).unwrap();
    std::os::unix::fs::symlink(&outside.0, package.0.join(".lake/build/lib/lean")).unwrap();
    assert!(failure(&package.build(&["+Lib.Top:olean"])).contains("symlink"));
    assert!(!outside.0.join("Lib/Top.olean").exists());
}

/// `lake build --jobs N` admits the external `.olean` closure N modules at a time
/// and builds the same report and the same artifact bytes at every N. The
/// consumer's closure holds two siblings that import only `Lib.Base`.
#[test]
fn external_imports_build_identically_at_one_and_several_jobs() {
    let library =
        Package::new("name = \"checked\"\n[[lean_lib]]\nname = \"Library\"\nroots = [\"Lib\"]\n");
    library.write("Lib/Base.lean", BASE);
    library.write(
        "Lib/Left.lean",
        "prelude\nimport Lib.Base\ndef Lib.left (A : Type) (a : A) : A := Lib.identity A a\n",
    );
    library.write(
        "Lib/Right.lean",
        "prelude\nimport Lib.Base\ntheorem Lib.right (P : Prop) (h : P) : P := h\n",
    );
    success(&library.build(&["+Lib.Left:olean", "+Lib.Right:olean"]));
    let built = |jobs: &str| {
        let consumer = Package::new("name = \"consumer\"\n[[lean_lib]]\nname = \"Consumer\"\n");
        consumer.write(
            "Consumer.lean",
            "prelude\nimport Lib.Left\nimport Lib.Right\ndef Consumer.value (A : Type) (a : A) : A := Lib.left A a\ntheorem Consumer.proof (P : Prop) (h : P) : P := Lib.right P h\n",
        );
        let output = Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&consumer.0)
            // The council's job count is this test's subject. Under the default
            // `reuse-verified` posture the second build would reuse the first one's
            // record and report it, so the posture is pinned (bead `fln-uyuz`).
            .args([
                "--json",
                "build",
                "--import-posture",
                "recheck",
                "--jobs",
                jobs,
                "+Consumer:olean",
            ])
            .env("LEAN_PATH", library.0.join(".lake/build/lib/lean"))
            .output()
            .unwrap();
        let report = success(&output).replace(&consumer.0.display().to_string(), "<package>");
        (
            report,
            std::fs::read(consumer.artifact("Consumer")).unwrap(),
        )
    };
    let serial = built("1");
    assert!(serial.0.contains("\"modules_built\":1"), "{}", serial.0);
    for jobs in ["2", "5"] {
        assert_eq!(built(jobs), serial, "--jobs {jobs}");
    }

    let refused = failure(
        &Command::new(env!("CARGO_BIN_EXE_lake"))
            .arg("--dir")
            .arg(&library.0)
            .args(["--json", "build", "--jobs", "0", "+Lib.Left:olean"])
            .output()
            .unwrap(),
    );
    assert!(
        refused.contains("--jobs takes a positive thread count"),
        "{refused}"
    );
}

/// A source module's own `protected` declarations survive into the `.olean` Lake
/// builds (bead `fln-eq4k`): the pin's `protectedExt` block, sorted by
/// `Name.quickLt` as the pin writes it and binary-searches it. Two readers then
/// agree on a consumer: FrankenLean's `check-source` and, when installed, the
/// pinned Reference `lean` itself, which refuses each tag's atomic name under
/// `open` and accepts the qualified name and the unprotected sibling.
#[test]
fn protected_declarations_survive_into_the_olean_for_both_readers() {
    let package = Package::new(CONFIG);
    package.write(
        "Lib/Guard.lean",
        "prelude\nnamespace Lib\nprotected def one (P : Prop) (h : P) : P := h\n\
         protected def two (P : Prop) (h : P) : P := h\n\
         protected theorem three (P : Prop) (h : P) : P := h\n\
         def plain (P : Prop) (h : P) : P := h\nend Lib\n",
    );
    success(&package.build(&["+Lib.Guard:olean"]));
    let bytes = std::fs::read(package.artifact("Lib.Guard")).unwrap();
    let blocks = fln_olean::region::OleanView::parse(&bytes)
        .unwrap()
        .extension_payloads(fln_olean::region::WalkBudget::default(), 1 << 20)
        .unwrap();
    let decoded = fln_olean::source_extensions::decode(
        &blocks,
        fln_olean::source_extensions::DecodeLimits::default(),
    )
    .unwrap();
    let mut expected: Vec<_> = ["Lib.one", "Lib.two", "Lib.three"]
        .map(|name| fln_core::name::Name::from_components(name.split('.')))
        .into();
    expected.sort_by(|left, right| left.quick_cmp(right));
    assert_eq!(decoded.protected, expected, "written in Name.quickLt order");

    let client = Package::new("name = \"client\"\n");
    // Inside `namespace Lib`, not under `open Lib`: the pin's resolution rule is the
    // same at the current namespace, and `open Lib` would test something else. A
    // FrankenLean-written olean records no `namespacesExt` entry, so the pin refuses
    // `open Lib` itself as an "unknown namespace", whatever the tags say.
    let consumer =
        |body: &str| format!("prelude\nimport Lib.Guard\nnamespace Lib\n{body}\nend Lib\n");
    // (program body, the pin's verdict on it)
    let cases = [
        ("theorem u (P : Prop) (h : P) : P := one P h", false),
        ("theorem u (P : Prop) (h : P) : P := two P h", false),
        ("theorem u (P : Prop) (h : P) : P := three P h", false),
        ("theorem u (P : Prop) (h : P) : P := Lib.one P h", true),
        ("theorem u (P : Prop) (h : P) : P := plain P h", true),
    ];
    let lib = package.0.join(".lake/build/lib/lean");
    let pinned = std::env::var_os("HOME")
        .map(|home| PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0"))
        .filter(|root| root.join("bin/lean").is_file());
    assert!(
        pinned.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
    );
    for (index, (body, accepted)) in cases.iter().enumerate() {
        let file = format!("Use{index}.lean");
        client.write(&file, consumer(body));
        let fln = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "--import-posture", "recheck"])
            .arg(client.0.join(&file))
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", client.0.join(".records"))
            .output()
            .unwrap();
        assert_eq!(fln.status.success(), *accepted, "fln on {body}: {fln:?}");
        let Some(root) = &pinned else {
            eprintln!("SKIP: pinned Reference absent; FrankenLean's verdict only");
            continue;
        };
        let search = std::env::join_paths([lib.clone(), root.join("lib/lean")]).unwrap();
        let lean = Command::new(root.join("bin/lean"))
            .arg(client.0.join(&file))
            .env("LEAN_PATH", search)
            .output()
            .unwrap();
        assert_eq!(
            lean.status.success(),
            *accepted,
            "the pinned lean on {body}, reading FrankenLean's olean: {lean:?}"
        );
        if !accepted {
            // Refused because the tag held the atomic name back, nothing else.
            let said = String::from_utf8_lossy(&lean.stdout);
            assert!(
                said.contains("Unknown identifier"),
                "the pinned lean refused {body} for another reason: {said}"
            );
        }
    }
}

#[test]
fn export_alias_libraries_build_and_resolve_through_physical_lake_outputs() {
    let package = Package::new(CONFIG);
    package.write("Lib/Base.lean","prelude\nnamespace Original\ninductive Token where | mk\ndef identity (x : Token) : Token := x\nend Original\nexport Original (Token identity)");
    package.write("Lib.lean","prelude\nimport Lib.Base\nnamespace Facade.Inner\nexport Original (Token identity)\nend Facade.Inner");
    success(&package.build(&["+Lib:olean"]));
    let base = std::fs::read(package.artifact("Lib.Base")).unwrap();
    let bridge = std::fs::read(package.artifact("Lib")).unwrap();
    assert_eq!(&bridge[..5], b"olean");
    success(&package.build(&["+Lib:olean"]));
    assert_eq!(std::fs::read(package.artifact("Lib.Base")).unwrap(), base);
    assert_eq!(std::fs::read(package.artifact("Lib")).unwrap(), bridge);
    let client = Package::new("name = \"aliasclient\"\n");
    client.write("Use.lean","prelude\nimport Lib\nopen Facade.Inner\ntheorem useAlias (P : Token -> Prop) (x : Token) (h : P x) : P (identity x) := h");
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--import-posture", "recheck"])
        .arg(client.0.join("Use.lean"))
        .env("LEAN_PATH", package.0.join(".lake/build/lib/lean"))
        .env("FLN_IMPORT_REUSE_DIR", client.0.join(".records"))
        .output()
        .unwrap();
    let report = success(&out);
    assert!(
        report.contains("\"trust\":\"recheck\",\"admission\":\"council\""),
        "{report}"
    );
}

#[test]
fn scoped_instance_libraries_build_and_keep_scope_activation_after_import() {
    let package = Package::new(CONFIG);
    package.write(
        "Lib/Base.lean",
        "prelude\ninductive Token where | left | right\nclass Pick where\n  value : Token\n\
         instance fallback : Pick := Pick.mk Token.left\nnamespace Regional\n\
         scoped instance preferred : Pick := Pick.mk Token.right\nend Regional\n",
    );
    package.write("Lib.lean", "prelude\nimport Lib.Base\n");
    success(&package.build(&["+Lib:olean"]));
    let bytes = std::fs::read(package.artifact("Lib.Base")).unwrap();
    success(&package.build(&["+Lib:olean"]));
    assert_eq!(std::fs::read(package.artifact("Lib.Base")).unwrap(), bytes);
    let client = Package::new("name = \"scopedclient\"\n");
    let library = package.0.join(".lake/build/lib/lean");
    let reference = std::env::var_os("FLN_REFERENCE_BIN")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
            })
        })
        .filter(|binary| binary.is_file());
    assert!(
        reference.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
    );
    let check_reference = |file: &str, accepted: bool| {
        let Some(binary) = &reference else {
            eprintln!("SKIP: pinned Reference absent; FrankenLean's verdict only");
            return;
        };
        let reference_library = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .unwrap_or_else(|| binary.parent().unwrap().parent().unwrap().join("lib/lean"));
        let output = Command::new(binary)
            .arg(client.0.join(file))
            .env(
                "LEAN_PATH",
                std::env::join_paths([library.clone(), reference_library]).unwrap(),
            )
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            accepted,
            "pinned Reference on {file}, importing FrankenLean's scoped instance: {output:?}"
        );
    };
    for (index, (scope, expected)) in [("", "left"), ("open scoped Regional\n", "right")]
        .into_iter()
        .enumerate()
    {
        let file = format!("Use{index}.lean");
        client.write(
            &file,
            format!(
                "prelude\nimport Lib\n{scope}\
                 theorem choiceProof (P : Token -> Prop) (h : P Token.{expected}) : P Pick.value := h\n"
            ),
        );
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "--import-posture", "recheck"])
            .arg(client.0.join(&file))
            .env("LEAN_PATH", &library)
            .env("FLN_IMPORT_REUSE_DIR", client.0.join(".records"))
            .output()
            .unwrap();
        success(&output);
        check_reference(&file, true);
    }
    client.write(
        "Wrong.lean",
        "prelude\nimport Lib\nopen scoped Regional\n\
         theorem wrongProof (P : Token -> Prop) (h : P Token.left) : P Pick.value := h\n",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--import-posture", "recheck"])
        .arg(client.0.join("Wrong.lean"))
        .env("LEAN_PATH", &library)
        .env("FLN_IMPORT_REUSE_DIR", client.0.join(".records"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    check_reference("Wrong.lean", false);
}
