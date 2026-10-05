//! Installed source checking and Lake builds activate checked import metadata.
//! Fixtures are real serialized module bytes, never trusted engine shortcuts.
#![forbid(unsafe_code)]
use fln::*;
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::{
    convert::{inject_expr, inject_name},
    obj::Obj,
};
use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

const CLASS: &str = "Lean.classExtension";
const INSTANCE: &str = "Lean.Meta.instanceExtension";
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}
fn axiom(name: &str, ty: Expr) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: ty,
        },
        is_unsafe: false,
    })
}
fn class() -> Obj {
    Obj::mk_ctor(
        0,
        vec![
            inject_name(&n("Class")),
            Obj::mk_array(vec![]),
            Obj::mk_array(vec![]),
        ],
        &[],
    )
}
fn instance(name: &str, priority: usize) -> Obj {
    let mut heap = fln_rt::native_heap::NativeHeap::new();
    let handle = heap.alloc(c(name));
    let row = Obj::mk_ctor(
        0,
        vec![
            Obj::mk_array(vec![]),
            inject_expr(&heap, handle).unwrap(),
            Obj::mk_nat(priority),
            Obj::mk_ctor(1, vec![inject_name(&n(name))], &[]),
            Obj::mk_array(vec![]),
        ],
        &[0],
    );
    Obj::mk_ctor(0, vec![row], &[])
}
fn encoded(
    constants: &[ConstantInfo],
    imports: &[&str],
    extensions: Vec<(&str, Vec<Obj>)>,
) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|s| OleanModuleImport {
            module: n(s),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    let names: Vec<_> = extensions.iter().map(|(name, _)| n(name)).collect();
    let extensions: Vec<_> = extensions
        .iter()
        .zip(&names)
        .map(|((_, entries), name)| ModuleExtensionInput { name, entries })
        .collect();
    encode_module_with_extensions(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        &extensions,
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: OLEAN_PIN_COMMIT,
            base_addr: 2 * OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
}
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "fln-cli-import-metadata-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        std::fs::create_dir(root.join("objects")).unwrap();
        Self(root)
    }
    fn write(&self, path: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    fn module(
        &self,
        name: &str,
        constants: &[ConstantInfo],
        imports: &[&str],
        metadata: Vec<(&str, Vec<Obj>)>,
    ) {
        self.write(
            &format!("objects/{name}.olean"),
            encoded(constants, imports, metadata),
        );
    }
    fn run(&self) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            // Council admission is this suite's subject, so the posture is pinned.
            .args([
                "check-source",
                "--json",
                "--import-posture",
                "recheck",
                "Main.lean",
            ])
            .current_dir(&self.0)
            .env("LEAN_PATH", self.0.join("objects"))
            .output()
            .unwrap()
    }
    fn success(&self) -> String {
        success(self.run())
    }
}
fn success(output: Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(stdout.lines().count(), 1, "{stdout}");
    stdout
}
fn fixture() -> Project {
    let p = Project::new();
    let family = Expr::forall_e(
        n("x"),
        c("Class"),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );
    p.module(
        "Core",
        &[
            axiom("Class", Expr::sort(Level::one())),
            axiom("a", c("Class")),
            axiom("b", c("Class")),
            axiom("Family", family),
            axiom("valueA", Expr::app(c("Family"), c("a"))),
            axiom("valueB", Expr::app(c("Family"), c("b"))),
        ],
        &[],
        vec![
            (CLASS, vec![class()]),
            ("Foreign.extension", vec![Obj::mk_nat(7)]),
        ],
    );
    p.module(
        "A",
        &[],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    p.module(
        "B",
        &[],
        &["Core"],
        vec![(INSTANCE, vec![instance("b", 1000)])],
    );
    p
}
fn source(imports: &str, selected: &str) -> String {
    format!(
        "prelude\nimport {imports}\ndef use [d : Class] : Class := d\ndef selected : Family use := {selected}\n"
    )
}

#[test]
fn cli_replays_dictionary_order_and_reports_uninterpreted_metadata() {
    let p = fixture();
    for (imports, selected) in [("A B", "valueB"), ("B A", "valueA")] {
        let source = source(imports, selected);
        p.write("Main.lean", &source);
        let report = p.success();
        assert!(report.contains("\"executed\":false"), "{report}");
        assert!(
            report.contains(
                "\"oleanImports\":{\"trust\":\"recheck\",\"admission\":\"council\",\"modules\":3,\"declarations\":6}"
            ),
            "{report}"
        );
        assert!(report.contains("\"classes\":1,\"instances\":2"), "{report}");
        assert!(report.contains("\"uninterpretedExtensions\":1"), "{report}");
        assert!(report.contains("\"declarationLogicalRoot\":"), "{report}");
        assert_eq!(
            std::fs::read(p.0.join("Main.lean")).unwrap(),
            source.as_bytes()
        );
        // Picking the earlier dictionary would produce the wrong dependent type.
        p.write(
            "Main.lean",
            source.replace(
                selected,
                if selected == "valueA" {
                    "valueB"
                } else {
                    "valueA"
                },
            ),
        );
        let output = p.run();
        assert!(!output.status.success(), "{output:?}");
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn imports_through_local_modules_preserve_declared_not_discovery_order() {
    let p = fixture();
    p.write("Wrapper.lean", "prelude\nimport B A\ndef wrapperUse [d : Class] : Class := d\ndef wrapperChoice : Family wrapperUse := valueA\n");
    // Filesystem discovery sees external A before visiting Wrapper. Metadata
    // replay must nevertheless visit Wrapper's B before the following A.
    p.write("Main.lean", source("Wrapper A", "valueA"));
    p.success();
    p.write("Main.lean", source("A Wrapper", "valueB"));
    p.success();
    // The wrapper's dictionary remains A even while its consumer chooses B.
    // Supplying A for the consumer is still rejected, not accepted by the
    // wrapper's otherwise correctly isolated context.
    p.write("Main.lean", source("A Wrapper", "valueA"));
    let refused = p.run();
    assert!(!refused.status.success(), "{refused:?}");
    assert!(refused.stdout.is_empty());
}

#[test]
fn invalid_metadata_and_invalid_declarations_never_publish_success() {
    let p = fixture();
    p.write("Main.lean", source("A", "valueA"));
    p.module(
        "A",
        &[],
        &["Core"],
        vec![(INSTANCE, vec![instance("missing", 1000)])],
    );
    let failed = p.run();
    assert!(!failed.status.success(), "{failed:?}");
    assert!(failed.stdout.is_empty());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("importing .olean modules"));
    p.module(
        "A",
        &[],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    p.success();
    let bad = ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n("bad"),
            level_params: vec![],
            type_: c("Class"),
        },
        value: Expr::sort(Level::one()),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n("bad")],
    });
    p.module(
        "A",
        &[bad],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    let failed = p.run();
    assert!(!failed.status.success(), "{failed:?}");
    assert!(failed.stdout.is_empty());
    p.module(
        "A",
        &[],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    p.success();
}

#[test]
fn source_cycles_remain_refusals_after_external_root_planning() {
    let p = fixture();
    p.write("Wrapper.lean", "prelude\nimport Main B\n");
    p.write("Main.lean", source("Wrapper A", "valueA"));
    let failed = p.run();
    assert!(!failed.status.success(), "{failed:?}");
    assert!(failed.stdout.is_empty());
}

#[test]
fn lake_build_uses_checked_metadata_and_original_external_import_order() {
    let p = fixture();
    p.write(
        "lakefile.toml",
        "name = \"metadata\"\n[[lean_lib]]\nname = \"Main\"\nroots = [\"Main\", \"Wrapper\"]\n",
    );
    p.write("Wrapper.lean", "prelude\nimport B A\n");
    p.write("Main.lean", source("Wrapper A", "valueA"));
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&p.0)
        .args(["--json", "build", "+Main:olean"])
        .env("LEAN_PATH", p.0.join("objects"))
        .output()
        .unwrap();
    success(output);
    let artifact = p.0.join(".lake/build/lib/lean/Main.olean");
    assert!(artifact.is_file());
    p.write(
        "Consumer.lean",
        "prelude\nimport Main\ndef downstream : Family use := selected\n",
    );
    let search =
        std::env::join_paths([p.0.join(".lake/build/lib/lean"), p.0.join("objects")]).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(p.0.join("Consumer.lean"))
        .env("LEAN_PATH", search)
        .output()
        .unwrap();
    success(output);
}

#[path = "source_olean_metadata/contexts.rs"]
mod contexts;

#[path = "source_olean_metadata/installed_contexts.rs"]
mod installed_contexts;

#[path = "source_olean_metadata/class_exports.rs"]
mod class_exports;
