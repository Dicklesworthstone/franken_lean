//! Native source metadata is compared with the actual pinned `.ilean` producer.
#![forbid(unsafe_code)]
use fln::source_check::inspect::SourceIleanLimits;
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession,
    imported::SourceOleanImport,
};
use fln::{Ilean, IleanBudget, IleanRefIdent, Name, Outcome, SourceModuleInput};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

const BASIC: &str = "prelude\naxiom T : Type\naxiom first : T\nnoncomputable def identity (x : T) : T := x\nnoncomputable def result : T := identity first\nnoncomputable def shadow (first : T) : T := first\n";

fn metadata(
    sources: &[(&str, &str)],
    entry: &str,
    limits: SourceIleanLimits,
) -> Result<Outcome<Ilean>, SourceModuleCheckError> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, || {
                let names: Vec<_> = sources
                    .iter()
                    .map(|(name, _)| Name::from_components([*name]))
                    .collect();
                let inputs: Vec<_> = names
                    .iter()
                    .zip(sources)
                    .map(|(name, (_, source))| SourceModuleInput {
                        name,
                        source: source.as_bytes(),
                    })
                    .collect();
                let admission =
                    fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(16 * 1024 * 1024));
                let mut session = SourceModuleSession::from_lean_imports(
                    SourceOleanImport::empty(&fln::KVMap::new()),
                    fln::KVMap::new(),
                    SourceModuleCheckLimits::new(fln::SourceCheckLimits::new(admission)),
                    SourceModuleCacheLimits::default(),
                );
                session.ilean(&inputs, &Name::from_components([entry]), limits)
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

fn complete(sources: &[(&str, &str)], entry: &str) -> Ilean {
    match metadata(sources, entry, SourceIleanLimits::default()).expect("checked native metadata") {
        Outcome::Complete(metadata) => metadata,
        stopped => panic!("metadata did not complete: {stopped:?}"),
    }
}

#[test]
fn resolved_references_roundtrip_and_exclude_shadowed_locals() {
    let metadata = complete(&[("Native", BASIC)], "Native");
    let first = &metadata.references[&IleanRefIdent::Const {
        module: "Native".into(),
        name: "first".into(),
    }];
    assert_eq!(first.usages.len(), 1);
    assert_eq!(first.usages[0].parent_decl.as_deref(), Some("result"));
    assert_eq!(
        first.definition.as_ref().unwrap().parent_decl.as_deref(),
        Some("first")
    );
    assert!(
        metadata.references[&IleanRefIdent::Const {
            module: "Native".into(),
            name: "identity".into()
        }]
            .definition
            .as_ref()
            .unwrap()
            .parent_decl
            .is_none()
    );
    let encoded = fln::encode_ilean(&metadata, IleanBudget::default()).unwrap();
    assert_eq!(
        fln::decode_ilean(&encoded, IleanBudget::default()).unwrap(),
        metadata
    );
    assert!(
        !metadata
            .references
            .keys()
            .any(|key| matches!(key, IleanRefIdent::FVar { .. }))
    );
}

#[test]
fn metadata_limits_and_unsupported_forms_never_return_partial_success() {
    for limits in [
        SourceIleanLimits {
            max_references: 0,
            ..Default::default()
        },
        SourceIleanLimits {
            max_name_bytes: 1,
            ..Default::default()
        },
    ] {
        assert!(!matches!(
            metadata(&[("Bounded", BASIC)], "Bounded", limits),
            Ok(Outcome::Complete(_))
        ));
    }
    let source = "prelude\naxiom P : Prop\naxiom proof : P\ntheorem t : P := by exact proof\n";
    let error = metadata(
        &[("Unsupported", source)],
        "Unsupported",
        SourceIleanLimits::default(),
    )
    .unwrap_err();
    assert_eq!(error.disposition().2, 5, "{error}");
}

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-source-ilean-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn oracle(&self, reference: &Path, name: &str, source: &str) -> Ilean {
        std::fs::write(self.0.join(format!("{name}.lean")), source).unwrap();
        let result = std::process::Command::new(reference)
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .args(["-i", &format!("{name}.ilean"), &format!("{name}.lean")])
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{name}: {}{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        fln::decode_ilean(
            &std::fs::read(self.0.join(format!("{name}.ilean"))).unwrap(),
            IleanBudget::default(),
        )
        .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn actual_reference_metadata_matches_native_positions_names_and_source_imports() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE requires FLN_REFERENCE_LEAN"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN for pinned .ilean production");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|word| word.strip_prefix("commit="))
        })
        .expect("SUITE.lock Reference commit");
    let identity = std::process::Command::new(&reference)
        .arg("--githash")
        .output()
        .expect("Reference identity");
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8_lossy(&identity.stdout).trim(),
        pin,
        "configured Reference differs from SUITE.lock"
    );
    let fixture = Fixture::new();
    for (name, source) in [
        ("Native", BASIC),
        (
            "Unicode",
            "prelude\r\naxiom «a.b» : Type\r\naxiom «c😀» : «a.b»\r\nnoncomputable def «δ😀» : «a.b» := «c😀»\r\n",
        ),
        (
            "Private",
            "prelude\naxiom T : Type\nnamespace N\nprivate axiom hidden : T\nnoncomputable def visible : T := hidden\nend N\n",
        ),
        (
            "Public",
            "module\nprelude\npublic axiom P : Prop\nprivate axiom hidden : P\npublic theorem checked : P := hidden\n",
        ),
        (
            "Bare",
            "prelude\nnoncomputable def poly (T : Type) (x : T) := x\n",
        ),
    ] {
        assert_eq!(
            complete(&[(name, source)], name),
            fixture.oracle(&reference, name, source),
            "{name} .ilean differs from Reference"
        );
    }
    let dependency = "prelude\naxiom T : Type\naxiom source : T\n";
    std::fs::write(fixture.0.join("Dep.lean"), dependency).unwrap();
    let compiled = std::process::Command::new(&reference)
        .current_dir(&fixture.0)
        .args(["-o", "Dep.olean", "Dep.lean"])
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}{}",
        String::from_utf8_lossy(&compiled.stdout),
        String::from_utf8_lossy(&compiled.stderr)
    );
    let entry = "prelude\nimport Dep\nnoncomputable def copy : T := source\n";
    assert_eq!(
        complete(&[("Main", entry), ("Dep", dependency)], "Main"),
        fixture.oracle(&reference, "Main", entry)
    );
    let public = "module\nprelude\npublic axiom P : Prop\npublic axiom p : P\n";
    let private = "module\nprelude\npublic axiom Q : Prop\npublic axiom q : Q\n";
    for (name, source) in [("PubDep", public), ("PrivDep", private)] {
        std::fs::write(fixture.0.join(format!("{name}.lean")), source).unwrap();
        let compiled = std::process::Command::new(&reference)
            .current_dir(&fixture.0)
            .args(["-o", &format!("{name}.olean"), &format!("{name}.lean")])
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "{}{}",
            String::from_utf8_lossy(&compiled.stdout),
            String::from_utf8_lossy(&compiled.stderr)
        );
    }
    let modern = "module\nprelude\npublic import PubDep\nimport all PrivDep\npublic theorem visible : P := p\nprivate theorem hidden : Q := q\n";
    assert_eq!(
        complete(
            &[
                ("Imports", modern),
                ("PubDep", public),
                ("PrivDep", private)
            ],
            "Imports"
        ),
        fixture.oracle(&reference, "Imports", modern),
        "module-system import flags and worlds"
    );
}
