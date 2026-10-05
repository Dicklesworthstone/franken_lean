//! Installed Lake builds retain classes, not only their record declarations.
#![forbid(unsafe_code)]
use super::*;

fn build(project: &Project, targets: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&project.0)
        .args(["--json", "build"])
        .args(targets)
        .env("LEAN_PATH", project.0.join("objects"))
        .output()
        .unwrap()
}

fn package() -> Project {
    let project = Project::new();
    project.write(
        "lakefile.toml",
        "name = \"classes\"\n[[lean_lib]]\nname = \"Lib\"\n",
    );
    project.write(
        "Lib.lean",
        "prelude\nclass Mapper (A : Type) where\n  apply : A -> A\n",
    );
    project
}

#[test]
fn lake_class_artifact_supports_a_downstream_instance_in_a_fresh_process() {
    let project = package();
    success(build(&project, &["+Lib:olean"]));
    let artifact = project.0.join(".lake/build/lib/lean/Lib.olean");
    assert!(artifact.is_file());
    // Name the consumer outside the library source root: only the .olean can
    // supply the class to this independent invocation.
    project.write(
        "consumer/Main.lean",
        r#"prelude
import Lib
instance mapperId (A : Type) : Mapper A := { apply := fun x => x }
def use (A : Type) (x : A) : A := Mapper.apply x
"#,
    );
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(project.0.join("consumer/Main.lean"))
        .env("LEAN_PATH", artifact.parent().unwrap())
        .output()
        .unwrap();
    let report = success(output);
    assert!(report.contains("\"classes\":1"), "{report}");
    assert!(report.contains("\"commands\":2"), "{report}");
    assert!(report.contains("\"executed\":false"), "{report}");
}

#[test]
fn class_dependency_is_reused_without_duplicating_its_metadata_in_child_artifacts() {
    let project = package();
    for side in ["Left", "Right"] {
        project.write(&format!("Lib/{side}.lean"), format!("prelude\nimport Lib\ndef {side} (A : Type) [Mapper A] (x : A) : A := Mapper.apply x\n"));
    }
    let report = success(build(&project, &["+Lib.Left:olean", "+Lib.Right:olean"]));
    assert!(report.contains("\"module_checks_reused\":1"), "{report}");
    assert!(report.contains("\"module_elaborations\":3"), "{report}");
    for child in ["Left", "Right"] {
        let bytes = std::fs::read(
            project
                .0
                .join(format!(".lake/build/lib/lean/Lib/{child}.olean")),
        )
        .unwrap();
        let view = fln_olean::region::OleanView::parse(&bytes).unwrap();
        let blocks = view
            .extension_payloads(OleanWalkBudget::default(), 1024 * 1024)
            .unwrap();
        assert!(
            blocks
                .iter()
                .all(|b| b.name != n(CLASS) || b.entries.is_empty())
        );
    }
}

#[test]
fn an_unsupported_registration_cannot_replace_a_previously_published_class_library() {
    let project = package();
    success(build(&project, &["+Lib:olean"]));
    let artifact = project.0.join(".lake/build/lib/lean/Lib.olean");
    let original = std::fs::read(&artifact).unwrap();
    project.write("Lib.lean", "prelude\nclass Mapper (A : Type) where\n  apply : A -> A\ninstance mapperId (A : Type) : Mapper A := Mapper.mk (fun x => x)\n");
    let failed = build(&project, &["+Lib:olean"]);
    assert!(!failed.status.success(), "{failed:?}");
    assert!(failed.stdout.is_empty(), "{failed:?}");
    assert_eq!(std::fs::read(artifact).unwrap(), original);
}
