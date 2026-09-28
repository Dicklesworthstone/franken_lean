//! Installed commands must use the context receipt, not the full ambient engine.
use super::*;

fn lake(project: &Project, targets: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--dir")
        .arg(&project.0)
        .args(["--json", "build"])
        .args(targets)
        .env("LEAN_PATH", project.0.join("objects"))
        .output()
        .unwrap()
}

fn separate_sources(project: &Project) {
    project.write("Left.lean", "prelude\nimport A\ndef leftUse [d : Class] : Class := d\ndef left : Family leftUse := valueA\n");
    project.write("Right.lean", "prelude\nimport B\ndef rightUse [d : Class] : Class := d\ndef right : Family rightUse := valueB\n");
    project.write("Main.lean", "prelude\nimport Left Right\ndef checkLeft : Family a := left\ndef checkRight : Family b := right\n");
}

#[test]
fn installed_distinct_sibling_contexts_check_without_lending_names_or_instances() {
    let project = fixture();
    project.module(
        "A",
        &[axiom("onlyA", c("Class"))],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    separate_sources(&project);
    let report = project.success();
    assert!(report.contains("\"commands\":6"), "{report}");
    assert!(report.contains("\"files\":3"), "{report}");
    for source in [
        "prelude\nimport B\ndef bad : Class := onlyA\n",
        "prelude\nimport Core\ndef use [d : Class] : Class := d\ndef bad : Class := use\n",
        "prelude\nimport B\ndef use [d : Class] : Class := d\ndef bad : Family use := valueA\n",
    ] {
        project.write("Right.lean", source);
        let refused = project.run();
        assert!(!refused.status.success(), "{refused:?}");
        assert!(refused.stdout.is_empty());
    }
    separate_sources(&project);
    project.success();
}

#[test]
fn installed_source_and_artifact_journals_preserve_interleaved_import_order() {
    let project = fixture();
    project.write(
        "Local.lean",
        "prelude\nimport A\ninstance localChoice : Class := a\n",
    );
    for (order, value) in [("Local B", "valueB"), ("B Local", "valueA")] {
        project.write("Main.lean", source(order, value));
        project.success();
        let wrong = if value == "valueA" {
            "valueB"
        } else {
            "valueA"
        };
        project.write("Main.lean", source(order, wrong));
        let refused = project.run();
        assert!(!refused.status.success(), "{refused:?}");
        assert!(refused.stdout.is_empty());
    }
}

#[test]
fn installed_lake_builds_distinct_contexts_reimports_and_preserves_prior_outputs_on_failure() {
    let project = fixture();
    project.module(
        "A",
        &[axiom("onlyA", c("Class"))],
        &["Core"],
        vec![(INSTANCE, vec![instance("a", 1000)])],
    );
    project.write("lakefile.toml", "name = \"contexts\"\n[[lean_lib]]\nname = \"Main\"\nroots = [\"Main\", \"Left\", \"Right\"]\n");
    separate_sources(&project);
    let report = success(lake(&project, &["+Main:olean"]));
    assert!(report.contains("\"modules_built\":3"), "{report}");
    let files: Vec<_> = ["Left", "Right", "Main"]
        .iter()
        .map(|name| project.0.join(format!(".lake/build/lib/lean/{name}.olean")))
        .collect();
    let prior: Vec<_> = files
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    success(lake(
        &project,
        &["+Right:olean", "+Main:olean", "+Left:olean"],
    ));
    for (path, prior) in files.iter().zip(&prior) {
        assert_eq!(std::fs::read(path).unwrap(), *prior);
    }
    project.write("Consumer.lean", "prelude\nimport Main\ndef useLeft : Family a := checkLeft\ndef useRight : Family b := checkRight\n");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(project.0.join("Consumer.lean"))
        .env(
            "LEAN_PATH",
            std::env::join_paths([
                project.0.join(".lake/build/lib/lean"),
                project.0.join("objects"),
            ])
            .unwrap(),
        )
        .output()
        .unwrap();
    success(output);
    // This constant exists in the complete closure but is not imported by Right.
    project.write(
        "Right.lean",
        "prelude\nimport B\ndef right : Class := onlyA\n",
    );
    let refused = lake(&project, &["+Main:olean"]);
    assert!(!refused.status.success(), "{refused:?}");
    assert!(refused.stdout.is_empty());
    for (path, prior) in files.iter().zip(&prior) {
        assert_eq!(std::fs::read(path).unwrap(), *prior);
    }
    assert!(
        !project
            .0
            .join(".lake/build/lib/lean/.fln-olean-build.lock")
            .exists()
    );
}

#[test]
fn installed_distinct_contexts_keep_shared_dependency_reuse_across_targets() {
    let project = fixture();
    separate_sources(&project);
    project.write("Second.lean", "prelude\nimport Left Right\ndef secondLeft : Family a := left\ndef secondRight : Family b := right\n");
    project.write("lakefile.toml", "name = \"contexts\"\n[[lean_lib]]\nname = \"Main\"\nroots = [\"Main\", \"Second\", \"Left\", \"Right\"]\n");
    for targets in [
        ["+Main:olean", "+Second:olean"],
        ["+Second:olean", "+Main:olean"],
    ] {
        let report = success(lake(&project, &targets));
        assert!(report.contains("\"modules_built\":4"), "{report}");
        assert!(report.contains("\"module_elaborations\":4"), "{report}");
        assert!(report.contains("\"module_checks_reused\":2"), "{report}");
        assert!(report.contains("\"modules_cached\":0"), "{report}");
    }
}
