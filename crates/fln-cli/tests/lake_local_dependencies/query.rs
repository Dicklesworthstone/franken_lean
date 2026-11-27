//! Native query results share the checked build and publication path.
#![forbid(unsafe_code)]

use super::*;

#[test]
fn query_builds_ordered_results_and_reuses_checked_records() {
    let workspace = artifact_workspace();
    let arguments = [
        "query",
        "@right/+Feature.Right:olean",
        "/+App.Top:olean",
        "right/Feature.Right:olean",
    ];
    let paths = artifact_paths(&workspace);
    let first = build_success(workspace.run(&arguments, None));
    // The package resolver canonicalizes roots, including Windows' verbatim
    // path prefix. Compare against the real produced files in that spelling.
    let canonical: Vec<_> = paths
        .iter()
        .map(|path| path.canonicalize().unwrap())
        .collect();
    let expected = format!(
        "{}\n{}\n{}\n",
        canonical[2].display(),
        canonical[0].display(),
        canonical[2].display(),
    );
    assert_eq!(first, expected);
    let previous: Vec<_> = paths
        .iter()
        .map(|path| {
            let bytes = std::fs::read(path).unwrap();
            fln_olean::region::OleanView::parse(&bytes).unwrap();
            bytes
        })
        .collect();
    assert_eq!(build_success(workspace.run(&arguments, None)), expected);
    let snapshot =
        std::fs::read_to_string(workspace.0.join("root/output/fln-build.snapshot")).unwrap();
    let decisions: Vec<_> = snapshot
        .lines()
        .filter(|line| line.starts_with("module\t"))
        .map(|line| line.split('\t').next_back().unwrap())
        .collect();
    assert_eq!(decisions, ["cached"; 4]);
    for (path, before) in paths.iter().zip(previous) {
        assert_eq!(std::fs::read(path).unwrap(), before);
    }
    let explanation = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--json", "--dir"])
        .arg(workspace.0.join("root"))
        .arg("@right/+Feature.Right:olean")
        .env("LEAN_PATH", workspace.0.join("absent-imports"))
        .output()
        .unwrap();
    let explanation = build_success(explanation);
    assert!(
        explanation.contains("\"reference_decision\":\"up-to-date\""),
        "{explanation}",
    );
    workspace.no_manifests();
}

#[test]
fn explain_facet_selectors_match_build_and_query_for_colliding_targets_and_owners() {
    let workspace = Workspace::new();
    workspace.write(
        "root/lakefile.toml",
        concat!(
            "name = \"root\"\n[[require]]\nname = \"dependency\"\npath = \"../right\"\n",
            "[[lean_lib]]\nname = \"Demo\"\n",
        ),
    );
    workspace.write(
        "right/lakefile.toml",
        "name = \"dependency\"\n[[lean_lib]]\nname = \"Other\"\nroots = [\"Demo\"]\n",
    );
    for path in ["root/Demo.lean", "right/Demo.lean"] {
        workspace.write(
            path,
            "module\nprelude\npublic theorem Demo.keep (P : Prop) (h : P) : P := h\n",
        );
    }
    let selected = "@root/+Demo:olean.private";
    build_success(workspace.run(&["--json", "build", selected], None));
    let explain = |target: &str| {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["build", "explain", "--json", "--dir"])
            .arg(workspace.0.join("root"))
            .arg(target)
            .env("LEAN_PATH", workspace.0.join("absent-imports"))
            .output()
            .unwrap()
    };
    for target in ["Demo", selected] {
        let report = build_success(explain(target));
        assert!(
            report.contains("\"reference_decision\":\"up-to-date\""),
            "{report}"
        );
    }
    for (target, detail) in [
        ("Demo:olean.server", "select the module explicitly"),
        ("+Demo:olean.private", "multiple local packages"),
    ] {
        for command in ["build", "query"] {
            refusal(
                workspace.run(&["--json", command, target], None),
                "unsupported",
                detail,
            );
        }
        let report = explain(target);
        assert_eq!(report.status.code(), Some(1), "{report:?}");
        assert!(
            String::from_utf8_lossy(&report.stderr).contains(detail),
            "{report:?}"
        );
    }
    let other = explain("@dependency/+Demo:olean.private");
    assert_eq!(other.status.code(), Some(1), "{other:?}");
    assert!(
        String::from_utf8_lossy(&other.stderr)
            .contains("different package from the recorded build"),
        "{other:?}",
    );
}

#[test]
fn query_failure_emits_no_result_and_preserves_every_previous_product() {
    let workspace = artifact_workspace();
    let arguments = ["--json", "query", "+Feature.Left:olean", "+App.Top:olean"];
    let expected = build_success(workspace.run(&arguments, None));
    let paths = artifact_paths(&workspace);
    let previous: Vec<_> = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    let snapshot = workspace.0.join("root/output/fln-build.snapshot");
    let original_snapshot = std::fs::read(&snapshot).unwrap();
    let right = std::fs::read(workspace.0.join("right/Feature/Right.lean")).unwrap();
    workspace.write(
        "left/code/lib/Feature/Left.lean",
        concat!(
            "prelude\nimport Shared\n",
            "def Feature.left (A : Type) (a : A) : A := Shared.identity A a\n",
            "theorem Feature.extra (P : Prop) (h : P) : P := h\n",
        ),
    );
    workspace.write(
        "right/Feature/Right.lean",
        concat!(
            "prelude\nimport Shared\n",
            "theorem impossible (P Q : Prop) (h : P) : Q := h\n",
        ),
    );
    let failed = workspace.run(&arguments, None);
    assert_eq!(failed.status.code(), Some(1), "{failed:?}");
    assert!(failed.stdout.is_empty(), "{failed:?}");
    assert!(
        std::str::from_utf8(&failed.stderr)
            .unwrap()
            .contains("\"schema\":\"fln.lake-query/1\""),
        "{failed:?}",
    );
    for (path, before) in paths.iter().zip(&previous) {
        assert_eq!(std::fs::read(path).unwrap(), *before);
    }
    assert_eq!(std::fs::read(&snapshot).unwrap(), original_snapshot);
    workspace.write("right/Feature/Right.lean", right);
    assert_eq!(build_success(workspace.run(&arguments, None)), expected);
    assert_ne!(std::fs::read(&paths[1]).unwrap(), previous[1]);

    // Query results already exist in memory when publication begins. A held
    // output lock must still prevent every result from reaching stdout.
    let recovered: Vec<_> = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect();
    let recovered_snapshot = std::fs::read(&snapshot).unwrap();
    workspace.write(
        "root/output/lib/lean/.fln-olean-build.lock",
        "another publisher holds this directory\n",
    );
    refusal(workspace.run(&arguments, None), "io", "fln.lake-query/1");
    for (path, before) in paths.iter().zip(recovered) {
        assert_eq!(std::fs::read(path).unwrap(), before);
    }
    assert_eq!(std::fs::read(&snapshot).unwrap(), recovered_snapshot);
    workspace.no_manifests();
}

#[test]
fn query_empty_targets_and_unavailable_requests_never_invent_products() {
    let workspace = artifact_workspace();
    for arguments in [vec!["query"], vec!["query", "--json"]] {
        assert_eq!(build_success(workspace.run(&arguments, None)), "");
    }
    for arguments in [
        vec!["--json", "query", "+App.Top:olean", "+App.Top:c"],
        vec!["--json", "query", "Bundle:olean"],
        vec!["--json", "query", "+App.Top"],
    ] {
        refusal(
            workspace.run(&arguments, None),
            "unsupported",
            "fln.lake-query/1",
        );
    }
    for arguments in [
        ["--json", "--no-build", "query", "+App.Top:olean"],
        ["--json", "query", "--no-build", "+App.Top:olean"],
    ] {
        let output = workspace.run(&arguments, None);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        let error = std::str::from_utf8(&output.stderr).unwrap();
        assert!(error.contains("\"schema\":\"fln.lake-query/1\""), "{error}");
        assert!(error.contains("\"status\":\"unsupported\""), "{error}");
        assert!(error.contains("--no-build"), "{error}");
    }
    let mut excessive = vec!["--json", "query"];
    excessive.extend(std::iter::repeat_n("+App.Top:olean", 257));
    refusal(
        workspace.run(&excessive, None),
        "resource",
        "build target count exceeds 256",
    );
    let root = std::fs::read_to_string(workspace.0.join("root/lakefile.toml")).unwrap();
    workspace.write(
        "root/lakefile.toml",
        format!("defaultTargets = [\"Bundle\"]\n{root}"),
    );
    refusal(
        workspace.run(&["--json", "query"], None),
        "unsupported",
        "default library and executable facets are unavailable",
    );
    for path in artifact_paths(&workspace) {
        assert!(!path.exists(), "{}", path.display());
    }
    assert!(!workspace.0.join("root/output/fln-build.snapshot").exists());
    assert!(!workspace.0.join("import-records").exists());
    assert!(!workspace.0.join("right/products").exists());
    workspace.no_products();
    workspace.no_manifests();
}

fn proof_build_directory() -> &'static str {
    if cfg!(windows) {
        // Quotes are not legal Windows filename characters. Backslashes in
        // Windows paths still exercise JSON escaping, alongside Unicode.
        "products Unicode λ"
    } else {
        "products \"quoted\" λ"
    }
}

fn proof_workspace() -> Workspace {
    let workspace = artifact_workspace();
    for (path, source) in [
        (
            "right/vendor/shared library/sources/lib/Shared.lean",
            "module\nprelude\npublic theorem Shared.keep (P : Prop) (h : P) : P := h\n",
        ),
        (
            "left/code/lib/Feature/Left.lean",
            "module\nprelude\npublic import Shared\npublic theorem Feature.left (P : Prop) (h : P) : P := Shared.keep P h\n",
        ),
        (
            "right/Feature/Right.lean",
            "module\nprelude\npublic import Shared\npublic theorem Feature.right (P : Prop) (h : P) : P := Shared.keep P h\n",
        ),
        (
            "root/src/lib/App/Top.lean",
            "module\nprelude\npublic import Feature.Left\npublic import Feature.Right\npublic theorem App.keep (P : Prop) (h : P) : P := Feature.left P (Feature.right P h)\n",
        ),
    ] {
        workspace.write(path, source);
    }
    let build_dir = proof_build_directory().replace('"', "\\\"");
    workspace.write(
        "right/lakefile.toml",
        format!("buildDir = \"{build_dir}\"\n{RIGHT}"),
    );
    workspace
}

fn normalize_query_output(mut output: String, workspace: &Workspace, json: bool) -> String {
    // Only the independent scratch root is normalized. Its canonical spelling
    // can differ on Windows and on platforms with a symlinked temp directory.
    for prefix in [workspace.0.canonicalize().unwrap(), workspace.0.clone()] {
        let prefix = prefix.display().to_string();
        let prefix = if json {
            prefix.replace('\\', "\\\\").replace('"', "\\\"")
        } else {
            prefix
        };
        output = output.replace(&prefix, "<workspace>");
    }
    output
}

#[test]
fn query_module_facets_match_pinned_text_and_json_output() {
    let Some((lake, _)) = reference() else {
        return;
    };
    let native = proof_workspace();
    let oracle = proof_workspace();
    for flags in [
        vec![],
        vec!["--json"],
        vec!["-J"],
        vec!["--json", "--text"],
        vec!["--text", "--json"],
    ] {
        let mut arguments = vec![
            "query",
            "@right/+Feature.Right:olean",
            "@program/+App.Top:ir",
            "right/Feature.Right:olean",
            "@/+App.Top:olean",
            "@right/+Feature.Right:ilean",
            "@/+App.Top:ilean",
        ];
        arguments.extend(&flags);
        let expected = Command::new(&lake)
            .arg("--dir")
            .arg(oracle.0.join("root"))
            .args(&arguments)
            .current_dir(&oracle.0)
            .env_remove("LEAN_PATH")
            .output()
            .unwrap();
        assert!(expected.status.success(), "{expected:?}");
        let json = matches!(flags.last(), Some(&"--json" | &"-J"));
        let expected =
            normalize_query_output(String::from_utf8(expected.stdout).unwrap(), &oracle, json);
        let actual =
            normalize_query_output(build_success(native.run(&arguments, None)), &native, json);
        assert_eq!(actual, expected, "flags: {flags:?}");
        let lines: Vec<_> = actual.lines().collect();
        assert_eq!(lines.len(), 6, "{actual}");
        assert_eq!(lines[0], lines[2], "{actual}");
        assert!(lines[1].contains("Top.ir"), "{actual}");
        assert!(lines[3].contains("Top.olean"), "{actual}");
        assert!(lines[4].contains("Right.ilean"), "{actual}");
        assert!(lines[5].contains("Top.ilean"), "{actual}");
        for relative in [
            PathBuf::from("root/output/lib/lean/App/Top.ilean"),
            PathBuf::from("right")
                .join(proof_build_directory())
                .join("lib/lean/Feature/Right.ilean"),
        ] {
            let decode = |workspace: &Workspace| {
                fln::decode_ilean(
                    &std::fs::read(workspace.0.join(&relative)).unwrap(),
                    fln::IleanBudget::default(),
                )
                .unwrap()
            };
            assert_eq!(decode(&native), decode(&oracle), "{}", relative.display());
        }
    }
    let mut paths = artifact_paths(&native);
    paths[2] = native
        .0
        .join("right")
        .join(proof_build_directory())
        .join("lib/lean/Feature/Right.olean");
    for path in paths {
        let bytes = std::fs::read(path.with_extension("ir")).unwrap();
        fln_olean::region::OleanView::parse(&bytes).unwrap();
    }
    native.no_manifests();
}
