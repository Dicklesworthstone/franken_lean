use super::*;

#[test]
fn native_lake_config_keeps_lean_terms_and_declared_defaults() {
    let source = b"import Lake\nopen System Lake DSL\ndef folder := \"src\" ++ \"/lean\"\npackage demo where\n  srcDir := FilePath.mk folder\n  buildDir := FilePath.mk (\".lake/\" ++ \"native\")\n@[default_target] lean_lib Demo where\n  srcDir := \"library\"\nlean_lib Other\n";
    let parsed = parse(source).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.config.name, "demo");
    assert_eq!(parsed.config.default_targets, ["Demo"]);
    assert_eq!(parsed.config.targets[0].roots, ["Demo"]);
    assert_eq!(parsed.config.targets[1].roots, ["Other"]);
    assert_eq!(parsed.fields.len(), 3);
    assert!(parsed.program.contains("FilePath.mk folder"));
    assert!(
        parsed
            .program
            .contains("def folder := \"src\" ++ \"/lean\"")
    );
    assert!(parsed.program.contains("_root_.System.FilePath"));
    assert!(!parsed.program.contains("import Lake"));
    assert!(!parsed.program.contains("structure FilePath"));
}

#[test]
fn native_lake_config_uses_prior_local_and_scoped_notation_tokens() {
    let source = "import Lake\nopen System Lake DSL\nnamespace Config\nscoped notation \"◆\" s => System.FilePath.mk s\nend Config\nopen scoped Config\nlocal notation \"◇\" => \"src\"\npackage p where\n  srcDir := ◆ ◇\n@[default_target] lean_lib P\n";
    let parsed = parse(source.as_bytes()).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.fields.len(), 1);
    assert!(!parsed.program.contains("srcDir"));
    assert!(parsed.program.contains("◆ ◇"));
    assert!(parsed.program.contains("open scoped Config"));
}

#[test]
fn native_lake_config_comments_strings_and_nested_terms_are_not_commands() {
    let source = b"import Lake\nopen Lake DSL\n/- package counterfeit\nlean_lib Wrong -/\npackage actual where\n  srcDir := System.FilePath.mk (let s := \"lean_lib Wrong\"; if true then s else \"package bad\")\n/-- the real library -/\n@[default_target] lean_lib Actual\n";
    let parsed = parse(source).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.config.name, "actual");
    assert_eq!(parsed.config.targets.len(), 1);
    assert_eq!(parsed.config.targets[0].name, "Actual");
    assert_eq!(parsed.fields.len(), 1);
    let crlf = std::str::from_utf8(source).unwrap().replace('\n', "\r\n");
    let windows = parse(crlf.as_bytes()).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(windows.config.name, parsed.config.name);
    assert_eq!(windows.config.targets, parsed.config.targets);
}

#[test]
fn native_lake_config_refuses_unimplemented_build_semantics() {
    for body in [
        "package p\nlean_exe Main\n",
        "package p\nrequire dep from git \"https://example.test/dep\"\n",
        "package p\nscript hi := return 0\n",
        "package p where\n  moreLeanArgs := #[\"--foo\"]\nlean_lib P\n",
        "package p\nlean_lib P where\n  roots := #[`Other]\n",
        "package p\nlean_lib P\nlean_lib P\n",
        "package p\npackage q\nlean_lib P\n",
        "lean_lib P\npackage p\n",
        "@[default_target] package p\nlean_lib P\n",
        "package p\n@[extern \"unrelated\"] lean_lib P\n",
    ] {
        let source = format!("import Lake\nopen Lake DSL\n{body}");
        assert!(parse(source.as_bytes()).is_err(), "{body}");
    }
}

#[test]
fn native_lake_config_does_not_invent_imports_or_capture_generated_names() {
    for source in [
        "package p\nlean_lib P\n",
        "import Lake\npackage p\nlean_lib P\n",
        "module\nimport Lake\nopen Lake DSL\npackage p\nlean_lib P\n",
        "import Lake\nimport ConfigHelper\nopen Lake DSL\npackage p\nlean_lib P\n",
        "public import Lake\nopen Lake DSL\npackage p\nlean_lib P\n",
        "meta import Lake\nopen Lake DSL\npackage p\nlean_lib P\n",
    ] {
        assert!(parse(source.as_bytes()).is_err(), "{source}");
    }
    let parsed = parse(b"import Lake\nopen Lake DSL\ndef _fln_lake_path_0 : Nat := 7\npackage p where\n  srcDir := \"src\"\nlean_lib P\n").unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.fields[0].declaration, "_fln_lake_path_1");
}
