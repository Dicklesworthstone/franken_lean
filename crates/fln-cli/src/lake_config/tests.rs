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
fn native_lake_config_keeps_roots_as_typed_lean_expressions() {
    let source = b"import Lake\nopen Lake DSL\ndef names : Array Lean.Name := #[`Other]\npackage p\nlean_lib Bundle where\n  roots := names\n  srcDir := \"library\"\nlean_lib Empty where\n  roots := #[]\n";
    let parsed = parse(source).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.fields.len(), 3);
    assert!(matches!(parsed.fields[0].slot, ConfigSlot::LibraryRoots(0)));
    assert!(matches!(parsed.fields[1].slot, ConfigSlot::TargetSource(0)));
    assert!(matches!(parsed.fields[2].slot, ConfigSlot::LibraryRoots(1)));
    let program = parsed.program.split_whitespace().collect::<String>();
    for (index, expression) in [(0, "names"), (2, "#[]")] {
        assert!(program.contains(&format!(
            "def{}:_root_.Array_root_.Lean.Name:=({expression})",
            parsed.fields[index].declaration
        )));
    }
    // Parsing preserves the expressions; checked evaluation replaces these
    // defaults, including when the resulting array is explicitly empty.
    assert_eq!(parsed.config.targets[0].roots, ["Bundle"]);
    assert_eq!(parsed.config.targets[1].roots, ["Empty"]);
}

#[test]
fn native_lake_config_keeps_executable_roots_typed_and_defaults_to_the_target_name() {
    let source = b"import Lake\nopen Lake DSL\ndef selected : Lean.Name := `App.Main\npackage p\n@[default_target] lean_exe runner where\n  srcDir := System.FilePath.mk (\"ap\" ++ \"p\")\n  root := selected\nlean_exe Other\n";
    let parsed = parse(source).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.config.default_targets, ["runner"]);
    assert_eq!(parsed.config.targets[0].kind, TargetKind::Executable);
    assert_eq!(parsed.config.targets[0].roots, ["runner"]);
    assert_eq!(parsed.config.targets[1].kind, TargetKind::Executable);
    assert_eq!(parsed.config.targets[1].roots, ["Other"]);
    assert_eq!(parsed.fields.len(), 2);
    assert!(matches!(parsed.fields[0].slot, ConfigSlot::TargetSource(0)));
    assert!(matches!(
        parsed.fields[1].slot,
        ConfigSlot::ExecutableRoot(0)
    ));
    let program = parsed.program.split_whitespace().collect::<String>();
    assert!(program.contains(&format!(
        "def{}:_root_.Lean.Name:=(selected)",
        parsed.fields[1].declaration
    )));
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
fn native_lake_config_keeps_local_requirements_as_typed_terms_in_source_order() {
    let source = r#"import Lake
open System Lake DSL
def sibling (name : String) : FilePath := FilePath.mk ("../" ++ name)
namespace Config
scoped notation "◆" s => sibling s
end Config
open scoped Config
require shared from ◆ "shared library"
def nextPath : FilePath := "../next"
package application
require "quoted-dependency" from nextPath
@[default_target] lean_lib Application
"#;
    let parsed = parse(source.as_bytes()).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.config.requires.len(), 2);
    assert_eq!(parsed.config.requires[0].name, "shared");
    assert_eq!(parsed.config.requires[1].name, "«quoted-dependency»");
    assert!(
        parsed
            .config
            .requires
            .iter()
            .all(|item| item.path.is_none())
    );
    assert!(matches!(
        parsed.fields[0].slot,
        ConfigSlot::DependencyPath(0)
    ));
    assert!(matches!(
        parsed.fields[1].slot,
        ConfigSlot::DependencyPath(1)
    ));
    let first = parsed.program.find(&parsed.fields[0].declaration).unwrap();
    let next = parsed.program.find("def nextPath").unwrap();
    let second = parsed.program.find(&parsed.fields[1].declaration).unwrap();
    assert!(first < next && next < second, "{}", parsed.program);
    assert!(parsed.program.contains("open scoped Config"));
    assert!(parsed.program.contains("◆ \"shared library\""));
    for field in &parsed.fields {
        assert!(parsed.program.contains(&format!(
            "def {} : _root_.System.FilePath := (",
            field.declaration
        )));
    }
    let windows = parse(source.replace('\n', "\r\n").as_bytes())
        .unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(windows.config.requires, parsed.config.requires);
    assert!(windows.program.contains("◆ \"shared library\""));
}

#[test]
fn native_lake_config_distinguishes_term_with_from_dependency_options() {
    for expression in [
        "match true with | true => \"../yes\" | false => \"../no\"",
        "(match true with | true => \"../yes\" | false => \"../no\")",
        "System.FilePath.mk (let s := \"with from git\"; s)",
    ] {
        let source = format!(
            "import Lake\nopen Lake DSL\npackage p\nrequire dep from {expression}\nlean_lib P\n"
        );
        let parsed = parse(source.as_bytes()).unwrap_or_else(|error| panic!("{}", error.detail));
        assert!(parsed.program.contains(expression), "{}", parsed.program);
    }
    for expression in [
        "\"../dep\" with {}",
        "(match true with | true => \"../yes\" | false => \"../no\") with {}",
    ] {
        let source =
            format!("import Lake\nopen Lake DSL\npackage p\nrequire dep from {expression}\n");
        let error = parse(source.as_bytes()).unwrap_err();
        assert_eq!(error.class, "unsupported", "{}", error.detail);
        assert!(error.detail.contains("`with` options"), "{}", error.detail);
    }
}

#[test]
fn native_lake_config_requirements_keep_package_names_separate_from_binding_names() {
    let source = "import Lake\nopen Lake DSL\npackage p\nrequire _root_.foo from \"../one\"\nrequire \"_root_.foo\" from \"../two\"\nrequire pkgConfig from \"../three\"\nrequire \"_package.name\" from \"../four\"\nrequire _package.other from \"../five\"\n";
    let parsed = parse(source.as_bytes()).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.config.requires[0].name, "_root_.foo");
    assert_eq!(parsed.config.requires[1].name, "«_root_.foo»");
    assert_eq!(parsed.config.requires[2].name, "pkgConfig");
    assert_eq!(parsed.config.requires[3].name, "«_package.name»");
    assert_eq!(parsed.config.requires[4].name, "_package.other");
    assert_eq!(parsed.requirement_names[0], Name::from_components(["foo"]));
    assert_eq!(
        parsed.requirement_names[1],
        Name::from_components(["_root_.foo"])
    );
    assert_eq!(
        parsed.requirement_names[3],
        Name::from_components(["_package.name"])
    );
}

#[test]
fn native_lake_config_refuses_unsupported_or_ambiguous_requirements() {
    for (body, diagnostic) in [
        ("require dep", "explicit `from` source"),
        ("require dep @ \"1.0.0\" from \"../dep\"", "version"),
        ("require dep from git", "Git URL and revision"),
        ("require dep from git \"../dep\" @", "Git URL and revision"),
        ("require dep from git \"../dep\" /", "FilePath expression"),
        ("require dep from git \"../dep\" with {}", "suffix"),
        (
            "require \"owner\" / dep from \"../dep\"",
            "scoped dependency",
        ),
        ("require dep from", "FilePath expression"),
        (
            "@[default_target] require dep from \"../dep\"",
            "only @[default_target]",
        ),
        (
            "namespace N\nrequire dep from \"../dep\"\nend N",
            "top level",
        ),
        (
            "require dep from \"../one\"\nrequire dep from \"../two\"",
            "already declared",
        ),
        (
            "lean_lib dep\nrequire dep from \"../dep\"",
            "already declared",
        ),
        (
            "require dep from \"../dep\"\nlean_lib dep",
            "already declared",
        ),
        (
            "require _root_.dep from \"../one\"\nrequire dep from \"../two\"",
            "already declared",
        ),
        (
            "require _root_.Dep from \"../dep\"\nlean_lib Dep",
            "already declared",
        ),
        (
            "lean_lib Dep\nrequire _root_.Dep from \"../dep\"",
            "already declared",
        ),
        ("require _package from \"../dep\"", "already declared"),
        ("require _package.name from \"../dep\"", "already declared"),
        (
            "require _root_._package from \"../dep\"",
            "already declared",
        ),
        ("require _root_ from \"../dep\"", "not a declaration name"),
    ] {
        let source = format!("import Lake\nopen Lake DSL\npackage p\n{body}\n");
        let error = parse(source.as_bytes()).unwrap_err();
        assert!(
            error.detail.contains(diagnostic),
            "{body}: {}",
            error.detail
        );
        assert!(!error.authority);
    }
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
        "package p\nlean_exe Main where\n  moreLinkArgs := #[\"-unexpected\"]\n",
        "package p\nlean_exe Main where\n  roots := #[`Main]\n",
        "package p\nlean_lib Main where\n  root := `Main\n",
        "package p\nlean_lib Main\nlean_exe Main\n",
        "lean_exe Main\npackage p\n",
        "package p\nrequire dep from git \"https://example.test/dep\" @ \"main\" with {}\n",
        "package p\nscript hi := return 0\n",
        "package p where\n  moreLeanArgs := #[\"--foo\"]\nlean_lib P\n",
        "package p where\n  roots := #[`Other]\nlean_lib P\n",
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

#[test]
fn native_lake_config_keeps_git_fields_as_checked_string_and_path_terms() {
    let source = r#"import Lake
open System Lake DSL
def endpoint : String := "https://example.invalid/" ++ "source"
def revision : String := "lock" ++ "ed"
package p
require "dep-name" from git endpoint @ (revision) / FilePath.mk ("lib/" ++ "nested")
require other from git ("https://example.invalid/" ++ "other")
lean_lib P
"#;
    let parsed = parse(source.as_bytes()).unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(parsed.config.requires.len(), 2);
    assert_eq!(parsed.config.requires[0].name, "«dep-name»");
    assert_eq!(parsed.fields.len(), 4);
    assert!(matches!(parsed.fields[0].slot, ConfigSlot::DependencyUrl(0)));
    assert!(matches!(
        parsed.fields[1].slot,
        ConfigSlot::DependencyRevision(0)
    ));
    assert!(matches!(parsed.fields[2].slot, ConfigSlot::DependencySubdir(0)));
    assert!(matches!(parsed.fields[3].slot, ConfigSlot::DependencyUrl(1)));
    for (index, type_) in [
        (0, "_root_.String"),
        (1, "_root_.String"),
        (2, "_root_.System.FilePath"),
        (3, "_root_.String"),
    ] {
        assert!(
            parsed.program.contains(&format!(
                "def {} : {type_} :=",
                parsed.fields[index].declaration
            )),
            "{}",
            parsed.program,
        );
    }
    assert!(parsed.program.contains("FilePath.mk (\"lib/\" ++ \"nested\")"));
    assert!(
        parsed
            .program
            .contains("(\"https://example.invalid/\" ++ \"other\")")
    );
    // Values are deliberately unresolved here: only checked Golem execution
    // may populate the dependency configuration.
    assert!(
        parsed
            .config
            .requires
            .iter()
            .all(|dependency| dependency.path.is_none() && dependency.url.is_none())
    );
    let windows = parse(source.replace('\n', "\r\n").as_bytes())
        .unwrap_or_else(|error| panic!("{}", error.detail));
    assert_eq!(windows.config.requires, parsed.config.requires);
    assert_eq!(windows.fields.len(), parsed.fields.len());
}

#[test]
fn git_requirement_delimiters_do_not_split_nested_terms_or_accept_options() {
    let accepted = [
        "git (\"https://example.invalid/@/repo\") @ (\"rev/@\") / (match true with | true => \"lib\" | false => \"other\")",
        "git \"repo\" / System.FilePath.mk (let s := \"with @ /\"; s)",
    ];
    for expression in accepted {
        let source = format!("import Lake\nopen Lake DSL\npackage p\nrequire dep from {expression}\n");
        parse(source.as_bytes()).unwrap_or_else(|error| panic!("{expression}: {}", error.detail));
    }
    for expression in [
        "git \"repo\" extra",
        "git \"repo\" @ \"rev\" extra",
        "git \"repo\" / \"lib\" with {}",
        "git \"repo\" / (match true with | true => \"lib\" | false => \"other\") with {}",
    ] {
        let source = format!("import Lake\nopen Lake DSL\npackage p\nrequire dep from {expression}\n");
        assert!(parse(source.as_bytes()).is_err(), "{expression}");
    }
}
