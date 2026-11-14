//! Installed `lake env` consumes real package outputs and preserves child I/O.

use super::*;
use std::collections::BTreeMap;
use std::ffi::OsString;

fn command_for(workspace: &Workspace, lake: &Path, prefix: &Path) -> Command {
    let mut command = Command::new(lake);
    command
        .arg("--dir")
        .arg(workspace.0.join("root"))
        .current_dir(&workspace.0)
        .env("LEAN_SYSROOT", prefix)
        .env_remove("ELAN_TOOLCHAIN")
        .env_remove("LEAN_GITHASH")
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .env_remove("LD_LIBRARY_PATH")
        .env_remove("DYLD_LIBRARY_PATH")
        .env("FLN_IMPORT_REUSE_DIR", workspace.0.join("import-records"));
    command
}

fn command(workspace: &Workspace) -> Command {
    command_for(
        workspace,
        Path::new(env!("CARGO_BIN_EXE_lake")),
        &workspace.0.join("installation"),
    )
}

fn variables(output: &Output) -> BTreeMap<&str, &str> {
    assert!(output.status.success(), "{output:?}");
    std::str::from_utf8(&output.stdout)
        .unwrap()
        .lines()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("not an environment assignment: {line}"))
        })
        .collect()
}

fn paths(value: &str) -> Vec<PathBuf> {
    std::env::split_paths(value).collect()
}

fn ambient(name: &str) -> OsString {
    std::env::join_paths([
        PathBuf::from(format!("{name} λ with spaces")),
        PathBuf::new(),
        PathBuf::from(format!("{name}-last")),
    ])
    .unwrap()
}

#[test]
fn workspace_environment_preserves_package_order_library_roots_and_ambient_paths() {
    let workspace = artifact_workspace();
    workspace.write(
        "root/lakefile.toml",
        format!(
            "{ROOT}[[lean_lib]]\nname = \"Bundle\"\nroots = [\"App\"]\nsrcDir = \"lib\"\n\
         [[lean_lib]]\nname = \"Extras\"\nsrcDir = \"extra sources\"\n",
        ),
    );
    let mut cmd = command(&workspace);
    cmd.arg("env")
        .env("PATH", ambient("bin"))
        .env("LEAN_PATH", ambient("lean"))
        .env("LEAN_SRC_PATH", ambient("source"))
        .env("ELAN_TOOLCHAIN", "selected-native-toolchain")
        .env("LEAN_GITHASH", "explicit-trace-version");
    let shared_key = if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else {
        "LD_LIBRARY_PATH"
    };
    cmd.env(shared_key, ambient("shared"));
    let output = cmd.output().unwrap();
    assert!(output.stderr.is_empty(), "{output:?}");
    let vars = variables(&output);
    let base = workspace.0.canonicalize().unwrap();
    let prefix = workspace.0.join("installation");
    let reverse_builds = [
        "right/vendor/shared library/.lake/build",
        "left/.lake/build",
        "right/products",
        "root/output",
    ]
    .map(|dir| base.join(dir));
    let mut lean_paths = reverse_builds
        .iter()
        .map(|dir| dir.join("lib/lean"))
        .collect::<Vec<_>>();
    lean_paths.push(prefix.join("lib/lean"));
    lean_paths.extend(std::env::split_paths(&ambient("lean")));
    assert_eq!(paths(vars["LEAN_PATH"]), lean_paths);

    let mut source_paths = [
        "right/vendor/shared library/sources/lib",
        "left/code/lib",
        "right",
        "root/src/lib",
        "root/src/extra sources",
    ]
    .map(|dir| base.join(dir))
    .to_vec();
    source_paths.push(prefix.join("src/lean/lake"));
    source_paths.extend(std::env::split_paths(&ambient("source")));
    assert_eq!(paths(vars["LEAN_SRC_PATH"]), source_paths);

    let native_lake = Path::new(env!("CARGO_BIN_EXE_lake"))
        .canonicalize()
        .unwrap();
    let native_bin = native_lake.parent().unwrap();
    let shared_packages = reverse_builds
        .iter()
        .rev()
        .map(|dir| dir.join("lib"))
        .collect::<Vec<_>>();
    let mut bins = reverse_builds
        .iter()
        .map(|dir| dir.join("bin"))
        .collect::<Vec<_>>();
    if cfg!(windows) {
        bins.extend(shared_packages.iter().cloned());
    }
    bins.push(native_bin.to_owned());
    bins.push(prefix.join("bin"));
    bins.extend(std::env::split_paths(&ambient("bin")));
    assert_eq!(paths(vars["PATH"]), bins);
    if !cfg!(windows) {
        let mut shared_paths = vec![prefix.join("lib/lean"), prefix.join("lib")];
        shared_paths.extend(shared_packages);
        shared_paths.extend(std::env::split_paths(&ambient("shared")));
        assert_eq!(paths(vars[shared_key]), shared_paths);
    }
    assert_eq!(Path::new(vars["LAKE"]), native_lake);
    assert_eq!(
        Path::new(vars["LEAN"]),
        native_bin.join(format!("lean{}", std::env::consts::EXE_SUFFIX))
    );
    assert_eq!(vars["ELAN_TOOLCHAIN"], "selected-native-toolchain");
    assert_eq!(vars["LEAN_GITHASH"], "explicit-trace-version");
    workspace.no_products();
    workspace.no_manifests();
}

#[test]
fn workspace_environment_paths_match_the_pin() {
    let Some((lake, lib)) = reference() else {
        return;
    };
    let workspace = artifact_workspace();
    let prefix = lib
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .canonicalize()
        .unwrap();
    let run = |binary: &Path| {
        command_for(&workspace, binary, &prefix)
            .arg("env")
            .env("LEAN_PATH", ambient("lean"))
            .env("LEAN_SRC_PATH", ambient("source"))
            .env("LD_LIBRARY_PATH", ambient("shared"))
            .env("DYLD_LIBRARY_PATH", ambient("shared"))
            .output()
            .unwrap()
    };
    // The pin's initial manifest update temporarily loads duplicate direct
    // requirements twice. Compare the same resolved workspace on both sides,
    // without removing or normalizing any path occurrences in the outputs.
    let materialized = run(&lake);
    assert!(materialized.status.success(), "{materialized:?}");
    let manifest_path = workspace.0.join("root/lake-manifest.json");
    let manifest = std::fs::read(&manifest_path).unwrap();
    let native = run(Path::new(env!("CARGO_BIN_EXE_lake")));
    assert!(native.stderr.is_empty(), "{native:?}");
    assert_eq!(std::fs::read(&manifest_path).unwrap(), manifest);
    let pinned = run(&lake);
    let actual = variables(&native);
    let expected = variables(&pinned);
    for key in ["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_GITHASH"] {
        assert_eq!(actual[key], expected[key], "{key}");
    }
    if !cfg!(windows) {
        let key = if cfg!(target_os = "macos") {
            "DYLD_LIBRARY_PATH"
        } else {
            "LD_LIBRARY_PATH"
        };
        assert_eq!(actual[key], expected[key], "{key}");
    }
    // A development native Lake has its own executable directory before the
    // selected library installation. The rest of PATH is the pinned order.
    let mut native_path = paths(actual["PATH"]);
    let native_lake = Path::new(env!("CARGO_BIN_EXE_lake"))
        .canonicalize()
        .unwrap();
    let native_bin = native_lake.parent().unwrap();
    let index = native_path
        .iter()
        .position(|path| path == native_bin)
        .unwrap();
    native_path.remove(index);
    assert_eq!(native_path, paths(expected["PATH"]));
}

#[test]
fn lake_env_native_lean_consumes_built_transitive_package_artifacts() {
    let workspace = artifact_workspace();
    workspace.write(
        "Consumer.lean",
        concat!(
            "prelude\nimport App.Top\n",
            "def consumer (A : Type) (a : A) : A := App.combine A a\n",
            "#check consumer\n#check Shared.identity\n",
        ),
    );
    let before = command(&workspace)
        .args(["env", "lean", "Consumer.lean"])
        .output()
        .unwrap();
    assert!(
        !before.status.success(),
        "artifacts must exist before consumption: {before:?}"
    );
    build_success(workspace.run(&["build", "+App.Top:olean"], None));
    let output = command(&workspace)
        .args(["env", "lean", "Consumer.lean"])
        .output()
        .unwrap();
    let text = build_success(output);
    assert!(
        text.contains("consumer") && text.contains("Shared.identity"),
        "{text}"
    );
    // The relative file lives in the caller's directory, not --dir's root.
    assert!(!workspace.0.join("root/Consumer.lean").exists());
    let paths = artifact_paths(&workspace);
    assert!(paths.iter().all(|path| path.is_file()));
    let previous = paths
        .iter()
        .map(|path| std::fs::read(path).unwrap())
        .collect::<Vec<_>>();
    workspace.write(
        "Consumer.lean",
        "prelude\nimport App.Top\ntheorem impossible (P Q : Prop) (h : P) : Q := h\n",
    );
    let rejected = command(&workspace)
        .args(["env", "lean", "Consumer.lean"])
        .output()
        .unwrap();
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    let diagnostic = String::from_utf8(rejected.stderr).unwrap();
    assert!(diagnostic.contains("NotDefEq"), "{diagnostic}");
    for (path, bytes) in paths.iter().zip(previous) {
        assert_eq!(std::fs::read(path).unwrap(), bytes);
    }
    workspace.no_manifests();
}

#[test]
fn lake_env_keeps_child_flags_and_environment_listing_distinct() {
    let workspace = artifact_workspace();
    let direct = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("--version")
        .output()
        .unwrap();
    let forwarded = command(&workspace)
        .args(["env", "lean", "--version"])
        .output()
        .unwrap();
    assert_eq!(forwarded.status.code(), direct.status.code());
    assert_eq!(forwarded.stdout, direct.stdout);
    assert_eq!(forwarded.stderr, direct.stderr);
    let help = command(&workspace)
        .args(["env", "--help"])
        .output()
        .unwrap();
    assert!(build_success(help).contains("lake env [<cmd>]"));
    let listing = command(&workspace).arg("env").output().unwrap();
    let separated = command(&workspace)
        .args(["env", "--", "nonexistent_program_must_not_run", "--version"])
        .output()
        .unwrap();
    assert_eq!(separated.status.code(), Some(0), "{separated:?}");
    assert_eq!(separated.stdout, listing.stdout);
    assert_eq!(separated.stderr, listing.stderr);
    workspace.no_products();
    workspace.no_manifests();
}

#[cfg(unix)]
#[test]
fn lake_env_preserves_native_argv_streams_and_exit_status() {
    use std::io::Write;
    use std::os::unix::ffi::OsStringExt;
    use std::process::Stdio;

    let workspace = artifact_workspace();
    let mut child = command(&workspace)
        .args(["env", "/bin/sh", "-c", "for value do printf '<%s>' \"$value\"; done; printf '\\000'; cat; printf '\\376stderr\\000' >&2; exit 23", "child-name"])
        .args([OsString::from("--help"), OsString::from("--version"), OsString::from("--dir"), OsString::from(""), OsString::from("λ with spaces"), OsString::from("--"), OsString::from_vec(vec![0xff, b'x'])])
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
        .spawn().unwrap();
    let input = b"interactive input\x00\xff\n";
    child.stdin.take().unwrap().write_all(input).unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.code(), Some(23), "{output:?}");
    let mut expected = "<--help><--version><--dir><><λ with spaces><-->"
        .as_bytes()
        .to_vec();
    expected.extend_from_slice(b"<\xffx>\x00");
    expected.extend_from_slice(input);
    assert_eq!(output.stdout, expected);
    assert_eq!(output.stderr, b"\xfestderr\x00");
    let signaled = command(&workspace)
        .args(["env", "/bin/sh", "-c", "kill -TERM $$"])
        .output()
        .unwrap();
    assert_eq!(signaled.status.code(), Some(143), "{signaled:?}");
    workspace.no_products();
    workspace.no_manifests();
}

#[cfg(unix)]
#[test]
fn lake_env_checks_workspace_before_starting_child_and_preserves_native_paths() {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::fs::PermissionsExt;

    let workspace = artifact_workspace();
    let executable = workspace.0.join(OsString::from_vec(b"child-\xff".to_vec()));
    std::fs::write(&executable, b"#!/bin/sh\nprintf '%s' \"$LEAN_PATH\"\n").unwrap();
    std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755)).unwrap();
    let ambient = OsString::from_vec(b"native-environment-\xff".to_vec());
    let output = command(&workspace)
        .arg("env")
        .arg(&executable)
        .env("LEAN_PATH", &ambient)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(
        output.stdout.ends_with(b"native-environment-\xff"),
        "{output:?}"
    );
    assert!(output.stderr.is_empty(), "{output:?}");
    let listing = command(&workspace)
        .arg("env")
        .env("LEAN_PATH", &ambient)
        .output()
        .unwrap();
    assert_eq!(listing.status.code(), Some(1), "{listing:?}");
    assert!(listing.stdout.is_empty(), "{listing:?}");

    workspace.write(
        "right/lakefile.toml",
        format!("buildDir = \"../escape\"\n{RIGHT}"),
    );
    let marker = workspace.0.join("must-not-run");
    let output = command(&workspace)
        .args([
            "--json",
            "env",
            "/bin/sh",
            "-c",
            "printf run > \"$1\"",
            "child-name",
        ])
        .arg(&marker)
        .output()
        .unwrap();
    refusal(output, "unsupported", "stay within the package");
    assert!(!marker.exists());
    workspace.no_products();
    workspace.no_manifests();
}
