//! Installed executable-main behavior through the full actual import loader.
//! Every subprocess uses the same Lean binary, roots and private record store.

use super::*;

const HEADER: &str = "prelude\nimport Init.System.IO\nimport Init.Data.Repr\n";

fn source(workspace: &Workspace, file: &str, body: &str) -> PathBuf {
    workspace.write(file, format!("{HEADER}{body}\n"))
}

fn lean_main(
    workspace: &Workspace,
    library: &Path,
    compiler_options: &[&str],
    flag: &str,
    entry: &Path,
    arguments: &[&str],
) -> Run {
    eprintln!("[checked main CLI] start {flag} {}", entry.display());
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .args(compiler_options)
        .arg(flag)
        .arg(entry)
        .args(arguments)
        .current_dir(&workspace.0)
        .env("LEAN_PATH", library)
        .env("FLN_IMPORT_REUSE_DIR", full_io_records(workspace))
        .output()
        .expect("run the installed lean main entry");
    let result = Run {
        code: output.status.code().expect("normal process exit"),
        stdout: String::from_utf8(output.stdout).unwrap(),
        stderr: String::from_utf8(output.stderr).unwrap(),
    };
    eprintln!(
        "[checked main CLI] exit {} for {}",
        result.code,
        entry.display()
    );
    result
}

#[test]
fn installed_main_preserves_arguments_effects_output_order_and_process_status() {
    let Some(library) = pinned_lib() else { return };
    for artifact in ["Init/System/IO.olean", "Init/Data/Repr.olean"] {
        assert!(
            library.join(artifact).is_file(),
            "required actual {artifact}"
        );
    }
    let workspace = Workspace::new("lean-executable-main");
    let actions = workspace.0.join("main-actions.txt");
    let actions_path = format!(
        "(System.FilePath.mk {:?})",
        actions.to_str().expect("UTF-8 fixture path"),
    );
    let argument_main = source(
        &workspace,
        "Arguments.lean",
        &format!(
            r#"def mainArgumentText (args : List String) : String :=
  match args with
  | [] => ""
  | arg :: rest => String.append "[" (String.append arg (String.append "]" (mainArgumentText rest)))
#eval (42 : Nat)
def main (args : List String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk {actions_path} IO.FS.Mode.append
  h.putStr "main ran\n"
  let stream ← IO.getStdout
  stream.putStr "main:"
  stream.putStr (mainArgumentText args)
  stream.putStr "\n"
  return 7"#,
        ),
    );
    let arguments = [
        "λ🙂",
        "",
        "--fln-max-steps=0",
        "--",
        "--version",
        "a b",
        "\"\\\n",
        "; #eval 999",
    ];
    let expected = format!(
        "42\nmain:{}\n",
        arguments
            .iter()
            .map(|argument| format!("[{argument}]"))
            .collect::<String>(),
    );
    // Both spellings stop compiler-option parsing before the script path.
    // Every following token is data, including otherwise meaningful options.
    for (index, flag) in ["--run", "-r"].into_iter().enumerate() {
        let result = lean_main(&workspace, &library, &[], flag, &argument_main, &arguments);
        assert_eq!(result.code, 7, "{result:?}");
        assert!(result.stderr.is_empty(), "{result:?}");
        assert_eq!(result.stdout, expected, "{result:?}");
        assert_eq!(
            std::fs::read(&actions).unwrap(),
            "main ran\n".repeat(index + 1).as_bytes()
        );
    }
    let empty = lean_main(&workspace, &library, &[], "--run", &argument_main, &[]);
    assert_eq!(empty.code, 7, "{empty:?}");
    assert_eq!(empty.stdout, "42\nmain:\n", "{empty:?}");
    assert!(empty.stderr.is_empty(), "{empty:?}");
    assert_eq!(
        std::fs::read(&actions).unwrap(),
        b"main ran\nmain ran\nmain ran\n"
    );

    let hello = source(
        &workspace,
        "Hello.lean",
        "def main : IO Unit := IO.println \"hello λ🙂\"",
    );
    let printed = lean_main(&workspace, &library, &[], "--run", &hello, &[]);
    assert_eq!(printed.code, 0, "{printed:?}");
    assert_eq!(printed.stdout, "hello λ🙂\n", "{printed:?}");
    assert!(printed.stderr.is_empty(), "{printed:?}");

    // The engine retains UInt32; the installed Unix process exposes its low
    // byte. Neither an exit status nor Unit/PUnit is a printed #eval result.
    for (file, body, expected_code) in [
        ("WideStatus.lean", "def main : IO UInt32 := pure 256", 0),
        ("SilentUnit.lean", "def main : IO Unit := pure ()", 0),
        (
            "SilentPUnit.lean",
            "def main (_args : List String) : IO PUnit := pure PUnit.unit",
            0,
        ),
    ] {
        let entry = source(&workspace, file, body);
        let result = lean_main(&workspace, &library, &[], "--run", &entry, &arguments);
        assert_eq!(result.code, expected_code, "{result:?}");
        assert!(
            result.stdout.is_empty(),
            "main result must stay silent: {result:?}"
        );
        assert!(result.stderr.is_empty(), "{result:?}");
    }

    let exception = source(
        &workspace,
        "Exception.lean",
        r#"#eval (43 : Nat)
def main : IO Unit := do
  let stream ← IO.getStdout
  stream.putStr "before main exception\n"
  throw (IO.userError "expected main exception λ")"#,
    );
    let raised = lean_main(&workspace, &library, &[], "--run", &exception, &[]);
    assert_eq!(raised.code, 1, "{raised:?}");
    assert_eq!(raised.stdout, "43\nbefore main exception\n", "{raised:?}");
    assert!(
        raised.stderr.contains("expected main exception λ"),
        "{raised:?}"
    );

    let sentinel = workspace.write("sentinel.txt", b"preserved\n");
    let sentinel_path = format!(
        "(System.FilePath.mk {:?})",
        sentinel.to_str().expect("UTF-8 fixture path"),
    );
    let invalid = source(
        &workspace,
        "Invalid.lean",
        &format!(
            r#"def main : IO Nat := do
  let h ← IO.FS.Handle.mk {sentinel_path} IO.FS.Mode.append
  h.putStr "invalid main ran\n"
  return 42"#,
        ),
    );
    let refused = lean_main(&workspace, &library, &[], "--run", &invalid, &[]);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused.stderr.contains("`main` function must have type"),
        "{refused:?}"
    );
    assert_eq!(std::fs::read(&sentinel).unwrap(), b"preserved\n");

    let missing = source(
        &workspace,
        "Missing.lean",
        &format!(
            r#"def dormantAction : IO Unit := do
  let h ← IO.FS.Handle.mk {sentinel_path} IO.FS.Mode.append
  h.putStr "dormant action ran\n""#,
        ),
    );
    let refused = lean_main(&workspace, &library, &[], "--run", &missing, &[]);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused
            .stderr
            .contains("unknown executable declaration `main`"),
        "{refused:?}"
    );
    assert_eq!(std::fs::read(&sentinel).unwrap(), b"preserved\n");

    let bounded = source(
        &workspace,
        "Bounded.lean",
        &format!(
            r#"def main : IO Unit := do
  let h ← IO.FS.Handle.mk {sentinel_path} IO.FS.Mode.append
  h.putStr "budget-exhausted main ran\n""#,
        ),
    );
    let stopped = lean_main(
        &workspace,
        &library,
        &["--fln-max-steps=0"],
        "--run",
        &bounded,
        &[],
    );
    assert_eq!(stopped.code, 3, "{stopped:?}");
    assert!(stopped.stdout.is_empty(), "{stopped:?}");
    assert!(stopped.stderr.contains("ExecutionSteps"), "{stopped:?}");
    assert_eq!(std::fs::read(&sentinel).unwrap(), b"preserved\n");

    // A local dependency's guarded query must be judged before main can run.
    // Both versions retain the same actual external roots and record store.
    let guarded_actions = workspace.write("guard-actions.txt", b"preserved\n");
    let guarded_path = format!(
        "(System.FilePath.mk {:?})",
        guarded_actions.to_str().expect("UTF-8 fixture path"),
    );
    let dependency = source(
        &workspace,
        "GuardDependency.lean",
        "/-- info: 999 -/\n#guard_msgs in\n#eval (42 : Nat)",
    );
    let guarded_main = source(
        &workspace,
        "GuardedMain.lean",
        &format!(
            r#"import GuardDependency
def main : IO Unit := do
  let h ← IO.FS.Handle.mk {guarded_path} IO.FS.Mode.append
  h.putStr "checked dependency\n""#,
        ),
    );
    let refused = lean_main(&workspace, &library, &[], "--run", &guarded_main, &[]);
    assert_eq!(refused.code, 1, "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    assert!(
        refused
            .stderr
            .contains("Docstring on `#guard_msgs` does not match generated message"),
        "{refused:?}",
    );
    assert_eq!(std::fs::read(&guarded_actions).unwrap(), b"preserved\n");
    std::fs::write(
        &dependency,
        format!("{HEADER}/-- info: 42 -/\n#guard_msgs in\n#eval (42 : Nat)\n"),
    )
    .unwrap();
    let accepted = lean_main(&workspace, &library, &[], "-r", &guarded_main, &[]);
    assert_eq!(accepted.code, 0, "{accepted:?}");
    assert!(accepted.stdout.is_empty(), "{accepted:?}");
    assert!(accepted.stderr.is_empty(), "{accepted:?}");
    assert_eq!(
        std::fs::read(&guarded_actions).unwrap(),
        b"preserved\nchecked dependency\n",
    );
}
