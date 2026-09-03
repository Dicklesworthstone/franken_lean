#![forbid(unsafe_code)]

use std::env;
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::io::{self, Write};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitCode};

const SCHEMA: &str = "fln.agent-anchor/1";
const USAGE: &str = "usage: fln-agent-anchor [--repo PATH] [--output PATH] [--allow-dirty] --bead ID --owner NAME [--path RELATIVE_PATH ...]";

#[derive(Debug, Clone, PartialEq, Eq)]
struct Args {
    repo: PathBuf,
    output: Option<PathBuf>,
    bead: String,
    owner: String,
    paths: Vec<PathBuf>,
    allow_dirty: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Anchor {
    path: String,
    head_blob: String,
    worktree_blob: String,
    dirty: bool,
}

fn main() -> ExitCode {
    match run(env::args_os().skip(1)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("fln-agent-anchor: {error}");
            ExitCode::from(2)
        }
    }
}

fn run(arguments: impl IntoIterator<Item = impl Into<std::ffi::OsString>>) -> Result<(), String> {
    let args = parse_args(arguments)?;
    let root = git_output(&args.repo, ["rev-parse", "--show-toplevel"])?;
    let root = PathBuf::from(root);
    let head = git_output(&root, ["rev-parse", "HEAD"])?;
    let tree = git_output(&root, ["rev-parse", "HEAD^{tree}"])?;
    let status = git_output(&root, ["status", "--porcelain=v1", "--untracked-files=all"])?;
    let repository_dirty = !status.is_empty();
    if repository_dirty && !args.allow_dirty {
        return Err("working tree is dirty; pass --allow-dirty only when the capsule explicitly records an in-flight experiment".to_owned());
    }

    let mut paths = args.paths;
    paths.sort();
    paths.dedup();
    let mut anchors = Vec::with_capacity(paths.len());
    for path in paths {
        let normalized = normalize_relative_path(&path)?;
        let path_text = path_to_git_text(&normalized)?;
        git_status(&root, ["ls-files", "--error-unmatch", "--", &path_text])?;
        let head_spec = format!("HEAD:{path_text}");
        let head_blob = git_output(&root, ["rev-parse", &head_spec])?;
        let worktree_blob = git_output(&root, ["hash-object", "--", &path_text])?;
        let dirty = head_blob != worktree_blob;
        anchors.push(Anchor {
            path: path_text,
            head_blob,
            worktree_blob,
            dirty,
        });
    }

    let document = render_document(
        &args.bead,
        &args.owner,
        &head,
        &tree,
        repository_dirty,
        &anchors,
    );
    match args.output {
        Some(output) => write_atomic(&output, document.as_bytes()),
        None => {
            let mut stdout = io::stdout().lock();
            stdout
                .write_all(document.as_bytes())
                .and_then(|()| stdout.write_all(b"\n"))
                .map_err(|error| format!("write stdout: {error}"))
        }
    }
}

fn parse_args(
    arguments: impl IntoIterator<Item = impl Into<std::ffi::OsString>>,
) -> Result<Args, String> {
    let mut arguments = arguments.into_iter().map(Into::into);
    let mut repo = PathBuf::from(".");
    let mut output = None;
    let mut bead = None;
    let mut owner = None;
    let mut paths = Vec::new();
    let mut allow_dirty = false;

    while let Some(argument) = arguments.next() {
        match argument.to_str() {
            Some("--repo") => repo = next_path(&mut arguments, "--repo")?,
            Some("--output") => output = Some(next_path(&mut arguments, "--output")?),
            Some("--bead") => bead = Some(next_string(&mut arguments, "--bead")?),
            Some("--owner") => owner = Some(next_string(&mut arguments, "--owner")?),
            Some("--path") => paths.push(next_path(&mut arguments, "--path")?),
            Some("--allow-dirty") => allow_dirty = true,
            Some("-h" | "--help") => return Err(USAGE.to_owned()),
            Some(flag) if flag.starts_with('-') => {
                return Err(format!("unknown option {flag:?}; {USAGE}"));
            }
            Some(value) => {
                return Err(format!("unexpected positional argument {value:?}; {USAGE}"));
            }
            None => return Err(format!("argument is not valid UTF-8; {USAGE}")),
        }
    }

    let bead = bead.ok_or_else(|| format!("missing --bead; {USAGE}"))?;
    let owner = owner.ok_or_else(|| format!("missing --owner; {USAGE}"))?;
    if bead.trim().is_empty() {
        return Err("--bead may not be empty".to_owned());
    }
    if owner.trim().is_empty() {
        return Err("--owner may not be empty".to_owned());
    }
    Ok(Args {
        repo,
        output,
        bead,
        owner,
        paths,
        allow_dirty,
    })
}

fn next_path<I>(arguments: &mut I, flag: &str) -> Result<PathBuf, String>
where
    I: Iterator<Item = std::ffi::OsString>,
{
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("{flag} requires a value; {USAGE}"))
}

fn next_string<I>(arguments: &mut I, flag: &str) -> Result<String, String>
where
    I: Iterator<Item = std::ffi::OsString>,
{
    arguments
        .next()
        .ok_or_else(|| format!("{flag} requires a value; {USAGE}"))?
        .into_string()
        .map_err(|_| format!("{flag} value is not valid UTF-8"))
}

fn normalize_relative_path(path: &Path) -> Result<PathBuf, String> {
    if path.as_os_str().is_empty() {
        return Err("anchor path may not be empty".to_owned());
    }
    if path.is_absolute() {
        return Err(format!(
            "anchor path must be repository-relative: {}",
            path.display()
        ));
    }
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Normal(value) => normalized.push(value),
            Component::CurDir => {}
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(format!(
                    "anchor path escapes the repository: {}",
                    path.display()
                ));
            }
        }
    }
    if normalized.as_os_str().is_empty() {
        return Err("anchor path resolves to the repository root, not a file".to_owned());
    }
    Ok(normalized)
}

fn path_to_git_text(path: &Path) -> Result<String, String> {
    let mut rendered = String::new();
    for (index, component) in path.components().enumerate() {
        let Component::Normal(value) = component else {
            return Err(format!("non-normal path component in {}", path.display()));
        };
        let value = value
            .to_str()
            .ok_or_else(|| format!("anchor path is not valid UTF-8: {}", path.display()))?;
        if index != 0 {
            rendered.push('/');
        }
        rendered.push_str(value);
    }
    Ok(rendered)
}

fn git_output<const N: usize>(repo: &Path, args: [&str; N]) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .map_err(|error| format!("launch git in {}: {error}", repo.display()))?;
    if !output.status.success() {
        return Err(format_command_failure("git", repo, &args, &output.stderr));
    }
    let text =
        String::from_utf8(output.stdout).map_err(|_| "git produced non-UTF-8 output".to_owned())?;
    Ok(text.trim_end_matches(['\r', '\n']).to_owned())
}

fn git_status<const N: usize>(repo: &Path, args: [&str; N]) -> Result<(), String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .map_err(|error| format!("launch git in {}: {error}", repo.display()))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format_command_failure("git", repo, &args, &output.stderr))
    }
}

fn format_command_failure(command: &str, repo: &Path, args: &[&str], stderr: &[u8]) -> String {
    let rendered = String::from_utf8_lossy(stderr);
    format!(
        "{command} -C {} {} failed: {}",
        repo.display(),
        args.join(" "),
        rendered.trim()
    )
}

fn render_document(
    bead: &str,
    owner: &str,
    head: &str,
    tree: &str,
    repository_dirty: bool,
    anchors: &[Anchor],
) -> String {
    let mut output = String::new();
    write!(
        output,
        "{{\"schema\":\"{SCHEMA}\",\"bead\":{},\"owner\":{},\"git\":{{\"head\":{},\"tree\":{},\"dirty\":{repository_dirty}}},\"anchors\":[",
        json_string(bead),
        json_string(owner),
        json_string(head),
        json_string(tree),
    )
    .expect("writing to a String cannot fail");
    for (index, anchor) in anchors.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        write!(
            output,
            "{{\"path\":{},\"head_blob\":{},\"worktree_blob\":{},\"dirty\":{}}}",
            json_string(&anchor.path),
            json_string(&anchor.head_blob),
            json_string(&anchor.worktree_blob),
            anchor.dirty,
        )
        .expect("writing to a String cannot fail");
    }
    output.push_str("]}");
    output
}

fn json_string(value: &str) -> String {
    let mut output = String::with_capacity(value.len().saturating_add(2));
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                write!(output, "\\u{:04x}", u32::from(character))
                    .expect("writing to a String cannot fail");
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

fn write_atomic(path: &Path, contents: &[u8]) -> Result<(), String> {
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent)
        .map_err(|error| format!("create output directory {}: {error}", parent.display()))?;
    let file_name = path
        .file_name()
        .and_then(OsStr::to_str)
        .ok_or_else(|| format!("output path has no UTF-8 file name: {}", path.display()))?;
    let temporary = parent.join(format!(".{file_name}.tmp-{}", std::process::id()));
    {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|error| format!("create temporary output {}: {error}", temporary.display()))?;
        file.write_all(contents)
            .and_then(|()| file.write_all(b"\n"))
            .and_then(|()| file.sync_all())
            .map_err(|error| format!("write temporary output {}: {error}", temporary.display()))?;
    }
    fs::rename(&temporary, path).map_err(|error| {
        let _ = fs::remove_file(&temporary);
        format!(
            "replace {} with {}: {error}",
            path.display(),
            temporary.display()
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relative_paths_are_normalized_without_permitting_escape() {
        assert_eq!(
            normalize_relative_path(Path::new("./crates/fln-core/src/lib.rs")).unwrap(),
            PathBuf::from("crates/fln-core/src/lib.rs")
        );
        assert!(normalize_relative_path(Path::new("../AGENTS.md")).is_err());
        assert!(normalize_relative_path(Path::new("/tmp/file")).is_err());
        assert!(normalize_relative_path(Path::new(".")).is_err());
    }

    #[test]
    fn json_strings_preserve_unicode_and_escape_controls() {
        assert_eq!(json_string("a\n\"β\\\u{0007}"), "\"a\\n\\\"β\\\\\\u0007\"");
    }

    #[test]
    fn documents_are_deterministic_and_keep_both_blob_identities() {
        let anchors = vec![Anchor {
            path: "crates/fln-checker/src/admit.rs".to_owned(),
            head_blob: "111".to_owned(),
            worktree_blob: "222".to_owned(),
            dirty: true,
        }];
        assert_eq!(
            render_document("fln-51y8", "agent", "abc", "def", true, &anchors),
            concat!(
                "{\"schema\":\"fln.agent-anchor/1\",",
                "\"bead\":\"fln-51y8\",\"owner\":\"agent\",",
                "\"git\":{\"head\":\"abc\",\"tree\":\"def\",\"dirty\":true},",
                "\"anchors\":[{\"path\":\"crates/fln-checker/src/admit.rs\",",
                "\"head_blob\":\"111\",\"worktree_blob\":\"222\",\"dirty\":true}]}"
            )
        );
    }

    #[test]
    fn arguments_require_bead_and_owner_and_collect_paths() {
        let args = parse_args([
            "--repo",
            "repo",
            "--bead",
            "fln-51y8",
            "--owner",
            "agent",
            "--path",
            "a",
            "--path",
            "b",
            "--allow-dirty",
        ])
        .unwrap();
        assert_eq!(args.repo, PathBuf::from("repo"));
        assert_eq!(args.bead, "fln-51y8");
        assert_eq!(args.owner, "agent");
        assert_eq!(args.paths, vec![PathBuf::from("a"), PathBuf::from("b")]);
        assert!(args.allow_dirty);
    }
}
