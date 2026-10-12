#!/usr/bin/env python3
"""Validate preserved well-founded source with the repository's native Rust gates.

This runner has read-only repository permissions. It reports exact tested blobs;
publication is a separate, explicit GitHub compare-and-swap update to main.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

PAYLOAD = Path(__file__).resolve().parent
CHECKOUT = Path(os.environ["GITHUB_WORKSPACE"]).resolve()
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
MANIFEST = json.loads((PAYLOAD / "candidate.json").read_text())
UA = "OpenAI File Downloader, XaiImageApiFetch/1.0"
ENV = os.environ.copy()
ENV.update({
    "CARGO_BUILD_JOBS": "1",
    "CARGO_PROFILE_DEV_DEBUG": "0",
    "CARGO_PROFILE_TEST_DEBUG": "0",
    "CARGO_INCREMENTAL": "0",
    "CARGO_TARGET_DIR": str(TEMP / "well-founded-target"),
    "CARGO_HTTP_USER_AGENT": UA,
    "FLN_REQUIRE_REFERENCE": "1",
})
LOGS = TEMP / "well-founded-logs"
LOGS.mkdir(exist_ok=True)


def git(*args, cwd=CHECKOUT):
    return subprocess.check_output(
        ["git", "-c", "http.userAgent=" + UA, *args], cwd=cwd, text=True
    ).strip()


def blob(data):
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def run(label, command, cwd, extra_env=None):
    print("::group::" + label, flush=True)
    print("+ " + shlex.join(command), flush=True)
    env = ENV | (extra_env or {})
    lines = []
    with (LOGS / (label + ".log")).open("w") as log:
        process = subprocess.Popen(
            command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, bufsize=1,
        )
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="", flush=True)
            log.write(line)
            lines.append(line)
        code = process.wait()
    print("::endgroup::", flush=True)
    if code:
        raise SystemExit(f"{label} failed with exit status {code}")
    return "".join(lines)


def index_entry(path, cwd):
    entry = git("ls-files", "--stage", "--", path, cwd=cwd)
    if not entry:
        return None
    header, actual = entry.split("\t", 1)
    mode, sha, stage = header.split()
    assert actual == path and stage == "0", (path, entry)
    return mode, sha


def main():
    assert MANIFEST["version"] == 1
    files = MANIFEST["files"]
    assert len(files) == 11
    paths = [item["path"] for item in files]
    assert len(set(paths)) == len(paths)
    for path in paths:
        assert re.fullmatch(r"crates/(fln-elab/src/source|fln/tests)/[A-Za-z0-9_/]+\.rs", path)
        assert ".." not in Path(path).parts

    assert ENV["FLN_REQUIRE_REFERENCE"] == "1"
    reference_lib = Path(ENV["FLN_REFERENCE_LIB"])
    reference_lean = Path(ENV["FLN_REFERENCE_LEAN"])
    assert (reference_lib / "Init.olean").is_file(), reference_lib
    assert subprocess.check_output([reference_lean, "--githash"], text=True).strip() == (
        "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
    )
    assert subprocess.check_output([reference_lean, "--short-version"], text=True).strip() == "4.32.0"

    git("fetch", "--no-tags", "origin", "main")
    base = git("rev-parse", "FETCH_HEAD")
    worktree = Path(tempfile.mkdtemp(prefix="fln-wf-", dir=TEMP)) / "source"
    git("worktree", "add", "--detach", str(worktree), base)
    print("WF_VALIDATION_BASE " + base, flush=True)
    rustc = run("pinned-rust", ["rustc", "-vV"], worktree)
    assert "commit-hash: 90850177249efe0321573c569aec5d12b257f8d6" in rustc

    original = {}
    for item in files:
        path = item["path"]
        expected = None if item["baselineSha"] is None else (
            item["baselineMode"], item["baselineSha"]
        )
        assert index_entry(path, worktree) == expected, f"Concurrent source overlap: {path}"
        data = (PAYLOAD / "candidate" / path).read_bytes()
        assert len(data) == item["bytes"] and blob(data) == item["blobSha"], path
        target = worktree / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(0o644)
        original[path] = data

    diagnostic = ENV.get("FLN_WF_RESOURCE_DIAGNOSTIC") == "1"
    if diagnostic:
        # This temporary overlay diagnoses an unchanged limit. It is never a
        # production candidate and cannot emit a successful validation result.
        edits = json.loads((PAYLOAD / "diagnostic.json").read_text())
        for item in edits:
            target = worktree / item["path"]
            data = target.read_bytes()
            assert blob(data) == item["expectedBlob"], item["path"]
            source = data.decode("utf-8")
            for edit in item["edits"]:
                assert source.count(edit["needle"]) == edit["count"], edit["needle"]
                source = source.replace(edit["needle"], edit["replacement"])
            target.write_text(source)

    # Freeze the exact formatted bytes BEFORE testing. Do not visit other modules.
    fmt = ["rustfmt", "--edition", "2024", "--config", "skip_children=true"]
    run("format-candidate", fmt + paths, worktree)
    frozen = {path: (worktree / path).read_bytes() for path in paths}
    run("format-check", fmt + ["--check"] + paths, worktree)
    git("add", "--", *paths, cwd=worktree)
    assert set(git("diff", "--cached", "--name-only", cwd=worktree).splitlines()) == set(paths)
    for path in paths:
        assert index_entry(path, worktree) == ("100644", blob(frozen[path])), path
    run("diff-check", ["git", "diff", "--cached", "--check"], worktree)

    command = [
        "cargo", "test", "--offline", "--locked", "-p", "fln",
        "--test", "source_well_founded",
    ]
    if diagnostic:
        command += ["native_automatic_well_founded_termination", "--", "--exact"]
    else:
        command += ["--"]
    command += ["--nocapture", "--test-threads=1"]
    output = run(
        "native-well-founded", command, worktree,
        {"CARGO_PROFILE_TEST_OPT_LEVEL": "2"},
    )
    if diagnostic:
        raise SystemExit("Diagnostic-only run cannot authorize source publication")
    assert re.search(
        r"test result: ok\. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out",
        output,
    ), "The full three-test well-founded gate did not run"
    assert "SKIP" not in output, "A required differential Reference check was skipped"
    run(
        "strict-clippy",
        ["cargo", "clippy", "--offline", "--locked", "-p", "fln-elab", "-p", "fln",
         "--lib", "--", "-D", "warnings"],
        worktree,
    )

    assert git("diff", "--name-only", cwd=worktree) == "", "Tracked source changed during validation"
    assert git("ls-files", "--others", "--exclude-standard", cwd=worktree) == "", "Unexpected untracked source"
    assert set(git("diff", "--cached", "--name-only", cwd=worktree).splitlines()) == set(paths)
    for path in paths:
        assert (worktree / path).read_bytes() == frozen[path], path
        assert index_entry(path, worktree) == ("100644", blob(frozen[path])), path

    result = {
        "version": 1, "validatedBase": base,
        "candidateTree": MANIFEST["candidateTree"],
        "gates": {"source_well_founded": "3 passed", "strictClippy": "passed"},
        "files": [],
    }
    for path in paths:
        data = frozen[path]
        changed = data != original[path]
        entry = {"path": path, "blobSha": blob(data), "bytes": len(data), "formatted": changed}
        result["files"].append(entry)
        if changed:
            encoded = base64.b64encode(data).decode("ascii")
            chunks = [encoded[i:i + 12000] for i in range(0, len(encoded), 12000)]
            for index, chunk in enumerate(chunks):
                print("WF_FORMATTED_CHUNK " + json.dumps({
                    **entry, "index": index, "total": len(chunks), "base64": chunk,
                }), flush=True)
    print("WF_VALIDATION_RESULT " + json.dumps(result, sort_keys=True), flush=True)
    print("WF_VALIDATION_COMPLETE", flush=True)


if __name__ == "__main__":
    main()
