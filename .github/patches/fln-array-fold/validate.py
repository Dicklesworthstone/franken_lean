#!/usr/bin/env python3
"""Validate checked bounded Array folds with native Rust and pinned oracle gates.

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
    "CARGO_TARGET_DIR": str(TEMP / "array-fold-target"),
    "CARGO_HTTP_USER_AGENT": UA,
    "FLN_REQUIRE_REFERENCE": "1",
})
LOGS = TEMP / "array-fold-logs"
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
    assert len(files) == 13
    paths = [item["path"] for item in files]
    assert len(set(paths)) == len(paths)
    for path in paths:
        assert re.fullmatch(r"crates/fln/(src|tests)/[A-Za-z0-9_/]+\.(rs|lean|py|txt)", path)
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
    worktree = Path(tempfile.mkdtemp(prefix="fln-array-fold-", dir=TEMP)) / "source"
    git("worktree", "add", "--detach", str(worktree), base)
    print("ARRAY_FOLD_VALIDATION_BASE " + base, flush=True)
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

    # Freeze the exact formatted bytes BEFORE testing. Do not visit other modules.
    fmt = ["rustfmt", "--edition", "2024", "--config", "skip_children=true"]
    rust_paths = [path for path in paths if path.endswith(".rs")]
    run("format-candidate", fmt + rust_paths, worktree)
    frozen = {path: (worktree / path).read_bytes() for path in paths}
    run("format-check", fmt + ["--check"] + rust_paths, worktree)
    git("add", "--", *paths, cwd=worktree)
    assert set(git("diff", "--cached", "--name-only", cwd=worktree).splitlines()) == set(paths)
    for path in paths:
        assert index_entry(path, worktree) == ("100644", blob(frozen[path])), path
    run("diff-check", ["git", "diff", "--cached", "--check"], worktree)

    oracle = run(
        "pinned-array-oracles",
        ["python3", "crates/fln/tests/source_imported_arrays/check_oracle.py",
         "--lean", str(reference_lean)],
        worktree,
    )
    assert "FLN_ARRAY_ORACLE: 70 passed; no skipped or unmarked evaluations" in oracle

    for label, test_filter, count in [
        ("array-fold-model", "runtime::array_fold::tests", 8),
        ("array-iteration-model", "runtime::array_iteration::tests", 6),
        ("global-callable-runtime", "runtime::global::", 55),
        ("well-founded-runtime", "runtime::well_founded::tests", 9),
    ]:
        unit_output = run(
            label,
            ["cargo", "test", "--offline", "--locked", "-p", "fln",
             "--lib", test_filter, "--", "--nocapture", "--test-threads=1"],
            worktree, {"CARGO_PROFILE_TEST_OPT_LEVEL": "0"},
        )
        assert re.search(
            rf"test result: ok\. {count} passed; 0 failed; 0 ignored; 0 measured; \d+ filtered out",
            unit_output,
        ), f"The complete {label} gate did not run"
        assert "SKIP" not in unit_output, f"A required {label} check was skipped"

    # Run every imported-array test once, beginning with the new feature so
    # a real implementation failure is reported before the longer old gate.
    for test_name in [
        "actual_imported_array_folds_execute_replay_and_preserve_authority",
        "dump_pinned_array_iteration_model",
        "actual_imported_array_iteration_executes_replays_and_preserves_authority",
        "dump_pinned_array_fold_model",
    ]:
        output = run(
            test_name,
            ["cargo", "test", "--offline", "--locked", "-p", "fln",
             "--test", "source_imported_arrays", test_name,
             "--", "--exact", "--nocapture", "--test-threads=1"],
            worktree, {"CARGO_PROFILE_TEST_OPT_LEVEL": "2"},
        )
        assert re.search(
            r"test result: ok\. 1 passed; 0 failed; 0 ignored; 0 measured; 3 filtered out",
            output,
        ), f"The exact imported Array test did not run: {test_name}"
        assert "SKIP" not in output, "A required actual Array import check was skipped"
    run(
        "strict-clippy",
        ["cargo", "clippy", "--offline", "--locked", "-p", "fln",
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
        "gates": {"pinnedOracles": "70 passed", "arrayFoldModel": "8 passed",
                  "arrayIterationModel": "6 passed", "globalRuntime": "55 passed",
                  "wellFoundedRuntime": "9 passed", "source_imported_arrays": "4 passed",
                  "strictClippy": "passed"},
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
                print("ARRAY_FOLD_FORMATTED_CHUNK " + json.dumps({
                    **entry, "index": index, "total": len(chunks), "base64": chunk,
                }), flush=True)
    print("ARRAY_FOLD_VALIDATION_RESULT " + json.dumps(result, sort_keys=True), flush=True)
    print("ARRAY_FOLD_VALIDATION_COMPLETE", flush=True)


if __name__ == "__main__":
    main()
