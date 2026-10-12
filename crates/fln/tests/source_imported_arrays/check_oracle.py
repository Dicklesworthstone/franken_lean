#!/usr/bin/env python3
"""Compare the exact shared Array programs against the actual pinned Lean."""
import argparse
import json
import pathlib
import re
import subprocess


def expected_values(path, count):
    expected = {}
    pending = None
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if line.startswith("-- FLN_EXPECT_NAT "):
            assert pending is None, f"{path}:{number}: duplicate expectation"
            value = line.removeprefix("-- FLN_EXPECT_NAT ")
            assert re.fullmatch(r"[0-9]+", value), (path, number, value)
            pending = ("Nat", int(value))
        elif line.startswith("-- FLN_EXPECT_STRING "):
            assert pending is None, f"{path}:{number}: duplicate expectation"
            pending = ("String", line.removeprefix("-- FLN_EXPECT_STRING "))
        elif line.startswith("#eval "):
            assert pending is not None, f"{path}:{number}: unmarked evaluation"
            expected[number] = pending
            pending = None
    assert pending is None, f"{path}: expectation without an evaluation"
    assert len(expected) == count, f"{path}: preserve all {count} shared probes"
    return expected


def check(lean, path, count):
    expected = expected_values(path, count)
    completed = subprocess.run(
        [lean, "--json", "-j1", "-M2048", "-s65536", "-T200000", str(path)],
        text=True,
        encoding="utf-8",
        capture_output=True,
        timeout=120,
        check=False,
    )
    assert len(completed.stdout) + len(completed.stderr) <= 4 * 1024 * 1024, (
        path, "unexpectedly large bounded oracle output"
    )
    assert completed.returncode == 0, (
        path, completed.returncode, completed.stdout, completed.stderr
    )
    observed = {}
    for raw in (completed.stdout + "\n" + completed.stderr).splitlines():
        if not raw.strip():
            continue
        message = json.loads(raw)
        assert isinstance(message, dict), (path, message)
        severity = message.get("severity")
        assert severity in ("information", "warning"), (path, message)
        if severity == "warning":
            print(f"{path.name}: pin warning: {message['data']}")
            continue
        line = message["pos"]["line"]
        assert line in expected and line not in observed, (path, message, expected)
        kind, wanted = expected[line]
        data = message["data"]
        assert isinstance(data, str), (path, message)
        if kind == "Nat":
            assert re.fullmatch(r"[0-9]+", data.strip()), (path, message)
            actual = int(data.strip())
        else:
            actual = json.loads(data)
            assert isinstance(actual, str), (path, message)
        assert actual == wanted, (path, line, actual, wanted)
        observed[line] = actual
    assert observed.keys() == expected.keys(), (path, "missing actual evaluations", observed, expected)
    print(f"{path.name}: {len(observed)} actual pinned Array evaluations matched")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, help="the installed pinned 4.32.0 Lean executable")
    arguments = parser.parse_args()
    version = subprocess.run(
        [arguments.lean, "--version"],
        text=True,
        encoding="utf-8",
        capture_output=True,
        timeout=10,
        check=True,
    )
    assert "version 4.32.0" in version.stdout, version.stdout
    directory = pathlib.Path(__file__).resolve().parent
    check(arguments.lean, directory / "programs.lean", 23)
    check(arguments.lean, directory / "effects.lean", 20)
    print("FLN_ARRAY_ORACLE: 43 passed; no skipped or unmarked evaluations")


if __name__ == "__main__":
    main()
