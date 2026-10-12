#!/usr/bin/env python3
"""Require every shared mutable-return result and effect trace to match the exact pin."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tempfile

COUNT = 29
WITNESS_MARKER = "-- FLN_MUTABLE_MONAD_WITNESSES\n"
WITNESSES = """
-- Dictionary construction only: both fields use the shared observable operations.
instance mutableStateOracleMonad : Monad MutableState :=
  { pure := fun value => mutableStatePure value,
    bind := fun action next => mutableStateBind action next }
instance mutableTraceOracleMonad : Monad MutableTrace :=
  { pure := fun value => mutableTracePure value,
    bind := fun action next => mutableTraceBind action next }
"""

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True)
    arguments = parser.parse_args()
    version = subprocess.run(
        [arguments.lean, "--version"], capture_output=True, text=True,
        encoding="utf-8", timeout=10, check=True,
    )
    assert "version 4.32.0" in version.stdout, version.stdout
    fixture = pathlib.Path(__file__).with_name("mutable_returns.lean")
    expected = {}
    expected_path = fixture.with_name("mutable_returns.expected.tsv")
    for line in expected_path.read_text(encoding="utf-8").splitlines():
        label, kind, value = line.split("\t", 2)
        assert label not in expected and kind in ("Nat", "String")
        expected[label] = [kind, value]
    assert len(expected) == COUNT
    shared = fixture.read_text(encoding="utf-8")
    assert shared.count(WITNESS_MARKER) == 1
    source = shared.replace(WITNESS_MARKER, WITNESS_MARKER + WITNESSES)
    probes = {}
    pending = None
    labels = set()
    for number, raw in enumerate(source.splitlines(), 1):
        line = raw.strip()
        if line.startswith("-- FLN_MUTABLE_PROBE "):
            assert pending is None, (number, "duplicate probe marker")
            label, kind = line.removeprefix("-- FLN_MUTABLE_PROBE ").split()
            assert label not in labels and kind in ("Nat", "String")
            labels.add(label)
            pending = (label, kind)
        elif line.startswith("#eval "):
            assert pending is not None, (number, "unmarked evaluation")
            probes[number] = pending
            pending = None
    assert pending is None and len(probes) == COUNT
    assert expected.keys() == labels, ("exact fixed probe coverage", expected, labels)
    with tempfile.TemporaryDirectory(prefix="fln-mutable-return-pin-") as directory:
        entry = pathlib.Path(directory) / "MutableReturns.lean"
        entry.write_text(source, encoding="utf-8")
        result = subprocess.run(
            [arguments.lean, "--json", "-j1", "-M2048", "-s65536", "-T200000", str(entry)],
            capture_output=True, text=True, encoding="utf-8", timeout=120, check=False,
        )
    assert len(result.stdout) + len(result.stderr) <= 4 * 1024 * 1024
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    observed = {}
    for raw in (result.stdout + "\n" + result.stderr).splitlines():
        if not raw.strip():
            continue
        message = json.loads(raw)
        severity = message.get("severity")
        assert severity in ("information", "warning"), message
        if severity == "warning":
            print("pin warning:", message["data"])
            continue
        line = message["pos"]["line"]
        assert line in probes and line not in observed, message
        label, kind = probes[line]
        data = message["data"]
        assert isinstance(data, str)
        if kind == "Nat":
            assert re.fullmatch(r"[0-9]+", data.strip()), message
            value = str(int(data.strip()))
        else:
            value = json.loads(data)
            assert isinstance(value, str)
        assert "\t" not in value and "\n" not in value and "\r" not in value
        assert [kind, value] == expected[label], (label, value, expected[label])
        observed[line] = (label, kind, value)
    assert observed.keys() == probes.keys(), ("missing evaluations", observed, probes)
    print("FLN_MUTABLE_RETURN_SHARED_SHA256", hashlib.sha256(shared.encode("utf-8")).hexdigest())
    print("FLN_MUTABLE_RETURN_PIN_OBSERVATIONS_BEGIN")
    for line in probes:
        print("\t".join(observed[line]))
    print("FLN_MUTABLE_RETURN_PIN_OBSERVATIONS_END")
    print(f"FLN_MUTABLE_RETURN_ORACLE: {COUNT} passed; no skipped or unmarked evaluations")

if __name__ == "__main__":
    main()
