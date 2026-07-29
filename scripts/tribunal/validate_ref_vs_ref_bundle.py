#!/usr/bin/env -S python3 -I -S
"""Independent validator for a reference_reference_no_mock_e2e bundle (bead fln-euo).

Separate from the writer on purpose — "validates the final bundle independently" is the
epic's own clause, and a bundle whose completeness is asserted by the process that wrote it
is asserting its own memory. This re-reads the NDJSON as bytes on disk and re-hashes the
retained plant artifacts against the digests recorded when they were written.

Refusals, each named:
  - a row that does not parse, or carries a foreign schema/run/scenario;
  - any step recorded failed inside a bundle presented as passing;
  - a step outside the closed roster (an undeclared step is evidence nobody reviewed);
  - a required step absent (silence is not success — the exact hollow-green shape);
  - elapsed_ms running backwards (rows from two runs interleaved);
  - a retained artifact whose bytes no longer hash to their recorded digest.

Exit 0 on a valid bundle; exit 1 with the refusal on stderr otherwise. Invoked by
scripts/tribunal/ref_vs_ref.sh as its bundle_validation step and usable standalone:

    python3 -I -S scripts/tribunal/validate_ref_vs_ref_bundle.py <run.ndjson> <run-id> <art-dir>
"""

import hashlib
import json
import sys

REQUIRED = {
    "run_start",
    "oracle",
    "determinism",
    "baseline",
    "seeded_divergence",
    "seeded_divergence_line",
    "seeded_divergence_subline",
    "seeded_divergence_diagnostic",
    "seeded_divergence_exit",
    "non_authoritative_outcome",
    "recovery",
}
ALLOWED = REQUIRED | {"plant_matrix", "bundle_validation", "run_end"}


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: validate_ref_vs_ref_bundle.py <run.ndjson> <run-id> <art-dir>", file=sys.stderr)
        return 2
    log, run_id, art_dir = sys.argv[1], sys.argv[2], sys.argv[3]

    seen = []
    last_elapsed = -1
    with open(log, encoding="utf-8") as handle:
        for number, line in enumerate(handle, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                print(f"{log}:{number}: unparseable row: {error}", file=sys.stderr)
                return 1
            checks = [
                (row.get("schema") == "fln-e2e/1", f"foreign schema {row.get('schema')!r}"),
                (row.get("run_id") == run_id, "a foreign run's row is in this bundle"),
                (
                    row.get("scenario") == "reference_reference_no_mock_e2e",
                    f"foreign scenario {row.get('scenario')!r}",
                ),
                (row.get("status") in ("started", "passed"), f"status {row.get('status')!r}"),
                (row.get("step") in ALLOWED, f"undeclared step {row.get('step')!r}"),
                (row.get("elapsed_ms", -1) >= last_elapsed, "elapsed_ms ran backwards"),
            ]
            for ok, why in checks:
                if not ok:
                    print(f"{log}:{number}: {why}", file=sys.stderr)
                    return 1
            last_elapsed = row["elapsed_ms"]
            seen.append(row["step"])

    missing = REQUIRED - set(seen)
    if missing:
        print(f"required steps absent from the bundle: {sorted(missing)}", file=sys.stderr)
        return 1

    digests = 0
    with open(f"{art_dir}/plant-digests.txt", encoding="utf-8") as handle:
        for entry in handle:
            digest, name = entry.split()
            with open(f"{art_dir}/{name}", "rb") as artifact:
                actual = hashlib.sha256(artifact.read()).hexdigest()
            if actual != digest:
                print(f"retained artifact {name} no longer hashes to its record", file=sys.stderr)
                return 1
            digests += 1
    if digests == 0:
        print("zero recorded plant digests — an empty ledger validates nothing", file=sys.stderr)
        return 1

    print(f"bundle valid: {len(seen)} rows, {digests} artifact digests re-verified", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
