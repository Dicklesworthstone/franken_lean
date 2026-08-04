#!/usr/bin/env -S python3 -I -S
"""Convert the official BLAKE3 test vectors JSON into the fln fixture line format.

Input : test_vectors.json from the upstream BLAKE3 repository
        (https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/master/test_vectors/test_vectors.json)
Output: crates/fln-hash/fixtures/blake3_vectors.txt with one line per case:
        input_len|hash_hex|keyed_hash_hex|derive_key_hex

The upstream JSON defines the input bytes for each case as the repeating
pattern 0,1,2,...,250,0,1,... of length input_len -- modulus 251, which is
prime so the pattern never aligns with a block boundary. The fixture stores
only lengths and expected hex, and the Rust tests regenerate the pattern.

The emitted header below is the ONLY statement of that convention a future
reader gets, and fln-hash pins its own `test_input` against it, so the two
strings are one fact in two files: change either and change both.

Usage: python3 scripts/extract/convert_blake3_vectors.py <test_vectors.json> <out.txt>
"""

import json
import os
import sys

SOURCE_URL = (
    "https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/"
    "master/test_vectors/test_vectors.json"
)
SCHEMA = "fln-blake3-vectors/1"

HEX_DIGITS = set("0123456789abcdef")


def fail(msg: str) -> None:
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


def main(argv: list[str]) -> None:
    if len(argv) != 3:
        fail(f"usage: {argv[0]} <test_vectors.json> <out.txt>")

    with open(argv[1], encoding="utf-8") as f:
        data = json.load(f)

    key = data["key"]
    context = data["context_string"]
    cases = data["cases"]
    if not cases:
        fail("no cases in input JSON")

    lines = [
        f"# provenance: converted from {SOURCE_URL}",
        f"# provenance: keyed_hash key = {json.dumps(key)} (ASCII, 32 bytes)",
        f"# provenance: derive_key context = {json.dumps(context)}",
        "# input bytes for each case: repeating pattern 0,1,...,250,0,1,... "
        "of length input_len (modulus 251)",
        f"# schema {SCHEMA}",
        "# format: input_len|hash_hex|keyed_hash_hex|derive_key_hex",
    ]

    if len(key.encode("ascii")) != 32:
        fail("keyed-hash key from JSON header is not 32 ASCII bytes")

    for case in cases:
        input_len = case["input_len"]
        if not isinstance(input_len, int) or input_len < 0:
            fail(f"bad input_len: {input_len!r}")
        row = [str(input_len)]
        for field in ("hash", "keyed_hash", "derive_key"):
            hexval = case[field]
            if len(hexval) % 2 != 0 or not set(hexval) <= HEX_DIGITS:
                fail(f"case {input_len}: field {field} is not lowercase hex")
            row.append(hexval)
        lines.append("|".join(row))

    with open(argv[2], "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"wrote {len(cases)} vectors to {argv[2]}")


if __name__ == "__main__":
    hostile_python = sorted(name for name in os.environ if name.startswith("PYTHON"))
    if not all(
        (
            sys.flags.isolated,
            sys.flags.ignore_environment,
            sys.flags.no_site,
            sys.flags.no_user_site,
            sys.flags.safe_path,
        )
    ):
        print("error: sealed_interpreter_unsealed_startup", file=sys.stderr)
        raise SystemExit(2)
    if hostile_python:
        print(
            "error: sealed_interpreter_hostile_environment names="
            + ",".join(hostile_python),
            file=sys.stderr,
        )
        raise SystemExit(2)
    main(sys.argv)
