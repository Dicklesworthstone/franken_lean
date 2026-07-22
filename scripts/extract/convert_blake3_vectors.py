#!/usr/bin/env python3
"""Convert the official BLAKE3 test vectors JSON into the fln fixture line format.

Input : test_vectors.json from the upstream BLAKE3 repository
        (https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/master/test_vectors/test_vectors.json)
Output: crates/fln-hash/fixtures/blake3_vectors.txt with one line per case:
        input_len|hash_hex|keyed_hash_hex|derive_key_hex

The upstream JSON defines the input bytes for each case as the repeating
pattern 0,1,2,...,249,0,1,... of length input_len; the fixture stores only
lengths and expected hex, and the Rust tests regenerate the pattern.

Usage: python3 scripts/extract/convert_blake3_vectors.py <test_vectors.json> <out.txt>
"""

import json
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
        "# input bytes for each case: repeating pattern 0,1,...,249,0,1,... "
        "of length input_len",
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
    main(sys.argv)
