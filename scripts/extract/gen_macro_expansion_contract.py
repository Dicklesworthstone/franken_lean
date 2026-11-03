#!/usr/bin/env python3
"""Extract the nested macro ABI from the published, exact pinned artifacts.

The native fln-olean decoder reads the official release's Init/Prelude.ir and
Init/Prelude.olean as data. No Reference implementation code executes. Both
digests are fixed to the verified official v4.32.0 Linux release archive;
changing the epoch or either artifact is a refusal, never a guessed layout.

    python3 scripts/extract/gen_macro_expansion_contract.py \
        --prelude-ir /path/to/lib/lean/Init/Prelude.ir \
        --prelude-olean /path/to/lib/lean/Init/Prelude.olean [--check]

An optional --lean cross-check compiles MacroLayoutModule.lean with the exact
pinned Reference and compares its independently emitted ABI with these values.
"""

import argparse
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "crates/fln-rt/src/macro_expansion_abi_generated.rs"
FIXTURE = ROOT / "crates/fln-olean/fixtures/ir/MacroLayoutModule.lean"
PIN = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
RELEASE = "https://github.com/leanprover/lean4/releases/download/v4.32.0/lean-4.32.0-linux.tar.zst"
ARCHIVE_SHA256 = "fca846f3588724a38ad19ee40292c67cb7438d7555903372e3308eef795ba516"
IR_SHA256 = "b92dd3951473cb32443ec94bc34223e05f392aa640085c0de442b735a0c01b5a"
OLEAN_SHA256 = "f6e75f21565d23e5e80c65489d2bbafbbbe9270d0ecb9a6656bf76c21d88d2c0"


def checked_digest(path, expected):
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"published Reference artifact mismatch: {path}: {actual}")


def live_cross_check(lean, values):
    version = subprocess.run([lean, "--githash"], check=True, capture_output=True,
                             text=True, timeout=30)
    if version.stdout.strip() != PIN:
        raise ValueError("live Reference commit mismatch")
    compiled = subprocess.run([lean, "--stdin"], input=FIXTURE.read_text(),
                              capture_output=True, text=True, timeout=120)
    if compiled.returncode:
        raise ValueError(f"macro layout fixture failed: {compiled.stdout}{compiled.stderr}")
    trace = compiled.stdout + compiled.stderr
    signature = re.search(
        r"(?m)^    def FrankenLean\.MacroLayout\.macroExpandMacro (.*?) : (\w+) :=$", trace)
    if signature is None:
        raise ValueError("missing live macroExpandMacro telescope")
    parameters = re.findall(r"\(x_\d+ : (@& )?(\w+)\)", signature[1])
    if ([bool(borrow) for borrow, _ in parameters] != values["borrowed"]
            or [ty for _, ty in parameters] != values["parameters"]
            or signature[2] != values["result"]):
        raise ValueError("live and published-IR macro telescopes differ")
    for function, key in [("contextDepth", "depth"), ("contextMaxDepth", "max_depth"),
                          ("contextRef", "reference")]:
        getter = re.search(
            rf"(?m)^    def FrankenLean\.MacroLayout\.{function} \((x_\d+) : @& obj\) : (?:tobj|obj) :=\n"
            r"(.*?)(?=^    def |^\[|\Z)", trace, re.S)
        if getter is None:
            raise ValueError(f"missing live getter: {function}")
        projection = re.fullmatch(
            rf"\s*let (x_\d+) : (?:tobj|obj) := proj\[(\d+)\] {re.escape(getter[1])};\s*inc \1;\s*ret \1\s*",
            getter[2])
        if projection is None or int(projection[2]) != values[key]:
            raise ValueError(f"live and published-artifact getter differs: {function}")
    for name in ["Option.some", "Option.none"]:
        matches = re.findall(
            rf"ctor_(\d+)(?:\.(\d+)\.(\d+))?\[{re.escape(name)}\]([^;\n]*);", trace)
        if not matches:
            raise ValueError(f"missing live constructor: {name}")
        for tag, usize, scalar, arguments in matches:
            fields = len(re.findall(r"\bx_\d+\b|◾", arguments))
            if usize not in ("", "0") or [int(tag), fields, int(scalar or 0)] != values[name]:
                raise ValueError(f"live and published-IR constructor differs: {name}")


def generate(args):
    lock = (ROOT / "SUITE.lock").read_text()
    if re.search(r'(?m)^reference leanprover/lean4 .*\bcommit=' + PIN + r'\b', lock) is None:
        raise ValueError("published artifact epoch differs from SUITE.lock")
    checked_digest(args.prelude_ir, IR_SHA256)
    checked_digest(args.prelude_olean, OLEAN_SHA256)
    decoded = subprocess.run(
        ["cargo", "run", "--offline", "--quiet", "-p", "fln-olean", "--example",
         "extract_macro_expansion_abi", "--", str(args.prelude_ir.resolve()),
         str(args.prelude_olean.resolve())],
        cwd=ROOT, capture_output=True, text=True, timeout=300)
    if decoded.returncode:
        raise ValueError(f"native artifact extraction failed: {decoded.stderr}")
    values = json.loads(decoded.stdout)
    if args.lean:
        live_cross_check(args.lean, values)
    tag, fields, scalar = values["Option.some"]
    none, none_fields, none_scalar = values["Option.none"]
    if none_fields or none_scalar:
        raise ValueError("Option.none has a non-nullary compiled layout")
    borrowed = ", ".join(str(value).lower() for value in values["borrowed"])
    parameters = ", ".join(json.dumps(value) for value in values["parameters"])
    return "\n".join([
        "// Generated by scripts/extract/gen_macro_expansion_contract.py; do not edit.",
        f"// Reference commit: {PIN}",
        f"// Official release: {RELEASE}",
        f"// Release archive SHA-256: {ARCHIVE_SHA256}",
        f"// Init/Prelude.ir SHA-256: {IR_SHA256}",
        f"// Init/Prelude.olean SHA-256: {OLEAN_SHA256}",
        "//! Exact compiled ABI for native recursive macro expansion.",
        "//! Extracted by native decoding of published Reference artifacts; no IR executes.",
        "", "use crate::syntax_abi_generated::CtorLayout;", "",
        "/// `Option.some`.", "pub const OPTION_SOME: CtorLayout = CtorLayout {",
        f"    tag: {tag},", f"    object_fields: {fields},",
        f"    scalar_bytes: {scalar},", "};", "",
        f"pub const OPTION_NONE_TAG: usize = {none};", "",
        f"pub const MACRO_CONTEXT_DEPTH_FIELD: usize = {values['depth']};",
        f"pub const MACRO_CONTEXT_MAX_DEPTH_FIELD: usize = {values['max_depth']};",
        f"pub const MACRO_CONTEXT_REF_FIELD: usize = {values['reference']};", "",
        f"pub const MACRO_EXPAND_MACRO_BORROWED: &[bool] = &[{borrowed}];",
        f"pub const MACRO_EXPAND_MACRO_PARAMETERS: &[&str] = &[{parameters}];",
        f"pub const MACRO_EXPAND_MACRO_RESULT: &str = {json.dumps(values['result'])};", "",
    ])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prelude-ir", required=True, type=pathlib.Path)
    parser.add_argument("--prelude-olean", required=True, type=pathlib.Path)
    parser.add_argument("--lean", help="Optionally cross-check with exact pinned Reference")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=pathlib.Path, default=OUTPUT)
    args = parser.parse_args()
    try:
        generated = generate(args)
        if args.check:
            if args.output.read_text() != generated:
                raise ValueError(f"macro expansion contract drift: {args.output}")
        else:
            args.output.write_text(generated)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
