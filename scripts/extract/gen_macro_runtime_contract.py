#!/usr/bin/env -S python3 -I -S
"""Extract the macro runtime's constructor layouts from the exact pinned Lean.

The generated constants are consumed by the native VM methods and the Syntax
conversion boundary. This is an oracle-only build tool, never a product path.
"""

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "crates/fln-olean/fixtures/ir/MacroLayoutModule.lean"
OUTPUT = ROOT / "crates/fln-rt/src/syntax_abi_generated.rs"

CONSTRUCTORS = {
    "SOURCE_ORIGINAL": "Lean.SourceInfo.original",
    "SOURCE_SYNTHETIC": "Lean.SourceInfo.synthetic",
    "SYNTAX_NODE": "Lean.Syntax.node",
    "SYNTAX_ATOM": "Lean.Syntax.atom",
    "SYNTAX_IDENT": "Lean.Syntax.ident",
    "SUBSTRING_RAW": "Substring.Raw.mk",
    "PRERESOLVED_NAMESPACE": "Lean.Syntax.Preresolved.namespace",
    "PRERESOLVED_DECL": "Lean.Syntax.Preresolved.decl",
    "MACRO_CONTEXT": "Lean.Macro.Context.mk",
    "MACRO_STATE": "_private.Init.Prelude.0.Lean.Macro.State.mk",
    "RESULT_OK": "EStateM.Result.ok",
    "RESULT_ERROR": "EStateM.Result.error",
    "EXCEPTION_ERROR": "Lean.Macro.Exception.error",
    "LIST_CONS": "List.cons",
    "PROD": "Prod.mk",
}
SCALARS = {
    "SOURCE_NONE_TAG": "Lean.SourceInfo.none",
    "SYNTAX_MISSING_TAG": "Lean.Syntax.missing",
    "EXCEPTION_UNSUPPORTED_TAG": "Lean.Macro.Exception.unsupportedSyntax",
    "LIST_NIL_TAG": "List.nil",
}
FUNCTIONS = {
    "NAME_MK_STR1": "nameMkStr1",
    "NAME_STR": "nameStr",
    "ADD_MACRO_SCOPE": "addMacroScope",
    "MACRO_ADD_MACRO_SCOPE": "macroAddMacroScope",
    "SYNTAX_IS_OF_KIND": "syntaxIsOfKind",
    "SYNTAX_GET_ARG": "syntaxGetArg",
    "SYNTAX_GET_NUM_ARGS": "syntaxGetNumArgs",
    "SYNTAX_GET_KIND": "syntaxGetKind",
    "SYNTAX_SET_KIND": "syntaxSetKind",
    "SYNTAX_GET_ARGS": "syntaxGetArgs",
    "SYNTAX_SET_ARGS": "syntaxSetArgs",
    "SYNTAX_SET_ARG": "syntaxSetArg",
    "SYNTAX_IS_ATOM": "syntaxIsAtom",
    "SYNTAX_GET_ATOM_VAL": "syntaxGetAtomVal",
    "SYNTAX_SET_ATOM_VAL": "syntaxSetAtomVal",
    "SYNTAX_GET_HEAD_INFO": "syntaxGetHeadInfo",
    "SOURCE_INFO_GET_POS": "sourceInfoGetPos",
    "SOURCE_INFO_GET_TAIL_POS": "sourceInfoGetTailPos",
    "SYNTAX_GET_POS": "syntaxGetPos",
    "SYNTAX_GET_TAIL_POS": "syntaxGetTailPos",
    "SOURCE_INFO_FROM_REF": "sourceInfoFromRef",
    "MK_ATOM": "mkAtom",
    "MK_ATOM_FROM": "mkAtomFrom",
    "SYNTAX_SET_INFO": "syntaxSetInfo",
    "SYNTAX_IS_MISSING": "syntaxIsMissing",
    "SYNTAX_IS_IDENT": "syntaxIsIdent",
    "SYNTAX_GET_ID": "syntaxGetId",
    "MACRO_GET_CURR_NAMESPACE": "macroGetCurrNamespace",
    "MACRO_HAS_DECL": "macroHasDecl",
    "MACRO_RESOLVE_NAMESPACE": "macroResolveNamespace",
    "MACRO_RESOLVE_GLOBAL_NAME": "macroResolveGlobalName",
}


def generate(lean):
    lock = (ROOT / "SUITE.lock").read_text()
    epoch = re.search(r'(?m)^reference leanprover/lean4 .*\bcommit=([0-9a-f]{40})\b', lock)
    if epoch is None:
        raise ValueError("SUITE.lock has no Lean Reference commit")
    pin = epoch.group(1)
    actual = subprocess.run([lean, "--githash"], check=True, capture_output=True, text=True,
                            timeout=30)
    if actual.stdout.strip() != pin:
        raise ValueError(f"Reference commit mismatch: expected {pin}, got {actual.stdout.strip()}")
    compiled = subprocess.run([lean, "-j1", "--stdin"], input=FIXTURE.read_text(),
                              capture_output=True, text=True, timeout=120)
    if compiled.returncode:
        sys.stderr.write(compiled.stdout + compiled.stderr)
        raise ValueError("macro layout fixture did not compile")
    trace = compiled.stdout + compiled.stderr
    # The computed-field constructor is a compiler-emitted override. Bind its
    # native row to the actual forwarded callee, not merely a wrapper whose
    # source-level telescope happens to match.
    name_str = re.search(
        r"(?m)^    def FrankenLean\.MacroLayout\.nameStr \((x_\d+) : tobj\) "
        r"\((x_\d+) : obj\) : tobj :=\n(.*?)(?=^    def |^\[|\Z)", trace, re.S,
    )
    if name_str is None or re.fullmatch(
        rf"\s*let (x_\d+) : tobj := Lean\.Name\.str\._override "
        rf"{re.escape(name_str[1])} {re.escape(name_str[2])};\s*ret \1\s*",
        name_str[3],
    ) is None:
        raise ValueError("Name.str constructor wrapper does not forward the reviewed override")
    layouts = {}
    pattern = r"ctor_(\d+)(?:\.(\d+)\.(\d+))?\[([^\]]+)\]([^;\n]*);"
    for match in re.finditer(pattern, trace):
        tag, usize_fields, scalar_bytes, name, arguments = match.groups()
        if usize_fields not in (None, "0"):
            raise ValueError(f"unexpected usize fields in {name}")
        fields = re.findall(r"\bx_\d+\b|◾", arguments)
        layout = (int(tag), len(fields), int(scalar_bytes or 0))
        previous = layouts.setdefault(name, layout)
        if previous != layout:
            raise ValueError(f"inconsistent layout for {name}: {previous} vs {layout}")
    missing = set(CONSTRUCTORS.values()) - layouts.keys()
    if missing:
        raise ValueError(f"missing constructor layouts: {sorted(missing)}")
    scalars = {}
    for constant, name in SCALARS.items():
        tag, fields, scalar = layouts[name]
        if fields or scalar:
            raise ValueError(f"nullary constructor carries fields: {name}")
        scalars[constant] = tag
    lines = [
        "// Generated by scripts/extract/gen_macro_runtime_contract.py; do not edit.",
        f"// Reference commit: {pin}",
        f"// Fixture SHA-256: {hashlib.sha256(FIXTURE.read_bytes()).hexdigest()}",
        "//! Exact constructor layouts used by the native macro runtime.",
        "", "#[derive(Debug, Clone, Copy, PartialEq, Eq)]",
        "pub struct CtorLayout {", "    pub tag: u8,",
        "    pub object_fields: usize,", "    pub scalar_bytes: usize,", "}", "",
    ]
    for constant, name in CONSTRUCTORS.items():
        tag, fields, scalar = layouts[name]
        lines.extend([
            f"/// `{name}`.", f"pub const {constant}: CtorLayout = CtorLayout {{",
            f"    tag: {tag},", f"    object_fields: {fields},",
            f"    scalar_bytes: {scalar},", "};", "",
        ])
    for constant, tag in scalars.items():
        lines.append(f"pub const {constant}: usize = {tag};")
    # Derive positional fields from the pin's compiled pattern projections.
    # SourceInfo positions are erased Nat values, not host-width integers.
    for function, constant, constructor in [
        ("sourceOriginalPos", "SOURCE_ORIGINAL_POS_FIELD", "SOURCE_ORIGINAL"),
        ("sourceOriginalTailPos", "SOURCE_ORIGINAL_TAIL_POS_FIELD", "SOURCE_ORIGINAL"),
        ("sourceSyntheticPos", "SOURCE_SYNTHETIC_POS_FIELD", "SOURCE_SYNTHETIC"),
        ("sourceSyntheticTailPos", "SOURCE_SYNTHETIC_TAIL_POS_FIELD", "SOURCE_SYNTHETIC"),
    ]:
        getter = re.search(
            rf"(?m)^    def FrankenLean\.MacroLayout\.{function} \((x_\d+) : @& tobj\) : tobj :=\n"
            r"(.*?)(?=^    def |^\[|\Z)", trace, re.S,
        )
        if getter is None:
            raise ValueError(f"missing SourceInfo getter: {function}")
        projection = re.fullmatch(
            rf"\s*case {re.escape(getter[1])} : tobj of\s*"
            rf"{re.escape(CONSTRUCTORS[constructor])} →\s*"
            rf"let (x_\d+) : tobj := proj\[(\d+)\] {re.escape(getter[1])};\s*inc \1;\s*ret \1\s*"
            r"default →\s*let (x_\d+) : tagged := 0;\s*ret \3\s*", getter[2],
        )
        if projection is None:
            raise ValueError(f"SourceInfo getter is not the reviewed projection: {function}")
        field = int(projection[2])
        if field >= layouts[CONSTRUCTORS[constructor]][1]:
            raise ValueError(f"SourceInfo getter is outside the extracted layout: {function}")
        lines.extend(["", f"pub const {constant}: usize = {field};"])
    canonical = re.search(
        r"(?m)^    def FrankenLean\.MacroLayout\.sourceSyntheticCanonical \((x_\d+) : @& tobj\) : u8 :=\n"
        r"(.*?)(?=^    def |^\[|\Z)", trace, re.S,
    )
    if canonical is None:
        raise ValueError("missing SourceInfo canonical getter")
    projection = re.fullmatch(
        rf"\s*case {re.escape(canonical[1])} : tobj of\s*Lean\.SourceInfo\.synthetic →\s*"
        rf"let (x_\d+) : u8 := sproj\[(\d+), (\d+)\] {re.escape(canonical[1])};\s*ret \1\s*"
        r"default →\s*let (x_\d+) : u8 := 0;\s*ret \4\s*", canonical[2],
    )
    if projection is None:
        raise ValueError("SourceInfo canonical getter is not the reviewed scalar projection")
    objects, offset = int(projection[2]), int(projection[3])
    _, fields, scalar_bytes = layouts[CONSTRUCTORS["SOURCE_SYNTHETIC"]]
    if objects != fields or offset >= scalar_bytes:
        raise ValueError("SourceInfo canonical flag is outside the extracted layout")
    lines.extend([
        "", f"pub const SOURCE_SYNTHETIC_CANONICAL_OBJECT_FIELDS: usize = {objects};",
        f"pub const SOURCE_SYNTHETIC_CANONICAL_BYTE_OFFSET: usize = {offset};",
    ])
    # The confinement boundary must not hand-copy the opaque field's offset.
    # Require the exact getter emitted by the pin, not an arbitrary projection
    # elsewhere in the trace or a fallback to a remembered source field order.
    for function, constant, rust_type in [
        ("contextMethods", "MACRO_CONTEXT_METHODS_FIELD", "u64"),
        ("contextQuotation", "MACRO_CONTEXT_QUOTATION_FIELD", "usize"),
        ("contextScope", "MACRO_CONTEXT_SCOPE_FIELD", "usize"),
    ]:
        getter = re.search(
            rf"(?m)^    def FrankenLean\.MacroLayout\.{function} \((x_\d+) : @& obj\) : tobj :=\n"
            r"(.*?)(?=^    def |^\[|\Z)", trace, re.S,
        )
        if getter is None:
            raise ValueError(f"missing Macro.Context getter: {function}")
        projection = re.fullmatch(
            rf"\s*let (x_\d+) : tobj := proj\[(\d+)\] {re.escape(getter[1])};\s*inc \1;\s*ret \1\s*", getter[2],
        )
        if projection is None:
            raise ValueError(f"Macro.Context getter is not one object projection: {function}")
        field = int(projection[2])
        if field >= layouts[CONSTRUCTORS["MACRO_CONTEXT"]][1]:
            raise ValueError(f"Macro.Context getter is outside the extracted layout: {function}")
        lines.extend(["", f"pub const {constant}: {rust_type} = {field};"])
    for constant, function in FUNCTIONS.items():
        signature = re.search(
            rf"(?m)^    def FrankenLean\.MacroLayout\.{function} (.*?) : (\w+) :=$", trace,
        )
        if signature is None:
            raise ValueError(f"missing primitive signature: {function}")
        parameters, result = signature.groups()
        matches = re.findall(r"\(x_\d+ : (@& )?(\w+)\)", parameters)
        if not matches:
            raise ValueError(f"missing primitive parameters: {function}")
        borrowed = ", ".join("true" if borrow else "false" for borrow, _ in matches)
        types = ", ".join(f'"{type_}"' for _, type_ in matches)
        lines.extend([
            "", f"pub const {constant}_BORROWED: &[bool] = &[{borrowed}];",
            f"pub const {constant}_PARAMETERS: &[&str] = &[{types}];",
            f'pub const {constant}_RESULT: &str = "{result}";',
        ])
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, help="Exact pinned Reference executable")
    parser.add_argument("--check", action="store_true", help="Compare without writing")
    parser.add_argument("--output", type=pathlib.Path, default=OUTPUT)
    args = parser.parse_args()
    try:
        generated = generate(args.lean)
        if args.check:
            if args.output.read_text() != generated:
                raise ValueError(f"macro runtime contract drift: {args.output}")
        else:
            args.output.write_text(generated)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
