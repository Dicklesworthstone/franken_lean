#!/usr/bin/env -S python3 -I -S
"""Extract the physical layout of the pinned IR declaration types (bead
`fln-ir-decoder-call-graph-sjzl`).

The pin stores a module's compiled code as `Lean.IR.Decl` values in the `.ir`
file beside its `.olean`. This renders the constructor tags and field slots of
`Decl` and everything it contains into `crates/fln-olean/src/ir_format.rs`, from
the vendored declarations. No Lean code executes, and nothing is copied by hand.

Layout rule (the pin's constructor object: a header, then object pointers in
declaration order, then scalar bytes in declaration order; all scalar fields
here are one byte). An inductive with at least one constructor that has a
relevant field represents its field-less constructors as boxed tags. A structure
with exactly one field is represented as that field itself.

Only the field types named in POINTER and SCALAR have a physical layout here; any
other type, any unlisted constructor shape, and any moved declaration is a typed
failure, never a guess.

    scripts/extract/gen_ir_contract.py            # write
    scripts/extract/gen_ir_contract.py --check    # fail if the file is stale
"""
import argparse
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
VENDOR = ROOT / "vendor/lean4-src"
OUTPUT = ROOT / "crates/fln-olean/src/ir_format.rs"

BASIC = "src/Lean/Compiler/IR/Basic.lean"
EXTERN = "src/Lean/Compiler/ExternAttr.lean"
COMPILER_M = "src/Lean/Compiler/IR/CompilerM.lean"
FILES = [BASIC, EXTERN, COMPILER_M]

# One-field structures the pin represents as the field itself, with that field's type.
TRANSPARENT = {
    "VarId": ("idx", "Index"),
    "JoinPointId": ("idx", "Index"),
    "DeclInfo": ("sorryDep?", "Option Name"),
    "ExternAttrData": ("entries", "List ExternEntry"),
}
# Field types stored as an object pointer (a boxed scalar counts as one).
POINTER = {
    "Nat", "Index", "Name", "FunId", "String", "VarId", "JoinPointId", "IRType", "Arg",
    "LitVal", "CtorInfo", "Expr", "FnBody", "Alt", "DeclInfo", "ExternAttrData",
    "Option Name", "Array IRType", "Array Arg", "Array Param", "Array Alt",
    "List ExternEntry",
}
# Field types stored as one scalar byte after the pointers.
SCALAR = {"Bool"}

# (file, declaration name, constant prefix, constructors in the pin's order)
INDUCTIVES = [
    (BASIC, "IRType", "IR_TYPE", ["float", "uint8", "uint16", "uint32", "uint64", "usize", "erased",
                                  "object", "tobject", "float32", "struct", "union", "tagged", "void"]),
    (BASIC, "Arg", "ARG", ["var", "erased"]),
    (BASIC, "LitVal", "LIT", ["num", "str"]),
    (BASIC, "Expr", "EXPR", ["ctor", "reset", "reuse", "proj", "uproj", "sproj", "fap", "pap", "ap",
                              "box", "unbox", "lit", "isShared"]),
    (BASIC, "Alt", "ALT", ["ctor", "default"]),
    (BASIC, "FnBody", "BODY", ["vdecl", "jdecl", "set", "setTag", "uset", "sset", "inc", "dec", "del",
                                "case", "ret", "jmp", "unreachable"]),
    (BASIC, "Decl", "DECL", ["fdecl", "extern"]),
    (EXTERN, "ExternEntry", "EXTERN_ENTRY", ["adhoc", "inline", "standard", "opaque"]),
]
STRUCTURES = [
    (BASIC, "CtorInfo", "CTOR_INFO"),
    (BASIC, "Param", "PARAM"),
]


def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean comment")
    return "".join(out)


def declaration(text, kind, name):
    found = re.search(r"^" + kind + r" " + re.escape(name) + r"\b[^\n]*\n", text, re.M)
    if found is None:
        raise ValueError(f"missing {kind} {name}")
    rest = text[found.end():]
    end = re.search(r"^(?:\S|\s*deriving\b)", rest, re.M)
    return rest[: end.start()] if end else rest


def screaming(name):
    return re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name).replace("?", "_OPTION").upper()


def binders(text):
    """`(a b : T) (c : U)` -> [(a, T), (b, T), (c, U)]; refuses anything left over."""
    fields, rest = [], text
    for group in re.finditer(r"\(([^():]+):([^()]+)\)", text):
        ty = " ".join(group.group(2).split())
        for field in group.group(1).split():
            fields.append((field, ty))
        rest = rest.replace(group.group(0), "", 1)
    return fields, rest.strip()


def constructors(body, name):
    """Constructors in order, each with its binder fields."""
    rows = []
    for chunk in re.split(r"(?m)^\s*\|", "\n" + body)[1:]:
        # one source line may hold several field-less constructors: `| float | uint8`
        for part in chunk.split("|"):
            part = " ".join(part.split())
            if not part:
                continue
            ctor = re.match(r"(\w+)\s*(.*)$", part)
            if ctor is None:
                raise ValueError(f"unreadable {name} constructor: {part!r}")
            fields, leftover = binders(ctor.group(2))
            leftover = re.sub(r"^:\s*" + re.escape(name) + r"$", "", leftover).strip()
            if leftover:
                raise ValueError(f"unsupported {name}.{ctor.group(1)} shape: {leftover!r}")
            rows.append((ctor.group(1), fields))
    return rows


def layout(owner, fields):
    """Pointer slots, then scalar bytes, each in declaration order."""
    pointers, scalars = [], []
    for field, ty in fields:
        if ty in POINTER:
            pointers.append(field)
        elif ty in SCALAR:
            scalars.append(field)
        else:
            raise ValueError(f"unsupported {owner} field {field} : {ty!r}")
    return pointers, scalars


def render():
    reference = [l for l in (ROOT / "SUITE.lock").read_text().splitlines() if l.startswith("reference ")]
    if len(reference) != 1:
        raise ValueError("expected one Reference pin")
    pin = dict(item.split("=", 1) for item in reference[0].split()[2:])
    sources = {path: (VENDOR / path).read_text(encoding="utf-8") for path in FILES}
    text = {path: strip_comments(value) for path, value in sources.items()}
    lines = ["//! Generated by scripts/extract/gen_ir_contract.py; do not edit.",
             f"//! Reference: {pin['tag']} @ {pin['commit']}."]
    for path in FILES:
        lines.append(f"//! {path}: sha256 {hashlib.sha256(sources[path].encode()).hexdigest()}")
    lines += ["#![allow(dead_code)]", ""]

    for name, (field, ty) in TRANSPARENT.items():
        path = EXTERN if name == "ExternAttrData" else BASIC
        body = declaration(text[path], "structure", name + " where")
        found = re.findall(r"^\s+([\w?]+)\s*:\s*(.+?)(?:\s*:=.*)?$", body, re.M)
        if found != [(field, ty)]:
            raise ValueError(f"{name} is no longer the one-field structure ({field} : {ty}): {found}")
    for alias, target in [("FunId", "Name"), ("Index", "Nat")]:
        if not re.search(r"^abbrev " + alias + r" := " + target + r"\s*$", text[BASIC], re.M):
            raise ValueError(f"abbreviation moved: {alias}")

    for path, name, prefix, expected in INDUCTIVES:
        rows = constructors(declaration(text[path], "inductive", name + " where"), name)
        if [ctor for ctor, _ in rows] != expected:
            raise ValueError(f"{name} constructor inventory drift: {[c for c, _ in rows]}")
        if not any(fields for _, fields in rows):
            raise ValueError(f"{name} has no constructor with fields; its layout rule differs")
        lines.append(f"// {name}: a constructor without fields is the boxed tag.")
        for tag, (ctor, fields) in enumerate(rows):
            stem = f"{prefix}_{screaming(ctor)}"
            lines.append(f"pub const {stem}: u8 = {tag};")
            pointers, scalars = layout(f"{name}.{ctor}", fields)
            if not fields:
                continue
            for slot, field in enumerate(pointers):
                lines.append(f"pub const {stem}_{screaming(field)}: usize = {slot};")
            for slot, field in enumerate(scalars):
                lines.append(f"pub const {stem}_{screaming(field)}_SCALAR: usize = {slot};")
            lines.append(f"pub const {stem}_POINTERS: usize = {len(pointers)};")
            lines.append(f"pub const {stem}_SCALAR_BYTES: usize = {len(scalars)};")
        lines.append(f"pub const {prefix}_CONSTRUCTORS: u8 = {len(rows)};")
        lines.append("")

    for path, name, prefix in STRUCTURES:
        body = declaration(text[path], "structure", name + " where")
        fields = [(f, " ".join(t.split())) for f, t in
                  re.findall(r"^\s+([\w?]+)\s*:\s*(.+?)(?:\s*:=.*)?$", body, re.M)]
        if len(fields) < 2:
            raise ValueError(f"{name} would be a one-field structure; its layout rule differs")
        pointers, scalars = layout(name, fields)
        for slot, field in enumerate(pointers):
            lines.append(f"pub const {prefix}_{screaming(field)}: usize = {slot};")
        for slot, field in enumerate(scalars):
            lines.append(f"pub const {prefix}_{screaming(field)}_SCALAR: usize = {slot};")
        lines += [f"pub const {prefix}_POINTERS: usize = {len(pointers)};",
                  f"pub const {prefix}_SCALAR_BYTES: usize = {len(scalars)};", ""]

    compiler = text[COMPILER_M]
    if not re.search(r"^namespace Lean\.IR\b", compiler, re.M):
        raise ValueError("namespace moved: Lean.IR")
    if not re.search(r"builtin_initialize declMapExt : SimplePersistentEnvExtension Decl DeclMap", compiler):
        raise ValueError("extension schema moved: declMapExt")
    if not re.search(r"#\[\(declMapExt\.name, irEntries\),", compiler):
        raise ValueError("the .ir export no longer leads with the declaration entries")
    lines.append('pub const DECL_MAP_EXTENSION: &str = "Lean.IR.declMapExt";')
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    rendered = render()
    if args.stdout:
        sys.stdout.write(rendered)
        return 0
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != rendered:
            print(f"{OUTPUT.relative_to(ROOT)} is stale; run scripts/extract/gen_ir_contract.py", file=sys.stderr)
            return 1
        return 0
    OUTPUT.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
