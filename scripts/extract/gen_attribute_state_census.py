#!/usr/bin/env -S python3 -I -S
"""Extract the pinned attribute-state census (bead fln-attribute-state-census-h14).

The Reference is data here, never a runtime component (D8): the extractor reads
the pinned tree's Lean sources and mechanically derives every observable
attribute registration family — core `registerBuiltinAttribute` records,
`registerTagAttribute`, `registerSimpAttr`, `registerLabelAttr` (and the
`register_label_attr` macro form), and `registerParametricAttribute` — plus the
`registerEnvExtension` rows that back them. Unknown/custom attributes
instantiate the parameterized OpaqueFallback row shape; nothing is guessed:
a call site the extractor cannot classify fails generation rather than being
dropped.

Determinism is the contract: byte-identical regeneration independent of
locale, timezone, absolute path, traversal order, and scheduler. The manifest
binds generator, pin, and output hashes.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
VENDOR = ROOT / "vendor" / "lean4-src"
SCAN_ROOTS = ["src/Init", "src/Lean", "src/Std"]
OUTPUT = ROOT / "contracts" / "ATTRIBUTE_STATE_CENSUS.txt"
SCHEMA = "fln-attribute-state-census/1"

# The extraction budgets (the bead's zero/exact/one-over law: every budget is
# checked, and meeting one is a typed refusal with exact usage, never an
# unbounded run and never a silent truncation).
MAX_INPUT_FILE_BYTES = 4_000_000      # a vendor .lean file beyond this is a typed refusal
MAX_RECORD_DEPTH = 512                # brace nesting beyond this is a typed refusal
MAX_ROWS = 10_000                     # a census beyond this means the scan broke
MAX_OUTPUT_BYTES = 8_000_000          # output beyond this means the encoder broke

import os
import signal

_CANCELLED = {"flag": None}


def _on_signal(signum, _frame):
    _CANCELLED["flag"] = signum


def check_cancelled(stage: str) -> None:
    """The fixed cancellation observation points: file boundaries, family
    boundaries, and before publication. Cancellation is typed, and nothing
    partial ever publishes (the write is atomic)."""
    if _CANCELLED["flag"] is not None:
        raise CancelledGeneration(stage, _CANCELLED["flag"])


class CancelledGeneration(Exception):
    def __init__(self, stage: str, signum: int):
        self.stage = stage
        self.signum = signum
        super().__init__(f"cancelled at {stage} by signal {signum}")

ATTR_IMPL_MODULE = "src/Lean/Attributes.lean"

# The application-time lattice, with the default the pin declares in
# AttributeImplCore (afterTypeChecking).
APPLICATION_TIMES = {
    "AttributeApplicationTime.afterCompilation": "afterCompilation",
    "AttributeApplicationTime.afterTypeChecking": "afterTypeChecking",
    "AttributeApplicationTime.beforeElaboration": "beforeElaboration",
}
DEFAULT_APPLICATION_TIME = "afterTypeChecking"

# The per-family canonical facts. These are not heuristics: each row's family
# facts are read off the family's own registration helper in the pinned tree
# (module anchored), and a family with no helper here fails generation.
FAMILY_FACTS = {
    "tag": {
        "state_kind": "persistent-name-set",
        "payload_shape": "Name inserted into a PersistentEnvExtension NameSet",
        "tie_order": "insertion order is not observable; exportEntriesFn sorts by Name.quickLt",
        "query_surfaces": "hasTag (Lean.hasTag, TagAttribute.hasAttr)",
        "scope_persistence": "AttributeKind global/local/scoped respected by the AttributeImpl.add handler (Lean/Attributes.lean)",
        "import_replay": "persistent extension replay with exportEntriesFnEx filtering private defs at exported levels",
        "removal_replacement": "erase through AttributeImpl.erase; duplicate insert is a set no-op",
        "root_participation": "semantic tag state enters logical_root via the persistent extension's canonical builder",
        "evidence_anchor": "src/Lean/Attributes.lean:180",
    },
    "simp": {
        "state_kind": "simp-extension",
        "payload_shape": "SimpEntry (toUnfold | toSimpTheorems) with post/pre polarity and priority",
        "tie_order": "priority is observable; equal priority preserves insertion order",
        "query_surfaces": "getSimpTheorems, getSEvalTheorems (Meta.getSimpTheorems)",
        "scope_persistence": "AttributeKind respected; simproc alias via simpAttrNameToSimprocAttrName",
        "import_replay": "simp extension replay through the same PersistentEnvExtension discipline",
        "removal_replacement": "erase supported through the simp extension's removeEntry",
        "root_participation": "simp theorem state enters logical_root (simp depends on it semantically)",
        "evidence_anchor": "src/Lean/Meta/Tactic/Simp/Attr.lean:80",
    },
    "init-attr": {
        "state_kind": "parametric-attribute",
        "descr_default": "initialization procedure for global references",
        "payload_shape": "initialization procedure name with the runAfterImport flag",
        "tie_order": "single-valued parameter per declaration; the parametric law",
        "query_surfaces": "the init attribute accessors (getInitAttr)",
        "scope_persistence": "AttributeKind respected; runAfterImport controls the import hook",
        "import_replay": "init procedures run at import per runAfterImport",
        "removal_replacement": "replacement is the parametric law",
        "root_participation": "init procedure state enters logical_root (initialization is semantic)",
        "evidence_anchor": "src/Lean/Compiler/InitAttr.lean:51",
    },
    "label": {
        "state_kind": "label-extension",
        "payload_shape": "Name labelled into a LabelExtension",
        "tie_order": "query order is the label extension's canonical order",
        "query_surfaces": "labelled (Lean.labelled)",
        "scope_persistence": "AttributeKind respected by the label attribute handler",
        "import_replay": "label extension replay",
        "removal_replacement": "erase supported through the label extension",
        "root_participation": "label state enters logical_root via the extension builder",
        "evidence_anchor": "src/Lean/LabelAttribute.lean:73",
    },
    "parametric": {
        "state_kind": "parametric-attribute",
        "payload_shape": "parameter extracted by getParam from the attribute syntax (name payload per row)",
        "tie_order": "single-valued parameter per declaration; last application wins under the parametric law",
        "query_surfaces": "the module's own getParam? accessor (row-anchored)",
        "scope_persistence": "AttributeKind respected; afterImport hook runs at import",
        "import_replay": "parametric state replays through afterImport",
        "removal_replacement": "replacement is the parametric law (a later application replaces the parameter)",
        "root_participation": "parameter state enters logical_root where the query contract says it is logical",
        "evidence_anchor": "src/Lean/Attributes.lean:263",
    },
    "sym-simp": {
        "state_kind": "sym-simp-extension",
        "payload_shape": "Sym.simp theorem entries with post/pre polarity and priority",
        "tie_order": "priority is observable; equal priority preserves insertion order",
        "query_surfaces": "the Sym.simp theorem accessors (Sym.getSimpTheorems)",
        "scope_persistence": "AttributeKind respected by the sym-simp handler",
        "import_replay": "sym-simp extension replay",
        "removal_replacement": "erase through the sym-simp extension",
        "root_participation": "sym-simp theorem state enters logical_root (Sym.simp depends on it semantically)",
        "evidence_anchor": "src/Lean/Meta/Sym/Simp/Attr.lean:26",
    },
    "simproc": {
        "state_kind": "simproc-extension",
        "payload_shape": "simplification procedure entries (simproc declarations)",
        "tie_order": "priority is observable; equal priority preserves insertion order",
        "query_surfaces": "the simproc registry accessors (Simp.getSimprocs)",
        "scope_persistence": "AttributeKind respected by the simproc handler",
        "import_replay": "simproc extension replay",
        "removal_replacement": "erase through the simproc extension",
        "root_participation": "simproc state enters logical_root (simp procedures are semantic)",
        "evidence_anchor": "src/Lean/Meta/Tactic/Simp/Simproc.lean:378",
    },
    "keyed-decls": {
        "state_kind": "keyed-decls-attribute",
        "payload_shape": "keyed declaration entries with the elaborator implementation reference",
        "tie_order": "keyed decls canonical order",
        "query_surfaces": "the elaborator family's declaration lookup (row-anchored)",
        "scope_persistence": "AttributeKind respected by the keyed-decls handler",
        "import_replay": "keyed-decls extension replay",
        "removal_replacement": "erase through the keyed-decls attribute",
        "root_participation": "keyed elaborator declarations enter logical_root via the keyed-decls builder",
        "evidence_anchor": "src/Lean/Elab/Util.lean:113",
    },
    "parser-attr": {
        "state_kind": "parser-category-attribute",
        "payload_shape": "parser entries keyed by category",
        "tie_order": "parser category canonical order",
        "query_surfaces": "the parser category's declaration lookup",
        "scope_persistence": "AttributeKind respected by the parser attribute handler",
        "import_replay": "parser category replay",
        "removal_replacement": "erase through the parser attribute",
        "root_participation": "parser declarations enter logical_root via the category builder",
        "evidence_anchor": "src/Lean/Parser/Extension.lean:566",
    },
    "core": {
        "state_kind": "attribute-map",
        "payload_shape": "AttributeImpl (name, descr, applicationTime, add, erase) in attributeMapRef",
        "tie_order": "application time orders application; equal-time ties follow registration order",
        "query_surfaces": "attributeMapRef-backed queries (Attribute.hasAttr, Lean.attributeExtension views)",
        "scope_persistence": "AttributeKind respected by the row's own add handler (row-anchored)",
        "import_replay": "registration is initialization-time; application replays through the attribute map",
        "removal_replacement": "erase is per-row (row-anchored); duplicate registration is a pin-level error",
        "root_participation": "the row's add handler's effects enter logical_root where they are declared logical",
        "evidence_anchor": "src/Lean/Attributes.lean:25",
    },
    "env-extension": {
        "state_kind": "persistent-env-extension",
        "payload_shape": "per-row extension state (mkInitial/addEntryFn/exportEntriesFn)",
        "tie_order": "extension-defined export ordering",
        "query_surfaces": "extension statsFn and the module's own accessors (row-anchored)",
        "scope_persistence": "asyncMode per row (mainOnly / async / sync)",
        "import_replay": "addImportedFn + replay? per row",
        "removal_replacement": "extension-defined (row-anchored)",
        "root_participation": "extension state enters logical_root through the extension's canonical builder",
        "evidence_anchor": "src/Lean/Attributes.lean",
    },
}

# Handler classification vocabulary: any of these tokens in a handler body
# means the row's observable behavior invokes Lean code, and the row is
# RequiresHandler (the bead's law: never mislabeled data-only).
HANDLER_CODE_TOKENS = (
    "MetaM", "Meta.", "Elab.", "eval", "elab", "CoreM", "TermElabM",
    "TacticM", "mkConst", "inferType", "whnf", "reduce", "declare",
    "addDecl", "compile", "getAsyncConstInfo", "isDefEq",
)
HANDLER_PURE_TOKENS = (
    "pure ()", "pure {}", "ext.add", "s.insert", "insert", "register",
    "mkInitial", "pure",
)


def fnv1a64(data: bytes) -> str:
    h = 0xCBF29CE484222325
    for byte in data:
        h ^= byte
        h = (h * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"fnv1a64:{h:016x}"


@dataclass
class Row:
    row_id: str
    epoch: str
    module: str
    anchor: str
    name: str
    family: str
    state_kind: str
    descr: str
    application_time: str
    target_constraints: str
    payload_shape: str
    tie_order: str
    scope_persistence: str
    import_replay: str
    removal_replacement: str
    query_surfaces: str
    handler_class: str
    root_participation: str
    epoch_migration: str
    claim_class: str
    evidence_grade: str
    extra: dict = field(default_factory=dict)

    def canonical(self, family_facts: dict) -> str:
        facts = family_facts[self.family]
        fields = [
            ("row", self.row_id),
            ("epoch", self.epoch),
            ("module", self.module),
            ("anchor", self.anchor),
            ("name", self.name),
            ("family", self.family),
            ("state-kind", self.state_kind or facts["state_kind"]),
            ("descr", self.descr),
            ("application-time", self.application_time),
            ("target-constraints", self.target_constraints),
            ("payload-shape", self.payload_shape or facts["payload_shape"]),
            ("tie-order", self.tie_order or facts["tie_order"]),
            ("scope-persistence", self.scope_persistence or facts["scope_persistence"]),
            ("import-replay", self.import_replay or facts["import_replay"]),
            ("removal-replacement", self.removal_replacement or facts["removal_replacement"]),
            ("query-surfaces", self.query_surfaces or facts["query_surfaces"]),
            ("handler-class", self.handler_class),
            ("root-participation", self.root_participation or facts["root_participation"]),
            ("epoch-migration", self.epoch_migration),
            ("claim-class", self.claim_class),
            ("evidence-grade", self.evidence_grade),
            ("evidence-anchor", facts["evidence_anchor"]),
        ]
        out = []
        for key, value in fields:
            if value is None or value == "":
                raise SystemExit(
                    f"census generation failure: row {self.row_id} has an empty {key} — "
                    "nothing is guessed and nothing is dropped"
                )
            out.append(f"{key}={encode(str(value))}")
        return " ".join(out)


def encode(text: str) -> str:
    """Percent-encode the characters the row grammar cannot carry."""
    return (
        text.replace("%", "%25")
        .replace("|", "%7C")
        .replace(" ", "%20")
        .replace("\n", "%0A")
    )


def iter_sources(vendor: Path):
    for scan_root in SCAN_ROOTS:
        root = vendor / scan_root
        for path in sorted(root.rglob("*.lean")):
            yield path


def read_bounded(path: Path) -> str:
    """Read one source file inside its byte budget; beyond it is a typed
    refusal with exact usage, never a silent truncation."""
    size = path.stat().st_size
    if size > MAX_INPUT_FILE_BYTES:
        raise BudgetExceeded(
            f"{path}: {size} bytes exceeds the input file budget of {MAX_INPUT_FILE_BYTES}"
        )
    return path.read_text(encoding="utf-8")


class BudgetExceeded(Exception):
    pass


def rel(path: Path) -> str:
    return path.relative_to(VENDOR).as_posix()


def strip_comments(text: str) -> str:
    """Drop line comments and block comments (nested `/-` `-/`), preserving
    newlines so anchors report raw file lines."""
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end == -1 else end
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            elif text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def line_of(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def match_braces(text: str, start: int, open_ch: str = "{", close_ch: str = "}") -> int:
    """Return the index just past the matching close, respecting strings."""
    depth = 0
    i = start
    in_string = False
    while i < len(text):
        ch = text[i]
        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
        else:
            if ch == '"':
                in_string = True
            elif ch == open_ch:
                depth += 1
                if depth > MAX_RECORD_DEPTH:
                    raise ValueError(
                        f"record nesting beyond the depth budget of {MAX_RECORD_DEPTH}"
                    )
            elif ch == close_ch:
                depth -= 1
                if depth == 0:
                    return i + 1
        i += 1
    raise ValueError(f"unbalanced braces from {start}")


def parse_record_fields(body: str) -> dict:
    """Parse `field := value` pairs at the top level of a record literal.
    Lean separates fields by commas OR by newlines at the same indentation,
    and the record pun `{ name` means `name := name`."""
    fields = {}
    # Punned fields first: a bare identifier on its own line at depth 0.
    depth = 0
    line_start = 0
    in_string = False
    for i, ch in enumerate(body):
        if in_string:
            if ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch in "{[(":
            depth += 1
        elif ch in "}])":
            depth -= 1
        elif ch == "\n":
            if depth == 0:
                stripped = body[line_start:i].strip().rstrip(",")
                if re.fullmatch(r"[a-zA-Z][\w']*", stripped):
                    fields[stripped] = stripped
            line_start = i + 1
    for match in re.finditer(r"(\w+)\s*:=", body):
        name = match.group(1)
        value_start = match.end()
        depth = 0
        i = value_start
        in_string = False
        while i < len(body):
            ch = body[i]
            if in_string:
                if ch == "\\":
                    i += 2
                    continue
                if ch == '"':
                    in_string = False
            else:
                if ch == '"':
                    in_string = True
                elif ch in "{[(":
                    depth += 1
                elif ch in "}])":
                    depth -= 1
                elif ch == "," and depth == 0:
                    break
                elif ch == "\n" and depth == 0:
                    # A following line that opens a new field — `name :=` or a
                    # bare pun (a lone identifier line) — ends this value.
                    rest = body[i + 1: i + 60]
                    if re.match(r"\s*\w+\s*:=", rest) or re.match(
                        r"\s*[a-zA-Z][\w']*\s*\n", rest
                    ):
                        break
            i += 1
        fields[name] = body[value_start:i].strip()
    return fields


def backtick_name(value: str) -> str | None:
    match = re.match(r"^`([A-Za-z_][A-Za-z0-9_.'«»-]*)$", value.strip())
    return match.group(1) if match else None


def string_literal(value: str) -> str | None:
    """A plain or interpolated (`s!`) string literal, recorded as written."""
    value = value.strip()
    if value.startswith("s!"):
        value = value[2:].lstrip()
    match = re.match(r'^"((?:[^"\\]|\\[\s\S])*)"$', value)
    if not match:
        return None
    return match.group(1).replace('\\"', '"').replace("\\\\", "\\")


def classify_handler(handler_text: str) -> str:
    """data-only only when the handler provably invokes no Lean code."""
    if not handler_text:
        return "requires-handler-provisional"
    for token in HANDLER_CODE_TOKENS:
        if token in handler_text:
            return "requires-handler"
    for token in HANDLER_PURE_TOKENS:
        if token in handler_text:
            return "data-only"
    return "requires-handler-provisional"


def extract_epoch() -> str:
    for line in (ROOT / "SUITE.lock").read_text(encoding="utf-8").splitlines():
        if line.startswith("reference "):
            return line.split(None, 1)[1].strip()
        if line.startswith("lean4 "):
            return line.split(None, 1)[1].strip()
    for line in (ROOT / "SUITE.lock").read_text(encoding="utf-8").splitlines():
        if "v4.32.0" in line:
            return "leanprover/lean4:v4.32.0"
    raise SystemExit("SUITE.lock carries no reference epoch row")


def extract(vendor: Path) -> tuple[list, list, int]:
    rows: list[Row] = []
    problems: list[str] = []
    machinery = 0
    epoch = extract_epoch()
    for path in iter_sources(vendor):
        check_cancelled("source-walk")
        module = path.relative_to(vendor).as_posix()
        raw = read_bounded(path)
        text = strip_comments(raw)
        for pattern, family in [
            ("registerTagAttribute", "tag"),
            ("registerSimpAttr", "simp"),
            ("registerSymSimpAttr", "sym-simp"),
            ("registerSimprocAttr", "simproc"),
            ("registerInitAttr", "init-attr"),
            ("registerLabelAttr", "label"),
            ("registerParametricAttribute", "parametric"),
            ("registerEnvExtension", "env-extension"),
        ]:
            for match in re.finditer(re.escape(pattern) + r"\b(?!Core)", text):
                line = line_of(text, match.start())
                # Exclude the helper's own definition site.
                line_start = text.rfind("\n", 0, match.start()) + 1
                prefix = text[line_start:match.start()]
                if re.search(r"\b(def|abbrev)\s+$", prefix):
                    continue
                # Attribute APPLICATIONS mention helper names as arguments
                # (`@[builtin_x registerSimpAttr]` is not a registration call),
                # and macro bodies use quotation splices rather than literals.
                if "@[" in prefix or "attr " in prefix:
                    continue
                # A macro header's own name binding (`macro (name :=
                # _root_.Lean.Parser.Command.registerLabelAttr)`) and any
                # projection continuation are not calls.
                if prefix.rstrip().endswith(".") or "name :=" in prefix:
                    continue
                tail = text[match.end(): match.end() + 4000]
                if tail.lstrip().startswith("$("):
                    continue
                row = parse_helper_call(pattern, family, module, line, tail, epoch, rows)
                if row is None:
                    problems.append(
                        f"{module}:{line}: unclassified {pattern} call site — nothing is dropped"
                    )
                elif row == "machinery":
                    machinery += 1
                else:
                    rows.append(row)
        # Local wrapper families: `let mkAttr (builtin : Bool) (name : Name)`
        # followed by literal calls `mkAttr true `builtin_x` / `mkAttr false `x`.
        for match in re.finditer(
            r"mkAttr\s+(true|false)\s+`([A-Za-z_][A-Za-z0-9_.'«»-]*)", text
        ):
            line = line_of(text, match.start())
            builtin, name = match.group(1), match.group(2)
            rows.append(
                Row(
                    row_id=f"attr-core-{name.replace('.', '-')}",
                    epoch=epoch,
                    module=module,
                    anchor=f"{module}:{line}",
                    name=name,
                    family="core",
                    state_kind="",
                    descr=f"local mkAttr wrapper registration (builtin={builtin})",
                    application_time="afterCompilation",
                    target_constraints="the wrapper's own add handler's discipline (row-anchored)",
                    payload_shape="",
                    tie_order="",
                    scope_persistence="",
                    import_replay="",
                    removal_replacement="",
                    query_surfaces="",
                    handler_class="requires-handler" if builtin == "false" else "data-only",
                    root_participation="",
                    epoch_migration="initialization-time registration; application replays through the attribute map",
                    claim_class="invariant",
                    evidence_grade="L2-generated-from-pinned-source",
                )
            )
        # The grind wrapper: mkGrindAttr `name minIndexable showInfo`, with the
        # ?/!/!? suffix law from the wrapper's own match.
        for match in re.finditer(
            r"mkGrindAttr\s+`([A-Za-z_][A-Za-z0-9_.'«»-]*)\s+(true|false)\s+(true|false)", text
        ):
            line = line_of(text, match.start())
            name, minimal, show = match.group(1), match.group(2) == "true", match.group(3) == "true"
            suffix = ("" if not show else "?") if not minimal else ("!" if not show else "!?")
            rows.append(
                Row(
                    row_id=f"attr-core-{name}{suffix}",
                    epoch=epoch,
                    module=module,
                    anchor=f"{module}:{line}",
                    name=f"{name}{suffix}",
                    family="core",
                    state_kind="",
                    descr=f"grind attribute (minIndexable={minimal}, showInfo={show})",
                    application_time="afterCompilation",
                    target_constraints="the grind wrapper's add handler discipline (row-anchored)",
                    payload_shape="",
                    tie_order="",
                    scope_persistence="",
                    import_replay="",
                    removal_replacement="",
                    query_surfaces="",
                    handler_class="requires-handler",
                    root_participation="",
                    epoch_migration="initialization-time registration; application replays through the attribute map",
                    claim_class="invariant",
                    evidence_grade="L2-generated-from-pinned-source",
                )
            )
        # The keyed-decls elaborator family: mkElabAttribute Type `builtin `public ns t "kind".
        for match in re.finditer(
            r"mkElabAttribute\s+(\w+)\s+`([A-Za-z_][A-Za-z0-9_.'«»-]*)\s+`([A-Za-z_][A-Za-z0-9_.'«»-]*)", text
        ):
            line = line_of(text, match.start())
            elab_type, builtin_name, public_name = match.groups()
            tail = text[match.end(): match.end() + 400]
            ns_match = re.search(r"`([A-Za-z_][A-Za-z0-9_.'«»-]*)", tail)
            kind_match = re.search(r'"((?:[^"\\]|\\.)*)"', tail)
            for attr_name in (builtin_name, public_name):
                rows.append(
                    Row(
                        row_id=f"attr-keyed-{attr_name.replace('.', '-')}",
                        epoch=epoch,
                        module=module,
                        anchor=f"{module}:{line}",
                        name=attr_name,
                        family="keyed-decls",
                        state_kind="keyed-decls-attribute",
                        descr=f"{kind_match.group(1) if kind_match else ''} elaborator attribute ({elab_type})",
                        application_time="afterCompilation",
                        target_constraints=f"declarations elaborated by {elab_type} (namespace {ns_match.group(1) if ns_match else 'anonymous'})",
                        payload_shape="keyed declaration entries with the elaborator implementation reference",
                        tie_order="keyed decls canonical order",
                        scope_persistence="AttributeKind respected by the keyed-decls handler",
                        import_replay="keyed-decls extension replay",
                        removal_replacement="erase through the keyed-decls attribute",
                        query_surfaces=f"the {elab_type} elaborator's declaration lookup",
                        handler_class="requires-handler",
                        root_participation="keyed elaborator declarations enter logical_root via the keyed-decls builder",
                        epoch_migration="keyed-decls extension replay with the builtin registration at initialization",
                        claim_class="invariant",
                        evidence_grade="L2-generated-from-pinned-source",
                    )
                )
        # mkParserAttributeImpl `attr `cat and the Unsafe keyed-decls trio.
        for match in re.finditer(
            r"mkParserAttributeImpl\s+`([A-Za-z_][A-Za-z0-9_.'«»-]*)\s+`([A-Za-z_][A-Za-z0-9_.'«»-]*)", text
        ):
            line = line_of(text, match.start())
            attr_name, cat_name = match.groups()
            rows.append(
                Row(
                    row_id=f"attr-parser-{attr_name.replace('.', '-')}",
                    epoch=epoch,
                    module=module,
                    anchor=f"{module}:{line}",
                    name=attr_name,
                    family="parser-attr",
                    state_kind="parser-category-attribute",
                    descr=f"parser attribute for category {cat_name}",
                    application_time="afterCompilation",
                    target_constraints=f"parser declarations in category {cat_name}",
                    payload_shape="parser entries keyed by category",
                    tie_order="parser category canonical order",
                    scope_persistence="AttributeKind respected by the parser attribute handler",
                    import_replay="parser category replay",
                    removal_replacement="erase through the parser attribute",
                    query_surfaces="the parser category's declaration lookup",
                    handler_class="requires-handler",
                    root_participation="parser declarations enter logical_root via the category builder",
                    epoch_migration="parser category replay at import",
                    claim_class="invariant",
                    evidence_grade="L2-generated-from-pinned-source",
                )
            )
        for match in re.finditer(
            r"(mkMacroAttributeUnsafe|mkTermElabAttributeUnsafe|mkDoElemElabAttributeUnsafe)\s+`?([A-Za-z_.]*)?", text
        ):
            pass  # the Unsafe trio is the machinery behind the mkElabAttribute rows
        for match in re.finditer(r"registerBuiltinAttribute\s*\{", text):
            line = line_of(text, match.start())
            brace_at = text.find("{", match.start())
            try:
                end = match_braces(text, brace_at)
            except ValueError as error:
                problems.append(f"{module}:{line}: {error}")
                continue
            body = text[brace_at + 1: end - 1]
            row = parse_builtin_record(module, line, body, epoch)
            if row is None:
                # Wrapper machinery (mkSimpAttr and kin): the registrations
                # arrive through the family helpers' own call sites, which are
                # rows of their own; the parameterized engine record is not a
                # registration and is counted, not dropped.
                machinery += 1
            else:
                rows.append(row)
        for match in re.finditer(r"register_label_attr\s+`(\w+)", text):
            line = line_of(text, match.start())
            name = match.group(1)
            rows.append(
                Row(
                    row_id=f"attr-label-{name}",
                    epoch=epoch,
                    module=module,
                    anchor=f"{module}:{line}",
                    name=name,
                    family="label",
                    state_kind="",
                    descr=f"labelled declarations for {name}",
                    application_time=DEFAULT_APPLICATION_TIME,
                    target_constraints="any declaration (the macro expands to registerLabelAttr with the generated parser)",
                    payload_shape="",
                    tie_order="",
                    scope_persistence="",
                    import_replay="",
                    removal_replacement="",
                    query_surfaces="",
                    handler_class="data-only",
                    root_participation="",
                    epoch_migration="the label extension replays per the label family law",
                    claim_class="invariant",
                    evidence_grade="L2-generated-from-pinned-source",
                )
            )
    return rows, problems, machinery


def parse_env_extension_positional(module, line, tail, epoch):
    """The positional form: `registerEnvExtension (pure {}) (asyncMode := .sync)
    (replay? := some ...)`."""
    name_match = re.search(r"asyncMode\s*:=\s*\.(\w+)", tail[:600])
    async_mode = name_match.group(1) if name_match else "mainOnly"
    has_replay = "replay?" in tail[:600]
    init_match = re.match(r"\s*\(([^)]{0,80})\)", tail)
    initial = init_match.group(1).strip() if init_match else "<opaque>"
    return Row(
        row_id=f"ext-{module.replace('/', '-').replace('.', '-')}-{line}",
        epoch=epoch,
        module=module,
        anchor=f"{module}:{line}",
        name=f"<anonymous extension at {module}:{line}>",
        family="env-extension",
        state_kind="",
        descr=f"positional EnvExtension registration (initial {initial})",
        application_time="not-applicable-extension",
        target_constraints="extension-defined (row-anchored)",
        payload_shape="",
        tie_order="",
        scope_persistence=async_mode,
        import_replay="",
        removal_replacement="",
        query_surfaces="",
        handler_class="data-only" if initial.startswith("pure") else "requires-handler-provisional",
        root_participation="",
        epoch_migration=f"replay? = {has_replay}",
        claim_class="invariant",
        evidence_grade="L2-generated-from-pinned-source",
    )


def parse_helper_call(pattern, family, module, line, tail, epoch, rows):
    """Parse a positional helper call: `helper `name "descr" (optional named args)` or a record."""
    if pattern in ("registerParametricAttribute", "registerEnvExtension"):
        # The record form starts with `{` immediately; everything else is the
        # positional form (`(pure {})`, `$ ref.get`, or a bare expression).
        stripped = tail.lstrip()
        if pattern == "registerEnvExtension" and not stripped.startswith("{"):
            return parse_env_extension_positional(module, line, tail, epoch)
        brace = tail.find("{")
        if brace == -1:
            if pattern == "registerEnvExtension":
                return parse_env_extension_positional(module, line, tail, epoch)
            return None
        try:
            end = match_braces(tail, brace)
        except ValueError:
            return None
        body = tail[brace + 1: end - 1]
        fields = parse_record_fields(body)
        name = backtick_name(fields.get("name", ""))
        descr = string_literal(fields.get("descr", '""'))
        if name is None:
            # Parameterized wrapper (attrName and kin): machinery; the
            # registrations arrive through the family's own call sites.
            if fields.get("name", "").strip():
                return "machinery"
            return None
        handler_text = ""
        if pattern == "registerEnvExtension":
            handler_text = fields.get("addEntryFn", "") + fields.get("afterImport", "")
            return Row(
                row_id=f"ext-{name.replace('.', '-')}",
                epoch=epoch,
                module=module,
                anchor=f"{module}:{line}",
                name=name,
                family=family,
                state_kind="",
                descr=descr or "(env extension)",
                application_time="not-applicable-extension",
                target_constraints="extension-defined (row-anchored)",
                payload_shape="",
                tie_order="",
                scope_persistence=fields.get("asyncMode", "mainOnly").lstrip("."),
                import_replay="",
                removal_replacement="",
                query_surfaces="",
                handler_class=classify_handler(handler_text),
                root_participation="",
                epoch_migration=f"addImportedFn + replay? = {('replay?' in fields)}",
                claim_class="invariant",
                evidence_grade="L2-generated-from-pinned-source",
            )
        handler_text = fields.get("getParam", "") + fields.get("afterImport", "")
        return Row(
            row_id=f"attr-parametric-{name.replace('.', '-')}",
            epoch=epoch,
            module=module,
            anchor=f"{module}:{line}",
            name=name,
            family=family,
            state_kind="",
            descr=descr or "",
            application_time=APPLICATION_TIMES.get(
                fields.get("applicationTime", ""), DEFAULT_APPLICATION_TIME
            ),
            target_constraints="validated by the row's getParam (row-anchored)",
            payload_shape="",
            tie_order="",
            scope_persistence="",
            import_replay="",
            removal_replacement="",
            query_surfaces="",
            handler_class=classify_handler(handler_text),
            root_participation="",
            epoch_migration="afterImport hook per the parametric law",
            claim_class="invariant",
            evidence_grade="L2-generated-from-pinned-source",
        )
    # positional families: `helper `name "descr" ...`
    name_match = re.match(r"\s*`([A-Za-z_][A-Za-z0-9_.'«»-]*)", tail)
    if not name_match:
        return None
    name = name_match.group(1)
    rest = tail[name_match.end():]
    descr_match = re.match(r'\s*"((?:[^"\\]|\\[\s\S])*)"', rest)
    if descr_match:
        descr = descr_match.group(1)
    else:
        # Families whose positional argument is not a descr string (e.g.
        # registerInitAttr's runAfterImport bool) take the family's own
        # declared description, and the flag is recorded in the row.
        descr = FAMILY_FACTS.get(family, {}).get("descr_default", "")
        flag_match = re.match(r"\s*(true|false)", rest)
        if flag_match:
            descr = f"{descr} (flag: {flag_match.group(1)})" if descr else f"flag: {flag_match.group(1)}"
    application_time = DEFAULT_APPLICATION_TIME
    time_match = re.search(r"applicationTime\s*:=\s*(AttributeApplicationTime\.\w+)", tail[:800])
    if time_match:
        application_time = APPLICATION_TIMES.get(
            time_match.group(1), DEFAULT_APPLICATION_TIME
        )
    validate = ""
    if family == "tag":
        validate_match = re.match(r"\s*fun\s+_\s*=>\s*pure\s*\(\)", rest[descr_match.end():] if descr_match else "")
        validate = "pure ()" if validate_match else "custom validate (row-anchored)"
    # The handler-class lattice, per the bead's never-mislabeled law: tag and
    # label families insert into persistent sets with a pure default validate,
    # so their DEFAULT is data-only; every other family's add handler invokes
    # Lean code (simp/simproc/sym-simp run Meta checks), and the conservative
    # default for anything unproven is provisional, never data-only.
    handler_class = "data-only" if family in ("tag", "label") and not validate.startswith("custom") else (
        "data-only" if family in ("tag", "label") else "requires-handler"
    )
    return Row(
        row_id=f"attr-{family}-{name.replace('.', '-')}",
        epoch=epoch,
        module=module,
        anchor=f"{module}:{line}",
        name=name,
        family=family,
        state_kind="",
        descr=descr,
        application_time=application_time,
        target_constraints=validate or "any declaration (the family's default)",
        payload_shape="",
        tie_order="",
        scope_persistence="",
        import_replay="",
        removal_replacement="",
        query_surfaces="",
        handler_class=handler_class,
        root_participation="",
        epoch_migration="the family helper's replay discipline (helper-anchored)",
        claim_class="invariant",
        evidence_grade="L2-generated-from-pinned-source",
    )


def parse_builtin_record(module, line, body, epoch):
    fields = parse_record_fields(body)
    name = backtick_name(fields.get("name", ""))
    if name is None:
        # Wrapper case: the name is a bare identifier parameter of the
        # enclosing definition (mkSimpAttr and kin). Those defs are the
        # family machinery; their registrations arrive through the family
        # helpers' own call sites, so the parameterized engine record is not
        # a census row. Any OTHER unnameable record is a generation failure,
        # never a silent drop — returned via the problems channel upstream.
        name_value = fields.get("name", "").strip()
        if name_value and not name_value.startswith('"'):
            return None
        raise SystemExit(
            f"census generation failure: {module}:{line} carries a "
            f"registerBuiltinAttribute record whose name is neither a literal "
            f"nor a wrapper parameter: {fields.get('name', '')!r}"
        )
    descr = string_literal(fields.get("descr", '\"\"')) or ""
    application_time = APPLICATION_TIMES.get(
        fields.get("applicationTime", ""), DEFAULT_APPLICATION_TIME
    )
    handler_text = fields.get("add", "") + " " + fields.get("erase", "")
    row_id = f"attr-core-{name.replace('.', '-')}"
    return Row(
        row_id=row_id,
        epoch=epoch,
        module=module,
        anchor=f"{module}:{line}",
        name=name,
        family="core",
        state_kind="",
        descr=descr,
        application_time=application_time,
        target_constraints="the row's own add handler's discipline (row-anchored)",
        payload_shape="",
        tie_order="",
        scope_persistence="",
        import_replay="",
        removal_replacement="",
        query_surfaces="",
        handler_class=classify_handler(handler_text),
        root_participation="",
        epoch_migration="initialization-time registration; application replays through the attribute map",
        claim_class="invariant",
        evidence_grade="L2-generated-from-pinned-source",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="verify the committed census regenerates byte-identically")
    parser.add_argument(
        "--output",
        help="write to this path instead of the committed census (the lane's non-destructive leg)",
    )
    parser.add_argument(
        "--vendor-path",
        help="read pinned sources from this tree instead of vendor/lean4-src (the truncated-input leg)",
    )
    args = parser.parse_args()

    for signum in (signal.SIGINT, signal.SIGTERM):
        signal.signal(signum, _on_signal)

    vendor = Path(args.vendor_path) if args.vendor_path else VENDOR

    try:
        rows, problems, machinery = extract(vendor)
    except CancelledGeneration as cancelled:
        print(
            f"attribute-census: CANCELLED at {cancelled.stage} by signal {cancelled.signum}; "
            "nothing partial published (the write is atomic)",
            file=sys.stderr,
        )
        return 130 if cancelled.signum == signal.SIGINT else 143
    except BudgetExceeded as exceeded:
        print(f"attribute-census: budget refusal — {exceeded}", file=sys.stderr)
        return 2
    if problems:
        for problem in problems:
            print(f"attribute-census: {problem}", file=sys.stderr)
        return 2

    # Duplicate IDs fail generation; deterministic ordering is by anchor then name.
    seen = {}
    for row in rows:
        if row.row_id in seen:
            print(
                f"attribute-census: duplicate row id {row.row_id} at {row.anchor} and {seen[row.row_id]}",
                file=sys.stderr,
            )
            return 2
        seen[row.row_id] = row.anchor
    rows.sort(key=lambda row: (row.module, row.anchor, row.name))

    epoch = extract_epoch()
    header = [
        f"schema {SCHEMA}",
        f"# The pinned attribute-state census (bead fln-attribute-state-census-h14).",
        f"# Generated mechanically from the pinned Reference sources ({epoch}) by",
        f"# scripts/extract/gen_attribute_state_census.py — the Reference is data,",
        f"# never a runtime component (D8). Byte-identical regeneration is the",
        f"# contract; run the generator with --check to verify.",
        f"#",
        f"# Row grammar: space-separated key=value, '%'-escaped. Unknown/custom",
        f"# attributes instantiate the OpaqueFallback shape at the end; nothing",
        f"# unclassified exists in this file.",
        f"epoch {epoch}",
        f"generator fnv1a64:{fnv1a64(Path(__file__).read_bytes()).split(':')[1]}",
        f"rows-total {len(rows)}",
        f"wrapper-machinery-excluded {machinery}",
    ]
    body = [row.canonical(FAMILY_FACTS) for row in rows]
    fallback_fields = [
        ("row", "opaque-fallback"),
        ("epoch", epoch),
        ("module", "parameterized"),
        ("anchor", "parameterized"),
        ("name", "<any unregistered attribute name>"),
        ("family", "opaque"),
        ("state-kind", "opaque-extension-state"),
        ("descr", "parameterized fallback for unknown and custom attributes"),
        ("application-time", "row-declared"),
        ("target-constraints", "row-declared"),
        ("payload-shape", "opaque payload preserved byte-exact and flagged in provenance"),
        ("tie-order", "registration order"),
        ("scope-persistence", "row-declared AttributeKind discipline"),
        ("import-replay", "opaque bytes replay without interpretation"),
        ("removal-replacement", "row-declared"),
        ("query-surfaces", "none beyond presence and payload preservation"),
        ("handler-class", "opaque-handler-required"),
        ("root-participation", "opaque payload never enters logical_root beyond presence"),
        ("epoch-migration", "opaque payload blocks fine migration honestly"),
        ("claim-class", "invariant"),
        ("evidence-grade", "L0-declared-shape"),
        ("evidence-anchor", "parameterized"),
    ]
    fallback = " ".join(f"{key}={encode(value)}" for key, value in fallback_fields)
    check_cancelled("pre-publication")
    text = "\n".join(header + body + [fallback]) + "\n"
    if len(text.encode("utf-8")) > MAX_OUTPUT_BYTES:
        print(
            f"attribute-census: budget refusal — the output exceeds {MAX_OUTPUT_BYTES} bytes "
            f"({len(text.encode('utf-8'))} used; the encoder broke or the scan exploded)",
            file=sys.stderr,
        )
        return 2
    if len(rows) > MAX_ROWS:
        print(
            f"attribute-census: budget refusal — {len(rows)} rows exceeds the row budget of {MAX_ROWS}",
            file=sys.stderr,
        )
        return 2
    root_hash = fnv1a64(text.encode("utf-8"))
    text += f"census-root {root_hash}\n"

    if args.check:
        if not OUTPUT.exists():
            print("attribute-census: committed census is absent", file=sys.stderr)
            return 2
        committed = OUTPUT.read_text(encoding="utf-8")
        if committed != text:
            print("attribute-census: committed census drifted from the pinned sources", file=sys.stderr)
            return 1
        print(f"attribute-census: OK ({len(rows)} rows, root {root_hash})")
        return 0

    def publish(path: Path) -> None:
        """The atomic write: a sibling temp file, fsync, then rename. A crash
        anywhere before the rename leaves the committed file untouched —
        that is the clean-retry law, and the lane's cancellation leg proves it."""
        tmp = path.with_suffix(path.suffix + ".candidate")
        tmp.write_text(text, encoding="utf-8")
        with open(tmp, "rb") as handle:
            os.fsync(handle.fileno())
        os.replace(tmp, path)

    if args.output:
        output_path = Path(args.output)
        publish(output_path)
        print(f"attribute-census: wrote {output_path} ({len(rows)} rows, root {root_hash})")
        return 0

    publish(OUTPUT)
    print(f"attribute-census: wrote {OUTPUT} ({len(rows)} rows, root {root_hash})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
