#!/usr/bin/env -S python3 -I -S
"""Compile the curated mathlib metaprogram slice's toolchain demand AGAINST THE
FACADE ALONE (bead `fln-l8f`, G0-8 acceptance b; plan §4.3, risk R1, OQ-3).

THE QUESTION THIS ANSWERS, and the one it does not. Acceptance (b) says "generated
facade stubs compile against real mathlib tactic code". Two readings live inside
that sentence and only one of them is affordable at G0:

  READING 1 (what this measures): every toolchain constant that a REAL curated
  mathlib metaprogram file actually uses — the elaborated demand measured in
  contracts/facade_demand_exact.ndjson, not a lexical guess — resolves, at its
  Reference type, against the standalone facade with NO Reference `Lean.*` in
  scope. That is a real compile against real demand, and it is falsifiable: the
  negative control below shows the same probe failing when the facade is emptied.

  READING 2 (NOT measured here, and named so nobody reads this artifact as it):
  elaborating the curated FILES themselves against the facade. Those files import
  Mathlib, Batteries, Aesop and Qq — the library-code partition — so that reading
  needs the whole library closure source-elaborated against the facade first. It
  is the Mirror rig's job and it is priced as such, not silently claimed here.

THE HIDDEN-ORACLE GUARDS, because a probe that quietly resolves its names through
the toolchain would report a perfect facade:

  * LEAN_PATH is the facade root and nothing else; no probe may contain `import
    Lean`; the facade root is refused if it holds any Reference artifact.
  * A NEGATIVE CONTROL runs the same probe against an EMPTY facade. If it does not
    fail, the whole run refuses: whatever the probe was proving, it was not the
    facade.
  * A ROW-REMOVAL CONTROL selects a demanded leaf axiom from the generated
    manifest, removes exactly that declaration from a temporary facade, and
    requires the matching probe row to become unavailable. This proves the rig
    can detect a missing generated row rather than merely a completely empty
    module.
  * A DEMANDED-ROW JOIN requires every real toolchain-api demand to have exactly
    one classified facade-manifest row. Each emitted check carries that row's
    disposition, so an unclassified name cannot disappear behind a name-only
    probe or a misleading aggregate.
  * A QUARANTINE CONTROL selects a demanded quarantined row and requires it to
    remain unresolved against both the generated and empty facades. A row marked
    quarantined is neither emitted nor Init substrate; treating it as available
    would make the disposition join lie.
  * A DISPOSITION MATRIX applies those expectations to the whole demanded set:
    emitted rows must be facade-only, Init rows must be substrate-only, and
    quarantined rows must be absent. A classified denominator is not enough if
    the generated facade's observed behavior contradicts its classification.
  * A REFERENCE-IMPORT CONTROL rejects `import Lean` (or `Lean.*`) in the facade
    source itself. Keeping Reference artifacts out of the temporary root is not
    sufficient if the source can ask the compiler to find them elsewhere.
  * A DEMANDED-ROLE JOIN makes the manifest's role agree with its disposition:
    emitted and quarantined rows must be explicitly demanded, while Init rows
    must be explicitly substrate. A closure row cannot impersonate a demand.
  * A CURATED-MODULE JOIN requires every toolchain-api use in the exact-demand
    artifact to name a declared curated module. Otherwise a use outside the
    reported slice can affect aggregate controls while disappearing from the
    per-module evidence.
  * A CENSUS-PARTITION JOIN requires every exact-demand symbol to resolve to a
    known partition row before the toolchain-api filter is applied. An
    uncensused symbol must refuse the run, never silently leave its denominator.
  * A DEMANDED-EMISSION JOIN makes the manifest's `emitted` bit agree with its
    demanded disposition: emitted rows must say true; Init and quarantined rows
    must say false. The row's stated provenance cannot contradict its outcome.
  * A STRUCTURAL-PROVIDER JOIN requires every demanded row that claims a
    `provided_by` structural block to name one emitted class or structure row.
    Generated projections and transparent wrappers cannot cite a phantom owner.
  * An UNRESOLVED-QUARANTINE JOIN requires the observed unresolved demanded set
    to equal the manifest's quarantined set, with an explicit quarantine reason
    for every member. The remaining known gap cannot be silently reclassified.
  * A SIGNATURE-PROVENANCE JOIN requires each non-Init demanded signature to
    carry a recognized Reference printer label and well-formed universe
    parameters. A type ascription cannot quietly consume an untyped payload.
  * A TYPE-ASCRIPTION JOIN requires every emitted or quarantined demand to enter
    the typed probe, while every Init-substrate demand remains name-only. The
    manifest disposition and the probe's actual checking mode must agree.
  * A PROVIDER-DEPENDENCY JOIN requires a demanded row's `provided_by` owner to
    occur exactly once in its declared type dependencies. Structural provenance
    and type-level closure must name the same generated owner.
  * A TYPE-DEPENDENCY SHAPE JOIN requires every non-Init demand to carry a
    duplicate-free, non-self-referential list of named type dependencies. The
    dependency relation used by the provider join must itself be well-formed.
  * A TYPE-DEPENDENCY TARGET JOIN resolves every non-manifest type dependency
    against the empty facade (Init only), while manifest targets must be unique.
    The generated closure cannot hide an undeclared dependency behind the pin.

Output: NDJSON, schema fln-facade-compile/1 — one row per (module, symbol), one
per module, and a summary that carries the reading above with it.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from collections import Counter, defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PARTITION = os.path.join(REPO, "contracts", "builtin_partition.tsv")
SCHEMA = "fln-facade-compile/1"
DEMANDED_OUTCOMES = frozenset(("emitted", "init-substrate", "quarantined"))


def input_digest(path):
    """Bind a derived artifact to the exact bytes it was derived FROM. Every input
    here is itself generated and is being regenerated by other hands; a summary
    that names its inputs by PATH alone goes stale silently, and the reader cannot
    tell a fresh row from one derived before the input moved."""
    with open(path, "rb") as fh:
        return {"path": os.path.relpath(path, REPO),
                "sha256": hashlib.sha256(fh.read()).hexdigest()}


def pinned_lean():
    with open(os.path.join(REPO, "SUITE.lock"), encoding="utf-8") as fh:
        lock = fh.read()
    tag = corpus = None
    for line in lock.splitlines():
        if line.startswith("reference "):
            for field in line.split():
                if field.startswith("tag="):
                    tag = field[4:]
        if line.startswith("corpus "):
            for field in line.split():
                if field.startswith("commit="):
                    corpus = field[7:]
    if not tag:
        raise SystemExit("REFUSE: SUITE.lock has no Reference tag")
    path = os.path.join(os.path.expanduser("~"), ".elan", "toolchains",
                        f"leanprover--lean4---{tag}", "bin", "lean")
    if not os.path.isfile(path):
        raise SystemExit(f"SKIP: pinned Reference not installed at {path}")
    return path, tag, corpus


def load_partition():
    """census key -> partition class. The denominator of this measurement must not
    come from the facade's own manifest: asking the facade which symbols it should
    serve and then checking exactly those is a tautology, and it reads as full
    coverage no matter how small the facade is."""
    part = {}
    with open(PARTITION, encoding="utf-8", errors="replace") as fh:
        for lineno, line in enumerate(fh, 1):
            if not line.startswith("partition\t"):
                continue
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 3:
                raise SystemExit(f"REFUSE: {PARTITION}:{lineno} is truncated")
            part[cols[1]] = cols[2]
    if not part:
        raise SystemExit("REFUSE: partition census loaded zero rows")
    return part


def load_demand(path, part):
    """Curated module -> the toolchain-api constants it actually uses, from the
    elaborated exact-demand artifact (never a lexical scan: `open Lean Meta Elab`
    makes ~95% of real usage unqualified, measured on this same slice)."""
    by_module = defaultdict(set)
    modules = None
    unscoped = []
    uncensused = []
    partition_classes = Counter()
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(f"REFUSE: {path}:{lineno} is not JSON ({exc})") from exc
            if row.get("kind") == "summary":
                if modules is not None:
                    raise SystemExit(f"REFUSE: {path} has multiple summaries")
                modules = row.get("curated_modules", [])
                continue
            if row.get("kind") != "symbol":
                continue
            key = row.get("census_key")
            if key is None:
                raise SystemExit(f"REFUSE: {path}:{lineno} carries no census_key")
            cls = part.get('"' + key.replace('"', '\\"') + '"')
            if cls is None:
                uncensused.append(f"{row['name']}[{key}]")
                continue
            partition_classes[cls] += 1
            if cls != "toolchain-api":
                continue
            used_by = row.get("used_by")
            if (not isinstance(used_by, list) or not used_by
                    or not all(isinstance(module, str) for module in used_by)):
                unscoped.append(row["name"])
                continue
            for module in used_by:
                by_module[module].add(row["name"])
    if (not isinstance(modules, list) or not modules
            or not all(isinstance(module, str) for module in modules)):
        raise SystemExit(f"REFUSE: {path} has no curated_modules summary — the slice "
                         "under test would be undefined")
    if len(set(modules)) != len(modules):
        raise SystemExit(f"REFUSE: {path} repeats a curated module — the per-module "
                         "denominator would be ambiguous")
    if uncensused:
        raise SystemExit(
            "REFUSE: exact-demand census-partition join found uncensused symbols "
            "(" + ", ".join(sorted(uncensused)[:8]) + ") — no demand may "
            "silently disappear before the toolchain-api filter"
        )
    out_of_slice = sorted(set(by_module).difference(modules))
    if unscoped or out_of_slice:
        details = []
        if unscoped:
            details.append("unscoped=" + ", ".join(sorted(unscoped)[:8]))
        if out_of_slice:
            details.append("out-of-slice=" + ", ".join(out_of_slice[:8]))
        raise SystemExit(
            "REFUSE: curated-module demand join failed (" + "; ".join(details)
            + ") — every toolchain-api use must be attributable to one declared "
            "curated module"
        )
    if not by_module:
        raise SystemExit("REFUSE: no toolchain-api demand joined — an empty demand "
                         "compiles vacuously and reads as full facade coverage")
    module_join = {
        "curated_modules": len(modules),
        "toolchain_use_edges": sum(len(names) for names in by_module.values()),
    }
    partition_join = dict(sorted(partition_classes.items()))
    return modules, by_module, module_join, partition_join


def reference_import_lines(text):
    """Return source lines that import Reference Lean modules.

    Imports are line-oriented Lean commands. Strip trailing line comments before
    tokenizing so the generator's explanatory comments do not trip the guard.
    The allowed shared substrate is implicit `Init`, never a direct Lean import.
    """
    hits = []
    for lineno, line in enumerate(text.splitlines(), 1):
        command = line.split("--", 1)[0].strip()
        if not command.startswith("import "):
            continue
        targets = command.removeprefix("import ").split()
        if any(target == "Lean" or target.startswith("Lean.") for target in targets):
            hits.append(lineno)
    return hits


def refuse_reference_imports(source, label):
    with open(source, encoding="utf-8") as fh:
        hits = reference_import_lines(fh.read())
    if hits:
        shown = ", ".join(str(line) for line in hits[:8])
        raise SystemExit(
            f"REFUSE: the {label} facade source imports Reference Lean at line(s) "
            f"{shown} — a standalone facade may not import the implementation it "
            "purports to replace"
        )


def build_facade(lean, env, root, source, label):
    refuse_reference_imports(source, label)
    os.makedirs(root, exist_ok=True)
    dst = os.path.join(root, "FlnFacade.lean")
    shutil.copyfile(source, dst)
    # `lean -o` refuses an input outside its root directory, so the build runs
    # WITH the facade root as cwd and relative names.
    proc = subprocess.run([lean, "-o", "FlnFacade.olean", "FlnFacade.lean"],
                          cwd=root, capture_output=True, text=True, env=env,
                          timeout=1800)
    if proc.returncode != 0:
        raise SystemExit(f"REFUSE: the {label} facade does not build:\n"
                         f"{(proc.stdout + proc.stderr)[:1200]}")
    for entry in os.listdir(root):
        if entry.startswith("Lean") and entry != "FlnFacade.lean" and not entry.startswith("FlnFacade"):
            raise SystemExit(f"REFUSE: {root} holds {entry} — a facade root that "
                             "carries a Reference artifact is not a facade")
    return root


def choose_row_removal_control(names, manifest_rows):
    """Choose a demanded axiom whose removal leaves the temporary facade buildable.

    A hard-coded symbol would rot when the exact demand or the generated closure
    moves. A leaf has no manifest type-level dependents, so deleting its one axiom
    line tests probe resolution rather than merely breaking a different signature
    while building the negative-control facade.
    """
    dependents = Counter(
        dep for row in manifest_rows for dep in row.get("type_deps", ())
    )
    candidates = sorted(
        row["name"]
        for row in manifest_rows
        if row["name"] in names
        and row.get("demanded_outcome") == "emitted"
        and row.get("form") == "axiom"
        and not row.get("provided_by")
        and dependents[row["name"]] == 0
    )
    if not candidates:
        raise SystemExit(
            "REFUSE: no demanded leaf axiom is available for the row-removal "
            "control — a rig that cannot make one generated row disappear cannot "
            "prove it detects missing-row drift"
        )
    return candidates[0]


def write_row_removed_facade(source, destination, name):
    """Copy `source` while removing exactly one generated axiom declaration."""
    with open(source, encoding="utf-8") as fh:
        text = fh.read()
    pattern = re.compile(
        rf"^axiom {re.escape(name)}(?:\.\{{[^}}]*\}})? : .*$", re.MULTILINE
    )
    candidate, removed = pattern.subn("", text, count=1)
    if removed != 1:
        raise SystemExit(
            f"REFUSE: row-removal control could not remove exactly one axiom for "
            f"{name} (removed={removed}) — the generated declaration spelling drifted"
        )
    with open(destination, "w", encoding="utf-8") as fh:
        fh.write(candidate)


def join_demanded_rows(names, manifest_rows):
    """Bind every demanded name to one classified manifest row.

    The exact-demand extractor sets the denominator while the facade generator
    records how it treated each demanded symbol. Neither artifact alone proves
    they cover the same names. Refuse missing, duplicate, or unclassified rows
    before compiling: otherwise a demand with no Reference signature degrades to
    a name-only probe and can be hidden in aggregate availability counts.
    """
    rows_by_name = defaultdict(list)
    for row in manifest_rows:
        rows_by_name[row["name"]].append(row)

    missing = sorted(name for name in names if name not in rows_by_name)
    duplicate = sorted(name for name in names if len(rows_by_name[name]) != 1)
    if missing or duplicate:
        details = []
        if missing:
            details.append("missing=" + ", ".join(missing[:8]))
        if duplicate:
            details.append("duplicate=" + ", ".join(duplicate[:8]))
        raise SystemExit(
            "REFUSE: demanded-row join is not one-to-one (" + "; ".join(details)
            + ") — a compile result without a classified facade disposition is "
            "not publishable"
        )

    dispositions = {}
    unclassified = []
    signatureless = []
    role_mismatches = []
    emission_mismatches = []
    provider_mismatches = []
    provider_dependency_mismatches = []
    type_dependency_shape_mismatches = []
    signature_provenance_mismatches = []
    roles = Counter()
    emission_join = Counter()
    provider_join = Counter()
    printer_join = Counter()
    type_dependency_join = Counter()
    for name in sorted(names):
        row = rows_by_name[name][0]
        outcome = row.get("demanded_outcome")
        if outcome not in DEMANDED_OUTCOMES:
            unclassified.append(name)
            continue
        # Init substrate names are deliberately absent from the generated facade;
        # their availability is separated by the empty-facade control. Every other
        # classified row must carry the Reference signature used for the type probe.
        if outcome != "init-substrate" and not isinstance(row.get("signature"), str):
            signatureless.append(name)
            continue
        type_deps = row.get("type_deps")
        if outcome != "init-substrate":
            printer = row.get("printer")
            level_params = row.get("level_params")
            if (printer not in ("pp.fullNames", "pp.explicit", "pp.maxexplicit")
                    or not isinstance(level_params, list)
                    or not all(isinstance(level, str) and level for level in level_params)):
                signature_provenance_mismatches.append(
                    f"{name}(printer={printer!r}, level_params={level_params!r})"
                )
                continue
            printer_join[printer] += 1
            if (not isinstance(type_deps, list)
                    or not all(isinstance(dep, str) and dep for dep in type_deps)
                    or len(type_deps) != len(set(type_deps))
                    or name in type_deps):
                type_dependency_shape_mismatches.append(
                    f"{name}(type_deps={type_deps!r})"
                )
                continue
            type_dependency_join["rows"] += 1
            type_dependency_join["edges"] += len(type_deps)
        expected_role = "init-substrate" if outcome == "init-substrate" else "demanded"
        if row.get("role") != expected_role:
            role_mismatches.append(
                f"{name}(outcome={outcome}, role={row.get('role')!r})"
            )
            continue
        expected_emitted = outcome == "emitted"
        if row.get("emitted") is not expected_emitted:
            emission_mismatches.append(
                f"{name}(outcome={outcome}, emitted={row.get('emitted')!r})"
            )
            continue
        provider = row.get("provided_by")
        if provider is not None:
            owners = rows_by_name.get(provider, ())
            owner = owners[0] if len(owners) == 1 else None
            if (row.get("form") not in ("class-projection", "transparent-abbrev")
                    or owner is None
                    or owner.get("form") not in ("class", "structure")
                    or owner.get("emitted") is not True):
                provider_mismatches.append(
                    f"{name}(provided_by={provider!r})"
                )
                continue
            if (not isinstance(type_deps, list)
                    or type_deps.count(provider) != 1):
                provider_dependency_mismatches.append(
                    f"{name}(provided_by={provider!r}, type_deps={type_deps!r})"
                )
                continue
            provider_join["structural"] += 1
            provider_join["structural_type_dependency"] += 1
        else:
            if row.get("form") == "class-projection":
                provider_mismatches.append(f"{name}(class-projection lacks provided_by)")
                continue
            provider_join["direct"] += 1
        dispositions[name] = outcome
        roles[expected_role] += 1
        emission_join["emitted" if expected_emitted else "not_emitted"] += 1
    if (unclassified or signatureless or role_mismatches or emission_mismatches
            or provider_mismatches or provider_dependency_mismatches
            or signature_provenance_mismatches or type_dependency_shape_mismatches):
        details = []
        if unclassified:
            details.append("unclassified=" + ", ".join(unclassified[:8]))
        if signatureless:
            details.append("signatureless=" + ", ".join(signatureless[:8]))
        if role_mismatches:
            details.append("role-mismatch=" + ", ".join(role_mismatches[:8]))
        if emission_mismatches:
            details.append("emission-mismatch=" + ", ".join(emission_mismatches[:8]))
        if provider_mismatches:
            details.append("provider-mismatch=" + ", ".join(provider_mismatches[:8]))
        if provider_dependency_mismatches:
            details.append("provider-dependency=" + ", ".join(
                provider_dependency_mismatches[:8]
            ))
        if signature_provenance_mismatches:
            details.append("signature-provenance=" + ", ".join(
                signature_provenance_mismatches[:8]
            ))
        if type_dependency_shape_mismatches:
            details.append("type-dependency-shape=" + ", ".join(
                type_dependency_shape_mismatches[:8]
            ))
        raise SystemExit(
            "REFUSE: demanded-row join cannot support a typed disposition ("
            + "; ".join(details) + ")"
        )
    return (dispositions, dict(sorted(roles.items())),
            dict(sorted(emission_join.items())), dict(sorted(provider_join.items())),
            dict(sorted(printer_join.items())), dict(sorted(type_dependency_join.items())))


def choose_quarantine_control(dispositions):
    """Choose an actually-demanded quarantine row for the disposition control."""
    candidates = sorted(
        name for name, outcome in dispositions.items() if outcome == "quarantined"
    )
    if not candidates:
        raise SystemExit(
            "REFUSE: demanded-row join found no quarantined demand — the "
            "quarantine disposition has no observable control"
        )
    return candidates[0]


def enforce_disposition_matrix(dispositions, generated, empty):
    """Refuse a manifest disposition that disagrees with both probe controls."""
    mismatches = []
    for name in sorted(dispositions):
        outcome = dispositions[name]
        generated_verdict = generated[name]
        empty_verdict = empty[name]
        if outcome == "emitted":
            matches = generated_verdict == "available" and empty_verdict != "available"
        elif outcome == "init-substrate":
            matches = generated_verdict == "available" and empty_verdict == "available"
        else:
            matches = generated_verdict == "unresolved" and empty_verdict == "unresolved"
        if not matches:
            mismatches.append(
                f"{name}({outcome}: generated={generated_verdict}, empty={empty_verdict})"
            )
    if mismatches:
        raise SystemExit(
            "REFUSE: demanded-row disposition matrix disagrees with the facade "
            "controls (" + "; ".join(mismatches[:8]) + ")"
        )
    return dict(sorted(Counter(dispositions.values()).items()))


def join_unresolved_quarantine(dispositions, manifest_rows, verdicts, diagnostics):
    """Bind every observed unresolved demanded name to one justified quarantine."""
    rows_by_name = {row["name"]: row for row in manifest_rows}
    unresolved = sorted(name for name, verdict in verdicts.items() if verdict == "unresolved")
    quarantined = sorted(
        name for name, outcome in dispositions.items() if outcome == "quarantined"
    )
    if unresolved != quarantined:
        raise SystemExit(
            "REFUSE: observed unresolved demand does not equal the quarantined "
            "manifest set (observed=" + ", ".join(unresolved[:8])
            + "; quarantined=" + ", ".join(quarantined[:8]) + ")"
        )
    joined = []
    for name in unresolved:
        reason = rows_by_name[name].get("quarantine_reason")
        if not isinstance(reason, str) or not reason.strip():
            raise SystemExit(
                f"REFUSE: unresolved demanded row {name} has no quarantine_reason"
            )
        joined.append({
            "name": name,
            "quarantine_reason": reason,
            "diagnostic": diagnostics.get(name),
        })
    return joined


def join_type_ascriptions(dispositions, sigs):
    """Make the probe's type-ascription set match demanded dispositions exactly."""
    expected_typed = {
        name for name, outcome in dispositions.items() if outcome != "init-substrate"
    }
    actual_typed = set(sigs).intersection(dispositions)
    missing = sorted(expected_typed.difference(actual_typed))
    unexpected = sorted(actual_typed.difference(expected_typed))
    if missing or unexpected:
        details = []
        if missing:
            details.append("missing-typed=" + ", ".join(missing[:8]))
        if unexpected:
            details.append("unexpected-typed=" + ", ".join(unexpected[:8]))
        raise SystemExit(
            "REFUSE: demanded type-ascription join failed (" + "; ".join(details)
            + ") — the probe's type-checking mode disagrees with its disposition"
        )
    return {
        "typed": len(actual_typed),
        "name_only_init": len(dispositions) - len(actual_typed),
    }


def join_type_dependency_targets(dispositions, manifest_rows):
    """Split demanded type dependencies into manifest and Init-only targets."""
    rows_by_name = defaultdict(list)
    for row in manifest_rows:
        rows_by_name[row["name"]].append(row)
    dependencies = {
        dependency
        for name, outcome in dispositions.items()
        if outcome != "init-substrate"
        for dependency in rows_by_name[name][0]["type_deps"]
    }
    ambiguous = sorted(
        dependency for dependency in dependencies
        if dependency in rows_by_name and len(rows_by_name[dependency]) != 1
    )
    if ambiguous:
        raise SystemExit(
            "REFUSE: type-dependency target join found ambiguous manifest targets "
            "(" + ", ".join(ambiguous[:8]) + ")"
        )
    init_only = sorted(dependency for dependency in dependencies if dependency not in rows_by_name)
    return init_only, {
        "manifest_targets": len(dependencies) - len(init_only),
        "init_only_targets": len(init_only),
    }


def probe_text(names, sigs):
    """Two lines per symbol, because they answer two different questions.

    `#check @X` answers "does the name resolve against the facade". The ascription
    `noncomputable def flnchk_i.{lvls} : <the Reference's printed type> := @X`
    answers "and does it have the REFERENCE's type", up to defeq, decided by the
    pin rather than by string comparison (which would drown in universe renaming:
    the pin prints `u, v, w` and `#check` prints `u_1, u_2, u_3`).

    For a row the facade declares as an `axiom` the ascription is tautological —
    the axiom was declared FROM that string. It is not tautological for the rows
    that matter here: a class projection is GENERATED by the structural class
    block from field declarations, so its type is Lean's inference, not a copy of
    the pin's, and this is the only thing that checks the two agree.
    """
    lines = ["import FlnFacade", "set_option autoImplicit false", ""]
    line_map = {}
    for i, name in enumerate(names):
        lines.append(f"#check @{name}")
        line_map[len(lines)] = (name, "resolve")
        sig = sigs.get(name)
        if sig and sig.get("signature"):
            lvls = sig.get("level_params") or []
            binder = (".{" + ", ".join(lvls) + "}") if lvls else ""
            lines.append(f"noncomputable def flnchk_{i}{binder} : "
                         f"{sig['signature']} := @{name}")
            line_map[len(lines)] = (name, "type")
    return "\n".join(lines) + "\n", line_map


def run_probe(lean, root, work, tag_name, names, sigs=None):
    text, line_map = probe_text(names, sigs or {})
    if "import Lean" in text:
        raise SystemExit("REFUSE: a probe imports the Reference")
    src = os.path.join(work, f"probe_{tag_name}.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(text)
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
    env["LC_ALL"] = "C"
    env["LEAN_PATH"] = root
    proc = subprocess.run([lean, "-DmaxErrors=100000", src],
                          capture_output=True, text=True, env=env, timeout=1800)
    out = proc.stdout + proc.stderr
    verdict = {n: "available" for n in names}
    detail = {}
    base = os.path.basename(src)
    for m in re.finditer(rf"{re.escape(base)}:(\d+):\d+: error(?:\(([^)]*)\))?: (.*)",
                         out):
        hit = line_map.get(int(m.group(1)))
        if hit is None:
            continue
        name, role = hit
        kind, msg = (m.group(2) or ""), m.group(3)
        unknown = ("nknown" in kind or "nknown identifier" in msg
                   or "nknown constant" in msg)
        if role == "resolve":
            # a resolution failure is final for the row and outranks whatever the
            # ascription said about a name that is not there
            verdict[name] = "unresolved" if unknown else "resolved-but-rejected"
            detail[name] = (kind or "-") + ": " + msg[:200]
        elif verdict[name] == "available":
            verdict[name] = ("type-mismatch" if "ype mismatch" in msg
                             else "type-unelaborable")
            detail[name] = (kind or "-") + ": " + msg[:200]
    return verdict, detail, out


def module_source(corpus, module):
    """Bind each curated row to the real upstream file it came from. A slice named
    only by module name is a claim about files nobody re-read."""
    if not corpus:
        return None
    path = os.path.join(corpus, *module.split(".")) + ".lean"
    if not os.path.isfile(path):
        return {"module": module, "present": False}
    with open(path, "rb") as fh:
        data = fh.read()
    return {"module": module, "present": True,
            "path": os.path.relpath(path, corpus),
            "bytes": len(data), "lines": data.count(b"\n"),
            "sha256": hashlib.sha256(data).hexdigest()}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--facade", required=True, help="the standalone facade module")
    ap.add_argument("--demand", required=True, help="fln-facade-demand-exact/1 NDJSON")
    ap.add_argument("--module-manifest", required=True,
                    help="fln-facade-module/1 NDJSON: supplies each row's Reference "
                         "signature so the check is a TYPE check, not just a name check")
    ap.add_argument("--corpus", help="the pinned mathlib source tree (provenance)")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    lean, tag, corpus_commit = pinned_lean()
    part = load_partition()
    modules, by_module, module_join, partition_join = load_demand(args.demand, part)
    work = os.path.join(os.environ.get("TMPDIR", "/tmp"), f"fln-l8f-compile-{os.getpid()}")
    os.makedirs(work, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
    env["LC_ALL"] = "C"

    sigs = {}
    manifest_rows = []
    with open(args.module_manifest, encoding="utf-8") as fh:
        for line in fh:
            row = json.loads(line)
            if row.get("kind") != "decl":
                continue
            manifest_rows.append(row)
            if row.get("signature"):
                sigs[row["name"]] = {"signature": row["signature"],
                                       "level_params": row.get("level_params") or [],
                                       "form": row.get("form")}
    if not sigs:
        raise SystemExit("REFUSE: the module manifest carries no signatures — the "
                         "run would silently degrade to a name-only check")

    demand_names = {name for names in by_module.values() for name in names}
    (demand_dispositions, demand_roles, demand_emission, demand_providers,
     demand_printers, demand_type_dependencies) = join_demanded_rows(
         demand_names, manifest_rows
     )
    type_ascription_join = join_type_ascriptions(demand_dispositions, sigs)

    # Mutation control for the source guard above. It is deliberately in-memory:
    # no Reference-importing file is ever handed to the pinned compiler.
    if not reference_import_lines("import Lean\n"):
        raise SystemExit(
            "REFUSE: Reference-import control did not recognize `import Lean` — "
            "the facade-source oracle guard is ineffective"
        )

    root = build_facade(lean, env, os.path.join(work, "facade"), args.facade, "generated")
    empty_src = os.path.join(work, "empty.lean")
    with open(empty_src, "w", encoding="utf-8") as fh:
        fh.write("-- the negative control: a facade that declares nothing\n")
    empty_root = build_facade(lean, env, os.path.join(work, "empty"), empty_src, "empty")

    init_type_dependencies, type_dependency_target_join = join_type_dependency_targets(
        demand_dispositions, manifest_rows
    )
    init_dependency_verdicts, _, _ = run_probe(
        lean, empty_root, work, "control_type_dependencies", init_type_dependencies
    )
    missing_init_dependencies = [
        name for name in init_type_dependencies
        if init_dependency_verdicts[name] != "available"
    ]
    if missing_init_dependencies:
        raise SystemExit(
            "REFUSE: type-dependency target join found non-manifest dependencies "
            "outside Init (" + ", ".join(missing_init_dependencies[:8]) + ")"
        )
    type_dependency_target_join["init_only_verified"] = len(init_type_dependencies)

    # THE NEGATIVE CONTROL, run before any result is believed. The same probe over
    # the same names against an EMPTY facade must resolve strictly fewer names. It
    # will not resolve zero: part of the demanded toolchain-api surface is defined
    # under Init, which every non-prelude module imports implicitly — so the honest
    # control is "the facade adds resolutions", not "nothing resolves without it".
    control_names = sorted(demand_names)
    v_facade, facade_detail, _ = run_probe(
        lean, root, work, "control_facade", control_names, sigs
    )
    v_empty, _, _ = run_probe(lean, empty_root, work, "control_empty", control_names, sigs)
    ok_facade = sum(1 for v in v_facade.values() if v == "available")
    ok_empty = sum(1 for v in v_empty.values() if v == "available")
    if ok_facade <= ok_empty:
        raise SystemExit(
            f"REFUSE: the facade resolves {ok_facade} of {len(control_names)} names and "
            f"an EMPTY facade resolves {ok_empty} — the probe is measuring the "
            "substrate, not the facade, and no result from it may be published")

    disposition_matrix = enforce_disposition_matrix(
        demand_dispositions, v_facade, v_empty
    )
    unresolved_quarantine_join = join_unresolved_quarantine(
        demand_dispositions, manifest_rows, v_facade, facade_detail
    )

    quarantine_name = choose_quarantine_control(demand_dispositions)
    quarantine_generated = v_facade[quarantine_name]
    quarantine_empty = v_empty[quarantine_name]
    if quarantine_generated != "unresolved" or quarantine_empty != "unresolved":
        raise SystemExit(
            f"REFUSE: quarantined demanded row {quarantine_name} resolves as "
            f"generated={quarantine_generated!r}, empty={quarantine_empty!r} — "
            "the demanded-row disposition is stale or the facade leaks a "
            "quarantined declaration"
        )

    removed_name = choose_row_removal_control(set(control_names), manifest_rows)
    if v_facade[removed_name] != "available":
        raise SystemExit(
            f"REFUSE: row-removal control selected {removed_name}, but the generated "
            f"facade already reports {v_facade[removed_name]!r}"
        )
    removed_src = os.path.join(work, "row_removed.lean")
    write_row_removed_facade(args.facade, removed_src, removed_name)
    removed_root = build_facade(
        lean, env, os.path.join(work, "row_removed"), removed_src, "row-removed"
    )
    v_removed, removed_detail, _ = run_probe(
        lean, removed_root, work, "control_row_removed", [removed_name], sigs
    )
    if v_removed[removed_name] == "available":
        raise SystemExit(
            f"REFUSE: row-removal control removed {removed_name}, but the probe still "
            "accepts it — missing generated rows are not observable to this rig"
        )

    rows = []
    per_module = {}
    verdict_counts = Counter()
    for module in sorted(modules):
        names = sorted(by_module.get(module, ()))
        if not names:
            per_module[module] = {"checked": 0}
            continue
        verdict, detail, _ = run_probe(lean, root, work, re.sub(r"\W", "_", module),
                                       names, sigs)
        counts = Counter(verdict.values())
        verdict_counts.update(counts)
        per_module[module] = dict(counts)
        for name in names:
            rows.append({
                "schema": SCHEMA, "kind": "check", "module": module, "name": name,
                "verdict": verdict[name],
                "diagnostic": detail.get(name),
                "demanded_disposition": demand_dispositions[name],
                "substrate_only": v_empty.get(name) == "available",
            })

    checked = sum(len(by_module.get(m, ())) for m in modules)
    if checked == 0:
        raise SystemExit("REFUSE: zero checks ran")

    summary = {
        "schema": SCHEMA, "kind": "summary", "pin": tag,
        "corpus_commit": corpus_commit, "claim_class": "bounded_model",
        "inputs": [input_digest(args.facade), input_digest(args.module_manifest),
                   input_digest(args.demand),
                   input_digest(PARTITION)],
        "curated_modules": sorted(modules),
        "curated_module_join": module_join,
        "census_partition_join": partition_join,
        "checked": checked,
        "distinct_symbols": len(control_names),
        "demanded_dispositions": disposition_matrix,
        "demanded_role_join": demand_roles,
        "demanded_emission_join": demand_emission,
        "demanded_provider_join": demand_providers,
        "demanded_signature_printer_join": demand_printers,
        "demanded_type_dependency_join": demand_type_dependencies,
        "type_dependency_target_join": type_dependency_target_join,
        "demanded_type_ascription_join": type_ascription_join,
        "disposition_matrix_control": {
            "emitted": disposition_matrix.get("emitted", 0),
            "init_substrate": disposition_matrix.get("init-substrate", 0),
            "quarantined": disposition_matrix.get("quarantined", 0),
        },
        "unresolved_quarantine_join": unresolved_quarantine_join,
        "available": verdict_counts["available"],
        "unresolved": verdict_counts["unresolved"],
        "resolved_but_rejected": verdict_counts["resolved-but-rejected"],
        "type_mismatch": verdict_counts["type-mismatch"],
        "type_unelaborable": verdict_counts["type-unelaborable"],
        "type_checked": sum(1 for n in control_names if n in sigs),
        "type_check_note": "tautological for axiom rows (declared from that very "
                           "string); independent for class-projection rows, whose "
                           "type Lean derives from the structural block",
        "control_facade_available": ok_facade,
        "control_empty_available": ok_empty,
        "control_delta": ok_facade - ok_empty,
        "row_removal_control": {
            "name": removed_name,
            "generated_verdict": v_facade[removed_name],
            "removed_verdict": v_removed[removed_name],
            "removed_diagnostic": removed_detail.get(removed_name),
        },
        "quarantine_control": {
            "name": quarantine_name,
            "generated_verdict": quarantine_generated,
            "empty_verdict": quarantine_empty,
        },
        "reference_import_control": {
            "mutant": "import Lean",
            "rejected": True,
        },
        "reference_imported": False,
        "reading": "every toolchain-api constant the curated real mathlib metaprogram "
                   "files actually use, checked at its Reference type against the "
                   "standalone facade with no Reference Lean.* in scope",
        "not_claimed": "the curated FILES are not elaborated against the facade: they "
                       "import the Mathlib/Batteries/Aesop/Qq library-code closure, "
                       "which the Mirror rig must source-elaborate first",
    }
    if args.corpus:
        summary["provenance"] = [module_source(args.corpus, m) for m in sorted(modules)]
        absent = [p["module"] for p in summary["provenance"] if not p.get("present")]
        if absent:
            summary["provenance_absent"] = absent
    tmp = args.out + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(summary, sort_keys=True) + "\n")
        for module in sorted(per_module):
            fh.write(json.dumps({"schema": SCHEMA, "kind": "module", "module": module,
                                 **per_module[module]}, sort_keys=True) + "\n")
        for row in rows:
            fh.write(json.dumps(row, sort_keys=True) + "\n")
    os.replace(tmp, args.out)
    print(f"facade-compile: modules={len(modules)} checked={checked} "
          f"available={verdict_counts['available']} "
          f"unresolved={verdict_counts['unresolved']} "
          f"rejected={verdict_counts['resolved-but-rejected']} "
          f"type_mismatch={verdict_counts['type-mismatch']} "
          f"type_unelab={verdict_counts['type-unelaborable']} "
          f"control facade={ok_facade} empty={ok_empty}", file=sys.stderr)


if __name__ == "__main__":
    main()
