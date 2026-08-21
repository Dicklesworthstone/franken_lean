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
  * A CURATED-MODULE NON-VACUITY JOIN requires every declared curated module to
    contribute at least one toolchain-api demand. A zero-demand module cannot
    inflate the reported real-mathlib slice without producing evidence rows.
  * An EXACT-DEMAND SUMMARY JOIN makes the artifact's declared toolchain-api
    distinct-symbol count equal the union rebuilt for this rig's controls. A
    stale summary cannot misstate the compiled denominator.
  * A CENSUS-COMPLETENESS SUMMARY JOIN requires the exact-demand artifact to
    report an empty `census_missing` set. A demand denominator with known absent
    census rows is not eligible for facade coverage evidence.
  * A REFERENCE-PIN JOIN requires the exact-demand artifact's extraction pin to
    equal the Reference compiler pin running this rig. Matching names from a
    different upstream epoch are not compatible evidence.
  * A MANIFEST-PIN JOIN requires the facade manifest's schema and extraction pin
    to match this rig before demanded rows are consumed. Demand and facade rows
    cannot be joined across generated-contract epochs.
  * A MANIFEST-TOTALITY JOIN requires the facade generator to report zero
    uncensused closure/emitted rows and no Reference import. The compile rig may
    not turn a manifest's known classification gap into availability evidence.
  * A MANIFEST-OUTCOME TOTAL JOIN makes the manifest summary's demanded outcome
    counts equal the declaration rows it summarizes. A stale aggregate cannot
    conceal an omitted emitted, Init, or quarantined demanded row.
  * A LEVEL-PARAMETER JOIN requires every universe parameter carried into a
    demanded typed probe to occur in its Reference signature. The probe cannot
    invent a stale universe binder that the signature no longer uses.

  * A DEMANDED-EFFECT JOIN requires every non-Init demanded row to carry a
    recognized effect class. Name/type availability never promotes an
    semantically unclassified facade row into the evidence set.

  * A DEMANDED-BUCKET JOIN requires every non-Init demanded row to carry a
    recognized risk bucket. Effect metadata alone is not a complete facade
    disposition when a row is exposed to the compilation probe.

  * A DEMANDED-SAFETY JOIN requires every non-Init demanded row to carry a
    recognized safety label. A risk bucket without an explicit safety boundary
    is not a complete classification for compilation evidence.

  * An INSTANCE-REGISTRATION JOIN requires demanded instance rows to agree with
    registration and drop-reason metadata. A name/type probe cannot claim an
    instance surface whose manifest lifecycle is contradictory.

  * A DEMANDED-FORM JOIN requires every non-Init demanded row to carry a
    recognized generated form. Name/type availability cannot stand in for an
    unclassified declaration-emission shape.

  * A TRANSPARENCY-REFUSAL JOIN requires transparent abbreviations and rejected
    transparent candidates to agree with their form and refusal metadata. The
    rig must not conflate a value-preserving abbreviation with an opaque axiom.

  * A DISPOSITION-MUTATION CONTROL relabels one facade-only emitted demand as
    Init substrate in memory and requires the disposition matrix to refuse. The
    matrix is proved sensitive to a wrong demanded-row classification.

  * A CORPUS-PIN JOIN requires the exact-demand artifact's mathlib commit to
    equal the corpus pin in `SUITE.lock`. The demand slice cannot be reported
    against a different source epoch.

  * A DEMAND-COVERAGE-SPLIT JOIN requires the exact-demand artifact's covered
    and uncovered counts to sum to its toolchain-api denominator. The coverage
    aggregate cannot silently drop a demanded row.

  * A CONSTANT-UNIVERSE JOIN requires the exact-demand artifact's non-API
    partition counts plus toolchain API demand to reconstruct the measured
    distinct-constant universe at the pinned Reference epoch.

  * A DECLARATION-BODY JOIN requires the exact-demand artifact's measured
    declaration count and opaque/theorem body-unavailability census to be
    well-formed and bounded at the pinned Reference epoch.

  * A GONE-SYMBOL JOIN requires the exact-demand artifact's measured `gone` set
    to be empty. Symbols absent at the pinned Reference epoch cannot silently
    remain in a compile-demand denominator.

  * A MANIFEST-EMISSION-VERIFICATION JOIN requires the facade manifest's
    pin-measured verified-emission count to equal its emitted-declaration count.
    A generated façade cannot overstate verification of its own rows.

  * A MANIFEST-GENERATOR-RESIDUE JOIN requires zero cycle/value residue and a
    terminal generator attempt with zero errors. The facade cannot advertise a
    clean emitted surface while its recorded generation remains unresolved.

  * A MANIFEST-ATTEMPT-FINALIZATION JOIN requires the terminal zero-error
    attempt's quarantine count to equal the manifest's published quarantine
    count. A clean final attempt cannot be paired with a stale outcome summary.

  * A MANIFEST-NEGATIVE-CONTROL JOIN requires the recorded emission and Init
    decoys to be distinct names outside every manifest and demand set, with no
    falsified Init-substrate checks. A claimed negative control cannot overlap
    the positive universe it is meant to falsify.

  * A MANIFEST-PRINTER-TOTALITY JOIN requires every typed declaration to use
    one recognized Reference printer mode, while Init-substrate rows carry
    none. Rows outside the explicit-printer subset cannot lose rendering
    provenance.

  * A MANIFEST-PROJECTION-CLOSURE JOIN requires every class-projection row to
    name a structural provider and include that provider in its type
    dependencies. Generated projections cannot lose their owning type outside
    the demanded subset.

  * A MANIFEST-INIT-ROW-PROVENANCE JOIN requires every extracted Init-substrate
    artifact row to carry a nonempty reason. The shared-substrate half of the
    no-import proof cannot become an unexplained name exclusion.

  * A MANIFEST-INSTANCE-STATE JOIN requires every registered instance to be
    emitted and every row with an explicit dropped-instance reason to remain
    unregistered. Instance metadata cannot claim a registration the façade did
    not actually emit.

  * A MANIFEST-PROVIDER-TYPE-CLOSURE JOIN requires every `provided_by` owner
    across the full manifest to occur in that row's type dependencies. Structural
    provenance cannot drift from the declaration's reported type closure.

  * A MANIFEST-INPUT-DIGEST JOIN recomputes every extraction-input hash named by
    the facade manifest. Pin-derived provenance cannot be a self-reported list
    detached from the actual census and resistance inputs.

  * A MANIFEST-INPUT-SET JOIN requires exactly the known resistance artifact and
    three pinned environment shards. A valid hash list cannot omit a load-bearing
    extraction input or substitute an unrelated file.

  * A RESISTANCE-DEMAND CROSS JOIN requires the resistance artifact's measured
    demand totals to agree with both the facade manifest and exact-demand
    denominator. A hashed resistance input cannot still report a stale cohort.

  * A RESISTANCE-RATCHET JOIN requires exactly one ratchet step per risk bucket
    and their measured memberships to reconstruct the joined resistance cohort.
    Bucket-level assurance rows cannot drift from their summary total.

  * A RESISTANCE-ASSURANCE JOIN requires each ratchet bucket's pinned step and
    assurance-level prefix. Measured resistance membership cannot drift from the
    confidence boundary that governs how it may be claimed.

  * A MANIFEST-EMITTED-ROW JOIN requires the manifest's measured emitted
    declaration count to equal the number of declaration rows carrying
    `emitted=true`. The summary may not claim pin-verified emission for rows
    that are absent from its own row set.

  * A MANIFEST-EMITTED-NAME JOIN requires every emitted row to name a distinct
    declaration and binds the manifest's distinct-emission count to that set.
    Duplicate rows may not impersonate distinct coverage.

  * A MANIFEST-TRANSPARENCY JOIN binds the generator's measured transparent
    declaration count to the declaration rows marked `transparent-abbrev`.
    A summary cannot claim a transparent compatibility surface that its own
    manifest does not enumerate.

  * A MANIFEST-STRUCTURAL JOIN binds the generator's structural and class
    declaration totals to rows marked `structure` and `class`. A claimed
    structural surface cannot omit a category or count it twice.

  * A MANIFEST-SUBSTRATE-EMISSION JOIN binds the summary's native substrate
    emission count to rows that are both emitted and marked `substrate`. A
    correct aggregate emission total may not hide a misclassified substrate.

  * A MANIFEST-INIT-SUBSTRATE JOIN binds the extracted Init-substrate rows and
    the demanded Init rows to the summary's Init-provided and probe-count
    measures. The no-import substrate proof cannot quietly omit one of its
    enumerated inputs.

  * A MANIFEST-INSTANCE-ATTRIBUTE JOIN binds the generator-wide kept and
    dropped instance-attribute counts to their declaration rows. The summary
    cannot erase an unregistered attribute or invent a successful registration.

  * A MANIFEST-PRIVATE-NAME JOIN binds the private declaration count and its
    owning-module distribution to `_private.*` declaration rows. Private names
    cannot disappear from the generated surface behind a summary-only claim.

  * A MANIFEST-PRINTER JOIN binds explicit and maximal-explicit printer counts
    to the declaration rows that record those rendering modes. Type-signature
    provenance cannot be overstated by a stale printer summary.

  * A MANIFEST-STRUCTURAL-REFUSAL JOIN binds the structural-refusal summary to
    declaration rows carrying a reason. The structural surface cannot hide a
    failed emission behind an aggregate count without row-level provenance.

  * A MANIFEST-SCHEMA-ROW JOIN requires every consumed declaration and
    Init-substrate row to carry the pinned manifest schema. A trusted summary
    cannot make mixed-epoch data rows appear compatible by itself.

  * A MANIFEST-ROW-KIND JOIN requires every non-summary row to be either a
    declaration or an Init-substrate row. A schema-valid but unknown row cannot
    be silently ignored by the compile-rig joins.

  * A MANIFEST-CLAIM-CLASS JOIN requires the source manifest to retain its
    bounded-model evidence class. A generated coverage artifact cannot silently
    promote its own evidence level before this rig publishes it.

  * A MANIFEST-WITHDRAWAL JOIN binds the summary's emission-withdrawal count to
    declaration rows marked withdrawn. A withdrawn declaration cannot remain
    hidden behind an otherwise successful emission aggregate.

  * A MANIFEST-FORM-TOTALITY JOIN requires every non-Init declaration row to
    use a recognized generator form, and every Init-substrate declaration to
    remain intentionally formless. A form classification cannot disappear
    outside the demanded subset.

  * A MANIFEST-DECLARATION-NAME JOIN requires every declaration name to be
    nonempty and unique before the signature map is built. A duplicate cannot
    overwrite another manifest row merely because neither is emitted.

  * A MANIFEST-SIGNATURE-TOTALITY JOIN requires every non-Init declaration to
    carry a usable Reference signature, while Init-substrate rows remain
    intentionally signature-free. A partial signature map cannot degrade rows
    into name-only evidence.

  * A MANIFEST-ROLE-PARTITION JOIN binds every declaration role to the
    generator's facade-demand, Init-demand, substrate-emission, and quarantine
    measures. Aggregate totals cannot hide a row that crossed role boundaries.

  * A MANIFEST-GLOBAL-PROVIDER JOIN requires every structural-provider edge in
    the full manifest to resolve to, and collectively cover, its class and
    structure declarations. An un-demanded projection cannot cite a phantom or
    self-referential owner.

  * A MANIFEST-TYPE-DEPENDENCY-TOTALITY JOIN requires every typed declaration
    in the full manifest to carry a well-formed, duplicate-free dependency list
    and every Init-substrate row to carry none. Closure-only rows cannot evade
    the provenance shape checks applied to demanded rows.

  * A MANIFEST-EFFECT-TOTALITY JOIN requires every typed declaration's effect
    to belong to the full generator vocabulary, including the task-only
    closure class, while Init-substrate rows carry none. An un-demanded row
    cannot introduce an unclassified semantic effect.

  * A MANIFEST-SAFETY-TOTALITY JOIN requires every typed declaration to carry
    a recognized safe or unsafe classification, while Init-substrate rows carry
    none. Closure-only declarations cannot evade the safety accounting used by
    the demanded slice.

  * A MANIFEST-LEVEL-PARAMETER-TOTALITY JOIN requires every typed declaration
    to carry a well-formed, duplicate-free universe-parameter list whose names
    occur in its signature, while Init-substrate rows carry none. Closure-only
    signatures cannot introduce unbound universe binders.

  * A MANIFEST-TRANSPARENCY-FALLBACK JOIN requires every transparent-form
    refusal to be either an emitted axiom fallback or a withheld transparent
    abbreviation, with a reason in both cases. A failed transparent emission
    cannot masquerade as a successful transparent row.

  * A MANIFEST-STRUCTURAL-FALLBACK JOIN requires every structural refusal to
    be either an axiomized fallback or a withheld structure, with every
    withheld structural row reasoned and no emitted class or structure marked
    refused. Structural failure cannot leak into a successful block claim.

  * A MANIFEST-NONEMISSION-PROVENANCE JOIN requires every withheld declaration
    to carry a nonempty quarantine reason and every emitted declaration to
    carry none. Emission status cannot become a row-level unexplained gap.

  * A MANIFEST-MODULE-PROVENANCE JOIN requires every declaration to name a
    nonempty owner module in the Lean, Init, or Std surface. A row cannot lose
    its source-module provenance or drift outside the native façade boundary.

  * A MANIFEST-PRIVATE-OWNER JOIN requires every `_private.*` declaration name
    to encode its row's reported owner module. A stale module field cannot
    make the private-name provenance map appear consistent by itself.

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
DEMANDED_EFFECTS = frozenset(("pure", "toolchain-monad", "io", "monad-transformer"))
MANIFEST_EFFECTS = DEMANDED_EFFECTS | frozenset(("task",))
DEMANDED_BUCKETS = frozenset(("R-NONE", "R-EFFECT", "R-EXTERN", "R-UNSAFE"))
DEMANDED_SAFETIES = frozenset(("safe", "unsafe"))
DEMANDED_FORMS = frozenset(("axiom", "transparent-abbrev", "class-projection", "class", "structure"))
MANIFEST_INPUTS = frozenset((
    "contracts/facade_resistance.ndjson",
    "contracts/builtin_environment.tsv",
    "contracts/builtin_environment.001.tsv",
    "contracts/builtin_environment.002.tsv",
))
RATCHET_STEPS = {
    "R-NONE": (1, "L2"),
    "R-EFFECT": (2, "L1"),
    "R-UNSAFE": (3, "L0"),
    "R-EXTERN": (4, "L1"),
}


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


def load_demand(path, part, expected_pin, expected_corpus_commit):
    """Curated module -> the toolchain-api constants it actually uses, from the
    elaborated exact-demand artifact (never a lexical scan: `open Lean Meta Elab`
    makes ~95% of real usage unqualified, measured on this same slice)."""
    by_module = defaultdict(set)
    modules = None
    declared_toolchain_api_demand = None
    census_missing = None
    demand_pin = None
    demand_corpus_commit = None
    covered_by_stubs = None
    uncovered = None
    demand_counts = None
    distinct_used_constants = None
    declared_decls = None
    unavailable_bodies = None
    gone = None
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
                declared_toolchain_api_demand = row.get("toolchain_api_demanded")
                census_missing = row.get("census_missing")
                demand_pin = row.get("pin")
                demand_corpus_commit = row.get("corpus_commit")
                covered_by_stubs = row.get("covered_by_stubs")
                uncovered = row.get("uncovered")
                demand_counts = row.get("counts")
                distinct_used_constants = row.get("distinct_used_constants")
                declared_decls = row.get("decls")
                unavailable_bodies = row.get("decl_bodies_unavailable")
                gone = row.get("gone")
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
    if (not isinstance(declared_toolchain_api_demand, int)
            or isinstance(declared_toolchain_api_demand, bool)):
        raise SystemExit(
            f"REFUSE: {path} summary has no integer toolchain_api_demanded count"
        )
    if not isinstance(census_missing, list) or census_missing:
        detail = (", ".join(str(item) for item in census_missing[:8])
                  if isinstance(census_missing, list) else repr(census_missing))
        raise SystemExit(
            "REFUSE: exact-demand census-completeness join found missing census "
            f"rows ({detail})"
        )
    if demand_pin != expected_pin:
        raise SystemExit(
            "REFUSE: exact-demand Reference-pin join disagrees with this rig "
            f"(demand={demand_pin!r}, compiler={expected_pin!r})"
        )
    if demand_corpus_commit != expected_corpus_commit:
        raise SystemExit(
            "REFUSE: exact-demand corpus-pin join disagrees with this rig "
            f"(demand={demand_corpus_commit!r}, "
            f"suite={expected_corpus_commit!r})"
        )
    if (not isinstance(covered_by_stubs, int) or isinstance(covered_by_stubs, bool)
            or not isinstance(uncovered, int) or isinstance(uncovered, bool)
            or covered_by_stubs < 0 or uncovered < 0
            or covered_by_stubs + uncovered != declared_toolchain_api_demand):
        raise SystemExit(
            "REFUSE: exact-demand coverage-split join disagrees with its "
            f"denominator (covered_by_stubs={covered_by_stubs!r}, "
            f"uncovered={uncovered!r}, "
            f"demanded={declared_toolchain_api_demand!r})"
        )
    expected_count_keys = {
        "corpus-internal", "toolchain-library-code", "toolchain-user-facing-data",
        "local",
    }
    if (not isinstance(demand_counts, dict)
            or set(demand_counts) != expected_count_keys
            or any(not isinstance(count, int) or isinstance(count, bool) or count < 0
                   for count in demand_counts.values())
            or not isinstance(distinct_used_constants, int)
            or isinstance(distinct_used_constants, bool)
            or distinct_used_constants < 0
            or sum(demand_counts.values()) + declared_toolchain_api_demand
            != distinct_used_constants):
        raise SystemExit(
            "REFUSE: exact-demand constant-universe join disagrees with the "
            f"Reference summary (counts={demand_counts!r}, "
            f"toolchain_api={declared_toolchain_api_demand!r}, "
            f"distinct_used_constants={distinct_used_constants!r})"
        )
    if (not isinstance(declared_decls, int) or isinstance(declared_decls, bool)
            or declared_decls < 0
            or not isinstance(unavailable_bodies, dict)
            or set(unavailable_bodies) != {"opaque", "thm"}
            or any(not isinstance(count, int) or isinstance(count, bool) or count < 0
                   for count in unavailable_bodies.values())
            or sum(unavailable_bodies.values()) > declared_decls):
        raise SystemExit(
            "REFUSE: exact-demand declaration-body join disagrees with the "
            f"Reference summary (decls={declared_decls!r}, "
            f"decl_bodies_unavailable={unavailable_bodies!r})"
        )
    if not isinstance(gone, list) or gone:
        detail = (", ".join(str(name) for name in gone[:8])
                  if isinstance(gone, list) else repr(gone))
        raise SystemExit(
            "REFUSE: exact-demand gone-symbol join found names absent from the "
            f"pinned Reference ({detail})"
        )
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
    modules_without_demand = sorted(set(modules).difference(by_module))
    if modules_without_demand:
        raise SystemExit(
            "REFUSE: curated-module non-vacuity join found module(s) with no "
            "toolchain-api demand (" + ", ".join(modules_without_demand[:8])
            + ") — a reported module must contribute compile evidence"
        )
    rebuilt_distinct = len({name for names in by_module.values() for name in names})
    if declared_toolchain_api_demand != rebuilt_distinct:
        raise SystemExit(
            "REFUSE: exact-demand summary join disagrees with rebuilt distinct "
            f"toolchain demand (declared={declared_toolchain_api_demand}, "
            f"rebuilt={rebuilt_distinct})"
        )
    module_join = {
        "curated_modules": len(modules),
        "modules_with_demand": len(by_module),
        "toolchain_use_edges": sum(len(names) for names in by_module.values()),
        "toolchain_distinct_symbols": rebuilt_distinct,
        "census_missing": 0,
        "reference_pin": expected_pin,
        "corpus_commit": expected_corpus_commit,
        "covered_by_stubs": covered_by_stubs,
        "uncovered": uncovered,
        "distinct_used_constants": distinct_used_constants,
        "decls": declared_decls,
        "decl_bodies_unavailable": dict(sorted(unavailable_bodies.items())),
        "gone": 0,
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
    level_parameter_mismatches = []
    effect_mismatches = []
    bucket_mismatches = []
    safety_mismatches = []
    instance_mismatches = []
    form_mismatches = []
    transparency_mismatches = []
    roles = Counter()
    emission_join = Counter()
    provider_join = Counter()
    printer_join = Counter()
    type_dependency_join = Counter()
    level_parameter_join = Counter()
    effect_join = Counter()
    bucket_join = Counter()
    safety_join = Counter()
    instance_join = Counter()
    form_join = Counter()
    transparency_join = Counter()
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
            effect = row.get("effect")
            if effect not in DEMANDED_EFFECTS:
                effect_mismatches.append(f"{name}(effect={effect!r})")
                continue
            effect_join[effect] += 1
            bucket = row.get("bucket")
            if bucket not in DEMANDED_BUCKETS:
                bucket_mismatches.append(f"{name}(bucket={bucket!r})")
                continue
            bucket_join[bucket] += 1
            safety = row.get("safety")
            if safety not in DEMANDED_SAFETIES:
                safety_mismatches.append(f"{name}(safety={safety!r})")
                continue
            safety_join[safety] += 1
            instance = row.get("instance")
            registered = row.get("instance_registered")
            drop_reason = row.get("instance_drop_reason")
            if instance is True and registered is True and drop_reason is None:
                instance_join["registered"] += 1
            elif (instance is True and registered is False
                  and isinstance(drop_reason, str) and drop_reason.strip()):
                instance_join["dropped"] += 1
            elif instance is False and registered is False and drop_reason is None:
                instance_join["not_instance"] += 1
            else:
                instance_mismatches.append(
                    f"{name}(instance={instance!r}, registered={registered!r}, "
                    f"drop_reason={drop_reason!r})"
                )
                continue
            form = row.get("form")
            if form not in DEMANDED_FORMS:
                form_mismatches.append(f"{name}(form={form!r})")
                continue
            form_join[form] += 1
            transparency_reason = row.get("transparent_refused_reason")
            if form == "transparent-abbrev" and transparency_reason is None:
                transparency_join["transparent"] += 1
            elif (form == "axiom" and isinstance(transparency_reason, str)
                  and transparency_reason.strip()):
                transparency_join["transparent_refused"] += 1
            elif transparency_reason is None:
                transparency_join["opaque"] += 1
            else:
                transparency_mismatches.append(
                    f"{name}(form={form!r}, transparent_refused_reason="
                    f"{transparency_reason!r})"
                )
                continue
            printer = row.get("printer")
            level_params = row.get("level_params")
            if (printer not in ("pp.fullNames", "pp.explicit", "pp.maxexplicit")
                    or not isinstance(level_params, list)
                    or not all(isinstance(level, str) and level for level in level_params)):
                signature_provenance_mismatches.append(
                    f"{name}(printer={printer!r}, level_params={level_params!r})"
                )
                continue
            signature = row["signature"]
            unused_levels = [
                level for level in level_params
                if not re.search(
                    rf"(?<![A-Za-z0-9_]){re.escape(level)}(?![A-Za-z0-9_])",
                    signature,
                )
            ]
            if unused_levels:
                level_parameter_mismatches.append(
                    f"{name}(unused-levels={unused_levels!r})"
                )
                continue
            printer_join[printer] += 1
            level_parameter_join["rows"] += 1
            level_parameter_join["parameters"] += len(level_params)
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
            or signature_provenance_mismatches or type_dependency_shape_mismatches
            or level_parameter_mismatches or effect_mismatches or bucket_mismatches
            or safety_mismatches or instance_mismatches or form_mismatches
            or transparency_mismatches):
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
        if level_parameter_mismatches:
            details.append("level-parameter=" + ", ".join(
                level_parameter_mismatches[:8]
            ))
        if effect_mismatches:
            details.append("effect=" + ", ".join(effect_mismatches[:8]))
        if bucket_mismatches:
            details.append("bucket=" + ", ".join(bucket_mismatches[:8]))
        if safety_mismatches:
            details.append("safety=" + ", ".join(safety_mismatches[:8]))
        if instance_mismatches:
            details.append("instance=" + ", ".join(instance_mismatches[:8]))
        if form_mismatches:
            details.append("form=" + ", ".join(form_mismatches[:8]))
        if transparency_mismatches:
            details.append("transparency=" + ", ".join(
                transparency_mismatches[:8]
            ))
        raise SystemExit(
            "REFUSE: demanded-row join cannot support a typed disposition ("
            + "; ".join(details) + ")"
        )
    return (dispositions, dict(sorted(roles.items())),
            dict(sorted(emission_join.items())), dict(sorted(provider_join.items())),
            dict(sorted(printer_join.items())), dict(sorted(type_dependency_join.items())),
            dict(sorted(level_parameter_join.items())), dict(sorted(effect_join.items())),
            dict(sorted(bucket_join.items())), dict(sorted(safety_join.items())),
            dict(sorted(instance_join.items())), dict(sorted(form_join.items())),
            dict(sorted(transparency_join.items())))


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


def run_disposition_mutation_control(dispositions, generated, empty):
    """Prove the disposition matrix rejects a one-row classification mutation."""
    candidates = sorted(
        name for name, outcome in dispositions.items() if outcome == "emitted"
    )
    if not candidates:
        raise SystemExit(
            "REFUSE: disposition mutation control found no emitted demand to mutate"
        )
    name = candidates[0]
    mutated = dict(dispositions)
    mutated[name] = "init-substrate"
    try:
        enforce_disposition_matrix(mutated, generated, empty)
    except SystemExit:
        return name
    raise SystemExit(
        f"REFUSE: disposition mutation control relabeled {name}, but the matrix "
        "still accepted the contradictory Init-substrate classification"
    )


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


def join_manifest_demanded_outcomes(manifest_rows, summary):
    """Make the manifest's demanded summary count the exact declaration rows."""
    actual_counts = Counter(
        row.get("demanded_outcome")
        for row in manifest_rows
        if row.get("demanded_outcome") is not None
    )
    unknown = sorted(set(actual_counts).difference(DEMANDED_OUTCOMES))
    actual = {outcome: actual_counts[outcome] for outcome in sorted(DEMANDED_OUTCOMES)}
    declared = summary.get("demanded_outcomes")
    if (unknown
            or declared != actual
            or summary.get("demanded") != sum(actual.values())
            or summary.get("demanded_emitted") != actual["emitted"]
            or summary.get("demanded_init_substrate") != actual["init-substrate"]):
        raise SystemExit(
            "REFUSE: facade manifest demanded-outcome join disagrees with its "
            f"declaration rows (actual={json.dumps(actual, sort_keys=True)}, "
            f"declared={json.dumps(declared, sort_keys=True) if isinstance(declared, dict) else declared!r}, "
            f"unknown={unknown!r})"
        )
    return actual


def join_manifest_input_digests(summary):
    """Bind manifest provenance entries to current repository input bytes."""
    entries = summary.get("inputs")
    if not isinstance(entries, list) or not entries:
        raise SystemExit("REFUSE: facade manifest has no extraction-input digests")
    declared_paths = [entry.get("path") if isinstance(entry, dict) else None for entry in entries]
    if (not all(isinstance(path, str) for path in declared_paths)
            or len(declared_paths) != len(MANIFEST_INPUTS)
            or frozenset(declared_paths) != MANIFEST_INPUTS):
        raise SystemExit(
            "REFUSE: facade manifest input-set join disagrees with the extraction "
            f"contract (declared={declared_paths!r})"
        )
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise SystemExit("REFUSE: facade manifest input entry is not an object")
        path = entry.get("path")
        digest = entry.get("sha256")
        full_path = os.path.abspath(os.path.join(REPO, path)) if isinstance(path, str) else None
        if (not isinstance(path, str)
                or os.path.isabs(path)
                or os.path.commonpath((REPO, full_path)) != REPO
                or not os.path.isfile(full_path)
                or not isinstance(digest, str)
                or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or path in seen):
            raise SystemExit(
                f"REFUSE: facade manifest carries an invalid input provenance row {entry!r}"
            )
        seen.add(path)
        actual = input_digest(full_path)["sha256"]
        if actual != digest:
            raise SystemExit(
                "REFUSE: facade manifest input-digest join drifted for "
                f"{path} (manifest={digest}, actual={actual})"
            )
    return {"verified_inputs": len(entries)}


def join_resistance_demand(manifest_summary, module_join):
    """Cross-bind the resistance cohort to manifest and exact-demand totals."""
    path = os.path.join(REPO, "contracts", "facade_resistance.ndjson")
    summaries = []
    ratchet_steps = []
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(
                    f"REFUSE: {path}:{lineno} is not JSON ({exc})"
                ) from exc
            if row.get("kind") == "summary":
                summaries.append(row)
            elif row.get("kind") == "ratchet-step":
                ratchet_steps.append(row)
    if len(summaries) != 1:
        raise SystemExit(
            f"REFUSE: resistance-demand join needs exactly one summary, found {len(summaries)}"
        )
    summary = summaries[0]
    fields = (
        "joined", "toolchain_api", "exact_demanded", "orphans", "resisting",
        "unresisting", "demanded_names", "union_demanded", "tactic_files",
    )
    values = {field: summary.get(field) for field in fields}
    ratchet_members = {}
    for step in ratchet_steps:
        bucket = step.get("bucket")
        members = step.get("members")
        expected = RATCHET_STEPS.get(bucket)
        if (expected is None
                or not isinstance(members, int)
                or isinstance(members, bool)
                or members < 0
                or bucket in ratchet_members
                or step.get("step") != expected[0]
                or not isinstance(step.get("l_level"), str)
                or not step["l_level"].startswith(expected[1])):
            raise SystemExit(
                f"REFUSE: resistance ratchet-step join found invalid row {step!r}"
            )
        ratchet_members[bucket] = members
    if (summary.get("schema") != "fln-facade-resistance/1"
            or any(not isinstance(value, int) or isinstance(value, bool) or value < 0
                   for value in values.values())
            or values["joined"] != values["toolchain_api"]
            or values["joined"] != manifest_summary.get("demanded")
            or values["exact_demanded"] != module_join["toolchain_distinct_symbols"]
            or values["orphans"] != 0
            or values["resisting"] + values["unresisting"] != values["joined"]
            or values["demanded_names"] < values["exact_demanded"]
            or values["union_demanded"] < values["joined"]
            or values["tactic_files"] == 0
            or set(ratchet_members) != set(RATCHET_STEPS)
            or sum(ratchet_members.values()) != values["joined"]):
        raise SystemExit(
            "REFUSE: resistance-demand cross join disagrees with its cohorts "
            f"(resistance={json.dumps(values, sort_keys=True)}, "
            f"manifest_demanded={manifest_summary.get('demanded')!r}, "
            f"exact_demanded={module_join['toolchain_distinct_symbols']!r})"
        )
    values["ratchet_members"] = sum(ratchet_members.values())
    return values


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
    modules, by_module, module_join, partition_join = load_demand(
        args.demand, part, tag, corpus_commit
    )
    work = os.path.join(os.environ.get("TMPDIR", "/tmp"), f"fln-l8f-compile-{os.getpid()}")
    os.makedirs(work, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
    env["LC_ALL"] = "C"

    sigs = {}
    manifest_rows = []
    manifest_init_substrate = []
    manifest_contract_rows = []
    manifest_summary = None
    with open(args.module_manifest, encoding="utf-8") as fh:
        for line in fh:
            row = json.loads(line)
            if row.get("kind") == "summary":
                if manifest_summary is not None:
                    raise SystemExit(
                        "REFUSE: facade manifest has multiple summaries — its "
                        "contract epoch is ambiguous"
                )
                manifest_summary = row
                continue
            manifest_contract_rows.append(row)
            if row.get("kind") == "init-substrate":
                manifest_init_substrate.append(row)
                continue
            if row.get("kind") != "decl":
                continue
            if not isinstance(row.get("name"), str) or not row["name"]:
                raise SystemExit(
                    "REFUSE: facade manifest declaration has no usable name"
                )
            manifest_rows.append(row)
            if row.get("signature"):
                sigs[row["name"]] = {"signature": row["signature"],
                                       "level_params": row.get("level_params") or [],
                                       "form": row.get("form")}
    if not sigs:
        raise SystemExit("REFUSE: the module manifest carries no signatures — the "
                         "run would silently degrade to a name-only check")
    if (manifest_summary is None
            or manifest_summary.get("schema") != "fln-facade-module/1"
            or manifest_summary.get("pin") != tag):
        raise SystemExit(
            "REFUSE: facade manifest pin join disagrees with this rig "
            f"(schema={None if manifest_summary is None else manifest_summary.get('schema')!r}, "
            f"pin={None if manifest_summary is None else manifest_summary.get('pin')!r}, "
            f"compiler={tag!r})"
        )
    manifest_schema_join = {
        "consumed_rows": len(manifest_contract_rows),
        "matching_schema_rows": sum(
            row.get("schema") == manifest_summary["schema"]
            for row in manifest_contract_rows
        ),
        "schema": manifest_summary["schema"],
    }
    if (manifest_schema_join["consumed_rows"] == 0
            or manifest_schema_join["matching_schema_rows"]
            != manifest_schema_join["consumed_rows"]):
        raise SystemExit(
            "REFUSE: facade manifest schema-row join disagrees with the pinned "
            f"summary ({json.dumps(manifest_schema_join, sort_keys=True)})"
        )
    unexpected_manifest_kinds = sorted({
        row.get("kind") for row in manifest_contract_rows
        if row.get("kind") not in {"decl", "init-substrate"}
    }, key=repr)
    manifest_row_kind_join = {
        "contract_rows": len(manifest_contract_rows),
        "declaration_rows": len(manifest_rows),
        "init_substrate_rows": len(manifest_init_substrate),
        "unexpected_kinds": len(unexpected_manifest_kinds),
    }
    if (manifest_row_kind_join["contract_rows"] == 0
            or manifest_row_kind_join["declaration_rows"]
            + manifest_row_kind_join["init_substrate_rows"]
            != manifest_row_kind_join["contract_rows"]
            or manifest_row_kind_join["unexpected_kinds"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest row-kind join failed "
            f"({json.dumps(manifest_row_kind_join, sort_keys=True)}, "
            f"unexpected={unexpected_manifest_kinds!r})"
        )
    manifest_claim_class_join = {
        "manifest_claim_class": manifest_summary.get("claim_class"),
        "rig_claim_class": "bounded_model",
    }
    if (manifest_claim_class_join["manifest_claim_class"]
            != manifest_claim_class_join["rig_claim_class"]):
        raise SystemExit(
            "REFUSE: facade manifest claim-class join disagrees with this rig "
            f"({json.dumps(manifest_claim_class_join, sort_keys=True)})"
        )
    manifest_withdrawal_join = {
        "withdrawn_rows": sum(
            row.get("emission_withdrawn") is True for row in manifest_rows
        ),
        "summary_withdrawn": manifest_summary.get("emission_withdrawn"),
    }
    if (not isinstance(manifest_withdrawal_join["summary_withdrawn"], int)
            or isinstance(manifest_withdrawal_join["summary_withdrawn"], bool)
            or manifest_withdrawal_join["summary_withdrawn"] < 0
            or manifest_withdrawal_join["withdrawn_rows"]
            != manifest_withdrawal_join["summary_withdrawn"]):
        raise SystemExit(
            "REFUSE: facade manifest withdrawal join disagrees with its rows "
            f"({json.dumps(manifest_withdrawal_join, sort_keys=True)})"
        )
    quarantine_summary_join = {
        "quarantine_rows": sum(
            row.get("emitted") is False and row.get("role") == "substrate"
            for row in manifest_rows
        ),
        "summary_quarantined": manifest_summary.get("quarantined"),
    }
    if (not isinstance(quarantine_summary_join["summary_quarantined"], int)
            or isinstance(quarantine_summary_join["summary_quarantined"], bool)
            or quarantine_summary_join["summary_quarantined"] < 0
            or quarantine_summary_join["quarantine_rows"]
            != quarantine_summary_join["summary_quarantined"]):
        raise SystemExit(
            "REFUSE: facade manifest quarantine-summary join disagrees with its rows "
            f"({json.dumps(quarantine_summary_join, sort_keys=True)})"
        )
    coverage_summary_join = {
        "emitted_coverage": manifest_summary.get("demanded_emitted"),
        "verified_coverage": manifest_summary.get("facade_demand"),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in coverage_summary_join.values())
            or coverage_summary_join["emitted_coverage"]
            != coverage_summary_join["verified_coverage"]):
        raise SystemExit(
            "REFUSE: facade manifest coverage-summary join diverges "
            f"({json.dumps(coverage_summary_join, sort_keys=True)})"
        )
    structural_field_set_join = {
        "summary_structural_declarations": manifest_summary.get(
            "structural_declarations"
        ),
        "pinned_structural_declarations": 175,
    }
    if (structural_field_set_join["summary_structural_declarations"]
            != structural_field_set_join["pinned_structural_declarations"]):
        raise SystemExit(
            "REFUSE: facade manifest structural field-set pin diverges "
            f"({json.dumps(structural_field_set_join, sort_keys=True)})"
        )
    projection_type_pin_join = {
        "summary_projection_types_checked": manifest_summary.get(
            "projection_types_checked"
        ),
        "pinned_projection_types_checked": 807,
    }
    if (projection_type_pin_join["summary_projection_types_checked"]
            != projection_type_pin_join["pinned_projection_types_checked"]):
        raise SystemExit(
            "REFUSE: facade manifest projection-type pin diverges "
            f"({json.dumps(projection_type_pin_join, sort_keys=True)})"
        )
    type_roundtrip_pin_join = {
        "summary_type_roundtrip_checked": manifest_summary.get(
            "type_roundtrip_checked"
        ),
        "pinned_type_roundtrip_checked": 736,
    }
    if (type_roundtrip_pin_join["summary_type_roundtrip_checked"]
            != type_roundtrip_pin_join["pinned_type_roundtrip_checked"]):
        raise SystemExit(
            "REFUSE: facade manifest type-round-trip pin diverges "
            f"({json.dumps(type_roundtrip_pin_join, sort_keys=True)})"
        )
    transparent_values_pin_join = {
        "summary_transparent_values_checked": manifest_summary.get(
            "transparent_values_checked"
        ),
        "pinned_transparent_values_checked": 667,
    }
    if (transparent_values_pin_join["summary_transparent_values_checked"]
            != transparent_values_pin_join["pinned_transparent_values_checked"]):
        raise SystemExit(
            "REFUSE: facade manifest transparent-values pin diverges "
            f"({json.dumps(transparent_values_pin_join, sort_keys=True)})"
        )
    init_substrate_pin_join = {
        "summary_init_substrate_checked": manifest_summary.get("init_substrate_checked"),
        "pinned_init_substrate_checked": 224,
    }
    if (init_substrate_pin_join["summary_init_substrate_checked"]
            != init_substrate_pin_join["pinned_init_substrate_checked"]):
        raise SystemExit(
            "REFUSE: facade manifest Init-substrate pin diverges "
            f"({json.dumps(init_substrate_pin_join, sort_keys=True)})"
        )
    init_provided_pin_join = {
        "summary_init_provided": manifest_summary.get("init_provided"),
        "pinned_init_provided": 109,
    }
    if (init_provided_pin_join["summary_init_provided"]
            != init_provided_pin_join["pinned_init_provided"]):
        raise SystemExit(
            "REFUSE: facade manifest Init-provided pin diverges "
            f"({json.dumps(init_provided_pin_join, sort_keys=True)})"
        )
    pin_presence_pin_join = {
        "summary_pin_presence_checked": manifest_summary.get("pin_presence_checked"),
        "pinned_pin_presence_checked": 1543,
    }
    if (pin_presence_pin_join["summary_pin_presence_checked"]
            != pin_presence_pin_join["pinned_pin_presence_checked"]):
        raise SystemExit(
            "REFUSE: facade manifest pin-presence pin diverges "
            f"({json.dumps(pin_presence_pin_join, sort_keys=True)})"
        )
    private_name_rows_pin_join = {
        "summary_private_name_rows": manifest_summary.get("private_name_rows"),
        "pinned_private_name_rows": 37,
    }
    if (private_name_rows_pin_join["summary_private_name_rows"]
            != private_name_rows_pin_join["pinned_private_name_rows"]):
        raise SystemExit(
            "REFUSE: facade manifest private-name-row pin diverges "
            f"({json.dumps(private_name_rows_pin_join, sort_keys=True)})"
        )
    instance_attrs_kept_pin_join = {
        "summary_instance_attrs_kept": manifest_summary.get("instance_attrs_kept"),
        "pinned_instance_attrs_kept": 94,
    }
    if (instance_attrs_kept_pin_join["summary_instance_attrs_kept"]
            != instance_attrs_kept_pin_join["pinned_instance_attrs_kept"]):
        raise SystemExit(
            "REFUSE: facade manifest kept-instance-attribute pin diverges "
            f"({json.dumps(instance_attrs_kept_pin_join, sort_keys=True)})"
        )
    instance_attrs_dropped_pin_join = {
        "summary_instance_attrs_dropped": manifest_summary.get("instance_attrs_dropped"),
        "pinned_instance_attrs_dropped": 1,
    }
    if (instance_attrs_dropped_pin_join["summary_instance_attrs_dropped"]
            != instance_attrs_dropped_pin_join["pinned_instance_attrs_dropped"]):
        raise SystemExit(
            "REFUSE: facade manifest dropped-instance-attribute pin diverges "
            f"({json.dumps(instance_attrs_dropped_pin_join, sort_keys=True)})"
        )
    substrate_emitted_pin_join = {
        "summary_substrate_emitted": manifest_summary.get("substrate_emitted"),
        "pinned_substrate_emitted": 1563,
    }
    if (substrate_emitted_pin_join["summary_substrate_emitted"]
            != substrate_emitted_pin_join["pinned_substrate_emitted"]):
        raise SystemExit(
            "REFUSE: facade manifest substrate-emitted pin diverges "
            f"({json.dumps(substrate_emitted_pin_join, sort_keys=True)})"
        )
    declarations_emitted_pin_join = {
        "summary_declarations_emitted": manifest_summary.get("declarations_emitted"),
        "pinned_declarations_emitted": 2005,
    }
    if (declarations_emitted_pin_join["summary_declarations_emitted"]
            != declarations_emitted_pin_join["pinned_declarations_emitted"]):
        raise SystemExit(
            "REFUSE: facade manifest declarations-emitted pin diverges "
            f"({json.dumps(declarations_emitted_pin_join, sort_keys=True)})"
        )
    emission_verified_pin_join = {
        "summary_emission_verified": manifest_summary.get("emission_verified"),
        "pinned_emission_verified": 2005,
    }
    if (emission_verified_pin_join["summary_emission_verified"]
            != emission_verified_pin_join["pinned_emission_verified"]):
        raise SystemExit(
            "REFUSE: facade manifest emission-verified pin diverges "
            f"({json.dumps(emission_verified_pin_join, sort_keys=True)})"
        )
    uncensused_emitted_pin_join = {
        "summary_uncensused_emitted": manifest_summary.get("uncensused_emitted"),
        "pinned_uncensused_emitted": 0,
    }
    if (uncensused_emitted_pin_join["summary_uncensused_emitted"]
            != uncensused_emitted_pin_join["pinned_uncensused_emitted"]):
        raise SystemExit(
            "REFUSE: facade manifest uncensused-emitted pin diverges "
            f"({json.dumps(uncensused_emitted_pin_join, sort_keys=True)})"
        )
    uncensused_closure_pin_join = {
        "summary_uncensused_closure": manifest_summary.get("uncensused_closure"),
        "pinned_uncensused_closure": 0,
    }
    if (uncensused_closure_pin_join["summary_uncensused_closure"]
            != uncensused_closure_pin_join["pinned_uncensused_closure"]):
        raise SystemExit(
            "REFUSE: facade manifest uncensused-closure pin diverges "
            f"({json.dumps(uncensused_closure_pin_join, sort_keys=True)})"
        )
    bare_names_probed_pin_join = {
        "summary_bare_names_probed": manifest_summary.get("bare_names_probed"),
        "pinned_bare_names_probed": 1416,
    }
    if (bare_names_probed_pin_join["summary_bare_names_probed"]
            != bare_names_probed_pin_join["pinned_bare_names_probed"]):
        raise SystemExit(
            "REFUSE: facade manifest bare-name probe pin diverges "
            f"({json.dumps(bare_names_probed_pin_join, sort_keys=True)})"
        )
    class_provided_projections_pin_join = {
        "summary_class_provided_projections": manifest_summary.get(
            "class_provided_projections"
        ),
        "pinned_class_provided_projections": 5541,
    }
    if (class_provided_projections_pin_join["summary_class_provided_projections"]
            != class_provided_projections_pin_join["pinned_class_provided_projections"]):
        raise SystemExit(
            "REFUSE: facade manifest class-projection pin diverges "
            f"({json.dumps(class_provided_projections_pin_join, sort_keys=True)})"
        )
    inductive_declarations_pin_join = {
        "summary_inductive_declarations": manifest_summary.get("inductive_declarations"),
        "pinned_inductive_declarations": 49,
    }
    if (inductive_declarations_pin_join["summary_inductive_declarations"]
            != inductive_declarations_pin_join["pinned_inductive_declarations"]):
        raise SystemExit(
            "REFUSE: facade manifest inductive-declaration pin diverges "
            f"({json.dumps(inductive_declarations_pin_join, sort_keys=True)})"
        )
    manifest_name_counts = Counter(row["name"] for row in manifest_rows)
    duplicate_manifest_names = sorted(
        name for name, count in manifest_name_counts.items() if count != 1
    )
    manifest_name_join = {
        "declaration_rows": len(manifest_rows),
        "distinct_declaration_names": len(manifest_name_counts),
        "duplicate_names": len(duplicate_manifest_names),
    }
    if (manifest_name_join["declaration_rows"] == 0
            or manifest_name_join["distinct_declaration_names"]
            != manifest_name_join["declaration_rows"]
            or manifest_name_join["duplicate_names"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest declaration-name join failed "
            f"({json.dumps(manifest_name_join, sort_keys=True)}, "
            f"duplicates={duplicate_manifest_names[:8]!r})"
        )
    manifest_signature_join = {
        "non_init_rows": sum(
            row.get("role") != "init-substrate" for row in manifest_rows
        ),
        "usable_non_init_signatures": sum(
            bool(row.get("role") != "init-substrate"
                 and isinstance(row.get("signature"), str)
                 and row["signature"].strip())
            for row in manifest_rows
        ),
        "init_rows": sum(
            row.get("role") == "init-substrate" for row in manifest_rows
        ),
        "signature_free_init_rows": sum(
            row.get("role") == "init-substrate" and not row.get("signature")
            for row in manifest_rows
        ),
    }
    if (manifest_signature_join["non_init_rows"] == 0
            or manifest_signature_join["usable_non_init_signatures"]
            != manifest_signature_join["non_init_rows"]
            or manifest_signature_join["signature_free_init_rows"]
            != manifest_signature_join["init_rows"]):
        raise SystemExit(
            "REFUSE: facade manifest signature-totality join failed "
            f"({json.dumps(manifest_signature_join, sort_keys=True)})"
        )
    manifest_role_counts = Counter(row.get("role") for row in manifest_rows)
    manifest_role_join = {
        "demanded_rows": manifest_role_counts["demanded"],
        "init_substrate_rows": manifest_role_counts["init-substrate"],
        "substrate_rows": manifest_role_counts["substrate"],
        "unknown_role_rows": sum(
            count for role, count in manifest_role_counts.items()
            if role not in {"demanded", "init-substrate", "substrate"}
        ),
        "summary_facade_demand": manifest_summary.get("facade_demand"),
        "summary_demanded_init_substrate": manifest_summary.get(
            "demanded_init_substrate"
        ),
        "summary_substrate_emitted": manifest_summary.get("substrate_emitted"),
        "summary_quarantined": manifest_summary.get("quarantined"),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in (manifest_role_join["summary_facade_demand"],
                          manifest_role_join["summary_demanded_init_substrate"],
                          manifest_role_join["summary_substrate_emitted"],
                          manifest_role_join["summary_quarantined"]))
            or manifest_role_join["unknown_role_rows"] != 0
            or manifest_role_join["demanded_rows"]
            != manifest_role_join["summary_facade_demand"]
            or manifest_role_join["init_substrate_rows"]
            != manifest_role_join["summary_demanded_init_substrate"]
            or manifest_role_join["substrate_rows"]
            != manifest_role_join["summary_substrate_emitted"]
            + manifest_role_join["summary_quarantined"]):
        raise SystemExit(
            "REFUSE: facade manifest role-partition join disagrees with its "
            f"summary ({json.dumps(manifest_role_join, sort_keys=True)})"
        )
    manifest_names = set(manifest_name_counts)
    structural_names = {
        row["name"] for row in manifest_rows
        if row.get("form") in {"class", "structure"}
    }
    provider_edges = [
        (row["name"], row.get("provided_by")) for row in manifest_rows
        if row.get("provided_by") is not None
    ]
    provider_names = {provider for _, provider in provider_edges}
    unresolved_providers = sorted(provider_names - manifest_names)
    self_providers = sorted(name for name, provider in provider_edges if name == provider)
    manifest_provider_join = {
        "provider_edges": len(provider_edges),
        "provider_owners": len(provider_names),
        "structural_declarations": len(structural_names),
        "unresolved_owners": len(unresolved_providers),
        "self_references": len(self_providers),
        "owners_without_dependents": len(structural_names - provider_names),
        "nonstructural_owners": len(provider_names - structural_names),
    }
    if (manifest_provider_join["provider_edges"] == 0
            or manifest_provider_join["unresolved_owners"] != 0
            or manifest_provider_join["self_references"] != 0
            or manifest_provider_join["owners_without_dependents"] != 0
            or manifest_provider_join["nonstructural_owners"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest global-provider join failed "
            f"({json.dumps(manifest_provider_join, sort_keys=True)}, "
            f"unresolved={unresolved_providers[:8]!r}, self={self_providers[:8]!r})"
        )
    malformed_type_dependencies = []
    duplicate_type_dependencies = []
    type_dependency_edges = 0
    typed_dependency_rows = 0
    for row in manifest_rows:
        dependencies = row.get("type_deps")
        if row.get("role") == "init-substrate":
            if dependencies not in (None, []):
                malformed_type_dependencies.append(row["name"])
            continue
        if (not isinstance(dependencies, list)
                or not all(isinstance(dependency, str) and dependency
                           for dependency in dependencies)):
            malformed_type_dependencies.append(row["name"])
            continue
        type_dependency_edges += len(dependencies)
        if dependencies:
            typed_dependency_rows += 1
        if len(dependencies) != len(set(dependencies)):
            duplicate_type_dependencies.append(row["name"])
    manifest_type_dependency_join = {
        "typed_rows": manifest_signature_join["non_init_rows"],
        "typed_dependency_rows": typed_dependency_rows,
        "type_dependency_edges": type_dependency_edges,
        "init_rows": manifest_signature_join["init_rows"],
        "malformed_rows": len(malformed_type_dependencies),
        "duplicate_dependency_rows": len(duplicate_type_dependencies),
    }
    if (manifest_type_dependency_join["typed_rows"] == 0
            or manifest_type_dependency_join["malformed_rows"] != 0
            or manifest_type_dependency_join["duplicate_dependency_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest type-dependency-totality join failed "
            f"({json.dumps(manifest_type_dependency_join, sort_keys=True)}, "
            f"malformed={malformed_type_dependencies[:8]!r}, "
            f"duplicates={duplicate_type_dependencies[:8]!r})"
        )
    unknown_effect_rows = []
    init_effect_rows = []
    manifest_effect_counts = Counter()
    for row in manifest_rows:
        effect = row.get("effect")
        if row.get("role") == "init-substrate":
            if effect is not None:
                init_effect_rows.append(row["name"])
            continue
        if effect not in MANIFEST_EFFECTS:
            unknown_effect_rows.append(row["name"])
            continue
        manifest_effect_counts[effect] += 1
    manifest_effect_join = {
        "typed_rows": manifest_signature_join["non_init_rows"],
        "recognized_effect_rows": sum(manifest_effect_counts.values()),
        "effects": dict(sorted(manifest_effect_counts.items())),
        "init_rows": manifest_signature_join["init_rows"],
        "init_rows_with_effect": len(init_effect_rows),
        "unknown_effect_rows": len(unknown_effect_rows),
    }
    if (manifest_effect_join["typed_rows"] == 0
            or manifest_effect_join["recognized_effect_rows"]
            != manifest_effect_join["typed_rows"]
            or manifest_effect_join["init_rows_with_effect"] != 0
            or manifest_effect_join["unknown_effect_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest effect-totality join failed "
            f"({json.dumps(manifest_effect_join, sort_keys=True)}, "
            f"unknown={unknown_effect_rows[:8]!r}, init={init_effect_rows[:8]!r})"
        )
    unknown_safety_rows = []
    init_safety_rows = []
    manifest_safety_counts = Counter()
    for row in manifest_rows:
        safety = row.get("safety")
        if row.get("role") == "init-substrate":
            if safety is not None:
                init_safety_rows.append(row["name"])
            continue
        if safety not in DEMANDED_SAFETIES:
            unknown_safety_rows.append(row["name"])
            continue
        manifest_safety_counts[safety] += 1
    manifest_safety_join = {
        "typed_rows": manifest_signature_join["non_init_rows"],
        "recognized_safety_rows": sum(manifest_safety_counts.values()),
        "safeties": dict(sorted(manifest_safety_counts.items())),
        "init_rows": manifest_signature_join["init_rows"],
        "init_rows_with_safety": len(init_safety_rows),
        "unknown_safety_rows": len(unknown_safety_rows),
    }
    if (manifest_safety_join["typed_rows"] == 0
            or manifest_safety_join["recognized_safety_rows"]
            != manifest_safety_join["typed_rows"]
            or manifest_safety_join["init_rows_with_safety"] != 0
            or manifest_safety_join["unknown_safety_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest safety-totality join failed "
            f"({json.dumps(manifest_safety_join, sort_keys=True)}, "
            f"unknown={unknown_safety_rows[:8]!r}, init={init_safety_rows[:8]!r})"
        )
    malformed_level_parameter_rows = []
    duplicate_level_parameter_rows = []
    unbound_level_parameter_rows = []
    level_parameter_count = 0
    parameterized_rows = 0
    for row in manifest_rows:
        parameters = row.get("level_params")
        if row.get("role") == "init-substrate":
            if parameters not in (None, []):
                malformed_level_parameter_rows.append(row["name"])
            continue
        if (not isinstance(parameters, list)
                or not all(isinstance(parameter, str) and parameter
                           for parameter in parameters)):
            malformed_level_parameter_rows.append(row["name"])
            continue
        level_parameter_count += len(parameters)
        if parameters:
            parameterized_rows += 1
        if len(parameters) != len(set(parameters)):
            duplicate_level_parameter_rows.append(row["name"])
        signature = row["signature"]
        if any(parameter not in signature for parameter in parameters):
            unbound_level_parameter_rows.append(row["name"])
    manifest_level_parameter_join = {
        "typed_rows": manifest_signature_join["non_init_rows"],
        "parameterized_rows": parameterized_rows,
        "level_parameters": level_parameter_count,
        "init_rows": manifest_signature_join["init_rows"],
        "malformed_rows": len(malformed_level_parameter_rows),
        "duplicate_parameter_rows": len(duplicate_level_parameter_rows),
        "unbound_parameter_rows": len(unbound_level_parameter_rows),
    }
    if (manifest_level_parameter_join["typed_rows"] == 0
            or manifest_level_parameter_join["malformed_rows"] != 0
            or manifest_level_parameter_join["duplicate_parameter_rows"] != 0
            or manifest_level_parameter_join["unbound_parameter_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest level-parameter-totality join failed "
            f"({json.dumps(manifest_level_parameter_join, sort_keys=True)}, "
            f"malformed={malformed_level_parameter_rows[:8]!r}, "
            f"duplicates={duplicate_level_parameter_rows[:8]!r}, "
            f"unbound={unbound_level_parameter_rows[:8]!r})"
        )
    transparent_fallback_rows = [
        row for row in manifest_rows
        if isinstance(row.get("transparent_refused_reason"), str)
        and row["transparent_refused_reason"].strip()
    ]
    emitted_axiom_fallbacks = [
        row for row in transparent_fallback_rows
        if row.get("form") == "axiom" and row.get("emitted") is True
    ]
    withheld_transparents = [
        row for row in transparent_fallback_rows
        if row.get("form") == "transparent-abbrev" and row.get("emitted") is False
    ]
    malformed_transparent_fallbacks = sorted(
        row["name"] for row in transparent_fallback_rows
        if row not in emitted_axiom_fallbacks and row not in withheld_transparents
    )
    unexplained_withheld_transparents = sorted(
        row["name"] for row in manifest_rows
        if row.get("form") == "transparent-abbrev"
        and row.get("emitted") is False
        and row not in withheld_transparents
    )
    refused_emitted_transparents = sorted(
        row["name"] for row in manifest_rows
        if row.get("form") == "transparent-abbrev"
        and row.get("emitted") is True
        and isinstance(row.get("transparent_refused_reason"), str)
        and row["transparent_refused_reason"].strip()
    )
    manifest_transparency_fallback_join = {
        "refusal_rows": len(transparent_fallback_rows),
        "emitted_axiom_fallbacks": len(emitted_axiom_fallbacks),
        "withheld_transparents": len(withheld_transparents),
        "malformed_fallback_rows": len(malformed_transparent_fallbacks),
        "unexplained_withheld_transparents": len(unexplained_withheld_transparents),
        "refused_emitted_transparents": len(refused_emitted_transparents),
    }
    if (manifest_transparency_fallback_join["refusal_rows"] == 0
            or manifest_transparency_fallback_join["emitted_axiom_fallbacks"]
            + manifest_transparency_fallback_join["withheld_transparents"]
            != manifest_transparency_fallback_join["refusal_rows"]
            or manifest_transparency_fallback_join["malformed_fallback_rows"] != 0
            or manifest_transparency_fallback_join["unexplained_withheld_transparents"] != 0
            or manifest_transparency_fallback_join["refused_emitted_transparents"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest transparency-fallback join failed "
            f"({json.dumps(manifest_transparency_fallback_join, sort_keys=True)}, "
            f"malformed={malformed_transparent_fallbacks[:8]!r}, "
            f"unexplained={unexplained_withheld_transparents[:8]!r}, "
            f"refused_emitted={refused_emitted_transparents[:8]!r})"
        )
    structural_fallback_rows = [
        row for row in manifest_rows
        if isinstance(row.get("structural_refused_reason"), str)
        and row["structural_refused_reason"].strip()
    ]
    axiomized_structural_fallbacks = [
        row for row in structural_fallback_rows if row.get("form") == "axiom"
    ]
    withheld_structures = [
        row for row in structural_fallback_rows
        if row.get("form") == "structure" and row.get("emitted") is False
    ]
    malformed_structural_fallbacks = sorted(
        row["name"] for row in structural_fallback_rows
        if row not in axiomized_structural_fallbacks and row not in withheld_structures
    )
    unexplained_withheld_structures = sorted(
        row["name"] for row in manifest_rows
        if row.get("form") in {"class", "structure"}
        and row.get("emitted") is False
        and row not in withheld_structures
    )
    refused_emitted_structurals = sorted(
        row["name"] for row in manifest_rows
        if row.get("form") in {"class", "structure"}
        and row.get("emitted") is True
        and isinstance(row.get("structural_refused_reason"), str)
        and row["structural_refused_reason"].strip()
    )
    manifest_structural_fallback_join = {
        "refusal_rows": len(structural_fallback_rows),
        "axiomized_fallbacks": len(axiomized_structural_fallbacks),
        "withheld_structures": len(withheld_structures),
        "malformed_fallback_rows": len(malformed_structural_fallbacks),
        "unexplained_withheld_structures": len(unexplained_withheld_structures),
        "refused_emitted_structurals": len(refused_emitted_structurals),
    }
    if (manifest_structural_fallback_join["refusal_rows"] == 0
            or manifest_structural_fallback_join["axiomized_fallbacks"]
            + manifest_structural_fallback_join["withheld_structures"]
            != manifest_structural_fallback_join["refusal_rows"]
            or manifest_structural_fallback_join["malformed_fallback_rows"] != 0
            or manifest_structural_fallback_join["unexplained_withheld_structures"] != 0
            or manifest_structural_fallback_join["refused_emitted_structurals"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest structural-fallback join failed "
            f"({json.dumps(manifest_structural_fallback_join, sort_keys=True)}, "
            f"malformed={malformed_structural_fallbacks[:8]!r}, "
            f"unexplained={unexplained_withheld_structures[:8]!r}, "
            f"refused_emitted={refused_emitted_structurals[:8]!r})"
        )
    invalid_emission_state_rows = []
    unexplained_withheld_rows = []
    reasoned_emitted_rows = []
    for row in manifest_rows:
        emitted = row.get("emitted")
        reason = row.get("quarantine_reason")
        reasoned = isinstance(reason, str) and bool(reason.strip())
        if emitted is not True and emitted is not False:
            invalid_emission_state_rows.append(row["name"])
        elif emitted is False and not reasoned:
            unexplained_withheld_rows.append(row["name"])
        elif emitted is True and reasoned:
            reasoned_emitted_rows.append(row["name"])
    manifest_nonemission_provenance_join = {
        "declaration_rows": len(manifest_rows),
        "withheld_rows": sum(row.get("emitted") is False for row in manifest_rows),
        "reasoned_withheld_rows": sum(
            row.get("emitted") is False
            and isinstance(row.get("quarantine_reason"), str)
            and bool(row["quarantine_reason"].strip())
            for row in manifest_rows
        ),
        "invalid_emission_state_rows": len(invalid_emission_state_rows),
        "unexplained_withheld_rows": len(unexplained_withheld_rows),
        "reasoned_emitted_rows": len(reasoned_emitted_rows),
    }
    if (manifest_nonemission_provenance_join["declaration_rows"] == 0
            or manifest_nonemission_provenance_join["withheld_rows"] == 0
            or manifest_nonemission_provenance_join["reasoned_withheld_rows"]
            != manifest_nonemission_provenance_join["withheld_rows"]
            or manifest_nonemission_provenance_join["invalid_emission_state_rows"] != 0
            or manifest_nonemission_provenance_join["unexplained_withheld_rows"] != 0
            or manifest_nonemission_provenance_join["reasoned_emitted_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest nonemission-provenance join failed "
            f"({json.dumps(manifest_nonemission_provenance_join, sort_keys=True)}, "
            f"invalid={invalid_emission_state_rows[:8]!r}, "
            f"unexplained={unexplained_withheld_rows[:8]!r}, "
            f"reasoned_emitted={reasoned_emitted_rows[:8]!r})"
        )
    invalid_module_rows = []
    manifest_module_counts = Counter()
    for row in manifest_rows:
        module = row.get("module")
        if not isinstance(module, str) or not module:
            invalid_module_rows.append(row["name"])
            continue
        manifest_module_counts[module] += 1
    manifest_module_namespaces = Counter(
        module.split(".", 1)[0] for module in manifest_module_counts
    )
    manifest_module_join = {
        "declaration_rows": len(manifest_rows),
        "module_owners": len(manifest_module_counts),
        "namespaces": dict(sorted(manifest_module_namespaces.items())),
        "invalid_module_rows": len(invalid_module_rows),
        "out_of_surface_namespaces": sum(
            count for namespace, count in manifest_module_namespaces.items()
            if namespace not in {"Lean", "Init", "Std"}
        ),
    }
    if (manifest_module_join["declaration_rows"] == 0
            or manifest_module_join["module_owners"] == 0
            or manifest_module_join["invalid_module_rows"] != 0
            or manifest_module_join["out_of_surface_namespaces"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest module-provenance join failed "
            f"({json.dumps(manifest_module_join, sort_keys=True)}, "
            f"invalid={invalid_module_rows[:8]!r})"
        )
    private_owner_rows = [
        row for row in manifest_rows
        if row["name"].startswith("_private.")
    ]
    private_owner_mismatches = sorted(
        row["name"] for row in private_owner_rows
        if not row["name"].startswith(f"_private.{row['module']}.")
    )
    manifest_private_owner_join = {
        "private_rows": len(private_owner_rows),
        "owner_aligned_rows": len(private_owner_rows) - len(private_owner_mismatches),
        "owner_mismatches": len(private_owner_mismatches),
    }
    if (manifest_private_owner_join["private_rows"] == 0
            or manifest_private_owner_join["owner_aligned_rows"]
            != manifest_private_owner_join["private_rows"]
            or manifest_private_owner_join["owner_mismatches"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest private-owner join failed "
            f"({json.dumps(manifest_private_owner_join, sort_keys=True)}, "
            f"mismatches={private_owner_mismatches[:8]!r})"
        )
    malformed_forms = sorted(
        row["name"] for row in manifest_rows
        if (row.get("role") == "init-substrate" and row.get("form") is not None)
        or (row.get("role") != "init-substrate"
            and row.get("form") not in DEMANDED_FORMS)
    )
    manifest_form_join = {
        "declaration_rows": len(manifest_rows),
        "recognized_form_rows": sum(
            row.get("form") in DEMANDED_FORMS for row in manifest_rows
        ),
        "init_formless_rows": sum(
            row.get("role") == "init-substrate" and row.get("form") is None
            for row in manifest_rows
        ),
        "malformed_rows": len(malformed_forms),
    }
    if (manifest_form_join["declaration_rows"] == 0
            or manifest_form_join["recognized_form_rows"]
            + manifest_form_join["init_formless_rows"]
            != manifest_form_join["declaration_rows"]
            or manifest_form_join["malformed_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest form-totality join failed "
            f"({json.dumps(manifest_form_join, sort_keys=True)}, "
            f"malformed={malformed_forms[:8]!r})"
        )
    totality = {
        "uncensused_closure": manifest_summary.get("uncensused_closure"),
        "uncensused_emitted": manifest_summary.get("uncensused_emitted"),
        "imports_reference": manifest_summary.get("imports_reference"),
    }
    if (totality["uncensused_closure"] != 0
            or totality["uncensused_emitted"] != 0
            or totality["imports_reference"] is not False):
        raise SystemExit(
            "REFUSE: facade manifest totality join failed "
            f"({json.dumps(totality, sort_keys=True)})"
        )
    emission_verification = {
        "declarations_emitted": manifest_summary.get("declarations_emitted"),
        "emission_verified": manifest_summary.get("emission_verified"),
        "emission_withdrawn": manifest_summary.get("emission_withdrawn"),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in emission_verification.values())
            or emission_verification["emission_verified"]
            != emission_verification["declarations_emitted"]
            or emission_verification["emission_withdrawn"]
            > emission_verification["declarations_emitted"]):
        raise SystemExit(
            "REFUSE: facade manifest emission-verification join failed "
            f"({json.dumps(emission_verification, sort_keys=True)})"
        )
    emitted_row_join = {
        "emitted_declaration_rows": sum(
            row.get("emitted") is True for row in manifest_rows
        ),
    }
    if (emitted_row_join["emitted_declaration_rows"]
            != emission_verification["declarations_emitted"]):
        raise SystemExit(
            "REFUSE: facade manifest emitted-row join disagrees with its "
            "summary "
            f"(rows={emitted_row_join['emitted_declaration_rows']}, "
            f"summary={emission_verification['declarations_emitted']})"
        )
    emitted_names = {
        row.get("name") for row in manifest_rows if row.get("emitted") is True
    }
    emitted_name_join = {
        "emitted_distinct_names": len(emitted_names),
        "summary_emitted_distinct": manifest_summary.get(
            "declarations_emitted_distinct"
        ),
    }
    if (not isinstance(emitted_name_join["summary_emitted_distinct"], int)
            or isinstance(emitted_name_join["summary_emitted_distinct"], bool)
            or emitted_name_join["summary_emitted_distinct"] < 0
            or emitted_name_join["emitted_distinct_names"]
            != emitted_row_join["emitted_declaration_rows"]
            or emitted_name_join["summary_emitted_distinct"]
            != emitted_name_join["emitted_distinct_names"]):
        raise SystemExit(
            "REFUSE: facade manifest emitted-name join failed "
            f"({json.dumps(emitted_name_join, sort_keys=True)}, "
            f"rows={emitted_row_join['emitted_declaration_rows']})"
        )
    transparency_join = {
        "transparent_rows": sum(
            row.get("form") == "transparent-abbrev" for row in manifest_rows
        ),
        "summary_transparent_declarations": manifest_summary.get(
            "transparent_declarations"
        ),
    }
    if (not isinstance(transparency_join["summary_transparent_declarations"], int)
            or isinstance(transparency_join["summary_transparent_declarations"], bool)
            or transparency_join["summary_transparent_declarations"] < 0
            or transparency_join["transparent_rows"]
            != transparency_join["summary_transparent_declarations"]):
        raise SystemExit(
            "REFUSE: facade manifest transparency join disagrees with its "
            f"declaration rows ({json.dumps(transparency_join, sort_keys=True)})"
        )
    structural_join = {
        "structure_rows": sum(row.get("form") == "structure" for row in manifest_rows),
        "class_rows": sum(row.get("form") == "class" for row in manifest_rows),
        "summary_structural_declarations": manifest_summary.get(
            "structural_declarations"
        ),
        "summary_structural_class": manifest_summary.get("structural_class"),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in (structural_join["summary_structural_declarations"],
                          structural_join["summary_structural_class"]))
            or structural_join["class_rows"]
            != structural_join["summary_structural_class"]
            or structural_join["structure_rows"] + structural_join["class_rows"]
            != structural_join["summary_structural_declarations"]):
        raise SystemExit(
            "REFUSE: facade manifest structural join disagrees with its "
            f"declaration rows ({json.dumps(structural_join, sort_keys=True)})"
        )
    substrate_emission_join = {
        "emitted_substrate_rows": sum(
            row.get("emitted") is True and row.get("role") == "substrate"
            for row in manifest_rows
        ),
        "summary_substrate_emitted": manifest_summary.get("substrate_emitted"),
    }
    if (not isinstance(substrate_emission_join["summary_substrate_emitted"], int)
            or isinstance(substrate_emission_join["summary_substrate_emitted"], bool)
            or substrate_emission_join["summary_substrate_emitted"] < 0
            or substrate_emission_join["emitted_substrate_rows"]
            != substrate_emission_join["summary_substrate_emitted"]):
        raise SystemExit(
            "REFUSE: facade manifest substrate-emission join disagrees with its "
            f"declaration rows ({json.dumps(substrate_emission_join, sort_keys=True)})"
        )
    init_substrate_names = {
        row.get("name") for row in manifest_init_substrate
        if isinstance(row.get("name"), str) and row["name"]
    }
    demanded_init_names = {
        row["name"] for row in manifest_rows
        if row.get("demanded_outcome") == "init-substrate"
    }
    init_substrate_join = {
        "init_substrate_rows": len(manifest_init_substrate),
        "init_substrate_names": len(init_substrate_names),
        "demanded_init_names": len(demanded_init_names),
        "checked_init_union": len(init_substrate_names | demanded_init_names),
        "summary_init_provided": manifest_summary.get("init_provided"),
        "summary_init_substrate_checked": manifest_summary.get(
            "init_substrate_checked"
        ),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in (init_substrate_join["summary_init_provided"],
                          init_substrate_join["summary_init_substrate_checked"]))
            or init_substrate_join["init_substrate_rows"]
            != init_substrate_join["init_substrate_names"]
            or init_substrate_join["init_substrate_names"]
            != init_substrate_join["summary_init_provided"]
            or init_substrate_join["checked_init_union"]
            != init_substrate_join["summary_init_substrate_checked"]):
        raise SystemExit(
            "REFUSE: facade manifest Init-substrate join disagrees with its "
            f"enumerated rows ({json.dumps(init_substrate_join, sort_keys=True)})"
        )
    instance_attribute_join = {
        "registered_instance_rows": sum(
            row.get("instance_registered") is True for row in manifest_rows
        ),
        "dropped_instance_rows": sum(
            bool(isinstance(row.get("instance_drop_reason"), str)
                 and row["instance_drop_reason"].strip())
            for row in manifest_rows
        ),
        "summary_instance_attrs_kept": manifest_summary.get("instance_attrs_kept"),
        "summary_instance_attrs_dropped": manifest_summary.get("instance_attrs_dropped"),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in (instance_attribute_join["summary_instance_attrs_kept"],
                          instance_attribute_join["summary_instance_attrs_dropped"]))
            or instance_attribute_join["registered_instance_rows"]
            != instance_attribute_join["summary_instance_attrs_kept"]
            or instance_attribute_join["dropped_instance_rows"]
            != instance_attribute_join["summary_instance_attrs_dropped"]):
        raise SystemExit(
            "REFUSE: facade manifest instance-attribute join disagrees with its "
            f"declaration rows ({json.dumps(instance_attribute_join, sort_keys=True)})"
        )
    private_module_counts = Counter(
        row.get("module") for row in manifest_rows
        if isinstance(row.get("name"), str) and row["name"].startswith("_private.")
    )
    private_name_join = {
        "private_rows": sum(private_module_counts.values()),
        "private_modules": dict(sorted(private_module_counts.items())),
        "summary_private_rows": manifest_summary.get("private_name_rows"),
        "summary_private_modules": manifest_summary.get("private_name_modules"),
    }
    if (not isinstance(private_name_join["summary_private_rows"], int)
            or isinstance(private_name_join["summary_private_rows"], bool)
            or private_name_join["summary_private_rows"] < 0
            or not all(isinstance(module, str) and module
                       and isinstance(count, int) and not isinstance(count, bool)
                       and count > 0
                       for module, count in private_module_counts.items())
            or private_name_join["private_rows"]
            != private_name_join["summary_private_rows"]
            or private_name_join["private_modules"]
            != private_name_join["summary_private_modules"]):
        raise SystemExit(
            "REFUSE: facade manifest private-name join disagrees with its "
            f"declaration rows ({json.dumps(private_name_join, sort_keys=True)})"
        )
    printer_counts = Counter(row.get("printer") for row in manifest_rows)
    printer_join = {
        "explicit_rows": printer_counts["pp.explicit"],
        "maxexplicit_rows": printer_counts["pp.maxexplicit"],
        "summary_explicit_printer": manifest_summary.get("explicit_printer"),
        "summary_maxexplicit_printer": manifest_summary.get("maxexplicit_printer"),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in (printer_join["summary_explicit_printer"],
                          printer_join["summary_maxexplicit_printer"]))
            or printer_join["maxexplicit_rows"]
            != printer_join["summary_maxexplicit_printer"]
            or printer_join["explicit_rows"] + printer_join["maxexplicit_rows"]
            != printer_join["summary_explicit_printer"]):
        raise SystemExit(
            "REFUSE: facade manifest printer join disagrees with its declaration "
            f"rows ({json.dumps(printer_join, sort_keys=True)})"
        )
    structural_refusal_join = {
        "structural_refusal_rows": sum(
            bool(isinstance(row.get("structural_refused_reason"), str)
                 and row["structural_refused_reason"].strip())
            for row in manifest_rows
        ),
        "summary_structural_refused": manifest_summary.get("structural_refused"),
    }
    if (not isinstance(structural_refusal_join["summary_structural_refused"], int)
            or isinstance(structural_refusal_join["summary_structural_refused"], bool)
            or structural_refusal_join["summary_structural_refused"] < 0
            or structural_refusal_join["structural_refusal_rows"]
            != structural_refusal_join["summary_structural_refused"]):
        raise SystemExit(
            "REFUSE: facade manifest structural-refusal join disagrees with its "
            f"declaration rows ({json.dumps(structural_refusal_join, sort_keys=True)})"
        )
    generator_attempts = manifest_summary.get("attempts")
    terminal_attempt = (
        generator_attempts[-1]
        if isinstance(generator_attempts, list) and generator_attempts else None
    )
    generator_residue = {
        "cycle_residue": manifest_summary.get("cycle_residue"),
        "value_residue": manifest_summary.get("value_residue"),
        "terminal_errors": (
            terminal_attempt.get("errors") if isinstance(terminal_attempt, dict) else None
        ),
    }
    if (any(not isinstance(count, int) or isinstance(count, bool) or count < 0
            for count in generator_residue.values())
            or generator_residue["cycle_residue"] != 0
            or generator_residue["value_residue"] != 0
            or generator_residue["terminal_errors"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest generator-residue join failed "
            f"({json.dumps(generator_residue, sort_keys=True)})"
        )
    attempt_finalization_join = {
        "attempts": len(generator_attempts),
        "terminal_quarantined": (
            terminal_attempt.get("quarantined")
            if isinstance(terminal_attempt, dict) else None
        ),
        "summary_quarantined": manifest_summary.get("quarantined"),
    }
    if (attempt_finalization_join["attempts"] == 0
            or any(not isinstance(count, int) or isinstance(count, bool) or count < 0
                   for count in (attempt_finalization_join["terminal_quarantined"],
                                 attempt_finalization_join["summary_quarantined"]))
            or attempt_finalization_join["terminal_quarantined"]
            != attempt_finalization_join["summary_quarantined"]):
        raise SystemExit(
            "REFUSE: facade manifest attempt-finalization join disagrees with its "
            f"summary ({json.dumps(attempt_finalization_join, sort_keys=True)})"
        )
    manifest_input_digest_join = join_manifest_input_digests(manifest_summary)
    resistance_demand_join = join_resistance_demand(manifest_summary, module_join)
    manifest_outcome_join = join_manifest_demanded_outcomes(
        manifest_rows, manifest_summary
    )

    demand_names = {name for names in by_module.values() for name in names}
    manifest_decoys = {
        "emission": manifest_summary.get("emission_decoy"),
        "init_substrate": manifest_summary.get("init_substrate_decoy"),
    }
    init_substrate_names = {row.get("name") for row in manifest_init_substrate}
    forbidden_decoy_names = (
        set(manifest_decoys.values()) &
        (set(manifest_name_counts) | init_substrate_names | demand_names)
    )
    init_substrate_falsified = manifest_summary.get("init_substrate_falsified")
    manifest_negative_control_join = {
        "decoys": manifest_decoys,
        "manifest_collisions": len(forbidden_decoy_names),
        "init_substrate_falsified": (
            len(init_substrate_falsified)
            if isinstance(init_substrate_falsified, list) else None
        ),
    }
    if (not all(isinstance(decoy, str) and decoy
                for decoy in manifest_decoys.values())
            or len(set(manifest_decoys.values())) != len(manifest_decoys)
            or manifest_negative_control_join["manifest_collisions"] != 0
            or init_substrate_falsified != []):
        raise SystemExit(
            "REFUSE: facade manifest negative-control join failed "
            f"({json.dumps(manifest_negative_control_join, sort_keys=True)}, "
            f"collisions={sorted(forbidden_decoy_names)!r})"
        )
    unexplained_init_artifact_rows = sorted(
        row.get("name", "<missing>") for row in manifest_init_substrate
        if not isinstance(row.get("reason"), str) or not row["reason"].strip()
    )
    manifest_init_row_provenance_join = {
        "init_artifact_rows": len(manifest_init_substrate),
        "reasoned_init_artifact_rows": len(manifest_init_substrate)
        - len(unexplained_init_artifact_rows),
        "unexplained_rows": len(unexplained_init_artifact_rows),
    }
    if (manifest_init_row_provenance_join["init_artifact_rows"] == 0
            or manifest_init_row_provenance_join["reasoned_init_artifact_rows"]
            != manifest_init_row_provenance_join["init_artifact_rows"]
            or manifest_init_row_provenance_join["unexplained_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest Init-row provenance join failed "
            f"({json.dumps(manifest_init_row_provenance_join, sort_keys=True)}, "
            f"unexplained={unexplained_init_artifact_rows[:8]!r})"
        )
    unemitted_registered_instances = sorted(
        row["name"] for row in manifest_rows
        if row.get("instance_registered") is True and row.get("emitted") is not True
    )
    registered_dropped_instances = sorted(
        row["name"] for row in manifest_rows
        if isinstance(row.get("instance_drop_reason"), str)
        and row["instance_drop_reason"].strip()
        and row.get("instance_registered") is not False
    )
    manifest_instance_state_join = {
        "registered_rows": sum(
            row.get("instance_registered") is True for row in manifest_rows
        ),
        "unemitted_registered_rows": len(unemitted_registered_instances),
        "dropped_rows": sum(
            bool(isinstance(row.get("instance_drop_reason"), str)
                 and row["instance_drop_reason"].strip())
            for row in manifest_rows
        ),
        "registered_dropped_rows": len(registered_dropped_instances),
    }
    if (manifest_instance_state_join["registered_rows"] == 0
            or manifest_instance_state_join["dropped_rows"] == 0
            or manifest_instance_state_join["unemitted_registered_rows"] != 0
            or manifest_instance_state_join["registered_dropped_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest instance-state join failed "
            f"({json.dumps(manifest_instance_state_join, sort_keys=True)}, "
            f"unemitted={unemitted_registered_instances[:8]!r}, "
            f"registered_dropped={registered_dropped_instances[:8]!r})"
        )
    provider_type_dependency_mismatches = sorted(
        row["name"] for row in manifest_rows
        if row.get("provided_by") is not None
        and row.get("provided_by") not in row.get("type_deps", [])
    )
    manifest_provider_type_closure_join = {
        "provider_edges": len(provider_edges),
        "provider_dependency_matches": len(provider_edges)
        - len(provider_type_dependency_mismatches),
        "mismatches": len(provider_type_dependency_mismatches),
    }
    if (manifest_provider_type_closure_join["provider_edges"] == 0
            or manifest_provider_type_closure_join["provider_dependency_matches"]
            != manifest_provider_type_closure_join["provider_edges"]
            or manifest_provider_type_closure_join["mismatches"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest provider-type-closure join failed "
            f"({json.dumps(manifest_provider_type_closure_join, sort_keys=True)}, "
            f"mismatches={provider_type_dependency_mismatches[:8]!r})"
        )
    unknown_printer_rows = []
    init_printer_rows = []
    manifest_printer_counts = Counter()
    for row in manifest_rows:
        printer = row.get("printer")
        if row.get("role") == "init-substrate":
            if printer is not None:
                init_printer_rows.append(row["name"])
            continue
        if printer not in {"pp.fullNames", "pp.explicit", "pp.maxexplicit"}:
            unknown_printer_rows.append(row["name"])
            continue
        manifest_printer_counts[printer] += 1
    manifest_printer_totality_join = {
        "typed_rows": manifest_signature_join["non_init_rows"],
        "recognized_printer_rows": sum(manifest_printer_counts.values()),
        "printers": dict(sorted(manifest_printer_counts.items())),
        "init_rows": manifest_signature_join["init_rows"],
        "init_rows_with_printer": len(init_printer_rows),
        "unknown_printer_rows": len(unknown_printer_rows),
    }
    if (manifest_printer_totality_join["typed_rows"] == 0
            or manifest_printer_totality_join["recognized_printer_rows"]
            != manifest_printer_totality_join["typed_rows"]
            or manifest_printer_totality_join["init_rows_with_printer"] != 0
            or manifest_printer_totality_join["unknown_printer_rows"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest printer-totality join failed "
            f"({json.dumps(manifest_printer_totality_join, sort_keys=True)}, "
            f"unknown={unknown_printer_rows[:8]!r}, init={init_printer_rows[:8]!r})"
        )
    projection_rows = [
        row for row in manifest_rows if row.get("form") == "class-projection"
    ]
    providerless_projections = sorted(
        row["name"] for row in projection_rows if not row.get("provided_by")
    )
    projection_provider_dependency_mismatches = sorted(
        row["name"] for row in projection_rows
        if row.get("provided_by") not in row.get("type_deps", [])
    )
    manifest_row_by_name = {row["name"]: row for row in manifest_rows}
    projection_owner_forms = Counter(
        manifest_row_by_name[row["provided_by"]].get("form") for row in projection_rows
        if row.get("provided_by") in manifest_row_by_name
    )
    manifest_projection_closure_join = {
        "projection_rows": len(projection_rows),
        "structure_owners": projection_owner_forms["structure"],
        "class_owners": projection_owner_forms["class"],
        "providerless_rows": len(providerless_projections),
        "provider_dependency_mismatches": len(
            projection_provider_dependency_mismatches
        ),
    }
    if (manifest_projection_closure_join["projection_rows"] == 0
            or manifest_projection_closure_join["structure_owners"]
            + manifest_projection_closure_join["class_owners"]
            != manifest_projection_closure_join["projection_rows"]
            or manifest_projection_closure_join["providerless_rows"] != 0
            or manifest_projection_closure_join["provider_dependency_mismatches"] != 0):
        raise SystemExit(
            "REFUSE: facade manifest projection-closure join failed "
            f"({json.dumps(manifest_projection_closure_join, sort_keys=True)}, "
            f"providerless={providerless_projections[:8]!r}, "
            f"mismatches={projection_provider_dependency_mismatches[:8]!r})"
        )
    (demand_dispositions, demand_roles, demand_emission, demand_providers,
     demand_printers, demand_type_dependencies,
     demand_level_parameters, demand_effects,
     demand_buckets, demand_safeties,
     demand_instances, demand_forms,
     demand_transparency) = join_demanded_rows(
         demand_names, manifest_rows
     )
    type_ascription_join = join_type_ascriptions(demand_dispositions, sigs)

    # Mutation control for the source guard above. It is deliberately in-memory:
    # no Reference-importing file is ever handed to the pinned compiler.
    reference_import_mutants = ("import Lean\n", "import Lean.Meta\n")
    missed_reference_imports = [
        mutant.rstrip() for mutant in reference_import_mutants
        if not reference_import_lines(mutant)
    ]
    if missed_reference_imports:
        raise SystemExit(
            "REFUSE: Reference-import control did not recognize "
            + ", ".join(missed_reference_imports)
            + " — the facade-source oracle guard is ineffective"
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
    disposition_mutation_control = run_disposition_mutation_control(
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
        "manifest_pin_join": {"schema": manifest_summary["schema"], "reference_pin": tag},
        "manifest_schema_row_join": manifest_schema_join,
        "manifest_row_kind_join": manifest_row_kind_join,
        "manifest_claim_class_join": manifest_claim_class_join,
        "manifest_withdrawal_join": manifest_withdrawal_join,
        "manifest_quarantine_summary_join": quarantine_summary_join,
        "manifest_coverage_summary_join": coverage_summary_join,
        "manifest_structural_field_set_join": structural_field_set_join,
        "manifest_projection_type_pin_join": projection_type_pin_join,
        "manifest_type_roundtrip_pin_join": type_roundtrip_pin_join,
        "manifest_transparent_values_pin_join": transparent_values_pin_join,
        "manifest_init_substrate_pin_join": init_substrate_pin_join,
        "manifest_init_provided_pin_join": init_provided_pin_join,
        "manifest_pin_presence_pin_join": pin_presence_pin_join,
        "manifest_private_name_rows_pin_join": private_name_rows_pin_join,
        "manifest_instance_attrs_kept_pin_join": instance_attrs_kept_pin_join,
        "manifest_instance_attrs_dropped_pin_join": instance_attrs_dropped_pin_join,
        "manifest_substrate_emitted_pin_join": substrate_emitted_pin_join,
        "manifest_declarations_emitted_pin_join": declarations_emitted_pin_join,
        "manifest_emission_verified_pin_join": emission_verified_pin_join,
        "manifest_uncensused_emitted_pin_join": uncensused_emitted_pin_join,
        "manifest_uncensused_closure_pin_join": uncensused_closure_pin_join,
        "manifest_bare_names_probed_pin_join": bare_names_probed_pin_join,
        "manifest_class_provided_projections_pin_join": class_provided_projections_pin_join,
        "manifest_inductive_declarations_pin_join": inductive_declarations_pin_join,
        "manifest_declaration_name_join": manifest_name_join,
        "manifest_signature_totality_join": manifest_signature_join,
        "manifest_role_partition_join": manifest_role_join,
        "manifest_global_provider_join": manifest_provider_join,
        "manifest_type_dependency_totality_join": manifest_type_dependency_join,
        "manifest_effect_totality_join": manifest_effect_join,
        "manifest_safety_totality_join": manifest_safety_join,
        "manifest_level_parameter_totality_join": manifest_level_parameter_join,
        "manifest_transparency_fallback_join": manifest_transparency_fallback_join,
        "manifest_structural_fallback_join": manifest_structural_fallback_join,
        "manifest_nonemission_provenance_join": manifest_nonemission_provenance_join,
        "manifest_module_provenance_join": manifest_module_join,
        "manifest_private_owner_join": manifest_private_owner_join,
        "manifest_form_totality_join": manifest_form_join,
        "manifest_totality_join": totality,
        "manifest_emission_verification_join": emission_verification,
        "manifest_emitted_row_join": emitted_row_join,
        "manifest_emitted_name_join": emitted_name_join,
        "manifest_transparency_join": transparency_join,
        "manifest_structural_join": structural_join,
        "manifest_substrate_emission_join": substrate_emission_join,
        "manifest_init_substrate_join": init_substrate_join,
        "manifest_instance_attribute_join": instance_attribute_join,
        "manifest_private_name_join": private_name_join,
        "manifest_printer_join": printer_join,
        "manifest_structural_refusal_join": structural_refusal_join,
        "manifest_generator_residue_join": generator_residue,
        "manifest_attempt_finalization_join": attempt_finalization_join,
        "manifest_input_digest_join": manifest_input_digest_join,
        "resistance_demand_join": resistance_demand_join,
        "manifest_demanded_outcome_join": manifest_outcome_join,
        "manifest_negative_control_join": manifest_negative_control_join,
        "manifest_init_row_provenance_join": manifest_init_row_provenance_join,
        "manifest_instance_state_join": manifest_instance_state_join,
        "manifest_provider_type_closure_join": manifest_provider_type_closure_join,
        "manifest_printer_totality_join": manifest_printer_totality_join,
        "manifest_projection_closure_join": manifest_projection_closure_join,
        "checked": checked,
        "distinct_symbols": len(control_names),
        "demanded_dispositions": disposition_matrix,
        "demanded_role_join": demand_roles,
        "demanded_emission_join": demand_emission,
        "demanded_provider_join": demand_providers,
        "demanded_signature_printer_join": demand_printers,
        "demanded_type_dependency_join": demand_type_dependencies,
        "demanded_level_parameter_join": demand_level_parameters,
        "demanded_effect_join": demand_effects,
        "demanded_bucket_join": demand_buckets,
        "demanded_safety_join": demand_safeties,
        "demanded_instance_join": demand_instances,
        "demanded_form_join": demand_forms,
        "demanded_transparency_join": demand_transparency,
        "type_dependency_target_join": type_dependency_target_join,
        "demanded_type_ascription_join": type_ascription_join,
        "disposition_matrix_control": {
            "emitted": disposition_matrix.get("emitted", 0),
            "init_substrate": disposition_matrix.get("init-substrate", 0),
            "quarantined": disposition_matrix.get("quarantined", 0),
        },
        "disposition_mutation_control": {
            "name": disposition_mutation_control,
            "mutated_disposition": "init-substrate",
            "rejected": True,
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
            "mutants": [mutant.rstrip() for mutant in reference_import_mutants],
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
