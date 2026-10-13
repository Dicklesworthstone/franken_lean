#!/usr/bin/env python3
"""One-time, guarded registration of the IR graph codec.

This runs only in an isolated checkout. It never rewrites historical vectors or
host attestations, and it does not commit: the caller must run the complete hash
and codec package tests and Clippy before publishing the resulting tree.
"""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def replace_once(text: str, old: str, new: str, path: str) -> str:
    if text.count(old) != 1:
        raise SystemExit(f"{path}: expected exactly one registration anchor {old!r}")
    return text.replace(old, new, 1)


def main() -> None:
    canon_path = "crates/fln-hash/src/canon.rs"
    domain_path = "crates/fln-hash/src/domain.rs"
    canon = (ROOT / canon_path).read_text()
    if "pub const SCHEMA_IR_CALL_GRAPH:" in canon:
        required = {
            canon_path: ["hash_rows, 15,"],
            domain_path: ["IrCallGraph", "IrPartition", "HISTORICAL_DOMAIN_VECTORS"],
            "crates/fln-hash/src/lib.rs": ["pub mod ir_graph;"],
            "crates/fln-olean/src/lib.rs": ["pub mod ir_archive;"],
            "crates/fln-hash/fixtures/ir_domain_vectors.txt": ["IrCallGraph|", "IrPartition|"],
        }
        for path, markers in required.items():
            text = (ROOT / path).read_text()
            if any(marker not in text for marker in markers):
                raise SystemExit(f"partial IR registration: {path}")
        print("already-registered")
        return
    edits = {}
    def change(path: str, old: str, new: str) -> None:
        text = edits.get(path, (ROOT / path).read_text())
        edits[path] = replace_once(text, old, new, path)

    change(canon_path, "pub const SCHEMA_REGISTRY: [SchemaRow; 20] = [", "pub const SCHEMA_REGISTRY: [SchemaRow; 21] = [")
    change(canon_path, "/// The crate that defines a durable format's codec.",
        '/// Canonical data-only IR call graph, including classification provenance.\n'
        'pub const SCHEMA_IR_CALL_GRAPH: SchemaId = SchemaId {\n'
        '    name: "fln.canon.ir-call-graph",\n    version: 1,\n};\n\n'
        "/// The crate that defines a durable format's codec.")
    change(canon_path, "pub const SCHEMA_REGISTRY: [SchemaRow; 21] = [\n",
        'pub const SCHEMA_REGISTRY: [SchemaRow; 21] = [\n'
        '    SchemaRow {\n        id: SCHEMA_IR_CALL_GRAPH,\n        owner: SchemaOwner::Hash,\n'
        '        covers: "a static IR call graph with exact names and census annotations; no execution authority",\n    },\n')
    change(canon_path, '            (SCHEMA_CARTRIDGE_ARCHIVE, "fln.canon.cartridge-archive"),\n',
        '            (SCHEMA_CARTRIDGE_ARCHIVE, "fln.canon.cartridge-archive"),\n'
        '            (SCHEMA_IR_CALL_GRAPH, "fln.canon.ir-call-graph"),\n')
    # The new constant is joined above and contributes exactly one Hash-owned
    # schema. Keep the guard's exact inventory assertion, rather than omitting it.
    change(canon_path, '            hash_rows, 14,\n', '            hash_rows, 15,\n')
    change(domain_path, '    /// Tribunal fixture and corpus identity (test apparatus only).\n    Fixture,',
        '    /// Canonical static IR graph analysis data, never kernel authority.\n    IrCallGraph,\n'
        '    /// Exact bytes of an input census partition used to classify an IR graph.\n    IrPartition,\n'
        '    /// Tribunal fixture and corpus identity (test apparatus only).\n    Fixture,')
    change(domain_path, '            Domain::Fixture => "fln 2026 domain fixture/1",',
        '            Domain::IrCallGraph => "fln 2026 domain ir-call-graph/1",\n'
        '            Domain::IrPartition => "fln 2026 domain ir-partition/1",\n'
        '            Domain::Fixture => "fln 2026 domain fixture/1",')
    change(domain_path, 'pub const ALL: [Domain; 20]', 'pub const ALL: [Domain; 22]')
    change(domain_path, '        Domain::Fixture,\n', '        Domain::IrCallGraph,\n        Domain::IrPartition,\n        Domain::Fixture,\n')
    change(domain_path, '            Domain::Fixture => "Fixture",',
        '            Domain::IrCallGraph => "IrCallGraph",\n            Domain::IrPartition => "IrPartition",\n'
        '            Domain::Fixture => "Fixture",')
    # Keep the exact historical multi-host evidence. Current registry tests and
    # their mutants use BOTH files; only the historical-host comparison uses its
    # originally attested bytes. New domains do not inherit a multi-host claim.
    change(domain_path, '    const DOMAIN_VECTORS: &str = include_str!("../fixtures/domain_vectors.txt");',
        '    // The recorded hosts attested this immutable historical vector set.\n'
        '    const HISTORICAL_DOMAIN_VECTORS: &str = include_str!("../fixtures/domain_vectors.txt");\n'
        '    // Current registry coverage extends, rather than rewrites, that evidence.\n'
        '    const DOMAIN_VECTORS: &str = concat!(\n'
        '        include_str!("../fixtures/domain_vectors.txt"),\n'
        '        include_str!("../fixtures/ir_domain_vectors.txt"),\n    );')
    change(domain_path, '        let here_digest = hash(Domain::Fixture, DOMAIN_VECTORS.as_bytes()).to_hex();',
        '        // This claim remains scoped to the bytes those hosts actually ran.\n'
        '        // The new IR domains are covered by the whole-registry vector tests,\n'
        '        // not retroactively attributed to these historical hosts.\n'
        '        let here_digest = hash(Domain::Fixture, HISTORICAL_DOMAIN_VECTORS.as_bytes()).to_hex();')
    change("crates/fln-hash/src/lib.rs", "pub mod domain;\n", "pub mod domain;\npub mod ir_graph;\n")
    change("crates/fln-olean/src/lib.rs", "pub mod ir;\n", "pub mod ir;\npub mod ir_archive;\n")
    enforcement = "crates/fln-hash/tests/domain_enforcement.rs"
    change(enforcement, 'const PUBLIC_MODULES: [&str; 7]', 'const PUBLIC_MODULES: [&str; 8]')
    change(enforcement, '    "domain",\n    "product",', '    "domain",\n    "ir_graph",\n    "product",')
    # Correct an unnecessary Copy clone in the new source before Clippy runs.
    change("crates/fln-olean/src/ir_archive.rs", '    parse_key(key, &mut max_components.clone())',
        '    let mut remaining = max_components;\n    parse_key(key, &mut remaining)')
    change("crates/fln-hash/src/ir_graph.rs", '        let mut left = max_work;\n',
        '        if self.nodes.len() as u64 > max_work {\n'
        '            return Err(GraphArchiveError::Limit("query work"));\n        }\n'
        '        let mut left = max_work;\n')
    # All anchors have been validated before touching the isolated checkout.
    historical = (ROOT / "crates/fln-hash/fixtures/domain_vectors.txt").read_bytes()
    attestations = (ROOT / "crates/fln-hash/fixtures/host_attestations.txt").read_bytes()
    for path, text in edits.items():
        (ROOT / path).write_text(text)
    vector_path = ROOT / "crates/fln-hash/fixtures/ir_domain_vectors.txt"
    if vector_path.exists():
        raise SystemExit("IR vector fixture already exists without registry activation")
    vector_path.write_text("\n# IR domains; new evidence, no historical multi-host claim.\n")
    # The existing producer freezes only the two NEW domains. Every pre-existing
    # domain vector and every attestation remains byte-for-byte unchanged.
    command = ["cargo", "test", "--locked", "-p", "fln-hash", "--lib",
        "emit_domain_vector_rows_for_regeneration", "--", "--nocapture"]
    output = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(output.stdout, end="")
    if output.returncode:
        raise SystemExit(output.returncode)
    rows = [line.removeprefix("fln-domain-vector-row ") for line in output.stdout.splitlines()
        if line.startswith(("fln-domain-vector-row IrCallGraph|", "fln-domain-vector-row IrPartition|"))]
    if len(rows) != 2 or len({row.split("|", 1)[0] for row in rows}) != 2:
        raise SystemExit("producer did not emit exactly the two new domain rows")
    with vector_path.open("a") as handle:
        handle.write("\n".join(rows) + "\n")
    assert historical == (ROOT / "crates/fln-hash/fixtures/domain_vectors.txt").read_bytes()
    assert attestations == (ROOT / "crates/fln-hash/fixtures/host_attestations.txt").read_bytes()
    print("registered")


if __name__ == "__main__":
    main()
