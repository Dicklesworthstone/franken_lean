# Reusable static IR graph snapshots

This is the graph-file implementation for `fln-ir-decoder-call-graph-sjzl`.
`fln-hash::ir_graph` owns the canonical data format; `fln-olean::ir_archive`
converts the existing validated graph and reads the generated census partition.
Module exports and registry entries are activated together only after the hash
and codec suites, Clippy, and workspace compilation pass the activation workflow.

## Data, not authority

A snapshot contains names, node kinds, static call targets, classifications and
classification provenance. It does not contain executable IR. Reading one does
not produce a kernel admission token or an IR-validation token. The digest is
integrity protection, not authentication: a caller needs a separately trusted
expected digest to authenticate a particular snapshot. An attacker can re-seal
arbitrary well-formed graph data; that does not make it evidence about a program.

## Version 1 encoding

The shared canonical writer emits a schema header for `fln.canon.ir-call-graph`,
version 1: a u64-length-prefixed UTF-8 schema name and u16 little-endian version.
It is followed by a u64 count of unresolved closure-value applications; a
canonical Boolean and optional 32-byte partition digest; and a u64 node count.

Nodes are strictly ordered by structural `Name` order. Each row holds the
shared canonical Name body, a one-byte kind (0 function, 1 extern, 2
signature-only), a one-byte class (0 toolchain-api, 1 library-code, 2 data,
3 explicitly declared user, 4 unclassified), a Boolean and optional canonical
census-row Name, then a u64 edge count and u32 target indices. Target indices are
strictly increasing, unique and inside the node table. Only function nodes may
have outgoing edges. Names preserve numeric/string distinctions and overflow
flags; display strings are never identity keys.

The file ends with the 32-byte BLAKE3 digest of the complete schema-headed
payload under the registered `IrCallGraph` domain. No trailing bytes or unknown
version/tag can be normalized away. The reader checks semantic invariants even
when the digest matches, including re-sealed malformed inputs.

The optional census fingerprint hashes every input TSV byte under the separate
`IrPartition` domain. Census classes require that fingerprint and an originating
row; user/unclassified nodes cannot claim a census row. The adapter performs
exact-key joins only. Specializations absent from the census stay unclassified;
there is no suffix or namespace heuristic that could turn toolchain code into
user code. The explicit-user API refuses census overrides and unknown names.

Host paths, temporary node numbering, timings and module enumeration do not
enter the snapshot. Reordering identical module inputs gives identical bytes.
Full and partial application edges are retained. Indirect `ap` calls have no
invented static edge; their whole-graph count is carried explicitly.

## Limits and evidence

Encoding and decoding enforce byte, node, edge and cumulative Name-component
limits. Lengths are checked before vector allocations. Queries are iterative,
cycle-safe and budgeted, and return no partial result for a missing root or an
exhausted budget. A native-boundary query must stop at unclassified nodes as
well as toolchain API nodes rather than presuming unknown code is harmless.

New domain-vector rows are retained separately from the historical vector set.
Old vectors and recorded host attestations remain byte-identical. The recorded
multi-host claim remains about the bytes those hosts actually observed; new IR
domains do not inherit it. Current registry/vector tests cover all domains.

Tests cover corrupted and re-sealed graphs, exact resource boundaries, source
annotations, cycles and stopped traversal, names with ambiguous display forms,
module-order independence, partial/indirect calls and strict census parsing.
Full corpus export and complete classification of compiler auxiliaries remain
unmeasured. A smaller set of static edges is not a complete runtime call graph.
