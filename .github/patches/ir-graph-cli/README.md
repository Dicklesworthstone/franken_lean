# IR graph command increment

These are complete implementation and test sources for the next command
increment, not pseudocode. They are staged here because the graph codec's
schema/domain exports must be registered and tested before a live binary can
import them. Installing the command first would break the existing build.

`scripts/register_ir_graph_cli.py` verifies these exact Git blob identities,
refuses a concurrent change to the live `fln-ir-check`, and installs the sources
in an isolated test checkout after codec registration. The activation workflow
runs both full package suites, Clippy and workspace compilation, then commits
only the tested registration/command files to main with a normal fast-forward.
Until that activation commit exists, these command options are NOT live.

After activation:

```sh
cargo build --locked -p fln-olean --bin fln-ir-check --bin fln-ir-graph

# Every supplied IR declaration must resolve in the explicit file closure.
# Unclassified nodes remain visible; no compiler-suffix guessing is performed.
./target/debug/fln-ir-check --archive --partition contracts/builtin_partition.tsv A.ir B.ir > graph.flig

# Query the saved data without opening A.ir/B.ir again.
./target/debug/fln-ir-graph graph.flig
./target/debug/fln-ir-graph --root Example.main graph.flig
./target/debug/fln-ir-graph --root-key 'a/s"Example"/s"main"' --native-boundary graph.flig
```

The partition is an explicitly provided generated input, not a bundled census.
`--user-key` annotates a known user symbol explicitly; it cannot override a
census match. `--strict-classes` refuses export while any node is unclassified.
Queries at the native boundary stop at unknown classifications as well as
known toolchain API. Ordinary queries follow all static calls. Neither is a
complete runtime call graph: `ap` targets are not known, and the reported
indirect-call count covers the whole archive, not just reached nodes.

`--expect-digest` on the query command checks a separately trusted payload digest.
The embedded checksum alone supplies integrity, not authentication. Resource,
malformedness, missing-root and usage errors emit no partial query result.
Output is completely prepared before writing, but shell redirection is not an
atomic publication API: it can create an empty destination, and I/O failure may
interrupt a write. The library format is defined in `docs/IR_GRAPH_FORMAT.md`.

The ten executable integration tests include exporting an unchanged real
Reference declaration in a synthetic wrapper and querying after the original
IR path is renamed, location/order-independent bytes, census annotations,
strict unknown-class refusal, digest verification, corruption, exact resource
boundaries and native-boundary traversal. A source/test being present is not
proof that its runner has executed it.
