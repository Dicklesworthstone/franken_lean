# Verdict certificate golden provenance

These fixtures freeze the observable bytes crossing the untrusted-solver boundary.
They are deterministic, platform-independent, volatility 1, and compared exactly.
The tests have no update mode and never write either this document or the corpus.

The producer is `fln-verdict@0.0.0` at commit
`25c0244fc5f6823f5dbbcf9357e7ba34d9c32e15`, using policy
`fln.verdict.cdcl.determinism/2`. The canonical input stream is
`fln.verdict.cnf/1`; the certificate stream is
`fln.verdict.unsat-proof/1`.

The reviewed corpus contains:

| Golden | Input constructor | Seed |
|---|---|---|
| `unit-conflict` | `unit-conflict/v1` | `0x6a09e667f3bcc909` |
| `xor-square` | `xor-square/v1` | `0xbb67ae8584caa73b` |
| `pigeonhole-3-2` | `pigeonhole-3-2/v1` | `0x3c6ef372fe94f82b` |

The seeds drive the in-test first-party shuffler before canonical clause
construction. The committed corpus records both resulting CNF bytes and the
independently checked proof bytes, so each fixture is reproducible from its
named constructor and seed without an external generator or dependency.

The initial candidates were emitted once during `fln-pu6i` development, reviewed
for the `FLNVRDCT` header, kind, version, zero extension bits, canonical input,
and independently accepted proof, then manually frozen. The normal verification
command is:

```text
rch exec -- cargo test --locked -p fln-verdict --test golden_certificates
```

An intentional format change must first bump and register the affected durable
schema version. Candidate bytes must then be produced out of band, every byte
diff reviewed, this producer identity and provenance updated, and the complete
Verdict suite rerun. A test failure never rewrites or accepts a fixture.
