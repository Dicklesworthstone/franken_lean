# Upstream contributions ledger

This is the W1 governance record for foundation work. It is not an approval to
change `SUITE.lock`: that lock remains authoritative until an isolated candidate
has passed the complete closure, contract/census, Tribunal, migration, rollback,
and unchanged-root joins.

Rows use `upstream-ledger/1`. `state` may only be one of `proposed`,
`investigated`, `upstream-requested`, `accepted-upstream`, `released`,
`pinned-in-SUITE.lock`, `acceptance-evidenced`, `load-bearing`, `rejected`, or
`superseded`. A request, merge, release, or prose rationale alone never promotes
a consumer. Waivers only defer or block a candidate; they never authorize a D1,
D3, D8, unknown-dependency, incomplete-evidence, or load-bearing violation.

```text
schema upstream-ledger/1
entry id=asupersync-ordered-merge|state=investigated|owner=W1|repository=asupersync|link=local-audit:SUITE.lock|rationale=Need deterministic ordered merge for speculative elaboration only if reviewed primitives are insufficient.|gate=Tribunal candidate acceptance|consumer=fln-elab|fallback=keep merge logic in fln-elab until an accepted upstream primitive exists.|revisit=Re-evaluate after the quorum and pipeline primitive audit.
entry id=franken-networkx-incremental-dominators|state=investigated|owner=W1|repository=franken_networkx|link=local-audit:SUITE.lock|rationale=Need incremental dominator maintenance for live declaration-DAG invalidation cones.|gate=Tribunal candidate acceptance|consumer=fln-ledger|fallback=Use the current conservative invalidation walk until upstream acceptance.|revisit=Re-evaluate when live-edit invalidation profiling identifies the dominator boundary.
entry id=frankensearch-transaction-commit-hooks|state=investigated|owner=W1|repository=frankensearch|link=local-audit:SUITE.lock|rationale=Need index commits aligned with Ledger transaction publication.|gate=Tribunal candidate acceptance|consumer=fln-ledger|fallback=Hold index publication behind the Ledger transaction boundary locally.|revisit=Re-evaluate when Bloodhound publishes its first transactional index consumer.
entry id=franken-markdown-lean-lexer-profile|state=investigated|owner=W1|repository=franken_markdown|link=local-audit:SUITE.lock|rationale=Need a shared Lean lexer profile for Folio highlighting.|gate=Tribunal candidate acceptance|consumer=fln-parse|fallback=Keep the lexer profile in FrankenLean until upstream acceptance.|revisit=Re-evaluate when Folio accepts a native syntax-profile extension.
entry id=frankensqlite-cas-blob-access|state=investigated|owner=W1|repository=frankensqlite|link=local-audit:SUITE.lock|rationale=Need CAS blob access patterns proven by Ledger storage workloads.|gate=Tribunal candidate acceptance|consumer=fln-ledger|fallback=Use the existing pinned blob interface without assuming a new access pattern.|revisit=Re-evaluate after the Ledger CAS workload establishes the needed access pattern.
entry id=fln-bignum-second-suite-consumer|state=investigated|owner=W3|repository=franken_lean|link=local-audit:SUITE.lock|rationale=Kernel-adjacent bignum remains in-repo under the kernel covenant.|gate=Second-suite-consumer review|consumer=fln-kernel|fallback=Keep fln-bignum in-repo.|revisit=Revisit only when a second suite member needs arbitrary precision.
```

An upgrade candidate records its exact old and proposed lock roots, closure delta,
contract/census root, Tribunal root, component migration, rollback result, and
unchanged-current-root check in its retained NDJSON. Cancellation, unavailable
external evidence, source drift, or any incomplete join leaves the current lock
untouched and the candidate non-authoritative.
