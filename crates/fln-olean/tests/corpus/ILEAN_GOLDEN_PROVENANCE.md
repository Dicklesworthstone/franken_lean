# Ilean golden provenance

This fixture freezes the exact compact JSON bytes emitted by the pinned
Reference for one declaration, one declaration site, one external reference,
and one parent-declaration-bearing usage.

- deterministic: yes
- platform-dependent: no
- volatility: 1
- comparison: exact bytes
- update mode: none

The producer was:

```text
Lean (version 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
```

The reviewed source was:

```lean
def localIdentity (x : Nat) := x
```

It was produced on 2026-07-30 with the pinned binary and no plugins:

```text
lean -R . -i IleanProbe.ilean IleanProbe.lean
```

`IleanProbe.ilean` was 318 bytes with no trailing newline. Its complete bytes
were converted to lowercase hexadecimal and reviewed for the generated
`Ilean` field inventory, compact import/reference/range shapes, version 5, and
module identity before being frozen in `ilean_probe.hex`.

Normal tests never regenerate or rewrite the fixture. An intentional format
change first updates the generated contract from a new suite pin, emits a
candidate out of band, reviews every byte difference, updates this provenance,
and reruns both the reviewed golden and the complete installed `.ilean` corpus.
