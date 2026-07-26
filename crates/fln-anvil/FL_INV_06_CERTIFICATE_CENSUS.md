# FL-INV-06 certificate-accepting path census — `fln-anvil`

Status: current-tree empty-referent result. This is a complete census of the
implemented `fln-anvil` surface, not a claim that FL-INV-06 is implemented.
Claim class: **proof** of zero reachable certificate/admission paths over the
bound implementation inputs and workspace search anchor; no future
implementation or invariant-enforcement claim.
Tracking: open W7 owner `fln-h1k`; the same current-tree negative is retained
in its comments 1313 and 1328. Future implementation obligations remain on
`franken_lean-jxw` and `fln-7kv`.

## Measurement boundary

- Source anchor:
  `6ad070b67d35eb5057df6d516976b11fc063c806`.
- Workspace search anchor:
  `a1559728b0f52ccd27f353f71b5829ebc43ce435`.
- `Cargo.toml` SHA-256:
  `8f9a49846a7f423df89e9a6ad9a8ba2c8006be9c4cca7d26d9c6d702767f62c9`.
- `src/lib.rs` SHA-256:
  `bacd6be0fe6badc781c8bd17123b0593a3a8ac6c52889c4090cde7e91cece561`.
- Scope: every public or private callable in `fln-anvil` that accepts,
  decodes, validates, or consumes a certificate or engine result; every
  publication or environment-admission route reachable from such a callable;
  and every public re-export or workspace consumer of such a route.

The certificate-accepting path count in that boundary is exactly **zero**.

## Census

| # | Entry point and what it accepts | Unknown or drifted version | Failure disposition | Can engine output reach an environment without a kernel-checked artifact? | How established |
|---:|---|---|---|---|---|
| ∅ | **No certificate-accepting entry point exists.** There is no certificate type, decoder, validator, engine-result type, publication function, environment-admission function, private module, or public callable beneath the crate root. | Neither silently accepted nor explicitly rejected. There is no input type, schema, version field, or version branch, so the question is unreachable rather than guarded. | Neither recomputation nor acceptance is reachable. No fallback exists because no certificate path or engine implementation exists. | **No, through `fln-anvil` at this source boundary.** The crate exports no callable, has no private implementation, has no dependency on `fln-env`, `fln-kernel`, `fln-checker`, or another authority crate, and has no workspace consumer or re-export. | **TYPE ARGUMENT (primary):** the compiler-generated public API contains only the crate-root module; the complete implementation source set contains no module or item declaration; the dependency set is empty, so the crate cannot name an environment or checking authority. **READING (supporting, weaker):** the six-line crate root explicitly says “Stub crate: charter only.” **PLANTED MUTANT: not applicable:** there is no production guard or admission join to invert without inventing the missing subsystem. |

There are no additional rows hidden behind private modules: the complete
implementation source set contains only `Cargo.toml` and `src/lib.rs`, and
`src/lib.rs` declares no module. This census document is evidence about that
source set, not an implementation input.

## Evidence

The compiler census was produced without Cargo and wrote only to `/data/tmp`:

```text
anvil_api_dir=$(mktemp -d /data/tmp/cod1-anvil-api.XXXXXX)
rustdoc --crate-name fln_anvil --crate-type lib --edition=2024 \
  -Z unstable-options --output-format json \
  crates/fln-anvil/src/lib.rs --out-dir "$anvil_api_dir"
```

At the source anchor, `fln_anvil.json` reports:

```text
index_size=1
id=0 name=fln_anvil visibility=public kind=module
```

That sole item is the crate-root module itself, so the public-item count beneath
the root is zero.

Independent structural evidence:

- `rg --files crates/fln-anvil -g 'Cargo.toml' -g '*.rs'` returns exactly
  `Cargo.toml` and `src/lib.rs`;
- `src/lib.rs` is six lines, with documentation and
  `#![forbid(unsafe_code)]` only;
- `Cargo.toml` has an empty `[dependencies]`;
- a workspace-wide Rust/manifest search finds no import, dependency, consumer,
  or re-export of `fln-anvil`; the only Rust-side occurrences outside this
  crate are structure-guard inventory rows;
- the two implementation inputs, `Cargo.toml` and `src/lib.rs`, are unchanged
  from the prior compiler census anchor
  `5c5ada4bc033ba17a532fb59b370644e9773c593`.

The environment non-reachability result is therefore a type/dependency fact at
the bound source tree, not merely an absence inferred from a keyword search.

## Claim boundary

Established:

- the implemented `fln-anvil` certificate-accepting path count is zero;
- no malformed, unknown-version, or drifted Anvil certificate is silently
  accepted by the current crate, because the crate cannot receive one;
- no Anvil engine output reaches an environment through the current crate.

Not established:

- that an unknown or drifted certificate version is rejected;
- that certificate-check failure falls back to faithful recomputation;
- that any certificate checker is simpler than recomputation;
- that an engine result is converted into and replayed as a kernel-checked
  artifact;
- that FL-INV-06 is enforced for Anvil.

Those properties have no implementation subject yet. Absence is not a guard,
and this census must not be cited as green FL-INV-06 enforcement.

## Upgrade trigger

Re-run this census when `crates/fln-anvil` gains its first non-documentation
item, module, or dependency, or when another crate first imports/re-exports an
Anvil surface. Each resulting certificate-accepting path must get its own row.
The first implementation must also plant the adjacent dangerous defects:

1. accept an unknown or drifted certificate version;
2. convert certificate-check failure into acceptance instead of recomputation;
3. bypass the kernel-checked artifact at environment admission;
4. remove the faithful recomputation fallback.

The named tests must kill each mutant for the stated reason. Until a production
join exists, manufacturing those mutants would test invented scaffolding rather
than the system.
