# FL-INV-06 certificate-accepting path census — `fln-anvil`

Status: current-tree census of every implemented `fln-anvil` certificate-accepting
or certificate-serializing join (`omega` linear contradiction DAGs and flat
scoped integer branch trees) and every workspace consumer reachable from
`fln-anvil`.

Evidence classes are mixed and explicitly separated:

- **proof** for type/dependency non-reachability of `fln-kernel` and
  `fln-checker` admission capabilities from `fln-anvil`;
- **bounded_model** for planted version/input/scale/parent/conclusion/context/
  framing mutants, resource/cancellation stops, exhaustive small-system models,
  and `fln` provider-boundary tests;
- **reading** where an interface property has no stronger machine check.

Tracking: open W7 owner `fln-h1k`; census reconciliation and out-of-line
`#[cfg(test)]` consumer-scan repair tracked by `fln-verdict-anvil-census-red-fgyp`.

## Measurement boundary

- Workspace anchor: `2000f9b5a3b923add46617ccc5519da2c6844bfb` (+ marker/test-boundary edits in this commit).
- `crates/fln-anvil/Cargo.toml` SHA-256:
  `8af4c7d388445542384b95cbc68e2be10a14231de8249ad60c0fd5f15f7c0bca`
  (4 dependencies: `fln-bignum`, `fln-core`, `fln-elab`, `fln-env`; zero
  dependencies on `fln-kernel`, `fln-checker`, or `fln-admission`).
- Production Rust sources (154 items/modules across 6 files; 2 test-only files
  under `#![cfg(test)]`):
  - `crates/fln-anvil/src/lib.rs`:
    `7cec182865701d946522c3145ffdac594731b1efa3e5c41c93233466199aa9a2`
    (first-order `DTree` lookup + non-executing `Simp*`/`EGraph*`/`NormNum*`/
    `Grind*`/`Portfolio*` data types; zero certificate joins).
  - `crates/fln-anvil/src/omega.rs`:
    `e1a474237df2b1a5f95bd3ecee85ece793c3ee7cb2a48439478f82a059c65d4b`
    (Fourier–Motzkin elimination + `Solver::certificate` producer + `check_witness`
    + `solve`/`solve_with_cancel`/`solve_with_integer_search`/
    `solve_with_integer_search_and_cancel`).
  - `crates/fln-anvil/src/omega/certificate.rs`:
    `80215a9a102ba1acff6fb1e21ec7de00633d05c89d5e7abb055ebfec0a69c89f`
    (linear certificate replay checker + canonical V1 `FLNOMEGA` codec).
  - `crates/fln-anvil/src/omega/branch.rs`:
    `7e82c441ea114c47a2dda72bec4207c6bcf183f0087f5898677319fb75bac72c`
    (iterative integer branch search producing `OmegaBranchCertificate`).
  - `crates/fln-anvil/src/omega/branch/certificate.rs`:
    `4c40cf56715f674d69eea0b13709ac52aca94c8c701c4fde0e7af45d8d33d5ea`
    (scoped flat-tree branch checker + canonical `FLNOMBRN` codec).
  - `crates/fln-anvil/src/omega/branch/rational.rs`:
    `c2e7c2e2f1e865ab0ccf64d9583be75fc81201c38740430f1a588a742c7e1453`
    (exact rational point reconstruction for search; never enters certificates).
- Production workspace consumers (`crates/fln/Cargo.toml` + `crates/fln/src/lib.rs`):
  `Engine::base_source_scope` (`crates/fln/src/lib.rs:1780-1786`) wires
  `fln_anvil::omega::solve` (Faithful/Sound) and
  `fln_anvil::omega::solve_with_integer_search` (Frontier) into
  `fln_elab::arithmetic::ArithmeticProvider`.

Aliases that delegate directly to one implementation join share that row. The
certificate-accepting / certificate-serializing path count in this boundary is
exactly **six**.
Certificate-accepting path cardinality: `6`.

## Census

| # | Boundary ID & entry point | Unknown or drifted version | Failure disposition | Can engine output reach an environment without a kernel-checked artifact? | How established |
|---:|---|---|---|---|---|
| 1 | `omega-linear-certificate-check`: `omega::certificate::check` (public alias `omega::check_certificate`) accepts expected `LinearConstraint` inputs plus an untrusted `OmegaCertificate` and replays exact input binding, positive scales, gcd divisions, and final negative constant contradiction. | `certificate.version != OMEGA_CERTIFICATE_VERSION` returns `Err(CertificateError::UnsupportedVersion(version))` before replaying steps. | Returns `Err(CertificateError)`; metered step/width/row/byte/cancellation stops return `Err(CertificateError::Inconclusive(OmegaInconclusive))` (FL-INV-07). Never mutates an environment or produces an admission token. | **No.** Returns `Checked<Vec<LinearConstraint>>` (derived rows only). `fln-anvil` has no dependency on `fln-kernel`, `fln-checker`, or `fln-admission`; source `omega` tactics build ordinary Lean `Expr` proof terms that must pass Crucible K1 + `fln-checker`. | **TYPE ARGUMENT** over return type and crate dependency graph (`ci/WORKSPACE_GRAPH.txt`). **PLANTED MUTANTS:** `certificate_checker_rejects_wrong_inputs_scales_parents_and_conclusions`, `resource_and_cancellation_stops_preserve_clean_recovery`, and `fln::source_omega::assert_provider_boundary` (`malformed`, `cancelled`, `exhausted`, `expanded_proof`). |
| 2 | `omega-linear-certificate-encode`: `omega::certificate::encode` (public alias `omega::encode_certificate`) serializes an `OmegaCertificate` into canonical V1 `FLNOMEGA` bytes under metered bounds. | `certificate.version != OMEGA_CERTIFICATE_VERSION` returns `Err(CertificateError::UnsupportedVersion(version))`. | Returns `Err(CertificateError)` on unsupported version, width/row/storage overflow, or cancellation; emits no partial authority. | **No.** Produces `Vec<u8>` data only; carries zero proof or admission authority. | **TYPE ARGUMENT** over `Checked<Vec<u8>>`. **BOUNDED MODEL:** `certificate_codec_is_canonical_bounded_and_rejects_corrupt_framing`. |
| 3 | `omega-linear-certificate-decode`: `omega::certificate::decode_after_rows` (aliases `omega::certificate::decode` and `omega::decode_certificate`) decodes bounded V1 `FLNOMEGA` bytes into a structural `OmegaCertificate`. | Non-`FLNOMEGA` magic is `Encoding("certificate magic")`; `version != OMEGA_CERTIFICATE_VERSION` is `Err(CertificateError::UnsupportedVersion(version))`; unknown step tags, noncanonical limbs, negative zero, truncation, and trailing bytes are `CertificateError::Encoding`. | Returns `Err(CertificateError)` (or `Inconclusive` on byte/row/limb/step caps before allocation). Structural decoding never validates arithmetic contradiction; semantic replay requires row 1. | **No.** `OmegaCertificate` is an unsealed plain struct in `fln_elab::arithmetic` accepted by no environment admission API. | **PLANTED MUTANTS:** `certificate_codec_is_canonical_bounded_and_rejects_corrupt_framing` and `certificate_codec_refuses_noncanonical_integers_and_unknown_steps`. **TYPE ARGUMENT** over unsealed data return. |
| 4 | `omega-branch-certificate-check`: `omega::branch::certificate::check` (public alias `omega::check_branch_certificate`) validates root input binding, strict postorder tree ownership (`shape`), scoped `x <= c` / `x >= c + 1` assumptions, and every leaf contradiction via row 1 under one cumulative meter. | `shape` rejects `certificate.version != OMEGA_BRANCH_CERTIFICATE_VERSION` with `Err(CertificateError::UnsupportedVersion(version))`, and row 1 rejects any drifted leaf version. | Returns `Err(CertificateError)` on shape/input/variable/leaf refusal or `Err(CertificateError::Inconclusive(_))` on cumulative meter exhaustion/cancellation. | **No.** Returns `Checked<()>` and touches no `Environment` or admission capability. Frontier source `omega` replays branch trees into Lean `Expr` proof terms checked by K1 + `fln-checker`. | **TYPE ARGUMENT** over `Checked<()>` and dependency closure. **PLANTED MUTANTS:** `branch_checker_rejects_context_substitution_and_malformed_trees`, `branch_resources_and_cancellation_are_cumulative_and_recoverable`, and `fln` integer-search source integration tests (`omega_integer_search.rs`). |
| 5 | `omega-branch-certificate-encode`: `omega::encode_branch_certificate` validates tree shape (`shape`) and writes canonical `FLNOMBRN` bytes with length-delimited V1 leaf certificates via row 2. | Rejects `certificate.version != OMEGA_BRANCH_CERTIFICATE_VERSION` (via `shape`) and drifted leaf versions (via row 2) with `CertificateError::UnsupportedVersion`. | Returns `Err(CertificateError)` on shape/version/resource failure; emits only `Vec<u8>` data. | **No.** Produces raw bytes with no admission route. | **TYPE ARGUMENT** over `Checked<Vec<u8>>`. **BOUNDED MODEL:** `branch_codec_rejects_truncation_unknown_versions_tags_and_lengths`. |
| 6 | `omega-branch-certificate-decode`: `omega::decode_branch_certificate` decodes bounded `FLNOMBRN` bytes, validates cumulative node/leaf row caps before leaf decode (row 3), rejects trailing bytes, and checks strict postorder tree ownership (`shape`). | Non-`FLNOMBRN` magic is `Encoding("branch magic")`; `version != OMEGA_BRANCH_CERTIFICATE_VERSION` (and any drifted leaf version) returns `Err(CertificateError::UnsupportedVersion(version))`; unknown node tags, truncation, and trailing bytes are `CertificateError::Encoding`. | Returns `Err(CertificateError)` without solving or granting authority; leaf arithmetic validity still requires row 4. | **No.** `OmegaBranchCertificate` is an unsealed data struct in `fln_elab::arithmetic` with no environment consumer; source elaboration constructs a Lean proof term checked by K1 + `fln-checker`. | **PLANTED MUTANTS:** `branch_codec_rejects_truncation_unknown_versions_tags_and_lengths` and `branch_resources_and_cancellation_are_cumulative_and_recoverable`. **TYPE ARGUMENT** over return type. |

## Adjacent producers and workspace consumer path

- `omega::solve`, `solve_with_cancel`, `solve_with_integer_search`, and
  `solve_with_integer_search_and_cancel` (backed by private `Solver::run`,
  `Solver::certificate`, and `omega::branch::solve`) are certificate/witness
  *producers* over `&[LinearConstraint]`, not certificate-accepting inputs.
  `omega::check_witness` checks a `Sat` assignment (`Attempt<bool>`) and grants
  no contradiction or admission authority.
- Although `crates/fln-anvil/Cargo.toml` declares `fln-env` for future §12.1
  rewrite-index transparency queries, `crates/fln-anvil/src/**` contains zero
  imports or references to `fln_env`, `fln_kernel`, `fln_checker`, or
  `fln_admission`.
- Across the entire workspace, the sole production consumer is `fln`
  (`crates/fln/Cargo.toml` + `crates/fln/src/lib.rs:1780-1786`), which passes
  `fln_anvil::omega::solve` (Faithful/Sound) or
  `fln_anvil::omega::solve_with_integer_search` (Frontier) into
  `fln_elab::arithmetic::ArithmeticProvider`. Inside `fln-elab`, the `omega`
  tactic replays the returned certificate to synthesize an ordinary Lean `Expr`
  proof term, and `Engine::admit_declaration` still checks every resulting
  declaration through Crucible K1 (`fln_kernel::check::plan_add_decl`) and the
  independent checker (`fln-checker`). As verified in
  `crates/fln/tests/source_omega.rs` (`assert_provider_boundary`), a malformed
  certificate is rejected as `"native arithmetic returned an invalid
  certificate"`, cancellation and resource exhaustion propagate as typed
  `Inconclusive` outcomes without `try` masking them, and no declaration enters
  the environment unchecked.

## Claim boundary

Established:

- all 6 implemented `fln-anvil` certificate checker/codec boundaries reject
  unknown versions with `CertificateError::UnsupportedVersion` and separate
  resource/cancellation stops (`CertificateError::Inconclusive`) from malformed
  certificates;
- `fln-anvil` cannot directly mutate an `Environment` or forge a checked
  declaration capability;
- the sole production workspace consumer (`fln` -> `ArithmeticProvider`) turns
  `omega` certificates into ordinary Lean proof terms that still cross K1 +
  `fln-checker`;
- `crates/fln-verdict/tests/input_validation.rs` binds `fln-anvil`'s exact
  6 boundaries, 5 wrapper aliases, 7 extra source paths, 154 production Rust
  items, 4 manifest dependencies, and 2 workspace consumer files (including
  files with early out-of-line `#[cfg(test)] mod ...;` declarations).

Not established:

- universal complexity dominance of certificate replay over proof search across
  all arbitrary-precision inputs;
- FL-INV-06 enforcement for future `simp`, e-graph proof extraction, `norm_num`,
  `grind`, or portfolio tactic implementations once `crates/fln-anvil/src/lib.rs`
  moves beyond data definitions and `DTree` pre-filtering.

## Upgrade triggers

Re-run and update this census whenever:

1. `crates/fln-anvil` adds or removes a production file, item, dependency, or
   certificate-handling function;
2. any new workspace crate or `src/` module imports `fln-anvil`;
3. `OMEGA_CERTIFICATE_VERSION` or `OMEGA_BRANCH_CERTIFICATE_VERSION` changes; or
4. `simp`, e-graph, `norm_num`, `grind`, or portfolio execution lands in
   `fln-anvil`.
