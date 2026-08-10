//! One reclaimer for every scratch root the workspace's test harnesses
//! materialize under [`std::env::temp_dir`] — the single fence of bead
//! `franken_lean-eir2`, successor to `franken_lean-s2sn` and
//! `fln-fixture-retention-unbounded-evit`.
//!
//! # Why the fence lives in fln-core (the Option B decision, disclosed)
//!
//! `evit` measured `tools/structure-guard` retaining every fixture it ever built
//! (16,370 directories / 11 GB, growing ~1.3 GB/hour under swarm load) and `s2sn`
//! repaired that one crate at `b0a52442` with a [`Drop`] that reclaims on the
//! passing path and retains on the failing one, closing with an explicit
//! unmeasured remainder. `eir2` censused the remainder at 2026-07-28: six more
//! producers outside structure-guard, 15,894 directories / 350.1 MiB, and posed
//! the address question — the bead's own words are that "the picking is the
//! work". The candidates:
//!
//! * **Option A — a second copy of the fence in `fln-conformance`.** Declined by
//!   `s2sn` already: two unbound copies of one rule, free to drift, is
//!   `franken_lean-evidence-python-config-rule-drift-imuu`'s defect exactly.
//! * **Option B — this module.** `fln-core` is rank 0: every producer crate
//!   already sits above it, so the move adds **zero dependency edges** (checked
//!   against every manifest at the conversion commit). The cost is test-support
//!   code in a product crate, which is a judgement about what `fln-core` is for;
//!   the bead's analysis called this the one-fence option and the conversion
//!   discloses it in the bead, the commit message, and a route to the graph's
//!   owner. If the address is overruled the conversion is two-line mechanical
//!   changes per producer.
//! * **Option C — leave them.** Indefensible for `ownership.rs`, 13,919
//!   directories and the largest producer by count in the workspace.
//!
//! # What retention still buys, and why it is kept
//!
//! A failing guard run is exactly the case the retained workspace was for.
//! [`ScratchRoot::drop`] checks [`std::thread::panicking`] and leaves a failing
//! test's root on disk with the same message it always printed; only the
//! passing path reclaims. Both directions are proved per converted family —
//! `panicking()` is only true during an unwind, so a cell that merely *asks*
//! cannot observe it and the failing direction needs a real `catch_unwind`.
//!
//! The one semantic edge, measured rather than reasoned (after-run v1 of the
//! conversion, 2026-07-29): a `#[should_panic]` cell passes **by unwinding**, so
//! the guard reads its pass as a failure and retains its root. Four rch-census
//! mutant cells were measured retaining exactly four roots that way. Cells that
//! build fixtures therefore assert refusals in the `catch_unwind` + payload form
//! instead of the attribute — identical refusal evidence, and the root reclaims
//! when the cell passes. `evidence_finalization.rs`'s `assert_panicked_with` is
//! the pattern to copy; the attribute stays fine for cells that build nothing.
//!
//! # The measurement trap, inherited from `s2sn` and still load-bearing
//!
//! Apparent size (`st_size`) is wrong here twice over, in opposite directions:
//! sparse fixture files over-report by orders of magnitude while directories of
//! small files round each up to a 4 KiB block and under-report. Any census of
//! these roots measures `st_blocks * 512` (allocated bytes), never `st_size`.
//!
//! # What this module does not do
//!
//! It removes nothing that already exists. The directories piled up before the
//! fence are `fln-fixture-retention-unbounded-evit` item 1, parked with the
//! repository owner; every reclamation here is of a root this process created
//! seconds earlier and still holds. RULE 1 forbids an *agent* deleting files;
//! the orchestrator ruled on 2026-07-26 that a harness reclaiming its own
//! scratch directory is ordinary hygiene — the authority `b0a52442` landed
//! under and the authority this module inherits.
//!
//! # The declared remainders, and why each is declared rather than routed
//!
//! `routed: false` rows are remainders, and each carries its reason here and in
//! the census that binds them (`scratch_reclamation_census` in fln-conformance):
//!
//! * `kernel-ownership-publisher` — a deliberately nested workspace with its own
//!   `Cargo.lock`; its manifest says its edges "must not add a tooling-only
//!   edge to the product workspace or force unrelated agents to rewrite the
//!   root `Cargo.lock`". The 2026-07-28 census found 0 directories under its
//!   prefix — a reason to defer, never evidence it cannot leak later.
//! * `tribunal/epoch-lab` (two producers) — likewise a nested workspace the
//!   members glob never walks; `eir2` pre-authorizes this remainder by name:
//!   "it may end up a declared remainder for the same reason; if so, declare it
//!   with the reason rather than omitting it."
//!
//! The remainder is one-way plus a floor: a row moves to `routed: true` when its
//! producer starts constructing a guard, and cannot move the other way without
//! someone deciding to. Both directions are bound by the census.
//!
//! `fln-rt/tests/region_engine.rs` is deliberately **not** a family at all: it
//! removes its own root on the passing path, so it is classified self-cleaning
//! by the census rather than held here as a remainder.

use std::fs;
use std::io;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

/// `tools/structure-guard/tests/common/mod.rs` — the seeded-law and authority workspaces.
pub const SEEDED_PREFIX: &str = "structure-guard-test-";
/// `tools/structure-guard/tests/closure.rs` — the dependency-closure audit fixtures.
pub const CLOSURE_PREFIX: &str = "structure-guard-closure-";
/// `tools/structure-guard/src/contract_handoff.rs` — the handoff publication fixtures.
pub const HANDOFF_PREFIX: &str = "contract-handoff-";
/// `tools/structure-guard/src/contract_inventory.rs` — the contract-inventory fixtures.
pub const INVENTORY_PREFIX: &str = "fln-contract-inventory-";
/// `tools/structure-guard/kernel-ownership-publisher/src/main.rs` — the publisher fixtures.
pub const PUBLISHER_PREFIX: &str = "fln-ownership-publisher-";
/// `crates/fln-conformance/src/ownership.rs` — the ownership-projection fixtures.
///
/// Renamed from the historical `fln-ownership-` at the unification: that literal is a
/// prefix of [`PUBLISHER_PREFIX`], and two families whose prefixes overlap would let one
/// family's fence admit the other's roots. Only fresh roots carry this prefix; the
/// pre-fence pile keeps its old name and stays parked with `evit` item 1.
pub const OWNERSHIP_FIXTURE_PREFIX: &str = "fln-ownership-fixture-";
/// `crates/fln-conformance/tests/evidence_finalization.rs` — the staged rch-census roots.
pub const RCH_STAGED_PREFIX: &str = "fln-rch-staged-";
/// `crates/fln-conformance/tests/gate_lock_discriminator.rs` — the gate-lock probe roots.
pub const GATE_DISCRIMINATOR_PREFIX: &str = "fln-gate-discriminator-";
/// `crates/fln-conformance/tests/promotion_protocol_no_mock_e2e.rs` — the shadow-promotion
/// journal roots. The journal file lived directly in the temp dir before the fence; the
/// guard now owns a directory the journal lives inside, so file and root reclaim together.
pub const SHADOW_PROMOTION_PREFIX: &str = "fln-shadow-promotion-";
/// `crates/fln-syntax/tests/golden_vellum.rs` — the anchor-inventory workspace fixtures.
pub const VDI4_PREFIX: &str = "fln-vdi4-";
/// `crates/fln-kernel/tests/reference_differential.rs` — the oracle question workspaces.
pub const REFDIFF_PREFIX: &str = "fln-refdiff-";
/// This module's own machinery tests — a real family, reclaimed like any other, so the
/// fence's self-cells are indistinguishable from production use.
pub const CORE_SELFTEST_PREFIX: &str = "fln-core-scratch-selftest-";
/// `tribunal/epoch-lab/tests/epoch_lab_hash_chain.rs` — the chain-model scratch epochs.
pub const EPOCH_LAB_PREFIX: &str = "fln-epoch-lab-";
/// `tribunal/epoch-lab/tests/derived_input_provenance.rs` — the synthetic workspaces.
pub const DERIVE_PREFIX: &str = "fln-derive-";
/// `crates/fln-vm/tests/extern_dispatch_no_mock_e2e.rs` — the extern dispatch e2e's
/// mirror-tree roots (bead `franken_lean-pw6t`).
pub const EXTERN_E2E_PREFIX: &str = "fln-extern-e2e-";
/// `crates/fln-kernel/tests/admission_laundering.rs` — the compile-fail probe roots
/// (bead `franken_lean-79k`).
pub const ADMISSION_PROBE_PREFIX: &str = "fln-admission-probe-";
/// `crates/fln-olean/tests/artifact_publication.rs` — crash-consistent multi-file
/// publication, cancellation, storage-fault, and process-death fixtures.
pub const ARTIFACT_PUBLICATION_PREFIX: &str = "fln-artifact-publication-";

/// One scratch-root namespace: its prefix, the constant producers name it by, the source
/// that produces it, and whether that source routes through [`ScratchRoot`].
pub struct ScratchFamily {
    /// The literal leading component of every root in this namespace.
    pub prefix: &'static str,
    /// The identifier a producer must name. Producers reference the constant rather than
    /// retyping the literal, so the binding census looks for the *identifier*: a producer
    /// that inlined the string would be reintroducing exactly the drift this table
    /// prevents.
    pub constant: &'static str,
    /// Workspace-relative path of the single source that materializes this namespace.
    pub producer: &'static str,
    /// Whether that producer reclaims via [`ScratchRoot`], or is a declared remainder
    /// (see the module header for each remainder's reason).
    pub routed: bool,
}

/// Every scratch-root namespace the workspace's harnesses materialize under
/// [`std::env::temp_dir`]. One table, so the fence, the producers, the census and the
/// disclosure cannot disagree: a producer that invents a prefix outside it cannot be
/// reclaimed at all — [`is_reclaimable`] refuses it — and a row whose producer has stopped
/// naming its constant is a stale entry, which `scratch_reclamation_census` reddens.
pub const SCRATCH_FAMILIES: &[ScratchFamily] = &[
    ScratchFamily {
        prefix: SEEDED_PREFIX,
        constant: "SEEDED_PREFIX",
        producer: "tools/structure-guard/tests/common/mod.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: CLOSURE_PREFIX,
        constant: "CLOSURE_PREFIX",
        producer: "tools/structure-guard/tests/closure.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: HANDOFF_PREFIX,
        constant: "HANDOFF_PREFIX",
        producer: "tools/structure-guard/src/contract_handoff.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: INVENTORY_PREFIX,
        constant: "INVENTORY_PREFIX",
        producer: "tools/structure-guard/src/contract_inventory.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: OWNERSHIP_FIXTURE_PREFIX,
        constant: "OWNERSHIP_FIXTURE_PREFIX",
        producer: "crates/fln-conformance/src/ownership.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: RCH_STAGED_PREFIX,
        constant: "RCH_STAGED_PREFIX",
        producer: "crates/fln-conformance/tests/evidence_finalization.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: GATE_DISCRIMINATOR_PREFIX,
        constant: "GATE_DISCRIMINATOR_PREFIX",
        producer: "crates/fln-conformance/tests/gate_lock_discriminator.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: SHADOW_PROMOTION_PREFIX,
        constant: "SHADOW_PROMOTION_PREFIX",
        producer: "crates/fln-conformance/tests/promotion_protocol_no_mock_e2e.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: VDI4_PREFIX,
        constant: "VDI4_PREFIX",
        producer: "crates/fln-syntax/tests/golden_vellum.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: REFDIFF_PREFIX,
        constant: "REFDIFF_PREFIX",
        producer: "crates/fln-kernel/tests/reference_differential.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: CORE_SELFTEST_PREFIX,
        constant: "CORE_SELFTEST_PREFIX",
        producer: "crates/fln-core/src/scratch.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: EXTERN_E2E_PREFIX,
        constant: "EXTERN_E2E_PREFIX",
        producer: "crates/fln-vm/tests/extern_dispatch_no_mock_e2e.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: ADMISSION_PROBE_PREFIX,
        constant: "ADMISSION_PROBE_PREFIX",
        producer: "crates/fln-kernel/tests/admission_laundering.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: ARTIFACT_PUBLICATION_PREFIX,
        constant: "ARTIFACT_PUBLICATION_PREFIX",
        producer: "crates/fln-olean/tests/artifact_publication.rs",
        routed: true,
    },
    // --- declared remainders; each one's reason is in the module header. A row here
    // moves to `routed: true` when its producer starts constructing a guard, and the
    // census refuses both an unrouted producer and an emptied remainder.
    ScratchFamily {
        prefix: PUBLISHER_PREFIX,
        constant: "PUBLISHER_PREFIX",
        producer: "tools/structure-guard/kernel-ownership-publisher/src/main.rs",
        routed: false,
    },
    ScratchFamily {
        prefix: EPOCH_LAB_PREFIX,
        constant: "EPOCH_LAB_PREFIX",
        producer: "tribunal/epoch-lab/tests/epoch_lab_hash_chain.rs",
        routed: false,
    },
    ScratchFamily {
        prefix: DERIVE_PREFIX,
        constant: "DERIVE_PREFIX",
        producer: "tribunal/epoch-lab/tests/derived_input_provenance.rs",
        routed: false,
    },
];

/// Whether `root` is one of ours under `prefix`, and therefore safe to reclaim.
///
/// Belt and braces on a `remove_dir_all`: the parent must be exactly the temp directory
/// this harness materializes into, the final component must carry `prefix`, and `prefix`
/// must name a **routed** [`SCRATCH_FAMILIES`] row — a caller cannot widen the fence by
/// passing `""` and turning it into "anything in `/tmp`", and a declared remainder's
/// prefix is refused, because the remainder declaration is precisely the statement that
/// the fence does not stand behind that namespace.
pub fn is_reclaimable(root: &Path, prefix: &str) -> bool {
    SCRATCH_FAMILIES
        .iter()
        .any(|family| family.prefix == prefix && family.routed)
        && root.parent() == Some(std::env::temp_dir().as_path())
        && root
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with(prefix))
}

/// A uniquely named scratch directory that reclaims itself when its test passes.
///
/// Deref-transparent to [`Path`], so a harness that used to bind a `PathBuf` binds this
/// instead and every `&root` and `root.join(..)` at the call sites keeps compiling
/// unchanged. The reclamation happens when the binding goes out of scope, which is the
/// end of the test body — so a fixture stays alive for exactly as long as the test that
/// owns it.
pub struct ScratchRoot {
    path: PathBuf,
    prefix: &'static str,
    /// What to call this fixture in the retention line a failing test prints.
    kind: &'static str,
}

impl ScratchRoot {
    /// Create a fresh root named `{prefix}{pid}-{stamp}-{serial}-{tag}` under the harness
    /// temp directory, retrying on the (vanishingly unlikely) collision rather than
    /// overwriting.
    ///
    /// `create_new`-style semantics are deliberate and predate the fence: a fixture must
    /// never silently inherit a previous run's bytes, which is a property worth more than
    /// the disk.
    pub fn create(prefix: &'static str, kind: &'static str, tag: &str) -> io::Result<ScratchRoot> {
        // A guard the fence cannot reclaim is a silent leak: the prefix must name a
        // routed family row. This is a programmer error, not data — a producer that
        // mistypes or inlines a prefix fails HERE, loudly, rather than at a quiet
        // eprintln on the drop path where the test still passes.
        assert!(
            SCRATCH_FAMILIES
                .iter()
                .any(|family| family.prefix == prefix && family.routed),
            "ScratchRoot::create with unregistered prefix {prefix:?}: the prefix must name \
             a routed SCRATCH_FAMILIES row (add the row deliberately, or use the family's \
             constant)"
        );
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| {
                io::Error::other(format!("system clock precedes the Unix epoch: {error}"))
            })?
            .as_nanos();
        loop {
            let serial = NEXT.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "{prefix}{}-{stamp}-{serial}-{tag}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(ScratchRoot { path, prefix, kind }),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error),
            }
        }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Give up ownership: the directory outlives this guard and is never reclaimed.
    ///
    /// Used only by the tests that *prove* retention happens, which must inspect a root
    /// after the guard that retained it is gone.
    pub fn into_retained(self) -> PathBuf {
        let path = self.path.clone();
        std::mem::forget(self);
        path
    }
}

impl Deref for ScratchRoot {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.path
    }
}

impl AsRef<Path> for ScratchRoot {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

/// So a root can be handed to `Command::env` and friends exactly as a `PathBuf` could.
/// Without it every such call site would need a `&*root`, which is churn that teaches
/// the reader nothing.
impl AsRef<std::ffi::OsStr> for ScratchRoot {
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.path.as_os_str()
    }
}

impl std::fmt::Debug for ScratchRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ScratchRoot")
            .field("path", &self.path)
            .field("prefix", &self.prefix)
            .finish()
    }
}

impl Drop for ScratchRoot {
    fn drop(&mut self) {
        // A failing test is precisely the case the retention was for. `panicking()` is
        // true for the whole unwind, so this covers an assertion failure anywhere in the
        // test body, not merely one raised while the fixture happens to be in scope.
        if std::thread::panicking() {
            eprintln!("retained {} fixture: {}", self.kind, self.path.display());
            return;
        }
        reclaim(&self.path, self.prefix, self.kind);
    }
}

/// Reclaim one root, refusing anything the fence does not recognise.
///
/// Never panics: on the success path a panic here would convert a passing test into a
/// confusing abort, and a directory left on disk is the lesser problem by a wide margin.
fn reclaim(path: &Path, prefix: &str, kind: &str) {
    if !is_reclaimable(path, prefix) {
        eprintln!(
            "refusing to reclaim a {kind} fixture root outside this harness's namespace: {}",
            path.display()
        );
        return;
    }
    if let Err(error) = fs::remove_dir_all(path) {
        eprintln!(
            "could not reclaim {kind} fixture {}: {error}",
            path.display()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    // These cells deliberately mirror the structure-guard suite of the same shape under
    // distinct names: the manifest cites the structure-guard cells by target-qualified
    // name (s2sn's coverage row), and a name colliding across crates would make either
    // citation ambiguous. The fence they exercise is one; each crate's gate covers its
    // own copy of the proof.

    #[test]
    fn core_passing_root_reclaimed_and_failing_root_retained() {
        // A reclaimer that never fires is indistinguishable from one with nothing to do,
        // so both directions are asserted rather than only the tidy one.
        let passing = {
            let root = ScratchRoot::create(CORE_SELFTEST_PREFIX, "core-selftest", "reclaim-pass")
                .expect("create the passing cell's root");
            std::fs::write(root.join("planted"), b"bytes").expect("plant a file");
            root.path().to_path_buf()
        };
        assert!(
            !passing.exists(),
            "a root whose guard dropped without a panic must be gone: {}",
            passing.display()
        );

        // `panicking()` is only true during an unwind, so the failing direction needs a
        // real one. The root is captured out of the panicking closure, which is why this
        // is a RefCell rather than a return value.
        let observed = std::cell::RefCell::new(None);
        let unwound = catch_unwind(AssertUnwindSafe(|| {
            let root = ScratchRoot::create(CORE_SELFTEST_PREFIX, "core-selftest", "reclaim-fail")
                .expect("create the failing cell's root");
            *observed.borrow_mut() = Some(root.path().to_path_buf());
            panic!("deliberate failure so the guard drops during an unwind");
        }));
        assert!(unwound.is_err(), "the failing cell must actually unwind");
        let retained = observed
            .into_inner()
            .expect("the failing cell materialized before it panicked");
        assert!(
            retained.exists(),
            "a root whose guard dropped during an unwind must be retained: {}",
            retained.display()
        );

        // The proof must not itself be a new leak, so reclaim what it deliberately kept.
        std::fs::remove_dir_all(&retained).expect("the probe reclaims the root it retained");
    }

    #[test]
    fn core_fence_refuses_foreign_remainder_and_undeclared_prefixes() {
        let temp = std::env::temp_dir();
        assert!(is_reclaimable(
            &temp.join("fln-core-scratch-selftest-1-2-3-tag"),
            CORE_SELFTEST_PREFIX
        ));
        assert!(
            !is_reclaimable(&temp.join("someone-elses-scratch"), CORE_SELFTEST_PREFIX),
            "a foreign name under the temp dir is refused"
        );
        assert!(
            !is_reclaimable(
                &temp
                    .join("nested")
                    .join("fln-core-scratch-selftest-1-2-3-tag"),
                CORE_SELFTEST_PREFIX
            ),
            "a matching name nested deeper is refused: the parent must be exactly the temp dir"
        );
        assert!(
            !is_reclaimable(Path::new("/"), CORE_SELFTEST_PREFIX),
            "the filesystem root is refused"
        );
        assert!(
            !is_reclaimable(&temp.join("fln-core-scratch-selftest-1-2-3-tag"), ""),
            "an empty prefix cannot widen the fence to everything under the temp dir"
        );
        assert!(
            !is_reclaimable(&temp.join("undeclared-prefix-1-2-3"), "undeclared-prefix-"),
            "a prefix absent from SCRATCH_FAMILIES is refused even if the name matches it"
        );
        assert!(
            !is_reclaimable(&temp.join("fln-epoch-lab-1-2-3"), EPOCH_LAB_PREFIX),
            "a declared remainder's prefix is refused: the declaration says the fence does \
             not stand behind that namespace"
        );
    }

    #[test]
    fn create_with_an_unregistered_prefix_fails_loudly() {
        // The assert is the fence against a silent leak: a producer that mistypes or
        // inlines a prefix must panic here, at construction, rather than at a quiet
        // eprintln on the drop path where the test still passes. Exercised directly,
        // because a guard nobody fires is decoration.
        let unwound = catch_unwind(AssertUnwindSafe(|| {
            let _ = ScratchRoot::create("fln-no-such-family-", "probe", "tag");
        }));
        let payload = unwound.expect_err("an unregistered prefix must panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("<non-string payload>");
        assert!(
            message.contains("fln-no-such-family-") && message.contains("routed"),
            "the refusal must name the prefix and the law: {message}"
        );
    }

    #[test]
    fn core_into_retained_gives_up_ownership_without_reclaiming() {
        let path = {
            let root = ScratchRoot::create(CORE_SELFTEST_PREFIX, "core-selftest", "into-retained")
                .expect("create root");
            root.into_retained()
        };
        assert!(
            path.exists(),
            "into_retained must not reclaim: {}",
            path.display()
        );
        std::fs::remove_dir_all(&path).expect("the probe reclaims what it deliberately kept");
    }

    #[test]
    fn the_family_table_is_internally_consistent() {
        // The table is the fence's whole knowledge of the workspace, and a table nobody
        // checks rots in both directions. The row-to-source half of this binding lives in
        // fln-conformance's `scratch_reclamation_census` — the one place with a checked
        // workspace root; what lives here is everything that needs no tree.
        assert!(
            !SCRATCH_FAMILIES.is_empty(),
            "refusing a vacuous table: no families at all"
        );

        let mut routed = 0usize;
        let mut remainder_prefixes = Vec::new();
        for family in SCRATCH_FAMILIES {
            assert!(
                !family.prefix.is_empty(),
                "an empty prefix admits everything"
            );
            assert!(
                family.prefix.ends_with('-'),
                "prefix {:?} must end in '-' so starts_with matches a whole namespace",
                family.prefix
            );
            assert!(
                !family.constant.is_empty() && !family.producer.is_empty(),
                "a row with an empty constant or producer cannot be bound to anything"
            );
            assert!(
                family.producer.contains('/') && !family.producer.starts_with('/'),
                "producer {:?} must be a workspace-relative path",
                family.producer
            );
            if family.routed {
                routed += 1;
            } else {
                remainder_prefixes.push(family.prefix);
            }
        }

        // Conservation, so the remainder cannot be emptied by deleting a row instead of
        // by routing its producer, and exact membership, so it cannot silently grow.
        assert_eq!(
            routed + remainder_prefixes.len(),
            SCRATCH_FAMILIES.len(),
            "every family is either routed or a declared remainder"
        );
        remainder_prefixes.sort_unstable();
        assert_eq!(
            remainder_prefixes,
            [DERIVE_PREFIX, EPOCH_LAB_PREFIX, PUBLISHER_PREFIX],
            "the declared remainder is exactly these three rows. A change here is a \
             decision: raise it deliberately with the reason, or lower it by routing a \
             producer"
        );
        assert!(
            routed >= 14,
            "at least fourteen producers route through ScratchRoot; found {routed}"
        );

        // Prefixes are distinct, and no prefix is a prefix of another — otherwise one
        // family's fence would admit another's roots and the `routed` column would not
        // mean what it says. This is why the ownership fixture prefix is
        // `fln-ownership-fixture-` and not the historical `fln-ownership-`.
        for (i, a) in SCRATCH_FAMILIES.iter().enumerate() {
            for b in SCRATCH_FAMILIES.iter().skip(i + 1) {
                assert_ne!(a.prefix, b.prefix, "duplicate family prefix {:?}", a.prefix);
                assert!(
                    !a.prefix.starts_with(b.prefix) && !b.prefix.starts_with(a.prefix),
                    "prefixes {:?} and {:?} overlap, so one fence admits the other's roots",
                    a.prefix,
                    b.prefix
                );
            }
        }
    }
}
