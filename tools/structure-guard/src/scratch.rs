//! One reclaimer for every scratch root this crate materializes (bead
//! `franken_lean-s2sn`, successor to `fln-fixture-retention-unbounded-evit`).
//!
//! # Why this module exists rather than a fourth copy of the same twelve lines
//!
//! `evit` measured `tools/structure-guard/tests/common/mod.rs` retaining every fixture it
//! ever built — 16,370 directories and 11 GB in `/data/tmp`, growing about 1.3 GB per hour
//! under swarm load — and repaired that one harness at `b0a52442` with a [`Drop`] that
//! reclaims on the passing path and retains on the failing one. It closed with an explicit
//! unmeasured remainder: *"Only structure-guard was fixed. Other harnesses may retain scratch
//! state the same way and I have not looked."*
//!
//! They do. Measured at 2026-07-28 16:19 local against `/data/tmp`, with the producer of each
//! family derived by reading every `std::env::temp_dir()` call site under `crates/`, `tools/`
//! and `tribunal/` rather than guessed from the directory names:
//!
//! ```text
//! family                        n   allocMiB  producer
//! structure-guard-test-     10911    7248.8   tests/common/mod.rs        (repaired at b0a52442)
//! structure-guard-closure-   3776    2486.9   tests/closure.rs
//! contract-handoff-          2080     321.7   src/contract_handoff.rs
//! fln-contract-inventory-    1267      76.4   src/contract_inventory.rs
//! ```
//!
//! Three unrepaired producers inside this one crate, still growing that day, holding
//! **2,885.0 MiB of the 3,235.0 MiB workspace-wide live leak**. They are routed through this
//! module instead of each growing a private reclaimer, because three more copies of one fence
//! is `franken_lean-evidence-python-config-rule-drift-imuu`'s defect — two unbound copies of a
//! rule, free to drift — and reproducing it inside its own repair is not a trade worth making.
//!
//! # The measurement trap, recorded because it inverts the conclusion in both directions
//!
//! Apparent size (`st_size`) is wrong here twice over, and the two errors point opposite ways.
//! `contract-handoff-` reads **92,763.8 MiB apparent against 321.7 MiB allocated** — 288× over,
//! because 181 of those roots hold a deliberately *sparse* 512 MiB file planted by the
//! `resource-exhaustion` cell, and the whole 181-root set costs 20.5 MiB of real disk.
//! `structure-guard-test-` reads **600.2 MiB apparent against 7,248.8 MiB allocated** — 12×
//! *under*, because 10,911 directories of small files each round up to a 4 KiB block. The first
//! figure reads as an emergency that does not exist; the second reads as "not worth fixing" and
//! is the largest pile on the box. Measure `st_blocks * 512`.
//!
//! # What retention still buys, and why it is kept
//!
//! A failing guard run is exactly the case the retained workspace was for, and nobody has
//! measured how often one is actually read afterwards. So the value side of that trade is
//! unpriced, and this module does not decide it: [`ScratchRoot::drop`] checks
//! [`std::thread::panicking`] and leaves a failing test's root on disk with the same message it
//! always printed. Only the passing path reclaims.
//!
//! # What this module does not do
//!
//! It removes nothing that exists. The directories already on disk when this landed are
//! `evit` item 1, parked with the repository owner, and no code here can reach them: every
//! reclamation is of a root this process created seconds earlier and still holds. RULE 1
//! forbids an *agent* deleting files; the orchestrator ruled on 2026-07-26 that a harness
//! reclaiming its own scratch directory is ordinary hygiene, which is the authority
//! `b0a52442` landed under and the authority this module inherits.

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

/// One scratch-root namespace: its prefix, the constant producers name it by, the source that
/// produces it, and whether that source routes through [`ScratchRoot`].
pub struct ScratchFamily {
    /// The literal leading component of every root in this namespace.
    pub prefix: &'static str,
    /// The identifier a producer must name. Producers reference the constant rather than
    /// retyping the literal, so the binding check below looks for the *identifier*: a producer
    /// that inlined the string would be reintroducing exactly the drift this table prevents.
    pub constant: &'static str,
    /// Crate-relative path of the single source that materializes this namespace.
    pub producer: &'static str,
    /// Whether that producer reclaims via [`ScratchRoot`], or is a declared remainder.
    pub routed: bool,
}

/// Every scratch-root namespace this tool tree materializes under [`std::env::temp_dir`].
///
/// One table, so the fence, the producers and the disclosure cannot disagree. A producer that
/// invents a prefix outside it cannot be reclaimed at all — [`is_reclaimable`] refuses it — and
/// a row whose producer has stopped naming its constant is a stale entry keeping a slot warm for
/// a future mismatch. Both directions are checked against the crate's own sources by
/// `every_declared_scratch_prefix_has_exactly_one_producer`.
///
/// `routed: false` is a **declared remainder**, and there is exactly one.
/// `kernel-ownership-publisher` is a deliberately nested workspace with its own `Cargo.lock`,
/// and its manifest says in as many words that its dependency edges "must not add a tooling-only
/// edge to the product workspace or force unrelated agents to rewrite the root `Cargo.lock`".
/// Reaching this module from there means a new dependency on `structure-guard`, which is a graph
/// decision belonging to the graph's owner and not to a disk-hygiene repair. It is also the
/// cheapest row to leave: the 2026-07-28 census found **0** directories under that prefix on a
/// box holding 33,928 others, so routing it would buy nothing measurable today — a reason to
/// defer it, never evidence that it cannot leak later.
///
/// The remainder is one-way plus a floor: a row moves to `routed: true` when its producer starts
/// constructing a guard, and cannot move the other way without someone deciding to.
pub const SCRATCH_FAMILIES: &[ScratchFamily] = &[
    ScratchFamily {
        prefix: SEEDED_PREFIX,
        constant: "SEEDED_PREFIX",
        producer: "tests/common/mod.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: CLOSURE_PREFIX,
        constant: "CLOSURE_PREFIX",
        producer: "tests/closure.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: HANDOFF_PREFIX,
        constant: "HANDOFF_PREFIX",
        producer: "src/contract_handoff.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: INVENTORY_PREFIX,
        constant: "INVENTORY_PREFIX",
        producer: "src/contract_inventory.rs",
        routed: true,
    },
    ScratchFamily {
        prefix: PUBLISHER_PREFIX,
        constant: "PUBLISHER_PREFIX",
        producer: "kernel-ownership-publisher/src/main.rs",
        routed: false,
    },
];

/// Whether `root` is one of ours under `prefix`, and therefore safe to reclaim.
///
/// Belt and braces on a `remove_dir_all`: the parent must be exactly the temp directory this
/// harness materializes into, and the final component must carry `prefix`. A bug that corrupted
/// a stored root then cannot reach anything outside that namespace — the reclaimer refuses and
/// says so instead of guessing. `prefix` must itself name a [`SCRATCH_FAMILIES`] row, so a
/// caller cannot widen the fence by passing `""` and turning it into "anything in `/tmp`".
pub fn is_reclaimable(root: &Path, prefix: &str) -> bool {
    SCRATCH_FAMILIES
        .iter()
        .any(|family| family.prefix == prefix)
        && root.parent() == Some(std::env::temp_dir().as_path())
        && root
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with(prefix))
}

/// A uniquely named scratch directory that reclaims itself when its test passes.
///
/// Deref-transparent to [`Path`], so a harness that used to bind a `PathBuf` binds this instead
/// and every `&root` and `root.join(..)` at the call sites keeps compiling unchanged. The
/// reclamation happens when the binding goes out of scope, which is the end of the test body —
/// so a fixture stays alive for exactly as long as the test that owns it.
pub struct ScratchRoot {
    path: PathBuf,
    prefix: &'static str,
    /// What to call this fixture in the retention line a failing test prints.
    kind: &'static str,
}

impl ScratchRoot {
    /// Create a fresh root named `{prefix}{pid}-{stamp}-{serial}-{tag}` under the harness temp
    /// directory, retrying on the (vanishingly unlikely) collision rather than overwriting.
    ///
    /// `create_new`-style semantics are deliberate and predate this module: a fixture must never
    /// silently inherit a previous run's bytes, which is a property worth more than the disk.
    pub fn create(prefix: &'static str, kind: &'static str, tag: &str) -> io::Result<ScratchRoot> {
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

    /// Adopt a root some other code created, so that harness gets the same reclamation without
    /// giving up its own naming scheme.
    pub fn adopt(path: PathBuf, prefix: &'static str, kind: &'static str) -> ScratchRoot {
        ScratchRoot { path, prefix, kind }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Give up ownership: the directory outlives this guard and is never reclaimed.
    ///
    /// Used only by the tests that *prove* retention happens, which must inspect a root after
    /// the guard that retained it is gone.
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

/// So a root can be handed to `Command::env` and friends exactly as a `PathBuf` could. Without
/// it every such call site would need a `&*root`, which is churn that teaches the reader nothing.
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
        // A failing test is precisely the case the retention was for. `panicking()` is true for
        // the whole unwind, so this covers an assertion failure anywhere in the test body, not
        // merely one raised while the fixture happens to be in scope.
        if std::thread::panicking() {
            eprintln!("retained {} fixture: {}", self.kind, self.path.display());
            return;
        }
        reclaim(&self.path, self.prefix, self.kind);
    }
}

/// Reclaim one root, refusing anything the fence does not recognise.
///
/// Never panics: on the success path a panic here would convert a passing test into a confusing
/// abort, and a directory left on disk is the lesser problem by a wide margin.
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

    #[test]
    fn a_passing_root_is_reclaimed_and_a_failing_one_is_retained() {
        // A reclaimer that never fires is indistinguishable from one with nothing to do, so
        // both directions are asserted rather than only the tidy one.
        let passing = {
            let root = ScratchRoot::create(HANDOFF_PREFIX, "contract-handoff", "reclaim-pass")
                .expect("create the passing cell's root");
            std::fs::write(root.join("planted"), b"bytes").expect("plant a file");
            root.path().to_path_buf()
        };
        assert!(
            !passing.exists(),
            "a root whose guard dropped without a panic must be gone: {}",
            passing.display()
        );

        // `panicking()` is only true during an unwind, so a cell that merely *asks* whether
        // retention would happen cannot observe it. The root has to be captured out of the
        // panicking closure, which is why this is a channel rather than a return value.
        let observed = std::cell::RefCell::new(None);
        let unwound = catch_unwind(AssertUnwindSafe(|| {
            let root = ScratchRoot::create(HANDOFF_PREFIX, "contract-handoff", "reclaim-fail")
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
    fn the_fence_refuses_everything_outside_the_harness_namespace() {
        let temp = std::env::temp_dir();
        assert!(is_reclaimable(
            &temp.join("contract-handoff-1-2-3-tag"),
            HANDOFF_PREFIX
        ));
        assert!(
            !is_reclaimable(&temp.join("someone-elses-scratch"), HANDOFF_PREFIX),
            "a foreign name under the temp dir is refused"
        );
        assert!(
            !is_reclaimable(
                &temp.join("nested").join("contract-handoff-1-2-3-tag"),
                HANDOFF_PREFIX
            ),
            "a matching name nested deeper is refused: the parent must be exactly the temp dir"
        );
        assert!(
            !is_reclaimable(Path::new("/"), HANDOFF_PREFIX),
            "the filesystem root is refused"
        );
        assert!(
            !is_reclaimable(&temp.join("contract-handoff-1-2-3-tag"), ""),
            "an empty prefix cannot widen the fence to everything under the temp dir"
        );
        assert!(
            !is_reclaimable(&temp.join("undeclared-prefix-1-2-3"), "undeclared-prefix-"),
            "a prefix absent from SCRATCH_PREFIXES is refused even if the name matches it"
        );
    }

    #[test]
    fn into_retained_gives_up_ownership_without_reclaiming() {
        let path = {
            let root = ScratchRoot::create(SEEDED_PREFIX, "structure-guard", "into-retained")
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
    fn every_declared_scratch_prefix_has_exactly_one_producer() {
        // The fence is only as good as the family table, and a table nobody checks rots in both
        // directions: a producer that invents a prefix is silently unreclaimable, and a row whose
        // producer is gone keeps a slot warm for a future mismatch. So each row is bound to the
        // crate's own sources rather than to this module's memory of them.
        //
        // This module's source is deliberately NOT in any corpus below. A scan whose search space
        // contains its own declaration passes by reading itself, which is the self-match shape
        // `fln-8zsq` paid for; every hit here therefore comes from a producer.
        let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        assert!(
            !SCRATCH_FAMILIES.is_empty(),
            "refusing a vacuous scan: the family table is empty"
        );

        let mut routed = 0usize;
        let mut remainder = 0usize;
        for family in SCRATCH_FAMILIES {
            let path = crate_root.join(family.producer);
            // assert-then-expect rather than `unwrap_or_else(|_| panic!(..))`: the message needs
            // the interpolated path, and `expect(&format!(..))` is what clippy's `expect_fun_call`
            // refuses. It also separates "the declared producer is gone" from "it is unreadable",
            // which are different failures of this table.
            assert!(
                path.is_file(),
                "declared producer for {:?} does not exist: {}",
                family.prefix,
                path.display()
            );
            let text = std::fs::read_to_string(&path).expect("declared producer is readable");
            assert!(
                text.len() > 512,
                "refusing a vacuous scan: {} is implausibly small at {} bytes",
                path.display(),
                text.len()
            );

            // A ROUTED producer must name its constant and must NOT also carry the raw literal:
            // two spellings of one prefix is how this table starts lying.
            //
            // A DECLARED REMAINDER cannot name the constant, and that is the whole reason it is
            // a remainder — `kernel-ownership-publisher` is a nested workspace with no dependency
            // on this crate, so the identifier is unreachable there and the literal is the only
            // spelling available. Requiring the constant of it would be a wall against the exact
            // condition being disclosed. So the needle is chosen by the row: constant when routed,
            // literal when not, and each direction is refused for the other kind.
            if family.routed {
                // The constant must be the FIRST ARGUMENT of the construction, not merely
                // present somewhere in the file. A blanket "the literal appears nowhere" ban was
                // tried first and is wrong: `tests/common/mod.rs` legitimately writes
                // `structure-guard-test-1-2-3-tag` as fence *test input*, so that rule refused a
                // correct file — a wall against the practice it was meant to protect. Bind the
                // call site instead, which is the thing that could actually drift.
                assert!(
                    text.contains(&format!("ScratchRoot::create({}", family.constant)),
                    "{} is routed but never calls ScratchRoot::create({}); the declared prefix \
                     {:?} therefore has no producer binding it",
                    path.display(),
                    family.constant,
                    family.prefix
                );
            } else {
                assert!(
                    text.contains(&format!("\"{}", family.prefix)),
                    "{} is a declared remainder but does not carry the literal {:?}, so the \
                     disclosure names a producer that no longer produces it",
                    path.display(),
                    family.prefix
                );
            }

            // A routed producer must actually construct a guard, and a declared remainder must
            // not. Without this the `routed` column is a comment: a producer could stop routing
            // while the table still claimed it did.
            let constructs_guard = text.contains("ScratchRoot::create");
            assert_eq!(
                constructs_guard,
                family.routed,
                "{} routed={} but constructs_guard={}: a routed producer must build a \
                 ScratchRoot and a declared remainder must not",
                path.display(),
                family.routed,
                constructs_guard
            );

            if family.routed {
                routed += 1;
            } else {
                remainder += 1;
            }
        }

        // Conservation, so the remainder cannot be emptied by deleting a row instead of by
        // routing its producer, and a floor so it cannot silently grow.
        assert_eq!(
            routed + remainder,
            SCRATCH_FAMILIES.len(),
            "every family is either routed or a declared remainder"
        );
        assert_eq!(
            remainder, 1,
            "the declared remainder is one row (kernel-ownership-publisher). A change here is a \
             decision: raise it deliberately with the reason, or lower it by routing a producer"
        );
        assert!(
            routed >= 4,
            "at least four producers route through ScratchRoot; found {routed}"
        );

        // Prefixes are distinct, and no prefix is a prefix of another — otherwise one family's
        // fence would admit another's roots and the `routed` column would not mean what it says.
        for (i, a) in SCRATCH_FAMILIES.iter().enumerate() {
            assert!(!a.prefix.is_empty(), "an empty prefix admits everything");
            for b in SCRATCH_FAMILIES.iter().skip(i + 1) {
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
