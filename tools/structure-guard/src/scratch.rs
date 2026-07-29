//! The fence moved to `fln-core` (bead `franken_lean-eir2`, Option B); this module
//! re-exports it so this crate's producers, probes and cited cells keep their names.
//!
//! # What lives here and why
//!
//! `s2sn` landed the reclaimer in this crate at `b0a52442` because every leaking
//! producer then known was in this crate. `eir2` censused six more producers outside
//! it and moved the machinery — [`ScratchRoot`], [`is_reclaimable`], the family table
//! — to `fln_core::scratch`, rank 0, which every producer crate already depends on.
//! Exactly one `Drop` body and one predicate exist across the workspace; nothing here
//! re-implements either. The module documentation, the measurement trap
//! (`st_blocks * 512`, never `st_size`), the retention semantics, and the declared
//! remainders with their reasons all live with the fence in `fln-core`.
//!
//! What stays in this file is what is *about* this crate: the manifest-cited cells
//! (`s2sn`'s coverage row cites four `test:structure-guard::lib::scratch::tests::*`
//! functions, which must keep resolving and running here) and the crate-local half
//! of the family binding — this crate's rows of the unified table bound to this
//! crate's sources. The workspace-wide half (every row, every `temp_dir` call site,
//! the site classification in both directions) is `scratch_reclamation_census` in
//! fln-conformance; deliberately narrower scope here, not a second copy of the rule.

pub use fln_core::scratch::{
    CLOSURE_PREFIX, HANDOFF_PREFIX, INVENTORY_PREFIX, PUBLISHER_PREFIX, SCRATCH_FAMILIES,
    SEEDED_PREFIX, ScratchFamily, ScratchRoot, is_reclaimable,
};

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::path::Path;

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
            "a prefix absent from SCRATCH_FAMILIES is refused even if the name matches it"
        );
        assert!(
            !is_reclaimable(
                &temp.join("fln-ownership-publisher-1-2-3"),
                PUBLISHER_PREFIX
            ),
            "a declared remainder's prefix is refused: the declaration says the fence \
             does not stand behind that namespace"
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
        // The crate-local half of the family binding: this crate's rows of the unified
        // table, bound to this crate's own sources. The workspace-wide half — every row,
        // every `std::env::temp_dir()` call site, the site classification in both
        // directions — is fln-conformance's `scratch_reclamation_census`, and this test
        // deliberately does not duplicate it: two copies of one census is
        // `franken_lean-evidence-python-config-rule-drift-imuu`'s defect.
        //
        // This module's source is deliberately NOT in any corpus below. A scan whose
        // search space contains its own declaration passes by reading itself, which is
        // the self-match shape `fln-8zsq` paid for; every hit here therefore comes from
        // a producer.
        //
        // The checked macro, not the raw compile-time manifest constant: that constant is
        // baked at build time, so a test binary built in one worktree and run in another
        // resolves these producers against the tree that COMPILED it while claiming to
        // describe the one running it (bead fln-cross-tree-baked-root-k60n).
        let workspace_root = fln_conformance::checked_workspace_root!();
        let workspace_root = workspace_root.as_path();

        let own: Vec<&ScratchFamily> = SCRATCH_FAMILIES
            .iter()
            .filter(|family| family.producer.starts_with("tools/structure-guard/"))
            .collect();
        assert_eq!(
            own.len(),
            5,
            "this crate declares exactly five scratch families (four routed, one \
             remainder); a sixth appears here only as a deliberate, disclosed act"
        );

        let mut routed = 0usize;
        let mut remainder = 0usize;
        for family in own {
            let path = workspace_root.join(family.producer);
            // assert-then-expect rather than `unwrap_or_else(|_| panic!(..))`: the message
            // needs the interpolated path, and `expect(&format!(..))` is what clippy's
            // `expect_fun_call` refuses. It also separates "the declared producer is
            // gone" from "it is unreadable", which are different failures of this table.
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

            // A ROUTED producer must bind its constant at the construction site; a
            // DECLARED REMAINDER cannot name the constant, and that is the whole reason
            // it is a remainder — `kernel-ownership-publisher` is a nested workspace
            // with no dependency on the fence's crate, so the identifier is unreachable
            // there and the literal is the only spelling available. Requiring the
            // constant of it would be a wall against the exact condition being
            // disclosed. So the needle is chosen by the row: constant when routed,
            // literal when not, and each direction is refused for the other kind.
            if family.routed {
                // The constant must be the FIRST ARGUMENT of the construction, not
                // merely present somewhere in the file. A blanket "the literal appears
                // nowhere" ban was tried first and is wrong: `tests/common/mod.rs`
                // legitimately writes `structure-guard-test-1-2-3-tag` as fence *test
                // input*, so that rule refused a correct file — a wall against the
                // practice it was meant to protect. Bind the call site instead, which
                // is the thing that could actually drift.
                assert!(
                    text.contains(&format!("ScratchRoot::create({}", family.constant)),
                    "{} is routed but never calls ScratchRoot::create({}); the declared \
                     prefix {:?} therefore has no producer binding it",
                    path.display(),
                    family.constant,
                    family.prefix
                );
            } else {
                assert!(
                    text.contains(&format!("\"{}", family.prefix)),
                    "{} is a declared remainder but does not carry the literal {:?}, so \
                     the disclosure names a producer that no longer produces it",
                    path.display(),
                    family.prefix
                );
            }

            // A routed producer must actually construct a guard, and a declared
            // remainder must not. Without this the `routed` column is a comment: a
            // producer could stop routing while the table still claimed it did.
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

        // Conservation, so the remainder cannot be emptied by deleting a row instead of
        // by routing its producer, and a floor so it cannot silently grow.
        assert_eq!(
            routed + remainder,
            5,
            "every one of this crate's five families is either routed or a declared \
             remainder"
        );
        assert_eq!(
            remainder, 1,
            "this crate's declared remainder is one row (kernel-ownership-publisher). A \
             change here is a decision: raise it deliberately with the reason, or lower \
             it by routing a producer"
        );
        assert_eq!(
            routed, 4,
            "exactly four of this crate's producers route through ScratchRoot; found \
             {routed}"
        );
    }
}
