#![forbid(unsafe_code)]

//! Stack-budget ceilings for the inference result types (bead `franken_lean-gii.20`).
//!
//! `crates/fln-checker/tests/infer.rs` proves stack safety by running the
//! 50,000-binder lambda, forall and application cells on a **64 KiB** thread.
//! That budget is shared by every rule, and it is TIGHT: these types are
//! returned **by value** through the whole inference path, so widening one taxes
//! every rule at once.
//!
//! This was measured, not predicted. While implementing KR-109 (Let inference)
//! eight new `InferenceProgress` counters took that struct from 176 to 240 bytes
//! and `InferenceStop` from 224 to 288, and
//! `fifty_thousand_binder_forall_telescope_fits_a_64k_stack` — a **forall** test
//! the slice never touched — began overflowing its stack. The failure names a
//! rule that is not the one that changed, which is why a ceiling belongs here
//! rather than in a comment: without it the next person to add a counter learns
//! about the budget from an unrelated red.
//!
//! **These are ceilings, not targets.** Shrinking is always fine and the
//! assertions say so. Raising one is a deliberate act paid for out of the 64 KiB
//! budget, so re-run the deep-stack cells in `infer.rs` before moving a number
//! here — a ceiling is not a substitute for them, it is an early warning that
//! they are about to fail for a non-obvious reason.
//!
//! **What this does NOT establish:** a size is not a stack depth. These types
//! being small does not prove the deep-stack cells pass, and frame growth from
//! added code — not from a wider type — is invisible here. That is not
//! hypothetical: the KR-109 overflow survived restoring every size to its HEAD
//! value and was finally fixed by moving three `match` arms out of `run`'s
//! single frame.

use fln_checker::infer::{InferenceOutcome, InferenceProgress, InferenceResult, InferenceStop};

/// Measured at the KR-109 landing. `InferenceProgress` is embedded by value in
/// `InferenceStop`, which is embedded in `InferenceOutcome`, so the four move
/// together and are pinned together.
const PROGRESS_CEILING: usize = 176;
const STOP_CEILING: usize = 224;
const OUTCOME_CEILING: usize = 256;
const RESULT_CEILING: usize = 232;

fn assert_ceiling(name: &str, actual: usize, ceiling: usize) {
    assert!(
        actual <= ceiling,
        "{name} is {actual} bytes, over its {ceiling}-byte ceiling.\n\
         These types are returned BY VALUE through inference, and the deep-stack \
         cells in tests/infer.rs run on a 64 KiB thread with very little margin. \
         Growing this is why a *forall* test once began overflowing during a *let* \
         slice. Re-run fifty_thousand_binder_forall_telescope_fits_a_64k_stack, \
         fifty_thousand_binder_lambda_telescope_fits_a_64k_stack and \
         fifty_thousand_argument_spine_fits_a_64k_stack before raising it."
    );
}

#[test]
fn inference_result_types_stay_within_their_stack_budget() {
    assert_ceiling(
        "InferenceProgress",
        size_of::<InferenceProgress>(),
        PROGRESS_CEILING,
    );
    assert_ceiling("InferenceStop", size_of::<InferenceStop>(), STOP_CEILING);
    assert_ceiling(
        "InferenceOutcome",
        size_of::<InferenceOutcome>(),
        OUTCOME_CEILING,
    );
    assert_ceiling(
        "InferenceResult",
        size_of::<InferenceResult>(),
        RESULT_CEILING,
    );
}

/// Anti-vacuity: a ceiling nothing could ever exceed is decoration.
///
/// This refuses a ceiling that has drifted far above what the type actually
/// costs, which is how a ceiling silently stops guarding.
#[test]
fn the_ceilings_are_tight_enough_to_bind() {
    let slack = PROGRESS_CEILING.saturating_sub(size_of::<InferenceProgress>());
    assert!(
        slack <= 64,
        "InferenceProgress has {slack} bytes of unused ceiling; a ceiling that far \
         above the measured size no longer refuses the growth it exists to refuse. \
         Lower it to the measured size."
    );
}
