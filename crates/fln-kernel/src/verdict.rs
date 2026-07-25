//! Domain verdicts and the resource algebra slice (plan §8.2b/§8.2c; beads
//! franken_lean-zht and franken_lean-1fxz).
//!
//! The kernel's one authority speaks in [`fln_core::outcome::Outcome<Verdict>`].
//! [`Verdict`] contains only completed domain answers: acceptance or a real
//! rejection. Budget exhaustion lives on the orthogonal operation-outcome axis, so
//! no caller can obtain a `Verdict` at all until it handles FL-INV-07's
//! non-authoritative cases.
//!
//! Bootstrap slice: receipts and the full typestate envelope (§8.2b) are follow-up
//! slices recorded on the bead; the verdict shape and the budget discipline are
//! final.

/// Stable rejection classes — cross-release comparable, KERNEL_CONTRACT-aligned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectClass {
    /// KR-100: loose bound variables reach the kernel.
    LooseBVar,
    /// KR-103: a metavariable reaches the kernel.
    MVarInKernel,
    /// KR-102: unknown free variable.
    UnknownFVar,
    /// KR-105: unknown constant, or level-arity mismatch.
    UnknownConstant,
    UniverseArityMismatch,
    /// KR-140-class: an undeclared universe parameter.
    UndefinedLevelParam,
    /// KR-106: the head of an application is not a function.
    FunctionExpected,
    /// KR-106/KR-109: an argument/value type failed defeq against the expected type.
    TypeMismatch,
    /// KR-107/108/109: a binder domain (or let type) is not a sort.
    SortExpected,
    /// KR-112: an ill-formed projection.
    InvalidProjection,
    /// KR-970: the one-name-one-constant law.
    AlreadyDeclared,
    /// KR-971: duplicate universe parameters.
    DuplicateLevelParams,
    /// KR-974: a theorem whose type is not a proposition.
    TheoremNotProp,
    /// The declared type and inferred body type are not defeq (KR-974).
    DefinitionTypeMismatch,
    /// The two sides are simply not definitionally equal (defeq query verdict).
    NotDefEq,
    /// KR-973 (pin type_checker.cpp:101/105): a non-unsafe context referenced an
    /// unsafe declaration, or a safe context referenced a partial definition.
    SafetyViolation,
    /// KR-6xx/95x/97x: a decoded declaration-block observable (flag, count,
    /// name list, generated recursor) does not match the kernel's own
    /// regeneration from the declaration.
    BlockMismatch,
}

impl RejectClass {
    pub fn as_str(self) -> &'static str {
        match self {
            RejectClass::LooseBVar => "loose_bvar",
            RejectClass::MVarInKernel => "mvar_in_kernel",
            RejectClass::UnknownFVar => "unknown_fvar",
            RejectClass::UnknownConstant => "unknown_constant",
            RejectClass::UniverseArityMismatch => "universe_arity_mismatch",
            RejectClass::UndefinedLevelParam => "undefined_level_param",
            RejectClass::FunctionExpected => "function_expected",
            RejectClass::TypeMismatch => "type_mismatch",
            RejectClass::SortExpected => "sort_expected",
            RejectClass::InvalidProjection => "invalid_projection",
            RejectClass::AlreadyDeclared => "already_declared",
            RejectClass::DuplicateLevelParams => "duplicate_level_params",
            RejectClass::TheoremNotProp => "theorem_not_prop",
            RejectClass::DefinitionTypeMismatch => "definition_type_mismatch",
            RejectClass::NotDefEq => "not_def_eq",
            RejectClass::SafetyViolation => "safety_violation",
            RejectClass::BlockMismatch => "block_mismatch",
        }
    }
}

/// The typed budget the caller hands the kernel (§8.2c slice: reduction/inference
/// steps and traversal depth). Exhaustion is an outcome about the run (KR-403),
/// never a [`Verdict`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Budget {
    /// Counted work steps (inference nodes + reduction steps + defeq queries).
    pub steps: u64,
    /// Maximum traversal depth. This is the bound that keeps the kernel's
    /// mutually recursive descent inside the caller's **native stack**: the
    /// kernel recurses on the host stack, and a stack overflow is the one
    /// failure FL-INV-07 cannot convert into a typed answer, because it aborts
    /// the process uncatchably. The safety therefore comes from the ceiling
    /// being provably below the floor, never from recovery — see
    /// [`Budget::depth_for_stack_bytes`].
    pub depth: u32,
}

impl Budget {
    /// Steps are a work bound, not a stack bound; they are independent of the
    /// stack calibration below and unchanged by it.
    pub const DEFAULT_STEPS: u64 = 10_000_000;

    /// The traversal depth [`Budget::DEFAULT`] offers.
    ///
    /// This one number is a **policy** choice — how much checking power the
    /// default hands a caller — and it is the only free parameter here.
    /// Everything else on this impl is measured or derived from it. Its cost
    /// is [`Budget::MIN_STACK_BYTES`], which is what a caller must actually
    /// provide; the pairing is asserted at compile time below.
    pub const DEFAULT_DEPTH: u32 = 4_096;

    /// **Measured** worst-case marginal native stack, in bytes, consumed per
    /// unit of [`Budget::depth`] (bead `franken_lean-kxbj`).
    ///
    /// A unit of depth is not a stack frame. `whnf` calls `whnf_core` at the
    /// *same* depth, `infer` calls `infer_core` at the same depth, and
    /// `is_def_eq` calls `quick_def_eq_rules` at the same depth, so one level
    /// of the ceiling buys several native frames of unknown width. This
    /// constant is therefore measured end-to-end rather than modelled from
    /// frame layouts: `crates/fln-kernel/tests/depth_stack_calibration.rs`
    /// bisects the deepest surviving descent at two known stack sizes for each
    /// of the four depth-threading descents (`forall` inference, `lam`
    /// inference, application-spine inference, defeq binder congruence) and
    /// takes the slope of the worst.
    ///
    /// Measured 2026-07-25 on `x86_64-unknown-linux-gnu` at the pinned
    /// nightly. The three inference descents all land on the same slope
    /// because the dominating cost is a single `infer_core` frame per level;
    /// defeq binder congruence is cheaper per level despite using two frames.
    ///
    /// | profile | worst shape    | bytes/depth |
    /// |---------|----------------|-------------|
    /// | `dev`   | `forall_infer` | 5_935       |
    /// | `release` | `forall_infer` | 640       |
    ///
    /// **The `dev` figure is the one shipped here**, deliberately: `cargo test`
    /// is the profile the Tribunal and every kernel replay actually run under,
    /// and it is 9.3x worse than `release`. Calibrating against the optimised
    /// build would leave the tested configuration unbounded.
    ///
    /// Rerun `cargo test -p fln-kernel --test depth_stack_calibration -- \
    /// --ignored --nocapture calibrate_stack_bytes_per_depth` after any change
    /// to the descent, and move this number if it moved. It is a `benchmark`
    /// class measurement (D7) on this target and toolchain; the safety factor
    /// below is what carries it to the ones we have not measured.
    pub const MEASURED_STACK_BYTES_PER_DEPTH: usize = 5_935;

    /// Stack consumed before the metered descent begins (the caller's own
    /// frames, the `check` entry path, `TypeChecker` construction). Measured
    /// as the intercept of the same two-point fit — 21.8 KiB worst case —
    /// and rounded up. Subtracted first so the per-level slope is never asked
    /// to absorb a fixed cost.
    pub const STACK_ENTRY_RESERVE_BYTES: usize = 64 * 1024;

    /// Multiplier applied to the measurement before deriving a stack
    /// requirement or a ceiling.
    ///
    /// The calibration is empirical over four planted descents on one target
    /// at one optimisation level; it is not a proof that no Corpus term is
    /// worse. This factor is what makes the derivation robust to a shape we
    /// did not plant, to a future rustc that widens a frame, and to a target
    /// whose ABI is fatter than this one.
    pub const STACK_SAFETY_FACTOR: usize = 2;

    /// The minimum usable native stack, in bytes, that [`Budget::DEFAULT`]
    /// requires of its caller's thread.
    ///
    /// This is a **requirement on the caller**, stated so it can be met rather
    /// than discovered by aborting. It is far above Rust's default spawned
    /// thread (2 MiB) and above a typical main thread (8 MiB), because
    /// `DEFAULT_DEPTH` at the measured `dev`-profile cost genuinely needs
    /// `4096 * 5935 * 2 + 64 KiB` = 46.4 MiB; 64 MiB is the next round,
    /// allocatable figure above it. Thread stacks are lazily committed, so
    /// this is address space, not resident memory.
    ///
    /// A caller who cannot provide it must not use `DEFAULT`. They call
    /// [`Budget::for_stack_bytes`] with the stack they actually have and get a
    /// correspondingly shallower — and safe — ceiling.
    pub const MIN_STACK_BYTES: usize = 64 * 1024 * 1024;

    /// The native stack a descent to `depth` requires, safety factor included.
    /// The inverse of [`Budget::depth_for_stack_bytes`].
    pub const fn stack_bytes_for_depth(depth: u32) -> usize {
        let per_level = Budget::MEASURED_STACK_BYTES_PER_DEPTH * Budget::STACK_SAFETY_FACTOR;
        (depth as usize) * per_level + Budget::STACK_ENTRY_RESERVE_BYTES
    }

    /// The largest depth ceiling that fits in `stack_bytes` of native stack,
    /// under the measured per-level cost and the safety factor.
    ///
    /// Monotone in `stack_bytes` and never zero: a caller with a tiny stack
    /// gets a ceiling of 1, which yields a typed depth non-answer on the first
    /// descent rather than an abort.
    pub const fn depth_for_stack_bytes(stack_bytes: usize) -> u32 {
        let usable = stack_bytes.saturating_sub(Budget::STACK_ENTRY_RESERVE_BYTES);
        let per_level = Budget::MEASURED_STACK_BYTES_PER_DEPTH * Budget::STACK_SAFETY_FACTOR;
        let depth = usable / per_level;
        if depth == 0 {
            1
        } else if depth > u32::MAX as usize {
            u32::MAX
        } else {
            depth as u32
        }
    }

    /// The budget for a caller with a **known** native stack.
    ///
    /// This is the constructor any caller running the kernel off a thread it
    /// created should use. `std::thread` defaults to 2 MiB — a quarter of the
    /// main thread and a small fraction of what `DEFAULT` needs — so a worker
    /// pool that inherits the default and passes `DEFAULT` is precisely the
    /// pairing that aborts. That pairing is the defect of bead
    /// `franken_lean-kxbj`, and this function is how a caller avoids it
    /// without having to know any of the constants above.
    pub const fn for_stack_bytes(stack_bytes: usize) -> Budget {
        Budget {
            steps: Budget::DEFAULT_STEPS,
            depth: Budget::depth_for_stack_bytes(stack_bytes),
        }
    }

    /// A generous default for interactive checking; callers with real budgets
    /// pass their own.
    ///
    /// Valid **only** on a thread carrying at least [`Budget::MIN_STACK_BYTES`]
    /// of stack. Do not raise `depth` without re-deriving that floor — the
    /// compile-time assertion below is what keeps the two in step.
    pub const DEFAULT: Budget = Budget {
        steps: Budget::DEFAULT_STEPS,
        depth: Budget::DEFAULT_DEPTH,
    };
}

/// The ceiling is below the floor, checked when the kernel compiles rather
/// than when a Corpus declaration happens to be deep enough to find out.
///
/// FL-INV-07 requires resource exhaustion to be a typed `Inconclusive`, and a
/// native stack overflow is the one exhaustion that cannot be — it aborts the
/// process uncatchably, so there is no "after the fact" in which to type it.
/// The guarantee has to be structural, and this is it.
const _: () = assert!(
    Budget::stack_bytes_for_depth(Budget::DEFAULT_DEPTH) <= Budget::MIN_STACK_BYTES,
    "Budget::DEFAULT_DEPTH needs more stack than Budget::MIN_STACK_BYTES promises: \
     raise the floor or lower the depth, but never leave them uncalibrated"
);

/// The two derivations must be mutual inverses at the shipped point, or one of
/// them is lying about the other.
const _: () = assert!(
    Budget::depth_for_stack_bytes(Budget::MIN_STACK_BYTES) >= Budget::DEFAULT_DEPTH,
    "the stack floor must admit at least the default depth"
);

/// What a completed run consumed — attached to every domain verdict (§8.2c).
/// An interrupted run instead reports the exceeded dimension through
/// [`fln_core::outcome::ResourceUsage`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Consumption {
    pub steps_used: u64,
    pub max_depth: u32,
}

/// Why a run could not finish (FL-INV-07: never a judgment about the term).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExhaustionReason {
    Steps,
    Depth,
}

/// The kernel's completed domain answer. Operation non-answers are represented only
/// by [`fln_core::outcome::Outcome`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The declaration is admitted. (Receipts: follow-up slice.)
    Accepted { consumption: Consumption },
    /// A real negative judgment about the term.
    Rejected {
        class: RejectClass,
        message: String,
        consumption: Consumption,
    },
}

impl Verdict {
    pub fn is_accepted(&self) -> bool {
        matches!(self, Verdict::Accepted { .. })
    }

    pub fn is_rejected(&self) -> bool {
        matches!(self, Verdict::Rejected { .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn completed_domain_answers_are_disjoint() {
        let consumption = Consumption::default();
        let accepted = Verdict::Accepted { consumption };
        let rejected = Verdict::Rejected {
            class: RejectClass::TypeMismatch,
            message: "x".into(),
            consumption,
        };
        assert!(accepted.is_accepted() && !accepted.is_rejected());
        assert!(rejected.is_rejected() && !rejected.is_accepted());
    }

    #[test]
    fn reject_classes_are_stable_strings() {
        let mut seen = std::collections::BTreeSet::new();
        for class in [
            RejectClass::LooseBVar,
            RejectClass::MVarInKernel,
            RejectClass::UnknownFVar,
            RejectClass::UnknownConstant,
            RejectClass::UniverseArityMismatch,
            RejectClass::UndefinedLevelParam,
            RejectClass::FunctionExpected,
            RejectClass::TypeMismatch,
            RejectClass::SortExpected,
            RejectClass::InvalidProjection,
            RejectClass::AlreadyDeclared,
            RejectClass::DuplicateLevelParams,
            RejectClass::TheoremNotProp,
            RejectClass::DefinitionTypeMismatch,
            RejectClass::NotDefEq,
            RejectClass::SafetyViolation,
            RejectClass::BlockMismatch,
        ] {
            assert!(seen.insert(class.as_str()), "duplicate class string");
        }
    }
}
