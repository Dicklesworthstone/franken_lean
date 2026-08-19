//! Domain verdicts and the resource algebra slice (plan §8.2b/§8.2c; beads
//! franken_lean-zht, franken_lean-1fxz, franken_lean-kxbj and
//! franken_lean-4o3n).
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

// ---------------------------------------------------------------------------
// Calibration — what a bound is DERIVED from (bead `franken_lean-4o3n`)
// ---------------------------------------------------------------------------
//
// The one sentence this section exists for, and it is cc_3's:
//
//     Two engines can report identical fuel while neither measured it in the
//     configuration it actually executes in, and the agreement then certifies
//     nothing.
//
// The measurement on record makes that concrete rather than theoretical. Bead
// `franken_lean-kxbj` measured this kernel's marginal native stack cost at
// 5,935 bytes per unit of depth in the `dev` profile and 640 in `release` — the
// same code, the same target, the same `depth = 4096`, a 9.3x gap in what that
// number COSTS. So "both engines ran at depth 4096" is agreement about a
// LABEL. It says nothing about a resource, and a seat that reads it as
// agreement about a resource has certified nothing while appearing to certify
// parity.
//
// Everything below exists so that a bound cannot be stated without the
// configuration it was measured in, and so that two bounds cannot be compared
// until that configuration has been established comparable. Parity here is
// parity of the *derivation*, never parity of the number.

/// Compile-time string equality, so configurations can be compared in `const`
/// contexts as well as at run time.
const fn str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// The smallest power of two at or above `n`. Written out rather than taken
/// from `usize::next_power_of_two` so the derivation of
/// [`Budget::MIN_STACK_BYTES`] is visible in the same file that justifies it.
const fn round_up_to_power_of_two(n: usize) -> usize {
    let mut p: usize = 1;
    while p < n {
        p *= 2;
    }
    p
}

/// Which engine's frames a measurement is of — and therefore which engine a
/// bound derived from it is a claim about.
///
/// Deliberately not [`crate::council::SeatId`]. A seat id names *who is
/// speaking*: two seats can be two runs of one engine, and a seat can be a
/// subprocess with no measurement at all. This names the **code that was
/// measured**, which is the only thing a depth ceiling is a statement about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineId(&'static str);

impl EngineId {
    /// The certified small-step engine in this crate — the only engine that
    /// exists today (`fln-checker` is an independence boundary and a schema,
    /// not an implementation that decides verdicts).
    pub const K1: EngineId = EngineId("fln-kernel/k1");

    /// Name another engine. Public because a second engine has to be able to
    /// state its own identity, and stating one grants nothing — exactly as
    /// stating a [`crate::council::SeatVerdict`] grants nothing.
    pub const fn named(name: &'static str) -> EngineId {
        EngineId(name)
    }

    pub const fn as_str(self) -> &'static str {
        self.0
    }

    pub const fn is(self, other: EngineId) -> bool {
        str_eq(self.0, other.0)
    }
}

/// Optimisation posture of the build a measurement was taken in, or that a
/// budget is derived for.
///
/// `debug_assertions` is a **proxy** for "unoptimised", and it is named as one
/// rather than presented as a fact about `opt-level`: a crate cannot see its own
/// optimisation level, and a profile that turns debug assertions off while
/// leaving optimisation off would be classified `Release` here and would get a
/// ceiling too generous for its frames. It is the right proxy for the measured
/// 9.3x gap — that gap is exactly `cargo test` versus `cargo test --release` —
/// and it is honest about being one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Profile {
    Dev,
    Release,
}

impl Profile {
    /// The profile THIS build was compiled under.
    ///
    /// Spelled with `#[cfg]` rather than `cfg!`: FLN-STRUCT-030 admits the
    /// `cfg` *attribute* into the kernel's reviewed builtin inventory and not
    /// the `cfg!` macro, because an attribute deletes the other arm before it
    /// is compiled while the macro leaves both in the LOC-counted body.
    #[cfg(debug_assertions)]
    pub const fn current() -> Profile {
        Profile::Dev
    }

    /// See the `debug_assertions` arm above; exactly one of the two exists in
    /// any build.
    #[cfg(not(debug_assertions))]
    pub const fn current() -> Profile {
        Profile::Release
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Profile::Dev => "dev",
            Profile::Release => "release",
        }
    }
}

/// The execution configuration a measurement was taken in — and therefore the
/// only configuration a bound derived from it describes.
///
/// Three axes, each of which moved the measured number in practice or can be
/// shown to: the optimisation posture (measured, 9.3x), and the target's
/// architecture and OS (frame layout and ABI). A budget that travels without
/// these is a number, and the whole defect class this type exists for is
/// numbers that look like bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecConfig {
    pub profile: Profile,
    pub arch: &'static str,
    pub os: &'static str,
}

impl ExecConfig {
    /// The configuration THIS build runs in, resolved entirely at compile time.
    /// No I/O: `std::env::consts` are constants baked in by rustc, not a
    /// lookup, so this respects the kernel's zero-I/O covenant (§8.1).
    pub const fn current() -> ExecConfig {
        ExecConfig {
            profile: Profile::current(),
            arch: std::env::consts::ARCH,
            os: std::env::consts::OS,
        }
    }

    pub const fn of(profile: Profile, arch: &'static str, os: &'static str) -> ExecConfig {
        ExecConfig { profile, arch, os }
    }

    /// Configuration equality, usable in `const` contexts.
    pub const fn is(self, other: ExecConfig) -> bool {
        matches!(
            (self.profile, other.profile),
            (Profile::Dev, Profile::Dev) | (Profile::Release, Profile::Release)
        ) && str_eq(self.arch, other.arch)
            && str_eq(self.os, other.os)
    }

    /// A stable one-line rendering for halts, refusals and logs.
    pub fn describe(self) -> String {
        format!("{}/{}/{}", self.profile.as_str(), self.arch, self.os)
    }
}

/// A **measured** native-stack cost for one engine, taken in one stated
/// configuration.
///
/// A unit of depth is not a stack frame. In this kernel `whnf` calls
/// `whnf_core` at the *same* depth, `infer` calls `infer_core` at the same
/// depth, and `is_def_eq` calls `quick_def_eq_rules` at the same depth, so one
/// level of the ceiling buys several native frames of unknown width. The
/// quantity is therefore measured end to end rather than modelled from frame
/// layouts — see `crates/fln-kernel/tests/depth_stack_calibration.rs`, which
/// bisects the deepest surviving descent at two known stack sizes for each of
/// the four depth-threading descents and takes the slope of the worst.
///
/// A second engine does **not** inherit these numbers. It is different code
/// with different frames, and handing it this kernel's ceiling because that is
/// the constant in this file is precisely the copied-number defect: either
/// unsafe for it or artificially shallow, and artificially shallow manufactures
/// the non-answers that erode a consensus seat.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StackMeasurement {
    engine: EngineId,
    taken_in: ExecConfig,
    bytes_per_depth: usize,
    entry_reserve_bytes: usize,
    safety_factor: usize,
}

impl StackMeasurement {
    /// Record a measurement. Every field is required: an engine that cannot say
    /// what it measured, where, cannot be established comparable with anything.
    pub const fn measured(
        engine: EngineId,
        taken_in: ExecConfig,
        bytes_per_depth: usize,
        entry_reserve_bytes: usize,
        safety_factor: usize,
    ) -> StackMeasurement {
        StackMeasurement {
            engine,
            taken_in,
            // A zero slope would make every ceiling infinite; refuse it here
            // rather than let it become an unbounded descent downstream.
            bytes_per_depth: if bytes_per_depth == 0 {
                1
            } else {
                bytes_per_depth
            },
            entry_reserve_bytes,
            safety_factor: if safety_factor == 0 { 1 } else { safety_factor },
        }
    }

    /// Stack consumed before the metered descent begins — the caller's own
    /// frames, the `check` entry path, `TypeChecker` construction. Measured as
    /// the intercept of the two-point fit (21.8 KiB worst case) and rounded up.
    /// Subtracted first so the per-level slope is never asked to absorb a fixed
    /// cost.
    pub const K1_ENTRY_RESERVE_BYTES: usize = 64 * 1024;

    /// Multiplier applied to a measurement before deriving a stack requirement
    /// or a ceiling.
    ///
    /// The calibration is empirical over four planted descents on one target at
    /// one optimisation level; it is not a proof that no Corpus term is worse.
    /// This factor is what makes the derivation robust to a shape we did not
    /// plant and to a future rustc that widens a frame. It is explicitly NOT
    /// what carries a measurement to a *different configuration*: that is what
    /// [`Grade::Extrapolated`] records, and an extrapolated bound is never
    /// established comparable.
    pub const K1_SAFETY_FACTOR: usize = 2;

    /// K1 measured in the `dev` profile on `x86_64-unknown-linux-gnu` at the
    /// pinned nightly, 2026-08-15, after the KR-311 right-nested heap walk.
    ///
    /// | shape                        | bytes/depth |
    /// |------------------------------|-------------|
    /// | `defeq_proj` (worst residual)| 3_567       |
    ///
    /// Converted inference/defeq spines (forall, right-nested app infer,
    /// projection infer, right-nested app congruence) are heap walks and no
    /// longer belong in this table. The residual is cheap-proj WHNF of a
    /// `.1.1.1` nest. Re-measured by
    /// `calibrate_stack_bytes_per_depth` (1 MiB → 288, 4 MiB → 1170).
    ///
    /// Rerun `cargo test -p fln-kernel --test depth_stack_calibration --
    /// --ignored --nocapture calibrate_stack_bytes_per_depth` after any change
    /// to the descent, and move this number if it moved. `benchmark` class (D7)
    /// on this target and toolchain.
    pub const K1_DEV: StackMeasurement = StackMeasurement::measured(
        EngineId::K1,
        ExecConfig::of(Profile::Dev, "x86_64", "linux"),
        3_567,
        StackMeasurement::K1_ENTRY_RESERVE_BYTES,
        StackMeasurement::K1_SAFETY_FACTOR,
    );

    /// K1 measured in the `release` profile on 2026-07-25 — 640 bytes per
    /// depth, 5.6x cheaper than [`StackMeasurement::K1_DEV`] for the
    /// identical depth number. This pair IS the bead: same label, different
    /// resource. The release figure was not re-run on 2026-08-15; only the
    /// residual `dev` descent moved.
    pub const K1_RELEASE: StackMeasurement = StackMeasurement::measured(
        EngineId::K1,
        ExecConfig::of(Profile::Release, "x86_64", "linux"),
        640,
        StackMeasurement::K1_ENTRY_RESERVE_BYTES,
        StackMeasurement::K1_SAFETY_FACTOR,
    );

    /// The K1 measurement for the profile this build was compiled under.
    ///
    /// Selected rather than fixed. Shipping the `dev` figure unconditionally
    /// would be *safe* — it is the worse of the two — but it would make the
    /// provenance lie in a release build, claiming a cost that was measured
    /// somewhere else. A bound whose provenance is wrong in the safe direction
    /// is still a bound nobody can compare.
    pub const fn k1_here() -> StackMeasurement {
        match Profile::current() {
            Profile::Dev => StackMeasurement::K1_DEV,
            Profile::Release => StackMeasurement::K1_RELEASE,
        }
    }

    pub const fn engine(self) -> EngineId {
        self.engine
    }

    pub const fn taken_in(self) -> ExecConfig {
        self.taken_in
    }

    pub const fn bytes_per_depth(self) -> usize {
        self.bytes_per_depth
    }

    pub const fn entry_reserve_bytes(self) -> usize {
        self.entry_reserve_bytes
    }

    pub const fn safety_factor(self) -> usize {
        self.safety_factor
    }

    /// The native stack a descent to `depth` requires under this measurement,
    /// safety factor included. The inverse of
    /// [`StackMeasurement::depth_for_stack_bytes`].
    pub const fn stack_bytes_for_depth(self, depth: u32) -> usize {
        let per_level = self.bytes_per_depth * self.safety_factor;
        (depth as usize) * per_level + self.entry_reserve_bytes
    }

    /// The largest depth ceiling that fits in `stack_bytes` under this
    /// measurement.
    ///
    /// Monotone in `stack_bytes` and never zero: a caller with a tiny stack
    /// gets a ceiling of 1, which yields a typed depth non-answer on the first
    /// descent rather than an abort.
    pub const fn depth_for_stack_bytes(self, stack_bytes: usize) -> u32 {
        let usable = stack_bytes.saturating_sub(self.entry_reserve_bytes);
        let per_level = self.bytes_per_depth * self.safety_factor;
        let depth = usable / per_level;
        if depth == 0 {
            1
        } else if depth > u32::MAX as usize {
            u32::MAX
        } else {
            depth as u32
        }
    }
}

/// How much a bound's number is worth where it is being used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grade {
    /// The measurement was taken in the configuration this bound runs in. The
    /// number is a measured resource.
    Measured,
    /// The measurement was taken somewhere else and carried here by the safety
    /// factor. Safe to *run* under — that is what the factor is for — and never
    /// comparable, because "safe by a factor we chose" and "measured" are not
    /// the same claim and only one of them supports certifying parity.
    Extrapolated,
}

/// The provenance a budget carries: which engine's measurement it came from,
/// where that measurement was taken, and which configuration and stack it was
/// derived FOR.
///
/// A budget without this is the same defect class as a `ProofCheckReceipt`
/// binding counts and no content (bead `fln-46mw`): a number that looks like
/// evidence and is not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Calibration {
    measurement: StackMeasurement,
    running_in: ExecConfig,
    stack_bytes: usize,
}

impl Calibration {
    /// The engine this bound is a claim about.
    pub const fn engine(self) -> EngineId {
        self.measurement.engine()
    }

    pub const fn measurement(self) -> StackMeasurement {
        self.measurement
    }

    /// The configuration the bound was derived for — i.e. where the run it
    /// governs is expected to happen.
    pub const fn running_in(self) -> ExecConfig {
        self.running_in
    }

    /// The native stack the derivation assumed. A *requirement on the caller*,
    /// stated so it can be met rather than discovered by aborting.
    pub const fn stack_bytes(self) -> usize {
        self.stack_bytes
    }

    pub const fn grade(self) -> Grade {
        if self.measurement.taken_in().is(self.running_in) {
            Grade::Measured
        } else {
            Grade::Extrapolated
        }
    }

    pub fn describe(self) -> String {
        format!(
            "engine={} measured_in={} running_in={} bytes_per_depth={} safety_factor={} \
             assumed_stack_bytes={}",
            self.engine().as_str(),
            self.measurement.taken_in().describe(),
            self.running_in.describe(),
            self.measurement.bytes_per_depth(),
            self.measurement.safety_factor(),
            self.stack_bytes,
        )
    }
}

/// Which bound a run stopped on. Public vocabulary, because a seat has to be
/// able to say *which* limit it hit — "disagreed" and "ran out" are different
/// facts, and "ran out of steps" and "ran out of depth" are different facts
/// again.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bound {
    /// The counted-work bound.
    ///
    /// Engine-local by nature: a step in a small-step checker is not a step in
    /// an NbE evaluator, so two step *numbers* are never comparable even when
    /// both engines are honest. Only the outcome — this engine ran out — is a
    /// fact about the world.
    Steps,
    /// The traversal-depth bound: the one calibrated against native stack, and
    /// the one whose cost is measured by [`StackMeasurement`].
    Depth,
    /// A bound this vocabulary does not name, stated by whoever hit it — a wall
    /// clock, a heap ceiling, a foreign checker's own limit. Open on purpose: a
    /// closed enum would force a foreign engine to misreport.
    Other(String),
}

impl Bound {
    pub fn describe(&self) -> String {
        match self {
            Bound::Steps => "steps".to_string(),
            Bound::Depth => "depth".to_string(),
            Bound::Other(what) => what.clone(),
        }
    }
}

/// Why a budget may not govern a particular run.
///
/// Both arms are refusals to *start*, not diagnoses after the fact. The depth
/// ceiling is the only thing standing between a legitimately deep term and a
/// native stack overflow, and a stack overflow is the one exhaustion FL-INV-07
/// cannot convert into a typed answer, because it aborts the process
/// uncatchably. So a ceiling whose derivation does not apply here must be
/// refused before the first descent, never audited afterwards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetObjection {
    /// The bound was derived from a measurement of a different engine. Its
    /// number says nothing about this engine's frames.
    CalibratedForAnotherEngine {
        calibrated_for: EngineId,
        running: EngineId,
    },
    /// The bound was derived for a different configuration than the one it is
    /// about to run in. This is the 9.3x case: a `release`-derived depth in a
    /// `dev` build is a ceiling nine times above the floor.
    CalibratedForAnotherConfiguration {
        calibrated_for: ExecConfig,
        running: ExecConfig,
    },
}

impl BudgetObjection {
    pub fn describe(&self) -> String {
        match self {
            BudgetObjection::CalibratedForAnotherEngine {
                calibrated_for,
                running,
            } => format!(
                "budget is calibrated for engine `{}` but would govern `{}`: a depth ceiling \
                 derived from another engine's frames is a number, not a bound",
                calibrated_for.as_str(),
                running.as_str()
            ),
            BudgetObjection::CalibratedForAnotherConfiguration {
                calibrated_for,
                running,
            } => format!(
                "budget is calibrated for configuration {} but would run in {}: the same depth \
                 costs a different amount of native stack in each, so the ceiling is not known \
                 to be below the floor",
                calibrated_for.describe(),
                running.describe()
            ),
        }
    }
}

/// Whether two bounds may have their OUTCOMES compared.
///
/// Never their numbers. Establishing comparability licenses reading "engine A
/// ran out where engine B did not" as a fact about the two engines; it never
/// licenses reading "A allowed 4096 and B allowed 4096" as agreement, because
/// that is the vacuity this whole section exists to prevent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comparability {
    /// Each bound was derived from a measurement of its own engine, taken in
    /// the configuration that engine actually runs in, and both run in the same
    /// configuration.
    Established,
    /// Not established. **Nothing** may be concluded from a difference between
    /// the two outcomes — not that the engines disagree, and not that a stop
    /// is a spurious artifact of asymmetric bounds. Both readings are claims
    /// about a comparison that did not happen.
    NotEstablished(ComparabilityDefect),
}

/// Why two bounds could not be established comparable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComparabilityDefect {
    /// Both bounds are calibrated for the same engine. An engine cannot
    /// corroborate itself, and two copies of one measurement agreeing is
    /// agreement with itself.
    SameEngine { engine: EngineId },
    /// One side's measurement was not taken where that side runs, so its number
    /// is carried by a safety factor rather than measured. Honest, safe to run
    /// under, and not comparable.
    NotMeasuredWhereItRuns {
        engine: EngineId,
        taken_in: ExecConfig,
        running_in: ExecConfig,
    },
    /// The two sides run in different configurations. The bead's headline case:
    /// identical depth numbers, incomparable resources.
    RunsInDifferentConfigurations { a: ExecConfig, b: ExecConfig },
}

impl ComparabilityDefect {
    pub fn describe(&self) -> String {
        match self {
            ComparabilityDefect::SameEngine { engine } => format!(
                "both bounds are calibrated for engine `{}`; an engine cannot corroborate itself",
                engine.as_str()
            ),
            ComparabilityDefect::NotMeasuredWhereItRuns {
                engine,
                taken_in,
                running_in,
            } => format!(
                "engine `{}` runs in {} but its measurement was taken in {}: the bound is \
                 extrapolated by a safety factor, not measured where it runs",
                engine.as_str(),
                running_in.describe(),
                taken_in.describe()
            ),
            ComparabilityDefect::RunsInDifferentConfigurations { a, b } => format!(
                "the two bounds run in different configurations ({} vs {}): the same depth \
                 number costs a different resource in each",
                a.describe(),
                b.describe()
            ),
        }
    }
}

impl Comparability {
    /// Establish — or refuse to establish — that two bounds may have their
    /// outcomes compared.
    ///
    /// The checks run in a fixed order so the reported defect is deterministic
    /// (FL-INV-01) when a pair has more than one: self-comparison first,
    /// because it invalidates the exercise entirely; then each side's own
    /// grade, in argument order; then the cross-configuration check, which is
    /// the only one that is a property of the pair rather than of a side.
    pub fn establish(a: &Budget, b: &Budget) -> Comparability {
        let (ca, cb) = (a.calibration(), b.calibration());
        if ca.engine().is(cb.engine()) {
            return Comparability::NotEstablished(ComparabilityDefect::SameEngine {
                engine: ca.engine(),
            });
        }
        for c in [ca, cb] {
            if c.grade() == Grade::Extrapolated {
                return Comparability::NotEstablished(
                    ComparabilityDefect::NotMeasuredWhereItRuns {
                        engine: c.engine(),
                        taken_in: c.measurement().taken_in(),
                        running_in: c.running_in(),
                    },
                );
            }
        }
        if !ca.running_in().is(cb.running_in()) {
            return Comparability::NotEstablished(
                ComparabilityDefect::RunsInDifferentConfigurations {
                    a: ca.running_in(),
                    b: cb.running_in(),
                },
            );
        }
        Comparability::Established
    }

    pub const fn is_established(&self) -> bool {
        matches!(self, Comparability::Established)
    }

    pub const fn defect(&self) -> Option<ComparabilityDefect> {
        match self {
            Comparability::Established => None,
            Comparability::NotEstablished(defect) => Some(*defect),
        }
    }
}

/// The typed budget the caller hands the kernel (§8.2c slice: reduction/inference
/// steps and traversal depth). Exhaustion is an outcome about the run (KR-403),
/// never a [`Verdict`].
///
/// The allowances are public and readable; the [`Calibration`] is private and
/// travels with them. That asymmetry is the point: there is no struct-literal
/// expression for a `Budget` outside this crate, so no engine can hand itself a
/// ceiling it did not derive from a stated measurement. `depth` can still be
/// *read* by anyone — a bound nobody can inspect would be its own problem.
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
    /// Where the ceiling came from. Private so it cannot be detached from the
    /// number it justifies.
    calibration: Calibration,
}

impl Budget {
    /// Steps are a work bound, not a stack bound; they are independent of the
    /// stack calibration and unchanged by it. They are also **engine-local**:
    /// see [`Bound::Steps`] for why a step count is never comparable across
    /// engines even when both engines are honest.
    pub const DEFAULT_STEPS: u64 = 10_000_000;

    /// The traversal depth [`Budget::DEFAULT`] offers.
    ///
    /// This one number is a **policy** choice — how much checking power the
    /// default hands a caller — and it is the only free parameter here.
    /// Everything else is measured or derived from it. Its cost is
    /// [`Budget::MIN_STACK_BYTES`], which is what a caller must actually
    /// provide; the pairing is asserted at compile time below.
    pub const DEFAULT_DEPTH: u32 = 4_160;

    /// The measured marginal native stack per unit of depth for THIS engine in
    /// THIS build's profile. See [`StackMeasurement::k1_here`].
    pub const MEASURED_STACK_BYTES_PER_DEPTH: usize = StackMeasurement::k1_here().bytes_per_depth();

    /// See [`StackMeasurement::K1_ENTRY_RESERVE_BYTES`].
    pub const STACK_ENTRY_RESERVE_BYTES: usize = StackMeasurement::K1_ENTRY_RESERVE_BYTES;

    /// See [`StackMeasurement::K1_SAFETY_FACTOR`].
    pub const STACK_SAFETY_FACTOR: usize = StackMeasurement::K1_SAFETY_FACTOR;

    /// The minimum usable native stack, in bytes, that [`Budget::DEFAULT`]
    /// requires of its caller's thread.
    ///
    /// A **requirement on the caller**, stated so it can be met rather than
    /// discovered by aborting. Derived, not chosen: it is exactly the stack
    /// `DEFAULT_DEPTH` needs under the current profile's measurement, rounded
    /// up to the next power of two. In the `dev` profile that is
    /// `4160 * 3567 * 2 + 64 KiB` = 28.4 MiB, rounded to **32 MiB** — far above
    /// Rust's default spawned thread (2 MiB) and above a typical main thread
    /// (8 MiB). Thread stacks are lazily committed, so this is address space,
    /// not resident memory.
    ///
    /// A caller who cannot provide it must not use `DEFAULT`. They call
    /// [`Budget::for_stack_bytes`] with the stack they actually have and get a
    /// correspondingly shallower — and safe — ceiling.
    pub const MIN_STACK_BYTES: usize = round_up_to_power_of_two(
        StackMeasurement::k1_here().stack_bytes_for_depth(Budget::DEFAULT_DEPTH),
    );

    /// The native stack a K1 descent to `depth` requires in this build, safety
    /// factor included.
    pub const fn stack_bytes_for_depth(depth: u32) -> usize {
        StackMeasurement::k1_here().stack_bytes_for_depth(depth)
    }

    /// The largest K1 depth ceiling that fits in `stack_bytes` in this build.
    pub const fn depth_for_stack_bytes(stack_bytes: usize) -> u32 {
        StackMeasurement::k1_here().depth_for_stack_bytes(stack_bytes)
    }

    /// Derive a budget from a measurement — the only way to make one.
    ///
    /// `running_in` is stated rather than assumed to be [`ExecConfig::current`]
    /// so that a budget for a run happening somewhere else (a subprocess
    /// witness, a worker built differently) is *representable and marked*
    /// rather than quietly mislabelled. The kernel refuses to run under a
    /// budget whose `running_in` is not this process — see
    /// [`Budget::objection_to_governing`] — so representing one costs nothing
    /// and lets a comparison say precisely what is wrong with it.
    pub const fn derive(
        measurement: StackMeasurement,
        running_in: ExecConfig,
        stack_bytes: usize,
        steps: u64,
    ) -> Budget {
        Budget {
            steps,
            depth: measurement.depth_for_stack_bytes(stack_bytes),
            calibration: Calibration {
                measurement,
                running_in,
                stack_bytes,
            },
        }
    }

    /// The budget for a caller with a **known** native stack, running this
    /// kernel in this process.
    ///
    /// This is the constructor any caller running the kernel off a thread it
    /// created should use. `std::thread` defaults to 2 MiB — a quarter of the
    /// main thread and a small fraction of what `DEFAULT` needs — so a worker
    /// pool that inherits the default and passes `DEFAULT` is precisely the
    /// pairing that aborts. That pairing is the defect of bead
    /// `franken_lean-kxbj`, and this function is how a caller avoids it without
    /// having to know any of the constants above.
    pub const fn for_stack_bytes(stack_bytes: usize) -> Budget {
        Budget::derive(
            StackMeasurement::k1_here(),
            ExecConfig::current(),
            stack_bytes,
            Budget::DEFAULT_STEPS,
        )
    }

    /// A budget for the CALIBRATION INSTRUMENT: a ceiling that is *stated*
    /// rather than derived, together with the stack the instrument claims to be
    /// running on.
    ///
    /// The one place in the program where a depth does not come out of a
    /// measurement, and it has to be one. An instrument that could only ask for
    /// depths the current constants already call safe could never discover that
    /// they are not — it would confirm the number it was given. So the
    /// instrument states a claim ("this depth is survivable on this stack") and
    /// the experiment finds out; see
    /// `crates/fln-kernel/tests/depth_stack_calibration.rs`, which runs exactly
    /// this in a subprocess and reads the exit status.
    ///
    /// It is still calibrated in the two senses [`Budget::objection_to_governing`]
    /// checks — K1's own engine, this process's configuration — so the kernel
    /// runs under it. What it is not is *derived*, and its name says so.
    pub const fn stated_for_measurement(steps: u64, depth: u32, stack_bytes: usize) -> Budget {
        Budget {
            steps,
            depth,
            calibration: Calibration {
                measurement: StackMeasurement::k1_here(),
                running_in: ExecConfig::current(),
                stack_bytes,
            },
        }
    }

    /// The provenance travelling with this bound.
    pub const fn calibration(&self) -> Calibration {
        self.calibration
    }

    /// The engine this bound is a claim about.
    pub const fn engine(&self) -> EngineId {
        self.calibration.engine()
    }

    /// Lower the allowances, keeping the derivation.
    ///
    /// Lowering is always safe: a shallower ceiling needs less stack than the
    /// calibration already promised. Raising is not, so both arguments are
    /// clamped rather than trusted — this is how the kernel's own internal
    /// re-budgeting (remaining steps after a header check) stays inside the
    /// derivation instead of quietly reconstructing a budget beside it.
    pub const fn narrowed(self, steps: u64, depth: u32) -> Budget {
        Budget {
            steps: if steps < self.steps {
                steps
            } else {
                self.steps
            },
            depth: if depth < self.depth {
                depth
            } else {
                self.depth
            },
            calibration: self.calibration,
        }
    }

    /// Why this budget may not govern a run of `engine` in this process, if it
    /// may not.
    ///
    /// Two refusals, both structural rather than advisory — see
    /// [`BudgetObjection`]. Note what is deliberately NOT refused: an
    /// [`Grade::Extrapolated`] bound, whose measurement was taken on another
    /// target. Refusing that would make the kernel unusable on every target we
    /// have not yet measured, and the safety factor exists precisely to carry
    /// it there. It cannot be established comparable, which is the honest
    /// consequence and is recorded by [`Comparability`] rather than here.
    pub fn objection_to_governing(&self, engine: EngineId) -> Option<BudgetObjection> {
        if !self.calibration.engine().is(engine) {
            return Some(BudgetObjection::CalibratedForAnotherEngine {
                calibrated_for: self.calibration.engine(),
                running: engine,
            });
        }
        if !self.calibration.running_in().is(ExecConfig::current()) {
            return Some(BudgetObjection::CalibratedForAnotherConfiguration {
                calibrated_for: self.calibration.running_in(),
                running: ExecConfig::current(),
            });
        }
        None
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
        calibration: Calibration {
            measurement: StackMeasurement::k1_here(),
            running_in: ExecConfig::current(),
            stack_bytes: Budget::MIN_STACK_BYTES,
        },
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

/// The default must be calibrated for the engine that runs it. If this ever
/// fails, `DEFAULT` was built from another engine's measurement — the exact
/// copied-number defect bead `franken_lean-4o3n` exists to make impossible.
const _: () = assert!(
    Budget::DEFAULT
        .calibration
        .measurement
        .engine
        .is(EngineId::K1),
    "Budget::DEFAULT must be derived from a measurement of K1's own frames"
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

    /// The two K1 measurements are the bead's evidence, and they must keep
    /// disagreeing about what one depth costs. If they ever converge, either
    /// somebody normalised them by hand or the profiles stopped differing —
    /// both worth noticing, because the whole argument rests on this gap.
    #[test]
    fn the_two_profiles_do_not_agree_about_what_one_depth_costs() {
        let dev = StackMeasurement::K1_DEV;
        let release = StackMeasurement::K1_RELEASE;
        assert!(dev.engine() == release.engine());
        assert!(dev.taken_in() != release.taken_in());
        assert!(
            dev.bytes_per_depth() > release.bytes_per_depth() * 5,
            "the measured dev/release gap is the evidence that a depth number is not a \
             resource: dev={} release={}",
            dev.bytes_per_depth(),
            release.bytes_per_depth()
        );
        assert!(
            dev.stack_bytes_for_depth(Budget::DEFAULT_DEPTH)
                != release.stack_bytes_for_depth(Budget::DEFAULT_DEPTH),
            "identical depth, identical cost would mean the profile does not matter"
        );
    }

    /// Narrowing keeps the derivation and cannot be used to widen it.
    #[test]
    fn narrowing_lowers_and_never_raises() {
        let base = Budget::DEFAULT;
        let narrowed = base.narrowed(10, 7);
        assert!(narrowed.steps == 10 && narrowed.depth == 7);
        assert!(narrowed.calibration() == base.calibration());

        let widened = base.narrowed(u64::MAX, u32::MAX);
        assert!(
            widened.steps == base.steps && widened.depth == base.depth,
            "narrowed() must clamp rather than trust its arguments"
        );
    }

    /// A zero slope would make every ceiling infinite. The constructor refuses
    /// it at the point of statement rather than letting it become an unbounded
    /// descent later.
    #[test]
    fn a_degenerate_measurement_cannot_produce_an_infinite_ceiling() {
        let degenerate = StackMeasurement::measured(
            EngineId::named("degenerate"),
            ExecConfig::current(),
            0,
            0,
            0,
        );
        assert!(degenerate.bytes_per_depth() >= 1);
        assert!(degenerate.safety_factor() >= 1);
        assert!(degenerate.depth_for_stack_bytes(usize::MAX) == u32::MAX);
    }
}
