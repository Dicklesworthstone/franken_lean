//! Deterministic FLBC register interpreter for the G0-3 prototype.
//!
//! The register file contains only [`Obj`] handles from Marrow's safe surface:
//! there is no host-value shadow representation and no conversion at calls.
//! Execution accepts only [`ValidatedProgram`]. Cooperative cancellation and
//! instruction/stack exhaustion use the shared FL-INV-07 [`Outcome`] algebra,
//! whose non-authoritative arms cannot carry a partially published object.
//!
//! Interpreter closures are real Marrow closure objects. Their first fixed
//! slot is a tagged function-table word followed by captured ABI values. The
//! raw function field remains the explicit shell sentinel, so applying a
//! native/plugin closure is a typed unsupported result until the G0 trampoline
//! exists; this slice does not misreport that boundary as zero-conversion
//! plugin interoperability.
//!
//! The pure effect nucleus uses the same identity: `ST.Ref` cells, evaluated
//! thunks, and finished tasks are Marrow objects all the way through their
//! intrinsic rows. A delayed thunk claims its closure once and completes only
//! through the ordinary return continuation. The manager-absent `Task.spawn`,
//! `Task.map`, and `Task.bind` fallbacks use that same continuation machinery
//! and produce only finished tasks. The allocation-linked
//! `IO.getNumHeartbeats` / `IO.setNumHeartbeats` rows share Marrow's runtime
//! counter and preserve arbitrary-`Nat` low-64 semantics. In this managerless
//! state, `IO.checkCanceled` observes false and `IO.cancel` is the pinned no-op
//! on a finished task; host execution cancellation remains a distinct
//! non-authoritative stop. Scheduled tasks, concurrent thunk forcing, ambient
//! IO, and capability effects remain outside this slice.

use crate::extern_row::{
    ArgumentOwnership as ContractArgumentOwnership, Ownership as ExternOwnership,
    ResultOwnership as ContractResultOwnership,
};
use crate::extern_table_generated::{EXTERN_ROW_CONTRACT_ROOT, EXTERN_ROWS};
use fln_comp::flbc::{
    ArgumentOwnership, CallableResultOwnership, CodecLimits, FunctionId, Instruction, Register,
    ResultOwnership, ValidatedProgram, encode_canonical,
};
use fln_core::diag::ResourceReason;
use fln_core::mode::{BuildProfileId, ContentRoot, Mode};
use fln_core::name::Name;
use fln_core::options::{
    Options,
    limits::{HEARTBEAT_UNIT, MAX_HEARTBEATS_DEFAULT},
};
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_hash::domain::{Digest, Domain, hash};
use fln_rt::abi;
use fln_rt::obj::Obj;
use std::fmt;

/// Caller-supplied execution limits. `max_steps` is a FrankenLean-owned FLBC
/// instruction allowance, not the Reference's allocation-linked heartbeat
/// option. A value of zero permits no work in that dimension; the first
/// attempted unit reports `observed = 1`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionLimits {
    pub max_steps: u64,
    pub max_stack_depth: u64,
}

impl Default for ExecutionLimits {
    fn default() -> Self {
        Self {
            max_steps: 1_000_000,
            max_stack_depth: 1_000,
        }
    }
}

/// The Reference `maxHeartbeats` option for one command, in its public
/// thousand-heartbeat units.
///
/// Zero disables the limit. A multiplication overflow also cannot be
/// exhausted by the runtime's `u64` counter, so it is represented as an
/// unbounded effective limit rather than wrapped to a smaller allowance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HeartbeatLimit {
    max_option_units: u64,
}

impl HeartbeatLimit {
    pub const UNLIMITED: Self = Self::from_option_units(0);

    pub const fn from_option_units(max_option_units: u64) -> Self {
        Self { max_option_units }
    }

    pub const fn max_option_units(self) -> u64 {
        self.max_option_units
    }

    pub const fn effective_limit(self) -> Option<u64> {
        if self.max_option_units == 0 {
            None
        } else {
            self.max_option_units.checked_mul(HEARTBEAT_UNIT)
        }
    }
}

/// Reference-facing command options captured before one Golem run.
///
/// This is distinct from [`ExecutionLimits`]: those are FrankenLean's own
/// interpreter work ceilings, while this context carries observable command
/// policy. The first field is the pin-defined `maxHeartbeats` option; future
/// command-scoped effect capabilities can extend the same explicit boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CommandExecutionContext {
    heartbeat_limit: HeartbeatLimit,
}

impl CommandExecutionContext {
    /// Compatibility context for callers that have not yet supplied `Options`.
    pub const UNLIMITED: Self = Self::new(HeartbeatLimit::UNLIMITED);

    pub const fn new(heartbeat_limit: HeartbeatLimit) -> Self {
        Self { heartbeat_limit }
    }

    /// Capture the pin-defined `maxHeartbeats` option in thousand-unit form.
    ///
    /// [`Options`] preserves Reference first-match lookup and defaults on both
    /// absence and type mismatch. This method preserves those observables and
    /// leaves the ×1000 overflow decision to [`HeartbeatLimit`].
    pub fn from_options(options: &Options) -> Self {
        let name = Name::str(Name::anonymous(), "maxHeartbeats");
        Self::new(HeartbeatLimit::from_option_units(
            options.get_nat(&name, MAX_HEARTBEATS_DEFAULT),
        ))
    }

    pub const fn heartbeat_limit(self) -> HeartbeatLimit {
        self.heartbeat_limit
    }
}

/// Logical resource use of a terminal, authoritative execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionUsage {
    /// Successfully executed FLBC instructions.
    pub steps: u64,
    /// Cooperative system polls issued for successfully executed instructions.
    ///
    /// The current policy polls once immediately before each instruction, so a
    /// completed result has `system_polls == steps`. This is a separate field
    /// because the policy can evolve without relabeling instruction work or
    /// allocator heartbeats.
    pub system_polls: u64,
    pub peak_stack_depth: u64,
}

/// Semantic coordinates outside the FLBC artifact that can change dispatch
/// meaning. Every axis is mandatory and this type intentionally has no
/// [`Default`] implementation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionCacheContext {
    environment_root: ContentRoot,
    build_profile: BuildProfileId,
    mode: Mode,
}

impl ExecutionCacheContext {
    pub const fn new(
        environment_root: ContentRoot,
        build_profile: BuildProfileId,
        mode: Mode,
    ) -> Self {
        Self {
            environment_root,
            build_profile,
            mode,
        }
    }

    pub const fn environment_root(self) -> ContentRoot {
        self.environment_root
    }

    pub const fn build_profile(self) -> BuildProfileId {
        self.build_profile
    }

    pub const fn mode(self) -> Mode {
        self.mode
    }
}

/// Cumulative, non-authoritative observations from one inline-cache instance.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct InlineCacheStats {
    pub lookups: u64,
    pub hits: u64,
    pub misses: u64,
    pub replacements: u64,
    pub namespace_invalidations: u64,
    pub identity_fallbacks: u64,
}

/// Typed refusal to allocate the caller-requested direct-mapped cache.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InlineCacheAllocationError {
    requested_slots: usize,
}

impl InlineCacheAllocationError {
    pub const fn requested_slots(self) -> usize {
        self.requested_slots
    }
}

impl fmt::Display for InlineCacheAllocationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "could not allocate {} inline-cache slots",
            self.requested_slots
        )
    }
}

impl std::error::Error for InlineCacheAllocationError {}

/// Bounded direct-mapped dispatch caches.
///
/// Entries contain only immutable validation metadata. They never retain
/// registers, closure captures, constructor children, or completed results.
/// Intrinsic entries bind one generated census row to a typed implementation
/// plan, so hits perform neither a census scan nor ownership-contract parsing.
#[derive(Debug)]
pub struct InlineCaches {
    slots: Vec<Option<InlineCacheEntry>>,
    namespace: Option<CacheNamespace>,
    stats: InlineCacheStats,
    identity_limits: CodecLimits,
}

impl InlineCaches {
    pub fn try_new(slot_count: usize) -> Result<Self, InlineCacheAllocationError> {
        Self::try_new_with_identity_limits(slot_count, CodecLimits::default())
    }

    pub fn try_new_with_identity_limits(
        slot_count: usize,
        identity_limits: CodecLimits,
    ) -> Result<Self, InlineCacheAllocationError> {
        let mut slots = Vec::new();
        slots
            .try_reserve_exact(slot_count)
            .map_err(|_| InlineCacheAllocationError {
                requested_slots: slot_count,
            })?;
        slots.resize(slot_count, None);
        Ok(Self {
            slots,
            namespace: None,
            stats: InlineCacheStats::default(),
            identity_limits,
        })
    }

    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub const fn stats(&self) -> InlineCacheStats {
        self.stats
    }

    fn is_disabled(&self) -> bool {
        self.slots.is_empty()
    }

    fn begin_namespace(&mut self, namespace: CacheNamespace) {
        if self.is_disabled() {
            return;
        }
        match self.namespace {
            None => self.namespace = Some(namespace),
            Some(current) if current == namespace => {}
            Some(_) => {
                self.slots.fill(None);
                self.namespace = Some(namespace);
                self.stats.namespace_invalidations =
                    self.stats.namespace_invalidations.saturating_add(1);
            }
        }
    }

    fn record_identity_fallback(&mut self) {
        self.stats.identity_fallbacks = self.stats.identity_fallbacks.saturating_add(1);
    }

    fn ctor_hit(&mut self, key: CtorCacheKey) -> bool {
        let Some(index) = self.slot_index(key.slot_hash()) else {
            return false;
        };
        self.stats.lookups = self.stats.lookups.saturating_add(1);
        if self.slots[index] == Some(InlineCacheEntry::Ctor(key)) {
            self.stats.hits = self.stats.hits.saturating_add(1);
            true
        } else {
            self.stats.misses = self.stats.misses.saturating_add(1);
            false
        }
    }

    fn record_ctor(&mut self, key: CtorCacheKey) {
        let Some(index) = self.slot_index(key.slot_hash()) else {
            return;
        };
        if self.slots[index].is_some() {
            self.stats.replacements = self.stats.replacements.saturating_add(1);
        }
        self.slots[index] = Some(InlineCacheEntry::Ctor(key));
    }

    fn apply_hit(&mut self, key: ApplyCacheKey) -> Option<ApplyCacheMetadata> {
        let index = self.slot_index(key.slot_hash())?;
        self.stats.lookups = self.stats.lookups.saturating_add(1);
        match self.slots[index] {
            Some(InlineCacheEntry::Apply {
                key: stored,
                metadata,
            }) if stored == key => {
                self.stats.hits = self.stats.hits.saturating_add(1);
                Some(metadata)
            }
            _ => {
                self.stats.misses = self.stats.misses.saturating_add(1);
                None
            }
        }
    }

    fn record_apply(&mut self, key: ApplyCacheKey, metadata: ApplyCacheMetadata) {
        let Some(index) = self.slot_index(key.slot_hash()) else {
            return;
        };
        if self.slots[index].is_some() {
            self.stats.replacements = self.stats.replacements.saturating_add(1);
        }
        self.slots[index] = Some(InlineCacheEntry::Apply { key, metadata });
    }

    fn intrinsic_hit(
        &mut self,
        site: CacheSite,
        row: &str,
        argument_ownership: &[ArgumentOwnership],
        result_ownership: ResultOwnership,
    ) -> Option<IntrinsicPlan> {
        let slot_hash = intrinsic_slot_hash(site, row, argument_ownership, result_ownership);
        let index = self.slot_index(slot_hash)?;
        self.stats.lookups = self.stats.lookups.saturating_add(1);
        match self.slots[index] {
            Some(InlineCacheEntry::Intrinsic { key, plan })
                if key.matches(site, row, argument_ownership, result_ownership) =>
            {
                self.stats.hits = self.stats.hits.saturating_add(1);
                Some(plan)
            }
            _ => {
                self.stats.misses = self.stats.misses.saturating_add(1);
                None
            }
        }
    }

    fn record_intrinsic(&mut self, key: IntrinsicCacheKey, plan: IntrinsicPlan) {
        let Some(index) = self.slot_index(key.slot_hash()) else {
            return;
        };
        if self.slots[index].is_some() {
            self.stats.replacements = self.stats.replacements.saturating_add(1);
        }
        self.slots[index] = Some(InlineCacheEntry::Intrinsic { key, plan });
    }

    fn slot_index(&self, slot_hash: u64) -> Option<usize> {
        if self.slots.is_empty() {
            None
        } else {
            Some((slot_hash as usize) % self.slots.len())
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CacheNamespace {
    program_root: Digest,
    schema_version: u16,
    extern_contract_root: Digest,
    environment_root: ContentRoot,
    build_profile: BuildProfileId,
    mode: Mode,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CacheSite {
    function: FunctionId,
    pc: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CtorCacheKey {
    site: CacheSite,
    actual_tag: u8,
    actual_fields: usize,
}

impl CtorCacheKey {
    fn slot_hash(self) -> u64 {
        cache_hash(
            1,
            &[
                u64::from(self.site.function.get()),
                self.site.pc as u64,
                u64::from(self.actual_tag),
                self.actual_fields as u64,
            ],
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ApplyCacheKey {
    site: CacheSite,
    function: FunctionId,
    encoded_arity: u16,
    capture_count: usize,
    argument_count: usize,
}

impl ApplyCacheKey {
    fn slot_hash(self) -> u64 {
        cache_hash(
            2,
            &[
                u64::from(self.site.function.get()),
                self.site.pc as u64,
                u64::from(self.function.get()),
                u64::from(self.encoded_arity),
                self.capture_count as u64,
                self.argument_count as u64,
            ],
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ApplyCacheMetadata {
    required: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IntrinsicCacheKey {
    site: CacheSite,
    row: &'static str,
    argument_count: usize,
    argument_ownership_hash: u64,
    result_ownership: ResultOwnership,
    slot_hash: u64,
}

impl IntrinsicCacheKey {
    fn new(
        site: CacheSite,
        row: &'static str,
        argument_ownership: &[ArgumentOwnership],
        result_ownership: ResultOwnership,
    ) -> Self {
        Self {
            site,
            row,
            argument_count: argument_ownership.len(),
            argument_ownership_hash: ownership_hash(argument_ownership),
            result_ownership,
            slot_hash: intrinsic_slot_hash(site, row, argument_ownership, result_ownership),
        }
    }

    fn matches(
        self,
        site: CacheSite,
        row: &str,
        argument_ownership: &[ArgumentOwnership],
        result_ownership: ResultOwnership,
    ) -> bool {
        self.site == site
            && self.row == row
            && self.argument_count == argument_ownership.len()
            && self.argument_ownership_hash == ownership_hash(argument_ownership)
            && self.result_ownership == result_ownership
    }

    fn slot_hash(self) -> u64 {
        self.slot_hash
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IntrinsicPlan {
    row: &'static str,
    implementation: IntrinsicImplementation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IntrinsicImplementation {
    NatAdd,
    NatSub,
    NatMul,
    StringAppend,
    ArraySize,
    ArrayGetInternal,
    ArrayGetBorrowed,
    ArrayPush,
    IoCancel,
    IoCheckCancelled,
    IoGetNumHeartbeats,
    IoSetNumHeartbeats,
    RefNew,
    RefGet,
    RefTake,
    RefSet,
    RefSwap,
    RefPtrEq,
    ThunkPure,
    ThunkNew,
    ThunkGet,
    TaskPure,
    TaskGet,
    TaskSpawn,
    TaskMap,
    TaskBind,
    Unsupported,
}

impl IntrinsicImplementation {
    fn for_row(row: &str) -> Self {
        match row {
            "extern:Nat.add" => Self::NatAdd,
            "extern:Nat.sub" => Self::NatSub,
            "extern:Nat.mul" => Self::NatMul,
            "extern:String.append" => Self::StringAppend,
            "extern:Array.size" => Self::ArraySize,
            "extern:Array.getInternal" => Self::ArrayGetInternal,
            "extern:Array.ugetBorrowed" => Self::ArrayGetBorrowed,
            "extern:Array.push" => Self::ArrayPush,
            "extern:IO.cancel" => Self::IoCancel,
            "extern:IO.checkCanceled" => Self::IoCheckCancelled,
            "extern:IO.getNumHeartbeats" => Self::IoGetNumHeartbeats,
            "extern:IO.setNumHeartbeats" => Self::IoSetNumHeartbeats,
            "extern:ST.Prim.mkRef" => Self::RefNew,
            "extern:ST.Prim.Ref.get" => Self::RefGet,
            "extern:ST.Prim.Ref.take" => Self::RefTake,
            "extern:ST.Prim.Ref.set" => Self::RefSet,
            "extern:ST.Prim.Ref.swap" => Self::RefSwap,
            "extern:ST.Prim.Ref.ptrEq" => Self::RefPtrEq,
            "extern:Thunk.pure" => Self::ThunkPure,
            "extern:Thunk.mk" => Self::ThunkNew,
            "extern:Thunk.get" => Self::ThunkGet,
            "extern:Task.pure" => Self::TaskPure,
            "extern:Task.get" => Self::TaskGet,
            "extern:Task.spawn" => Self::TaskSpawn,
            "extern:Task.map" => Self::TaskMap,
            "extern:Task.bind" => Self::TaskBind,
            _ => Self::Unsupported,
        }
    }

    const fn is_managerless_task(self) -> bool {
        matches!(self, Self::TaskSpawn | Self::TaskMap | Self::TaskBind)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InlineCacheEntry {
    Ctor(CtorCacheKey),
    Apply {
        key: ApplyCacheKey,
        metadata: ApplyCacheMetadata,
    },
    Intrinsic {
        key: IntrinsicCacheKey,
        plan: IntrinsicPlan,
    },
}

fn cache_hash(discriminant: u64, words: &[u64]) -> u64 {
    words
        .iter()
        .copied()
        .fold(0x6a09_e667_f3bc_c909_u64 ^ discriminant, |state, word| {
            (state ^ word.wrapping_add(0x9e37_79b9_7f4a_7c15))
                .rotate_left(27)
                .wrapping_mul(0x94d0_49bb_1331_11eb)
        })
}

fn intrinsic_slot_hash(
    site: CacheSite,
    row: &str,
    argument_ownership: &[ArgumentOwnership],
    result_ownership: ResultOwnership,
) -> u64 {
    cache_hash(
        3,
        &[
            u64::from(site.function.get()),
            site.pc as u64,
            stable_text_hash(row),
            argument_ownership.len() as u64,
            ownership_hash(argument_ownership),
            result_ownership_word(result_ownership),
        ],
    )
}

fn stable_text_hash(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |state, byte| {
        (state ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

fn ownership_hash(ownership: &[ArgumentOwnership]) -> u64 {
    ownership
        .iter()
        .copied()
        .fold(0x243f_6a88_85a3_08d3, |state, disposition| {
            (state ^ argument_ownership_word(disposition))
                .rotate_left(17)
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        })
}

const fn argument_ownership_word(ownership: ArgumentOwnership) -> u64 {
    match ownership {
        ArgumentOwnership::Borrowed => 1,
        ArgumentOwnership::Owned => 2,
        ArgumentOwnership::Unique => 3,
        ArgumentOwnership::Scalar => 4,
    }
}

const fn result_ownership_word(ownership: ResultOwnership) -> u64 {
    match ownership {
        ResultOwnership::Owned => 1,
        ResultOwnership::Borrowed => 2,
        ResultOwnership::Scalar => 3,
        ResultOwnership::RawObject => 4,
    }
}

/// A successful return. `value` is the owned Marrow ABI object that occupied
/// the entry function's return register.
pub struct CompletedExecution {
    pub value: Obj,
    pub usage: ExecutionUsage,
}

impl fmt::Debug for CompletedExecution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CompletedExecution")
            .field("value_kind", &value_kind(&self.value))
            .field("usage", &self.usage)
            .finish()
    }
}

/// A fully determined execution result. Refusal and user panic are completed
/// domain answers; only cancellation/resource/internal failure live outside
/// this enum in [`Outcome`].
#[derive(Debug)]
pub enum VmExit {
    Returned(CompletedExecution),
    Panicked {
        message: String,
        usage: ExecutionUsage,
    },
    Refused {
        refusal: VmRefusal,
        usage: ExecutionUsage,
    },
}

/// Runtime object category, derived directly from the ABI header/tagged word.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueKind {
    Scalar,
    Ctor(u8),
    Promise,
    Closure,
    Array,
    StructArray,
    ScalarArray,
    String,
    Mpz,
    Thunk,
    Task,
    Ref,
    External,
    Reserved,
}

/// A completed refusal: the bytecode was structurally valid, but a dynamic
/// value or requested host row did not satisfy the operation contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmRefusal {
    UnknownIntrinsic {
        row: String,
    },
    UnsupportedIntrinsic {
        row: String,
    },
    IntrinsicArity {
        row: String,
        expected: usize,
        actual: usize,
    },
    IntrinsicOwnershipContract {
        row: String,
        reason: String,
    },
    IntrinsicOwnershipMismatch {
        row: String,
        argument: usize,
        expected: ArgumentOwnership,
        actual: ArgumentOwnership,
    },
    IntrinsicResultOwnershipMismatch {
        row: String,
        expected: ResultOwnership,
        actual: ResultOwnership,
    },
    IntrinsicResultImplementationMismatch {
        row: String,
        expected: ResultOwnership,
        actual: ResultOwnership,
    },
    IntrinsicResultKind {
        row: String,
        expected: &'static str,
        actual: ValueKind,
    },
    CallResultOwnershipMismatch {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: CallableResultOwnership,
    },
    ApplyResultOwnershipMismatch {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: CallableResultOwnership,
    },
    CallableResultKind {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: ValueKind,
    },
    ApplyOwnershipMismatch {
        function: FunctionId,
        argument: usize,
        expected: ArgumentOwnership,
        actual: ArgumentOwnership,
    },
    ApplyUniquePartial {
        function: FunctionId,
        argument: usize,
    },
    TypeMismatch {
        operation: &'static str,
        argument: usize,
        expected: &'static str,
        actual: ValueKind,
    },
    NatOverflow {
        operation: &'static str,
    },
    ArrayIndexOutOfBounds {
        index: usize,
        size: usize,
    },
    ConstructorProjectionTag {
        expected: u8,
        actual: ValueKind,
    },
    ConstructorProjectionShape {
        expected_fields: usize,
        actual_fields: usize,
    },
    InvalidStringObject,
    UnsupportedNativeClosure,
    MalformedClosure {
        reason: &'static str,
    },
    InvalidBoolScalar {
        operation: &'static str,
        argument: usize,
        value: usize,
    },
    ThunkForceInFlight,
    UnsupportedTaskState,
}

impl fmt::Display for VmRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownIntrinsic { row } => write!(f, "unknown intrinsic row {row:?}"),
            Self::UnsupportedIntrinsic { row } => {
                write!(f, "intrinsic row {row:?} has no prototype implementation")
            }
            Self::IntrinsicArity {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} received {actual} values, expected {expected}"
            ),
            Self::IntrinsicOwnershipContract { row, reason } => write!(
                f,
                "intrinsic row {row:?} has a non-executable ownership contract: {reason}"
            ),
            Self::IntrinsicOwnershipMismatch {
                row,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} argument {argument} ownership is {}, generated contract requires {}",
                actual.token(),
                expected.token()
            ),
            Self::IntrinsicResultOwnershipMismatch {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} result ownership is {}, generated contract requires {}",
                actual.token(),
                expected.token()
            ),
            Self::IntrinsicResultImplementationMismatch {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} implementation produced a {} result, executable bytecode requires {}",
                actual.token(),
                expected.token()
            ),
            Self::IntrinsicResultKind {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} result expected {expected}, got {actual:?}"
            ),
            Self::CallResultOwnershipMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "Call result ownership is {}, function {} requires {}",
                actual.token(),
                function.get(),
                expected.token()
            ),
            Self::ApplyResultOwnershipMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "Apply result ownership is {}, dynamic function {} requires {}",
                actual.token(),
                function.get(),
                expected.token()
            ),
            Self::CallableResultKind {
                function,
                expected,
                actual,
            } => write!(
                f,
                "function {} returned {actual:?}, contract requires {}",
                function.get(),
                expected.token()
            ),
            Self::ApplyOwnershipMismatch {
                function,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "Apply argument {argument} ownership is {}, dynamic function {} requires {}",
                actual.token(),
                function.get(),
                expected.token()
            ),
            Self::ApplyUniquePartial { function, argument } => write!(
                f,
                "Apply argument {argument} for function {} is unique but under-application would retain it in a reusable closure",
                function.get()
            ),
            Self::TypeMismatch {
                operation,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "{operation} argument {argument} expected {expected}, got {actual:?}"
            ),
            Self::NatOverflow { operation } => {
                write!(
                    f,
                    "{operation} result exceeds the prototype Nat scalar range"
                )
            }
            Self::ArrayIndexOutOfBounds { index, size } => {
                write!(f, "array index {index} is outside size {size}")
            }
            Self::ConstructorProjectionTag { expected, actual } => write!(
                f,
                "constructor projection expected tag {expected}, got {actual:?}"
            ),
            Self::ConstructorProjectionShape {
                expected_fields,
                actual_fields,
            } => write!(
                f,
                "constructor projection expected {expected_fields} object fields, got {actual_fields}"
            ),
            Self::InvalidStringObject => write!(f, "Marrow String object is not canonical UTF-8"),
            Self::UnsupportedNativeClosure => {
                write!(
                    f,
                    "native closure application requires the plugin trampoline"
                )
            }
            Self::MalformedClosure { reason } => {
                write!(f, "Golem closure shell is malformed: {reason}")
            }
            Self::InvalidBoolScalar {
                operation,
                argument,
                value,
            } => write!(
                f,
                "{operation} argument {argument} expected Bool scalar 0 or 1, got {value}"
            ),
            Self::ThunkForceInFlight => {
                write!(f, "thunk force is already in flight")
            }
            Self::UnsupportedTaskState => {
                write!(f, "scheduled or waiting task access is not implemented")
            }
        }
    }
}

impl std::error::Error for VmRefusal {}

/// Cooperative cancellation source. Golem samples it once before every
/// instruction; a true observation stops without executing or publishing that
/// instruction.
///
/// This VM scheduling checkpoint is distinct from both allocation-linked
/// heartbeats and the explicit `Lean.Core.checkSystem` instruction. At that
/// instruction, the same poll is the Reference-compatible cancellation half of
/// `checkSystem`; all other instructions retain the ordinary scheduler poll.
pub trait CancellationProbe {
    fn is_cancelled(&self) -> bool;
}

impl<F> CancellationProbe for F
where
    F: Fn() -> bool,
{
    fn is_cancelled(&self) -> bool {
        self()
    }
}

struct Frame {
    function: FunctionId,
    pc: usize,
    registers: Vec<Option<Obj>>,
    return_to: Option<ReturnTo>,
}

enum ReturnTo {
    Store(Register),
    Apply {
        destination: Register,
        args: Vec<Obj>,
        argument_ownership: Vec<ArgumentOwnership>,
        result_ownership: CallableResultOwnership,
    },
    CompleteThunk {
        destination: Register,
        thunk: Obj,
        result_ownership: ResultOwnership,
    },
    CompleteManagerlessTask {
        destination: Register,
        completion: ManagerlessTaskCompletion,
        row: &'static str,
        result_ownership: ResultOwnership,
    },
}

enum PreparedApply {
    Partial {
        function: FunctionId,
        captures: Vec<Obj>,
    },
    Call {
        function: FunctionId,
        args: Vec<Obj>,
        remainder: Vec<Obj>,
        remainder_ownership: Vec<ArgumentOwnership>,
    },
}

struct ApplyPlan {
    function: FunctionId,
    captures: Vec<Obj>,
    required: usize,
}

struct InspectedClosure {
    encoded_arity: u16,
    function: FunctionId,
    captures: Vec<Obj>,
}

enum ManagerlessTaskCompletion {
    WrapPure,
    RequireFinishedTask,
}

struct ManagerlessTaskApplication {
    row: &'static str,
    closure: Obj,
    argument: Obj,
    argument_ownership: ArgumentOwnership,
    completion: ManagerlessTaskCompletion,
}

struct IntrinsicResult {
    ownership: ResultOwnership,
    value: Obj,
}

impl IntrinsicResult {
    fn owned(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::Owned,
            value,
        }
    }

    fn borrowed_promoted(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::Borrowed,
            value,
        }
    }

    fn raw_object(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::RawObject,
            value,
        }
    }

    const fn ownership(&self) -> ResultOwnership {
        self.ownership
    }

    fn into_object(self) -> Obj {
        self.value
    }
}

enum Stop {
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct HeartbeatContext {
    initial: u64,
    effective_limit: Option<u64>,
}

impl HeartbeatContext {
    fn snapshot(limit: HeartbeatLimit) -> Self {
        Self {
            initial: fln_rt::heartbeat::allocation_heartbeats(),
            effective_limit: limit.effective_limit(),
        }
    }

    fn exhaustion(self) -> Option<(u64, u64)> {
        let limit = self.effective_limit?;
        let current = fln_rt::heartbeat::allocation_heartbeats();
        let consumed = current.saturating_sub(self.initial);
        (consumed > limit).then_some((consumed, limit))
    }
}

/// Execute a validated program. Non-authoritative paths contain no object
/// result, so a caller cannot accidentally cache a half-run register.
pub fn execute(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<VmExit> {
    execute_with_context(
        program,
        limits,
        CommandExecutionContext::UNLIMITED,
        cancellation,
    )
}

/// Execute with an explicit command-scoped Reference heartbeat option.
///
/// The initial allocation counter is captured on entry, as `CoreM.toIO` does.
/// Only the two `checkSystem` instruction forms observe its saturating delta.
pub fn execute_with_heartbeat_limit(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    heartbeat_limit: HeartbeatLimit,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<VmExit> {
    execute_with_context(
        program,
        limits,
        CommandExecutionContext::new(heartbeat_limit),
        cancellation,
    )
}

/// Execute with one context captured from the command's observable options.
pub fn execute_with_context(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    context: CommandExecutionContext,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<VmExit> {
    finish_run(run(
        program,
        limits,
        context.heartbeat_limit(),
        cancellation,
        None,
    ))
}

/// Execute through bounded inline caches while preserving [`execute`] as the
/// uncached semantic path.
///
/// If canonical identity construction exceeds the FLBC codec's bounded
/// resource limits, this function records a fallback and runs uncached. Cache
/// acceleration can therefore disappear, but it cannot change a VM outcome.
pub fn execute_cached(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
    context: ExecutionCacheContext,
    caches: &mut InlineCaches,
) -> Outcome<VmExit> {
    execute_cached_with_heartbeat_limit(
        program,
        limits,
        HeartbeatLimit::UNLIMITED,
        cancellation,
        context,
        caches,
    )
}

/// Cached execution with the same explicit command-scoped heartbeat contract
/// as [`execute_with_heartbeat_limit`].
pub fn execute_cached_with_heartbeat_limit(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    heartbeat_limit: HeartbeatLimit,
    cancellation: Option<&dyn CancellationProbe>,
    context: ExecutionCacheContext,
    caches: &mut InlineCaches,
) -> Outcome<VmExit> {
    execute_cached_with_context(
        program,
        limits,
        CommandExecutionContext::new(heartbeat_limit),
        cancellation,
        context,
        caches,
    )
}

/// Cached execution with the same captured command context as
/// [`execute_with_context`].
pub fn execute_cached_with_context(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    command_context: CommandExecutionContext,
    cancellation: Option<&dyn CancellationProbe>,
    context: ExecutionCacheContext,
    caches: &mut InlineCaches,
) -> Outcome<VmExit> {
    if caches.is_disabled() {
        return execute_with_context(program, limits, command_context, cancellation);
    }
    let Some(namespace) = cache_namespace(program, context, caches.identity_limits) else {
        caches.record_identity_fallback();
        return execute_with_context(program, limits, command_context, cancellation);
    };
    caches.begin_namespace(namespace);
    finish_run(run(
        program,
        limits,
        command_context.heartbeat_limit(),
        cancellation,
        Some(caches),
    ))
}

fn finish_run(result: Result<VmExit, Stop>) -> Outcome<VmExit> {
    match result {
        Ok(exit) => Outcome::Complete(exit),
        Err(Stop::Inconclusive(inconclusive)) => Outcome::Inconclusive(inconclusive),
        Err(Stop::InternalFault(fault)) => Outcome::InternalFault(fault),
    }
}

fn cache_namespace(
    program: &ValidatedProgram,
    context: ExecutionCacheContext,
    limits: CodecLimits,
) -> Option<CacheNamespace> {
    let canonical = encode_canonical(program, limits).ok()?;
    Some(CacheNamespace {
        program_root: hash(Domain::CacheKey, &canonical),
        schema_version: program.schema_version(),
        extern_contract_root: hash(Domain::CacheKey, EXTERN_ROW_CONTRACT_ROOT.as_bytes()),
        environment_root: context.environment_root(),
        build_profile: context.build_profile(),
        mode: context.mode(),
    })
}

fn run(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    heartbeat_limit: HeartbeatLimit,
    cancellation: Option<&dyn CancellationProbe>,
    mut inline_caches: Option<&mut InlineCaches>,
) -> Result<VmExit, Stop> {
    let heartbeat_context = HeartbeatContext::snapshot(heartbeat_limit);
    if limits.max_stack_depth < 1 {
        return Err(stack_exhausted(limits.max_stack_depth, 1, "entry frame"));
    }
    let entry = program.function(program.entry()).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-TARGET",
            "validated entry function disappeared",
        ))
    })?;
    let mut stack = vec![Frame {
        function: entry.id,
        pc: 0,
        registers: empty_registers(entry.register_count),
        return_to: None,
    }];
    let mut steps = 0u64;
    let mut peak_stack_depth = 1u64;

    loop {
        let frame = stack.last().ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-FRAME-STACK",
                "execution stack became empty without an entry return",
            ))
        })?;
        let function = program.function(frame.function).ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-TARGET",
                format!(
                    "validated function {} disappeared during execution",
                    frame.function.get()
                ),
            ))
        })?;
        let instruction = function.code.get(frame.pc).cloned().ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-PC",
                format!(
                    "function {} reached invalid pc {}",
                    frame.function.get(),
                    frame.pc
                ),
            ))
        })?;
        let cache_site = CacheSite {
            function: frame.function,
            pc: frame.pc,
        };
        let location = format!("function {} pc {}", frame.function.get(), frame.pc);

        let dynamic_check_system_module =
            if let Instruction::CheckSystemValue { module_name } = &instruction {
                Some(string_value(
                    register(frame, *module_name)?,
                    "Lean.Core.checkSystem",
                    0,
                ))
            } else {
                None
            };
        let check_system_location = match (&instruction, &dynamic_check_system_module) {
            (Instruction::CheckSystem { module_name }, _) => Some(format!(
                "{location} Lean.Core.checkSystem module {module_name}"
            )),
            (Instruction::CheckSystemValue { .. }, Some(Ok(module_name))) => Some(format!(
                "{location} Lean.Core.checkSystem module {module_name}"
            )),
            _ => None,
        };
        let poll_location = check_system_location.as_deref().unwrap_or(&location);
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Err(Stop::Inconclusive(
                Inconclusive::cancelled(poll_location).with_progress(poll_location),
            ));
        }
        if let Some(check_location) = check_system_location.as_deref()
            && let Some((consumed, limit)) = heartbeat_context.exhaustion()
        {
            return Err(heartbeat_exhausted(consumed, limit, check_location));
        }
        let observed_steps = steps.checked_add(1).ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-RESOURCE-ACCOUNTING",
                "step counter overflowed",
            ))
        })?;
        if observed_steps > limits.max_steps {
            return Err(execution_steps_exhausted(
                limits.max_steps,
                observed_steps,
                &location,
            ));
        }
        steps = observed_steps;

        match instruction {
            Instruction::Nat { dst, value } => {
                let value = usize::try_from(value).map_err(|_| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-VALIDATED-NAT",
                        "validated Nat constant does not fit the certified target",
                    ))
                })?;
                set_register(current_frame_mut(&mut stack)?, dst, Obj::mk_nat(value))?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::String { dst, value } => {
                set_register(current_frame_mut(&mut stack)?, dst, Obj::mk_string(&value))?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Copy { dst, src } => {
                let value = clone_register(current_frame(&stack)?, src)?;
                set_register(current_frame_mut(&mut stack)?, dst, value)?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Move { dst, src } => {
                if dst != src {
                    let value = take_register(current_frame_mut(&mut stack)?, src)?;
                    set_register(current_frame_mut(&mut stack)?, dst, value)?;
                }
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Drop { src } => {
                drop(take_register(current_frame_mut(&mut stack)?, src)?);
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Ctor {
                dst,
                tag,
                fields,
                scalar_bytes,
            } => {
                let values = clone_registers(current_frame(&stack)?, fields.iter().copied())?;
                set_register(
                    current_frame_mut(&mut stack)?,
                    dst,
                    Obj::mk_ctor(tag, values, &scalar_bytes),
                )?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::CtorField {
                dst,
                src,
                expected_tag,
                expected_fields,
                field,
            } => {
                let projected = {
                    let value = register(current_frame(&stack)?, src)?;
                    let actual = value_kind(value);
                    let ValueKind::Ctor(actual_tag) = actual else {
                        return Ok(VmExit::Refused {
                            refusal: VmRefusal::ConstructorProjectionTag {
                                expected: expected_tag,
                                actual,
                            },
                            usage: usage(steps, peak_stack_depth),
                        });
                    };
                    let actual_fields = usize::from(value.header().other);
                    let cache_key = CtorCacheKey {
                        site: cache_site,
                        actual_tag,
                        actual_fields,
                    };
                    let cache_hit = inline_caches
                        .as_deref_mut()
                        .is_some_and(|caches| caches.ctor_hit(cache_key));
                    let expected_fields = usize::from(expected_fields);
                    if !cache_hit {
                        if actual_tag != expected_tag {
                            return Ok(VmExit::Refused {
                                refusal: VmRefusal::ConstructorProjectionTag {
                                    expected: expected_tag,
                                    actual,
                                },
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                        if actual_fields != expected_fields {
                            return Ok(VmExit::Refused {
                                refusal: VmRefusal::ConstructorProjectionShape {
                                    expected_fields,
                                    actual_fields,
                                },
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                        if let Some(caches) = inline_caches.as_deref_mut() {
                            caches.record_ctor(cache_key);
                        }
                    }
                    value.ctor_child(usize::from(field))
                };
                set_register(current_frame_mut(&mut stack)?, dst, projected)?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Array { dst, items } => {
                let values = clone_registers(current_frame(&stack)?, items.iter().copied())?;
                set_register(current_frame_mut(&mut stack)?, dst, Obj::mk_array(values))?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Intrinsic {
                dst,
                row,
                args,
                argument_ownership,
                result_ownership,
            } => {
                let cached_plan = inline_caches.as_deref_mut().and_then(|caches| {
                    caches.intrinsic_hit(cache_site, &row, &argument_ownership, result_ownership)
                });
                let plan = match cached_plan {
                    Some(plan) => plan,
                    None => {
                        let plan = match resolve_intrinsic_plan(
                            &row,
                            &argument_ownership,
                            result_ownership,
                        ) {
                            Ok(plan) => plan,
                            Err(refusal) => {
                                return Ok(VmExit::Refused {
                                    refusal,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        };
                        if let Some(caches) = inline_caches.as_deref_mut() {
                            caches.record_intrinsic(
                                IntrinsicCacheKey::new(
                                    cache_site,
                                    plan.row,
                                    &argument_ownership,
                                    result_ownership,
                                ),
                                plan,
                            );
                        }
                        plan
                    }
                };
                let values = transfer_intrinsic_arguments(
                    current_frame_mut(&mut stack)?,
                    &args,
                    &argument_ownership,
                )?;
                if plan.implementation == IntrinsicImplementation::ThunkGet {
                    let thunk = match delayed_thunk_operand(values) {
                        Ok(thunk) => thunk,
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    };
                    if let Some(value) = thunk.evaluated_thunk_value() {
                        let value = match finish_intrinsic_result(
                            plan.row,
                            result_ownership,
                            IntrinsicResult::owned(value),
                        ) {
                            Ok(value) => value,
                            Err(refusal) => {
                                return Ok(VmExit::Refused {
                                    refusal,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        };
                        set_register(current_frame_mut(&mut stack)?, dst, value)?;
                        advance(current_frame_mut(&mut stack)?)?;
                    } else {
                        let closure = match thunk.claim_thunk_closure() {
                            Some(closure) => closure,
                            None => {
                                return Ok(VmExit::Refused {
                                    refusal: VmRefusal::ThunkForceInFlight,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        };
                        match prepare_internal_apply(
                            program,
                            &closure,
                            Obj::mk_nat(0),
                            ArgumentOwnership::Scalar,
                        ) {
                            Ok(PreparedApply::Partial { function, captures }) => {
                                let value = make_golem_closure(program, function, captures)?;
                                let value = match finish_intrinsic_result(
                                    plan.row,
                                    result_ownership,
                                    IntrinsicResult::owned(value),
                                ) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                cache_thunk_value(&thunk, &value)?;
                                set_register(current_frame_mut(&mut stack)?, dst, value)?;
                                advance(current_frame_mut(&mut stack)?)?;
                            }
                            Ok(PreparedApply::Call {
                                function,
                                args,
                                remainder,
                                remainder_ownership: _,
                            }) => {
                                if !remainder.is_empty() {
                                    return Err(Stop::InternalFault(InternalFault::new(
                                        "FLBC-THUNK-APPLY",
                                        "one Unit argument over-applied a validated closure",
                                    )));
                                }
                                advance(current_frame_mut(&mut stack)?)?;
                                let next_depth = push_call(
                                    program,
                                    &mut stack,
                                    function,
                                    args,
                                    ReturnTo::CompleteThunk {
                                        destination: dst,
                                        thunk,
                                        result_ownership,
                                    },
                                    limits.max_stack_depth,
                                    &location,
                                )?;
                                peak_stack_depth = peak_stack_depth.max(next_depth);
                            }
                            Err(refusal) => {
                                return Ok(VmExit::Refused {
                                    refusal,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        }
                    }
                } else if plan.implementation.is_managerless_task() {
                    let application =
                        match managerless_task_application(plan.implementation, plan.row, values) {
                            Ok(application) => application,
                            Err(refusal) => {
                                return Ok(VmExit::Refused {
                                    refusal,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        };
                    match prepare_internal_apply(
                        program,
                        &application.closure,
                        application.argument,
                        application.argument_ownership,
                    ) {
                        Ok(PreparedApply::Partial { function, captures }) => {
                            let value = make_golem_closure(program, function, captures)?;
                            let value =
                                match complete_managerless_task(application.completion, value) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                            let value = match finish_intrinsic_result(
                                application.row,
                                result_ownership,
                                IntrinsicResult::owned(value),
                            ) {
                                Ok(value) => value,
                                Err(refusal) => {
                                    return Ok(VmExit::Refused {
                                        refusal,
                                        usage: usage(steps, peak_stack_depth),
                                    });
                                }
                            };
                            set_register(current_frame_mut(&mut stack)?, dst, value)?;
                            advance(current_frame_mut(&mut stack)?)?;
                        }
                        Ok(PreparedApply::Call {
                            function,
                            args,
                            remainder,
                            remainder_ownership: _,
                        }) => {
                            if !remainder.is_empty() {
                                return Err(Stop::InternalFault(InternalFault::new(
                                    "FLBC-TASK-APPLY",
                                    "one managerless task argument over-applied a validated closure",
                                )));
                            }
                            advance(current_frame_mut(&mut stack)?)?;
                            let next_depth = push_call(
                                program,
                                &mut stack,
                                function,
                                args,
                                ReturnTo::CompleteManagerlessTask {
                                    destination: dst,
                                    completion: application.completion,
                                    row: application.row,
                                    result_ownership,
                                },
                                limits.max_stack_depth,
                                &location,
                            )?;
                            peak_stack_depth = peak_stack_depth.max(next_depth);
                        }
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    }
                } else {
                    match invoke_intrinsic(plan.implementation, plan.row, &values) {
                        Ok(result) => {
                            let value =
                                match finish_intrinsic_result(plan.row, result_ownership, result) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                            set_register(current_frame_mut(&mut stack)?, dst, value)?;
                            advance(current_frame_mut(&mut stack)?)?;
                        }
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    }
                }
            }
            Instruction::Call {
                dst,
                function,
                args,
                argument_ownership,
                result_ownership,
            } => {
                let callee = program.function(function).ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-VALIDATED-TARGET",
                        format!("validated call target {} disappeared", function.get()),
                    ))
                })?;
                if callee.parameter_ownership != argument_ownership {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CALL-OWNERSHIP",
                        format!(
                            "validated call to function {} disagrees with its parameter ownership",
                            function.get()
                        ),
                    )));
                }
                if callee.result_ownership != result_ownership {
                    return Ok(VmExit::Refused {
                        refusal: VmRefusal::CallResultOwnershipMismatch {
                            function,
                            expected: callee.result_ownership,
                            actual: result_ownership,
                        },
                        usage: usage(steps, peak_stack_depth),
                    });
                }
                let values = transfer_call_arguments(
                    current_frame_mut(&mut stack)?,
                    &args,
                    &argument_ownership,
                )?;
                advance(current_frame_mut(&mut stack)?)?;
                let next_depth = push_call(
                    program,
                    &mut stack,
                    function,
                    values,
                    ReturnTo::Store(dst),
                    limits.max_stack_depth,
                    &location,
                )?;
                peak_stack_depth = peak_stack_depth.max(next_depth);
            }
            Instruction::Closure {
                dst,
                function,
                captures,
                capture_ownership,
            } => {
                let callee = program.function(function).ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-VALIDATED-TARGET",
                        format!("validated closure target {} disappeared", function.get()),
                    ))
                })?;
                let Some(expected) = callee.parameter_ownership.get(..captures.len()) else {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CLOSURE-OWNERSHIP",
                        "validated closure capture count exceeds the target parameter contract",
                    )));
                };
                if expected != capture_ownership {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CLOSURE-OWNERSHIP",
                        format!(
                            "validated closure for function {} disagrees with its capture ownership",
                            function.get()
                        ),
                    )));
                }
                if capture_ownership.contains(&ArgumentOwnership::Unique) {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CLOSURE-OWNERSHIP",
                        "validated reusable closure carries a unique capture",
                    )));
                }
                let captures = transfer_closure_captures(
                    current_frame_mut(&mut stack)?,
                    &captures,
                    &capture_ownership,
                )?;
                let closure = make_golem_closure(program, function, captures)?;
                set_register(current_frame_mut(&mut stack)?, dst, closure)?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Apply {
                dst,
                closure,
                args,
                argument_ownership,
                result_ownership,
            } => {
                let closure = clone_register(current_frame(&stack)?, closure)?;
                let plan = match plan_cached_apply(
                    program,
                    &closure,
                    args.len(),
                    &argument_ownership,
                    result_ownership,
                    cache_site,
                    inline_caches.as_deref_mut(),
                ) {
                    Ok(plan) => plan,
                    Err(refusal) => {
                        return Ok(VmExit::Refused {
                            refusal,
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                };
                let args = transfer_apply_arguments(
                    current_frame_mut(&mut stack)?,
                    &args,
                    &argument_ownership,
                )?;
                match finish_apply(plan, args, Some(argument_ownership)) {
                    PreparedApply::Partial { function, captures } => {
                        let value = make_golem_closure(program, function, captures)?;
                        set_register(current_frame_mut(&mut stack)?, dst, value)?;
                        advance(current_frame_mut(&mut stack)?)?;
                    }
                    PreparedApply::Call {
                        function,
                        args,
                        remainder,
                        remainder_ownership,
                    } => {
                        let return_to = if remainder.is_empty() {
                            ReturnTo::Store(dst)
                        } else {
                            ReturnTo::Apply {
                                destination: dst,
                                args: remainder,
                                argument_ownership: remainder_ownership,
                                result_ownership,
                            }
                        };
                        advance(current_frame_mut(&mut stack)?)?;
                        let next_depth = push_call(
                            program,
                            &mut stack,
                            function,
                            args,
                            return_to,
                            limits.max_stack_depth,
                            &location,
                        )?;
                        peak_stack_depth = peak_stack_depth.max(next_depth);
                    }
                }
            }
            Instruction::Jump { target } => {
                current_frame_mut(&mut stack)?.pc =
                    usize::try_from(target.get()).map_err(|_| {
                        Stop::InternalFault(InternalFault::new(
                            "FLBC-VALIDATED-PC",
                            "validated jump target does not fit usize",
                        ))
                    })?;
            }
            Instruction::JumpIfZero {
                cond,
                zero,
                nonzero,
            } => {
                let frame = current_frame(&stack)?;
                let condition = register(frame, cond)?;
                if !condition.is_scalar() {
                    return Ok(VmExit::Refused {
                        refusal: type_mismatch("jump_if_zero", 0, "Nat scalar", condition),
                        usage: usage(steps, peak_stack_depth),
                    });
                }
                let target = if condition.unbox() == 0 {
                    zero
                } else {
                    nonzero
                };
                current_frame_mut(&mut stack)?.pc =
                    usize::try_from(target.get()).map_err(|_| {
                        Stop::InternalFault(InternalFault::new(
                            "FLBC-VALIDATED-PC",
                            "validated branch target does not fit usize",
                        ))
                    })?;
            }
            Instruction::CheckSystem { .. } => {
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::CheckSystemValue { .. } => {
                let module_name = dynamic_check_system_module.ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-CHECK-SYSTEM-CONTEXT",
                        "dynamic checkpoint did not prepare its module operand",
                    ))
                })?;
                match module_name {
                    Ok(_) => advance(current_frame_mut(&mut stack)?)?,
                    Err(refusal) => {
                        return Ok(VmExit::Refused {
                            refusal,
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                }
            }
            Instruction::Return { src } => {
                let value = take_register(current_frame_mut(&mut stack)?, src)?;
                let value =
                    match finish_callable_result(function.id, function.result_ownership, value) {
                        Ok(value) => value,
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    };
                let finished = stack.pop().ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-FRAME-STACK",
                        "return observed an empty execution stack",
                    ))
                })?;
                match finished.return_to {
                    None => {
                        if !stack.is_empty() {
                            return Err(Stop::InternalFault(InternalFault::new(
                                "FLBC-FRAME-RETURN",
                                "non-entry frame has no return action",
                            )));
                        }
                        return Ok(VmExit::Returned(CompletedExecution {
                            value,
                            usage: usage(steps, peak_stack_depth),
                        }));
                    }
                    Some(return_to) => {
                        if stack.is_empty() {
                            return Err(Stop::InternalFault(InternalFault::new(
                                "FLBC-FRAME-RETURN",
                                "entry frame unexpectedly has a return action",
                            )));
                        }
                        match return_to {
                            ReturnTo::Store(destination) => {
                                set_register(current_frame_mut(&mut stack)?, destination, value)?;
                            }
                            ReturnTo::Apply {
                                destination,
                                args,
                                argument_ownership,
                                result_ownership,
                            } => {
                                match prepare_owned_apply(
                                    program,
                                    &value,
                                    args,
                                    argument_ownership,
                                    result_ownership,
                                ) {
                                    Ok(PreparedApply::Partial { function, captures }) => {
                                        let closure =
                                            make_golem_closure(program, function, captures)?;
                                        set_register(
                                            current_frame_mut(&mut stack)?,
                                            destination,
                                            closure,
                                        )?;
                                    }
                                    Ok(PreparedApply::Call {
                                        function,
                                        args,
                                        remainder,
                                        remainder_ownership,
                                    }) => {
                                        let return_to = if remainder.is_empty() {
                                            ReturnTo::Store(destination)
                                        } else {
                                            ReturnTo::Apply {
                                                destination,
                                                args: remainder,
                                                argument_ownership: remainder_ownership,
                                                result_ownership,
                                            }
                                        };
                                        let next_depth = push_call(
                                            program,
                                            &mut stack,
                                            function,
                                            args,
                                            return_to,
                                            limits.max_stack_depth,
                                            &location,
                                        )?;
                                        peak_stack_depth = peak_stack_depth.max(next_depth);
                                    }
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                }
                            }
                            ReturnTo::CompleteThunk {
                                destination,
                                thunk,
                                result_ownership,
                            } => {
                                let value = match finish_intrinsic_result(
                                    "extern:Thunk.get",
                                    result_ownership,
                                    IntrinsicResult::owned(value),
                                ) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                cache_thunk_value(&thunk, &value)?;
                                set_register(current_frame_mut(&mut stack)?, destination, value)?;
                            }
                            ReturnTo::CompleteManagerlessTask {
                                destination,
                                completion,
                                row,
                                result_ownership,
                            } => {
                                let value = match complete_managerless_task(completion, value) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                let value = match finish_intrinsic_result(
                                    row,
                                    result_ownership,
                                    IntrinsicResult::owned(value),
                                ) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                set_register(current_frame_mut(&mut stack)?, destination, value)?;
                            }
                        }
                    }
                }
            }
            Instruction::Panic { message } => {
                let message = string_value(register(current_frame(&stack)?, message)?, "panic", 0);
                return match message {
                    Ok(message) => Ok(VmExit::Panicked {
                        message,
                        usage: usage(steps, peak_stack_depth),
                    }),
                    Err(refusal) => Ok(VmExit::Refused {
                        refusal,
                        usage: usage(steps, peak_stack_depth),
                    }),
                };
            }
        }
    }
}

fn make_golem_closure(
    program: &ValidatedProgram,
    function: FunctionId,
    captures: Vec<Obj>,
) -> Result<Obj, Stop> {
    let callee = program.function(function).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-TARGET",
            format!(
                "validated closure target {} disappeared during execution",
                function.get()
            ),
        ))
    })?;
    if captures.len() >= usize::from(callee.arity) {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-CLOSURE",
            format!(
                "closure target {} has {} captures for arity {}",
                function.get(),
                captures.len(),
                callee.arity
            ),
        )));
    }
    let encoded_arity = callee.arity.checked_add(1).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-CLOSURE",
            "validated closure arity cannot encode the target word",
        ))
    })?;
    let target_word = usize::try_from(function.get()).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-CLOSURE-TARGET",
            "function id does not fit the target word",
        ))
    })?;
    if target_word > usize::MAX >> 1 {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-CLOSURE-TARGET",
            "function id does not fit a Marrow Nat scalar",
        )));
    }
    let mut fixed = Vec::with_capacity(captures.len() + 1);
    fixed.push(Obj::mk_nat(target_word));
    fixed.extend(captures);
    Ok(Obj::mk_closure(encoded_arity, fixed))
}

fn prepare_internal_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    argument: Obj,
    argument_ownership: ArgumentOwnership,
) -> Result<PreparedApply, VmRefusal> {
    let ownership = [argument_ownership];
    let plan = plan_apply(program, closure, 1, Some(&ownership), None)?;
    Ok(finish_apply(plan, vec![argument], Some(ownership.into())))
}

fn prepare_owned_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    args: Vec<Obj>,
    argument_ownership: Vec<ArgumentOwnership>,
    result_ownership: CallableResultOwnership,
) -> Result<PreparedApply, VmRefusal> {
    let plan = plan_apply(
        program,
        closure,
        args.len(),
        Some(&argument_ownership),
        Some(result_ownership),
    )?;
    Ok(finish_apply(plan, args, Some(argument_ownership)))
}

fn plan_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    argument_count: usize,
    argument_ownership: Option<&[ArgumentOwnership]>,
    result_ownership: Option<CallableResultOwnership>,
) -> Result<ApplyPlan, VmRefusal> {
    let inspected = inspect_closure(closure)?;
    validate_inspected_apply(
        program,
        inspected,
        argument_count,
        argument_ownership,
        result_ownership,
    )
}

fn plan_cached_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    argument_count: usize,
    argument_ownership: &[ArgumentOwnership],
    result_ownership: CallableResultOwnership,
    site: CacheSite,
    inline_caches: Option<&mut InlineCaches>,
) -> Result<ApplyPlan, VmRefusal> {
    let inspected = inspect_closure(closure)?;
    let key = ApplyCacheKey {
        site,
        function: inspected.function,
        encoded_arity: inspected.encoded_arity,
        capture_count: inspected.captures.len(),
        argument_count,
    };
    if let Some(caches) = inline_caches {
        if let Some(metadata) = caches.apply_hit(key) {
            return Ok(ApplyPlan {
                function: inspected.function,
                captures: inspected.captures,
                required: metadata.required,
            });
        }
        let plan = validate_inspected_apply(
            program,
            inspected,
            argument_count,
            Some(argument_ownership),
            Some(result_ownership),
        )?;
        caches.record_apply(
            key,
            ApplyCacheMetadata {
                required: plan.required,
            },
        );
        Ok(plan)
    } else {
        validate_inspected_apply(
            program,
            inspected,
            argument_count,
            Some(argument_ownership),
            Some(result_ownership),
        )
    }
}

fn inspect_closure(closure: &Obj) -> Result<InspectedClosure, VmRefusal> {
    if value_kind(closure) != ValueKind::Closure {
        return Err(type_mismatch("apply", 0, "Golem closure", closure));
    }
    let Some((encoded_arity, fixed)) = closure.closure_shell_parts() else {
        return Err(VmRefusal::UnsupportedNativeClosure);
    };
    let mut fixed = fixed.into_iter();
    let target_word = fixed.next().ok_or(VmRefusal::MalformedClosure {
        reason: "missing target word",
    })?;
    if !target_word.is_scalar() {
        return Err(VmRefusal::MalformedClosure {
            reason: "target word is not a Nat scalar",
        });
    }
    let raw_function =
        u32::try_from(target_word.unbox()).map_err(|_| VmRefusal::MalformedClosure {
            reason: "target word is outside the FunctionId range",
        })?;
    Ok(InspectedClosure {
        encoded_arity,
        function: FunctionId::new(raw_function),
        captures: fixed.collect(),
    })
}

fn validate_inspected_apply(
    program: &ValidatedProgram,
    inspected: InspectedClosure,
    argument_count: usize,
    argument_ownership: Option<&[ArgumentOwnership]>,
    result_ownership: Option<CallableResultOwnership>,
) -> Result<ApplyPlan, VmRefusal> {
    let InspectedClosure {
        encoded_arity,
        function,
        captures,
    } = inspected;
    let callee = program
        .function(function)
        .ok_or(VmRefusal::MalformedClosure {
            reason: "target function is absent",
        })?;
    if callee.arity.checked_add(1) != Some(encoded_arity) {
        return Err(VmRefusal::MalformedClosure {
            reason: "encoded arity does not match the target function",
        });
    }

    if captures.len() >= usize::from(callee.arity) {
        return Err(VmRefusal::MalformedClosure {
            reason: "fixed arguments exhaust the target arity",
        });
    }
    let required = usize::from(callee.arity) - captures.len();
    let expected_result_ownership = if argument_count < required {
        CallableResultOwnership::Owned
    } else {
        callee.result_ownership
    };
    if let Some(actual) = result_ownership
        && argument_count <= required
        && actual != expected_result_ownership
    {
        return Err(VmRefusal::ApplyResultOwnershipMismatch {
            function,
            expected: expected_result_ownership,
            actual,
        });
    }
    if argument_count > required && callee.result_ownership != CallableResultOwnership::Owned {
        return Err(VmRefusal::ApplyResultOwnershipMismatch {
            function,
            expected: CallableResultOwnership::Owned,
            actual: callee.result_ownership,
        });
    }
    if let Some(actual) = argument_ownership {
        let segment = argument_count.min(required);
        let expected =
            &callee.parameter_ownership[captures.len()..captures.len().saturating_add(segment)];
        if let Some((argument, (expected, actual))) = expected
            .iter()
            .copied()
            .zip(actual.iter().copied())
            .enumerate()
            .find(|(_, (expected, actual))| expected != actual)
        {
            return Err(VmRefusal::ApplyOwnershipMismatch {
                function,
                argument,
                expected,
                actual,
            });
        }
        if argument_count < required
            && let Some(argument) = actual
                .iter()
                .position(|disposition| *disposition == ArgumentOwnership::Unique)
        {
            return Err(VmRefusal::ApplyUniquePartial { function, argument });
        }
    }
    Ok(ApplyPlan {
        function,
        captures,
        required,
    })
}

fn finish_apply(
    plan: ApplyPlan,
    args: Vec<Obj>,
    argument_ownership: Option<Vec<ArgumentOwnership>>,
) -> PreparedApply {
    let ApplyPlan {
        function,
        mut captures,
        required,
    } = plan;
    if args.len() < required {
        captures.extend(args);
        return PreparedApply::Partial { function, captures };
    }

    let mut args = args.into_iter();
    captures.extend(args.by_ref().take(required));
    let remainder_ownership = argument_ownership
        .map(|ownership| ownership.into_iter().skip(required).collect())
        .unwrap_or_default();
    PreparedApply::Call {
        function,
        args: captures,
        remainder: args.collect(),
        remainder_ownership,
    }
}

fn push_call(
    program: &ValidatedProgram,
    stack: &mut Vec<Frame>,
    function: FunctionId,
    args: Vec<Obj>,
    return_to: ReturnTo,
    max_stack_depth: u64,
    location: &str,
) -> Result<u64, Stop> {
    let next_len = stack.len().checked_add(1).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-RESOURCE-ACCOUNTING",
            "stack length overflowed",
        ))
    })?;
    let next_depth = u64::try_from(next_len).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-RESOURCE-ACCOUNTING",
            "stack depth does not fit the resource counter",
        ))
    })?;
    if next_depth > max_stack_depth {
        return Err(stack_exhausted(max_stack_depth, next_depth, location));
    }
    let callee = program.function(function).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-TARGET",
            format!("validated call target {} disappeared", function.get()),
        ))
    })?;
    if args.len() != usize::from(callee.arity) {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-ARITY",
            format!(
                "function {} received {} arguments after validation, expected {}",
                function.get(),
                args.len(),
                callee.arity
            ),
        )));
    }
    let mut registers = empty_registers(callee.register_count);
    for (slot, value) in registers.iter_mut().zip(args) {
        *slot = Some(value);
    }
    stack.push(Frame {
        function,
        pc: 0,
        registers,
        return_to: Some(return_to),
    });
    Ok(next_depth)
}

fn current_frame(stack: &[Frame]) -> Result<&Frame, Stop> {
    stack.last().ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-FRAME-STACK",
            "execution attempted to read an empty frame stack",
        ))
    })
}

fn current_frame_mut(stack: &mut [Frame]) -> Result<&mut Frame, Stop> {
    stack.last_mut().ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-FRAME-STACK",
            "execution attempted to mutate an empty frame stack",
        ))
    })
}

fn empty_registers(count: u16) -> Vec<Option<Obj>> {
    std::iter::repeat_with(|| None)
        .take(usize::from(count))
        .collect()
}

fn usage(steps: u64, peak_stack_depth: u64) -> ExecutionUsage {
    ExecutionUsage {
        steps,
        system_polls: steps,
        peak_stack_depth,
    }
}

fn execution_steps_exhausted(allowed: u64, observed: u64, location: &str) -> Stop {
    Stop::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::ExecutionSteps,
            allowed,
            observed,
        })
        .with_progress(location),
    )
}

fn heartbeat_exhausted(consumed: u64, limit: u64, location: &str) -> Stop {
    Stop::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::Heartbeats { consumed, limit },
            allowed: limit,
            observed: consumed,
        })
        .with_progress(location),
    )
}

fn stack_exhausted(allowed: u64, observed: u64, location: &str) -> Stop {
    Stop::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::RecursionDepth { limit: allowed },
            allowed,
            observed,
        })
        .with_progress(location),
    )
}

fn advance(frame: &mut Frame) -> Result<(), Stop> {
    frame.pc = frame.pc.checked_add(1).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-PC",
            "program counter overflowed",
        ))
    })?;
    Ok(())
}

fn register(frame: &Frame, register: Register) -> Result<&Obj, Stop> {
    frame
        .registers
        .get(register.index())
        .and_then(Option::as_ref)
        .ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-REGISTER",
                format!(
                    "function {} pc {} read missing register {}",
                    frame.function.get(),
                    frame.pc,
                    register.get()
                ),
            ))
        })
}

fn clone_register(frame: &Frame, register_id: Register) -> Result<Obj, Stop> {
    register(frame, register_id).map(Obj::clone_ref)
}

fn clone_registers(
    frame: &Frame,
    registers: impl IntoIterator<Item = Register>,
) -> Result<Vec<Obj>, Stop> {
    registers
        .into_iter()
        .map(|register_id| clone_register(frame, register_id))
        .collect()
}

fn resolve_intrinsic_plan(
    row: &str,
    declared_arguments: &[ArgumentOwnership],
    declared_result: ResultOwnership,
) -> Result<IntrinsicPlan, VmRefusal> {
    let generated = EXTERN_ROWS
        .iter()
        .find(|generated| generated.id == row)
        .ok_or_else(|| VmRefusal::UnknownIntrinsic {
            row: row.to_string(),
        })?;
    let ownership = ExternOwnership::parse(generated.ownership).map_err(|error| {
        VmRefusal::IntrinsicOwnershipContract {
            row: row.to_string(),
            reason: error.message().to_string(),
        }
    })?;
    let expected_arguments = ownership
        .argument_ownership(declared_arguments.len())
        .map_err(|error| VmRefusal::IntrinsicOwnershipContract {
            row: row.to_string(),
            reason: error.message().to_string(),
        })?;
    if let Some((argument, (expected, actual))) = expected_arguments
        .into_iter()
        .map(runtime_argument_ownership)
        .zip(declared_arguments.iter().copied())
        .enumerate()
        .find(|(_, (expected, actual))| expected != actual)
    {
        return Err(VmRefusal::IntrinsicOwnershipMismatch {
            row: row.to_string(),
            argument,
            expected,
            actual,
        });
    }
    let expected_result =
        ownership
            .result_ownership()
            .map_err(|error| VmRefusal::IntrinsicOwnershipContract {
                row: row.to_string(),
                reason: error.message().to_string(),
            })?;
    let expected_result = match expected_result {
        ContractResultOwnership::Owned => ResultOwnership::Owned,
        ContractResultOwnership::Borrowed => ResultOwnership::Borrowed,
        ContractResultOwnership::Scalar => ResultOwnership::Scalar,
        ContractResultOwnership::RawObject => ResultOwnership::RawObject,
    };
    if expected_result != declared_result {
        return Err(VmRefusal::IntrinsicResultOwnershipMismatch {
            row: row.to_string(),
            expected: expected_result,
            actual: declared_result,
        });
    }
    Ok(IntrinsicPlan {
        row: generated.id,
        implementation: IntrinsicImplementation::for_row(generated.id),
    })
}

const fn runtime_argument_ownership(ownership: ContractArgumentOwnership) -> ArgumentOwnership {
    match ownership {
        ContractArgumentOwnership::Borrowed => ArgumentOwnership::Borrowed,
        ContractArgumentOwnership::Owned => ArgumentOwnership::Owned,
        ContractArgumentOwnership::Unique => ArgumentOwnership::Unique,
        ContractArgumentOwnership::Scalar => ArgumentOwnership::Scalar,
    }
}

fn finish_intrinsic_result(
    row: &str,
    expected: ResultOwnership,
    result: IntrinsicResult,
) -> Result<Obj, VmRefusal> {
    let actual = result.ownership();
    if actual != expected {
        return Err(VmRefusal::IntrinsicResultImplementationMismatch {
            row: row.to_string(),
            expected,
            actual,
        });
    }
    let value = result.into_object();
    if expected == ResultOwnership::Scalar && !value.is_scalar() {
        return Err(VmRefusal::IntrinsicResultKind {
            row: row.to_string(),
            expected: "tagged scalar",
            actual: value_kind(&value),
        });
    }
    Ok(value)
}

fn finish_callable_result(
    function: FunctionId,
    expected: CallableResultOwnership,
    value: Obj,
) -> Result<Obj, VmRefusal> {
    let matches = match expected {
        CallableResultOwnership::Owned => !value.is_scalar(),
        CallableResultOwnership::Scalar => value.is_scalar(),
    };
    if !matches {
        return Err(VmRefusal::CallableResultKind {
            function,
            expected,
            actual: value_kind(&value),
        });
    }
    Ok(value)
}

fn transfer_intrinsic_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(
        frame,
        registers,
        ownership,
        "FLBC-INTRINSIC-ARGUMENTS",
        "intrinsic",
    )
}

fn transfer_call_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(
        frame,
        registers,
        ownership,
        "FLBC-CALL-ARGUMENTS",
        "direct-call",
    )
}

fn transfer_closure_captures(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(
        frame,
        registers,
        ownership,
        "FLBC-CLOSURE-CAPTURES",
        "closure capture",
    )
}

fn transfer_apply_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(frame, registers, ownership, "FLBC-APPLY-ARGUMENTS", "Apply")
}

fn transfer_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
    fault_code: &'static str,
    boundary: &'static str,
) -> Result<Vec<Obj>, Stop> {
    let mut borrowed = Vec::new();
    borrowed.try_reserve_exact(registers.len()).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            fault_code,
            format!(
                "could not reserve {} borrowed {boundary} argument slots",
                registers.len()
            ),
        ))
    })?;
    borrowed.resize_with(registers.len(), || None::<Obj>);
    for (index, (register_id, disposition)) in registers
        .iter()
        .copied()
        .zip(ownership.iter().copied())
        .enumerate()
    {
        if !disposition.consumes() {
            borrowed[index] = Some(clone_register(frame, register_id)?);
        }
    }
    for (register_id, disposition) in registers.iter().copied().zip(ownership.iter().copied()) {
        if disposition.consumes() {
            register(frame, register_id)?;
        }
    }

    let mut values = Vec::new();
    values.try_reserve_exact(registers.len()).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            fault_code,
            format!(
                "could not reserve {} transferred {boundary} arguments",
                registers.len()
            ),
        ))
    })?;
    for (index, (register_id, disposition)) in registers
        .iter()
        .copied()
        .zip(ownership.iter().copied())
        .enumerate()
    {
        if disposition.consumes() {
            values.push(take_register(frame, register_id)?);
        } else {
            values.push(borrowed[index].take().ok_or_else(|| {
                Stop::InternalFault(InternalFault::new(
                    fault_code,
                    format!("borrowed {boundary} argument {index} was not prepared"),
                ))
            })?);
        }
    }
    Ok(values)
}

fn take_register(frame: &mut Frame, register: Register) -> Result<Obj, Stop> {
    frame
        .registers
        .get_mut(register.index())
        .and_then(Option::take)
        .ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-REGISTER",
                format!(
                    "function {} pc {} moved missing register {}",
                    frame.function.get(),
                    frame.pc,
                    register.get()
                ),
            ))
        })
}

fn set_register(frame: &mut Frame, register: Register, value: Obj) -> Result<(), Stop> {
    let slot = frame.registers.get_mut(register.index()).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-REGISTER",
            format!(
                "function {} pc {} wrote missing register {}",
                frame.function.get(),
                frame.pc,
                register.get()
            ),
        ))
    })?;
    *slot = Some(value);
    Ok(())
}

fn invoke_intrinsic(
    implementation: IntrinsicImplementation,
    row: &str,
    args: &[Obj],
) -> Result<IntrinsicResult, VmRefusal> {
    match implementation {
        IntrinsicImplementation::NatAdd => {
            expect_arity(row, args, 2)?;
            let lhs = nat_value(&args[0], "Nat.add", 0)?;
            let rhs = nat_value(&args[1], "Nat.add", 1)?;
            let sum = lhs.checked_add(rhs).ok_or(VmRefusal::NatOverflow {
                operation: "Nat.add",
            })?;
            if sum > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "Nat.add",
                });
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(sum)))
        }
        IntrinsicImplementation::NatSub => {
            expect_arity(row, args, 2)?;
            let lhs = nat_value(&args[0], "Nat.sub", 0)?;
            let rhs = nat_value(&args[1], "Nat.sub", 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(lhs.saturating_sub(rhs))))
        }
        IntrinsicImplementation::NatMul => {
            expect_arity(row, args, 2)?;
            let lhs = nat_value(&args[0], "Nat.mul", 0)?;
            let rhs = nat_value(&args[1], "Nat.mul", 1)?;
            let product = lhs.checked_mul(rhs).ok_or(VmRefusal::NatOverflow {
                operation: "Nat.mul",
            })?;
            if product > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "Nat.mul",
                });
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(product)))
        }
        IntrinsicImplementation::StringAppend => {
            expect_arity(row, args, 2)?;
            let mut lhs = string_value(&args[0], "String.append", 0)?;
            lhs.push_str(&string_value(&args[1], "String.append", 1)?);
            Ok(IntrinsicResult::owned(Obj::mk_string(&lhs)))
        }
        IntrinsicImplementation::ArraySize => {
            expect_arity(row, args, 1)?;
            let (size, _) = array_value(&args[0], "Array.size", 0)?;
            if size > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "Array.size",
                });
            }
            Ok(IntrinsicResult::raw_object(Obj::mk_nat(size)))
        }
        IntrinsicImplementation::ArrayGetInternal => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.getInternal", 0)?;
            let index = nat_value(&args[1], "Array.getInternal", 1)?;
            if index >= size {
                return Err(VmRefusal::ArrayIndexOutOfBounds { index, size });
            }
            Ok(IntrinsicResult::owned(args[0].array_child(index)))
        }
        IntrinsicImplementation::ArrayGetBorrowed => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.ugetBorrowed", 0)?;
            let index = nat_value(&args[1], "Array.ugetBorrowed", 1)?;
            if index >= size {
                return Err(VmRefusal::ArrayIndexOutOfBounds { index, size });
            }
            Ok(IntrinsicResult::borrowed_promoted(
                args[0].array_child(index),
            ))
        }
        IntrinsicImplementation::ArrayPush => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.push", 0)?;
            let mut items = Vec::with_capacity(size.saturating_add(1));
            for index in 0..size {
                items.push(args[0].array_child(index));
            }
            items.push(args[1].clone_ref());
            Ok(IntrinsicResult::raw_object(Obj::mk_array(items)))
        }
        IntrinsicImplementation::IoCancel => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "IO.cancel", 0, "Task", ValueKind::Task)?;
            if args[0].finished_task_value().is_none() {
                return Err(VmRefusal::UnsupportedTaskState);
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(0)))
        }
        IntrinsicImplementation::IoCheckCancelled => {
            expect_arity(row, args, 0)?;
            // Golem's managerless execution path has no current scheduled
            // task. This is the pin's exact non-task-manager observation;
            // host execution cancellation remains the separate scheduler
            // probe sampled before every instruction.
            Ok(IntrinsicResult::owned(Obj::mk_nat(0)))
        }
        IntrinsicImplementation::IoGetNumHeartbeats => {
            expect_arity(row, args, 0)?;
            Ok(IntrinsicResult::owned(nat_from_u64(
                fln_rt::heartbeat::allocation_heartbeats(),
            )))
        }
        IntrinsicImplementation::IoSetNumHeartbeats => {
            expect_arity(row, args, 1)?;
            let count = nat_low_u64(&args[0], "IO.setNumHeartbeats", 0)?;
            fln_rt::heartbeat::set_allocation_heartbeats(count);
            Ok(IntrinsicResult::owned(Obj::mk_nat(0)))
        }
        IntrinsicImplementation::RefNew => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_ref(args[0].clone_ref())))
        }
        IntrinsicImplementation::RefGet => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.get", 0, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(args[0].ref_get()))
        }
        IntrinsicImplementation::RefTake => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.take", 0, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(args[0].ref_take()))
        }
        IntrinsicImplementation::RefSet => {
            expect_arity(row, args, 2)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.set", 0, "ST.Ref", ValueKind::Ref)?;
            args[0].ref_set(args[1].clone_ref());
            Ok(IntrinsicResult::owned(Obj::mk_nat(0)))
        }
        IntrinsicImplementation::RefSwap => {
            expect_arity(row, args, 2)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.swap", 0, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(
                args[0].ref_swap(args[1].clone_ref()),
            ))
        }
        IntrinsicImplementation::RefPtrEq => {
            expect_arity(row, args, 2)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.ptrEq", 0, "ST.Ref", ValueKind::Ref)?;
            expect_value_kind(&args[1], "ST.Prim.Ref.ptrEq", 1, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(
                if args[0].ref_ptr_eq(&args[1]) { 1 } else { 0 },
            )))
        }
        IntrinsicImplementation::ThunkPure => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_thunk_value(
                args[0].clone_ref(),
            )))
        }
        IntrinsicImplementation::ThunkNew => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "Thunk.mk", 0, "Golem closure", ValueKind::Closure)?;
            if args[0].closure_shell_parts().is_none() {
                return Err(VmRefusal::UnsupportedNativeClosure);
            }
            Ok(IntrinsicResult::owned(Obj::mk_thunk_closure(
                args[0].clone_ref(),
            )))
        }
        IntrinsicImplementation::TaskPure => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_task_pure(
                args[0].clone_ref(),
            )))
        }
        IntrinsicImplementation::TaskGet => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "Task.get", 0, "finished Task", ValueKind::Task)?;
            args[0]
                .finished_task_value()
                .map(IntrinsicResult::owned)
                .ok_or(VmRefusal::UnsupportedTaskState)
        }
        IntrinsicImplementation::ThunkGet
        | IntrinsicImplementation::TaskSpawn
        | IntrinsicImplementation::TaskMap
        | IntrinsicImplementation::TaskBind
        | IntrinsicImplementation::Unsupported => Err(VmRefusal::UnsupportedIntrinsic {
            row: row.to_string(),
        }),
    }
}

fn delayed_thunk_operand(args: Vec<Obj>) -> Result<Obj, VmRefusal> {
    const ROW: &str = "extern:Thunk.get";
    expect_arity(ROW, &args, 1)?;
    let thunk = args
        .into_iter()
        .next()
        .ok_or_else(|| VmRefusal::IntrinsicArity {
            row: ROW.to_string(),
            expected: 1,
            actual: 0,
        })?;
    expect_value_kind(&thunk, "Thunk.get", 0, "Thunk", ValueKind::Thunk)?;
    Ok(thunk)
}

fn cache_thunk_value(thunk: &Obj, value: &Obj) -> Result<(), Stop> {
    if thunk.complete_claimed_thunk(value.clone_ref()) {
        return Ok(());
    }
    Err(Stop::InternalFault(InternalFault::new(
        "FLBC-THUNK-COMPLETION",
        "claimed thunk rejected its single completion",
    )))
}

fn managerless_task_application(
    implementation: IntrinsicImplementation,
    row: &'static str,
    args: Vec<Obj>,
) -> Result<ManagerlessTaskApplication, VmRefusal> {
    match implementation {
        IntrinsicImplementation::TaskSpawn => {
            let [closure, priority] = exact_owned_args(row, args)?;
            expect_golem_task_closure(&closure, "Task.spawn", 0)?;
            nat_value(&priority, "Task.spawn", 1)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                argument: Obj::mk_nat(0),
                argument_ownership: ArgumentOwnership::Scalar,
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        IntrinsicImplementation::TaskMap => {
            let [closure, task, priority, sync] = exact_owned_args(row, args)?;
            expect_golem_task_closure(&closure, "Task.map", 0)?;
            expect_value_kind(&task, "Task.map", 1, "finished Task", ValueKind::Task)?;
            nat_value(&priority, "Task.map", 2)?;
            bool_value(&sync, "Task.map", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                argument,
                argument_ownership: ArgumentOwnership::Owned,
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        IntrinsicImplementation::TaskBind => {
            let [task, closure, priority, sync] = exact_owned_args(row, args)?;
            expect_value_kind(&task, "Task.bind", 0, "finished Task", ValueKind::Task)?;
            expect_golem_task_closure(&closure, "Task.bind", 1)?;
            nat_value(&priority, "Task.bind", 2)?;
            bool_value(&sync, "Task.bind", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                argument,
                argument_ownership: ArgumentOwnership::Owned,
                completion: ManagerlessTaskCompletion::RequireFinishedTask,
            })
        }
        IntrinsicImplementation::NatAdd
        | IntrinsicImplementation::NatSub
        | IntrinsicImplementation::NatMul
        | IntrinsicImplementation::StringAppend
        | IntrinsicImplementation::ArraySize
        | IntrinsicImplementation::ArrayGetInternal
        | IntrinsicImplementation::ArrayGetBorrowed
        | IntrinsicImplementation::ArrayPush
        | IntrinsicImplementation::IoCancel
        | IntrinsicImplementation::IoCheckCancelled
        | IntrinsicImplementation::IoGetNumHeartbeats
        | IntrinsicImplementation::IoSetNumHeartbeats
        | IntrinsicImplementation::RefNew
        | IntrinsicImplementation::RefGet
        | IntrinsicImplementation::RefTake
        | IntrinsicImplementation::RefSet
        | IntrinsicImplementation::RefSwap
        | IntrinsicImplementation::RefPtrEq
        | IntrinsicImplementation::ThunkPure
        | IntrinsicImplementation::ThunkNew
        | IntrinsicImplementation::ThunkGet
        | IntrinsicImplementation::TaskPure
        | IntrinsicImplementation::TaskGet
        | IntrinsicImplementation::Unsupported => Err(VmRefusal::UnsupportedIntrinsic {
            row: row.to_string(),
        }),
    }
}

fn exact_owned_args<const N: usize>(row: &str, args: Vec<Obj>) -> Result<[Obj; N], VmRefusal> {
    args.try_into()
        .map_err(|args: Vec<Obj>| VmRefusal::IntrinsicArity {
            row: row.to_string(),
            expected: N,
            actual: args.len(),
        })
}

fn expect_golem_task_closure(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<(), VmRefusal> {
    expect_value_kind(
        value,
        operation,
        argument,
        "Golem closure",
        ValueKind::Closure,
    )?;
    if value.closure_shell_parts().is_none() {
        return Err(VmRefusal::UnsupportedNativeClosure);
    }
    Ok(())
}

fn complete_managerless_task(
    completion: ManagerlessTaskCompletion,
    value: Obj,
) -> Result<Obj, VmRefusal> {
    match completion {
        ManagerlessTaskCompletion::WrapPure => Ok(Obj::mk_task_pure(value)),
        ManagerlessTaskCompletion::RequireFinishedTask => {
            expect_value_kind(
                &value,
                "Task.bind result",
                0,
                "finished Task",
                ValueKind::Task,
            )?;
            if value.finished_task_value().is_none() {
                return Err(VmRefusal::UnsupportedTaskState);
            }
            Ok(value)
        }
    }
}

fn expect_arity(row: &str, args: &[Obj], expected: usize) -> Result<(), VmRefusal> {
    if args.len() != expected {
        return Err(VmRefusal::IntrinsicArity {
            row: row.to_string(),
            expected,
            actual: args.len(),
        });
    }
    Ok(())
}

fn expect_value_kind(
    value: &Obj,
    operation: &'static str,
    argument: usize,
    expected: &'static str,
    expected_kind: ValueKind,
) -> Result<(), VmRefusal> {
    let actual = value_kind(value);
    if actual != expected_kind {
        return Err(VmRefusal::TypeMismatch {
            operation,
            argument,
            expected,
            actual,
        });
    }
    Ok(())
}

fn nat_value(value: &Obj, operation: &'static str, argument: usize) -> Result<usize, VmRefusal> {
    if !value.is_scalar() {
        return Err(type_mismatch(operation, argument, "Nat scalar", value));
    }
    Ok(value.unbox())
}

fn nat_low_u64(value: &Obj, operation: &'static str, argument: usize) -> Result<u64, VmRefusal> {
    if value.is_scalar() {
        return Ok(value.unbox() as u64);
    }
    if value_kind(value) != ValueKind::Mpz {
        return Err(type_mismatch(operation, argument, "Nat", value));
    }
    let (_, size, limbs) = value.mpz_view();
    if size < 0 {
        return Err(type_mismatch(operation, argument, "Nat", value));
    }
    Ok(limbs.first().copied().unwrap_or(0))
}

fn nat_from_u64(value: u64) -> Obj {
    if value <= (usize::MAX >> 1) as u64 {
        Obj::mk_nat(value as usize)
    } else {
        Obj::mk_mpz(&[value], false)
    }
}

fn bool_value(value: &Obj, operation: &'static str, argument: usize) -> Result<bool, VmRefusal> {
    let value = nat_value(value, operation, argument)?;
    match value {
        0 => Ok(false),
        1 => Ok(true),
        value => Err(VmRefusal::InvalidBoolScalar {
            operation,
            argument,
            value,
        }),
    }
}

fn array_value(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<(usize, usize), VmRefusal> {
    if value_kind(value) != ValueKind::Array {
        return Err(type_mismatch(operation, argument, "Array", value));
    }
    Ok(value.array_view())
}

fn string_value(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<String, VmRefusal> {
    if value_kind(value) != ValueKind::String {
        return Err(type_mismatch(operation, argument, "String", value));
    }
    let (size, _, _, bytes) = value.string_view();
    if size == 0 || size > bytes.len() || bytes[size - 1] != 0 {
        return Err(VmRefusal::InvalidStringObject);
    }
    std::str::from_utf8(&bytes[..size - 1])
        .map(str::to_string)
        .map_err(|_| VmRefusal::InvalidStringObject)
}

fn type_mismatch(
    operation: &'static str,
    argument: usize,
    expected: &'static str,
    value: &Obj,
) -> VmRefusal {
    VmRefusal::TypeMismatch {
        operation,
        argument,
        expected,
        actual: value_kind(value),
    }
}

/// Derive the runtime category without exposing an address or host shadow.
pub fn value_kind(value: &Obj) -> ValueKind {
    if value.is_scalar() {
        return ValueKind::Scalar;
    }
    let tag = value.obj_tag();
    if tag <= usize::from(abi::TAG_MAX_CTOR_TAG) {
        return ValueKind::Ctor(u8::try_from(tag).unwrap_or(abi::TAG_RESERVED));
    }
    match tag {
        tag if tag == usize::from(abi::TAG_PROMISE) => ValueKind::Promise,
        tag if tag == usize::from(abi::TAG_CLOSURE) => ValueKind::Closure,
        tag if tag == usize::from(abi::TAG_ARRAY) => ValueKind::Array,
        tag if tag == usize::from(abi::TAG_STRUCT_ARRAY) => ValueKind::StructArray,
        tag if tag == usize::from(abi::TAG_SCALAR_ARRAY) => ValueKind::ScalarArray,
        tag if tag == usize::from(abi::TAG_STRING) => ValueKind::String,
        tag if tag == usize::from(abi::TAG_MPZ) => ValueKind::Mpz,
        tag if tag == usize::from(abi::TAG_THUNK) => ValueKind::Thunk,
        tag if tag == usize::from(abi::TAG_TASK) => ValueKind::Task,
        tag if tag == usize::from(abi::TAG_REF) => ValueKind::Ref,
        tag if tag == usize::from(abi::TAG_EXTERNAL) => ValueKind::External,
        _ => ValueKind::Reserved,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intrinsic_result_adapter_refuses_class_and_scalar_kind_drift() {
        let scalar_kind = finish_intrinsic_result(
            "extern:Float.abs",
            ResultOwnership::Scalar,
            IntrinsicResult {
                ownership: ResultOwnership::Scalar,
                value: Obj::mk_string("not-a-scalar"),
            },
        );
        assert!(matches!(
            scalar_kind,
            Err(VmRefusal::IntrinsicResultKind {
                ref row,
                expected: "tagged scalar",
                actual: ValueKind::String,
            }) if row == "extern:Float.abs"
        ));

        let class = finish_intrinsic_result(
            "extern:Array.ugetBorrowed",
            ResultOwnership::Borrowed,
            IntrinsicResult::owned(Obj::mk_nat(0)),
        );
        assert!(matches!(
            class,
            Err(VmRefusal::IntrinsicResultImplementationMismatch {
                ref row,
                expected: ResultOwnership::Borrowed,
                actual: ResultOwnership::Owned,
            }) if row == "extern:Array.ugetBorrowed"
        ));
    }
}
