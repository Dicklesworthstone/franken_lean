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
//! through the ordinary return continuation. The manager-absent
//! `BaseIO.asTask`, `BaseIO.mapTask`, `BaseIO.bindTask`, `Task.spawn`,
//! `Task.map`, and `Task.bind` fallbacks use that same continuation machinery
//! and produce only finished tasks. The
//! allocation-linked `IO.getNumHeartbeats` / `IO.setNumHeartbeats` rows share
//! Marrow's runtime counter and preserve arbitrary-`Nat` low-64 semantics. In
//! the certified 64-bit runtime, the pure `System.Platform` word-size and
//! OS-family probes report the build target directly. Definition execution is
//! post-initialization, so `IO.initializing` observes false; module initializer
//! execution remains outside this slice. In this managerless state,
//! `IO.getTaskState` reports finished, `IO.wait`
//! returns the finished value, `IO.waitAny` selects the first finished task,
//! `IO.checkCanceled`
//! observes false, and `IO.cancel` is the pinned no-op on a finished task;
//! host execution cancellation remains a distinct non-authoritative stop.
//! Scheduled tasks, concurrent thunk forcing, ambient IO, and capability
//! effects remain outside this slice.

use crate::extern_row::{
    ArgumentOwnership as ContractArgumentOwnership, Ownership as ExternOwnership,
    ResultOwnership as ContractResultOwnership,
};
use crate::extern_table_generated::{EXTERN_ROW_CONTRACT_ROOT, EXTERN_ROWS};
use fln_bignum::nat::{BigNat, BigNatView, MAX_LIMBS};
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
    /// Maximum normalized mpz-limb storage charged to one Nat arithmetic result.
    ///
    /// This is a Golem-owned memory ceiling, not Lean heartbeat fuel. The
    /// Growth paths charge their operation-specific allocation bound before
    /// allocating; exhaustion is an outcome-level [`Inconclusive`], never an
    /// authoritative VM refusal.
    pub max_nat_magnitude_bytes: u64,
}

impl Default for ExecutionLimits {
    fn default() -> Self {
        Self {
            max_steps: 1_000_000,
            max_stack_depth: 1_000,
            max_nat_magnitude_bytes: 8 * 1024 * 1024,
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
    BaseIoAsTask,
    BaseIoBindTask,
    BaseIoMapTask,
    NatAdd,
    NatBeq,
    NatBle,
    NatSub,
    NatMul,
    NatDiv,
    NatGcd,
    NatLand,
    NatLog2,
    NatLor,
    NatMod,
    NatPow,
    NatPred,
    NatShiftLeft,
    NatShiftRight,
    NatXor,
    StringAppend,
    StringAtEnd,
    StringCompare,
    StringDecEq,
    StringDecLt,
    StringLength,
    StringUtf8ByteSize,
    StringCapitalize,
    StringContains,
    StringDrop,
    StringDropRight,
    StringExtract,
    StringInternalIsEmpty,
    StringInternalIsPrefixOf,
    StringNext,
    StringPrev,
    StringPush,
    StringTrim,
    ArraySize,
    ArrayGetInternal,
    ArrayUGet,
    ArrayGetBorrowed,
    ArrayUSize,
    ArrayPush,
    PlatformNumBits,
    PlatformIsWindows,
    PlatformIsOsx,
    PlatformIsEmscripten,
    IoCancel,
    IoCheckCancelled,
    IoInitializing,
    IoGetTaskState,
    IoWait,
    IoWaitAny,
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
            "extern:BaseIO.asTask" => Self::BaseIoAsTask,
            "extern:BaseIO.bindTask" => Self::BaseIoBindTask,
            "extern:BaseIO.mapTask" => Self::BaseIoMapTask,
            "extern:Nat.add" => Self::NatAdd,
            "extern:Nat.beq" => Self::NatBeq,
            "extern:Nat.ble" => Self::NatBle,
            "extern:Nat.sub" => Self::NatSub,
            "extern:Nat.mul" => Self::NatMul,
            "extern:Nat.div" => Self::NatDiv,
            "extern:Nat.gcd" => Self::NatGcd,
            "extern:Nat.land" => Self::NatLand,
            "extern:Nat.log2" => Self::NatLog2,
            "extern:Nat.lor" => Self::NatLor,
            "extern:Nat.mod" => Self::NatMod,
            "extern:Nat.pow" => Self::NatPow,
            "extern:Nat.pred" => Self::NatPred,
            "extern:Nat.shiftLeft" => Self::NatShiftLeft,
            "extern:Nat.shiftRight" => Self::NatShiftRight,
            "extern:Nat.xor" => Self::NatXor,
            "extern:String.Internal.append" => Self::StringAppend,
            "extern:String.Internal.atEnd" => Self::StringAtEnd,
            "extern:String.Internal.length" => Self::StringLength,
            "extern:String.append" => Self::StringAppend,
            "extern:String.atEnd" | "extern:String.Pos.Raw.atEnd" => Self::StringAtEnd,
            "extern:String.compare" => Self::StringCompare,
            "extern:String.decEq" => Self::StringDecEq,
            "extern:String.decidableLT" => Self::StringDecLt,
            "extern:String.length" => Self::StringLength,
            "extern:String.utf8ByteSize" => Self::StringUtf8ByteSize,
            "extern:String.Internal.capitalize" => Self::StringCapitalize,
            "extern:String.Internal.contains" => Self::StringContains,
            "extern:String.Internal.drop" => Self::StringDrop,
            "extern:String.Internal.dropRight" => Self::StringDropRight,
            "extern:String.Internal.extract"
            | "extern:String.extract"
            | "extern:String.Pos.Raw.extract" => Self::StringExtract,
            "extern:String.Internal.isEmpty" => Self::StringInternalIsEmpty,
            "extern:String.Internal.isPrefixOf" => Self::StringInternalIsPrefixOf,
            "extern:String.Internal.next" | "extern:String.next" | "extern:String.Pos.Raw.next" => {
                Self::StringNext
            }
            "extern:String.Internal.prev" | "extern:String.prev" | "extern:String.Pos.Raw.prev" => {
                Self::StringPrev
            }
            "extern:String.push" => Self::StringPush,
            "extern:String.Internal.trim" => Self::StringTrim,
            "extern:Array.size" => Self::ArraySize,
            "extern:Array.getInternal" => Self::ArrayGetInternal,
            "extern:Array.uget" => Self::ArrayUGet,
            "extern:Array.ugetBorrowed" => Self::ArrayGetBorrowed,
            "extern:Array.usize" => Self::ArrayUSize,
            "extern:Array.push" => Self::ArrayPush,
            "extern:System.Platform.getNumBits" => Self::PlatformNumBits,
            "extern:System.Platform.getIsWindows" => Self::PlatformIsWindows,
            "extern:System.Platform.getIsOSX" => Self::PlatformIsOsx,
            "extern:System.Platform.getIsEmscripten" => Self::PlatformIsEmscripten,
            "extern:IO.cancel" => Self::IoCancel,
            "extern:IO.checkCanceled" => Self::IoCheckCancelled,
            "extern:IO.initializing" => Self::IoInitializing,
            "extern:IO.getTaskState" => Self::IoGetTaskState,
            "extern:IO.wait" => Self::IoWait,
            "extern:IO.waitAny" => Self::IoWaitAny,
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
        matches!(
            self,
            Self::BaseIoAsTask
                | Self::BaseIoBindTask
                | Self::BaseIoMapTask
                | Self::TaskSpawn
                | Self::TaskMap
                | Self::TaskBind
        )
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
    InvalidArrayObject,
    InvalidCtorObject,
    InvalidRefObject,
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
            Self::InvalidArrayObject => write!(f, "Marrow Array object header is inconsistent"),
            Self::InvalidCtorObject => {
                write!(f, "Marrow constructor object slot is past the allocation")
            }
            Self::InvalidRefObject => write!(f, "Marrow ST.Ref cell is empty"),
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
    arguments: Vec<Obj>,
    argument_ownership: Vec<ArgumentOwnership>,
    completion: ManagerlessTaskCompletion,
}

struct IntrinsicResult {
    ownership: ResultOwnership,
    value: Obj,
}

enum IntrinsicFailure {
    Refused(VmRefusal),
    NatMagnitudeLimit { allowed: u64, observed: u64 },
}

impl From<VmRefusal> for IntrinsicFailure {
    fn from(refusal: VmRefusal) -> Self {
        Self::Refused(refusal)
    }
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

    fn scalar(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::Scalar,
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
            Instruction::NatBig { dst, limbs_le } => {
                let observed = u64::try_from(limbs_le.len())
                    .unwrap_or(u64::MAX)
                    .saturating_mul(8);
                let allowed = limits.max_nat_magnitude_bytes.min(
                    u64::try_from(MAX_LIMBS)
                        .unwrap_or(u64::MAX)
                        .saturating_mul(8),
                );
                if observed > allowed {
                    return Err(nat_magnitude_exhausted(allowed, observed, &location));
                }
                set_register(
                    current_frame_mut(&mut stack)?,
                    dst,
                    Obj::mk_mpz(&limbs_le, false),
                )?;
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
                    let Some(projected) = value.try_ctor_child(usize::from(field)) else {
                        return Ok(VmExit::Refused {
                            refusal: VmRefusal::InvalidCtorObject,
                            usage: usage(steps, peak_stack_depth),
                        });
                    };
                    projected
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
                    match prepare_internal_apply_many(
                        program,
                        &application.closure,
                        application.arguments,
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
                                    "managerless task arguments over-applied a validated closure",
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
                    match invoke_intrinsic(
                        plan.implementation,
                        plan.row,
                        &values,
                        limits.max_nat_magnitude_bytes,
                    ) {
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
                        Err(IntrinsicFailure::Refused(refusal)) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                        Err(IntrinsicFailure::NatMagnitudeLimit { allowed, observed }) => {
                            return Err(nat_magnitude_exhausted(allowed, observed, &location));
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
                // FIR BranchZero types the condition as Nat | Bool. Bool is
                // always a 0/1 scalar; a Nat may be a nonnegative mpz after
                // the wide-Nat landing. A well-typed 2^64 is nonzero, not
                // "not a Nat".
                let is_zero =
                    match with_nat_view(condition, "jump_if_zero", 0, |view| view.is_zero()) {
                        Ok(is_zero) => is_zero,
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    };
                let target = if is_zero { zero } else { nonzero };
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
    prepare_internal_apply_many(program, closure, vec![argument], vec![argument_ownership])
}

fn prepare_internal_apply_many(
    program: &ValidatedProgram,
    closure: &Obj,
    arguments: Vec<Obj>,
    argument_ownership: Vec<ArgumentOwnership>,
) -> Result<PreparedApply, VmRefusal> {
    let plan = plan_apply(
        program,
        closure,
        arguments.len(),
        Some(&argument_ownership),
        None,
    )?;
    Ok(finish_apply(plan, arguments, Some(argument_ownership)))
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

fn nat_magnitude_exhausted(allowed: u64, observed: u64, location: &str) -> Stop {
    Stop::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::Memory {
                limit_bytes: allowed,
            },
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
        // Schema v12: a Nat is a tagged scalar or a nonnegative mpz.
        // A String/Array/ctor is not a Nat just because the union exists.
        CallableResultOwnership::OwnedOrScalar => is_nat_abi(&value),
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

/// Lean `Nat` at the ABI: small values are tagged scalars; large values are
/// nonnegative mpz objects. Negative mpz is `Int`, not `Nat`.
fn is_nat_abi(value: &Obj) -> bool {
    if value.is_scalar() {
        return true;
    }
    if value_kind(value) != ValueKind::Mpz {
        return false;
    }
    matches!(value.try_mpz_view(), Some((_, size, _)) if size >= 0)
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
    max_nat_magnitude_bytes: u64,
) -> Result<IntrinsicResult, IntrinsicFailure> {
    let max_nat_magnitude_bytes = max_nat_magnitude_bytes.min(
        u64::try_from(MAX_LIMBS)
            .expect("the bignum limb ceiling fits u64")
            .saturating_mul(8),
    );
    match implementation {
        IntrinsicImplementation::NatAdd => {
            expect_arity(row, args, 2)?;
            let sum = with_nat_views(
                &args[0],
                &args[1],
                "Nat.add",
                |left, right| -> Result<_, IntrinsicFailure> {
                    let result_bits = if left.is_zero() && right.is_zero() {
                        0
                    } else {
                        u128::from(left.bit_length().max(right.bit_length())) + 1
                    };
                    ensure_nat_bits(max_nat_magnitude_bytes, result_bits)?;
                    Ok(left.add(right))
                },
            )??;
            finish_nat_result(sum, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatBeq => {
            expect_arity(row, args, 2)?;
            let equal =
                with_nat_views(&args[0], &args[1], "Nat.beq", |left, right| left.beq(right))?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(if equal {
                1
            } else {
                0
            })))
        }
        IntrinsicImplementation::NatBle => {
            expect_arity(row, args, 2)?;
            let less_or_equal =
                with_nat_views(&args[0], &args[1], "Nat.ble", |left, right| left.ble(right))?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(if less_or_equal {
                1
            } else {
                0
            })))
        }
        IntrinsicImplementation::NatSub => {
            expect_arity(row, args, 2)?;
            let difference = with_nat_views(
                &args[0],
                &args[1],
                "Nat.sub",
                |left, right| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(max_nat_magnitude_bytes, u128::from(left.bit_length()))?;
                    Ok(left.sub(right))
                },
            )??;
            finish_nat_result(difference, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatMul => {
            expect_arity(row, args, 2)?;
            let product = with_nat_views(
                &args[0],
                &args[1],
                "Nat.mul",
                |left, right| -> Result<_, IntrinsicFailure> {
                    let result_bits = if left.is_zero() || right.is_zero() {
                        0
                    } else {
                        u128::from(left.bit_length()) + u128::from(right.bit_length())
                    };
                    ensure_nat_bits(max_nat_magnitude_bytes, result_bits)?;
                    Ok(left.mul(right))
                },
            )??;
            finish_nat_result(product, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatDiv => {
            expect_arity(row, args, 2)?;
            let quotient = with_nat_views(
                &args[0],
                &args[1],
                "Nat.div",
                |dividend, divisor| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(max_nat_magnitude_bytes, u128::from(dividend.bit_length()))?;
                    Ok(dividend.div(divisor))
                },
            )??;
            finish_nat_result(quotient, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatGcd => {
            expect_arity(row, args, 2)?;
            let gcd = with_nat_views(
                &args[0],
                &args[1],
                "Nat.gcd",
                |left, right| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(left.bit_length().max(right.bit_length())),
                    )?;
                    Ok(left.gcd(right))
                },
            )??;
            finish_nat_result(gcd, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatLand => {
            expect_arity(row, args, 2)?;
            let result = with_nat_views(
                &args[0],
                &args[1],
                "Nat.land",
                |left, right| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(left.bit_length().min(right.bit_length())),
                    )?;
                    Ok(left.land(right))
                },
            )??;
            finish_nat_result(result, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatLog2 => {
            expect_arity(row, args, 1)?;
            let result = with_nat_view(&args[0], "Nat.log2", 0, |value| {
                BigNat::from_u64(value.bit_length().saturating_sub(1))
            })?;
            finish_nat_result(result, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatLor => {
            expect_arity(row, args, 2)?;
            let result = with_nat_views(
                &args[0],
                &args[1],
                "Nat.lor",
                |left, right| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(left.bit_length().max(right.bit_length())),
                    )?;
                    Ok(left.lor(right))
                },
            )??;
            finish_nat_result(result, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatMod => {
            expect_arity(row, args, 2)?;
            let remainder = with_nat_views(
                &args[0],
                &args[1],
                "Nat.mod",
                |dividend, divisor| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(max_nat_magnitude_bytes, u128::from(dividend.bit_length()))?;
                    Ok(dividend.rem(divisor))
                },
            )??;
            finish_nat_result(remainder, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatPow => {
            expect_arity(row, args, 2)?;
            let power = with_nat_views(
                &args[0],
                &args[1],
                "Nat.pow",
                |base, exponent| -> Result<_, IntrinsicFailure> {
                    if exponent.is_zero() {
                        return Ok(BigNat::from_u64(1));
                    }
                    match base.to_u64() {
                        Some(0) => return Ok(BigNat::zero()),
                        Some(1) => return Ok(BigNat::from_u64(1)),
                        _ => {}
                    }
                    let base_bits = u128::from(base.bit_length());
                    let exponent_u64 = exponent.to_u64();
                    let observed = exponent_u64.map_or(u64::MAX, |exponent| {
                        nat_magnitude_bytes(base_bits.saturating_mul(u128::from(exponent)))
                    });
                    let exponent = exponent_u64
                        .and_then(|value| u32::try_from(value).ok())
                        .ok_or_else(|| {
                            nat_magnitude_limit(
                                max_nat_magnitude_bytes.min(nat_magnitude_bytes(
                                    base_bits.saturating_mul(u128::from(u32::MAX)),
                                )),
                                observed,
                            )
                        })?;
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        base_bits.saturating_mul(u128::from(exponent)),
                    )?;
                    base.checked_pow(exponent)
                        .ok_or_else(|| nat_magnitude_limit(max_nat_magnitude_bytes, observed))
                },
            )??;
            finish_nat_result(power, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatPred => {
            expect_arity(row, args, 1)?;
            let predecessor = with_nat_view(&args[0], "Nat.pred", 0, |value| {
                value.sub(BigNatView::from_limbs_le(&[1]))
            })?;
            finish_nat_result(predecessor, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatShiftLeft => {
            expect_arity(row, args, 2)?;
            let shifted = with_nat_views(
                &args[0],
                &args[1],
                "Nat.shiftLeft",
                |value, amount| -> Result<_, IntrinsicFailure> {
                    if value.is_zero() {
                        return Ok(BigNat::zero());
                    }
                    let Some(amount) = amount.to_u64() else {
                        return Err(nat_magnitude_limit(max_nat_magnitude_bytes, u64::MAX));
                    };
                    let result_bits =
                        u128::from(value.bit_length()).saturating_add(u128::from(amount));
                    ensure_nat_bits(max_nat_magnitude_bytes, result_bits)?;
                    value.checked_shl(amount).ok_or_else(|| {
                        nat_magnitude_limit(
                            max_nat_magnitude_bytes,
                            nat_magnitude_bytes(result_bits),
                        )
                    })
                },
            )??;
            finish_nat_result(shifted, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatShiftRight => {
            expect_arity(row, args, 2)?;
            let shifted = with_nat_views(&args[0], &args[1], "Nat.shiftRight", |value, amount| {
                amount
                    .to_u64()
                    .map_or_else(BigNat::zero, |amount| value.shr(amount))
            })?;
            finish_nat_result(shifted, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::NatXor => {
            expect_arity(row, args, 2)?;
            let result = with_nat_views(
                &args[0],
                &args[1],
                "Nat.xor",
                |left, right| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(left.bit_length().max(right.bit_length())),
                    )?;
                    Ok(left.lxor(right))
                },
            )??;
            finish_nat_result(result, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::StringAppend => {
            expect_arity(row, args, 2)?;
            let mut lhs = string_value(&args[0], "String.append", 0)?;
            lhs.push_str(&string_value(&args[1], "String.append", 1)?);
            Ok(IntrinsicResult::owned(Obj::mk_string(&lhs)))
        }
        IntrinsicImplementation::StringAtEnd => {
            expect_arity(row, args, 2)?;
            let byte_len = string_bytes(&args[0], "String.atEnd", 0)?.len();
            let at_end = match nat_as_usize(&args[1], "String.atEnd", 1)? {
                Some(index) => index >= byte_len,
                None => true,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(at_end))))
        }
        IntrinsicImplementation::StringCompare => {
            expect_arity(row, args, 2)?;
            let left = string_bytes(&args[0], "String.compare", 0)?;
            let right = string_bytes(&args[1], "String.compare", 1)?;
            let ordering = match left.cmp(&right) {
                std::cmp::Ordering::Less => 0,
                std::cmp::Ordering::Equal => 1,
                std::cmp::Ordering::Greater => 2,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(ordering)))
        }
        IntrinsicImplementation::StringDecEq => {
            expect_arity(row, args, 2)?;
            let left = string_value(&args[0], "String.decEq", 0)?;
            let right = string_value(&args[1], "String.decEq", 1)?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(if left == right {
                1
            } else {
                0
            })))
        }
        IntrinsicImplementation::StringDecLt => {
            expect_arity(row, args, 2)?;
            let left = string_bytes(&args[0], "String.decidableLT", 0)?;
            let right = string_bytes(&args[1], "String.decidableLT", 1)?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                left < right,
            ))))
        }
        IntrinsicImplementation::StringLength => {
            expect_arity(row, args, 1)?;
            // Pin `lean_string_length` boxes `m_length`, the stored UTF-8
            // scalar count. Recounting `chars()` agrees on objects we minted,
            // but would silently disagree with the Reference on a string whose
            // header and payload had drifted.
            if value_kind(&args[0]) != ValueKind::String {
                return Err(type_mismatch("String.length", 0, "String", &args[0]).into());
            }
            let Some((size, _, length, bytes)) = args[0].try_string_view() else {
                return Err(VmRefusal::InvalidStringObject.into());
            };
            if std::str::from_utf8(&bytes[..size - 1]).is_err() {
                return Err(VmRefusal::InvalidStringObject.into());
            }
            if length > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "String.length",
                }
                .into());
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(length)))
        }
        IntrinsicImplementation::StringUtf8ByteSize => {
            expect_arity(row, args, 1)?;
            let length = string_bytes(&args[0], "String.utf8ByteSize", 0)?.len();
            if length > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "String.utf8ByteSize",
                }
                .into());
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(length)))
        }
        // The pin implements these on validated UTF-8 and asserts (UB) on
        // out-of-range scalars; here every such input is a typed range
        // refusal — an FL-INV-07 non-answer, never undefined behavior.
        IntrinsicImplementation::StringInternalIsEmpty => {
            expect_arity(row, args, 1)?;
            let empty = string_bytes(&args[0], "String.isEmpty", 0)?.is_empty();
            // The census rule is owned-result: Bool crosses as a boxed
            // constructor object, not a tagged scalar.
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(empty))))
        }
        IntrinsicImplementation::StringInternalIsPrefixOf => {
            expect_arity(row, args, 2)?;
            let prefix = string_value(&args[0], "String.isPrefixOf", 0)?;
            let candidate = string_value(&args[1], "String.isPrefixOf", 1)?;
            // UTF-8 is self-synchronizing, so a byte prefix is a character
            // prefix; the pin's `startsWith` agrees byte-for-byte here.
            let is_prefix = candidate.starts_with(prefix.as_str());
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(is_prefix))))
        }
        IntrinsicImplementation::StringContains => {
            expect_arity(row, args, 2)?;
            let haystack = string_value(&args[0], "String.contains", 0)?;
            let scalar = scalar_code_point(&args[1], "String.contains", 1)?;
            let needle = char::from_u32(scalar).ok_or(VmRefusal::NatOverflow {
                operation: "String.contains",
            })?;
            let contains = haystack.contains(needle);
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(contains))))
        }
        IntrinsicImplementation::StringPush => {
            expect_arity(row, args, 2)?;
            let mut base = string_value(&args[0], "String.push", 0)?;
            let scalar = scalar_code_point(&args[1], "String.push", 1)?;
            let pushed = char::from_u32(scalar).ok_or(VmRefusal::NatOverflow {
                operation: "String.push",
            })?;
            base.push(pushed);
            Ok(IntrinsicResult::owned(Obj::mk_string(&base)))
        }
        IntrinsicImplementation::StringNext => {
            expect_arity(row, args, 2)?;
            let bytes = string_bytes(&args[0], "String.next", 0)?;
            match nat_as_usize(&args[1], "String.next", 1)? {
                None => Ok(IntrinsicResult::owned(args[1].clone_ref())),
                Some(index) if index >= bytes.len() => {
                    Ok(IntrinsicResult::owned(args[1].clone_ref()))
                }
                Some(index) => {
                    let next = index + utf8_first_byte_width(bytes[index]);
                    Ok(IntrinsicResult::owned(Obj::mk_nat(next)))
                }
            }
        }
        IntrinsicImplementation::StringPrev => {
            expect_arity(row, args, 2)?;
            let bytes = string_bytes(&args[0], "String.prev", 0)?;
            match nat_as_usize(&args[1], "String.prev", 1)? {
                // The pin subtracts one at arbitrary precision; positions
                // beyond the machine word are outside this VM's Nat ceiling.
                None => Err(VmRefusal::NatOverflow {
                    operation: "String.prev",
                }
                .into()),
                Some(0) => Ok(IntrinsicResult::owned(Obj::mk_nat(0))),
                Some(index) if index > bytes.len() => {
                    Ok(IntrinsicResult::owned(Obj::mk_nat(index - 1)))
                }
                Some(mut index) => {
                    index -= 1;
                    while !is_utf8_first_byte(bytes[index]) {
                        index -= 1;
                    }
                    Ok(IntrinsicResult::owned(Obj::mk_nat(index)))
                }
            }
        }
        IntrinsicImplementation::StringExtract => {
            expect_arity(row, args, 3)?;
            let bytes = string_bytes(&args[0], "String.extract", 0)?;
            let begin = nat_as_usize(&args[1], "String.extract", 1)?;
            let end = nat_as_usize(&args[2], "String.extract", 2)?;
            let extracted =
                extract_utf8(&bytes, begin, end).ok_or(VmRefusal::InvalidStringObject)?;
            Ok(IntrinsicResult::owned(Obj::mk_string(extracted.as_str())))
        }
        IntrinsicImplementation::StringDrop => {
            expect_arity(row, args, 2)?;
            let base = string_value(&args[0], "String.drop", 0)?;
            let count = nat_as_usize(&args[1], "String.drop", 1)?.unwrap_or(usize::MAX);
            let dropped: String = base.chars().skip(count).collect();
            Ok(IntrinsicResult::owned(Obj::mk_string(&dropped)))
        }
        IntrinsicImplementation::StringDropRight => {
            expect_arity(row, args, 2)?;
            let base = string_value(&args[0], "String.dropRight", 0)?;
            let count = nat_as_usize(&args[1], "String.dropRight", 1)?.unwrap_or(usize::MAX);
            let keep = base.chars().count().saturating_sub(count);
            let dropped: String = base.chars().take(keep).collect();
            Ok(IntrinsicResult::owned(Obj::mk_string(&dropped)))
        }
        IntrinsicImplementation::StringTrim => {
            expect_arity(row, args, 1)?;
            // `Char.isWhitespace` is exactly these four scalars at the pin.
            const WHITESPACE: [char; 4] = [' ', '\t', '\r', '\n'];
            let untrimmed = string_value(&args[0], "String.trim", 0)?;
            let trimmed = untrimmed.trim_matches(WHITESPACE);
            Ok(IntrinsicResult::owned(Obj::mk_string(trimmed)))
        }
        IntrinsicImplementation::StringCapitalize => {
            expect_arity(row, args, 1)?;
            let mut base = string_value(&args[0], "String.capitalize", 0)?;
            // `Char.toUpper` at the pin maps only 'a'..='z'; everything else
            // passes through unchanged.
            let mut chars = base.chars();
            if let Some(first @ 'a'..='z') = chars.next() {
                let mut capitalized = String::with_capacity(base.len());
                capitalized.push(first.to_ascii_uppercase());
                capitalized.push_str(chars.as_str());
                base = capitalized;
            }
            Ok(IntrinsicResult::owned(Obj::mk_string(&base)))
        }
        IntrinsicImplementation::ArraySize => {
            expect_arity(row, args, 1)?;
            let (size, _) = array_value(&args[0], "Array.size", 0)?;
            if size > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "Array.size",
                }
                .into());
            }
            Ok(IntrinsicResult::raw_object(Obj::mk_nat(size)))
        }
        IntrinsicImplementation::ArrayGetInternal => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.getInternal", 0)?;
            let index = array_index(&args[1], "Array.getInternal", size)?;
            Ok(IntrinsicResult::owned(args[0].array_child(index)))
        }
        IntrinsicImplementation::ArrayUGet => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.uget", 0)?;
            let index = array_index(&args[1], "Array.uget", size)?;
            Ok(IntrinsicResult::raw_object(args[0].array_child(index)))
        }
        IntrinsicImplementation::ArrayGetBorrowed => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.ugetBorrowed", 0)?;
            let index = array_index(&args[1], "Array.ugetBorrowed", size)?;
            Ok(IntrinsicResult::borrowed_promoted(
                args[0].array_child(index),
            ))
        }
        IntrinsicImplementation::ArrayUSize => {
            expect_arity(row, args, 1)?;
            let (size, _) = array_value(&args[0], "Array.usize", 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(size)))
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
        IntrinsicImplementation::PlatformNumBits => {
            expect_arity(row, args, 1)?;
            // Marrow refuses non-64-bit targets at compile time because its
            // ABI layout twin is certified only for 64-bit little-endian
            // hosts. The erased subtype proof has no runtime field.
            Ok(IntrinsicResult::owned(Obj::mk_nat(
                std::mem::size_of::<usize>() * 8,
            )))
        }
        IntrinsicImplementation::PlatformIsWindows => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(cfg!(
                target_os = "windows"
            )))))
        }
        IntrinsicImplementation::PlatformIsOsx => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(cfg!(
                target_os = "macos"
            )))))
        }
        IntrinsicImplementation::PlatformIsEmscripten => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(cfg!(
                target_os = "emscripten"
            )))))
        }
        IntrinsicImplementation::IoCancel => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "IO.cancel", 0, "Task", ValueKind::Task)?;
            if args[0].finished_task_value().is_none() {
                return Err(VmRefusal::UnsupportedTaskState.into());
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
        IntrinsicImplementation::IoInitializing => {
            expect_arity(row, args, 0)?;
            // The only Golem entry point currently executes an admitted
            // definition after environment construction. It does not execute
            // module `initialize` blocks, so this is the complete reachable
            // phase observation rather than a process-global approximation.
            Ok(IntrinsicResult::owned(Obj::mk_nat(0)))
        }
        IntrinsicImplementation::IoGetTaskState => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "IO.getTaskState", 0, "Task", ValueKind::Task)?;
            if args[0].finished_task_value().is_none() {
                return Err(VmRefusal::UnsupportedTaskState.into());
            }
            // The pin returns state 2 for a finished task before consulting
            // the task manager. Golem creates only finished tasks in its
            // managerless execution slice, so this is the complete reachable
            // arm; scheduled and waiting states remain typed unsupported.
            Ok(IntrinsicResult::owned(Obj::mk_nat(2)))
        }
        IntrinsicImplementation::IoWait => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "IO.wait", 0, "finished Task", ValueKind::Task)?;
            args[0]
                .finished_task_value()
                .map(IntrinsicResult::owned)
                .ok_or_else(|| VmRefusal::UnsupportedTaskState.into())
        }
        IntrinsicImplementation::IoWaitAny => {
            expect_arity(row, args, 1)?;
            expect_value_kind(
                &args[0],
                "IO.waitAny",
                0,
                "non-empty List (Task _)",
                ValueKind::Ctor(1),
            )?;
            let first = args[0]
                .try_ctor_child(0)
                .ok_or(VmRefusal::InvalidCtorObject)?;
            expect_value_kind(&first, "IO.waitAny", 0, "finished Task", ValueKind::Task)?;
            first
                .finished_task_value()
                .map(IntrinsicResult::owned)
                .ok_or_else(|| VmRefusal::UnsupportedTaskState.into())
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
            let Some(value) = args[0].try_ref_get() else {
                return Err(VmRefusal::InvalidRefObject.into());
            };
            Ok(IntrinsicResult::owned(value))
        }
        IntrinsicImplementation::RefTake => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.take", 0, "ST.Ref", ValueKind::Ref)?;
            let Some(value) = args[0].try_ref_take() else {
                return Err(VmRefusal::InvalidRefObject.into());
            };
            Ok(IntrinsicResult::owned(value))
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
            let Some(old) = args[0].try_ref_take() else {
                return Err(VmRefusal::InvalidRefObject.into());
            };
            args[0].ref_set(args[1].clone_ref());
            Ok(IntrinsicResult::owned(old))
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
                return Err(VmRefusal::UnsupportedNativeClosure.into());
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
                .ok_or_else(|| VmRefusal::UnsupportedTaskState.into())
        }
        IntrinsicImplementation::BaseIoAsTask
        | IntrinsicImplementation::BaseIoBindTask
        | IntrinsicImplementation::BaseIoMapTask
        | IntrinsicImplementation::ThunkGet
        | IntrinsicImplementation::TaskSpawn
        | IntrinsicImplementation::TaskMap
        | IntrinsicImplementation::TaskBind
        | IntrinsicImplementation::Unsupported => Err(VmRefusal::UnsupportedIntrinsic {
            row: row.to_string(),
        }
        .into()),
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
        IntrinsicImplementation::BaseIoAsTask | IntrinsicImplementation::TaskSpawn => {
            let [closure, priority] = exact_owned_args(row, args)?;
            let operation = if implementation == IntrinsicImplementation::BaseIoAsTask {
                "BaseIO.asTask"
            } else {
                "Task.spawn"
            };
            expect_golem_task_closure(&closure, operation, 0)?;
            // Priority is a Nat; the managerless path ignores the number.
            // An mpz priority is still a Nat — refusing it as a type
            // mismatch would treat 2^64 as ill-typed rather than a valid
            // (and here unused) priority.
            with_nat_view(&priority, operation, 1, |_| ())?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                arguments: vec![Obj::mk_nat(0)],
                argument_ownership: vec![ArgumentOwnership::Scalar],
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        IntrinsicImplementation::BaseIoMapTask => {
            let [closure, task, priority, sync] = exact_owned_args(row, args)?;
            expect_golem_task_closure(&closure, "BaseIO.mapTask", 0)?;
            expect_value_kind(&task, "BaseIO.mapTask", 1, "finished Task", ValueKind::Task)?;
            with_nat_view(&priority, "BaseIO.mapTask", 2, |_| ())?;
            bool_value(&sync, "BaseIO.mapTask", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                arguments: vec![argument, Obj::mk_nat(0)],
                argument_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Scalar],
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        IntrinsicImplementation::BaseIoBindTask => {
            let [task, closure, priority, sync] = exact_owned_args(row, args)?;
            expect_value_kind(
                &task,
                "BaseIO.bindTask",
                0,
                "finished Task",
                ValueKind::Task,
            )?;
            expect_golem_task_closure(&closure, "BaseIO.bindTask", 1)?;
            with_nat_view(&priority, "BaseIO.bindTask", 2, |_| ())?;
            bool_value(&sync, "BaseIO.bindTask", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                arguments: vec![argument, Obj::mk_nat(0)],
                argument_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Scalar],
                completion: ManagerlessTaskCompletion::RequireFinishedTask,
            })
        }
        IntrinsicImplementation::TaskMap => {
            let [closure, task, priority, sync] = exact_owned_args(row, args)?;
            expect_golem_task_closure(&closure, "Task.map", 0)?;
            expect_value_kind(&task, "Task.map", 1, "finished Task", ValueKind::Task)?;
            with_nat_view(&priority, "Task.map", 2, |_| ())?;
            bool_value(&sync, "Task.map", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                arguments: vec![argument],
                argument_ownership: vec![ArgumentOwnership::Owned],
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        IntrinsicImplementation::TaskBind => {
            let [task, closure, priority, sync] = exact_owned_args(row, args)?;
            expect_value_kind(&task, "Task.bind", 0, "finished Task", ValueKind::Task)?;
            expect_golem_task_closure(&closure, "Task.bind", 1)?;
            with_nat_view(&priority, "Task.bind", 2, |_| ())?;
            bool_value(&sync, "Task.bind", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row,
                closure,
                arguments: vec![argument],
                argument_ownership: vec![ArgumentOwnership::Owned],
                completion: ManagerlessTaskCompletion::RequireFinishedTask,
            })
        }
        IntrinsicImplementation::NatAdd
        | IntrinsicImplementation::NatBeq
        | IntrinsicImplementation::NatBle
        | IntrinsicImplementation::NatSub
        | IntrinsicImplementation::NatMul
        | IntrinsicImplementation::NatDiv
        | IntrinsicImplementation::NatGcd
        | IntrinsicImplementation::NatLand
        | IntrinsicImplementation::NatLog2
        | IntrinsicImplementation::NatLor
        | IntrinsicImplementation::NatMod
        | IntrinsicImplementation::NatPow
        | IntrinsicImplementation::NatPred
        | IntrinsicImplementation::NatShiftLeft
        | IntrinsicImplementation::NatShiftRight
        | IntrinsicImplementation::NatXor
        | IntrinsicImplementation::StringAppend
        | IntrinsicImplementation::StringAtEnd
        | IntrinsicImplementation::StringCompare
        | IntrinsicImplementation::StringDecEq
        | IntrinsicImplementation::StringDecLt
        | IntrinsicImplementation::StringLength
        | IntrinsicImplementation::StringUtf8ByteSize
        | IntrinsicImplementation::StringCapitalize
        | IntrinsicImplementation::StringContains
        | IntrinsicImplementation::StringDrop
        | IntrinsicImplementation::StringDropRight
        | IntrinsicImplementation::StringExtract
        | IntrinsicImplementation::StringInternalIsEmpty
        | IntrinsicImplementation::StringInternalIsPrefixOf
        | IntrinsicImplementation::StringNext
        | IntrinsicImplementation::StringPrev
        | IntrinsicImplementation::StringPush
        | IntrinsicImplementation::StringTrim
        | IntrinsicImplementation::ArraySize
        | IntrinsicImplementation::ArrayGetInternal
        | IntrinsicImplementation::ArrayUGet
        | IntrinsicImplementation::ArrayGetBorrowed
        | IntrinsicImplementation::ArrayUSize
        | IntrinsicImplementation::ArrayPush
        | IntrinsicImplementation::PlatformNumBits
        | IntrinsicImplementation::PlatformIsWindows
        | IntrinsicImplementation::PlatformIsOsx
        | IntrinsicImplementation::PlatformIsEmscripten
        | IntrinsicImplementation::IoCancel
        | IntrinsicImplementation::IoCheckCancelled
        | IntrinsicImplementation::IoInitializing
        | IntrinsicImplementation::IoGetTaskState
        | IntrinsicImplementation::IoWait
        | IntrinsicImplementation::IoWaitAny
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

fn with_nat_view<R>(
    value: &Obj,
    operation: &'static str,
    argument: usize,
    use_view: impl FnOnce(BigNatView<'_>) -> R,
) -> Result<R, VmRefusal> {
    if value.is_scalar() {
        let limb = [value.unbox() as u64];
        return Ok(use_view(BigNatView::from_limbs_le(&limb)));
    }
    if value_kind(value) != ValueKind::Mpz {
        return Err(type_mismatch(operation, argument, "Nat", value));
    }
    let Some((_, size, limbs)) = value.try_mpz_view() else {
        return Err(type_mismatch(operation, argument, "Nat", value));
    };
    if size < 0 {
        return Err(type_mismatch(operation, argument, "Nat", value));
    }
    Ok(use_view(BigNatView::from_limbs_le(limbs)))
}

fn with_nat_views<R>(
    left: &Obj,
    right: &Obj,
    operation: &'static str,
    use_views: impl FnOnce(BigNatView<'_>, BigNatView<'_>) -> R,
) -> Result<R, VmRefusal> {
    with_nat_view(left, operation, 0, |left| {
        with_nat_view(right, operation, 1, |right| use_views(left, right))
    })?
}

fn nat_magnitude_bytes(bits: u128) -> u64 {
    if bits <= u128::from(usize::BITS - 1) {
        return 0;
    }
    let limbs = bits.saturating_add(63) / 64;
    u64::try_from(limbs.saturating_mul(8)).unwrap_or(u64::MAX)
}

fn ensure_nat_bits(allowed: u64, result_bits: u128) -> Result<(), IntrinsicFailure> {
    let observed = nat_magnitude_bytes(result_bits);
    if observed > allowed {
        return Err(nat_magnitude_limit(allowed, observed));
    }
    Ok(())
}

fn nat_magnitude_limit(allowed: u64, observed: u64) -> IntrinsicFailure {
    IntrinsicFailure::NatMagnitudeLimit {
        allowed,
        observed: observed.max(allowed.saturating_add(1)),
    }
}

fn finish_nat_result(
    value: BigNat,
    max_nat_magnitude_bytes: u64,
) -> Result<IntrinsicResult, IntrinsicFailure> {
    let observed = match value.to_u64() {
        Some(value) if value <= (usize::MAX >> 1) as u64 => 0,
        _ => u64::try_from(value.limbs_le().len())
            .unwrap_or(u64::MAX)
            .saturating_mul(8),
    };
    if observed > max_nat_magnitude_bytes {
        return Err(nat_magnitude_limit(max_nat_magnitude_bytes, observed));
    }
    Ok(IntrinsicResult::owned(nat_from_big_nat(&value)))
}

fn nat_from_big_nat(value: &BigNat) -> Obj {
    match value.to_u64() {
        Some(value) if value <= (usize::MAX >> 1) as u64 => Obj::mk_nat(value as usize),
        _ => Obj::mk_mpz(value.limbs_le(), false),
    }
}

fn nat_value(value: &Obj, operation: &'static str, argument: usize) -> Result<usize, VmRefusal> {
    if !value.is_scalar() {
        return Err(type_mismatch(operation, argument, "Nat scalar", value));
    }
    Ok(value.unbox())
}

/// A Marrow `Nat` used as a host index. `None` means a well-typed Nat larger
/// than `usize::MAX` — out of range for every in-memory array, not a type error.
fn nat_as_usize(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<Option<usize>, VmRefusal> {
    with_nat_view(value, operation, argument, |view| {
        view.to_u64().and_then(|word| usize::try_from(word).ok())
    })
}

fn array_index(value: &Obj, operation: &'static str, size: usize) -> Result<usize, VmRefusal> {
    let Some(index) = nat_as_usize(value, operation, 1)? else {
        return Err(VmRefusal::ArrayIndexOutOfBounds {
            index: usize::MAX,
            size,
        });
    };
    if index >= size {
        return Err(VmRefusal::ArrayIndexOutOfBounds { index, size });
    }
    Ok(index)
}

fn nat_low_u64(value: &Obj, operation: &'static str, argument: usize) -> Result<u64, VmRefusal> {
    if value.is_scalar() {
        return Ok(value.unbox() as u64);
    }
    if value_kind(value) != ValueKind::Mpz {
        return Err(type_mismatch(operation, argument, "Nat", value));
    }
    let Some((_, size, limbs)) = value.try_mpz_view() else {
        return Err(type_mismatch(operation, argument, "Nat", value));
    };
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
    value.try_array_view().ok_or(VmRefusal::InvalidArrayObject)
}

fn string_value(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<String, VmRefusal> {
    String::from_utf8(string_bytes(value, operation, argument)?)
        .map_err(|_| VmRefusal::InvalidStringObject)
}

fn string_bytes(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<Vec<u8>, VmRefusal> {
    if value_kind(value) != ValueKind::String {
        return Err(type_mismatch(operation, argument, "String", value));
    }
    let Some((size, _, _, mut bytes)) = value.try_string_view() else {
        return Err(VmRefusal::InvalidStringObject);
    };
    if std::str::from_utf8(&bytes[..size - 1]).is_err() {
        return Err(VmRefusal::InvalidStringObject);
    }
    bytes.truncate(size - 1);
    Ok(bytes)
}

/// The scalar argument of a string intrinsic, range-checked before any
/// `char` conversion. The pin asserts on out-of-range scalars; this VM
/// refuses with a typed range fault instead.
fn scalar_code_point(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<u32, VmRefusal> {
    let word = match nat_as_usize(value, operation, argument)? {
        Some(word) => word,
        None => return Err(VmRefusal::NatOverflow { operation }),
    };
    u32::try_from(word).map_err(|_| VmRefusal::NatOverflow { operation })
}

/// Width of the UTF-8 sequence led by `lead`, per the pin's
/// `lean_string_utf8_next_fast_cold`: an invalid lead byte advances by one.
fn utf8_first_byte_width(lead: u8) -> usize {
    if lead & 0xe0 == 0xc0 {
        2
    } else if lead & 0xf0 == 0xe0 {
        3
    } else if lead & 0xf8 == 0xf0 {
        4
    } else {
        1
    }
}

/// The pin's `is_utf8_first_byte`: does a byte begin a UTF-8 sequence?
const fn is_utf8_first_byte(byte: u8) -> bool {
    byte & 0x80 == 0 || byte & 0xe0 == 0xc0 || byte & 0xf0 == 0xe0 || byte & 0xf8 == 0xf0
}

/// Exact port of the pin's `lean_string_utf8_extract`, including its two
/// documented quirks: an empty result when `begin` is mid-character, and an
/// end clamped to the string when `end` is mid-character. A non-scalar
/// position leaves that side of the slice unbounded (the whole string).
fn extract_utf8(bytes: &[u8], begin: Option<usize>, end: Option<usize>) -> Option<String> {
    let (Some(begin), Some(end)) = (begin, end) else {
        return std::str::from_utf8(bytes)
            .ok()
            .map(std::borrow::ToOwned::to_owned);
    };
    let size = bytes.len();
    if begin >= end || begin >= size {
        return Some(String::new());
    }
    if !is_utf8_first_byte(bytes[begin]) {
        return Some(String::new());
    }
    let mut end = end;
    if end > size {
        end = size;
    }
    if end < size && !is_utf8_first_byte(bytes[end]) {
        end = size;
    }
    std::str::from_utf8(&bytes[begin..end])
        .ok()
        .map(std::borrow::ToOwned::to_owned)
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

/// Copy a nonnegative Marrow `Nat` value to canonical decimal text.
///
/// Tagged small values and positive mpz objects share this projection. Other
/// ABI kinds, including negative mpz values used for `Int`, return `None`.
pub fn nat_decimal(value: &Obj) -> Option<String> {
    with_nat_view(value, "Nat decimal projection", 0, |value| {
        value.to_owned().to_decimal()
    })
    .ok()
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

    const CEILING: u64 = 8 * 1024 * 1024;

    fn invoke(row: &'static str, args: &[Obj]) -> Result<Obj, VmRefusal> {
        let implementation = IntrinsicImplementation::for_row(row);
        assert!(
            implementation != IntrinsicImplementation::Unsupported,
            "{row} must be registered"
        );
        let generated = EXTERN_ROWS
            .iter()
            .find(|candidate| candidate.id == row)
            .expect("the row exists in the generated census");
        let expected_ownership = match ExternOwnership::parse(generated.ownership)
            .expect("the census ownership form parses")
            .result_ownership()
            .expect("the census result ownership is executable")
        {
            ContractResultOwnership::Owned => ResultOwnership::Owned,
            ContractResultOwnership::Borrowed => ResultOwnership::Borrowed,
            ContractResultOwnership::Scalar => ResultOwnership::Scalar,
            ContractResultOwnership::RawObject => ResultOwnership::RawObject,
        };
        finish_intrinsic_result(
            row,
            expected_ownership,
            invoke_intrinsic(implementation, row, args, CEILING).map_err(
                |failure| match failure {
                    IntrinsicFailure::Refused(refusal) => refusal,
                    other => panic!(
                        "unexpected intrinsic failure class: {name}",
                        name = std::any::type_name_of_val(&other)
                    ),
                },
            )?,
        )
    }

    fn s(value: &str) -> Obj {
        Obj::mk_string(value)
    }

    fn n(value: usize) -> Obj {
        Obj::mk_nat(value)
    }

    fn owned_string(result: Result<Obj, VmRefusal>) -> String {
        let object = result.expect("the intrinsic answers");
        string_value(&object, "test projection", 0).expect("a string result")
    }

    fn owned_usize(result: Result<Obj, VmRefusal>) -> usize {
        let object = result.expect("the intrinsic answers");
        nat_as_usize(&object, "test projection", 0)
            .expect("a well-typed Nat")
            .expect("a machine-word Nat")
    }

    #[test]
    fn string_navigation_walks_utf8_scalars_like_the_pin() {
        // "héllo" — é is two bytes, so positions are 0, 1, 3, 4, 5, 6.
        let text = s("héllo");
        assert_eq!(
            owned_usize(invoke("extern:String.next", &[text.clone_ref(), n(0)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:String.next", &[text.clone_ref(), n(1)])),
            3
        );
        assert_eq!(
            owned_usize(invoke("extern:String.next", &[text.clone_ref(), n(6)])),
            6
        );
        assert_eq!(
            owned_usize(invoke("extern:String.prev", &[text.clone_ref(), n(3)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:String.prev", &[text.clone_ref(), n(0)])),
            0
        );
        // The pin returns i-1 without walking when i is past the end.
        assert_eq!(
            owned_usize(invoke("extern:String.prev", &[text, n(99)])),
            98
        );
    }

    #[test]
    fn string_push_appends_one_utf8_scalar() {
        let pushed = owned_string(invoke("extern:String.push", &[s("héllo"), n('!' as usize)]));
        assert_eq!(pushed, "héllo!");
        let snowman = owned_string(invoke("extern:String.push", &[s(""), n('☃' as usize)]));
        assert_eq!(snowman, "☃");
    }

    #[test]
    fn string_push_refuses_out_of_range_scalars_typed() {
        for scalar in [0xD800usize, 0xDFFF, 0x11_0000] {
            let result = invoke("extern:String.push", &[s("x"), n(scalar)]);
            assert!(
                matches!(
                    result,
                    Err(VmRefusal::NatOverflow {
                        operation: "String.push"
                    })
                ),
                "scalar {scalar:#x} must refuse as a range fault"
            );
        }
    }

    #[test]
    fn string_extract_ports_the_pin_quirks() {
        let text = s("héllo");
        // A finite Nat far past the end clamps to empty; the pin's
        // non-scalar whole-string branch is unreachable through well-typed
        // machine-word Nats in this VM and stays defensive totality.
        let big = Obj::mk_mpz(&[u64::from(u32::MAX) + 1], false);
        assert_eq!(
            owned_string(invoke(
                "extern:String.extract",
                &[text.clone_ref(), big, n(2)]
            )),
            ""
        );
        // Empty on begin >= end and on begin past the end.
        assert_eq!(
            owned_string(invoke(
                "extern:String.extract",
                &[text.clone_ref(), n(3), n(1)]
            )),
            ""
        );
        assert_eq!(
            owned_string(invoke(
                "extern:String.extract",
                &[text.clone_ref(), n(9), n(10)]
            )),
            ""
        );
        // End clamps to the string; mid-character end means "to the end".
        assert_eq!(
            owned_string(invoke(
                "extern:String.extract",
                &[text.clone_ref(), n(1), n(99)]
            )),
            "éllo"
        );
        assert_eq!(
            owned_string(invoke(
                "extern:String.extract",
                &[text.clone_ref(), n(1), n(2)]
            )),
            "éllo"
        );
        assert_eq!(
            owned_string(invoke("extern:String.extract", &[text, n(1), n(3)])),
            "é"
        );
    }

    #[test]
    fn string_drop_drop_right_trim_capitalize_match_the_pin() {
        let text = s("héllo");
        assert_eq!(
            owned_string(invoke(
                "extern:String.Internal.drop",
                &[text.clone_ref(), n(2)]
            )),
            "llo"
        );
        assert_eq!(
            owned_string(invoke(
                "extern:String.Internal.drop",
                &[text.clone_ref(), n(99)]
            )),
            ""
        );
        assert_eq!(
            owned_string(invoke(
                "extern:String.Internal.dropRight",
                &[text.clone_ref(), n(2)]
            )),
            "hél"
        );
        assert_eq!(
            owned_string(invoke(
                "extern:String.Internal.trim",
                &[s("  \t héllo \r\n")],
            )),
            "héllo"
        );
        assert_eq!(
            owned_string(invoke("extern:String.Internal.capitalize", &[s("hello")])),
            "Hello"
        );
        // Only 'a'..='z' capitalizes; multi-byte first scalars pass through.
        assert_eq!(
            owned_string(invoke("extern:String.Internal.capitalize", &[s("élan")])),
            "élan"
        );
        assert_eq!(
            owned_string(invoke("extern:String.Internal.capitalize", &[s("")])),
            ""
        );
    }

    #[test]
    fn string_predicates_report_bool_scalars() {
        assert_eq!(
            owned_usize(invoke("extern:String.Internal.isEmpty", &[s("")])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:String.Internal.isEmpty", &[s("x")])),
            0
        );
        assert_eq!(
            owned_usize(invoke(
                "extern:String.Internal.isPrefixOf",
                &[s("hél"), s("héllo")]
            )),
            1
        );
        assert_eq!(
            owned_usize(invoke(
                "extern:String.Internal.isPrefixOf",
                &[s("helo"), s("héllo")]
            )),
            0
        );
        assert_eq!(
            owned_usize(invoke(
                "extern:String.Internal.contains",
                &[s("héllo"), n('ł' as usize)]
            )),
            0
        );
        assert_eq!(
            owned_usize(invoke(
                "extern:String.Internal.contains",
                &[s("héllo"), n('é' as usize)]
            )),
            1
        );
    }

    #[test]
    fn every_registered_row_resolves_and_every_string_row_has_an_owner() {
        let rows = [
            "extern:String.Internal.capitalize",
            "extern:String.Internal.contains",
            "extern:String.Internal.drop",
            "extern:String.Internal.dropRight",
            "extern:String.Internal.extract",
            "extern:String.Internal.isEmpty",
            "extern:String.Internal.isPrefixOf",
            "extern:String.Internal.next",
            "extern:String.Pos.Raw.extract",
            "extern:String.Pos.Raw.next",
            "extern:String.Pos.Raw.prev",
            "extern:String.Internal.prev",
            "extern:String.Internal.trim",
            "extern:String.extract",
            "extern:String.next",
            "extern:String.prev",
            "extern:String.push",
        ];
        for row in rows {
            assert_ne!(
                IntrinsicImplementation::for_row(row),
                IntrinsicImplementation::Unsupported,
                "{row} must resolve"
            );
        }
    }
}
