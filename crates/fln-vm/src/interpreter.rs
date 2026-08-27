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
    NatDivExact,
    NatModCore,
    NatDecEq,
    NatDecLe,
    NatDecLt,
    IntAdd,
    IntSub,
    IntMul,
    IntNeg,
    IntNegSucc,
    IntOfNat,
    IntNatAbs,
    IntDecEq,
    IntDecLe,
    IntDecLt,
    IntDecNonneg,
    IntEDiv,
    IntEMod,
    IntTDiv,
    IntTMod,
    IntDivExact,
    UInt8Add,
    UInt8Sub,
    UInt8Mul,
    UInt8Div,
    UInt8Mod,
    UInt8Land,
    UInt8Lor,
    UInt8Xor,
    UInt8ShiftLeft,
    UInt8ShiftRight,
    UInt8Complement,
    UInt8Neg,
    UInt8Log2,
    UInt8DecEq,
    UInt8DecLe,
    UInt8DecLt,
    UInt8OfNat,
    UInt8ToNat,
    UInt8ToUInt16,
    UInt8ToUInt32,
    UInt8ToUInt64,
    UInt8ToUSize,
    UInt16Add,
    UInt16Sub,
    UInt16Mul,
    UInt16Div,
    UInt16Mod,
    UInt16Land,
    UInt16Lor,
    UInt16Xor,
    UInt16ShiftLeft,
    UInt16ShiftRight,
    UInt16Complement,
    UInt16Neg,
    UInt16Log2,
    UInt16DecEq,
    UInt16DecLe,
    UInt16DecLt,
    UInt16OfNat,
    UInt16ToNat,
    UInt16ToUInt8,
    UInt16ToUInt32,
    UInt16ToUInt64,
    UInt16ToUSize,
    UInt32Add,
    UInt32Sub,
    UInt32Mul,
    UInt32Div,
    UInt32Mod,
    UInt32Land,
    UInt32Lor,
    UInt32Xor,
    UInt32ShiftLeft,
    UInt32ShiftRight,
    UInt32Complement,
    UInt32Neg,
    UInt32Log2,
    UInt32DecEq,
    UInt32DecLe,
    UInt32DecLt,
    UInt32OfNat,
    UInt32ToNat,
    UInt32ToUInt8,
    UInt32ToUInt16,
    UInt32ToUInt64,
    UInt32ToUSize,
    UInt64Add,
    UInt64Sub,
    UInt64Mul,
    UInt64Div,
    UInt64Mod,
    UInt64Land,
    UInt64Lor,
    UInt64Xor,
    UInt64ShiftLeft,
    UInt64ShiftRight,
    UInt64Complement,
    UInt64Neg,
    UInt64Log2,
    UInt64DecEq,
    UInt64DecLe,
    UInt64DecLt,
    UInt64OfNat,
    UInt64ToNat,
    UInt64ToUInt8,
    UInt64ToUInt16,
    UInt64ToUInt32,
    UInt64ToUSize,
    UInt64MixHash,
    USizeAdd,
    USizeSub,
    USizeMul,
    USizeDiv,
    USizeMod,
    USizeLand,
    USizeLor,
    USizeXor,
    USizeShiftLeft,
    USizeShiftRight,
    USizeComplement,
    USizeNeg,
    USizeLog2,
    USizeDecEq,
    USizeDecLe,
    USizeDecLt,
    USizeOfNat,
    USizeToNat,
    USizeToUInt8,
    USizeToUInt16,
    USizeToUInt32,
    USizeToUInt64,
    USizeRepr,
    Int8Add,
    Int8Sub,
    Int8Mul,
    Int8Div,
    Int8Mod,
    Int8Land,
    Int8Lor,
    Int8Xor,
    Int8ShiftLeft,
    Int8ShiftRight,
    Int8Complement,
    Int8Neg,
    Int8Abs,
    Int8DecEq,
    Int8DecLe,
    Int8DecLt,
    Int8OfNat,
    Int8ToInt,
    Int8ToWidth,
    Int16Add,
    Int16Sub,
    Int16Mul,
    Int16Div,
    Int16Mod,
    Int16Land,
    Int16Lor,
    Int16Xor,
    Int16ShiftLeft,
    Int16ShiftRight,
    Int16Complement,
    Int16Neg,
    Int16Abs,
    Int16DecEq,
    Int16DecLe,
    Int16DecLt,
    Int16OfNat,
    Int16ToInt,
    Int16ToWidth,
    Int32Add,
    Int32Sub,
    Int32Mul,
    Int32Div,
    Int32Mod,
    Int32Land,
    Int32Lor,
    Int32Xor,
    Int32ShiftLeft,
    Int32ShiftRight,
    Int32Complement,
    Int32Neg,
    Int32Abs,
    Int32DecEq,
    Int32DecLe,
    Int32DecLt,
    Int32OfNat,
    Int32ToInt,
    Int32ToWidth,
    Int64Add,
    Int64Sub,
    Int64Mul,
    Int64Div,
    Int64Mod,
    Int64Land,
    Int64Lor,
    Int64Xor,
    Int64ShiftLeft,
    Int64ShiftRight,
    Int64Complement,
    Int64Neg,
    Int64Abs,
    Int64DecEq,
    Int64DecLe,
    Int64DecLt,
    Int64OfNat,
    Int64ToInt,
    Int64ToWidth,
    ISizeAdd,
    ISizeSub,
    ISizeMul,
    ISizeDiv,
    ISizeMod,
    ISizeLand,
    ISizeLor,
    ISizeXor,
    ISizeShiftLeft,
    ISizeShiftRight,
    ISizeComplement,
    ISizeNeg,
    ISizeAbs,
    ISizeDecEq,
    ISizeDecLe,
    ISizeDecLt,
    ISizeOfNat,
    ISizeToInt,
    ISizeToWidth,
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
    ByteArrayBeq,
    ByteArrayCopySlice,
    ByteArrayData,
    ByteArrayDecEq,
    ByteArrayEmptyWithCapacity,
    ByteArrayGet,
    ByteArrayHash,
    ByteArrayMk,
    ByteArrayPush,
    ByteArraySet,
    ByteArraySize,
    ByteArrayUGet,
    ByteArrayUset,
    ByteArrayValidateUtf8,
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
            "extern:Nat.divExact" => Self::NatDivExact,
            "extern:Nat.modCore" => Self::NatModCore,
            "extern:Nat.decEq" => Self::NatDecEq,
            "extern:Nat.decLe" => Self::NatDecLe,
            "extern:Nat.decLt" => Self::NatDecLt,
            "extern:Int.add" => Self::IntAdd,
            "extern:Int.sub" => Self::IntSub,
            "extern:Int.mul" => Self::IntMul,
            "extern:Int.neg" => Self::IntNeg,
            "extern:Int.negSucc" => Self::IntNegSucc,
            "extern:Int.ofNat" => Self::IntOfNat,
            "extern:Int.natAbs" => Self::IntNatAbs,
            "extern:Int.decEq" => Self::IntDecEq,
            "extern:Int.decLe" => Self::IntDecLe,
            "extern:Int.decLt" => Self::IntDecLt,
            "extern:Int.decNonneg" => Self::IntDecNonneg,
            "extern:Int.ediv" => Self::IntEDiv,
            "extern:Int.emod" => Self::IntEMod,
            "extern:Int.tdiv" => Self::IntTDiv,
            "extern:Int.tmod" => Self::IntTMod,
            "extern:Int.divExact" => Self::IntDivExact,
            "extern:UInt8.add" => Self::UInt8Add,
            "extern:UInt8.sub" => Self::UInt8Sub,
            "extern:UInt8.mul" => Self::UInt8Mul,
            "extern:UInt8.div" => Self::UInt8Div,
            "extern:UInt8.mod" => Self::UInt8Mod,
            "extern:UInt8.land" => Self::UInt8Land,
            "extern:UInt8.lor" => Self::UInt8Lor,
            "extern:UInt8.xor" => Self::UInt8Xor,
            "extern:UInt8.shiftLeft" => Self::UInt8ShiftLeft,
            "extern:UInt8.shiftRight" => Self::UInt8ShiftRight,
            "extern:UInt8.complement" => Self::UInt8Complement,
            "extern:UInt8.neg" => Self::UInt8Neg,
            "extern:UInt8.log2" => Self::UInt8Log2,
            "extern:UInt8.decEq" => Self::UInt8DecEq,
            "extern:UInt8.decLe" => Self::UInt8DecLe,
            "extern:UInt8.decLt" => Self::UInt8DecLt,
            "extern:UInt8.ofNat" | "extern:UInt8.ofNatLT" | "extern:UInt8.ofBitVec" => {
                Self::UInt8OfNat
            }
            "extern:UInt8.toNat" | "extern:UInt8.toBitVec" => Self::UInt8ToNat,
            "extern:UInt8.toUInt16" => Self::UInt8ToUInt16,
            "extern:UInt8.toUInt32" => Self::UInt8ToUInt32,
            "extern:UInt8.toUInt64" => Self::UInt8ToUInt64,
            "extern:UInt8.toUSize" => Self::UInt8ToUSize,
            "extern:UInt16.add" => Self::UInt16Add,
            "extern:UInt16.sub" => Self::UInt16Sub,
            "extern:UInt16.mul" => Self::UInt16Mul,
            "extern:UInt16.div" => Self::UInt16Div,
            "extern:UInt16.mod" => Self::UInt16Mod,
            "extern:UInt16.land" => Self::UInt16Land,
            "extern:UInt16.lor" => Self::UInt16Lor,
            "extern:UInt16.xor" => Self::UInt16Xor,
            "extern:UInt16.shiftLeft" => Self::UInt16ShiftLeft,
            "extern:UInt16.shiftRight" => Self::UInt16ShiftRight,
            "extern:UInt16.complement" => Self::UInt16Complement,
            "extern:UInt16.neg" => Self::UInt16Neg,
            "extern:UInt16.log2" => Self::UInt16Log2,
            "extern:UInt16.decEq" => Self::UInt16DecEq,
            "extern:UInt16.decLe" => Self::UInt16DecLe,
            "extern:UInt16.decLt" => Self::UInt16DecLt,
            "extern:UInt16.ofNat" | "extern:UInt16.ofNatLT" | "extern:UInt16.ofBitVec" => {
                Self::UInt16OfNat
            }
            "extern:UInt16.toNat" | "extern:UInt16.toBitVec" => Self::UInt16ToNat,
            "extern:UInt16.toUInt8" => Self::UInt16ToUInt8,
            "extern:UInt16.toUInt32" => Self::UInt16ToUInt32,
            "extern:UInt16.toUInt64" => Self::UInt16ToUInt64,
            "extern:UInt16.toUSize" => Self::UInt16ToUSize,
            "extern:UInt32.add" => Self::UInt32Add,
            "extern:UInt32.sub" => Self::UInt32Sub,
            "extern:UInt32.mul" => Self::UInt32Mul,
            "extern:UInt32.div" => Self::UInt32Div,
            "extern:UInt32.mod" => Self::UInt32Mod,
            "extern:UInt32.land" => Self::UInt32Land,
            "extern:UInt32.lor" => Self::UInt32Lor,
            "extern:UInt32.xor" => Self::UInt32Xor,
            "extern:UInt32.shiftLeft" => Self::UInt32ShiftLeft,
            "extern:UInt32.shiftRight" => Self::UInt32ShiftRight,
            "extern:UInt32.complement" => Self::UInt32Complement,
            "extern:UInt32.neg" => Self::UInt32Neg,
            "extern:UInt32.log2" => Self::UInt32Log2,
            "extern:UInt32.decEq" => Self::UInt32DecEq,
            "extern:UInt32.decLe" => Self::UInt32DecLe,
            "extern:UInt32.decLt" => Self::UInt32DecLt,
            "extern:UInt32.ofNat" | "extern:UInt32.ofNatLT" | "extern:UInt32.ofBitVec" => {
                Self::UInt32OfNat
            }
            "extern:UInt32.toNat" | "extern:UInt32.toBitVec" => Self::UInt32ToNat,
            "extern:UInt32.toUInt8" => Self::UInt32ToUInt8,
            "extern:UInt32.toUInt16" => Self::UInt32ToUInt16,
            "extern:UInt32.toUInt64" => Self::UInt32ToUInt64,
            "extern:UInt32.toUSize" => Self::UInt32ToUSize,
            "extern:UInt64.add" => Self::UInt64Add,
            "extern:UInt64.sub" => Self::UInt64Sub,
            "extern:UInt64.mul" => Self::UInt64Mul,
            "extern:UInt64.div" => Self::UInt64Div,
            "extern:UInt64.mod" => Self::UInt64Mod,
            "extern:UInt64.land" => Self::UInt64Land,
            "extern:UInt64.lor" => Self::UInt64Lor,
            "extern:UInt64.xor" => Self::UInt64Xor,
            "extern:UInt64.shiftLeft" => Self::UInt64ShiftLeft,
            "extern:UInt64.shiftRight" => Self::UInt64ShiftRight,
            "extern:UInt64.complement" => Self::UInt64Complement,
            "extern:UInt64.neg" => Self::UInt64Neg,
            "extern:UInt64.log2" => Self::UInt64Log2,
            "extern:UInt64.decEq" => Self::UInt64DecEq,
            "extern:UInt64.decLe" => Self::UInt64DecLe,
            "extern:UInt64.decLt" => Self::UInt64DecLt,
            "extern:UInt64.ofNat" | "extern:UInt64.ofNatLT" | "extern:UInt64.ofBitVec" => {
                Self::UInt64OfNat
            }
            "extern:UInt64.toNat" | "extern:UInt64.toBitVec" => Self::UInt64ToNat,
            "extern:UInt64.toUInt8" => Self::UInt64ToUInt8,
            "extern:UInt64.toUInt16" => Self::UInt64ToUInt16,
            "extern:UInt64.toUInt32" => Self::UInt64ToUInt32,
            "extern:UInt64.toUSize" => Self::UInt64ToUSize,
            "extern:mixHash" | "extern:UInt64.mixHash" => Self::UInt64MixHash,
            "extern:USize.add" => Self::USizeAdd,
            "extern:USize.sub" => Self::USizeSub,
            "extern:USize.mul" => Self::USizeMul,
            "extern:USize.div" => Self::USizeDiv,
            "extern:USize.mod" => Self::USizeMod,
            "extern:USize.land" => Self::USizeLand,
            "extern:USize.lor" => Self::USizeLor,
            "extern:USize.xor" => Self::USizeXor,
            "extern:USize.shiftLeft" => Self::USizeShiftLeft,
            "extern:USize.shiftRight" => Self::USizeShiftRight,
            "extern:USize.complement" => Self::USizeComplement,
            "extern:USize.neg" => Self::USizeNeg,
            "extern:USize.log2" => Self::USizeLog2,
            "extern:USize.decEq" => Self::USizeDecEq,
            "extern:USize.decLe" => Self::USizeDecLe,
            "extern:USize.decLt" => Self::USizeDecLt,
            "extern:USize.ofNat"
            | "extern:USize.ofNatLT"
            | "extern:USize.ofNat32"
            | "extern:USize.ofBitVec" => Self::USizeOfNat,
            "extern:USize.toNat" | "extern:USize.toBitVec" => Self::USizeToNat,
            "extern:USize.toUInt8" => Self::USizeToUInt8,
            "extern:USize.toUInt16" => Self::USizeToUInt16,
            "extern:USize.toUInt32" => Self::USizeToUInt32,
            "extern:USize.toUInt64" => Self::USizeToUInt64,
            "extern:USize.repr" => Self::USizeRepr,
            "extern:Int8.add" => Self::Int8Add,
            "extern:Int8.sub" => Self::Int8Sub,
            "extern:Int8.mul" => Self::Int8Mul,
            "extern:Int8.div" => Self::Int8Div,
            "extern:Int8.mod" => Self::Int8Mod,
            "extern:Int8.land" => Self::Int8Land,
            "extern:Int8.lor" => Self::Int8Lor,
            "extern:Int8.xor" => Self::Int8Xor,
            "extern:Int8.shiftLeft" => Self::Int8ShiftLeft,
            "extern:Int8.shiftRight" => Self::Int8ShiftRight,
            "extern:Int8.complement" => Self::Int8Complement,
            "extern:Int8.neg" => Self::Int8Neg,
            "extern:Int8.abs" => Self::Int8Abs,
            "extern:Int8.decEq" => Self::Int8DecEq,
            "extern:Int8.decLe" => Self::Int8DecLe,
            "extern:Int8.decLt" => Self::Int8DecLt,
            "extern:Int8.ofNat" | "extern:Int8.ofInt" => Self::Int8OfNat,
            "extern:Int8.toInt" => Self::Int8ToInt,
            "extern:Int8.toInt16"
            | "extern:Int8.toInt32"
            | "extern:Int8.toInt64"
            | "extern:Int8.toISize" => Self::Int8ToWidth,
            "extern:Int16.add" => Self::Int16Add,
            "extern:Int16.sub" => Self::Int16Sub,
            "extern:Int16.mul" => Self::Int16Mul,
            "extern:Int16.div" => Self::Int16Div,
            "extern:Int16.mod" => Self::Int16Mod,
            "extern:Int16.land" => Self::Int16Land,
            "extern:Int16.lor" => Self::Int16Lor,
            "extern:Int16.xor" => Self::Int16Xor,
            "extern:Int16.shiftLeft" => Self::Int16ShiftLeft,
            "extern:Int16.shiftRight" => Self::Int16ShiftRight,
            "extern:Int16.complement" => Self::Int16Complement,
            "extern:Int16.neg" => Self::Int16Neg,
            "extern:Int16.abs" => Self::Int16Abs,
            "extern:Int16.decEq" => Self::Int16DecEq,
            "extern:Int16.decLe" => Self::Int16DecLe,
            "extern:Int16.decLt" => Self::Int16DecLt,
            "extern:Int16.ofNat" | "extern:Int16.ofInt" => Self::Int16OfNat,
            "extern:Int16.toInt" => Self::Int16ToInt,
            "extern:Int16.toInt8"
            | "extern:Int16.toInt32"
            | "extern:Int16.toInt64"
            | "extern:Int16.toISize" => Self::Int16ToWidth,
            "extern:Int32.add" => Self::Int32Add,
            "extern:Int32.sub" => Self::Int32Sub,
            "extern:Int32.mul" => Self::Int32Mul,
            "extern:Int32.div" => Self::Int32Div,
            "extern:Int32.mod" => Self::Int32Mod,
            "extern:Int32.land" => Self::Int32Land,
            "extern:Int32.lor" => Self::Int32Lor,
            "extern:Int32.xor" => Self::Int32Xor,
            "extern:Int32.shiftLeft" => Self::Int32ShiftLeft,
            "extern:Int32.shiftRight" => Self::Int32ShiftRight,
            "extern:Int32.complement" => Self::Int32Complement,
            "extern:Int32.neg" => Self::Int32Neg,
            "extern:Int32.abs" => Self::Int32Abs,
            "extern:Int32.decEq" => Self::Int32DecEq,
            "extern:Int32.decLe" => Self::Int32DecLe,
            "extern:Int32.decLt" => Self::Int32DecLt,
            "extern:Int32.ofNat" | "extern:Int32.ofInt" => Self::Int32OfNat,
            "extern:Int32.toInt" => Self::Int32ToInt,
            "extern:Int32.toInt8"
            | "extern:Int32.toInt16"
            | "extern:Int32.toInt64"
            | "extern:Int32.toISize" => Self::Int32ToWidth,
            "extern:Int64.add" => Self::Int64Add,
            "extern:Int64.sub" => Self::Int64Sub,
            "extern:Int64.mul" => Self::Int64Mul,
            "extern:Int64.div" => Self::Int64Div,
            "extern:Int64.mod" => Self::Int64Mod,
            "extern:Int64.land" => Self::Int64Land,
            "extern:Int64.lor" => Self::Int64Lor,
            "extern:Int64.xor" => Self::Int64Xor,
            "extern:Int64.shiftLeft" => Self::Int64ShiftLeft,
            "extern:Int64.shiftRight" => Self::Int64ShiftRight,
            "extern:Int64.complement" => Self::Int64Complement,
            "extern:Int64.neg" => Self::Int64Neg,
            "extern:Int64.abs" => Self::Int64Abs,
            "extern:Int64.decEq" => Self::Int64DecEq,
            "extern:Int64.decLe" => Self::Int64DecLe,
            "extern:Int64.decLt" => Self::Int64DecLt,
            "extern:Int64.ofNat" | "extern:Int64.ofInt" => Self::Int64OfNat,
            "extern:Int64.toInt" => Self::Int64ToInt,
            "extern:Int64.toInt8"
            | "extern:Int64.toInt16"
            | "extern:Int64.toInt32"
            | "extern:Int64.toISize" => Self::Int64ToWidth,
            "extern:ISize.add" => Self::ISizeAdd,
            "extern:ISize.sub" => Self::ISizeSub,
            "extern:ISize.mul" => Self::ISizeMul,
            "extern:ISize.div" => Self::ISizeDiv,
            "extern:ISize.mod" => Self::ISizeMod,
            "extern:ISize.land" => Self::ISizeLand,
            "extern:ISize.lor" => Self::ISizeLor,
            "extern:ISize.xor" => Self::ISizeXor,
            "extern:ISize.shiftLeft" => Self::ISizeShiftLeft,
            "extern:ISize.shiftRight" => Self::ISizeShiftRight,
            "extern:ISize.complement" => Self::ISizeComplement,
            "extern:ISize.neg" => Self::ISizeNeg,
            "extern:ISize.abs" => Self::ISizeAbs,
            "extern:ISize.decEq" => Self::ISizeDecEq,
            "extern:ISize.decLe" => Self::ISizeDecLe,
            "extern:ISize.decLt" => Self::ISizeDecLt,
            "extern:ISize.ofNat" | "extern:ISize.ofInt" => Self::ISizeOfNat,
            "extern:ISize.toInt" => Self::ISizeToInt,
            "extern:ISize.toInt8"
            | "extern:ISize.toInt16"
            | "extern:ISize.toInt32"
            | "extern:ISize.toInt64" => Self::ISizeToWidth,
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
            "extern:ByteArray.beq" => Self::ByteArrayBeq,
            "extern:ByteArray.copySlice" => Self::ByteArrayCopySlice,
            "extern:ByteArray.data" => Self::ByteArrayData,
            "extern:ByteArray.decEq" => Self::ByteArrayDecEq,
            "extern:ByteArray.emptyWithCapacity" => Self::ByteArrayEmptyWithCapacity,
            "extern:ByteArray.get" => Self::ByteArrayGet,
            "extern:ByteArray.hash" => Self::ByteArrayHash,
            "extern:ByteArray.mk" => Self::ByteArrayMk,
            "extern:ByteArray.push" => Self::ByteArrayPush,
            "extern:ByteArray.set" => Self::ByteArraySet,
            "extern:ByteArray.size" => Self::ByteArraySize,
            "extern:ByteArray.uget" => Self::ByteArrayUGet,
            "extern:ByteArray.uset" => Self::ByteArrayUset,
            "extern:ByteArray.validateUTF8" => Self::ByteArrayValidateUtf8,
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
    InvalidByteArrayObject,
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
            Self::InvalidByteArrayObject => {
                write!(
                    f,
                    "Marrow scalar-array element size disagrees with ByteArray"
                )
            }
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
        // Nat.divExact shares Nat.div's runtime: the pin's definition is
        // `x / y` with the divisibility proof erased before the call
        // (Init/Data/Nat/Div/Basic.lean:110).
        IntrinsicImplementation::NatDiv | IntrinsicImplementation::NatDivExact => {
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
        // Nat.modCore x y = if 0 < y then x mod y else x (Init/Prelude.lean:2196):
        // the zero divisor yields the dividend, which is exactly Nat.mod's
        // runtime contract, so one handler serves both rows.
        IntrinsicImplementation::NatMod | IntrinsicImplementation::NatModCore => {
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
        // Int rows (bead franken_lean-m7vm). The pin's scalar plane is
        // i32-ranged: every fast path computes in i64 and re-boxes through
        // lean_int64_to_int (src/include/lean/lean.h:1611-1623), while big
        // operands take the exact mpz paths (lean_int_big_*,
        // src/runtime/object.cpp). Both planes produce the same mathematical
        // value, so these handlers compute on sign + magnitude pairs and
        // canonicalize once; only the zero-divisor contracts differ per row.
        IntrinsicImplementation::IntAdd | IntrinsicImplementation::IntSub => {
            expect_arity(row, args, 2)?;
            let is_add = implementation == IntrinsicImplementation::IntAdd;
            let (negative, magnitude) = with_int_views(
                &args[0],
                &args[1],
                if is_add { "Int.add" } else { "Int.sub" },
                |left, right| -> Result<_, IntrinsicFailure> {
                    let estimate = u128::from(
                        left.magnitude
                            .bit_length()
                            .max(right.magnitude.bit_length()),
                    ) + 1;
                    ensure_nat_bits(max_nat_magnitude_bytes, estimate)?;
                    Ok(if is_add {
                        signed_add(left, right)
                    } else {
                        signed_sub(left, right)
                    })
                },
            )??;
            finish_int_result(negative, magnitude, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::IntMul => {
            expect_arity(row, args, 2)?;
            let (negative, product) = with_int_views(
                &args[0],
                &args[1],
                "Int.mul",
                |left, right| -> Result<_, IntrinsicFailure> {
                    let estimate = u128::from(left.magnitude.bit_length())
                        .saturating_add(u128::from(right.magnitude.bit_length()));
                    ensure_nat_bits(max_nat_magnitude_bytes, estimate)?;
                    Ok(signed_mul(left, right))
                },
            )??;
            finish_int_result(negative, product, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::IntNeg => {
            expect_arity(row, args, 1)?;
            let (negative, magnitude) = with_int_view(
                &args[0],
                "Int.neg",
                0,
                |value| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(value.magnitude.bit_length()),
                    )?;
                    Ok((
                        !value.negative && !value.magnitude.is_zero(),
                        value.magnitude.to_owned(),
                    ))
                },
            )??;
            finish_int_result(negative, magnitude, max_nat_magnitude_bytes)
        }
        // Init/Data/Int/Basic.lean:61 — negSucc n is -(n + 1), never zero.
        IntrinsicImplementation::IntNegSucc => {
            expect_arity(row, args, 1)?;
            let (magnitude, _) = with_nat_view(&args[0], "Int.negSucc", 0, |value| {
                let successor_bits = u128::from(value.bit_length()) + 1;
                ensure_nat_bits(max_nat_magnitude_bytes, successor_bits)?;
                Ok::<_, IntrinsicFailure>((
                    value.add(BigNatView::from_limbs_le(&[1])),
                    successor_bits,
                ))
            })??;
            finish_int_result(true, magnitude, max_nat_magnitude_bytes)
        }
        // Init/Data/Int/Basic.lean:60 — ofNat re-boxes a Nat as an Int; the
        // value plane is identical and only the canonical form can differ.
        IntrinsicImplementation::IntOfNat => {
            expect_arity(row, args, 1)?;
            let (magnitude, _) = with_nat_view(&args[0], "Int.ofNat", 0, |value| {
                ensure_nat_bits(max_nat_magnitude_bytes, u128::from(value.bit_length()))?;
                Ok::<_, IntrinsicFailure>((value.to_owned(), ()))
            })??;
            finish_int_result(false, magnitude, max_nat_magnitude_bytes)
        }
        // Init/Data/Int/Basic.lean:326 — natAbs keeps nonnegative values and
        // negates the rest; the result is a Nat, not an Int.
        IntrinsicImplementation::IntNatAbs => {
            expect_arity(row, args, 1)?;
            let magnitude = with_int_view(&args[0], "Int.natAbs", 0, |value| {
                ensure_nat_bits(
                    max_nat_magnitude_bytes,
                    u128::from(value.magnitude.bit_length()),
                )?;
                Ok::<_, IntrinsicFailure>(value.magnitude.to_owned())
            })??;
            finish_nat_result(magnitude, max_nat_magnitude_bytes)
        }
        IntrinsicImplementation::IntDecEq
        | IntrinsicImplementation::IntDecLe
        | IntrinsicImplementation::IntDecLt => {
            expect_arity(row, args, 2)?;
            use std::cmp::Ordering;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::IntDecEq => "Int.decEq",
                IntrinsicImplementation::IntDecLe => "Int.decLe",
                _ => "Int.decLt",
            };
            let ordering =
                with_int_views(
                    &args[0],
                    &args[1],
                    operation,
                    |left, right| match implementation {
                        IntrinsicImplementation::IntDecEq => {
                            left.magnitude.beq(right.magnitude) && left.negative == right.negative
                        }
                        _ => match signed_cmp(left, right) {
                            Ordering::Equal => implementation == IntrinsicImplementation::IntDecLe,
                            Ordering::Less => true,
                            Ordering::Greater => false,
                        },
                    },
                )?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        // Init/Data/Int/Basic.lean:278.
        IntrinsicImplementation::IntDecNonneg => {
            expect_arity(row, args, 1)?;
            let nonneg = with_int_view(&args[0], "Int.decNonneg", 0, |value| !value.negative)?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(nonneg))))
        }
        // T-rounding division: lean_int_div and lean_int_div_exact share one
        // body (lean.h:1698-1746); truncation toward zero, divisor zero
        // answers box(0). Euclidean division adjusts the quotient when the
        // truncated remainder is negative (lean.h:1765-1805).
        IntrinsicImplementation::IntTDiv
        | IntrinsicImplementation::IntDivExact
        | IntrinsicImplementation::IntEDiv => {
            expect_arity(row, args, 2)?;
            let euclidean = implementation == IntrinsicImplementation::IntEDiv;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::IntTDiv => "Int.tdiv",
                IntrinsicImplementation::IntDivExact => "Int.divExact",
                _ => "Int.ediv",
            };
            let (negative, quotient) = with_int_views(
                &args[0],
                &args[1],
                operation,
                |numerator, denominator| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(numerator.magnitude.bit_length()),
                    )?;
                    if denominator.magnitude.is_zero() {
                        return Ok((false, BigNat::zero()));
                    }
                    Ok(signed_quotient(numerator, denominator, euclidean))
                },
            )??;
            finish_int_result(negative, quotient, max_nat_magnitude_bytes)
        }
        // T-rounding remainder follows the dividend's sign; a zero divisor
        // returns the dividend itself (lean.h:1749-1762). The Euclidean
        // remainder is normalized into 0 <= r < |d| (lean.h:1807-1845).
        IntrinsicImplementation::IntTMod | IntrinsicImplementation::IntEMod => {
            expect_arity(row, args, 2)?;
            let euclidean = implementation == IntrinsicImplementation::IntEMod;
            let operation: &'static str = if euclidean { "Int.emod" } else { "Int.tmod" };
            let zero_divisor_identity = with_int_views(
                &args[0],
                &args[1],
                operation,
                |numerator, denominator| -> Result<_, IntrinsicFailure> {
                    ensure_nat_bits(
                        max_nat_magnitude_bytes,
                        u128::from(numerator.magnitude.bit_length()),
                    )?;
                    Ok(denominator.magnitude.is_zero())
                },
            )??;
            if zero_divisor_identity {
                return Ok(IntrinsicResult::owned(args[0].clone_ref()));
            }
            let (negative, remainder) = with_int_views(
                &args[0],
                &args[1],
                operation,
                |numerator, denominator| -> Result<_, IntrinsicFailure> {
                    Ok(signed_remainder(numerator, denominator, euclidean))
                },
            )??;
            finish_int_result(negative, remainder, max_nat_magnitude_bytes)
        }
        // UInt8 rows. The pin's inline C computes in the byte storage plane:
        // wrapping two's-complement arithmetic (lean.h uint8 section), C
        // truncation for div with box(0) on a zero divisor, dividend identity
        // for mod, and shift amounts reduced modulo 8.
        IntrinsicImplementation::UInt8Add
        | IntrinsicImplementation::UInt8Sub
        | IntrinsicImplementation::UInt8Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt8Add => "UInt8.add",
                IntrinsicImplementation::UInt8Sub => "UInt8.sub",
                _ => "UInt8.mul",
            };
            let left = byte_argument(&args[0], operation, 0)?;
            let right = byte_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt8Add => left.wrapping_add(right),
                IntrinsicImplementation::UInt8Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(uint8_result(value))
        }
        IntrinsicImplementation::UInt8Div | IntrinsicImplementation::UInt8Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::UInt8Div;
            let operation: &'static str = if is_div { "UInt8.div" } else { "UInt8.mod" };
            let dividend = byte_argument(&args[0], operation, 0)?;
            let divisor = byte_argument(&args[1], operation, 1)?;
            // lean_uint8_div/mod: divisor zero answers 0 / the dividend.
            let value = if divisor == 0 {
                if is_div { 0 } else { dividend }
            } else if is_div {
                dividend / divisor
            } else {
                dividend % divisor
            };
            Ok(uint8_result(value))
        }
        IntrinsicImplementation::UInt8Land
        | IntrinsicImplementation::UInt8Lor
        | IntrinsicImplementation::UInt8Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt8Land => "UInt8.land",
                IntrinsicImplementation::UInt8Lor => "UInt8.lor",
                _ => "UInt8.xor",
            };
            let left = byte_argument(&args[0], operation, 0)?;
            let right = byte_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt8Land => left & right,
                IntrinsicImplementation::UInt8Lor => left | right,
                _ => left ^ right,
            };
            Ok(uint8_result(value))
        }
        IntrinsicImplementation::UInt8ShiftLeft | IntrinsicImplementation::UInt8ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::UInt8ShiftLeft;
            let operation: &'static str = if is_left {
                "UInt8.shiftLeft"
            } else {
                "UInt8.shiftRight"
            };
            let value = byte_argument(&args[0], operation, 0)?;
            let amount = byte_argument(&args[1], operation, 1)?;
            // The pin shifts by `b % 8`; amounts past one storage byte wrap.
            let amount = u32::from(amount % 8);
            Ok(uint8_result(if is_left {
                ((value as u16) << amount) as u8
            } else {
                value >> amount
            }))
        }
        IntrinsicImplementation::UInt8Complement | IntrinsicImplementation::UInt8Neg => {
            expect_arity(row, args, 1)?;
            let is_complement = implementation == IntrinsicImplementation::UInt8Complement;
            let operation: &'static str = if is_complement {
                "UInt8.complement"
            } else {
                "UInt8.neg"
            };
            let value = byte_argument(&args[0], operation, 0)?;
            Ok(uint8_result(if is_complement {
                !value
            } else {
                value.wrapping_neg()
            }))
        }
        IntrinsicImplementation::UInt8Log2 => {
            expect_arity(row, args, 1)?;
            let value = byte_argument(&args[0], "UInt8.log2", 0)?;
            // lean_uint8_log2 counts halvings from >= 2; 0 and 1 answer 0.
            Ok(uint8_result(if value < 2 {
                0
            } else {
                value.ilog2() as u8
            }))
        }
        IntrinsicImplementation::UInt8DecEq
        | IntrinsicImplementation::UInt8DecLe
        | IntrinsicImplementation::UInt8DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt8DecEq => "UInt8.decEq",
                IntrinsicImplementation::UInt8DecLe => "UInt8.decLe",
                _ => "UInt8.decLt",
            };
            let left = byte_argument(&args[0], operation, 0)?;
            let right = byte_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::UInt8DecEq => left == right,
                IntrinsicImplementation::UInt8DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        // ofNat, ofNatLT and ofBitVec share the pin's lean_uint8_of_nat
        // runtime: a truncating cast of an arbitrary Nat to its low byte.
        IntrinsicImplementation::UInt8OfNat => {
            expect_arity(row, args, 1)?;
            let low = nat_low_u64(&args[0], "UInt8.ofNat", 0)?;
            Ok(uint8_result(low as u8))
        }
        IntrinsicImplementation::UInt8ToNat => {
            expect_arity(row, args, 1)?;
            let value = byte_argument(&args[0], "UInt8.toNat", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(value))))
        }
        IntrinsicImplementation::UInt8ToUInt16
        | IntrinsicImplementation::UInt8ToUInt32
        | IntrinsicImplementation::UInt8ToUInt64
        | IntrinsicImplementation::UInt8ToUSize => {
            expect_arity(row, args, 1)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt8ToUInt16 => "UInt8.toUInt16",
                IntrinsicImplementation::UInt8ToUInt32 => "UInt8.toUInt32",
                IntrinsicImplementation::UInt8ToUInt64 => "UInt8.toUInt64",
                _ => "UInt8.toUSize",
            };
            let value = byte_argument(&args[0], operation, 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(value))))
        }
        IntrinsicImplementation::UInt16Add
        | IntrinsicImplementation::UInt16Sub
        | IntrinsicImplementation::UInt16Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt16Add => "UInt16.add",
                IntrinsicImplementation::UInt16Sub => "UInt16.sub",
                _ => "UInt16.mul",
            };
            let left = uint16_argument(&args[0], operation, 0)?;
            let right = uint16_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt16Add => left.wrapping_add(right),
                IntrinsicImplementation::UInt16Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(uint16_result(value))
        }
        IntrinsicImplementation::UInt16Div | IntrinsicImplementation::UInt16Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::UInt16Div;
            let operation: &'static str = if is_div { "UInt16.div" } else { "UInt16.mod" };
            let dividend = uint16_argument(&args[0], operation, 0)?;
            let divisor = uint16_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0 } else { dividend }
            } else if is_div {
                dividend / divisor
            } else {
                dividend % divisor
            };
            Ok(uint16_result(value))
        }
        IntrinsicImplementation::UInt16Land
        | IntrinsicImplementation::UInt16Lor
        | IntrinsicImplementation::UInt16Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt16Land => "UInt16.land",
                IntrinsicImplementation::UInt16Lor => "UInt16.lor",
                _ => "UInt16.xor",
            };
            let left = uint16_argument(&args[0], operation, 0)?;
            let right = uint16_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt16Land => left & right,
                IntrinsicImplementation::UInt16Lor => left | right,
                _ => left ^ right,
            };
            Ok(uint16_result(value))
        }
        IntrinsicImplementation::UInt16ShiftLeft | IntrinsicImplementation::UInt16ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::UInt16ShiftLeft;
            let operation: &'static str = if is_left {
                "UInt16.shiftLeft"
            } else {
                "UInt16.shiftRight"
            };
            let value = uint16_argument(&args[0], operation, 0)?;
            let amount = uint16_argument(&args[1], operation, 1)?;
            let amount = u32::from(amount % 16);
            Ok(uint16_result(if is_left {
                ((value as u32) << amount) as u16
            } else {
                value >> amount
            }))
        }
        IntrinsicImplementation::UInt16Complement | IntrinsicImplementation::UInt16Neg => {
            expect_arity(row, args, 1)?;
            let is_complement = implementation == IntrinsicImplementation::UInt16Complement;
            let operation: &'static str = if is_complement {
                "UInt16.complement"
            } else {
                "UInt16.neg"
            };
            let value = uint16_argument(&args[0], operation, 0)?;
            Ok(uint16_result(if is_complement {
                !value
            } else {
                value.wrapping_neg()
            }))
        }
        IntrinsicImplementation::UInt16Log2 => {
            expect_arity(row, args, 1)?;
            let value = uint16_argument(&args[0], "UInt16.log2", 0)?;
            Ok(uint16_result(if value < 2 {
                0
            } else {
                value.ilog2() as u16
            }))
        }
        IntrinsicImplementation::UInt16DecEq
        | IntrinsicImplementation::UInt16DecLe
        | IntrinsicImplementation::UInt16DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt16DecEq => "UInt16.decEq",
                IntrinsicImplementation::UInt16DecLe => "UInt16.decLe",
                _ => "UInt16.decLt",
            };
            let left = uint16_argument(&args[0], operation, 0)?;
            let right = uint16_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::UInt16DecEq => left == right,
                IntrinsicImplementation::UInt16DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::UInt16OfNat => {
            expect_arity(row, args, 1)?;
            let low = nat_low_u64(&args[0], "UInt16.ofNat", 0)?;
            Ok(uint16_result(low as u16))
        }
        IntrinsicImplementation::UInt16ToNat => {
            expect_arity(row, args, 1)?;
            let value = uint16_argument(&args[0], "UInt16.toNat", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(value))))
        }
        IntrinsicImplementation::UInt16ToUInt8
        | IntrinsicImplementation::UInt16ToUInt32
        | IntrinsicImplementation::UInt16ToUInt64
        | IntrinsicImplementation::UInt16ToUSize => {
            expect_arity(row, args, 1)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt16ToUInt8 => "UInt16.toUInt8",
                IntrinsicImplementation::UInt16ToUInt32 => "UInt16.toUInt32",
                IntrinsicImplementation::UInt16ToUInt64 => "UInt16.toUInt64",
                _ => "UInt16.toUSize",
            };
            let value = uint16_argument(&args[0], operation, 0)?;
            Ok(match implementation {
                IntrinsicImplementation::UInt16ToUInt8 => uint8_result(value as u8),
                IntrinsicImplementation::UInt16ToUInt32 => uint32_result(value as u32),
                IntrinsicImplementation::UInt16ToUInt64 => uint64_result(value as u64),
                _ => usize_result(value as usize),
            })
        }
        IntrinsicImplementation::UInt32Add
        | IntrinsicImplementation::UInt32Sub
        | IntrinsicImplementation::UInt32Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt32Add => "UInt32.add",
                IntrinsicImplementation::UInt32Sub => "UInt32.sub",
                _ => "UInt32.mul",
            };
            let left = uint32_argument(&args[0], operation, 0)?;
            let right = uint32_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt32Add => left.wrapping_add(right),
                IntrinsicImplementation::UInt32Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(uint32_result(value))
        }
        IntrinsicImplementation::UInt32Div | IntrinsicImplementation::UInt32Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::UInt32Div;
            let operation: &'static str = if is_div { "UInt32.div" } else { "UInt32.mod" };
            let dividend = uint32_argument(&args[0], operation, 0)?;
            let divisor = uint32_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0 } else { dividend }
            } else if is_div {
                dividend / divisor
            } else {
                dividend % divisor
            };
            Ok(uint32_result(value))
        }
        IntrinsicImplementation::UInt32Land
        | IntrinsicImplementation::UInt32Lor
        | IntrinsicImplementation::UInt32Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt32Land => "UInt32.land",
                IntrinsicImplementation::UInt32Lor => "UInt32.lor",
                _ => "UInt32.xor",
            };
            let left = uint32_argument(&args[0], operation, 0)?;
            let right = uint32_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt32Land => left & right,
                IntrinsicImplementation::UInt32Lor => left | right,
                _ => left ^ right,
            };
            Ok(uint32_result(value))
        }
        IntrinsicImplementation::UInt32ShiftLeft | IntrinsicImplementation::UInt32ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::UInt32ShiftLeft;
            let operation: &'static str = if is_left {
                "UInt32.shiftLeft"
            } else {
                "UInt32.shiftRight"
            };
            let value = uint32_argument(&args[0], operation, 0)?;
            let amount = uint32_argument(&args[1], operation, 1)?;
            let amount = amount % 32;
            Ok(uint32_result(if is_left {
                ((value as u64) << amount) as u32
            } else {
                value >> amount
            }))
        }
        IntrinsicImplementation::UInt32Complement | IntrinsicImplementation::UInt32Neg => {
            expect_arity(row, args, 1)?;
            let is_complement = implementation == IntrinsicImplementation::UInt32Complement;
            let operation: &'static str = if is_complement {
                "UInt32.complement"
            } else {
                "UInt32.neg"
            };
            let value = uint32_argument(&args[0], operation, 0)?;
            Ok(uint32_result(if is_complement {
                !value
            } else {
                value.wrapping_neg()
            }))
        }
        IntrinsicImplementation::UInt32Log2 => {
            expect_arity(row, args, 1)?;
            let value = uint32_argument(&args[0], "UInt32.log2", 0)?;
            Ok(uint32_result(if value < 2 { 0 } else { value.ilog2() }))
        }
        IntrinsicImplementation::UInt32DecEq
        | IntrinsicImplementation::UInt32DecLe
        | IntrinsicImplementation::UInt32DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt32DecEq => "UInt32.decEq",
                IntrinsicImplementation::UInt32DecLe => "UInt32.decLe",
                _ => "UInt32.decLt",
            };
            let left = uint32_argument(&args[0], operation, 0)?;
            let right = uint32_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::UInt32DecEq => left == right,
                IntrinsicImplementation::UInt32DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::UInt32OfNat => {
            expect_arity(row, args, 1)?;
            let low = nat_low_u64(&args[0], "UInt32.ofNat", 0)?;
            Ok(uint32_result(low as u32))
        }
        IntrinsicImplementation::UInt32ToNat => {
            expect_arity(row, args, 1)?;
            let value = uint32_argument(&args[0], "UInt32.toNat", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(value as usize)))
        }
        IntrinsicImplementation::UInt32ToUInt8
        | IntrinsicImplementation::UInt32ToUInt16
        | IntrinsicImplementation::UInt32ToUInt64
        | IntrinsicImplementation::UInt32ToUSize => {
            expect_arity(row, args, 1)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt32ToUInt8 => "UInt32.toUInt8",
                IntrinsicImplementation::UInt32ToUInt16 => "UInt32.toUInt16",
                IntrinsicImplementation::UInt32ToUInt64 => "UInt32.toUInt64",
                _ => "UInt32.toUSize",
            };
            let value = uint32_argument(&args[0], operation, 0)?;
            Ok(match implementation {
                IntrinsicImplementation::UInt32ToUInt8 => uint8_result(value as u8),
                IntrinsicImplementation::UInt32ToUInt16 => uint16_result(value as u16),
                IntrinsicImplementation::UInt32ToUInt64 => uint64_result(value as u64),
                _ => usize_result(value as usize),
            })
        }
        IntrinsicImplementation::UInt64Add
        | IntrinsicImplementation::UInt64Sub
        | IntrinsicImplementation::UInt64Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt64Add => "UInt64.add",
                IntrinsicImplementation::UInt64Sub => "UInt64.sub",
                _ => "UInt64.mul",
            };
            let left = uint64_argument(&args[0], operation, 0)?;
            let right = uint64_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt64Add => left.wrapping_add(right),
                IntrinsicImplementation::UInt64Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(uint64_result(value))
        }
        IntrinsicImplementation::UInt64Div | IntrinsicImplementation::UInt64Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::UInt64Div;
            let operation: &'static str = if is_div { "UInt64.div" } else { "UInt64.mod" };
            let dividend = uint64_argument(&args[0], operation, 0)?;
            let divisor = uint64_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0 } else { dividend }
            } else if is_div {
                dividend / divisor
            } else {
                dividend % divisor
            };
            Ok(uint64_result(value))
        }
        IntrinsicImplementation::UInt64Land
        | IntrinsicImplementation::UInt64Lor
        | IntrinsicImplementation::UInt64Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt64Land => "UInt64.land",
                IntrinsicImplementation::UInt64Lor => "UInt64.lor",
                _ => "UInt64.xor",
            };
            let left = uint64_argument(&args[0], operation, 0)?;
            let right = uint64_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::UInt64Land => left & right,
                IntrinsicImplementation::UInt64Lor => left | right,
                _ => left ^ right,
            };
            Ok(uint64_result(value))
        }
        IntrinsicImplementation::UInt64ShiftLeft | IntrinsicImplementation::UInt64ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::UInt64ShiftLeft;
            let operation: &'static str = if is_left {
                "UInt64.shiftLeft"
            } else {
                "UInt64.shiftRight"
            };
            let value = uint64_argument(&args[0], operation, 0)?;
            let amount = uint64_argument(&args[1], operation, 1)?;
            let amount = (amount % 64) as u32;
            Ok(uint64_result(if is_left {
                value.wrapping_shl(amount)
            } else {
                value >> amount
            }))
        }
        IntrinsicImplementation::UInt64Complement | IntrinsicImplementation::UInt64Neg => {
            expect_arity(row, args, 1)?;
            let is_complement = implementation == IntrinsicImplementation::UInt64Complement;
            let operation: &'static str = if is_complement {
                "UInt64.complement"
            } else {
                "UInt64.neg"
            };
            let value = uint64_argument(&args[0], operation, 0)?;
            Ok(uint64_result(if is_complement {
                !value
            } else {
                value.wrapping_neg()
            }))
        }
        IntrinsicImplementation::UInt64Log2 => {
            expect_arity(row, args, 1)?;
            let value = uint64_argument(&args[0], "UInt64.log2", 0)?;
            Ok(uint64_result(if value < 2 {
                0
            } else {
                u64::from(value.ilog2())
            }))
        }
        IntrinsicImplementation::UInt64DecEq
        | IntrinsicImplementation::UInt64DecLe
        | IntrinsicImplementation::UInt64DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt64DecEq => "UInt64.decEq",
                IntrinsicImplementation::UInt64DecLe => "UInt64.decLe",
                _ => "UInt64.decLt",
            };
            let left = uint64_argument(&args[0], operation, 0)?;
            let right = uint64_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::UInt64DecEq => left == right,
                IntrinsicImplementation::UInt64DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::UInt64OfNat => {
            expect_arity(row, args, 1)?;
            let low = nat_low_u64(&args[0], "UInt64.ofNat", 0)?;
            Ok(uint64_result(low))
        }
        IntrinsicImplementation::UInt64ToNat => {
            expect_arity(row, args, 1)?;
            let value = uint64_argument(&args[0], "UInt64.toNat", 0)?;
            Ok(IntrinsicResult::owned(nat_from_u64(value)))
        }
        IntrinsicImplementation::UInt64ToUInt8
        | IntrinsicImplementation::UInt64ToUInt16
        | IntrinsicImplementation::UInt64ToUInt32
        | IntrinsicImplementation::UInt64ToUSize => {
            expect_arity(row, args, 1)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::UInt64ToUInt8 => "UInt64.toUInt8",
                IntrinsicImplementation::UInt64ToUInt16 => "UInt64.toUInt16",
                IntrinsicImplementation::UInt64ToUInt32 => "UInt64.toUInt32",
                _ => "UInt64.toUSize",
            };
            let value = uint64_argument(&args[0], operation, 0)?;
            Ok(match implementation {
                IntrinsicImplementation::UInt64ToUInt8 => uint8_result(value as u8),
                IntrinsicImplementation::UInt64ToUInt16 => uint16_result(value as u16),
                IntrinsicImplementation::UInt64ToUInt32 => uint32_result(value as u32),
                _ => usize_result(value as usize),
            })
        }
        IntrinsicImplementation::UInt64MixHash => {
            expect_arity(row, args, 2)?;
            let left = uint64_argument(&args[0], "UInt64.mixHash", 0)?;
            let right = uint64_argument(&args[1], "UInt64.mixHash", 1)?;
            let m: u64 = 0xc6a4_a793_5bd1_e995;
            let r: u32 = 47;
            let mut k = right.wrapping_mul(m);
            k ^= k >> r;
            k = k.wrapping_mul(m);
            let mut h = left ^ k;
            h = h.wrapping_mul(m);
            Ok(uint64_result(h))
        }
        IntrinsicImplementation::USizeAdd
        | IntrinsicImplementation::USizeSub
        | IntrinsicImplementation::USizeMul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::USizeAdd => "USize.add",
                IntrinsicImplementation::USizeSub => "USize.sub",
                _ => "USize.mul",
            };
            let left = usize_argument(&args[0], operation, 0)?;
            let right = usize_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::USizeAdd => left.wrapping_add(right),
                IntrinsicImplementation::USizeSub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(usize_result(value))
        }
        IntrinsicImplementation::USizeDiv | IntrinsicImplementation::USizeMod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::USizeDiv;
            let operation: &'static str = if is_div { "USize.div" } else { "USize.mod" };
            let dividend = usize_argument(&args[0], operation, 0)?;
            let divisor = usize_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0 } else { dividend }
            } else if is_div {
                dividend / divisor
            } else {
                dividend % divisor
            };
            Ok(usize_result(value))
        }
        IntrinsicImplementation::USizeLand
        | IntrinsicImplementation::USizeLor
        | IntrinsicImplementation::USizeXor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::USizeLand => "USize.land",
                IntrinsicImplementation::USizeLor => "USize.lor",
                _ => "USize.xor",
            };
            let left = usize_argument(&args[0], operation, 0)?;
            let right = usize_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::USizeLand => left & right,
                IntrinsicImplementation::USizeLor => left | right,
                _ => left ^ right,
            };
            Ok(usize_result(value))
        }
        IntrinsicImplementation::USizeShiftLeft | IntrinsicImplementation::USizeShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::USizeShiftLeft;
            let operation: &'static str = if is_left {
                "USize.shiftLeft"
            } else {
                "USize.shiftRight"
            };
            let value = usize_argument(&args[0], operation, 0)?;
            let amount = usize_argument(&args[1], operation, 1)?;
            let amount = (amount % (std::mem::size_of::<usize>() * 8)) as u32;
            Ok(usize_result(if is_left {
                value.wrapping_shl(amount)
            } else {
                value >> amount
            }))
        }
        IntrinsicImplementation::USizeComplement | IntrinsicImplementation::USizeNeg => {
            expect_arity(row, args, 1)?;
            let is_complement = implementation == IntrinsicImplementation::USizeComplement;
            let operation: &'static str = if is_complement {
                "USize.complement"
            } else {
                "USize.neg"
            };
            let value = usize_argument(&args[0], operation, 0)?;
            Ok(usize_result(if is_complement {
                !value
            } else {
                value.wrapping_neg()
            }))
        }
        IntrinsicImplementation::USizeLog2 => {
            expect_arity(row, args, 1)?;
            let value = usize_argument(&args[0], "USize.log2", 0)?;
            Ok(usize_result(if value < 2 {
                0
            } else {
                value.ilog2() as usize
            }))
        }
        IntrinsicImplementation::USizeDecEq
        | IntrinsicImplementation::USizeDecLe
        | IntrinsicImplementation::USizeDecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::USizeDecEq => "USize.decEq",
                IntrinsicImplementation::USizeDecLe => "USize.decLe",
                _ => "USize.decLt",
            };
            let left = usize_argument(&args[0], operation, 0)?;
            let right = usize_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::USizeDecEq => left == right,
                IntrinsicImplementation::USizeDecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::USizeOfNat => {
            expect_arity(row, args, 1)?;
            let low = nat_low_u64(&args[0], "USize.ofNat", 0)?;
            Ok(usize_result(low as usize))
        }
        IntrinsicImplementation::USizeToNat => {
            expect_arity(row, args, 1)?;
            let value = usize_argument(&args[0], "USize.toNat", 0)?;
            Ok(IntrinsicResult::owned(nat_from_u64(value as u64)))
        }
        IntrinsicImplementation::USizeToUInt8
        | IntrinsicImplementation::USizeToUInt16
        | IntrinsicImplementation::USizeToUInt32
        | IntrinsicImplementation::USizeToUInt64 => {
            expect_arity(row, args, 1)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::USizeToUInt8 => "USize.toUInt8",
                IntrinsicImplementation::USizeToUInt16 => "USize.toUInt16",
                IntrinsicImplementation::USizeToUInt32 => "USize.toUInt32",
                _ => "USize.toUInt64",
            };
            let value = usize_argument(&args[0], operation, 0)?;
            Ok(match implementation {
                IntrinsicImplementation::USizeToUInt8 => uint8_result(value as u8),
                IntrinsicImplementation::USizeToUInt16 => uint16_result(value as u16),
                IntrinsicImplementation::USizeToUInt32 => uint32_result(value as u32),
                _ => uint64_result(value as u64),
            })
        }
        IntrinsicImplementation::USizeRepr => {
            expect_arity(row, args, 1)?;
            let value = usize_argument(&args[0], "USize.repr", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_string(&value.to_string())))
        }
        // Int8 rows. Storage stays in the byte plane exactly like the C:
        // add/sub/mul/neg wrap without ever casting to int8 (the comments in
        // lean.h forbid it — overflow there is UB); div/mod widen to int16 so
        // INT8_MIN / -1 cannot trap; shift amounts are smod 8 with an
        // arithmetic right shift on the signed plane.
        IntrinsicImplementation::Int8Add
        | IntrinsicImplementation::Int8Sub
        | IntrinsicImplementation::Int8Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int8Add => "Int8.add",
                IntrinsicImplementation::Int8Sub => "Int8.sub",
                _ => "Int8.mul",
            };
            let left = int8_argument(&args[0], operation, 0)?;
            let right = int8_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int8Add => left.wrapping_add(right),
                IntrinsicImplementation::Int8Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(int8_result(value))
        }
        IntrinsicImplementation::Int8Div | IntrinsicImplementation::Int8Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::Int8Div;
            let operation: &'static str = if is_div { "Int8.div" } else { "Int8.mod" };
            let dividend = int8_argument(&args[0], operation, 0)?;
            let divisor = int8_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0i8 } else { dividend }
            } else {
                let widened = i32::from(dividend) / i32::from(divisor);
                let remainder = i32::from(dividend) % i32::from(divisor);
                (if is_div { widened } else { remainder }) as i8
            };
            Ok(int8_result(value))
        }
        IntrinsicImplementation::Int8Land
        | IntrinsicImplementation::Int8Lor
        | IntrinsicImplementation::Int8Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int8Land => "Int8.land",
                IntrinsicImplementation::Int8Lor => "Int8.lor",
                _ => "Int8.xor",
            };
            let left = int8_argument(&args[0], operation, 0)?;
            let right = int8_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int8Land => left & right,
                IntrinsicImplementation::Int8Lor => left | right,
                _ => left ^ right,
            };
            Ok(int8_result(value))
        }
        IntrinsicImplementation::Int8ShiftLeft | IntrinsicImplementation::Int8ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::Int8ShiftLeft;
            let operation: &'static str = if is_left {
                "Int8.shiftLeft"
            } else {
                "Int8.shiftRight"
            };
            let storage = byte_argument(&args[0], operation, 0)?;
            let amount = int8_argument(&args[1], operation, 1)?;
            // ((int8_t)a2 % 8 + 8) % 8 — the pin's smod reduction.
            let amount = ((i32::from(amount) % 8) + 8) % 8;
            let value = if is_left {
                ((u16::from(storage)) << amount) as u8
            } else {
                ((storage as i8) >> amount) as u8
            };
            Ok(int8_result(value as i8))
        }
        IntrinsicImplementation::Int8Complement
        | IntrinsicImplementation::Int8Neg
        | IntrinsicImplementation::Int8Abs => {
            expect_arity(row, args, 1)?;
            let storage = byte_argument(
                &args[0],
                match implementation {
                    IntrinsicImplementation::Int8Complement => "Int8.complement",
                    IntrinsicImplementation::Int8Neg => "Int8.neg",
                    _ => "Int8.abs",
                },
                0,
            )?;
            let signed = storage as i8;
            let value = match implementation {
                IntrinsicImplementation::Int8Complement => !signed,
                IntrinsicImplementation::Int8Neg => signed.wrapping_neg(),
                // -a on the unsigned storage plane wraps INT8_MIN back to
                // itself, exactly like the C's deliberate unsigned negate.
                _ => signed.checked_abs().unwrap_or(signed),
            };
            Ok(int8_result(value))
        }
        IntrinsicImplementation::Int8DecEq
        | IntrinsicImplementation::Int8DecLe
        | IntrinsicImplementation::Int8DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int8DecEq => "Int8.decEq",
                IntrinsicImplementation::Int8DecLe => "Int8.decLe",
                _ => "Int8.decLt",
            };
            let left = int8_argument(&args[0], operation, 0)?;
            let right = int8_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::Int8DecEq => left == right,
                IntrinsicImplementation::Int8DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        // ofNat and ofInt share the truncating low-byte cast; big operands
        // truncate their magnitude's low limb with the sign folded in.
        IntrinsicImplementation::Int8OfNat => {
            expect_arity(row, args, 1)?;
            let low = with_int_view(&args[0], "Int8.ofNat", 0, |view| {
                let limbs = view.magnitude.limbs_le();
                let low_byte = limbs.first().copied().unwrap_or(0) as u8;
                if view.negative {
                    (!low_byte).wrapping_add(1)
                } else {
                    low_byte
                }
            })?;
            Ok(int8_result(low as i8))
        }
        // Every widening target shares one scalar encoding at this VM layer:
        // the sign-extended value re-boxed through mk_int, which reproduces
        // the pin's per-width scalar payloads bit for bit. toInt's census
        // contract is owned_res (a fresh object); the fixed-width targets
        // are scalar-class rows.
        IntrinsicImplementation::Int8ToInt => {
            expect_arity(row, args, 1)?;
            let value = int8_argument(&args[0], "Int8.toInt", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_int(i64::from(value))))
        }
        IntrinsicImplementation::Int8ToWidth => {
            expect_arity(row, args, 1)?;
            let value = int8_argument(&args[0], "Int8.toInt16", 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_int(i64::from(value))))
        }
        IntrinsicImplementation::Int16Add
        | IntrinsicImplementation::Int16Sub
        | IntrinsicImplementation::Int16Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int16Add => "Int16.add",
                IntrinsicImplementation::Int16Sub => "Int16.sub",
                _ => "Int16.mul",
            };
            let left = int16_argument(&args[0], operation, 0)?;
            let right = int16_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int16Add => left.wrapping_add(right),
                IntrinsicImplementation::Int16Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(int16_result(value))
        }
        IntrinsicImplementation::Int16Div | IntrinsicImplementation::Int16Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::Int16Div;
            let operation: &'static str = if is_div { "Int16.div" } else { "Int16.mod" };
            let dividend = int16_argument(&args[0], operation, 0)?;
            let divisor = int16_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0i16 } else { dividend }
            } else {
                let widened = i32::from(dividend) / i32::from(divisor);
                let remainder = i32::from(dividend) % i32::from(divisor);
                (if is_div { widened } else { remainder }) as i16
            };
            Ok(int16_result(value))
        }
        IntrinsicImplementation::Int16Land
        | IntrinsicImplementation::Int16Lor
        | IntrinsicImplementation::Int16Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int16Land => "Int16.land",
                IntrinsicImplementation::Int16Lor => "Int16.lor",
                _ => "Int16.xor",
            };
            let left = int16_argument(&args[0], operation, 0)?;
            let right = int16_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int16Land => left & right,
                IntrinsicImplementation::Int16Lor => left | right,
                _ => left ^ right,
            };
            Ok(int16_result(value))
        }
        IntrinsicImplementation::Int16ShiftLeft | IntrinsicImplementation::Int16ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::Int16ShiftLeft;
            let operation: &'static str = if is_left {
                "Int16.shiftLeft"
            } else {
                "Int16.shiftRight"
            };
            let storage = uint16_argument(&args[0], operation, 0)?;
            let amount = int16_argument(&args[1], operation, 1)?;
            let amount = ((i32::from(amount) % 16) + 16) % 16;
            let value = if is_left {
                ((u32::from(storage)) << amount) as u16
            } else {
                ((storage as i16) >> amount) as u16
            };
            Ok(int16_result(value as i16))
        }
        IntrinsicImplementation::Int16Complement
        | IntrinsicImplementation::Int16Neg
        | IntrinsicImplementation::Int16Abs => {
            expect_arity(row, args, 1)?;
            let storage = uint16_argument(
                &args[0],
                match implementation {
                    IntrinsicImplementation::Int16Complement => "Int16.complement",
                    IntrinsicImplementation::Int16Neg => "Int16.neg",
                    _ => "Int16.abs",
                },
                0,
            )?;
            let signed = storage as i16;
            let value = match implementation {
                IntrinsicImplementation::Int16Complement => !signed,
                IntrinsicImplementation::Int16Neg => signed.wrapping_neg(),
                _ => signed.checked_abs().unwrap_or(signed),
            };
            Ok(int16_result(value))
        }
        IntrinsicImplementation::Int16DecEq
        | IntrinsicImplementation::Int16DecLe
        | IntrinsicImplementation::Int16DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int16DecEq => "Int16.decEq",
                IntrinsicImplementation::Int16DecLe => "Int16.decLe",
                _ => "Int16.decLt",
            };
            let left = int16_argument(&args[0], operation, 0)?;
            let right = int16_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::Int16DecEq => left == right,
                IntrinsicImplementation::Int16DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::Int16OfNat => {
            expect_arity(row, args, 1)?;
            let low = with_int_view(&args[0], "Int16.ofNat", 0, |view| {
                let limbs = view.magnitude.limbs_le();
                let low_word = limbs.first().copied().unwrap_or(0) as u16;
                if view.negative {
                    (!low_word).wrapping_add(1)
                } else {
                    low_word
                }
            })?;
            Ok(int16_result(low as i16))
        }
        IntrinsicImplementation::Int16ToInt => {
            expect_arity(row, args, 1)?;
            let value = int16_argument(&args[0], "Int16.toInt", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_int(i64::from(value))))
        }
        IntrinsicImplementation::Int16ToWidth => {
            expect_arity(row, args, 1)?;
            let value = int16_argument(&args[0], "Int16.toInt32", 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_int(i64::from(value))))
        }
        IntrinsicImplementation::Int32Add
        | IntrinsicImplementation::Int32Sub
        | IntrinsicImplementation::Int32Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int32Add => "Int32.add",
                IntrinsicImplementation::Int32Sub => "Int32.sub",
                _ => "Int32.mul",
            };
            let left = int32_argument(&args[0], operation, 0)?;
            let right = int32_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int32Add => left.wrapping_add(right),
                IntrinsicImplementation::Int32Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(int32_result(value))
        }
        IntrinsicImplementation::Int32Div | IntrinsicImplementation::Int32Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::Int32Div;
            let operation: &'static str = if is_div { "Int32.div" } else { "Int32.mod" };
            let dividend = int32_argument(&args[0], operation, 0)?;
            let divisor = int32_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0i32 } else { dividend }
            } else {
                let widened = i64::from(dividend) / i64::from(divisor);
                let remainder = i64::from(dividend) % i64::from(divisor);
                (if is_div { widened } else { remainder }) as i32
            };
            Ok(int32_result(value))
        }
        IntrinsicImplementation::Int32Land
        | IntrinsicImplementation::Int32Lor
        | IntrinsicImplementation::Int32Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int32Land => "Int32.land",
                IntrinsicImplementation::Int32Lor => "Int32.lor",
                _ => "Int32.xor",
            };
            let left = int32_argument(&args[0], operation, 0)?;
            let right = int32_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int32Land => left & right,
                IntrinsicImplementation::Int32Lor => left | right,
                _ => left ^ right,
            };
            Ok(int32_result(value))
        }
        IntrinsicImplementation::Int32ShiftLeft | IntrinsicImplementation::Int32ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::Int32ShiftLeft;
            let operation: &'static str = if is_left {
                "Int32.shiftLeft"
            } else {
                "Int32.shiftRight"
            };
            let storage = uint32_argument(&args[0], operation, 0)?;
            let amount = int32_argument(&args[1], operation, 1)?;
            let amount = ((i64::from(amount) % 32) + 32) % 32;
            let value = if is_left {
                ((u64::from(storage)) << amount) as u32
            } else {
                ((storage as i32) >> amount) as u32
            };
            Ok(int32_result(value as i32))
        }
        IntrinsicImplementation::Int32Complement
        | IntrinsicImplementation::Int32Neg
        | IntrinsicImplementation::Int32Abs => {
            expect_arity(row, args, 1)?;
            let storage = uint32_argument(
                &args[0],
                match implementation {
                    IntrinsicImplementation::Int32Complement => "Int32.complement",
                    IntrinsicImplementation::Int32Neg => "Int32.neg",
                    _ => "Int32.abs",
                },
                0,
            )?;
            let signed = storage as i32;
            let value = match implementation {
                IntrinsicImplementation::Int32Complement => !signed,
                IntrinsicImplementation::Int32Neg => signed.wrapping_neg(),
                _ => signed.checked_abs().unwrap_or(signed),
            };
            Ok(int32_result(value))
        }
        IntrinsicImplementation::Int32DecEq
        | IntrinsicImplementation::Int32DecLe
        | IntrinsicImplementation::Int32DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int32DecEq => "Int32.decEq",
                IntrinsicImplementation::Int32DecLe => "Int32.decLe",
                _ => "Int32.decLt",
            };
            let left = int32_argument(&args[0], operation, 0)?;
            let right = int32_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::Int32DecEq => left == right,
                IntrinsicImplementation::Int32DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::Int32OfNat => {
            expect_arity(row, args, 1)?;
            let low = with_int_view(&args[0], "Int32.ofNat", 0, |view| {
                let limbs = view.magnitude.limbs_le();
                let low_word = limbs.first().copied().unwrap_or(0) as u32;
                if view.negative {
                    (!low_word).wrapping_add(1)
                } else {
                    low_word
                }
            })?;
            Ok(int32_result(low as i32))
        }
        IntrinsicImplementation::Int32ToInt => {
            expect_arity(row, args, 1)?;
            let value = int32_argument(&args[0], "Int32.toInt", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_int(i64::from(value))))
        }
        IntrinsicImplementation::Int32ToWidth => {
            expect_arity(row, args, 1)?;
            let value = int32_argument(&args[0], "Int32.toInt64", 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_int(i64::from(value))))
        }
        IntrinsicImplementation::Int64Add
        | IntrinsicImplementation::Int64Sub
        | IntrinsicImplementation::Int64Mul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int64Add => "Int64.add",
                IntrinsicImplementation::Int64Sub => "Int64.sub",
                _ => "Int64.mul",
            };
            let left = int64_argument(&args[0], operation, 0)?;
            let right = int64_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int64Add => left.wrapping_add(right),
                IntrinsicImplementation::Int64Sub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(int64_result(value))
        }
        IntrinsicImplementation::Int64Div | IntrinsicImplementation::Int64Mod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::Int64Div;
            let operation: &'static str = if is_div { "Int64.div" } else { "Int64.mod" };
            let dividend = int64_argument(&args[0], operation, 0)?;
            let divisor = int64_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0i64 } else { dividend }
            } else {
                let widened = i128::from(dividend) / i128::from(divisor);
                let remainder = i128::from(dividend) % i128::from(divisor);
                (if is_div { widened } else { remainder }) as i64
            };
            Ok(int64_result(value))
        }
        IntrinsicImplementation::Int64Land
        | IntrinsicImplementation::Int64Lor
        | IntrinsicImplementation::Int64Xor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int64Land => "Int64.land",
                IntrinsicImplementation::Int64Lor => "Int64.lor",
                _ => "Int64.xor",
            };
            let left = int64_argument(&args[0], operation, 0)?;
            let right = int64_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::Int64Land => left & right,
                IntrinsicImplementation::Int64Lor => left | right,
                _ => left ^ right,
            };
            Ok(int64_result(value))
        }
        IntrinsicImplementation::Int64ShiftLeft | IntrinsicImplementation::Int64ShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::Int64ShiftLeft;
            let operation: &'static str = if is_left {
                "Int64.shiftLeft"
            } else {
                "Int64.shiftRight"
            };
            let storage = uint64_argument(&args[0], operation, 0)?;
            let amount = int64_argument(&args[1], operation, 1)?;
            let amount = (((amount % 64) + 64) % 64) as u32;
            let value = if is_left {
                storage.wrapping_shl(amount)
            } else {
                ((storage as i64) >> amount) as u64
            };
            Ok(int64_result(value as i64))
        }
        IntrinsicImplementation::Int64Complement
        | IntrinsicImplementation::Int64Neg
        | IntrinsicImplementation::Int64Abs => {
            expect_arity(row, args, 1)?;
            let storage = uint64_argument(
                &args[0],
                match implementation {
                    IntrinsicImplementation::Int64Complement => "Int64.complement",
                    IntrinsicImplementation::Int64Neg => "Int64.neg",
                    _ => "Int64.abs",
                },
                0,
            )?;
            let signed = storage as i64;
            let value = match implementation {
                IntrinsicImplementation::Int64Complement => !signed,
                IntrinsicImplementation::Int64Neg => signed.wrapping_neg(),
                _ => signed.checked_abs().unwrap_or(signed),
            };
            Ok(int64_result(value))
        }
        IntrinsicImplementation::Int64DecEq
        | IntrinsicImplementation::Int64DecLe
        | IntrinsicImplementation::Int64DecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::Int64DecEq => "Int64.decEq",
                IntrinsicImplementation::Int64DecLe => "Int64.decLe",
                _ => "Int64.decLt",
            };
            let left = int64_argument(&args[0], operation, 0)?;
            let right = int64_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::Int64DecEq => left == right,
                IntrinsicImplementation::Int64DecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::Int64OfNat => {
            expect_arity(row, args, 1)?;
            let low = with_int_view(&args[0], "Int64.ofNat", 0, |view| {
                let limbs = view.magnitude.limbs_le();
                let low_word = limbs.first().copied().unwrap_or(0);
                if view.negative {
                    (!low_word).wrapping_add(1)
                } else {
                    low_word
                }
            })?;
            Ok(int64_result(low as i64))
        }
        IntrinsicImplementation::Int64ToInt => {
            expect_arity(row, args, 1)?;
            let value = int64_argument(&args[0], "Int64.toInt", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_int(value)))
        }
        IntrinsicImplementation::Int64ToWidth => {
            expect_arity(row, args, 1)?;
            let value = int64_argument(&args[0], "Int64.toISize", 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_int(value)))
        }
        IntrinsicImplementation::ISizeAdd
        | IntrinsicImplementation::ISizeSub
        | IntrinsicImplementation::ISizeMul => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::ISizeAdd => "ISize.add",
                IntrinsicImplementation::ISizeSub => "ISize.sub",
                _ => "ISize.mul",
            };
            let left = isize_argument(&args[0], operation, 0)?;
            let right = isize_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::ISizeAdd => left.wrapping_add(right),
                IntrinsicImplementation::ISizeSub => left.wrapping_sub(right),
                _ => left.wrapping_mul(right),
            };
            Ok(isize_result(value))
        }
        IntrinsicImplementation::ISizeDiv | IntrinsicImplementation::ISizeMod => {
            expect_arity(row, args, 2)?;
            let is_div = implementation == IntrinsicImplementation::ISizeDiv;
            let operation: &'static str = if is_div { "ISize.div" } else { "ISize.mod" };
            let dividend = isize_argument(&args[0], operation, 0)?;
            let divisor = isize_argument(&args[1], operation, 1)?;
            let value = if divisor == 0 {
                if is_div { 0isize } else { dividend }
            } else {
                let widened = (dividend as i128) / (divisor as i128);
                let remainder = (dividend as i128) % (divisor as i128);
                (if is_div { widened } else { remainder }) as isize
            };
            Ok(isize_result(value))
        }
        IntrinsicImplementation::ISizeLand
        | IntrinsicImplementation::ISizeLor
        | IntrinsicImplementation::ISizeXor => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::ISizeLand => "ISize.land",
                IntrinsicImplementation::ISizeLor => "ISize.lor",
                _ => "ISize.xor",
            };
            let left = isize_argument(&args[0], operation, 0)?;
            let right = isize_argument(&args[1], operation, 1)?;
            let value = match implementation {
                IntrinsicImplementation::ISizeLand => left & right,
                IntrinsicImplementation::ISizeLor => left | right,
                _ => left ^ right,
            };
            Ok(isize_result(value))
        }
        IntrinsicImplementation::ISizeShiftLeft | IntrinsicImplementation::ISizeShiftRight => {
            expect_arity(row, args, 2)?;
            let is_left = implementation == IntrinsicImplementation::ISizeShiftLeft;
            let operation: &'static str = if is_left {
                "ISize.shiftLeft"
            } else {
                "ISize.shiftRight"
            };
            let storage = usize_argument(&args[0], operation, 0)?;
            let amount = isize_argument(&args[1], operation, 1)?;
            let num_bits = (std::mem::size_of::<isize>() * 8) as isize;
            let amount = (((amount % num_bits) + num_bits) % num_bits) as u32;
            let value = if is_left {
                storage.wrapping_shl(amount)
            } else {
                ((storage as isize) >> amount) as usize
            };
            Ok(isize_result(value as isize))
        }
        IntrinsicImplementation::ISizeComplement
        | IntrinsicImplementation::ISizeNeg
        | IntrinsicImplementation::ISizeAbs => {
            expect_arity(row, args, 1)?;
            let storage = usize_argument(
                &args[0],
                match implementation {
                    IntrinsicImplementation::ISizeComplement => "ISize.complement",
                    IntrinsicImplementation::ISizeNeg => "ISize.neg",
                    _ => "ISize.abs",
                },
                0,
            )?;
            let signed = storage as isize;
            let value = match implementation {
                IntrinsicImplementation::ISizeComplement => !signed,
                IntrinsicImplementation::ISizeNeg => signed.wrapping_neg(),
                _ => signed.checked_abs().unwrap_or(signed),
            };
            Ok(isize_result(value))
        }
        IntrinsicImplementation::ISizeDecEq
        | IntrinsicImplementation::ISizeDecLe
        | IntrinsicImplementation::ISizeDecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::ISizeDecEq => "ISize.decEq",
                IntrinsicImplementation::ISizeDecLe => "ISize.decLe",
                _ => "ISize.decLt",
            };
            let left = isize_argument(&args[0], operation, 0)?;
            let right = isize_argument(&args[1], operation, 1)?;
            let ordering = match implementation {
                IntrinsicImplementation::ISizeDecEq => left == right,
                IntrinsicImplementation::ISizeDecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        IntrinsicImplementation::ISizeOfNat => {
            expect_arity(row, args, 1)?;
            let low = with_int_view(&args[0], "ISize.ofNat", 0, |view| {
                let limbs = view.magnitude.limbs_le();
                let low_word = limbs.first().copied().unwrap_or(0) as usize;
                if view.negative {
                    (!low_word).wrapping_add(1)
                } else {
                    low_word
                }
            })?;
            Ok(isize_result(low as isize))
        }
        IntrinsicImplementation::ISizeToInt => {
            expect_arity(row, args, 1)?;
            let value = isize_argument(&args[0], "ISize.toInt", 0)?;
            Ok(IntrinsicResult::owned(Obj::mk_int(value as i64)))
        }
        IntrinsicImplementation::ISizeToWidth => {
            expect_arity(row, args, 1)?;
            let value = isize_argument(&args[0], "ISize.toInt64", 0)?;
            Ok(IntrinsicResult::scalar(Obj::mk_int(value as i64)))
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
        IntrinsicImplementation::NatDecEq
        | IntrinsicImplementation::NatDecLe
        | IntrinsicImplementation::NatDecLt => {
            expect_arity(row, args, 2)?;
            let operation: &'static str = match implementation {
                IntrinsicImplementation::NatDecEq => "Nat.decEq",
                IntrinsicImplementation::NatDecLe => "Nat.decLe",
                _ => "Nat.decLt",
            };
            let (left, right) = with_nat_views(&args[0], &args[1], operation, |left, right| {
                (left.to_owned(), right.to_owned())
            })?;
            let ordering = match implementation {
                IntrinsicImplementation::NatDecEq => left == right,
                IntrinsicImplementation::NatDecLe => left <= right,
                _ => left < right,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(ordering))))
        }
        // ByteArray rows. The pin mutates in place when its refcount shows a
        // sole owner and copies otherwise; that optimization is invisible to
        // pure value semantics, so every handler here builds a fresh object —
        // the same copy-always discipline as Array.push above.
        IntrinsicImplementation::ByteArraySize => {
            expect_arity(row, args, 1)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.size", 0)?;
            if bytes.len() > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "ByteArray.size",
                }
                .into());
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(bytes.len())))
        }
        IntrinsicImplementation::ByteArrayUGet => {
            expect_arity(row, args, 2)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.uget", 0)?;
            let index = nat_as_usize(&args[1], "ByteArray.uget", 1)?.ok_or(
                VmRefusal::ArrayIndexOutOfBounds {
                    index: usize::MAX,
                    size: bytes.len(),
                },
            )?;
            if index >= bytes.len() {
                return Err(VmRefusal::ArrayIndexOutOfBounds {
                    index,
                    size: bytes.len(),
                }
                .into());
            }
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                bytes[index],
            ))))
        }
        IntrinsicImplementation::ByteArrayGet => {
            expect_arity(row, args, 2)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.get", 0)?;
            // The pin answers 0 for any out-of-bounds index — including a
            // non-scalar Nat, which cannot name a valid byte here.
            let byte = match nat_as_usize(&args[1], "ByteArray.get", 1)? {
                Some(index) if index < bytes.len() => bytes[index],
                _ => 0,
            };
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(byte))))
        }
        IntrinsicImplementation::ByteArraySet => {
            expect_arity(row, args, 3)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.set", 0)?;
            let index = nat_as_usize(&args[1], "ByteArray.set", 1)?.ok_or(
                VmRefusal::ArrayIndexOutOfBounds {
                    index: usize::MAX,
                    size: bytes.len(),
                },
            )?;
            let value = byte_argument(&args[2], "ByteArray.set", 2)?;
            // The pin returns the array UNCHANGED for an out-of-range set.
            if index < bytes.len() {
                let mut updated = bytes;
                updated[index] = value;
                Ok(IntrinsicResult::owned(mk_byte_array(&updated)))
            } else {
                Ok(IntrinsicResult::owned(args[0].clone_ref()))
            }
        }
        IntrinsicImplementation::ByteArrayUset => {
            expect_arity(row, args, 3)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.uset", 0)?;
            let index = nat_as_usize(&args[1], "ByteArray.uset", 1)?.ok_or(
                VmRefusal::ArrayIndexOutOfBounds {
                    index: usize::MAX,
                    size: bytes.len(),
                },
            )?;
            if index >= bytes.len() {
                return Err(VmRefusal::ArrayIndexOutOfBounds {
                    index,
                    size: bytes.len(),
                }
                .into());
            }
            let value = byte_argument(&args[2], "ByteArray.uset", 2)?;
            let mut updated = bytes;
            updated[index] = value;
            Ok(IntrinsicResult::raw_object(mk_byte_array(&updated)))
        }
        IntrinsicImplementation::ByteArrayPush => {
            expect_arity(row, args, 2)?;
            let mut bytes = byte_array_bytes(&args[0], "ByteArray.push", 0)?;
            bytes.push(byte_argument(&args[1], "ByteArray.push", 1)?);
            Ok(IntrinsicResult::owned(mk_byte_array(&bytes)))
        }
        IntrinsicImplementation::ByteArrayMk => {
            expect_arity(row, args, 1)?;
            let (size, _) = array_value(&args[0], "ByteArray.mk", 0)?;
            let mut bytes = Vec::with_capacity(size);
            for index in 0..size {
                let element = args[0].array_child(index);
                bytes.push(byte_argument(&element, "ByteArray.mk", 0)?);
            }
            Ok(IntrinsicResult::owned(mk_byte_array(&bytes)))
        }
        IntrinsicImplementation::ByteArrayData => {
            expect_arity(row, args, 1)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.data", 0)?;
            let items: Vec<Obj> = bytes
                .iter()
                .map(|byte| Obj::mk_nat(usize::from(*byte)))
                .collect();
            Ok(IntrinsicResult::owned(Obj::mk_array(items)))
        }
        IntrinsicImplementation::ByteArrayEmptyWithCapacity => {
            expect_arity(row, args, 1)?;
            // Capacity is an allocation fact; the empty value is canonical.
            with_nat_view(&args[0], "ByteArray.emptyWithCapacity", 0, |_| ())?;
            Ok(IntrinsicResult::owned(mk_byte_array(&[])))
        }
        IntrinsicImplementation::ByteArrayBeq | IntrinsicImplementation::ByteArrayDecEq => {
            expect_arity(row, args, 2)?;
            let left = byte_array_bytes(&args[0], "ByteArray.beq", 0)?;
            let right = byte_array_bytes(&args[1], "ByteArray.beq", 1)?;
            let equal = left == right;
            Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(equal))))
        }
        IntrinsicImplementation::ByteArrayHash => {
            expect_arity(row, args, 1)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.hash", 0)?;
            // `hash_str(size, ptr, seed=11)` at the pin is MurmurHash64A. The
            // census declares a scalar result, so hashes beyond the tagged
            // ceiling are a typed non-answer until mpz-carrying result
            // contracts exist for this row.
            let hash_value = fln_core::lean_hash::murmur_hash_64a(&bytes, 11);
            if hash_value > (usize::MAX >> 1) as u64 {
                return Err(VmRefusal::NatOverflow {
                    operation: "ByteArray.hash",
                }
                .into());
            }
            Ok(IntrinsicResult::scalar(Obj::mk_nat(hash_value as usize)))
        }
        IntrinsicImplementation::ByteArrayCopySlice => {
            expect_arity(row, args, 6)?;
            let source = byte_array_bytes(&args[0], "ByteArray.copySlice", 0)?;
            let src_off = nat_as_usize(&args[1], "ByteArray.copySlice", 1)?.unwrap_or(usize::MAX);
            let dest = byte_array_bytes(&args[2], "ByteArray.copySlice", 2)?;
            let dest_off = nat_as_usize(&args[3], "ByteArray.copySlice", 3)?.unwrap_or(usize::MAX);
            let len = nat_as_usize(&args[4], "ByteArray.copySlice", 4)?.unwrap_or(usize::MAX);
            // `exact` only shapes the C capacity policy; values are identical.
            bool_value(&args[5], "ByteArray.copySlice", 5)?;
            Ok(IntrinsicResult::owned(mk_byte_array(&copy_slice_bytes(
                &source, src_off, &dest, dest_off, len,
            ))))
        }
        IntrinsicImplementation::ByteArrayValidateUtf8 => {
            expect_arity(row, args, 1)?;
            let bytes = byte_array_bytes(&args[0], "ByteArray.validateUTF8", 0)?;
            let valid = validate_utf8_bytes(&bytes);
            Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(valid))))
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
        | IntrinsicImplementation::NatDecEq
        | IntrinsicImplementation::NatDecLe
        | IntrinsicImplementation::NatDecLt
        | IntrinsicImplementation::NatDivExact
        | IntrinsicImplementation::NatModCore
        | IntrinsicImplementation::IntAdd
        | IntrinsicImplementation::IntSub
        | IntrinsicImplementation::IntMul
        | IntrinsicImplementation::IntNeg
        | IntrinsicImplementation::IntNegSucc
        | IntrinsicImplementation::IntOfNat
        | IntrinsicImplementation::IntNatAbs
        | IntrinsicImplementation::IntDecEq
        | IntrinsicImplementation::IntDecLe
        | IntrinsicImplementation::IntDecLt
        | IntrinsicImplementation::IntDecNonneg
        | IntrinsicImplementation::IntEDiv
        | IntrinsicImplementation::IntEMod
        | IntrinsicImplementation::IntTDiv
        | IntrinsicImplementation::IntTMod
        | IntrinsicImplementation::IntDivExact
        | IntrinsicImplementation::UInt8Add
        | IntrinsicImplementation::UInt8Sub
        | IntrinsicImplementation::UInt8Mul
        | IntrinsicImplementation::UInt8Div
        | IntrinsicImplementation::UInt8Mod
        | IntrinsicImplementation::UInt8Land
        | IntrinsicImplementation::UInt8Lor
        | IntrinsicImplementation::UInt8Xor
        | IntrinsicImplementation::UInt8ShiftLeft
        | IntrinsicImplementation::UInt8ShiftRight
        | IntrinsicImplementation::UInt8Complement
        | IntrinsicImplementation::UInt8Neg
        | IntrinsicImplementation::UInt8Log2
        | IntrinsicImplementation::UInt8DecEq
        | IntrinsicImplementation::UInt8DecLe
        | IntrinsicImplementation::UInt8DecLt
        | IntrinsicImplementation::UInt8OfNat
        | IntrinsicImplementation::UInt8ToNat
        | IntrinsicImplementation::UInt8ToUInt16
        | IntrinsicImplementation::UInt8ToUInt32
        | IntrinsicImplementation::UInt8ToUInt64
        | IntrinsicImplementation::UInt8ToUSize
        | IntrinsicImplementation::UInt16Add
        | IntrinsicImplementation::UInt16Sub
        | IntrinsicImplementation::UInt16Mul
        | IntrinsicImplementation::UInt16Div
        | IntrinsicImplementation::UInt16Mod
        | IntrinsicImplementation::UInt16Land
        | IntrinsicImplementation::UInt16Lor
        | IntrinsicImplementation::UInt16Xor
        | IntrinsicImplementation::UInt16ShiftLeft
        | IntrinsicImplementation::UInt16ShiftRight
        | IntrinsicImplementation::UInt16Complement
        | IntrinsicImplementation::UInt16Neg
        | IntrinsicImplementation::UInt16Log2
        | IntrinsicImplementation::UInt16DecEq
        | IntrinsicImplementation::UInt16DecLe
        | IntrinsicImplementation::UInt16DecLt
        | IntrinsicImplementation::UInt16OfNat
        | IntrinsicImplementation::UInt16ToNat
        | IntrinsicImplementation::UInt16ToUInt8
        | IntrinsicImplementation::UInt16ToUInt32
        | IntrinsicImplementation::UInt16ToUInt64
        | IntrinsicImplementation::UInt16ToUSize
        | IntrinsicImplementation::UInt32Add
        | IntrinsicImplementation::UInt32Sub
        | IntrinsicImplementation::UInt32Mul
        | IntrinsicImplementation::UInt32Div
        | IntrinsicImplementation::UInt32Mod
        | IntrinsicImplementation::UInt32Land
        | IntrinsicImplementation::UInt32Lor
        | IntrinsicImplementation::UInt32Xor
        | IntrinsicImplementation::UInt32ShiftLeft
        | IntrinsicImplementation::UInt32ShiftRight
        | IntrinsicImplementation::UInt32Complement
        | IntrinsicImplementation::UInt32Neg
        | IntrinsicImplementation::UInt32Log2
        | IntrinsicImplementation::UInt32DecEq
        | IntrinsicImplementation::UInt32DecLe
        | IntrinsicImplementation::UInt32DecLt
        | IntrinsicImplementation::UInt32OfNat
        | IntrinsicImplementation::UInt32ToNat
        | IntrinsicImplementation::UInt32ToUInt8
        | IntrinsicImplementation::UInt32ToUInt16
        | IntrinsicImplementation::UInt32ToUInt64
        | IntrinsicImplementation::UInt32ToUSize
        | IntrinsicImplementation::UInt64Add
        | IntrinsicImplementation::UInt64Sub
        | IntrinsicImplementation::UInt64Mul
        | IntrinsicImplementation::UInt64Div
        | IntrinsicImplementation::UInt64Mod
        | IntrinsicImplementation::UInt64Land
        | IntrinsicImplementation::UInt64Lor
        | IntrinsicImplementation::UInt64Xor
        | IntrinsicImplementation::UInt64ShiftLeft
        | IntrinsicImplementation::UInt64ShiftRight
        | IntrinsicImplementation::UInt64Complement
        | IntrinsicImplementation::UInt64Neg
        | IntrinsicImplementation::UInt64Log2
        | IntrinsicImplementation::UInt64DecEq
        | IntrinsicImplementation::UInt64DecLe
        | IntrinsicImplementation::UInt64DecLt
        | IntrinsicImplementation::UInt64OfNat
        | IntrinsicImplementation::UInt64ToNat
        | IntrinsicImplementation::UInt64ToUInt8
        | IntrinsicImplementation::UInt64ToUInt16
        | IntrinsicImplementation::UInt64ToUInt32
        | IntrinsicImplementation::UInt64ToUSize
        | IntrinsicImplementation::UInt64MixHash
        | IntrinsicImplementation::USizeAdd
        | IntrinsicImplementation::USizeSub
        | IntrinsicImplementation::USizeMul
        | IntrinsicImplementation::USizeDiv
        | IntrinsicImplementation::USizeMod
        | IntrinsicImplementation::USizeLand
        | IntrinsicImplementation::USizeLor
        | IntrinsicImplementation::USizeXor
        | IntrinsicImplementation::USizeShiftLeft
        | IntrinsicImplementation::USizeShiftRight
        | IntrinsicImplementation::USizeComplement
        | IntrinsicImplementation::USizeNeg
        | IntrinsicImplementation::USizeLog2
        | IntrinsicImplementation::USizeDecEq
        | IntrinsicImplementation::USizeDecLe
        | IntrinsicImplementation::USizeDecLt
        | IntrinsicImplementation::USizeOfNat
        | IntrinsicImplementation::USizeToNat
        | IntrinsicImplementation::USizeToUInt8
        | IntrinsicImplementation::USizeToUInt16
        | IntrinsicImplementation::USizeToUInt32
        | IntrinsicImplementation::USizeToUInt64
        | IntrinsicImplementation::USizeRepr
        | IntrinsicImplementation::Int8Add
        | IntrinsicImplementation::Int8Sub
        | IntrinsicImplementation::Int8Mul
        | IntrinsicImplementation::Int8Div
        | IntrinsicImplementation::Int8Mod
        | IntrinsicImplementation::Int8Land
        | IntrinsicImplementation::Int8Lor
        | IntrinsicImplementation::Int8Xor
        | IntrinsicImplementation::Int8ShiftLeft
        | IntrinsicImplementation::Int8ShiftRight
        | IntrinsicImplementation::Int8Complement
        | IntrinsicImplementation::Int8Neg
        | IntrinsicImplementation::Int8Abs
        | IntrinsicImplementation::Int8DecEq
        | IntrinsicImplementation::Int8DecLe
        | IntrinsicImplementation::Int8DecLt
        | IntrinsicImplementation::Int8OfNat
        | IntrinsicImplementation::Int8ToInt
        | IntrinsicImplementation::Int8ToWidth
        | IntrinsicImplementation::Int16Add
        | IntrinsicImplementation::Int16Sub
        | IntrinsicImplementation::Int16Mul
        | IntrinsicImplementation::Int16Div
        | IntrinsicImplementation::Int16Mod
        | IntrinsicImplementation::Int16Land
        | IntrinsicImplementation::Int16Lor
        | IntrinsicImplementation::Int16Xor
        | IntrinsicImplementation::Int16ShiftLeft
        | IntrinsicImplementation::Int16ShiftRight
        | IntrinsicImplementation::Int16Complement
        | IntrinsicImplementation::Int16Neg
        | IntrinsicImplementation::Int16Abs
        | IntrinsicImplementation::Int16DecEq
        | IntrinsicImplementation::Int16DecLe
        | IntrinsicImplementation::Int16DecLt
        | IntrinsicImplementation::Int16OfNat
        | IntrinsicImplementation::Int16ToInt
        | IntrinsicImplementation::Int16ToWidth
        | IntrinsicImplementation::Int32Add
        | IntrinsicImplementation::Int32Sub
        | IntrinsicImplementation::Int32Mul
        | IntrinsicImplementation::Int32Div
        | IntrinsicImplementation::Int32Mod
        | IntrinsicImplementation::Int32Land
        | IntrinsicImplementation::Int32Lor
        | IntrinsicImplementation::Int32Xor
        | IntrinsicImplementation::Int32ShiftLeft
        | IntrinsicImplementation::Int32ShiftRight
        | IntrinsicImplementation::Int32Complement
        | IntrinsicImplementation::Int32Neg
        | IntrinsicImplementation::Int32Abs
        | IntrinsicImplementation::Int32DecEq
        | IntrinsicImplementation::Int32DecLe
        | IntrinsicImplementation::Int32DecLt
        | IntrinsicImplementation::Int32OfNat
        | IntrinsicImplementation::Int32ToInt
        | IntrinsicImplementation::Int32ToWidth
        | IntrinsicImplementation::Int64Add
        | IntrinsicImplementation::Int64Sub
        | IntrinsicImplementation::Int64Mul
        | IntrinsicImplementation::Int64Div
        | IntrinsicImplementation::Int64Mod
        | IntrinsicImplementation::Int64Land
        | IntrinsicImplementation::Int64Lor
        | IntrinsicImplementation::Int64Xor
        | IntrinsicImplementation::Int64ShiftLeft
        | IntrinsicImplementation::Int64ShiftRight
        | IntrinsicImplementation::Int64Complement
        | IntrinsicImplementation::Int64Neg
        | IntrinsicImplementation::Int64Abs
        | IntrinsicImplementation::Int64DecEq
        | IntrinsicImplementation::Int64DecLe
        | IntrinsicImplementation::Int64DecLt
        | IntrinsicImplementation::Int64OfNat
        | IntrinsicImplementation::Int64ToInt
        | IntrinsicImplementation::Int64ToWidth
        | IntrinsicImplementation::ISizeAdd
        | IntrinsicImplementation::ISizeSub
        | IntrinsicImplementation::ISizeMul
        | IntrinsicImplementation::ISizeDiv
        | IntrinsicImplementation::ISizeMod
        | IntrinsicImplementation::ISizeLand
        | IntrinsicImplementation::ISizeLor
        | IntrinsicImplementation::ISizeXor
        | IntrinsicImplementation::ISizeShiftLeft
        | IntrinsicImplementation::ISizeShiftRight
        | IntrinsicImplementation::ISizeComplement
        | IntrinsicImplementation::ISizeNeg
        | IntrinsicImplementation::ISizeAbs
        | IntrinsicImplementation::ISizeDecEq
        | IntrinsicImplementation::ISizeDecLe
        | IntrinsicImplementation::ISizeDecLt
        | IntrinsicImplementation::ISizeOfNat
        | IntrinsicImplementation::ISizeToInt
        | IntrinsicImplementation::ISizeToWidth
        | IntrinsicImplementation::ByteArrayBeq
        | IntrinsicImplementation::ByteArrayCopySlice
        | IntrinsicImplementation::ByteArrayData
        | IntrinsicImplementation::ByteArrayDecEq
        | IntrinsicImplementation::ByteArrayEmptyWithCapacity
        | IntrinsicImplementation::ByteArrayGet
        | IntrinsicImplementation::ByteArrayHash
        | IntrinsicImplementation::ByteArrayMk
        | IntrinsicImplementation::ByteArrayPush
        | IntrinsicImplementation::ByteArraySet
        | IntrinsicImplementation::ByteArraySize
        | IntrinsicImplementation::ByteArrayUGet
        | IntrinsicImplementation::ByteArrayUset
        | IntrinsicImplementation::ByteArrayValidateUtf8
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

/// A decoded Marrow `Int`: a sign plus its magnitude. The pin stores small
/// values as i32-range scalars — `(int)((unsigned)lean_unbox(a))`,
/// src/include/lean/lean.h:1616 — and everything else as a signed mpz whose
/// `m_size` field carries the sign.
struct IntView<'a> {
    negative: bool,
    magnitude: BigNatView<'a>,
}

fn with_int_view<R>(
    value: &Obj,
    operation: &'static str,
    argument: usize,
    use_view: impl FnOnce(IntView<'_>) -> R,
) -> Result<R, VmRefusal> {
    if value.is_scalar() {
        let signed = i64::from(value.unbox() as u32 as i32);
        let limbs = [signed.unsigned_abs()];
        return Ok(use_view(IntView {
            negative: signed < 0,
            magnitude: BigNatView::from_limbs_le(&limbs),
        }));
    }
    if value_kind(value) != ValueKind::Mpz {
        return Err(type_mismatch(operation, argument, "Int", value));
    }
    let Some((_, size, limbs)) = value.try_mpz_view() else {
        return Err(type_mismatch(operation, argument, "Int", value));
    };
    Ok(use_view(IntView {
        negative: size < 0,
        magnitude: BigNatView::from_limbs_le(limbs),
    }))
}

fn with_int_views<R>(
    left: &Obj,
    right: &Obj,
    operation: &'static str,
    use_views: impl FnOnce(IntView<'_>, IntView<'_>) -> R,
) -> Result<R, VmRefusal> {
    with_int_view(left, operation, 0, |left| {
        with_int_view(right, operation, 1, |right| use_views(left, right))
    })?
}

fn subtract_magnitudes(minuend: IntView<'_>, subtrahend: IntView<'_>) -> (bool, BigNat) {
    if minuend.magnitude.beq(subtrahend.magnitude) {
        (false, BigNat::zero())
    } else if minuend.magnitude.ble(subtrahend.magnitude) {
        (true, subtrahend.magnitude.sub(minuend.magnitude))
    } else {
        (false, minuend.magnitude.sub(subtrahend.magnitude))
    }
}

fn signed_add(left: IntView<'_>, right: IntView<'_>) -> (bool, BigNat) {
    match (left.negative, right.negative) {
        (false, false) => (false, left.magnitude.add(right.magnitude)),
        (true, true) => (true, left.magnitude.add(right.magnitude)),
        (true, false) => subtract_magnitudes(right, left),
        (false, true) => subtract_magnitudes(left, right),
    }
}

fn signed_sub(left: IntView<'_>, right: IntView<'_>) -> (bool, BigNat) {
    match (left.negative, right.negative) {
        (false, false) => subtract_magnitudes(left, right),
        (true, true) => subtract_magnitudes(right, left),
        (true, false) => (true, left.magnitude.add(right.magnitude)),
        (false, true) => (false, left.magnitude.add(right.magnitude)),
    }
}

fn signed_mul(left: IntView<'_>, right: IntView<'_>) -> (bool, BigNat) {
    (
        left.negative != right.negative,
        left.magnitude.mul(right.magnitude),
    )
}

fn cmp_magnitudes(left: BigNatView<'_>, right: BigNatView<'_>) -> std::cmp::Ordering {
    if left.beq(right) {
        std::cmp::Ordering::Equal
    } else if left.ble(right) {
        std::cmp::Ordering::Less
    } else {
        std::cmp::Ordering::Greater
    }
}

fn signed_cmp(left: IntView<'_>, right: IntView<'_>) -> std::cmp::Ordering {
    match (left.negative, right.negative) {
        (false, true) => std::cmp::Ordering::Greater,
        (true, false) => std::cmp::Ordering::Less,
        (false, false) => cmp_magnitudes(left.magnitude, right.magnitude),
        (true, true) => cmp_magnitudes(right.magnitude, left.magnitude),
    }
}

/// Truncated division shares its body across tdiv and divExact; the Euclidean
/// form bumps the quotient when the truncated remainder is negative so the
/// final remainder lands in `0 <= r < |d|` (lean.h:1765-1805).
fn signed_quotient(
    numerator: IntView<'_>,
    denominator: IntView<'_>,
    euclidean: bool,
) -> (bool, BigNat) {
    let truncated = numerator.magnitude.div(denominator.magnitude);
    let remainder = numerator.magnitude.rem(denominator.magnitude);
    let quotient = if euclidean && numerator.negative && !remainder.is_zero() {
        truncated.as_view().add(BigNatView::from_limbs_le(&[1]))
    } else {
        truncated
    };
    let negative = (numerator.negative != denominator.negative) && !quotient.is_zero();
    (negative, quotient)
}

/// The T-rounding remainder keeps the dividend's sign; the E-rounding form
/// normalizes into a nonnegative residue (lean.h:1749-1845).
fn signed_remainder(
    numerator: IntView<'_>,
    denominator: IntView<'_>,
    euclidean: bool,
) -> (bool, BigNat) {
    let truncated = numerator.magnitude.rem(denominator.magnitude);
    if euclidean && numerator.negative && !truncated.is_zero() {
        (false, denominator.magnitude.sub(truncated.as_view()))
    } else {
        (numerator.negative && !truncated.is_zero(), truncated)
    }
}

/// Canonicalize a signed magnitude exactly as the pin re-boxes results:
/// scalar when it fits the i32 plane (lean_int64_to_int), signed mpz
/// otherwise, zero always positive.
fn int_obj(negative: bool, magnitude: &BigNat) -> Obj {
    if magnitude.is_zero() {
        return Obj::mk_int(0);
    }
    if let Some(word) = magnitude.to_u64()
        && let Ok(small) = i32::try_from(word)
    {
        return Obj::mk_int(if negative {
            -i64::from(small)
        } else {
            i64::from(small)
        });
    }
    Obj::mk_mpz(magnitude.limbs_le(), negative)
}

fn finish_int_result(
    negative: bool,
    magnitude: BigNat,
    max_nat_magnitude_bytes: u64,
) -> Result<IntrinsicResult, IntrinsicFailure> {
    ensure_nat_bits(max_nat_magnitude_bytes, u128::from(magnitude.bit_length()))?;
    Ok(IntrinsicResult::owned(int_obj(negative, &magnitude)))
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

fn mk_byte_array(bytes: &[u8]) -> Obj {
    Obj::mk_sarray(1, bytes)
}

/// The bytes of a Marrow `ByteArray`: a scalar array whose element size is
/// exactly one. Any other scalar-array element size is a different type and
/// refuses here rather than aliasing its payload.
fn byte_array_bytes(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<Vec<u8>, VmRefusal> {
    if value_kind(value) != ValueKind::ScalarArray {
        return Err(type_mismatch(operation, argument, "ByteArray", value));
    }
    let Some((elem_size, _, _, data)) = value.try_sarray_view() else {
        return Err(VmRefusal::InvalidByteArrayObject);
    };
    if elem_size != 1 {
        return Err(VmRefusal::InvalidByteArrayObject);
    }
    Ok(data)
}

/// A `UInt8` argument: any Nat that fits one byte. The pin truncates through
/// `uint8_t` parameters; a wider value is a typed range fault here.
fn byte_argument(value: &Obj, operation: &'static str, argument: usize) -> Result<u8, VmRefusal> {
    match nat_as_usize(value, operation, argument)? {
        Some(word) if word <= u8::MAX as usize => Ok(word as u8),
        _ => Err(VmRefusal::NatOverflow { operation }),
    }
}

/// A signed byte argument: the pin stores int8 values in the same scalar
/// word as uint8, with the sign in bit 7 (`(int8_t)a` casts).
fn int8_argument(value: &Obj, operation: &'static str, argument: usize) -> Result<i8, VmRefusal> {
    Ok(byte_argument(value, operation, argument)? as i8)
}

fn uint8_result(value: u8) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(usize::from(value)))
}

fn int8_result(value: i8) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(usize::from(value as u8)))
}

fn uint16_argument(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<u16, VmRefusal> {
    match nat_as_usize(value, operation, argument)? {
        Some(word) if word <= u16::MAX as usize => Ok(word as u16),
        _ => Err(VmRefusal::NatOverflow { operation }),
    }
}

fn int16_argument(value: &Obj, operation: &'static str, argument: usize) -> Result<i16, VmRefusal> {
    Ok(uint16_argument(value, operation, argument)? as i16)
}

fn uint16_result(value: u16) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(usize::from(value)))
}

fn int16_result(value: i16) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(usize::from(value as u16)))
}

fn uint32_argument(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<u32, VmRefusal> {
    match nat_as_usize(value, operation, argument)? {
        Some(word) if word <= u32::MAX as usize => Ok(word as u32),
        _ => Err(VmRefusal::NatOverflow { operation }),
    }
}

fn int32_argument(value: &Obj, operation: &'static str, argument: usize) -> Result<i32, VmRefusal> {
    Ok(uint32_argument(value, operation, argument)? as i32)
}

fn uint32_result(value: u32) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(value as usize))
}

fn int32_result(value: i32) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(value as u32 as usize))
}

fn uint64_argument(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<u64, VmRefusal> {
    if value.is_scalar() {
        return Ok(value.unbox() as u64);
    }
    with_nat_view(value, operation, argument, |view| view.to_u64())?
        .ok_or(VmRefusal::NatOverflow { operation })
}

fn int64_argument(value: &Obj, operation: &'static str, argument: usize) -> Result<i64, VmRefusal> {
    if value.is_scalar() {
        return Ok(value.unbox() as u64 as i64);
    }
    with_nat_view(value, operation, argument, |view| view.to_u64())?
        .map(|u| u as i64)
        .ok_or(VmRefusal::NatOverflow { operation })
}

fn uint64_result(value: u64) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat((value as usize) & (usize::MAX >> 1)))
}

fn int64_result(value: i64) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat((value as usize) & (usize::MAX >> 1)))
}

fn usize_argument(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<usize, VmRefusal> {
    if value.is_scalar() {
        return Ok(value.unbox());
    }
    nat_as_usize(value, operation, argument)?.ok_or(VmRefusal::NatOverflow { operation })
}

fn isize_argument(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<isize, VmRefusal> {
    Ok(usize_argument(value, operation, argument)? as isize)
}

fn usize_result(value: usize) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(value & (usize::MAX >> 1)))
}

fn isize_result(value: isize) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat((value as usize) & (usize::MAX >> 1)))
}
/// Exact port of the pin's `lean_byte_array_copy_slice` value semantics:
/// a source offset past the source returns the destination unchanged; the
/// length clamps to the remaining source; a destination offset past the
/// destination clamps to the destination end (so no gap past the old end is
/// ever reachable); and the result grows to `max(dest_len, dest_off + len)`.
/// The copy-always discipline makes the pin's exclusivity fast path
/// observationally identical.
fn copy_slice_bytes(
    source: &[u8],
    src_off: usize,
    dest: &[u8],
    dest_off: usize,
    len: usize,
) -> Vec<u8> {
    if src_off > source.len() {
        return dest.to_vec();
    }
    let len = len.min(source.len() - src_off);
    let dest_off = dest_off.min(dest.len());
    let new_size = dest.len().max(dest_off + len);
    let mut out = vec![0u8; new_size];
    out[..dest.len()].copy_from_slice(dest);
    out[dest_off..dest_off + len].copy_from_slice(&source[src_off..src_off + len]);
    out
}

/// Exact port of the pin's `validate_utf8`/`validate_utf8_one`
/// (src/runtime/utf8.cpp): full sequence validation with the overlong,
/// surrogate, and range checks the C encodes inline.
fn validate_utf8_bytes(bytes: &[u8]) -> bool {
    let mut position = 0_usize;
    while position < bytes.len() {
        let c = bytes[position];
        if c & 0x80 == 0 {
            position += 1;
            continue;
        }
        let (width, minimum) = if c & 0xe0 == 0xc0 {
            (2usize, 0x80u32)
        } else if c & 0xf0 == 0xe0 {
            (3, 0x800)
        } else if c & 0xf8 == 0xf0 {
            (4, 0x1_0000)
        } else {
            return false;
        };
        if position + width > bytes.len() {
            return false;
        }
        let mut scalar = u32::from(c & (0x7f >> width));
        for continuation in &bytes[position + 1..position + width] {
            if continuation & 0xc0 != 0x80 {
                return false;
            }
            scalar = (scalar << 6) | u32::from(continuation & 0x3f);
        }
        let upper = match width {
            2 => 0x7ff,
            3 => 0xffff,
            _ => 0x10_ffff,
        };
        if scalar < minimum || scalar > upper {
            return false;
        }
        if (0xd800..=0xdfff).contains(&scalar) {
            return false;
        }
        position += width;
    }
    true
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

    #[test]
    fn every_byte_array_and_nat_decidable_row_resolves() {
        let rows = [
            "extern:ByteArray.beq",
            "extern:ByteArray.copySlice",
            "extern:ByteArray.data",
            "extern:ByteArray.decEq",
            "extern:ByteArray.emptyWithCapacity",
            "extern:ByteArray.get",
            "extern:ByteArray.hash",
            "extern:ByteArray.mk",
            "extern:ByteArray.push",
            "extern:ByteArray.set",
            "extern:ByteArray.size",
            "extern:ByteArray.uget",
            "extern:ByteArray.uset",
            "extern:ByteArray.validateUTF8",
            "extern:Nat.decEq",
            "extern:Nat.decLe",
            "extern:Nat.decLt",
        ];
        for row in rows {
            assert_ne!(
                IntrinsicImplementation::for_row(row),
                IntrinsicImplementation::Unsupported,
                "{row} must resolve"
            );
        }
    }

    fn ba(bytes: &[u8]) -> Obj {
        mk_byte_array(bytes)
    }

    fn ba_bytes(result: Result<Obj, VmRefusal>) -> Vec<u8> {
        let object = result.expect("the intrinsic answers");
        byte_array_bytes(&object, "test projection", 0).expect("a byte-array result")
    }

    #[test]
    fn byte_array_construction_and_access_follow_the_pin() {
        let source = invoke(
            "extern:ByteArray.mk",
            &[Obj::mk_array(vec![n(104), n(105), n(255)])],
        );
        assert_eq!(ba_bytes(source), [104, 105, 255]);

        let array = ba(&[104, 105, 255]);
        assert_eq!(
            owned_usize(invoke("extern:ByteArray.size", &[array.clone_ref()])),
            3
        );
        // get answers 0 out of bounds; uget refuses typed.
        assert_eq!(
            owned_usize(invoke("extern:ByteArray.get", &[array.clone_ref(), n(1)])),
            105
        );
        assert_eq!(
            owned_usize(invoke("extern:ByteArray.get", &[array.clone_ref(), n(9)])),
            0
        );
        assert!(matches!(
            invoke("extern:ByteArray.uget", &[array.clone_ref(), n(9)]),
            Err(VmRefusal::ArrayIndexOutOfBounds { index: 9, size: 3 })
        ));
        assert_eq!(
            owned_usize(invoke(
                "extern:ByteArray.get",
                &[array, Obj::mk_mpz(&[u64::from(u32::MAX) + 1], false)]
            )),
            0
        );
    }

    #[test]
    fn byte_array_set_uset_push_copy_slice_port_the_pin() {
        let array = ba(&[104, 105]);
        // set in range replaces; set out of range returns the array unchanged.
        assert_eq!(
            ba_bytes(invoke(
                "extern:ByteArray.set",
                &[array.clone_ref(), n(1), n(98)]
            )),
            [104, 98]
        );
        assert_eq!(
            ba_bytes(invoke(
                "extern:ByteArray.set",
                &[array.clone_ref(), n(9), n(98)]
            )),
            [104, 105]
        );
        assert_eq!(
            ba_bytes(invoke(
                "extern:ByteArray.uset",
                &[array.clone_ref(), n(0), n(42)]
            )),
            [42, 105]
        );
        assert_eq!(
            ba_bytes(invoke(
                "extern:ByteArray.push",
                &[array.clone_ref(), n(255)]
            )),
            [104, 105, 255]
        );

        let destination = ba(&[1, 2]);
        // dest_off past the destination clamps to its end (the pin's rule).
        assert_eq!(
            ba_bytes(invoke(
                "extern:ByteArray.copySlice",
                &[
                    ba(&[9, 9, 9]),
                    n(1),
                    destination.clone_ref(),
                    n(4),
                    n(2),
                    n(0)
                ]
            )),
            [1, 2, 9, 9]
        );
        assert_eq!(
            ba_bytes(invoke(
                "extern:ByteArray.copySlice",
                &[ba(&[7]), n(5), destination, n(0), n(1), n(0)]
            )),
            [1, 2]
        );
    }

    #[test]
    fn byte_array_predicates_hash_and_validate_like_the_pin() {
        assert_eq!(
            owned_usize(invoke("extern:ByteArray.beq", &[ba(&[1, 2]), ba(&[1, 2])])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:ByteArray.decEq", &[ba(&[1]), ba(&[2])])),
            0
        );

        // Most 64-bit hashes exceed the tagged-Nat ceiling and are typed
        // non-answers under this row's scalar contract; find an input whose
        // hash fits, then pin the exact value.
        let mut fitted = None;
        for seed_byte in 0u8..=255 {
            let candidate_input = [seed_byte];
            let candidate = fln_core::lean_hash::murmur_hash_64a(&candidate_input, 11);
            if candidate <= (usize::MAX >> 1) as u64 {
                fitted = Some((candidate_input, candidate));
                break;
            }
        }
        let (input_bytes, expected) = fitted.expect("some byte hashes below the ceiling");
        let hash =
            invoke("extern:ByteArray.hash", &[ba(&input_bytes)]).expect("the fitting hash answers");
        assert_eq!(
            nat_as_usize(&hash, "test projection", 0)
                .expect("well-typed")
                .expect("machine word"),
            expected as usize
        );

        assert_eq!(
            owned_usize(invoke(
                "extern:ByteArray.validateUTF8",
                &[ba("héllo".as_bytes())]
            )),
            1
        );
        // Overlong encoding of 'a' (c0 80) and a surrogate (ed a0 80) fail.
        assert_eq!(
            owned_usize(invoke(
                "extern:ByteArray.validateUTF8",
                &[ba(&[0xc0, 0x80])]
            )),
            0
        );
        assert_eq!(
            owned_usize(invoke(
                "extern:ByteArray.validateUTF8",
                &[ba(&[0xed, 0xa0, 0x80])]
            )),
            0
        );
        assert_eq!(
            ba_bytes(invoke("extern:ByteArray.emptyWithCapacity", &[n(64)])),
            []
        );
    }

    #[test]
    fn nat_decidable_rows_report_bool_scalars() {
        assert_eq!(owned_usize(invoke("extern:Nat.decEq", &[n(5), n(5)])), 1);
        assert_eq!(owned_usize(invoke("extern:Nat.decEq", &[n(5), n(6)])), 0);
        assert_eq!(owned_usize(invoke("extern:Nat.decLe", &[n(5), n(5)])), 1);
        assert_eq!(owned_usize(invoke("extern:Nat.decLe", &[n(6), n(5)])), 0);
        assert_eq!(owned_usize(invoke("extern:Nat.decLt", &[n(5), n(6)])), 1);
        assert_eq!(owned_usize(invoke("extern:Nat.decLt", &[n(5), n(5)])), 0);
        // Arbitrary-precision operands compare by value, not representation.
        let big = Obj::mk_mpz(&[u64::from(u32::MAX) + 1], false);
        assert_eq!(
            owned_usize(invoke("extern:Nat.decEq", &[big.clone_ref(), big])),
            1
        );
    }

    #[test]
    fn nat_div_exact_shares_div_runtime_including_zero_divisor() {
        assert_eq!(
            owned_usize(invoke("extern:Nat.divExact", &[n(100), n(4)])),
            25
        );
        // The pin's div answers 0 for a zero divisor; divExact is `x / y`
        // with only the proof erased, so the runtime contract is identical.
        assert_eq!(owned_usize(invoke("extern:Nat.divExact", &[n(7), n(0)])), 0);
    }

    #[test]
    fn nat_mod_core_matches_mod_with_zero_divisor_identity() {
        assert_eq!(owned_usize(invoke("extern:Nat.modCore", &[n(17), n(5)])), 2);
        // Init/Prelude.lean:2196 — the zero divisor yields the dividend.
        assert_eq!(
            owned_usize(invoke("extern:Nat.modCore", &[n(17), n(0)])),
            17
        );
        assert_eq!(owned_usize(invoke("extern:Nat.modCore", &[n(0), n(3)])), 0);
    }

    #[test]
    fn nat_arith_rows_resolve_and_stay_off_managerless_task_path() {
        for row in ["extern:Nat.divExact", "extern:Nat.modCore"] {
            assert_ne!(
                IntrinsicImplementation::for_row(row),
                IntrinsicImplementation::Unsupported,
                "{row} must resolve"
            );
            assert!(!IntrinsicImplementation::for_row(row).is_managerless_task());
        }
    }
    /// Decode an Int result the way the pin's consumers read it back: scalar
    /// via `(int)((unsigned)lean_unbox(a))`, mpz by sign + magnitude limbs.
    fn int_words(result: Result<Obj, VmRefusal>) -> (bool, Vec<u64>, bool) {
        let object = result.expect("the intrinsic answers");
        if object.is_scalar() {
            let signed = object.unbox() as u32 as i32;
            (signed < 0, vec![signed.unsigned_abs() as u64], true)
        } else {
            let (_, size, limbs) = object.mpz_view();
            (size < 0, limbs.to_vec(), false)
        }
    }

    fn int_i64(result: Result<Obj, VmRefusal>) -> i64 {
        let object = result.expect("the intrinsic answers");
        assert!(object.is_scalar(), "expected a scalar-plane Int");
        i64::from(object.unbox() as u32 as i32)
    }

    fn i(value: i64) -> Obj {
        Obj::mk_int(value)
    }

    #[test]
    fn int_arithmetic_matches_the_pin_scalar_plane() {
        assert_eq!(int_i64(invoke("extern:Int.add", &[i(7), i(-3)])), 4);
        assert_eq!(int_i64(invoke("extern:Int.sub", &[i(7), i(-3)])), 10);
        assert_eq!(int_i64(invoke("extern:Int.mul", &[i(-6), i(-4)])), 24);
        assert_eq!(
            int_i64(invoke("extern:Int.neg", &[i(-2147483647)])),
            2147483647
        );
        // lean_int64_to_int re-boxes past the i32 scalar plane, so boundary
        // arithmetic must land in the mpz plane rather than wrap.
        let overflow = invoke("extern:Int.add", &[i(i64::from(i32::MAX)), i(1)]);
        assert!(!overflow.as_ref().expect("answers").is_scalar());
        let (negative, limbs, _) = int_words(overflow);
        assert!(!negative);
        assert_eq!(
            BigNat::from_limbs_le(limbs),
            BigNat::from_u64(2_147_483_648)
        );
        let underflow = invoke("extern:Int.sub", &[i(i64::from(i32::MIN)), i(1)]);
        let (negative, _, _) = int_words(underflow);
        assert!(negative);
    }

    #[test]
    fn int_big_operands_take_the_exact_mpz_plane() {
        // Operands beyond u64: (2^128 + 1) - 1 == 2^128 must not lose a limb.
        let huge = Obj::mk_mpz(&[1, 0, 1], false);
        let one = Obj::mk_mpz(&[1], false);
        let (negative, limbs, _) = int_words(invoke("extern:Int.sub", &[huge.clone_ref(), one]));
        assert!(!negative);
        assert_eq!(BigNat::from_limbs_le(limbs), BigNat::from_u64(1).shl(128));
        let (negative, limbs, _) =
            int_words(invoke("extern:Int.mul", &[huge, Obj::mk_mpz(&[3], true)]));
        assert!(negative);
        assert_eq!(
            BigNat::from_limbs_le(limbs),
            BigNat::from_u64(3).mul(&BigNat::from_limbs_le(vec![1, 0, 1]))
        );
    }

    #[test]
    fn int_tdiv_tmod_follow_the_pin_truncation_contracts() {
        // Sign matrices quoted verbatim from Init/Data/Int/DivMod/Basic.lean.
        for (x, y, q, r) in [
            (12, 7, 1, 5),
            (12, -7, -1, 5),
            (-12, 7, -1, -5),
            (-12, -7, 1, -5),
        ] {
            assert_eq!(
                int_i64(invoke("extern:Int.tdiv", &[i(x), i(y)])),
                q,
                "tdiv {x} {y}"
            );
            assert_eq!(
                int_i64(invoke("extern:Int.tmod", &[i(x), i(y)])),
                r,
                "tmod {x} {y}"
            );
        }
        // A zero divisor: tdiv answers box(0); tmod returns the dividend.
        assert_eq!(int_i64(invoke("extern:Int.tdiv", &[i(7), i(0)])), 0);
        assert_eq!(int_i64(invoke("extern:Int.tmod", &[i(7), i(0)])), 7);
        assert_eq!(int_i64(invoke("extern:Int.tmod", &[i(-7), i(0)])), -7);
    }
    #[test]
    fn int_ediv_emod_follow_the_pin_euclidean_contracts() {
        for (x, y, q, r) in [(12, -7, -1, 5), (-12, 7, -2, 2), (-12, -7, 2, 2)] {
            assert_eq!(
                int_i64(invoke("extern:Int.ediv", &[i(x), i(y)])),
                q,
                "ediv {x} {y}"
            );
            assert_eq!(
                int_i64(invoke("extern:Int.emod", &[i(x), i(y)])),
                r,
                "emod {x} {y}"
            );
        }
        assert_eq!(int_i64(invoke("extern:Int.ediv", &[i(-12), i(7)])), -2);
        // A zero divisor: ediv answers box(0); emod returns the dividend.
        assert_eq!(int_i64(invoke("extern:Int.ediv", &[i(7), i(0)])), 0);
        assert_eq!(int_i64(invoke("extern:Int.emod", &[i(-7), i(0)])), -7);
    }

    #[test]
    fn int_div_exact_shares_tdiv_runtime() {
        assert_eq!(int_i64(invoke("extern:Int.divExact", &[i(21), i(3)])), 7);
        assert_eq!(int_i64(invoke("extern:Int.divExact", &[i(-21), i(3)])), -7);
        assert_eq!(int_i64(invoke("extern:Int.divExact", &[i(21), i(-3)])), -7);
        assert_eq!(int_i64(invoke("extern:Int.divExact", &[i(0), i(22)])), 0);
        assert_eq!(int_i64(invoke("extern:Int.divExact", &[i(9), i(0)])), 0);
    }

    #[test]
    fn int_neg_succ_of_nat_and_nat_abs_convert_like_the_pin() {
        // negSucc n = -(n + 1): Basic.lean:61.
        assert_eq!(int_i64(invoke("extern:Int.negSucc", &[n(0)])), -1);
        assert_eq!(int_i64(invoke("extern:Int.negSucc", &[n(5)])), -6);
        assert_eq!(int_i64(invoke("extern:Int.ofNat", &[n(5)])), 5);
        assert_eq!(int_i64(invoke("extern:Int.natAbs", &[i(-9)])), 9);
        assert_eq!(owned_usize(invoke("extern:Int.natAbs", &[i(5)])), 5);
        // natAbs of a big negative keeps the exact magnitude in the Nat
        // plane: |-(2^64)| = 2^64, one limb past the scalar Nat ceiling.
        let big_negative = Obj::mk_mpz(&[0, 1], true);
        let absolute = invoke("extern:Int.natAbs", &[big_negative]).expect("answers");
        let (_, size, limbs) = absolute.mpz_view();
        assert_eq!(size, 2);
        assert_eq!(limbs, &[0u64, 1u64]);
        // ofNat over a big Nat re-boxes without changing the magnitude.
        let big_nat = Obj::mk_mpz(&[0, 1], false);
        let widened = invoke("extern:Int.ofNat", &[big_nat]).expect("answers");
        let (negative, limbs, _) = int_words(Ok(widened));
        assert!(!negative);
        assert_eq!(limbs, vec![0u64, 1u64]);
    }

    #[test]
    fn int_decidables_span_both_planes() {
        assert_eq!(owned_usize(invoke("extern:Int.decEq", &[i(-3), i(-3)])), 1);
        assert_eq!(owned_usize(invoke("extern:Int.decEq", &[i(-3), i(3)])), 0);
        assert_eq!(owned_usize(invoke("extern:Int.decLt", &[i(-4), i(-3)])), 1);
        assert_eq!(owned_usize(invoke("extern:Int.decLt", &[i(-3), i(-4)])), 0);
        assert_eq!(owned_usize(invoke("extern:Int.decLe", &[i(-4), i(3)])), 1);
        // Scalar vs mpz representation of the same value compares by value.
        let big_five = Obj::mk_mpz(&[5], false);
        assert_eq!(
            owned_usize(invoke("extern:Int.decEq", &[big_five, i(5)])),
            1
        );
        assert_eq!(owned_usize(invoke("extern:Int.decNonneg", &[i(0)])), 1);
        assert_eq!(owned_usize(invoke("extern:Int.decNonneg", &[i(-1)])), 0);
    }

    #[test]
    fn int_zero_results_stay_positive_and_canonical() {
        let product = invoke("extern:Int.mul", &[i(-5), i(0)]);
        assert_eq!(int_i64(product), 0);
        let difference = invoke("extern:Int.sub", &[i(-2), i(-2)]);
        assert_eq!(int_i64(difference), 0);
        // neg of zero keeps the canonical positive scalar.
        assert_eq!(int_i64(invoke("extern:Int.neg", &[i(0)])), 0);
    }

    #[test]
    fn int_rows_resolve_and_stay_off_managerless_task_path() {
        for row in [
            "extern:Int.add",
            "extern:Int.sub",
            "extern:Int.mul",
            "extern:Int.neg",
            "extern:Int.negSucc",
            "extern:Int.ofNat",
            "extern:Int.natAbs",
            "extern:Int.decEq",
            "extern:Int.decLe",
            "extern:Int.decLt",
            "extern:Int.decNonneg",
            "extern:Int.ediv",
            "extern:Int.emod",
            "extern:Int.tdiv",
            "extern:Int.tmod",
            "extern:Int.divExact",
        ] {
            assert_ne!(
                IntrinsicImplementation::for_row(row),
                IntrinsicImplementation::Unsupported,
                "{row} must resolve"
            );
            assert!(!IntrinsicImplementation::for_row(row).is_managerless_task());
        }
    }

    fn b(value: u8) -> Obj {
        Obj::mk_nat(usize::from(value))
    }

    /// Decode a byte-plane result: the storage word is the unsigned pattern.
    fn byte_word(result: Result<Obj, VmRefusal>) -> u8 {
        let object = result.expect("the intrinsic answers");
        assert!(object.is_scalar(), "expected a scalar-plane result");
        object.unbox() as u8
    }

    fn signed_byte(result: Result<Obj, VmRefusal>) -> i8 {
        i8::from_ne_bytes([byte_word(result)])
    }

    #[test]
    fn uint8_arithmetic_wraps_in_the_storage_plane() {
        assert_eq!(byte_word(invoke("extern:UInt8.add", &[b(255), b(1)])), 0);
        assert_eq!(byte_word(invoke("extern:UInt8.sub", &[b(0), b(1)])), 255);
        assert_eq!(byte_word(invoke("extern:UInt8.mul", &[b(16), b(16)])), 0);
        assert_eq!(byte_word(invoke("extern:UInt8.neg", &[b(0)])), 0);
        assert_eq!(byte_word(invoke("extern:UInt8.neg", &[b(1)])), 255);
        assert_eq!(byte_word(invoke("extern:UInt8.complement", &[b(0)])), 255);
    }

    #[test]
    fn uint8_div_mod_follow_the_pin_zero_contracts() {
        assert_eq!(byte_word(invoke("extern:UInt8.div", &[b(7), b(2)])), 3);
        assert_eq!(byte_word(invoke("extern:UInt8.mod", &[b(7), b(2)])), 1);
        // lean_uint8_div: divisor zero answers 0; mod returns the dividend.
        assert_eq!(byte_word(invoke("extern:UInt8.div", &[b(5), b(0)])), 0);
        assert_eq!(byte_word(invoke("extern:UInt8.mod", &[b(5), b(0)])), 5);
    }

    #[test]
    fn uint8_shifts_reduce_amounts_modulo_eight() {
        // 1 << 8 wraps to 1 through the pin's `a << (b % 8)`.
        assert_eq!(
            byte_word(invoke("extern:UInt8.shiftLeft", &[b(1), b(8)])),
            1
        );
        assert_eq!(
            byte_word(invoke("extern:UInt8.shiftLeft", &[b(1), b(4)])),
            16
        );
        assert_eq!(
            byte_word(invoke("extern:UInt8.shiftRight", &[b(255), b(4)])),
            15
        );
        assert_eq!(byte_word(invoke("extern:UInt8.log2", &[b(255)])), 7);
        assert_eq!(byte_word(invoke("extern:UInt8.log2", &[b(1)])), 0);
        assert_eq!(byte_word(invoke("extern:UInt8.log2", &[b(0)])), 0);
        assert_eq!(
            byte_word(invoke("extern:UInt8.land", &[b(0b1100), b(0b1010)])),
            0b1000
        );
        assert_eq!(
            byte_word(invoke("extern:UInt8.xor", &[b(0xFF), b(0x0F)])),
            0xF0
        );
    }

    #[test]
    fn uint8_of_nat_truncates_big_operands_to_the_low_byte() {
        assert_eq!(byte_word(invoke("extern:UInt8.ofNat", &[n(300)])), 44);
        assert_eq!(byte_word(invoke("extern:UInt8.ofNatLT", &[n(7)])), 7);
        // ofBitVec shares of_nat_mk: truncate the wrapped Nat field.
        assert_eq!(byte_word(invoke("extern:UInt8.ofBitVec", &[n(256 + 9)])), 9);
        // A big mpz truncates to its magnitude's low limb low byte.
        let big = Obj::mk_mpz(&[0x88], false);
        assert_eq!(byte_word(invoke("extern:UInt8.ofNat", &[big])), 0x88);
        assert_eq!(owned_usize(invoke("extern:UInt8.toNat", &[b(200)])), 200);
        // toBitVec shares lean_uint8_to_nat.
        assert_eq!(owned_usize(invoke("extern:UInt8.toBitVec", &[b(200)])), 200);
    }

    #[test]
    fn uint8_widening_and_decidables_match_the_pin() {
        for row in [
            "extern:UInt8.toUInt16",
            "extern:UInt8.toUInt32",
            "extern:UInt8.toUInt64",
            "extern:UInt8.toUSize",
        ] {
            assert_eq!(owned_usize(invoke(row, &[b(250)])), 250, "{row}");
        }
        assert_eq!(owned_usize(invoke("extern:UInt8.decEq", &[b(5), b(5)])), 1);
        assert_eq!(owned_usize(invoke("extern:UInt8.decLt", &[b(6), b(5)])), 0);
        assert_eq!(owned_usize(invoke("extern:UInt8.decLe", &[b(5), b(6)])), 1);
    }

    #[test]
    fn int8_signed_arithmetic_wraps_like_the_unsigned_c() {
        // The C computes add/sub/mul/neg on the unsigned storage byte; the
        // byte-plane constructor `b` is how an Int8 value reaches the VM.
        assert_eq!(
            signed_byte(invoke("extern:Int8.add", &[b(255), b(255)])),
            -2
        );
        assert_eq!(signed_byte(invoke("extern:Int8.sub", &[b(128), b(1)])), 127);
        assert_eq!(signed_byte(invoke("extern:Int8.mul", &[b(240), b(16)])), 0);
        assert_eq!(
            signed_byte(invoke("extern:Int8.mul", &[b(255), b(128)])),
            -128
        );
        assert_eq!(signed_byte(invoke("extern:Int8.neg", &[b(128)])), -128);
        assert_eq!(signed_byte(invoke("extern:Int8.abs", &[b(251)])), 5);
        // abs(INT8_MIN) wraps back to INT8_MIN via the unsigned negate.
        assert_eq!(signed_byte(invoke("extern:Int8.abs", &[b(128)])), -128);
        assert_eq!(signed_byte(invoke("extern:Int8.complement", &[b(0)])), -1);
    }

    #[test]
    fn int8_division_widens_to_avoid_the_int_min_trap() {
        assert_eq!(signed_byte(invoke("extern:Int8.div", &[b(249), b(2)])), -3);
        assert_eq!(signed_byte(invoke("extern:Int8.mod", &[b(249), b(2)])), -1);
        // The pin widens to int16 exactly so this does not trap: 128 wraps.
        assert_eq!(
            signed_byte(invoke("extern:Int8.div", &[b(128), b(255)])),
            -128
        );
        assert_eq!(signed_byte(invoke("extern:Int8.mod", &[b(128), b(255)])), 0);
        // Zero divisors mirror the uint plane: div answers 0, mod identity.
        assert_eq!(signed_byte(invoke("extern:Int8.div", &[b(251), b(0)])), 0);
        assert_eq!(signed_byte(invoke("extern:Int8.mod", &[b(251), b(0)])), -5);
    }

    #[test]
    fn int8_shifts_use_smod_amounts_and_arithmetic_right() {
        // smod 8 keeps negative amounts in [0, 8): ((255 as i8 = -1) % 8 + 8) % 8 == 7.
        assert_eq!(
            signed_byte(invoke("extern:Int8.shiftLeft", &[b(255), b(255)])),
            -128
        );
        assert_eq!(
            signed_byte(invoke("extern:Int8.shiftRight", &[b(240), b(1)])),
            -8
        );
        // shiftLeft stays logical on the storage byte: sign bits spill.
        assert_eq!(
            signed_byte(invoke("extern:Int8.shiftLeft", &[b(64), b(1)])),
            -128
        );
    }

    #[test]
    fn int8_of_nat_of_int_truncate_low_bits_with_sign() {
        assert_eq!(signed_byte(invoke("extern:Int8.ofNat", &[n(129)])), -127);
        // (int8_t)(-257): the low two's-complement byte is 0xFF, i.e. -1.
        assert_eq!(signed_byte(invoke("extern:Int8.ofInt", &[i(-257)])), -1);
        assert_eq!(signed_byte(invoke("extern:Int8.ofInt", &[i(127)])), 127);
        // Big operands fold the sign into the magnitude's low byte: -(257)
        // has low byte 0x01 negated, i.e. 0xFF = -1.
        let big_negative = Obj::mk_mpz(&[257], true);
        assert_eq!(
            signed_byte(invoke("extern:Int8.ofInt", &[big_negative])),
            -1
        );
    }

    #[test]
    fn int8_widening_sign_extends_into_the_int_plane() {
        for row in [
            "extern:Int8.toInt",
            "extern:Int8.toInt16",
            "extern:Int8.toInt32",
            "extern:Int8.toInt64",
            "extern:Int8.toISize",
        ] {
            assert_eq!(int_i64(invoke(row, &[b(254)])), -2, "{row}");
        }
    }

    #[test]
    fn int8_decidables_compare_signed_values() {
        assert_eq!(owned_usize(invoke("extern:Int8.decLt", &[b(255), b(1)])), 1);
        // Unsigned comparison would read 255 < 1 again here: -1 < -128 is
        // false on the signed plane.
        assert_eq!(
            owned_usize(invoke("extern:Int8.decLt", &[b(255), b(128)])),
            0
        );
        assert_eq!(
            owned_usize(invoke("extern:Int8.decLe", &[b(128), b(127)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:Int8.decEq", &[b(128), b(128)])),
            1
        );
    }

    #[test]
    fn every_eight_bit_row_resolves_and_stays_off_managerless_task_path() {
        for row in [
            "extern:UInt8.add",
            "extern:UInt8.sub",
            "extern:UInt8.mul",
            "extern:UInt8.div",
            "extern:UInt8.mod",
            "extern:UInt8.land",
            "extern:UInt8.lor",
            "extern:UInt8.xor",
            "extern:UInt8.shiftLeft",
            "extern:UInt8.shiftRight",
            "extern:UInt8.complement",
            "extern:UInt8.neg",
            "extern:UInt8.log2",
            "extern:UInt8.decEq",
            "extern:UInt8.decLe",
            "extern:UInt8.decLt",
            "extern:UInt8.ofNat",
            "extern:UInt8.ofNatLT",
            "extern:UInt8.ofBitVec",
            "extern:UInt8.toNat",
            "extern:UInt8.toBitVec",
            "extern:UInt8.toUInt16",
            "extern:UInt8.toUInt32",
            "extern:UInt8.toUInt64",
            "extern:UInt8.toUSize",
            "extern:Int8.add",
            "extern:Int8.sub",
            "extern:Int8.mul",
            "extern:Int8.div",
            "extern:Int8.mod",
            "extern:Int8.land",
            "extern:Int8.lor",
            "extern:Int8.xor",
            "extern:Int8.shiftLeft",
            "extern:Int8.shiftRight",
            "extern:Int8.complement",
            "extern:Int8.neg",
            "extern:Int8.abs",
            "extern:Int8.decEq",
            "extern:Int8.decLe",
            "extern:Int8.decLt",
            "extern:Int8.ofNat",
            "extern:Int8.ofInt",
            "extern:Int8.toInt",
            "extern:Int8.toInt16",
            "extern:Int8.toInt32",
            "extern:Int8.toInt64",
            "extern:Int8.toISize",
        ] {
            assert_ne!(
                IntrinsicImplementation::for_row(row),
                IntrinsicImplementation::Unsupported,
                "{row} must resolve"
            );
            assert!(!IntrinsicImplementation::for_row(row).is_managerless_task());
        }
    }

    fn u16_val(result: Result<Obj, VmRefusal>) -> u16 {
        owned_usize(result) as u16
    }
    fn i16_val(result: Result<Obj, VmRefusal>) -> i16 {
        u16_val(result) as i16
    }
    fn u32_val(result: Result<Obj, VmRefusal>) -> u32 {
        owned_usize(result) as u32
    }
    fn i32_val(result: Result<Obj, VmRefusal>) -> i32 {
        u32_val(result) as i32
    }
    fn u64_val(result: Result<Obj, VmRefusal>) -> u64 {
        let obj = result.expect("intrinsic result");
        if obj.is_scalar() {
            obj.unbox() as u64
        } else {
            with_nat_view(&obj, "test", 0, |view| view.to_u64())
                .unwrap()
                .unwrap()
        }
    }
    fn i64_val(result: Result<Obj, VmRefusal>) -> i64 {
        u64_val(result) as i64
    }
    fn usize_val(result: Result<Obj, VmRefusal>) -> usize {
        u64_val(result) as usize
    }
    fn isize_val(result: Result<Obj, VmRefusal>) -> isize {
        usize_val(result) as isize
    }
    fn str_val(result: Result<Obj, VmRefusal>) -> String {
        let obj = result.expect("intrinsic result");
        string_value(&obj, "test", 0).unwrap()
    }

    #[test]
    fn uint16_arithmetic_and_conversions() {
        assert_eq!(u16_val(invoke("extern:UInt16.add", &[n(65535), n(1)])), 0);
        assert_eq!(u16_val(invoke("extern:UInt16.sub", &[n(0), n(1)])), 65535);
        assert_eq!(
            u16_val(invoke("extern:UInt16.mul", &[n(300), n(300)])),
            (300u32 * 300u32) as u16
        );
        assert_eq!(u16_val(invoke("extern:UInt16.div", &[n(100), n(7)])), 14);
        assert_eq!(u16_val(invoke("extern:UInt16.mod", &[n(100), n(7)])), 2);
        assert_eq!(u16_val(invoke("extern:UInt16.div", &[n(100), n(0)])), 0);
        assert_eq!(u16_val(invoke("extern:UInt16.mod", &[n(100), n(0)])), 100);
        assert_eq!(
            u16_val(invoke("extern:UInt16.shiftLeft", &[n(1), n(16)])),
            1
        );
        assert_eq!(
            u16_val(invoke("extern:UInt16.shiftLeft", &[n(1), n(4)])),
            16
        );
        assert_eq!(
            u16_val(invoke("extern:UInt16.shiftRight", &[n(65535), n(4)])),
            4095
        );
        assert_eq!(u16_val(invoke("extern:UInt16.complement", &[n(0)])), 65535);
        assert_eq!(u16_val(invoke("extern:UInt16.neg", &[n(1)])), 65535);
        assert_eq!(u16_val(invoke("extern:UInt16.log2", &[n(65535)])), 15);
        assert_eq!(u16_val(invoke("extern:UInt16.log2", &[n(0)])), 0);
        assert_eq!(
            owned_usize(invoke("extern:UInt16.decEq", &[n(42), n(42)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:UInt16.decLt", &[n(42), n(43)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:UInt16.decLe", &[n(43), n(42)])),
            0
        );
        assert_eq!(
            u16_val(invoke("extern:UInt16.ofNat", &[n(70000)])),
            (70000 % 65536) as u16
        );
        assert_eq!(owned_usize(invoke("extern:UInt16.toNat", &[n(500)])), 500);
        assert_eq!(
            byte_word(invoke("extern:UInt16.toUInt8", &[n(0x1234)])),
            0x34
        );
        assert_eq!(
            u32_val(invoke("extern:UInt16.toUInt32", &[n(0x1234)])),
            0x1234
        );
        assert_eq!(
            u64_val(invoke("extern:UInt16.toUInt64", &[n(0x1234)])),
            0x1234
        );
        assert_eq!(
            usize_val(invoke("extern:UInt16.toUSize", &[n(0x1234)])),
            0x1234
        );
    }

    #[test]
    fn int16_arithmetic_widening_and_conversions() {
        assert_eq!(
            i16_val(invoke("extern:Int16.add", &[n(32767), n(1)])),
            -32768
        );
        assert_eq!(i16_val(invoke("extern:Int16.sub", &[n(0), n(1)])), -1);
        assert_eq!(
            i16_val(invoke("extern:Int16.div", &[n(32768), n(65535)])),
            -32768
        ); // INT16_MIN / -1
        assert_eq!(
            i16_val(invoke("extern:Int16.mod", &[n(32768), n(65535)])),
            0
        );
        assert_eq!(i16_val(invoke("extern:Int16.div", &[n(100), n(0)])), 0);
        assert_eq!(i16_val(invoke("extern:Int16.mod", &[n(100), n(0)])), 100);
        assert_eq!(
            i16_val(invoke("extern:Int16.shiftLeft", &[n(65535), n(65535)])),
            -32768
        );
        assert_eq!(
            i16_val(invoke("extern:Int16.shiftRight", &[n(65535), n(1)])),
            -1
        );
        assert_eq!(i16_val(invoke("extern:Int16.abs", &[n(65535)])), 1);
        assert_eq!(i16_val(invoke("extern:Int16.abs", &[n(32768)])), -32768); // INT16_MIN abs wraps
        assert_eq!(i16_val(invoke("extern:Int16.neg", &[n(32768)])), -32768);
        assert_eq!(i16_val(invoke("extern:Int16.complement", &[n(0)])), -1);
        assert_eq!(
            owned_usize(invoke("extern:Int16.decLt", &[n(65535), n(1)])),
            1
        ); // -1 < 1
        assert_eq!(
            owned_usize(invoke("extern:Int16.decLe", &[n(1), n(65535)])),
            0
        ); // 1 <= -1
        assert_eq!(i16_val(invoke("extern:Int16.ofInt", &[i(-300)])), -300);
        assert_eq!(int_i64(invoke("extern:Int16.toInt", &[n(65535)])), -1);
    }

    #[test]
    fn uint32_arithmetic_and_conversions() {
        assert_eq!(
            u32_val(invoke("extern:UInt32.add", &[n(0xFFFF_FFFF), n(1)])),
            0
        );
        assert_eq!(
            u32_val(invoke("extern:UInt32.sub", &[n(0), n(1)])),
            0xFFFF_FFFF
        );
        assert_eq!(
            u32_val(invoke("extern:UInt32.mul", &[n(0x10000), n(0x10000)])),
            0
        );
        assert_eq!(u32_val(invoke("extern:UInt32.div", &[n(100), n(3)])), 33);
        assert_eq!(u32_val(invoke("extern:UInt32.mod", &[n(100), n(3)])), 1);
        assert_eq!(u32_val(invoke("extern:UInt32.div", &[n(100), n(0)])), 0);
        assert_eq!(u32_val(invoke("extern:UInt32.mod", &[n(100), n(0)])), 100);
        assert_eq!(
            u32_val(invoke("extern:UInt32.shiftLeft", &[n(1), n(32)])),
            1
        );
        assert_eq!(
            u32_val(invoke("extern:UInt32.shiftLeft", &[n(1), n(8)])),
            256
        );
        assert_eq!(
            u32_val(invoke("extern:UInt32.shiftRight", &[n(0xFFFF_FFFF), n(8)])),
            0x00FF_FFFF
        );
        assert_eq!(
            u32_val(invoke("extern:UInt32.complement", &[n(0)])),
            0xFFFF_FFFF
        );
        assert_eq!(u32_val(invoke("extern:UInt32.neg", &[n(1)])), 0xFFFF_FFFF);
        assert_eq!(u32_val(invoke("extern:UInt32.log2", &[n(0xFFFF_FFFF)])), 31);
        assert_eq!(u32_val(invoke("extern:UInt32.log2", &[n(0)])), 0);
        assert_eq!(
            owned_usize(invoke("extern:UInt32.decEq", &[n(12345), n(12345)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:UInt32.decLt", &[n(12345), n(12346)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:UInt32.decLe", &[n(12346), n(12345)])),
            0
        );
        assert_eq!(
            u32_val(invoke("extern:UInt32.ofNat", &[n(0x1_0000_0005)])),
            5
        );
        assert_eq!(owned_usize(invoke("extern:UInt32.toNat", &[n(777)])), 777);
        assert_eq!(
            byte_word(invoke("extern:UInt32.toUInt8", &[n(0x1234_5678)])),
            0x78
        );
        assert_eq!(
            u16_val(invoke("extern:UInt32.toUInt16", &[n(0x1234_5678)])),
            0x5678
        );
        assert_eq!(
            u64_val(invoke("extern:UInt32.toUInt64", &[n(0x1234_5678)])),
            0x1234_5678
        );
        assert_eq!(
            usize_val(invoke("extern:UInt32.toUSize", &[n(0x1234_5678)])),
            0x1234_5678
        );
    }

    #[test]
    fn int32_arithmetic_widening_and_conversions() {
        assert_eq!(
            i32_val(invoke("extern:Int32.add", &[n(0x7FFF_FFFF), n(1)])),
            i32::MIN
        );
        assert_eq!(i32_val(invoke("extern:Int32.sub", &[n(0), n(1)])), -1);
        assert_eq!(
            i32_val(invoke(
                "extern:Int32.div",
                &[n(0x8000_0000), n(0xFFFF_FFFF)]
            )),
            i32::MIN
        ); // INT32_MIN / -1
        assert_eq!(
            i32_val(invoke(
                "extern:Int32.mod",
                &[n(0x8000_0000), n(0xFFFF_FFFF)]
            )),
            0
        );
        assert_eq!(i32_val(invoke("extern:Int32.div", &[n(100), n(0)])), 0);
        assert_eq!(i32_val(invoke("extern:Int32.mod", &[n(100), n(0)])), 100);
        assert_eq!(
            i32_val(invoke(
                "extern:Int32.shiftLeft",
                &[n(0xFFFF_FFFF), n(0xFFFF_FFFF)]
            )),
            i32::MIN
        );
        assert_eq!(
            i32_val(invoke("extern:Int32.shiftRight", &[n(0xFFFF_FFFF), n(1)])),
            -1
        );
        assert_eq!(i32_val(invoke("extern:Int32.abs", &[n(0xFFFF_FFFF)])), 1);
        assert_eq!(
            i32_val(invoke("extern:Int32.abs", &[n(0x8000_0000)])),
            i32::MIN
        );
        assert_eq!(
            i32_val(invoke("extern:Int32.neg", &[n(0x8000_0000)])),
            i32::MIN
        );
        assert_eq!(i32_val(invoke("extern:Int32.complement", &[n(0)])), -1);
        assert_eq!(
            owned_usize(invoke("extern:Int32.decLt", &[n(0xFFFF_FFFF), n(1)])),
            1
        ); // -1 < 1
        assert_eq!(i32_val(invoke("extern:Int32.ofInt", &[i(-50000)])), -50000);
        assert_eq!(int_i64(invoke("extern:Int32.toInt", &[n(0xFFFF_FFFF)])), -1);
    }

    #[test]
    fn uint64_arithmetic_and_conversions() {
        let zero = n(0);
        let one = n(1);
        assert_eq!(u64_val(invoke("extern:UInt64.add", &[n(100), n(200)])), 300);
        assert_eq!(u64_val(invoke("extern:UInt64.sub", &[n(200), n(50)])), 150);
        assert_eq!(
            u64_val(invoke("extern:UInt64.mul", &[n(1000), n(2000)])),
            2_000_000
        );
        assert_eq!(u64_val(invoke("extern:UInt64.div", &[n(100), n(7)])), 14);
        assert_eq!(u64_val(invoke("extern:UInt64.mod", &[n(100), n(7)])), 2);
        assert_eq!(
            u64_val(invoke("extern:UInt64.div", &[n(100), zero.clone_ref()])),
            0
        );
        assert_eq!(
            u64_val(invoke("extern:UInt64.mod", &[n(100), zero.clone_ref()])),
            100
        );
        assert_eq!(
            u64_val(invoke("extern:UInt64.shiftLeft", &[one.clone_ref(), n(16)])),
            0x10000
        );
        assert_eq!(
            u64_val(invoke("extern:UInt64.shiftRight", &[n(0x10000), n(8)])),
            0x100
        );
        assert_eq!(u64_val(invoke("extern:UInt64.log2", &[n(0x10000)])), 16);
        assert_eq!(
            u64_val(invoke("extern:UInt64.log2", &[zero.clone_ref()])),
            0
        );
        assert_ne!(u64_val(invoke("extern:mixHash", &[n(12345), n(67890)])), 0);
        assert_eq!(
            owned_usize(invoke("extern:UInt64.decEq", &[n(999), n(999)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:UInt64.decLt", &[n(999), n(1000)])),
            1
        );
        assert_eq!(
            owned_usize(invoke("extern:UInt64.decLe", &[n(1000), n(999)])),
            0
        );
        assert_eq!(
            byte_word(invoke("extern:UInt64.toUInt8", &[n(0x1234_5678)])),
            0x78
        );
        assert_eq!(
            u16_val(invoke("extern:UInt64.toUInt16", &[n(0x1234_5678)])),
            0x5678
        );
        assert_eq!(
            u32_val(invoke("extern:UInt64.toUInt32", &[n(0x1234_5678)])),
            0x1234_5678
        );
        assert_eq!(
            u64_val(invoke("extern:UInt64.toNat", &[n(0x1234_5678)])),
            0x1234_5678
        );
    }

    #[test]
    fn int64_arithmetic_widening_and_conversions() {
        assert_eq!(i64_val(invoke("extern:Int64.add", &[n(100), n(200)])), 300);
        assert_eq!(i64_val(invoke("extern:Int64.mul", &[n(50), n(40)])), 2000);
        assert_eq!(i64_val(invoke("extern:Int64.div", &[n(100), n(7)])), 14);
        assert_eq!(i64_val(invoke("extern:Int64.mod", &[n(100), n(7)])), 2);
        assert_eq!(i64_val(invoke("extern:Int64.div", &[n(100), n(0)])), 0);
        assert_eq!(i64_val(invoke("extern:Int64.mod", &[n(100), n(0)])), 100);
        assert_eq!(
            i64_val(invoke("extern:Int64.shiftLeft", &[n(1), n(8)])),
            256
        );
        assert_eq!(
            i64_val(invoke("extern:Int64.shiftRight", &[n(256), n(4)])),
            16
        );
        assert_eq!(i64_val(invoke("extern:Int64.abs", &[n(50)])), 50);
        assert_eq!(
            owned_usize(invoke("extern:Int64.decLt", &[n(10), n(20)])),
            1
        );
        assert_eq!(
            i64_val(invoke("extern:Int64.ofInt", &[i(-999999)])),
            (-999999i64 as usize & (usize::MAX >> 1)) as i64
        );
        assert_eq!(int_i64(invoke("extern:Int64.toInt", &[n(42)])), 42);
    }

    #[test]
    fn usize_and_isize_arithmetic_and_conversions() {
        assert_eq!(usize_val(invoke("extern:USize.add", &[n(10), n(20)])), 30);
        assert_eq!(usize_val(invoke("extern:USize.sub", &[n(50), n(20)])), 30);
        assert_eq!(usize_val(invoke("extern:USize.div", &[n(100), n(0)])), 0);
        assert_eq!(usize_val(invoke("extern:USize.mod", &[n(100), n(0)])), 100);
        assert_eq!(str_val(invoke("extern:USize.repr", &[n(42)])), "42");
        assert_eq!(isize_val(invoke("extern:ISize.add", &[n(10), n(20)])), 30);
        assert_eq!(isize_val(invoke("extern:ISize.sub", &[n(50), n(20)])), 30);
        assert_eq!(isize_val(invoke("extern:ISize.div", &[n(100), n(0)])), 0);
        assert_eq!(isize_val(invoke("extern:ISize.mod", &[n(100), n(0)])), 100);
        assert_eq!(
            isize_val(invoke("extern:ISize.ofInt", &[i(-42)])),
            (-42isize as usize & (usize::MAX >> 1)) as isize
        );
        assert_eq!(int_i64(invoke("extern:ISize.toInt", &[n(42)])), 42);
    }

    #[test]
    fn all_fixed_width_integer_families_resolve_and_stay_off_managerless_task_path() {
        let all_rows = [
            "extern:UInt16.add",
            "extern:UInt16.sub",
            "extern:UInt16.mul",
            "extern:UInt16.div",
            "extern:UInt16.mod",
            "extern:UInt16.land",
            "extern:UInt16.lor",
            "extern:UInt16.xor",
            "extern:UInt16.shiftLeft",
            "extern:UInt16.shiftRight",
            "extern:UInt16.complement",
            "extern:UInt16.neg",
            "extern:UInt16.log2",
            "extern:UInt16.decEq",
            "extern:UInt16.decLe",
            "extern:UInt16.decLt",
            "extern:UInt16.ofNat",
            "extern:UInt16.ofNatLT",
            "extern:UInt16.ofBitVec",
            "extern:UInt16.toNat",
            "extern:UInt16.toBitVec",
            "extern:UInt16.toUInt8",
            "extern:UInt16.toUInt32",
            "extern:UInt16.toUInt64",
            "extern:UInt16.toUSize",
            "extern:UInt32.add",
            "extern:UInt32.sub",
            "extern:UInt32.mul",
            "extern:UInt32.div",
            "extern:UInt32.mod",
            "extern:UInt32.land",
            "extern:UInt32.lor",
            "extern:UInt32.xor",
            "extern:UInt32.shiftLeft",
            "extern:UInt32.shiftRight",
            "extern:UInt32.complement",
            "extern:UInt32.neg",
            "extern:UInt32.log2",
            "extern:UInt32.decEq",
            "extern:UInt32.decLe",
            "extern:UInt32.decLt",
            "extern:UInt32.ofNat",
            "extern:UInt32.ofNatLT",
            "extern:UInt32.ofBitVec",
            "extern:UInt32.toNat",
            "extern:UInt32.toBitVec",
            "extern:UInt32.toUInt8",
            "extern:UInt32.toUInt16",
            "extern:UInt32.toUInt64",
            "extern:UInt32.toUSize",
            "extern:UInt64.add",
            "extern:UInt64.sub",
            "extern:UInt64.mul",
            "extern:UInt64.div",
            "extern:UInt64.mod",
            "extern:UInt64.land",
            "extern:UInt64.lor",
            "extern:UInt64.xor",
            "extern:UInt64.shiftLeft",
            "extern:UInt64.shiftRight",
            "extern:UInt64.complement",
            "extern:UInt64.neg",
            "extern:UInt64.log2",
            "extern:UInt64.decEq",
            "extern:UInt64.decLe",
            "extern:UInt64.decLt",
            "extern:UInt64.ofNat",
            "extern:UInt64.ofNatLT",
            "extern:UInt64.ofBitVec",
            "extern:UInt64.toNat",
            "extern:UInt64.toBitVec",
            "extern:UInt64.toUInt8",
            "extern:UInt64.toUInt16",
            "extern:UInt64.toUInt32",
            "extern:UInt64.toUSize",
            "extern:mixHash",
            "extern:USize.add",
            "extern:USize.sub",
            "extern:USize.mul",
            "extern:USize.div",
            "extern:USize.mod",
            "extern:USize.land",
            "extern:USize.lor",
            "extern:USize.xor",
            "extern:USize.shiftLeft",
            "extern:USize.shiftRight",
            "extern:USize.complement",
            "extern:USize.neg",
            "extern:USize.log2",
            "extern:USize.decEq",
            "extern:USize.decLe",
            "extern:USize.decLt",
            "extern:USize.ofNat",
            "extern:USize.ofNatLT",
            "extern:USize.ofNat32",
            "extern:USize.ofBitVec",
            "extern:USize.toNat",
            "extern:USize.toBitVec",
            "extern:USize.toUInt8",
            "extern:USize.toUInt16",
            "extern:USize.toUInt32",
            "extern:USize.toUInt64",
            "extern:USize.repr",
            "extern:Int16.add",
            "extern:Int16.sub",
            "extern:Int16.mul",
            "extern:Int16.div",
            "extern:Int16.mod",
            "extern:Int16.land",
            "extern:Int16.lor",
            "extern:Int16.xor",
            "extern:Int16.shiftLeft",
            "extern:Int16.shiftRight",
            "extern:Int16.complement",
            "extern:Int16.neg",
            "extern:Int16.abs",
            "extern:Int16.decEq",
            "extern:Int16.decLe",
            "extern:Int16.decLt",
            "extern:Int16.ofNat",
            "extern:Int16.ofInt",
            "extern:Int16.toInt",
            "extern:Int16.toInt8",
            "extern:Int16.toInt32",
            "extern:Int16.toInt64",
            "extern:Int16.toISize",
            "extern:Int32.add",
            "extern:Int32.sub",
            "extern:Int32.mul",
            "extern:Int32.div",
            "extern:Int32.mod",
            "extern:Int32.land",
            "extern:Int32.lor",
            "extern:Int32.xor",
            "extern:Int32.shiftLeft",
            "extern:Int32.shiftRight",
            "extern:Int32.complement",
            "extern:Int32.neg",
            "extern:Int32.abs",
            "extern:Int32.decEq",
            "extern:Int32.decLe",
            "extern:Int32.decLt",
            "extern:Int32.ofNat",
            "extern:Int32.ofInt",
            "extern:Int32.toInt",
            "extern:Int32.toInt8",
            "extern:Int32.toInt16",
            "extern:Int32.toInt64",
            "extern:Int32.toISize",
            "extern:Int64.add",
            "extern:Int64.sub",
            "extern:Int64.mul",
            "extern:Int64.div",
            "extern:Int64.mod",
            "extern:Int64.land",
            "extern:Int64.lor",
            "extern:Int64.xor",
            "extern:Int64.shiftLeft",
            "extern:Int64.shiftRight",
            "extern:Int64.complement",
            "extern:Int64.neg",
            "extern:Int64.abs",
            "extern:Int64.decEq",
            "extern:Int64.decLe",
            "extern:Int64.decLt",
            "extern:Int64.ofNat",
            "extern:Int64.ofInt",
            "extern:Int64.toInt",
            "extern:Int64.toInt8",
            "extern:Int64.toInt16",
            "extern:Int64.toInt32",
            "extern:Int64.toISize",
            "extern:ISize.add",
            "extern:ISize.sub",
            "extern:ISize.mul",
            "extern:ISize.div",
            "extern:ISize.mod",
            "extern:ISize.land",
            "extern:ISize.lor",
            "extern:ISize.xor",
            "extern:ISize.shiftLeft",
            "extern:ISize.shiftRight",
            "extern:ISize.complement",
            "extern:ISize.neg",
            "extern:ISize.abs",
            "extern:ISize.decEq",
            "extern:ISize.decLe",
            "extern:ISize.decLt",
            "extern:ISize.ofNat",
            "extern:ISize.ofInt",
            "extern:ISize.toInt",
            "extern:ISize.toInt8",
            "extern:ISize.toInt16",
            "extern:ISize.toInt32",
            "extern:ISize.toInt64",
        ];
        for row in all_rows {
            assert_ne!(
                IntrinsicImplementation::for_row(row),
                IntrinsicImplementation::Unsupported,
                "{row} must resolve"
            );
            assert!(!IntrinsicImplementation::for_row(row).is_managerless_task());
        }
    }
}
