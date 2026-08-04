//! Failure-atomic macro transactions and collision-safe memoization (plan §9.2, §10.6).
//!
//! A macro never receives a mutable environment directly. It reads through [`MacroTxn`],
//! which records positive, negative, iteration, option, and capability observations, and writes
//! into nested private journals. Only a completed [`MacroTxnProduct`] can be published. Rejection,
//! cancellation, resource exhaustion, and internal faults therefore have no state object through
//! which partial work could escape.
//!
//! Digest buckets are accelerators, never authority. Invocation identities retain their complete
//! canonical row, memo hits compare that row byte-for-byte, and publication revalidates every
//! snapshot observation plus every effect precondition against the live state.

use crate::macro_expand::{
    MacroExpansion, MacroExpansionBudget, MacroExpansionCheckpoint, MacroExpansionError,
    MacroExpansionInput, QuotationTemplate, QuotedSyntax, expand_quotation,
};
use crate::registry::GrammarEpoch;
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::{BoundedText, Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_hash::canon::Canonical;
use fln_hash::domain::{Digest, Domain, hash};
use fln_syntax::hygiene::{ExpansionSourceMap, OriginKind, SourceOrigin, SyntaxPath};
use fln_syntax::source::{ByteSpan, SourceInfo};
use fln_syntax::tree::{Preresolved, Syntax};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

const INVOCATION_SCHEMA: &[u8] = b"fln.macro-invocation/1\0";
const STATE_SCHEMA: &[u8] = b"fln.macro-state/1\0";

/// A bounded semantic value in macro-visible state.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MacroValue(Arc<[u8]>);

impl MacroValue {
    pub fn from_bytes(bytes: impl Into<Vec<u8>>) -> MacroValue {
        MacroValue(Arc::from(bytes.into()))
    }

    pub fn from_text(text: impl Into<String>) -> MacroValue {
        MacroValue::from_bytes(text.into().into_bytes())
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

/// A lexically canonical absolute path supplied by the capability authority.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonicalPath(String);

impl CanonicalPath {
    pub fn new(path: impl Into<String>) -> Result<CanonicalPath, CanonicalPathError> {
        let path = path.into();
        if path.as_bytes().contains(&0) {
            return Err(CanonicalPathError::Nul);
        }
        if !path.starts_with('/') {
            return Err(CanonicalPathError::NotAbsolute);
        }
        if path != "/" && path.ends_with('/') {
            return Err(CanonicalPathError::TrailingSeparator);
        }
        if path != "/"
            && path
                .split('/')
                .skip(1)
                .any(|component| component.is_empty() || component == "." || component == "..")
        {
            return Err(CanonicalPathError::NonCanonicalComponent);
        }
        Ok(CanonicalPath(path))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CanonicalPathError {
    Nul,
    NotAbsolute,
    TrailingSeparator,
    NonCanonicalComponent,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CapabilityFile {
    bytes: MacroValue,
    digest: Digest,
}

/// Immutable capability snapshot for one invocation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MacroCapabilities {
    files: BTreeMap<CanonicalPath, CapabilityFile>,
}

impl MacroCapabilities {
    pub fn new() -> MacroCapabilities {
        MacroCapabilities::default()
    }

    pub fn insert_file(
        &mut self,
        path: CanonicalPath,
        bytes: impl Into<Vec<u8>>,
    ) -> Option<MacroValue> {
        let bytes = MacroValue::from_bytes(bytes);
        let digest = hash(Domain::CacheKey, bytes.as_bytes());
        self.files
            .insert(path, CapabilityFile { bytes, digest })
            .map(|old| old.bytes)
    }

    pub fn remove_file(&mut self, path: &CanonicalPath) -> Option<MacroValue> {
        self.files.remove(path).map(|file| file.bytes)
    }

    pub fn file_digest(&self, path: &CanonicalPath) -> Option<Digest> {
        self.files.get(path).map(|file| file.digest)
    }
}

/// One macro-visible state snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MacroState {
    environment: BTreeMap<Name, MacroValue>,
    extensions: BTreeMap<Name, MacroValue>,
    options: BTreeMap<Name, MacroValue>,
    next_gensym: u64,
}

impl MacroState {
    pub fn new() -> MacroState {
        MacroState::default()
    }

    pub fn environment(&self, name: &Name) -> Option<&MacroValue> {
        self.environment.get(name)
    }

    pub fn extension(&self, name: &Name) -> Option<&MacroValue> {
        self.extensions.get(name)
    }

    pub fn option(&self, name: &Name) -> Option<&MacroValue> {
        self.options.get(name)
    }

    pub const fn next_gensym(&self) -> u64 {
        self.next_gensym
    }

    pub fn insert_environment(&mut self, name: Name, value: MacroValue) -> Option<MacroValue> {
        self.environment.insert(name, value)
    }

    pub fn insert_extension(&mut self, name: Name, value: MacroValue) -> Option<MacroValue> {
        self.extensions.insert(name, value)
    }

    pub fn insert_option(&mut self, name: Name, value: MacroValue) -> Option<MacroValue> {
        self.options.insert(name, value)
    }

    pub fn remove_environment(&mut self, name: &Name) -> Option<MacroValue> {
        self.environment.remove(name)
    }

    pub fn remove_extension(&mut self, name: &Name) -> Option<MacroValue> {
        self.extensions.remove(name)
    }

    pub fn remove_option(&mut self, name: &Name) -> Option<MacroValue> {
        self.options.remove(name)
    }

    pub fn set_next_gensym(&mut self, next: u64) {
        self.next_gensym = next;
    }

    pub fn identity(&self) -> MacroStateIdentity {
        MacroStateIdentity::of(self)
    }

    fn value_at(&self, slot: &MacroStateSlot) -> MacroObservedValue {
        match slot {
            MacroStateSlot::Environment(name) => self
                .environment
                .get(name)
                .cloned()
                .map_or(MacroObservedValue::Absent, MacroObservedValue::Value),
            MacroStateSlot::Extension(name) => self
                .extensions
                .get(name)
                .cloned()
                .map_or(MacroObservedValue::Absent, MacroObservedValue::Value),
            MacroStateSlot::Option(name) => self
                .options
                .get(name)
                .cloned()
                .map_or(MacroObservedValue::Absent, MacroObservedValue::Value),
            MacroStateSlot::Gensym => MacroObservedValue::Counter(self.next_gensym),
        }
    }

    fn apply_value(
        &mut self,
        slot: &MacroStateSlot,
        value: &MacroObservedValue,
    ) -> Result<(), MacroPublishError> {
        match (slot, value) {
            (MacroStateSlot::Environment(name), MacroObservedValue::Absent) => {
                self.environment.remove(name);
            }
            (MacroStateSlot::Environment(name), MacroObservedValue::Value(value)) => {
                self.environment.insert(name.clone(), value.clone());
            }
            (MacroStateSlot::Extension(name), MacroObservedValue::Absent) => {
                self.extensions.remove(name);
            }
            (MacroStateSlot::Extension(name), MacroObservedValue::Value(value)) => {
                self.extensions.insert(name.clone(), value.clone());
            }
            (MacroStateSlot::Option(name), MacroObservedValue::Absent) => {
                self.options.remove(name);
            }
            (MacroStateSlot::Option(name), MacroObservedValue::Value(value)) => {
                self.options.insert(name.clone(), value.clone());
            }
            (MacroStateSlot::Gensym, MacroObservedValue::Counter(next)) => {
                self.next_gensym = *next;
            }
            _ => return Err(MacroPublishError::IllTypedEffect),
        }
        Ok(())
    }

    fn surface_entries(&self, surface: MacroStateSurface) -> Vec<(Name, MacroValue)> {
        match surface {
            MacroStateSurface::Environment => self
                .environment
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect(),
            MacroStateSurface::Extension => self
                .extensions
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect(),
            MacroStateSurface::Option => self
                .options
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect(),
        }
    }
}

/// Complete state identity; the digest is only a lookup accelerator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroStateIdentity {
    digest: Digest,
    canonical: Arc<[u8]>,
}

impl MacroStateIdentity {
    fn of(state: &MacroState) -> MacroStateIdentity {
        let canonical = canonical_state(state);
        MacroStateIdentity {
            digest: hash(Domain::CacheKey, &canonical),
            canonical: Arc::from(canonical),
        }
    }

    pub const fn digest(&self) -> Digest {
        self.digest
    }

    pub fn canonical(&self) -> &[u8] {
        &self.canonical
    }
}

/// A state location visible to a macro.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MacroStateSlot {
    Environment(Name),
    Extension(Name),
    Option(Name),
    Gensym,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MacroStateSurface {
    Environment,
    Extension,
    Option,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MacroObservedValue {
    Absent,
    Value(MacroValue),
    Counter(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MacroReadSource {
    Snapshot,
    Journal,
}

/// One exact observation made by a transaction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MacroReadObservation {
    StateSlot {
        slot: MacroStateSlot,
        source: MacroReadSource,
        observed: MacroObservedValue,
    },
    StateIteration {
        surface: MacroStateSurface,
        snapshot_entries: Vec<(Name, MacroValue)>,
        observed_entries: Vec<(Name, MacroValue)>,
    },
    CapabilityFile {
        path: CanonicalPath,
        content: Option<Digest>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum OpaqueReadReason {
    Clock,
    Uninstrumented(String),
}

/// Exact external and journal-local dependencies of one invocation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MacroReadSet {
    observations: BTreeSet<MacroReadObservation>,
    opaque: BTreeSet<OpaqueReadReason>,
}

impl MacroReadSet {
    pub fn new() -> MacroReadSet {
        MacroReadSet::default()
    }

    pub fn observations(&self) -> &BTreeSet<MacroReadObservation> {
        &self.observations
    }

    pub fn opaque_reasons(&self) -> &BTreeSet<OpaqueReadReason> {
        &self.opaque
    }

    pub fn is_complete(&self) -> bool {
        self.opaque.is_empty()
    }

    pub fn matches(&self, state: &MacroState, capabilities: &MacroCapabilities) -> bool {
        self.observations
            .iter()
            .all(|observation| match observation {
                MacroReadObservation::StateSlot {
                    slot,
                    source: MacroReadSource::Snapshot,
                    observed,
                } => state.value_at(slot) == *observed,
                MacroReadObservation::StateSlot {
                    source: MacroReadSource::Journal,
                    ..
                } => true,
                MacroReadObservation::StateIteration {
                    surface,
                    snapshot_entries,
                    ..
                } => state.surface_entries(*surface) == *snapshot_entries,
                MacroReadObservation::CapabilityFile { path, content } => {
                    capabilities.file_digest(path) == *content
                }
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroCacheability {
    Cacheable,
    Uncacheable { reasons: BTreeSet<OpaqueReadReason> },
}

/// One semantic write, including the exact precondition needed for atomic replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroEffect {
    slot: MacroStateSlot,
    before: MacroObservedValue,
    after: MacroObservedValue,
}

impl MacroEffect {
    pub fn slot(&self) -> &MacroStateSlot {
        &self.slot
    }

    pub fn before(&self) -> &MacroObservedValue {
        &self.before
    }

    pub fn after(&self) -> &MacroObservedValue {
        &self.after
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticRetention {
    CommitOnly,
    FailureVisible,
}

/// A bounded diagnostic and its optional complete source map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroDiagnostic {
    code: BoundedText,
    message: BoundedText,
    retention: DiagnosticRetention,
    source_map: Option<ExpansionSourceMap>,
}

impl MacroDiagnostic {
    pub fn new(
        code: impl Into<String>,
        message: impl Into<String>,
        retention: DiagnosticRetention,
        source_map: Option<ExpansionSourceMap>,
    ) -> MacroDiagnostic {
        MacroDiagnostic {
            code: BoundedText::new(code),
            message: BoundedText::new(message),
            retention,
            source_map,
        }
    }

    pub fn code(&self) -> &str {
        self.code.text()
    }

    pub fn message(&self) -> &str {
        self.message.text()
    }

    pub const fn retention(&self) -> DiagnosticRetention {
        self.retention
    }

    pub fn source_map(&self) -> Option<&ExpansionSourceMap> {
        self.source_map.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroCapabilityEvent {
    FileRead {
        path: CanonicalPath,
        content: Option<Digest>,
    },
    ClockObservedOpaque {
        tick: u64,
    },
    ClockDenied {
        mode: Mode,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacroTxnBudget {
    pub max_operations: u64,
}

impl MacroTxnBudget {
    pub const fn generous() -> MacroTxnBudget {
        MacroTxnBudget {
            max_operations: u64::MAX,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroTxnCheckpoint {
    BeforeOperation { completed: u64 },
    BeforePublication { completed: u64 },
}

impl MacroTxnCheckpoint {
    fn progress(self) -> String {
        match self {
            MacroTxnCheckpoint::BeforeOperation { completed } => {
                format!("macro transaction before operation {completed}")
            }
            MacroTxnCheckpoint::BeforePublication { completed } => {
                format!("macro transaction before publication after {completed} operations")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroTxnError {
    CapabilityDenied {
        capability: &'static str,
        mode: Mode,
    },
    Expansion(MacroExpansionError),
    Identity(MacroIdentityError),
    NoNestedTransaction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroTxnAbort {
    Refused(MacroTxnError),
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

impl From<MacroTxnError> for MacroTxnAbort {
    fn from(error: MacroTxnError) -> MacroTxnAbort {
        MacroTxnAbort::Refused(error)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroIdentityError {
    PositionTooLarge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroTxnFailure {
    error: MacroTxnError,
    diagnostics: Vec<MacroDiagnostic>,
}

impl MacroTxnFailure {
    pub const fn error(&self) -> &MacroTxnError {
        &self.error
    }

    pub fn diagnostics(&self) -> &[MacroDiagnostic] {
        &self.diagnostics
    }
}

/// Complete canonical identity of one macro invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroInvocationIdentity {
    digest: Digest,
    canonical: Arc<[u8]>,
    grammar_epoch: GrammarEpoch,
    mode: Mode,
}

impl MacroInvocationIdentity {
    /// Bind a macro-specific canonical payload to the mandatory grammar/mode coordinates.
    pub fn from_canonical_row(
        grammar_epoch: GrammarEpoch,
        mode: Mode,
        canonical_payload: impl Into<Vec<u8>>,
    ) -> MacroInvocationIdentity {
        let mut row = CanonRow::new(INVOCATION_SCHEMA);
        row.u64(grammar_epoch.revision());
        row.bytes(&grammar_epoch.digest().0);
        row.byte(mode.tag());
        row.bytes(&canonical_payload.into());
        MacroInvocationIdentity::from_complete_row(grammar_epoch, mode, row.finish())
    }

    fn from_complete_row(
        grammar_epoch: GrammarEpoch,
        mode: Mode,
        canonical: Vec<u8>,
    ) -> MacroInvocationIdentity {
        MacroInvocationIdentity {
            digest: hash(Domain::CacheKey, &canonical),
            canonical: Arc::from(canonical),
            grammar_epoch,
            mode,
        }
    }

    /// Reconstruct a decoded identity. Authority still compares the complete row.
    pub fn from_decoded(
        digest: Digest,
        canonical: impl Into<Vec<u8>>,
        grammar_epoch: GrammarEpoch,
        mode: Mode,
    ) -> MacroInvocationIdentity {
        MacroInvocationIdentity {
            digest,
            canonical: Arc::from(canonical.into()),
            grammar_epoch,
            mode,
        }
    }

    pub fn from_expansion_input(
        input: &MacroExpansionInput,
    ) -> Result<MacroInvocationIdentity, MacroIdentityError> {
        Ok(MacroInvocationIdentity::from_complete_row(
            input.coordinates.grammar_epoch,
            input.coordinates.mode,
            canonical_expansion_input(input)?,
        ))
    }

    pub const fn digest(&self) -> Digest {
        self.digest
    }

    pub fn canonical(&self) -> &[u8] {
        &self.canonical
    }

    pub const fn grammar_epoch(&self) -> GrammarEpoch {
        self.grammar_epoch
    }

    pub const fn mode(&self) -> Mode {
        self.mode
    }
}

#[derive(Default)]
struct TxnFrame {
    overlay: BTreeMap<MacroStateSlot, MacroObservedValue>,
    effects: Vec<MacroEffect>,
    diagnostics: Vec<MacroDiagnostic>,
}

/// Private mutable view used only while an invocation body executes.
pub struct MacroTxn<'a> {
    identity: MacroInvocationIdentity,
    grammar_epoch: GrammarEpoch,
    mode: Mode,
    base: &'a MacroState,
    capabilities: &'a MacroCapabilities,
    budget: MacroTxnBudget,
    cancellation: Option<&'a dyn Fn(MacroTxnCheckpoint) -> bool>,
    completed: u64,
    frames: Vec<TxnFrame>,
    reads: MacroReadSet,
    capability_events: Vec<MacroCapabilityEvent>,
}

impl MacroTxn<'_> {
    pub const fn grammar_epoch(&self) -> GrammarEpoch {
        self.grammar_epoch
    }

    pub const fn mode(&self) -> Mode {
        self.mode
    }

    pub fn begin_nested(&mut self) -> Result<(), MacroTxnAbort> {
        self.observe_operation()?;
        self.frames.push(TxnFrame::default());
        Ok(())
    }

    pub fn commit_nested(&mut self) -> Result<(), MacroTxnAbort> {
        self.observe_operation()?;
        if self.frames.len() == 1 {
            return Err(MacroTxnError::NoNestedTransaction.into());
        }
        let child = self.frames.pop().ok_or_else(|| {
            MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "nested commit lost the child frame",
            ))
        })?;
        let parent = self.frames.last_mut().ok_or_else(|| {
            MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "nested commit lost the parent frame",
            ))
        })?;
        parent.overlay.extend(child.overlay);
        parent.effects.extend(child.effects);
        parent.diagnostics.extend(child.diagnostics);
        Ok(())
    }

    pub fn rollback_nested(&mut self) -> Result<(), MacroTxnAbort> {
        self.observe_operation()?;
        if self.frames.len() == 1 {
            return Err(MacroTxnError::NoNestedTransaction.into());
        }
        let child = self.frames.pop().ok_or_else(|| {
            MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "nested rollback lost the child frame",
            ))
        })?;
        let parent = self.frames.last_mut().ok_or_else(|| {
            MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "nested rollback lost the parent frame",
            ))
        })?;
        parent.diagnostics.extend(
            child
                .diagnostics
                .into_iter()
                .filter(|diagnostic| diagnostic.retention == DiagnosticRetention::FailureVisible),
        );
        Ok(())
    }

    pub fn read_environment(&mut self, name: &Name) -> Result<Option<MacroValue>, MacroTxnAbort> {
        self.read_value(MacroStateSlot::Environment(name.clone()))
    }

    pub fn read_extension(&mut self, name: &Name) -> Result<Option<MacroValue>, MacroTxnAbort> {
        self.read_value(MacroStateSlot::Extension(name.clone()))
    }

    pub fn read_option(&mut self, name: &Name) -> Result<Option<MacroValue>, MacroTxnAbort> {
        self.read_value(MacroStateSlot::Option(name.clone()))
    }

    pub fn set_environment(&mut self, name: Name, value: MacroValue) -> Result<(), MacroTxnAbort> {
        self.write_slot(
            MacroStateSlot::Environment(name),
            MacroObservedValue::Value(value),
        )
    }

    pub fn set_extension(&mut self, name: Name, value: MacroValue) -> Result<(), MacroTxnAbort> {
        self.write_slot(
            MacroStateSlot::Extension(name),
            MacroObservedValue::Value(value),
        )
    }

    pub fn set_option(&mut self, name: Name, value: MacroValue) -> Result<(), MacroTxnAbort> {
        self.write_slot(
            MacroStateSlot::Option(name),
            MacroObservedValue::Value(value),
        )
    }

    pub fn remove_environment(&mut self, name: Name) -> Result<(), MacroTxnAbort> {
        self.write_slot(
            MacroStateSlot::Environment(name),
            MacroObservedValue::Absent,
        )
    }

    pub fn remove_extension(&mut self, name: Name) -> Result<(), MacroTxnAbort> {
        self.write_slot(MacroStateSlot::Extension(name), MacroObservedValue::Absent)
    }

    pub fn remove_option(&mut self, name: Name) -> Result<(), MacroTxnAbort> {
        self.write_slot(MacroStateSlot::Option(name), MacroObservedValue::Absent)
    }

    pub fn fresh_gensym(&mut self) -> Result<u64, MacroTxnAbort> {
        self.observe_operation()?;
        let slot = MacroStateSlot::Gensym;
        let (source, before) = self.effective_value(&slot);
        self.record_slot_read(slot.clone(), source, before.clone());
        let MacroObservedValue::Counter(current) = before else {
            return Err(MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-GENSYM",
                "gensym slot did not contain a counter",
            )));
        };
        let next = current.checked_add(1).ok_or_else(|| {
            MacroTxnAbort::Inconclusive(Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::StructuralBudget {
                    unit: StructuralUnit::ProducedNodes,
                },
                allowed: u64::MAX - 1,
                observed: u64::MAX,
            }))
        })?;
        self.append_effect(
            slot,
            MacroObservedValue::Counter(current),
            MacroObservedValue::Counter(next),
        )?;
        Ok(current)
    }

    pub fn iterate_environment(&mut self) -> Result<Vec<(Name, MacroValue)>, MacroTxnAbort> {
        self.iterate_surface(MacroStateSurface::Environment)
    }

    pub fn iterate_extensions(&mut self) -> Result<Vec<(Name, MacroValue)>, MacroTxnAbort> {
        self.iterate_surface(MacroStateSurface::Extension)
    }

    pub fn iterate_options(&mut self) -> Result<Vec<(Name, MacroValue)>, MacroTxnAbort> {
        self.iterate_surface(MacroStateSurface::Option)
    }

    pub fn read_file(&mut self, path: &CanonicalPath) -> Result<Option<MacroValue>, MacroTxnAbort> {
        self.observe_operation()?;
        let file = self.capabilities.files.get(path);
        let content = file.map(|file| file.digest);
        self.reads
            .observations
            .insert(MacroReadObservation::CapabilityFile {
                path: path.clone(),
                content,
            });
        self.capability_events.push(MacroCapabilityEvent::FileRead {
            path: path.clone(),
            content,
        });
        Ok(file.map(|file| file.bytes.clone()))
    }

    /// Faithful mode may observe a supplied clock value, but the observation is opaque and
    /// therefore uncacheable. Sound/frontier profiles deny it by default.
    pub fn observe_clock(&mut self, tick: u64) -> Result<u64, MacroTxnAbort> {
        self.observe_operation()?;
        if self.mode == Mode::Faithful {
            self.reads.opaque.insert(OpaqueReadReason::Clock);
            self.capability_events
                .push(MacroCapabilityEvent::ClockObservedOpaque { tick });
            Ok(tick)
        } else {
            self.capability_events
                .push(MacroCapabilityEvent::ClockDenied { mode: self.mode });
            Err(MacroTxnError::CapabilityDenied {
                capability: "clock",
                mode: self.mode,
            }
            .into())
        }
    }

    pub fn mark_uninstrumented_read(
        &mut self,
        label: impl Into<String>,
    ) -> Result<(), MacroTxnAbort> {
        self.observe_operation()?;
        let mut label = label.into();
        if label.len() > 256 {
            let mut end = 256;
            while end > 0 && !label.is_char_boundary(end) {
                end -= 1;
            }
            label.truncate(end);
        }
        self.reads
            .opaque
            .insert(OpaqueReadReason::Uninstrumented(label));
        Ok(())
    }

    pub fn emit_diagnostic(&mut self, diagnostic: MacroDiagnostic) -> Result<(), MacroTxnAbort> {
        self.observe_operation()?;
        let frame = self.frames.last_mut().ok_or_else(|| {
            MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "diagnostic emission observed no root frame",
            ))
        })?;
        frame.diagnostics.push(diagnostic);
        Ok(())
    }

    fn read_value(&mut self, slot: MacroStateSlot) -> Result<Option<MacroValue>, MacroTxnAbort> {
        self.observe_operation()?;
        let (source, observed) = self.effective_value(&slot);
        self.record_slot_read(slot, source, observed.clone());
        match observed {
            MacroObservedValue::Absent => Ok(None),
            MacroObservedValue::Value(value) => Ok(Some(value)),
            MacroObservedValue::Counter(_) => {
                Err(MacroTxnAbort::InternalFault(InternalFault::new(
                    "FLN-W4-MACRO-TXN-SLOT-TYPE",
                    "value read observed the gensym counter",
                )))
            }
        }
    }

    fn write_slot(
        &mut self,
        slot: MacroStateSlot,
        after: MacroObservedValue,
    ) -> Result<(), MacroTxnAbort> {
        self.observe_operation()?;
        let (source, before) = self.effective_value(&slot);
        self.record_slot_read(slot.clone(), source, before.clone());
        self.append_effect(slot, before, after)
    }

    fn append_effect(
        &mut self,
        slot: MacroStateSlot,
        before: MacroObservedValue,
        after: MacroObservedValue,
    ) -> Result<(), MacroTxnAbort> {
        let frame = self.frames.last_mut().ok_or_else(|| {
            MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "state write observed no root frame",
            ))
        })?;
        frame.overlay.insert(slot.clone(), after.clone());
        frame.effects.push(MacroEffect {
            slot,
            before,
            after,
        });
        Ok(())
    }

    fn effective_value(&self, slot: &MacroStateSlot) -> (MacroReadSource, MacroObservedValue) {
        for frame in self.frames.iter().rev() {
            if let Some(value) = frame.overlay.get(slot) {
                return (MacroReadSource::Journal, value.clone());
            }
        }
        (MacroReadSource::Snapshot, self.base.value_at(slot))
    }

    fn record_slot_read(
        &mut self,
        slot: MacroStateSlot,
        source: MacroReadSource,
        observed: MacroObservedValue,
    ) {
        self.reads
            .observations
            .insert(MacroReadObservation::StateSlot {
                slot,
                source,
                observed,
            });
    }

    fn iterate_surface(
        &mut self,
        surface: MacroStateSurface,
    ) -> Result<Vec<(Name, MacroValue)>, MacroTxnAbort> {
        self.observe_operation()?;
        let snapshot_entries = self.base.surface_entries(surface);
        let mut effective = self.base.clone();
        for frame in &self.frames {
            for effect in &frame.effects {
                effective
                    .apply_value(&effect.slot, &effect.after)
                    .map_err(|_| {
                        MacroTxnAbort::InternalFault(InternalFault::new(
                            "FLN-W4-MACRO-TXN-EFFECT",
                            "journal contained an ill-typed state effect",
                        ))
                    })?;
            }
        }
        let observed_entries = effective.surface_entries(surface);
        self.reads
            .observations
            .insert(MacroReadObservation::StateIteration {
                surface,
                snapshot_entries,
                observed_entries: observed_entries.clone(),
            });
        Ok(observed_entries)
    }

    fn observe_operation(&mut self) -> Result<(), MacroTxnAbort> {
        let checkpoint = MacroTxnCheckpoint::BeforeOperation {
            completed: self.completed,
        };
        if self.cancellation.is_some_and(|probe| probe(checkpoint)) {
            return Err(MacroTxnAbort::Inconclusive(Inconclusive::cancelled(
                checkpoint.progress(),
            )));
        }
        if self.completed == self.budget.max_operations {
            return Err(MacroTxnAbort::Inconclusive(Inconclusive::resource(
                ResourceUsage {
                    reason: ResourceReason::StructuralBudget {
                        unit: StructuralUnit::ProducedNodes,
                    },
                    allowed: self.budget.max_operations,
                    observed: self.completed.saturating_add(1),
                },
            )));
        }
        self.completed += 1;
        Ok(())
    }

    fn observe_publication(&self) -> Result<(), MacroTxnAbort> {
        let checkpoint = MacroTxnCheckpoint::BeforePublication {
            completed: self.completed,
        };
        if self.cancellation.is_some_and(|probe| probe(checkpoint)) {
            Err(MacroTxnAbort::Inconclusive(Inconclusive::cancelled(
                checkpoint.progress(),
            )))
        } else {
            Ok(())
        }
    }
}

/// Immutable, unpublished result of a successful transaction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroTxnProduct<T> {
    identity: MacroInvocationIdentity,
    grammar_epoch: GrammarEpoch,
    mode: Mode,
    value: T,
    reads: MacroReadSet,
    effects: Vec<MacroEffect>,
    diagnostics: Vec<MacroDiagnostic>,
    capability_events: Vec<MacroCapabilityEvent>,
    operations: u64,
    planned_state: MacroStateIdentity,
}

impl<T> MacroTxnProduct<T> {
    pub const fn identity(&self) -> &MacroInvocationIdentity {
        &self.identity
    }

    pub const fn grammar_epoch(&self) -> GrammarEpoch {
        self.grammar_epoch
    }

    pub const fn mode(&self) -> Mode {
        self.mode
    }

    pub fn reads(&self) -> &MacroReadSet {
        &self.reads
    }

    pub fn effects(&self) -> &[MacroEffect] {
        &self.effects
    }

    pub fn diagnostics(&self) -> &[MacroDiagnostic] {
        &self.diagnostics
    }

    pub fn capability_events(&self) -> &[MacroCapabilityEvent] {
        &self.capability_events
    }

    pub const fn operations(&self) -> u64 {
        self.operations
    }

    pub const fn planned_state(&self) -> &MacroStateIdentity {
        &self.planned_state
    }

    pub fn cacheability(&self) -> MacroCacheability {
        if self.reads.is_complete() {
            MacroCacheability::Cacheable
        } else {
            MacroCacheability::Uncacheable {
                reasons: self.reads.opaque.clone(),
            }
        }
    }

    pub fn publish(
        self,
        state: &mut MacroState,
        capabilities: &MacroCapabilities,
    ) -> Result<PublishedMacro<T>, MacroPublishError> {
        if !self.reads.matches(state, capabilities) {
            return Err(MacroPublishError::ReadSetChanged);
        }
        let mut planned = state.clone();
        for effect in &self.effects {
            let actual = planned.value_at(&effect.slot);
            if actual != effect.before {
                return Err(MacroPublishError::EffectPrecondition {
                    slot: effect.slot.clone(),
                    expected: effect.before.clone(),
                    actual,
                });
            }
            planned.apply_value(&effect.slot, &effect.after)?;
        }
        let final_state = planned.identity();
        *state = planned;
        Ok(PublishedMacro {
            value: self.value,
            reads: self.reads,
            effects: self.effects,
            diagnostics: self.diagnostics,
            capability_events: self.capability_events,
            final_state,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroPublishError {
    ReadSetChanged,
    EffectPrecondition {
        slot: MacroStateSlot,
        expected: MacroObservedValue,
        actual: MacroObservedValue,
    },
    IllTypedEffect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublishedMacro<T> {
    value: T,
    reads: MacroReadSet,
    effects: Vec<MacroEffect>,
    diagnostics: Vec<MacroDiagnostic>,
    capability_events: Vec<MacroCapabilityEvent>,
    final_state: MacroStateIdentity,
}

impl<T> PublishedMacro<T> {
    pub const fn value(&self) -> &T {
        &self.value
    }

    pub fn into_value(self) -> T {
        self.value
    }

    pub fn reads(&self) -> &MacroReadSet {
        &self.reads
    }

    pub fn effects(&self) -> &[MacroEffect] {
        &self.effects
    }

    pub fn diagnostics(&self) -> &[MacroDiagnostic] {
        &self.diagnostics
    }

    pub fn capability_events(&self) -> &[MacroCapabilityEvent] {
        &self.capability_events
    }

    pub const fn final_state(&self) -> &MacroStateIdentity {
        &self.final_state
    }
}

/// Status plus diagnostic facts that remain available on non-authoritative paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroRunReport<T> {
    status: Outcome<Result<MacroTxnProduct<T>, MacroTxnFailure>>,
    diagnostics: Vec<MacroDiagnostic>,
    reads: MacroReadSet,
    capability_events: Vec<MacroCapabilityEvent>,
    operations: u64,
    initial_state: MacroStateIdentity,
}

impl<T> MacroRunReport<T> {
    pub const fn status(&self) -> &Outcome<Result<MacroTxnProduct<T>, MacroTxnFailure>> {
        &self.status
    }

    pub fn into_status(self) -> Outcome<Result<MacroTxnProduct<T>, MacroTxnFailure>> {
        self.status
    }

    pub fn diagnostics(&self) -> &[MacroDiagnostic] {
        &self.diagnostics
    }

    pub fn reads(&self) -> &MacroReadSet {
        &self.reads
    }

    pub fn capability_events(&self) -> &[MacroCapabilityEvent] {
        &self.capability_events
    }

    pub const fn operations(&self) -> u64 {
        self.operations
    }

    pub const fn initial_state(&self) -> &MacroStateIdentity {
        &self.initial_state
    }
}

/// Inputs and controls for one transaction run.
pub struct MacroTxnConfig<'a> {
    identity: MacroInvocationIdentity,
    state: &'a MacroState,
    capabilities: &'a MacroCapabilities,
    budget: MacroTxnBudget,
    cancellation: Option<&'a dyn Fn(MacroTxnCheckpoint) -> bool>,
}

impl<'a> MacroTxnConfig<'a> {
    pub fn new(
        identity: MacroInvocationIdentity,
        state: &'a MacroState,
        capabilities: &'a MacroCapabilities,
        budget: MacroTxnBudget,
        cancellation: Option<&'a dyn Fn(MacroTxnCheckpoint) -> bool>,
    ) -> MacroTxnConfig<'a> {
        MacroTxnConfig {
            identity,
            state,
            capabilities,
            budget,
            cancellation,
        }
    }
}

/// Execute one invocation against a private journal.
pub fn run_macro_transaction<T>(
    config: MacroTxnConfig<'_>,
    body: impl FnOnce(&mut MacroTxn<'_>) -> Result<T, MacroTxnAbort>,
) -> MacroRunReport<T> {
    let MacroTxnConfig {
        identity,
        state,
        capabilities,
        budget,
        cancellation,
    } = config;
    let grammar_epoch = identity.grammar_epoch;
    let mode = identity.mode;
    let initial_state = state.identity();
    let mut txn = MacroTxn {
        identity,
        grammar_epoch,
        mode,
        base: state,
        capabilities,
        budget,
        cancellation,
        completed: 0,
        frames: vec![TxnFrame::default()],
        reads: MacroReadSet::new(),
        capability_events: Vec::new(),
    };

    let result = body(&mut txn);
    if result.is_ok() && txn.frames.len() != 1 {
        return fault_report(
            txn,
            initial_state,
            InternalFault::new(
                "FLN-W4-MACRO-TXN-FRAME",
                "macro body completed with unclosed nested transactions",
            ),
        );
    }
    let result = match result {
        Ok(value) => match txn.observe_publication() {
            Ok(()) => Ok(value),
            Err(abort) => Err(abort),
        },
        Err(abort) => Err(abort),
    };

    match result {
        Ok(value) => {
            let frame = txn
                .frames
                .pop()
                .expect("the root transaction frame was established at construction");
            let mut planned = state.clone();
            for effect in &frame.effects {
                if planned.value_at(&effect.slot) != effect.before
                    || planned.apply_value(&effect.slot, &effect.after).is_err()
                {
                    return fault_report(
                        txn,
                        initial_state,
                        InternalFault::new(
                            "FLN-W4-MACRO-TXN-EFFECT",
                            "private journal could not be replayed over its own snapshot",
                        ),
                    );
                }
            }
            let planned_state = planned.identity();
            let product = MacroTxnProduct {
                identity: txn.identity,
                grammar_epoch: txn.grammar_epoch,
                mode: txn.mode,
                value,
                reads: txn.reads.clone(),
                effects: frame.effects,
                diagnostics: frame.diagnostics.clone(),
                capability_events: txn.capability_events.clone(),
                operations: txn.completed,
                planned_state,
            };
            MacroRunReport {
                status: Outcome::Complete(Ok(product)),
                diagnostics: frame.diagnostics,
                reads: txn.reads,
                capability_events: txn.capability_events,
                operations: txn.completed,
                initial_state,
            }
        }
        Err(MacroTxnAbort::Refused(error)) => {
            let diagnostics = failure_visible_diagnostics(&txn.frames);
            MacroRunReport {
                status: Outcome::Complete(Err(MacroTxnFailure {
                    error,
                    diagnostics: diagnostics.clone(),
                })),
                diagnostics,
                reads: txn.reads,
                capability_events: txn.capability_events,
                operations: txn.completed,
                initial_state,
            }
        }
        Err(MacroTxnAbort::Inconclusive(inconclusive)) => MacroRunReport {
            status: Outcome::Inconclusive(inconclusive),
            diagnostics: failure_visible_diagnostics(&txn.frames),
            reads: txn.reads,
            capability_events: txn.capability_events,
            operations: txn.completed,
            initial_state,
        },
        Err(MacroTxnAbort::InternalFault(fault)) => fault_report(txn, initial_state, fault),
    }
}

fn fault_report<T>(
    txn: MacroTxn<'_>,
    initial_state: MacroStateIdentity,
    fault: InternalFault,
) -> MacroRunReport<T> {
    MacroRunReport {
        status: Outcome::InternalFault(fault),
        diagnostics: failure_visible_diagnostics(&txn.frames),
        reads: txn.reads,
        capability_events: txn.capability_events,
        operations: txn.completed,
        initial_state,
    }
}

fn failure_visible_diagnostics(frames: &[TxnFrame]) -> Vec<MacroDiagnostic> {
    frames
        .iter()
        .flat_map(|frame| frame.diagnostics.iter())
        .filter(|diagnostic| diagnostic.retention == DiagnosticRetention::FailureVisible)
        .cloned()
        .collect()
}

/// Run the landed quotation expander behind the real transaction publication boundary.
pub fn expand_quotation_transactional(
    input: MacroExpansionInput,
    state: &MacroState,
    capabilities: &MacroCapabilities,
    txn_budget: MacroTxnBudget,
    expansion_budget: MacroExpansionBudget,
    txn_cancellation: Option<&dyn Fn(MacroTxnCheckpoint) -> bool>,
    expansion_cancellation: Option<&dyn Fn(MacroExpansionCheckpoint) -> bool>,
) -> MacroRunReport<MacroExpansion> {
    let identity = match MacroInvocationIdentity::from_expansion_input(&input) {
        Ok(identity) => identity,
        Err(error) => {
            let identity = MacroInvocationIdentity::from_canonical_row(
                input.coordinates.grammar_epoch,
                input.coordinates.mode,
                INVOCATION_SCHEMA.to_vec(),
            );
            return run_macro_transaction(
                MacroTxnConfig::new(identity, state, capabilities, txn_budget, txn_cancellation),
                |_| Err(MacroTxnError::Identity(error).into()),
            );
        }
    };
    run_macro_transaction(
        MacroTxnConfig::new(identity, state, capabilities, txn_budget, txn_cancellation),
        |_| match expand_quotation(input, expansion_budget, expansion_cancellation) {
            Outcome::Complete(Ok(expansion)) => Ok(expansion),
            Outcome::Complete(Err(error)) => Err(MacroTxnError::Expansion(error).into()),
            Outcome::Inconclusive(inconclusive) => Err(MacroTxnAbort::Inconclusive(inconclusive)),
            Outcome::InternalFault(fault) => Err(MacroTxnAbort::InternalFault(fault)),
        },
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroMemoInsert {
    Inserted,
    Replaced,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroMemoRefusal {
    Uncacheable { reasons: BTreeSet<OpaqueReadReason> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroMemoLookup<'a, T> {
    Hit(&'a MacroTxnProduct<T>),
    Miss,
    CollisionMiss,
    StaleReadMiss,
}

/// Collision-safe memo store for completed macro transactions.
pub struct MacroMemo<T> {
    buckets: BTreeMap<Digest, Vec<MacroTxnProduct<T>>>,
}

impl<T> MacroMemo<T> {
    pub fn new() -> MacroMemo<T> {
        MacroMemo {
            buckets: BTreeMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        product: MacroTxnProduct<T>,
    ) -> Result<MacroMemoInsert, MacroMemoRefusal> {
        if let MacroCacheability::Uncacheable { reasons } = product.cacheability() {
            return Err(MacroMemoRefusal::Uncacheable { reasons });
        }
        let bucket = self.buckets.entry(product.identity.digest).or_default();
        if let Some(existing) = bucket
            .iter_mut()
            .find(|entry| entry.identity == product.identity)
        {
            *existing = product;
            Ok(MacroMemoInsert::Replaced)
        } else {
            bucket.push(product);
            Ok(MacroMemoInsert::Inserted)
        }
    }

    pub fn lookup(
        &self,
        identity: &MacroInvocationIdentity,
        state: &MacroState,
        capabilities: &MacroCapabilities,
    ) -> MacroMemoLookup<'_, T> {
        let Some(bucket) = self.buckets.get(&identity.digest) else {
            return MacroMemoLookup::Miss;
        };
        let Some(product) = bucket.iter().find(|entry| entry.identity == *identity) else {
            return MacroMemoLookup::CollisionMiss;
        };
        if product.reads.matches(state, capabilities) {
            MacroMemoLookup::Hit(product)
        } else {
            MacroMemoLookup::StaleReadMiss
        }
    }

    pub fn len(&self) -> usize {
        self.buckets.values().map(Vec::len).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.buckets.is_empty()
    }
}

impl<T> Default for MacroMemo<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Perturbation oracle for a declared read set.
///
/// If every recorded dependency still matches but a fresh semantic root changes, some read was
/// omitted or observed outside the transaction. Such a candidate is an internal fault, never a
/// cache hit.
pub fn validate_read_set_perturbation(
    reads: &MacroReadSet,
    perturbed_state: &MacroState,
    perturbed_capabilities: &MacroCapabilities,
    recorded_semantic_root: Digest,
    fresh_semantic_root: Digest,
) -> Result<(), InternalFault> {
    if reads.matches(perturbed_state, perturbed_capabilities)
        && recorded_semantic_root != fresh_semantic_root
    {
        Err(InternalFault::new(
            "FLN-W4-MACRO-READ-SET-COMPLETE",
            "macro output changed while every declared read remained equal",
        ))
    } else {
        Ok(())
    }
}

fn canonical_state(state: &MacroState) -> Vec<u8> {
    let mut row = CanonRow::new(STATE_SCHEMA);
    row.named_values(&state.environment);
    row.named_values(&state.extensions);
    row.named_values(&state.options);
    row.u64(state.next_gensym);
    row.finish()
}

fn canonical_expansion_input(input: &MacroExpansionInput) -> Result<Vec<u8>, MacroIdentityError> {
    let mut row = CanonRow::new(INVOCATION_SCHEMA);
    row.u64(input.coordinates.grammar_epoch.revision());
    row.bytes(&input.coordinates.grammar_epoch.digest().0);
    row.byte(input.coordinates.mode.tag());
    row.bytes(input.coordinates.expansion_path.canonical().as_bytes());
    row.name(&input.quotation.name);
    row.u64(input.quotation.macro_scope);
    row.optional_span(input.quotation.call_site)?;
    row.bool(input.quotation.canonical);
    row.byte(match input.quotation.hygiene {
        crate::macro_expand::HygienePolicy::Enabled => 1,
        crate::macro_expand::HygienePolicy::Disabled => 2,
    });
    row.template(&input.template)?;
    Ok(row.finish())
}

struct CanonRow {
    bytes: Vec<u8>,
}

impl CanonRow {
    fn new(schema: &[u8]) -> CanonRow {
        CanonRow {
            bytes: schema.to_vec(),
        }
    }

    fn finish(self) -> Vec<u8> {
        self.bytes
    }

    fn byte(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn bool(&mut self, value: bool) {
        self.byte(u8::from(value));
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn usize(&mut self, value: usize) -> Result<(), MacroIdentityError> {
        self.u64(u64::try_from(value).map_err(|_| MacroIdentityError::PositionTooLarge)?);
        Ok(())
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.u64(bytes.len() as u64);
        self.bytes.extend_from_slice(bytes);
    }

    fn name(&mut self, name: &Name) {
        self.bytes(&name.to_canonical_bytes());
    }

    fn named_values(&mut self, values: &BTreeMap<Name, MacroValue>) {
        self.u64(values.len() as u64);
        for (name, value) in values {
            self.name(name);
            self.bytes(value.as_bytes());
        }
    }

    fn span(&mut self, span: ByteSpan) -> Result<(), MacroIdentityError> {
        self.usize(span.start().0)?;
        self.usize(span.end().0)
    }

    fn optional_span(&mut self, span: Option<ByteSpan>) -> Result<(), MacroIdentityError> {
        match span {
            Some(span) => {
                self.byte(1);
                self.span(span)
            }
            None => {
                self.byte(0);
                Ok(())
            }
        }
    }

    fn source_info(&mut self, info: SourceInfo) -> Result<(), MacroIdentityError> {
        match info {
            SourceInfo::None => self.byte(0),
            SourceInfo::Original {
                leading,
                pos,
                trailing,
                end_pos,
            } => {
                self.byte(1);
                self.span(leading)?;
                self.usize(pos.0)?;
                self.span(trailing)?;
                self.usize(end_pos.0)?;
            }
            SourceInfo::Synthetic {
                pos,
                end_pos,
                canonical,
            } => {
                self.byte(2);
                self.usize(pos.0)?;
                self.usize(end_pos.0)?;
                self.bool(canonical);
            }
        }
        Ok(())
    }

    fn template(&mut self, root: &QuotationTemplate) -> Result<(), MacroIdentityError> {
        let mut pending = vec![root];
        while let Some(template) = pending.pop() {
            match template {
                QuotationTemplate::Literal(syntax) => {
                    self.byte(0);
                    self.syntax(syntax)?;
                }
                QuotationTemplate::Antiquotation { hole_info, value } => {
                    self.byte(1);
                    self.source_info(*hole_info)?;
                    self.quoted(value)?;
                }
                QuotationTemplate::Splice { hole_info, values } => {
                    self.byte(2);
                    self.source_info(*hole_info)?;
                    self.u64(values.len() as u64);
                    for value in values {
                        self.quoted(value)?;
                    }
                }
                QuotationTemplate::Node {
                    definition_info,
                    kind,
                    args,
                } => {
                    self.byte(3);
                    self.source_info(*definition_info)?;
                    self.name(kind);
                    self.u64(args.len() as u64);
                    pending.extend(args.iter().rev());
                }
                QuotationTemplate::GeneratedIdent {
                    definition_info,
                    raw_val,
                    base,
                    preresolved,
                    local_ordinal,
                } => {
                    self.byte(4);
                    self.source_info(*definition_info)?;
                    self.span(*raw_val)?;
                    self.name(base);
                    self.preresolved(preresolved);
                    self.u64(*local_ordinal);
                }
                QuotationTemplate::Nested {
                    definition_info,
                    quotation_ordinal,
                    body,
                } => {
                    self.byte(5);
                    self.source_info(*definition_info)?;
                    self.u64(*quotation_ordinal);
                    pending.push(body);
                }
            }
        }
        Ok(())
    }

    fn quoted(&mut self, quoted: &QuotedSyntax) -> Result<(), MacroIdentityError> {
        self.syntax(quoted.syntax())?;
        self.source_map(quoted.source_map())
    }

    fn syntax(&mut self, root: &Syntax) -> Result<(), MacroIdentityError> {
        let mut pending = vec![root];
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Missing => self.byte(0),
                Syntax::Node { info, kind, args } => {
                    self.byte(1);
                    self.source_info(*info)?;
                    self.name(kind);
                    self.u64(args.len() as u64);
                    pending.extend(args.iter().rev());
                }
                Syntax::Atom { info, val } => {
                    self.byte(2);
                    self.source_info(*info)?;
                    self.bytes(val.as_bytes());
                }
                Syntax::Ident {
                    info,
                    raw_val,
                    val,
                    preresolved,
                } => {
                    self.byte(3);
                    self.source_info(*info)?;
                    self.span(*raw_val)?;
                    self.name(val);
                    self.preresolved(preresolved);
                }
            }
        }
        Ok(())
    }

    fn preresolved(&mut self, values: &[Preresolved]) {
        self.u64(values.len() as u64);
        for value in values {
            match value {
                Preresolved::Namespace { ns } => {
                    self.byte(0);
                    self.name(ns);
                }
                Preresolved::Decl { name, fields } => {
                    self.byte(1);
                    self.name(name);
                    self.u64(fields.len() as u64);
                    for field in fields {
                        self.bytes(field.as_bytes());
                    }
                }
            }
        }
    }

    fn source_map(&mut self, source_map: &ExpansionSourceMap) -> Result<(), MacroIdentityError> {
        self.u64(source_map.len() as u64);
        for (path, origins) in source_map.entries() {
            self.syntax_path(path);
            self.u64(origins.iter().count() as u64);
            for origin in origins.iter() {
                self.source_origin(origin)?;
            }
        }
        Ok(())
    }

    fn syntax_path(&mut self, path: &SyntaxPath) {
        self.u64(path.components().len() as u64);
        for component in path.components() {
            self.u64(*component);
        }
    }

    fn source_origin(&mut self, origin: &SourceOrigin) -> Result<(), MacroIdentityError> {
        self.byte(match origin.kind {
            OriginKind::Literal => 0,
            OriginKind::MacroDefinition => 1,
            OriginKind::MacroCall => 2,
            OriginKind::Quotation => 3,
            OriginKind::Antiquotation => 4,
            OriginKind::Recovered => 5,
        });
        self.optional_span(origin.span)?;
        match &origin.expansion {
            Some(expansion) => {
                self.byte(1);
                self.bytes(expansion.canonical().as_bytes());
            }
            None => self.byte(0),
        }
        Ok(())
    }
}
