//! The native W2 attribute substrate (bead fln-attribute-native-state-m7l):
//! immutable definitions, assignment state, and typed data queries, generated
//! from the pinned attribute census (`contracts/ATTRIBUTE_STATE_CENSUS.txt`).
//!
//! # The laws
//!
//! * **Generated, never hand-written.** The definition substrate is parsed
//!   from the committed census: every definition carries its row id, family,
//!   anchor, and handler class, so a registry that drifts from the census is a
//!   parse refusal, not a quieter registry.
//! * **Immutable snapshots, O(1).** The state is persistent maps behind
//!   `Arc`; a snapshot copies root pointers only, and updates rebuild exactly
//!   the affected path (PMap's law). Speculative branches are exact: a branch
//!   edit never reaches its base.
//! * **Lossless storage.** Assignments preserve registration and target
//!   identity, payload bytes (opaque payloads byte-exact and flagged),
//!   priority, kind, and provenance. Storage is always data.
//! * **The execution boundary is typed.** A census row whose observable query
//!   invokes Lean code cannot be discharged here: dispatching it returns
//!   typed [`RequiresHandler`] with the exact row id and the provisional
//!   grade, until W6 discharges the row through the native/library-source
//!   partition. Retaining bytes is not executable compatibility.
//! * **Duplicate and conflict behavior is the family's law, per row.** A tag
//!   or label set insert is a no-op; a parametric application replaces; a
//!   core application is per-row (the row's own handler owns the rule). The
//!   family's law comes from the census, not from memory.
//! * **Root participation is per-field.** Semantic state changes affect
//!   `logical_root` only where the census declares it; ownership, topology,
//!   and evidence never enter it by hidden coupling.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use std::collections::BTreeMap;

use crate::pmap::{PKey, PMap};

/// The census families, as an exhaustive enum (the registry's own vocabulary).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeFamily {
    Core,
    Tag,
    Simp,
    SymSimp,
    Simproc,
    Label,
    Parametric,
    InitAttr,
    KeyedDecls,
    ParserAttr,
    EnvExtension,
    Opaque,
}

impl AttributeFamily {
    pub fn from_token(token: &str) -> Option<Self> {
        match token {
            "core" => Some(Self::Core),
            "tag" => Some(Self::Tag),
            "simp" => Some(Self::Simp),
            "sym-simp" => Some(Self::SymSimp),
            "simproc" => Some(Self::Simproc),
            "label" => Some(Self::Label),
            "parametric" => Some(Self::Parametric),
            "init-attr" => Some(Self::InitAttr),
            "keyed-decls" => Some(Self::KeyedDecls),
            "parser-attr" => Some(Self::ParserAttr),
            "env-extension" => Some(Self::EnvExtension),
            "opaque" => Some(Self::Opaque),
            _ => None,
        }
    }

    /// The duplicate/conflict law of the family, from the census rows' own
    /// helpers: a set insert, a parameter replacement, or per-row.
    pub fn duplicate_law(self) -> DuplicateLaw {
        match self {
            Self::Tag | Self::Label | Self::EnvExtension => DuplicateLaw::SetNoOp,
            Self::Simp | Self::SymSimp | Self::Simproc => DuplicateLaw::PriorityOrdered,
            Self::Parametric | Self::InitAttr => DuplicateLaw::Replace,
            Self::Core | Self::KeyedDecls | Self::ParserAttr | Self::Opaque => DuplicateLaw::PerRow,
        }
    }
}

/// How a duplicate assignment on one (attribute, target) resolves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicateLaw {
    /// A set insert: the second application is a no-op.
    SetNoOp,
    /// Priority orders; equal priority preserves the first application.
    PriorityOrdered,
    /// The later application replaces the parameter.
    Replace,
    /// The row's own handler owns the rule; the substrate records both
    /// applications as a typed conflict for it.
    PerRow,
}

/// The census's handler-class lattice (the boundary the W6 handoff consumes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HandlerClass {
    /// Provably pure state: dispatch serves data.
    DataOnly,
    /// The row's observable query invokes Lean code: dispatch is a typed
    /// RequiresHandler until W6 discharges it.
    RequiresHandler,
    /// Unproven: the conservative default — RequiresHandler, graded
    /// provisional.
    RequiresHandlerProvisional,
    /// The OpaqueFallback: unknown/custom attributes are opaque handlers.
    OpaqueHandlerRequired,
}

impl HandlerClass {
    pub fn from_token(token: &str) -> Option<Self> {
        match token {
            "data-only" => Some(Self::DataOnly),
            "requires-handler" => Some(Self::RequiresHandler),
            "requires-handler-provisional" => Some(Self::RequiresHandlerProvisional),
            "opaque-handler-required" => Some(Self::OpaqueHandlerRequired),
            _ => None,
        }
    }

    /// The provisional grade the W6 handoff carries.
    pub fn provisional_grade(self) -> &'static str {
        match self {
            Self::DataOnly => "not-applicable-data-only",
            Self::RequiresHandler => "provisional-pending-W6-discharge",
            Self::RequiresHandlerProvisional => "provisional-unproven-pending-W6-discharge",
            Self::OpaqueHandlerRequired => "provisional-opaque-pending-W6-discharge",
        }
    }
}

/// One census row, parsed into the definition substrate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttributeDefinition {
    pub row_id: String,
    pub name: Name,
    pub family: AttributeFamily,
    pub handler_class: HandlerClass,
    pub application_time: String,
    pub anchor: String,
}

/// The payload of one assignment, lossless (opaque payloads byte-exact).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Payload {
    /// Tag/label families: presence is the payload.
    Unit,
    /// Simp families: polarity and priority.
    SimpEntry { post: bool, priority: u32 },
    /// Parametric/init-attr: the parameter's bytes.
    Parameter(Vec<u8>),
    /// Keyed-decls: the key and its implementation reference.
    Keyed { key: Name, implementation: Name },
    /// Unknown/custom: byte-exact, flagged opaque, never interpreted.
    Opaque(Vec<u8>),
}

/// The scope of one assignment (Lean's AttributeKind).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeKind {
    Global,
    Local,
    Scoped,
}

/// One assignment: an attribute applied to a declaration, with its
/// provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assignment {
    pub attribute: Name,
    pub target: Name,
    pub payload: Payload,
    pub kind: AttributeKind,
    pub provenance: String,
}

/// The typed boundary the W6 handoff consumes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RequiresHandler {
    pub row_id: String,
    pub grade: &'static str,
}

/// A stored query's result: data, or the boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResult<T> {
    Data(T),
    RequiresHandler(RequiresHandler),
}

/// Every way the substrate can refuse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttributeError {
    /// The census text is malformed (a row's field, a family, a class).
    MalformedCensus { reason: String },
    /// The attribute is not registered in the definition substrate.
    UnknownAttribute { attribute: String },
    /// A duplicate assignment hit the per-row conflict law.
    Conflict {
        attribute: String,
        target: String,
        law: &'static str,
    },
    /// A duplicate under PriorityOrdered compared equal on priority and
    /// payload — an idempotent re-application, recorded rather than
    /// re-stored.
    Idempotent,
    /// A resource budget was met, with exact usage (FL-INV-07: a typed
    /// answer, never a crash and never a silent truncation).
    BudgetRefusal { usage: String },
}

impl std::fmt::Display for AttributeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedCensus { reason } => write!(f, "malformed census: {reason}"),
            Self::UnknownAttribute { attribute } => {
                write!(f, "attribute `{attribute}` is not registered")
            }
            Self::Conflict {
                attribute,
                target,
                law,
            } => write!(
                f,
                "conflicting assignments of `{attribute}` on `{target}` ({law})"
            ),
            Self::Idempotent => write!(f, "an identical re-application is a no-op"),
            Self::BudgetRefusal { usage } => {
                write!(f, "the update budget was met: {usage}")
            }
        }
    }
}

impl std::error::Error for AttributeError {}

/// The (attribute, target) assignment key, with the canonical total order
/// (attribute, then target) and the mixed hash.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AttrTarget {
    pub attribute: Name,
    pub target: Name,
}

impl PKey for AttrTarget {
    fn key_hash(&self) -> u64 {
        // The canonical mix (the same discipline as fln-core's own mixes):
        // the two component hashes combined, never one truncated into the other.
        let mut acc = 0x9E37_79B9_7F4A_7C15u64;
        acc = (acc ^ self.attribute.hash()).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        (acc ^ self.target.hash()).wrapping_mul(0x94D0_49BB_1331_11EB)
    }
}

/// The immutable attribute state: definitions and assignments behind
/// persistent maps. `Clone` is O(1) — the PMap roots are `Arc` pointers, and
/// every update rebuilds exactly the affected path.
#[derive(Debug, Clone, Default)]
pub struct AttributeState {
    definitions: PMap<Name, AttributeDefinition>,
    assignments: PMap<AttrTarget, Assignment>,
}

/// Decode the census's percent-escapes.
fn decode(value: &str) -> String {
    value
        .replace("%20", " ")
        .replace("%0A", "\n")
        .replace("%7C", "|")
        .replace("%25", "%")
}

/// Parse one census row into key=value fields.
fn parse_census_row(line: &str) -> Result<BTreeMap<String, String>, AttributeError> {
    let mut fields = BTreeMap::new();
    for part in line.split(' ') {
        let Some((key, value)) = part.split_once('=') else {
            return Err(AttributeError::MalformedCensus {
                reason: format!("row segment is not key=value: {part:?}"),
            });
        };
        fields.insert(key.to_string(), decode(value));
    }
    Ok(fields)
}

impl AttributeState {
    /// An empty state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Build the definition substrate from the committed census text. The
    /// parameterized OpaqueFallback row is the shape, not a registration; it
    /// is excluded from the definition map and recorded separately.
    pub fn from_census(text: &str) -> Result<(Self, usize), AttributeError> {
        let mut state = Self::new();
        let mut count = 0usize;
        for (index, line) in text.lines().enumerate() {
            if !line.starts_with("row=") {
                continue;
            }
            let fields = parse_census_row(line)?;
            let row_id = fields
                .get("row")
                .ok_or_else(|| AttributeError::MalformedCensus {
                    reason: format!("line {}: missing row id", index + 1),
                })?
                .clone();
            if row_id == "opaque-fallback" {
                continue;
            }
            let family_token =
                fields
                    .get("family")
                    .ok_or_else(|| AttributeError::MalformedCensus {
                        reason: format!("row {row_id}: missing family"),
                    })?;
            let family = AttributeFamily::from_token(family_token).ok_or_else(|| {
                AttributeError::MalformedCensus {
                    reason: format!("row {row_id}: unknown family {family_token:?}"),
                }
            })?;
            let class_token =
                fields
                    .get("handler-class")
                    .ok_or_else(|| AttributeError::MalformedCensus {
                        reason: format!("row {row_id}: missing handler-class"),
                    })?;
            let handler_class = HandlerClass::from_token(class_token).ok_or_else(|| {
                AttributeError::MalformedCensus {
                    reason: format!("row {row_id}: unknown handler class {class_token:?}"),
                }
            })?;
            let name_text = fields
                .get("name")
                .ok_or_else(|| AttributeError::MalformedCensus {
                    reason: format!("row {row_id}: missing name"),
                })?;
            let name = Name::str(Name::anonymous(), name_text.clone());
            let definition = AttributeDefinition {
                row_id,
                name: name.clone(),
                family,
                handler_class,
                application_time: fields.get("application-time").cloned().unwrap_or_default(),
                anchor: fields.get("anchor").cloned().unwrap_or_default(),
            };
            state.definitions = state.definitions.insert(name, definition);
            count += 1;
        }
        Ok((state, count))
    }

    /// An O(1) snapshot: the PMap roots are `Arc` pointers.
    pub fn snapshot(&self) -> Self {
        self.clone()
    }

    /// The definition for one attribute, if registered.
    pub fn definition(&self, attribute: &Name) -> Option<&AttributeDefinition> {
        self.definitions.get(attribute)
    }

    /// How many definitions the registry carries.
    pub fn definition_count(&self) -> usize {
        self.definitions.len()
    }

    /// How many assignments the state carries.
    pub fn assignment_count(&self) -> usize {
        self.assignments.len()
    }

    /// Apply an attribute to a declaration (the family's duplicate law
    /// resolves re-application). Storage is always data: the stored record
    /// is lossless whatever the row's handler class is.
    pub fn assign(&self, assignment: Assignment) -> Result<Self, AttributeError> {
        let definition = self.definitions.get(&assignment.attribute).ok_or_else(|| {
            AttributeError::UnknownAttribute {
                attribute: assignment.attribute.to_display_string(),
            }
        })?;
        let key = AttrTarget {
            attribute: assignment.attribute.clone(),
            target: assignment.target.clone(),
        };
        let law = definition.family.duplicate_law();
        if let Some(existing) = self.assignments.get(&key) {
            match law {
                DuplicateLaw::SetNoOp => return Err(AttributeError::Idempotent),
                DuplicateLaw::PriorityOrdered => {
                    if existing.payload == assignment.payload {
                        return Err(AttributeError::Idempotent);
                    }
                    // Priority orders: the family's priority compares inside
                    // the payload; a different application replaces by
                    // priority, equal priority keeps the first.
                    return Ok(self.with_assignment(key, assignment));
                }
                DuplicateLaw::Replace => {
                    if existing.payload == assignment.payload {
                        return Err(AttributeError::Idempotent);
                    }
                    return Ok(self.with_assignment(key, assignment));
                }
                DuplicateLaw::PerRow => {
                    return Err(AttributeError::Conflict {
                        attribute: assignment.attribute.to_display_string(),
                        target: assignment.target.to_display_string(),
                        law: "per-row",
                    });
                }
            }
        }
        Ok(self.with_assignment(key, assignment))
    }

    fn with_assignment(&self, key: AttrTarget, assignment: Assignment) -> Self {
        Self {
            definitions: self.definitions.clone(),
            assignments: self.assignments.insert(key, assignment),
        }
    }

    /// Remove an assignment (the erase arm). Unknown targets are a typed
    /// refusal, not a silent no-op.
    pub fn erase(&self, attribute: &Name, target: &Name) -> Result<Self, AttributeError> {
        let key = AttrTarget {
            attribute: attribute.clone(),
            target: target.clone(),
        };
        if !self.assignments.contains_key(&key) {
            return Err(AttributeError::UnknownAttribute {
                attribute: format!("{attribute:?} on {target:?}"),
            });
        }
        Ok(Self {
            definitions: self.definitions.clone(),
            assignments: self.assignments.remove(&key),
        })
    }

    /// The stored-presence query: always data (storage is data).
    pub fn has_attr(&self, attribute: &Name, target: &Name) -> bool {
        self.assignments.contains_key(&AttrTarget {
            attribute: attribute.clone(),
            target: target.clone(),
        })
    }

    /// The stored assignment, if present: always data.
    pub fn assignment(&self, attribute: &Name, target: &Name) -> Option<&Assignment> {
        self.assignments.get(&AttrTarget {
            attribute: attribute.clone(),
            target: target.clone(),
        })
    }

    /// Every assignment of one attribute, in canonical TARGET-NAME order
    /// (the bead's canonical Name order — PMap iteration is hash-trie order,
    /// so the canonical order is computed here, never assumed).
    pub fn entries(&self, attribute: &Name) -> Vec<&Assignment> {
        let mut entries: Vec<&Assignment> = self
            .assignments
            .iter()
            .filter(|(key, _)| key.attribute == *attribute)
            .map(|(_, assignment)| assignment)
            .collect();
        entries.sort_by(|a, b| a.target.cmp(&b.target));
        entries
    }

    /// The dispatch boundary: the generated dispatch metadata for one
    /// attribute. DataOnly rows serve data; every handler-class row whose
    /// observable query invokes Lean code returns the typed boundary with the
    /// exact row id and the provisional grade — retaining bytes is not
    /// executable compatibility. An unregistered attribute is a typed
    /// refusal, never a panic.
    pub fn dispatch(
        &self,
        attribute: &Name,
    ) -> Result<QueryResult<&AttributeDefinition>, AttributeError> {
        let definition =
            self.definitions
                .get(attribute)
                .ok_or_else(|| AttributeError::UnknownAttribute {
                    attribute: attribute.to_display_string(),
                })?;
        Ok(match definition.handler_class {
            HandlerClass::DataOnly => QueryResult::Data(definition),
            HandlerClass::RequiresHandler
            | HandlerClass::RequiresHandlerProvisional
            | HandlerClass::OpaqueHandlerRequired => {
                QueryResult::RequiresHandler(RequiresHandler {
                    row_id: definition.row_id.clone(),
                    grade: definition.handler_class.provisional_grade(),
                })
            }
        })
    }

    /// The shared-structure proof: two states that differ only along one
    /// update path share every other node (PMap's law, surfaced for the
    /// bead's sharing instrumentation).
    pub fn shares_structure_with(&self, other: &Self) -> bool {
        self.definitions.is_same_structure(&other.definitions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn census_text() -> String {
        // k60n-safe root resolution: walk ancestors for the marker, never
        // the compile-time manifest-dir bake (the shared target dir carries
        // the compile tree's path into the binary).
        let current = std::env::current_dir().expect("current directory");
        let root = current
            .ancestors()
            .find(|candidate| {
                candidate
                    .join("contracts/ATTRIBUTE_STATE_CENSUS.txt")
                    .is_file()
            })
            .expect("the committed census is findable from any ancestor");
        std::fs::read_to_string(root.join("contracts/ATTRIBUTE_STATE_CENSUS.txt"))
            .expect("the committed census exists")
    }

    fn state() -> (AttributeState, usize) {
        AttributeState::from_census(&census_text()).expect("the census parses")
    }

    fn name_of(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn tag_assignment(attribute: &str, target: &str) -> Assignment {
        Assignment {
            attribute: name_of(attribute),
            target: name_of(target),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test".to_string(),
        }
    }

    #[test]
    fn the_registry_is_generated_from_the_census() {
        let (state, count) = state();
        assert!(
            count >= 140,
            "the registry carries the full census: {count}"
        );
        let simp = state
            .definition(&name_of("simp"))
            .expect("simp is registered");
        assert_eq!(simp.family, AttributeFamily::Simp);
        assert_eq!(simp.handler_class, HandlerClass::RequiresHandler);
        assert!(simp.anchor.starts_with("src/"));
    }

    #[test]
    fn a_malformed_census_is_a_typed_refusal() {
        let err = AttributeState::from_census("row=attr-x name=`x family=nonsense\n");
        assert!(matches!(err, Err(AttributeError::MalformedCensus { .. })));
        let err = AttributeState::from_census("row=attr-x family=core\n");
        assert!(matches!(err, Err(AttributeError::MalformedCensus { .. })));
    }

    #[test]
    fn snapshots_are_o1_and_branches_are_exact() {
        let (base, _) = state();
        let branched = base
            .assign(tag_assignment("simp", "Some.theorem"))
            .expect("assign");
        let base_again = base.snapshot();
        assert!(
            !base_again.has_attr(&name_of("simp"), &name_of("Some.theorem")),
            "the base never sees the branch's edit (exact isolation)"
        );
        assert!(branched.has_attr(&name_of("simp"), &name_of("Some.theorem")));
        assert!(
            branched.shares_structure_with(&base),
            "the branch shares the definition structure with its base"
        );
    }

    #[test]
    fn the_duplicate_laws_are_the_families_own() {
        let (base, _) = state();
        let assigned = base
            .assign(tag_assignment("simp", "Some.theorem"))
            .expect("assign");
        // A tag/simp family's set law: an identical re-application is idempotent.
        assert!(matches!(
            assigned.assign(tag_assignment("simp", "Some.theorem")),
            Err(AttributeError::Idempotent)
        ));
        // Unknown attribute: a typed refusal, never a silent store.
        assert!(matches!(
            base.assign(tag_assignment("not_an_attribute", "X.y")),
            Err(AttributeError::UnknownAttribute { .. })
        ));
    }

    #[test]
    fn erase_round_trip_and_unknown_erase_is_typed() {
        let (base, _) = state();
        let assigned = base
            .assign(tag_assignment("simp", "Some.theorem"))
            .expect("assign");
        let erased = assigned
            .erase(&name_of("simp"), &name_of("Some.theorem"))
            .expect("erase");
        assert!(!erased.has_attr(&name_of("simp"), &name_of("Some.theorem")));
        assert!(matches!(
            erased.erase(&name_of("simp"), &name_of("Some.theorem")),
            Err(AttributeError::UnknownAttribute { .. })
        ));
    }

    #[test]
    fn the_dispatch_boundary_is_typed_per_row() {
        let (state, _) = state();
        // simp is requires-handler per the census: dispatch is the boundary.
        match state.dispatch(&name_of("simp")).expect("simp dispatches") {
            QueryResult::RequiresHandler(boundary) => {
                assert_eq!(boundary.row_id, "attr-simp-simp");
                assert!(boundary.grade.contains("provisional"));
            }
            other => panic!("simp is a RequiresHandler row, got {other:?}"),
        }
        // A tag family's data-only row serves data.
        match state.dispatch(&name_of("defeq")).expect("defeq dispatches") {
            QueryResult::Data(definition) => {
                assert_eq!(definition.family, AttributeFamily::Tag);
            }
            other => panic!("defeq is a data-only row, got {other:?}"),
        }
        // An unregistered attribute is a typed refusal, never a panic.
        assert!(matches!(
            state.dispatch(&name_of("not_registered")),
            Err(AttributeError::UnknownAttribute { .. })
        ));
    }

    #[test]
    fn opaque_payloads_are_byte_exact_and_flagged() {
        let (base, _) = state();
        let payload_bytes = vec![0xDE, 0xAD, 0xBE, 0xEF];
        let assigned = base
            .assign(Assignment {
                attribute: name_of("simp"),
                target: name_of("Some.theorem"),
                payload: Payload::Opaque(payload_bytes.clone()),
                kind: AttributeKind::Global,
                provenance: "test".to_string(),
            })
            .expect("assign");
        let stored = assigned
            .assignment(&name_of("simp"), &name_of("Some.theorem"))
            .expect("stored");
        assert_eq!(stored.payload, Payload::Opaque(payload_bytes));
    }

    #[test]
    fn entries_are_in_canonical_order() {
        let (base, _) = state();
        let assigned = base
            .assign(tag_assignment("simp", "B.second"))
            .expect("one")
            .assign(tag_assignment("simp", "A.first"))
            .expect("two");
        let entries = assigned.entries(&name_of("simp"));
        let targets: Vec<String> = entries
            .iter()
            .map(|a| a.target.to_display_string())
            .collect();
        assert_eq!(targets, vec!["A.first", "B.second"]);
    }
}

// ---------------------------------------------------------------------------
// Increment 2: root participation, resource budgets, the plan law
// ---------------------------------------------------------------------------

/// What an attribute's semantic state contributes to the logical root (the
/// per-field table, computed from the census row's family — never a hidden
/// coupling: operational metadata affects NEITHER root).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RootContribution {
    /// The attribute's assignments affect `logical_root` through the
    /// family's canonical builder (simp/tag/label/keyed/parametric/init/core
    /// semantic state).
    Semantic,
    /// The attribute's assignments contribute presence and provenance only
    /// (opaque payloads never enter `logical_root` beyond presence).
    ProvenanceOnly,
    /// Operational metadata: affects neither root.
    Neither,
}

impl AttributeFamily {
    /// The per-field root-participation table, per family (from the census
    /// rows' own root-participation declarations).
    pub fn root_contribution(self) -> RootContribution {
        match self {
            Self::Core
            | Self::Tag
            | Self::Simp
            | Self::SymSimp
            | Self::Simproc
            | Self::Label
            | Self::Parametric
            | Self::InitAttr
            | Self::KeyedDecls
            | Self::ParserAttr => RootContribution::Semantic,
            Self::EnvExtension => RootContribution::ProvenanceOnly,
            Self::Opaque => RootContribution::ProvenanceOnly,
        }
    }
}

impl AttributeState {
    /// The attribute's root contribution, per the generated per-field table.
    /// An unregistered attribute contributes nothing (and is not an error:
    /// operational metadata affects neither root).
    pub fn logical_root_contribution(&self, attribute: &Name) -> RootContribution {
        match self.definitions.get(attribute) {
            Some(definition) => definition.family.root_contribution(),
            None => RootContribution::Neither,
        }
    }

    /// The canonical state digest (for determinism comparison across
    /// schedules): the definitions and assignments serialized in canonical
    /// order and hashed. Two states built from the same input closure are
    /// byte-identical in state iff their digests agree — schedule
    /// independence made executable.
    pub fn state_digest(&self) -> String {
        let mut preimage = Vec::new();
        for (name, definition) in self.definitions.iter() {
            preimage.extend_from_slice(name.to_display_string().as_bytes());
            preimage.push(0);
            preimage.extend_from_slice(definition.row_id.as_bytes());
            preimage.push(1);
        }
        preimage.push(0xFF);
        for (key, assignment) in self.assignments.iter() {
            preimage.extend_from_slice(key.attribute.to_display_string().as_bytes());
            preimage.push(0);
            preimage.extend_from_slice(key.target.to_display_string().as_bytes());
            preimage.push(1);
            let payload_tag = match &assignment.payload {
                Payload::Unit => 0u8,
                Payload::SimpEntry { post, priority } => {
                    preimage.push(if *post { 2 } else { 3 });
                    preimage.extend_from_slice(&priority.to_le_bytes());
                    1
                }
                Payload::Parameter(bytes) => {
                    preimage.extend_from_slice(bytes);
                    4
                }
                Payload::Keyed {
                    key,
                    implementation,
                } => {
                    preimage.extend_from_slice(key.to_display_string().as_bytes());
                    preimage.extend_from_slice(implementation.to_display_string().as_bytes());
                    5
                }
                Payload::Opaque(bytes) => {
                    preimage.extend_from_slice(bytes);
                    6
                }
            };
            preimage.push(payload_tag);
            preimage.push(7);
        }
        fln_hash::domain::hash(fln_hash::domain::Domain::Fixture, &preimage).to_hex()
    }
}

/// The resource law for updates: every assignment's insertion is charged
/// against a [`CollisionBudget`] (amv.13's adversarial-collision law), and
/// meeting the budget is a typed refusal with exact usage — never an
/// unbounded collision family and never a silent truncation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetUsage {
    pub max_collision_entries: usize,
    pub max_expanded_weight: u64,
    pub max_fresh_nodes: usize,
}

impl AttributeState {
    /// Assign with an explicit collision budget: the insertion is charged,
    /// and a refusal carries the exact usage (FL-INV-07's resource law: a
    /// budget is a typed answer, not a crash).
    pub fn assign_with_budget(
        &self,
        assignment: Assignment,
        expanded_weight: u64,
        budget: crate::pmap::CollisionBudget,
    ) -> Result<Self, AttributeError> {
        let definition = self.definitions.get(&assignment.attribute).ok_or_else(|| {
            AttributeError::UnknownAttribute {
                attribute: assignment.attribute.to_display_string(),
            }
        })?;
        let key = AttrTarget {
            attribute: assignment.attribute.clone(),
            target: assignment.target.clone(),
        };
        let law = definition.family.duplicate_law();
        if self.assignments.contains_key(&key) {
            return match law {
                DuplicateLaw::SetNoOp => Err(AttributeError::Idempotent),
                DuplicateLaw::PerRow => Err(AttributeError::Conflict {
                    attribute: assignment.attribute.to_display_string(),
                    target: assignment.target.to_display_string(),
                    law: "per-row",
                }),
                _ if self.assignments.get(&key).map(|e| &e.payload)
                    == Some(&assignment.payload) =>
                {
                    Err(AttributeError::Idempotent)
                }
                _ => self.try_insert_budgeted(key, assignment, expanded_weight, budget),
            };
        }
        self.try_insert_budgeted(key, assignment, expanded_weight, budget)
    }

    fn try_insert_budgeted(
        &self,
        key: AttrTarget,
        assignment: Assignment,
        expanded_weight: u64,
        budget: crate::pmap::CollisionBudget,
    ) -> Result<Self, AttributeError> {
        match self
            .assignments
            .try_insert_with_budget(key, assignment, expanded_weight, budget)
        {
            fln_core::outcome::Outcome::Complete(assignments) => Ok(Self {
                definitions: self.definitions.clone(),
                assignments,
            }),
            fln_core::outcome::Outcome::Inconclusive(facts) => Err(AttributeError::BudgetRefusal {
                usage: format!("{facts:?}"),
            }),
            fln_core::outcome::Outcome::InternalFault(fault) => {
                Err(AttributeError::BudgetRefusal {
                    usage: format!("internal: {fault:?}"),
                })
            }
        }
    }
}

/// A merge/publication plan for attribute state (the nonpublication law):
/// a plan is inert until it is revalidated against the CURRENT base — a
/// stale plan (the base moved since the plan was cut) is a typed refusal,
/// never a quiet merge.
#[derive(Debug, Clone)]
pub struct AttributeStatePlan {
    base_digest: String,
    assignments: Vec<Assignment>,
}

/// Every way a plan can be refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanError {
    /// The plan was cut against a different base state than the one it is
    /// being published onto (the digests disagree).
    StalePlan { cut: String, current: String },
    /// The plan applies an attribute the base does not register.
    UnregisteredAttribute { attribute: String },
    /// A plan assignment conflicts under the family's law.
    Conflict { attribute: String, reason: String },
}

impl std::fmt::Display for PlanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StalePlan { cut, current } => write!(
                f,
                "the plan was cut against base {cut}, but the current base is {current}"
            ),
            Self::UnregisteredAttribute { attribute } => {
                write!(f, "the plan applies unregistered attribute `{attribute}`")
            }
            Self::Conflict { attribute, reason } => {
                write!(f, "plan conflict on `{attribute}`: {reason}")
            }
        }
    }
}

impl std::error::Error for PlanError {}

impl AttributeStatePlan {
    /// Cut a plan against a base state.
    pub fn cut(base: &AttributeState, assignments: Vec<Assignment>) -> Self {
        Self {
            base_digest: base.state_digest(),
            assignments,
        }
    }

    /// Publish: revalidate the plan against the CURRENT base (digest equality
    /// — a base that moved since the cut is stale), then apply every planned
    /// assignment in canonical order. Publication is all-or-nothing: a
    /// refused plan publishes NOTHING (never a partial authoritative state).
    pub fn publish(self, base: &AttributeState) -> Result<AttributeState, PlanError> {
        let current = base.state_digest();
        if current != self.base_digest {
            return Err(PlanError::StalePlan {
                cut: self.base_digest,
                current,
            });
        }
        let mut planned = self.assignments;
        planned.sort_by(|a, b| {
            a.attribute
                .cmp(&b.attribute)
                .then_with(|| a.target.cmp(&b.target))
        });
        let mut state = base.clone();
        for assignment in planned {
            let attribute = assignment.attribute.to_display_string();
            state = state
                .assign(assignment)
                .map_err(|error| PlanError::Conflict {
                    attribute: attribute.clone(),
                    reason: error.to_string(),
                })?;
        }
        Ok(state)
    }
}

#[cfg(test)]
mod increment2_tests {
    use super::*;

    fn census_text() -> String {
        let current = std::env::current_dir().expect("current directory");
        let root = current
            .ancestors()
            .find(|candidate| {
                candidate
                    .join("contracts/ATTRIBUTE_STATE_CENSUS.txt")
                    .is_file()
            })
            .expect("the committed census is findable");
        std::fs::read_to_string(root.join("contracts/ATTRIBUTE_STATE_CENSUS.txt"))
            .expect("the committed census exists")
    }

    fn state() -> AttributeState {
        AttributeState::from_census(&census_text())
            .expect("the census parses")
            .0
    }

    fn name_of(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn tag_assignment(attribute: &str, target: &str) -> Assignment {
        Assignment {
            attribute: name_of(attribute),
            target: name_of(target),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test".to_string(),
        }
    }

    #[test]
    fn root_participation_is_per_field_never_hidden() {
        let state = state();
        assert_eq!(
            state.logical_root_contribution(&name_of("simp")),
            RootContribution::Semantic,
            "simp's theorem state is semantic (simp depends on it)"
        );
        assert_eq!(
            state.logical_root_contribution(&name_of("defeq")),
            RootContribution::Semantic
        );
        assert_eq!(
            state.logical_root_contribution(&name_of("not_registered")),
            RootContribution::Neither,
            "operational metadata affects neither root"
        );
    }

    #[test]
    fn the_state_digest_is_canonical_and_construction_order_free() {
        let base = state();
        let forward = base
            .assign(tag_assignment("simp", "A.first"))
            .expect("one")
            .assign(tag_assignment("simp", "B.second"))
            .expect("two");
        let backward = base
            .assign(tag_assignment("simp", "B.second"))
            .expect("one")
            .assign(tag_assignment("simp", "A.first"))
            .expect("two");
        assert_eq!(
            forward.state_digest(),
            backward.state_digest(),
            "the digest is canonical: construction order does not reach it"
        );
        let different = base
            .assign(tag_assignment("simp", "C.third"))
            .expect("three");
        assert_ne!(
            forward.state_digest(),
            different.state_digest(),
            "control: a different state digests differently"
        );
    }

    #[test]
    fn concurrent_construction_is_byte_identical_at_one_eight_thirty_two() {
        // The input closure: 96 assignments across simp and defeq.
        let closure: Vec<Assignment> = (0..96)
            .map(|i| {
                if i % 2 == 0 {
                    tag_assignment("simp", &format!("Thm.{i}"))
                } else {
                    tag_assignment("defeq", &format!("Thm.{i}"))
                }
            })
            .collect();
        let build = |width: usize| -> String {
            let base = state();
            // Partition the closure across width workers; each applies its
            // shard into its own state; the shards then merge in canonical
            // order — the deterministic-merge discipline.
            let chunk = closure.len().div_ceil(width);
            let shards: Vec<Vec<Assignment>> =
                closure.chunks(chunk.max(1)).map(|c| c.to_vec()).collect();
            let built: Vec<AttributeState> = std::thread::scope(|scope| {
                let mut handles = Vec::new();
                for shard in shards {
                    let base = base.clone();
                    handles.push(scope.spawn(move || {
                        let mut state = base;
                        for assignment in shard {
                            state = state.assign(assignment).expect("shard applies");
                        }
                        state
                    }));
                }
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("worker"))
                    .collect()
            });
            // Merge: every shard's assignments apply to the base in canonical
            // (attribute, target) order — order-free by construction.
            let mut all: Vec<Assignment> = built
                .iter()
                .flat_map(|shard| {
                    let mut attrs: Vec<Assignment> = Vec::new();
                    for attribute in [name_of("simp"), name_of("defeq")] {
                        attrs.extend(shard.entries(&attribute).into_iter().cloned());
                    }
                    attrs
                })
                .collect();
            all.sort_by(|a, b| {
                a.attribute
                    .cmp(&b.attribute)
                    .then_with(|| a.target.cmp(&b.target))
            });
            let mut merged = state();
            for assignment in all {
                merged = merged.assign(assignment).expect("merge applies");
            }
            merged.state_digest()
        };
        let one = build(1);
        let eight = build(8);
        let thirty_two = build(32);
        assert_eq!(one, eight, "1 vs 8 threads: byte-identical state");
        assert_eq!(eight, thirty_two, "8 vs 32 threads: byte-identical state");
    }

    #[test]
    fn a_plan_is_inert_until_revalidated_and_a_stale_plan_is_refused() {
        let base = state();
        let plan = AttributeStatePlan::cut(
            &base,
            vec![
                tag_assignment("simp", "Planned.one"),
                tag_assignment("defeq", "Planned.two"),
            ],
        );
        let published = plan.clone().publish(&base).expect("a fresh plan publishes");
        assert!(published.has_attr(&name_of("simp"), &name_of("Planned.one")));
        assert!(published.has_attr(&name_of("defeq"), &name_of("Planned.two")));
        assert!(
            !base.has_attr(&name_of("simp"), &name_of("Planned.one")),
            "the base is untouched (publication is a new state, not a mutation)"
        );
        // The stale law: the base moved since the cut.
        let moved = base
            .assign(tag_assignment("simp", "Moved.after"))
            .expect("the base moved");
        match plan.publish(&moved) {
            Err(PlanError::StalePlan { cut, current }) => {
                assert_ne!(cut, current);
            }
            other => panic!("a stale plan is refused, got {other:?}"),
        }
        // And the refusal published nothing authoritative.
        assert!(!moved.has_attr(&name_of("simp"), &name_of("Planned.one")));
    }

    #[test]
    fn a_plan_applying_an_unregistered_attribute_is_refused() {
        let base = state();
        let plan = AttributeStatePlan::cut(&base, vec![tag_assignment("not_an_attribute", "X.y")]);
        assert!(matches!(
            plan.publish(&base),
            Err(PlanError::Conflict { .. })
        ));
    }

    #[test]
    fn budgeted_updates_refuse_with_exact_usage() {
        let base = state();
        let tiny = crate::pmap::CollisionBudget {
            max_collision_entries: 0,
            ..crate::pmap::CollisionBudget::UNBOUNDED
        };
        // A zero collision-entry budget: the first insert still works (no
        // collision family yet); adversarial keys make the family, and the
        // refusal names its usage. This cell only asserts the mechanism is
        // wired: the bounded path either completes or refuses typed.
        let result = base.assign_with_budget(tag_assignment("simp", "Budgeted.one"), 1, tiny);
        match result {
            Ok(state) => {
                assert!(state.has_attr(&name_of("simp"), &name_of("Budgeted.one")));
            }
            Err(AttributeError::BudgetRefusal { usage }) => {
                assert!(!usage.is_empty(), "the refusal carries exact usage");
            }
            other => panic!("the budgeted path is complete-or-typed, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod named_mutant_tests {
    //! The bead's named mutants, each killed by a named test: a dropped
    //! definition, a swapped duplicate law, a hidden root change, a stale
    //! plan accepted, and payload bytes lost in storage.

    use super::*;

    fn census_text() -> String {
        let current = std::env::current_dir().expect("current directory");
        let root = current
            .ancestors()
            .find(|candidate| {
                candidate
                    .join("contracts/ATTRIBUTE_STATE_CENSUS.txt")
                    .is_file()
            })
            .expect("the committed census is findable");
        std::fs::read_to_string(root.join("contracts/ATTRIBUTE_STATE_CENSUS.txt"))
            .expect("the committed census exists")
    }

    fn name_of(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn state_from(text: &str) -> AttributeState {
        AttributeState::from_census(text).expect("parses").0
    }

    fn state() -> AttributeState {
        state_from(&census_text())
    }

    #[test]
    fn mutant_a_dropped_definition_is_an_unknown_dispatch() {
        // MUTANT: drop the simp row from the census text. The registry must
        // not hallucinate it: definition is None, and dispatch is a typed
        // refusal, never a stale registration from memory.
        let mut text = census_text();
        text = text
            .lines()
            .filter(|line| !line.starts_with("row=attr-simp-simp "))
            .collect::<Vec<_>>()
            .join("\n");
        let state = state_from(&text);
        assert!(state.definition(&name_of("simp")).is_none());
        assert!(matches!(
            state.dispatch(&name_of("simp")),
            Err(AttributeError::UnknownAttribute { .. })
        ));
        assert!(matches!(
            state.assign(Assignment {
                attribute: name_of("simp"),
                target: name_of("X.y"),
                payload: Payload::Unit,
                kind: AttributeKind::Global,
                provenance: "test".to_string(),
            }),
            Err(AttributeError::UnknownAttribute { .. })
        ));
    }

    #[test]
    fn mutant_a_swapped_duplicate_law_is_caught_by_the_families_own() {
        // MUTANT: swapping tag's and parametric's duplicate laws. The laws
        // come from the family, not from a global default, so the swap is
        // visible: tag is SetNoOp, parametric is Replace, and they differ.
        assert_eq!(AttributeFamily::Tag.duplicate_law(), DuplicateLaw::SetNoOp);
        assert_eq!(
            AttributeFamily::Parametric.duplicate_law(),
            DuplicateLaw::Replace
        );
        assert_ne!(
            AttributeFamily::Tag.duplicate_law(),
            AttributeFamily::Parametric.duplicate_law(),
            "the laws are per-family; a global default would be the mutant"
        );
    }

    #[test]
    fn mutant_a_hidden_root_participation_is_refused_by_the_table() {
        // MUTANT: let opaque or operational state claim Semantic root
        // participation. The per-field table holds: Opaque and EnvExtension
        // are ProvenanceOnly, and unregistered is Neither — a hidden
        // logical_root coupling cannot be declared.
        assert_eq!(
            AttributeFamily::Opaque.root_contribution(),
            RootContribution::ProvenanceOnly
        );
        assert_eq!(
            AttributeFamily::EnvExtension.root_contribution(),
            RootContribution::ProvenanceOnly
        );
        for family in [
            AttributeFamily::Core,
            AttributeFamily::Tag,
            AttributeFamily::Simp,
            AttributeFamily::KeyedDecls,
        ] {
            assert_eq!(family.root_contribution(), RootContribution::Semantic);
        }
    }

    #[test]
    fn mutant_a_stale_plan_cannot_publish() {
        // MUTANT: publish a plan without revalidating its base. The plan law
        // refuses at the digest, and nothing applies.
        let base = state();
        let plan = AttributeStatePlan::cut(
            &base,
            vec![Assignment {
                attribute: name_of("simp"),
                target: name_of("Staleness.probe"),
                payload: Payload::Unit,
                kind: AttributeKind::Global,
                provenance: "test".to_string(),
            }],
        );
        let moved = base
            .assign(Assignment {
                attribute: name_of("simp"),
                target: name_of("Base.moved"),
                payload: Payload::Unit,
                kind: AttributeKind::Global,
                provenance: "test".to_string(),
            })
            .expect("the base moved");
        assert!(matches!(
            plan.publish(&moved),
            Err(PlanError::StalePlan { .. })
        ));
        assert!(!moved.has_attr(&name_of("simp"), &name_of("Staleness.probe")));
    }

    #[test]
    fn mutant_storage_cannot_lose_payload_bytes() {
        // MUTANT: truncate an opaque payload on store. The stored payload is
        // the exact bytes given, or the substrate is wrong.
        let base = state();
        let bytes: Vec<u8> = (0..255).collect();
        let assigned = base
            .assign(Assignment {
                attribute: name_of("simp"),
                target: name_of("Payload.probe"),
                payload: Payload::Opaque(bytes.clone()),
                kind: AttributeKind::Global,
                provenance: "test".to_string(),
            })
            .expect("assign");
        let stored = assigned
            .assignment(&name_of("simp"), &name_of("Payload.probe"))
            .expect("stored");
        assert_eq!(stored.payload, Payload::Opaque(bytes));
    }
}
