//! Parser recovery without a second acceptance authority (plan §9.3; bead
//! `franken_lean-7xw`).
//!
//! Recovery is useful to an editor only if it can continue past a malformed
//! command. It is dangerous to a prover if the repaired product can be confused
//! with the command that decides acceptance. This module therefore keeps two
//! products with deliberately different types:
//!
//! * [`AuthoritativeCommandStream`] contains the result of the exact command
//!   parser the session was opened with ([`crate::parse_nat_definition`] or
//!   [`crate::parse_definition`]). Recovery mode never changes this value.
//! * [`SpeculativeBoundaryMap`] and [`RecoveredSyntax`] are editor-only
//!   observations. They can drive diagnostics and completion, but expose no
//!   conversion to [`crate::ParsedNatDefinition`].
//!
//! [`RecoverySession::publication_candidate`] is the single bridge toward
//! publication. It checks the session generation, grammar epoch, authoritative
//! verdict, and absence of recovered syntax. A speculative boundary therefore
//! cannot become a declaration by being mistaken for a successful parse.

use crate::registry::{EpochSyntax, GrammarEpoch, Registry};
use crate::{
    NatDefinitionParseError, ParsedDefinition, ParsedNatDefinition, parse_definition,
    parse_nat_definition,
};

type CommandParser = fn(&[u8]) -> Result<ParsedDefinition, NatDefinitionParseError>;
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_syntax::run::{Damage, Event, LexBudget, LexRun, lex_run_bounded, relex_incremental};
use fln_syntax::source::{BytePos, ByteSpan, SourceError, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;
use std::collections::{BTreeMap, BTreeSet};

const PARSER_CATEGORY_INVENTORY: &str = include_str!("../fixtures/PARSER_CATEGORY_INVENTORY.txt");

/// Whether the editor-only recovery product is requested.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryMode {
    Disabled,
    Enabled,
}

/// One token at which a category-specific recovery parser may resume.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResynchronizationToken {
    Symbol(String),
    Identifier(Name),
}

/// A category's explicit recovery contract.
///
/// There is intentionally no default or catch-all specification. A category
/// without an audited resynchronization set must be refused by the caller
/// rather than silently inheriting command recovery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoverySpec {
    category: Name,
    marker_kind: Name,
    resynchronization: Vec<ResynchronizationToken>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecoverySpecError {
    AnonymousCategory,
    AnonymousMarkerKind,
    EmptyResynchronizationSet,
    DuplicateResynchronizationToken(ResynchronizationToken),
}

impl RecoverySpec {
    pub fn new(
        category: Name,
        marker_kind: Name,
        mut resynchronization: Vec<ResynchronizationToken>,
    ) -> Result<RecoverySpec, RecoverySpecError> {
        if category.is_anonymous() {
            return Err(RecoverySpecError::AnonymousCategory);
        }
        if marker_kind.is_anonymous() {
            return Err(RecoverySpecError::AnonymousMarkerKind);
        }
        if resynchronization.is_empty() {
            return Err(RecoverySpecError::EmptyResynchronizationSet);
        }
        resynchronization.sort();
        for pair in resynchronization.windows(2) {
            if pair[0] == pair[1] {
                return Err(RecoverySpecError::DuplicateResynchronizationToken(
                    pair[0].clone(),
                ));
            }
        }
        Ok(RecoverySpec {
            category,
            marker_kind,
            resynchronization,
        })
    }

    pub fn category(&self) -> &Name {
        &self.category
    }

    pub fn marker_kind(&self) -> &Name {
        &self.marker_kind
    }

    pub fn resynchronization(&self) -> &[ResynchronizationToken] {
        &self.resynchronization
    }
}

/// Why an exact recovery-policy catalog could not be built.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecoveryCatalogError {
    MalformedInventoryRow { line: usize },
    DuplicateInventoryCategory(Name),
    DuplicateSpecification(Name),
    MissingSpecifications(Vec<Name>),
    UnexpectedSpecifications(Vec<Name>),
}

/// Recovery policies covering exactly the parser categories at the pinned
/// Reference epoch.
///
/// The category inventory is generated and independently re-derived by
/// `parser_category_inventory`. This type binds policies to that authority:
/// construction refuses a missing row and also refuses a policy for a category
/// the inventory does not contain. There is no fallback lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveryCatalog {
    specifications: BTreeMap<Name, RecoverySpec>,
}

fn inventory_category_name(spelling: &str) -> Name {
    Name::str(Name::anonymous(), spelling)
}

/// Parse the governed category inventory embedded in this build.
pub fn pinned_parser_categories() -> Result<Vec<Name>, RecoveryCatalogError> {
    let mut categories = BTreeSet::new();
    for (index, raw) in PARSER_CATEGORY_INVENTORY.lines().enumerate() {
        let row = raw.trim();
        if row.is_empty() || row.starts_with('#') {
            continue;
        }
        let fields = row.split_whitespace().collect::<Vec<_>>();
        let category = match fields.as_slice() {
            ["builtin", name, behavior] if matches!(*behavior, "default" | "symbol" | "both") => {
                inventory_category_name(name)
            }
            ["declared", name] => inventory_category_name(name),
            _ => {
                return Err(RecoveryCatalogError::MalformedInventoryRow { line: index + 1 });
            }
        };
        if !categories.insert(category.clone()) {
            return Err(RecoveryCatalogError::DuplicateInventoryCategory(category));
        }
    }
    Ok(categories.into_iter().collect())
}

impl RecoveryCatalog {
    pub fn for_pinned_categories(
        specifications: Vec<RecoverySpec>,
    ) -> Result<RecoveryCatalog, RecoveryCatalogError> {
        let required = pinned_parser_categories()?
            .into_iter()
            .collect::<BTreeSet<_>>();
        let mut by_category = BTreeMap::new();
        for specification in specifications {
            let category = specification.category.clone();
            if by_category
                .insert(category.clone(), specification)
                .is_some()
            {
                return Err(RecoveryCatalogError::DuplicateSpecification(category));
            }
        }
        let supplied = by_category.keys().cloned().collect::<BTreeSet<_>>();
        let missing = required.difference(&supplied).cloned().collect::<Vec<_>>();
        if !missing.is_empty() {
            return Err(RecoveryCatalogError::MissingSpecifications(missing));
        }
        let unexpected = supplied.difference(&required).cloned().collect::<Vec<_>>();
        if !unexpected.is_empty() {
            return Err(RecoveryCatalogError::UnexpectedSpecifications(unexpected));
        }
        Ok(RecoveryCatalog {
            specifications: by_category,
        })
    }

    pub fn get(&self, category: &Name) -> Option<&RecoverySpec> {
        self.specifications.get(category)
    }

    pub fn categories(&self) -> impl ExactSizeIterator<Item = &Name> {
        self.specifications.keys()
    }

    pub fn len(&self) -> usize {
        self.specifications.len()
    }

    pub fn is_empty(&self) -> bool {
        self.specifications.is_empty()
    }
}

/// The category served by the first source-to-parser command seam.
pub fn command_category() -> Name {
    inventory_category_name("command")
}

/// The explicit recovery specification for the first command seam.
pub fn nat_definition_recovery_spec() -> RecoverySpec {
    RecoverySpec::new(
        command_category(),
        Name::from_components(["Lean", "Parser", "Command", "recovered"]),
        vec![ResynchronizationToken::Symbol("def".to_string())],
    )
    .expect("the built-in command recovery specification is structurally valid")
}

/// Work limits for one recovery session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecoveryBudget {
    pub lex: LexBudget,
    pub max_boundaries: u64,
    pub max_recovered_nodes: u64,
}

impl RecoveryBudget {
    pub const fn generous() -> RecoveryBudget {
        RecoveryBudget {
            lex: LexBudget::generous(),
            max_boundaries: 4 * 1024 * 1024,
            max_recovered_nodes: 4 * 1024 * 1024,
        }
    }
}

/// Stable cancellation points. A cancellation is a non-answer and publishes no
/// partial session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryCheckpoint {
    BeforeLex,
    Event { processed: u64 },
    BeforePublication { processed: u64 },
}

/// One command boundary in the parser's normalized coordinate system.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CommandBoundary {
    span: ByteSpan,
    epoch: GrammarEpoch,
}

impl CommandBoundary {
    pub const fn span(self) -> ByteSpan {
        self.span
    }

    pub const fn epoch(self) -> GrammarEpoch {
        self.epoch
    }
}

/// The sole semantic authority for the seed command parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthoritativeCommandStream {
    result: Result<ParsedNatDefinition, NatDefinitionParseError>,
    boundaries: Vec<CommandBoundary>,
}

impl AuthoritativeCommandStream {
    pub fn accepted(&self) -> bool {
        self.result.is_ok()
    }

    pub fn result(&self) -> &Result<ParsedNatDefinition, NatDefinitionParseError> {
        &self.result
    }

    pub fn boundaries(&self) -> &[CommandBoundary] {
        &self.boundaries
    }
}

/// Provenance attached to every repaired syntax product.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveryMarker {
    id: u64,
    category: Name,
    span: ByteSpan,
    epoch: GrammarEpoch,
}

impl RecoveryMarker {
    pub const fn id(&self) -> u64 {
        self.id
    }

    pub fn category(&self) -> &Name {
        &self.category
    }

    pub const fn span(&self) -> ByteSpan {
        self.span
    }

    pub const fn epoch(&self) -> GrammarEpoch {
        self.epoch
    }
}

/// An editor-only repaired syntax product.
///
/// The epoch-bound syntax is private on purpose. Consumers may inspect its
/// provenance and use its span for diagnostics, but cannot extract a raw
/// [`Syntax`] and feed it to an elaboration API.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveredSyntax {
    marker: RecoveryMarker,
    syntax: EpochSyntax,
}

impl RecoveredSyntax {
    pub fn marker(&self) -> &RecoveryMarker {
        &self.marker
    }

    pub fn is_epoch_bound(&self) -> bool {
        self.syntax.all_nodes_belong_to(self.marker.epoch)
    }
}

/// One editor-only candidate command boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpeculativeObservation {
    AcceptedCommandShape,
    RejectedCommandShape(NatDefinitionParseError),
}

/// One editor-only candidate command boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpeculativeBoundary {
    span: ByteSpan,
    epoch: GrammarEpoch,
    observation: SpeculativeObservation,
}

impl SpeculativeBoundary {
    pub const fn span(&self) -> ByteSpan {
        self.span
    }

    pub const fn epoch(&self) -> GrammarEpoch {
        self.epoch
    }

    pub fn observation(&self) -> &SpeculativeObservation {
        &self.observation
    }
}

/// The boundary product a scheduler or editor may use for continued work.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SpeculativeBoundaryMap {
    boundaries: Vec<SpeculativeBoundary>,
}

impl SpeculativeBoundaryMap {
    pub fn boundaries(&self) -> &[SpeculativeBoundary] {
        &self.boundaries
    }
}

/// A disagreement record retains both products and their source extent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveryJournalEntry {
    authoritative: Vec<CommandBoundary>,
    speculative: Vec<SpeculativeBoundary>,
    disagreement_span: ByteSpan,
    markers: Vec<RecoveryMarker>,
}

impl RecoveryJournalEntry {
    pub fn authoritative(&self) -> &[CommandBoundary] {
        &self.authoritative
    }

    pub fn speculative(&self) -> &[SpeculativeBoundary] {
        &self.speculative
    }

    pub const fn disagreement_span(&self) -> ByteSpan {
        self.disagreement_span
    }

    pub fn markers(&self) -> &[RecoveryMarker] {
        &self.markers
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecoveryError {
    CategoryMismatch {
        expected: Name,
        actual: Name,
    },
    StaleBaseGeneration {
        session: u64,
        supplied: u64,
    },
    NonMonotonicGeneration {
        base: u64,
        next: u64,
    },
    StaleGrammarEpoch {
        session: GrammarEpoch,
        supplied: GrammarEpoch,
    },
    ForeignGrammarEpoch {
        supplied: GrammarEpoch,
    },
    InvalidNormalizedEdit {
        replaced: ByteSpan,
        old_len: usize,
        inserted_len: usize,
        new_len: usize,
    },
    IncrementalRestartRequired(IncrementalRestartReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncrementalRestartReason {
    BaseHasNoLexicalSnapshot,
    NewSourceIsNotUtf8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublicationRefusal {
    StaleGeneration {
        session: u64,
        expected: u64,
    },
    EpochMismatch {
        product: GrammarEpoch,
        expected: GrammarEpoch,
    },
    AuthoritativeRejected,
    UnacknowledgedRecovery {
        markers: usize,
    },
}

/// Capability produced only after the publication checks succeed.
#[derive(Debug, Clone, Copy)]
pub struct PublicationCandidate<'a> {
    parsed: &'a ParsedNatDefinition,
    generation: u64,
    epoch: GrammarEpoch,
}

/// One editor edit, expressed in the old parser-visible coordinate system.
///
/// `inserted_len` is the length after CRLF normalization. Keeping that unit in
/// the type name and docs avoids silently mixing an LSP/original byte span with
/// the lexer's coordinate system.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NormalizedRecoveryEdit {
    pub base_generation: u64,
    pub next_generation: u64,
    pub base_registry_epoch: GrammarEpoch,
    pub replaced: ByteSpan,
    pub inserted_len: usize,
}

/// All policy and authority inputs for one incremental recovery transaction.
pub struct IncrementalRecoveryRequest<'a> {
    pub edit: NormalizedRecoveryEdit,
    pub registry: &'a Registry,
    pub spec: &'a RecoverySpec,
    pub mode: RecoveryMode,
    pub budget: RecoveryBudget,
    pub cancellation: Option<&'a dyn Fn(RecoveryCheckpoint) -> bool>,
}

/// How much of the editor-only candidate parse map was reused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundaryDamage {
    pub reused_prefix: usize,
    pub reparsed: usize,
}

impl BoundaryDamage {
    pub const fn total_boundaries(self) -> usize {
        self.reused_prefix + self.reparsed
    }

    pub const fn reused_anything(self) -> bool {
        self.reused_prefix > 0
    }
}

/// An incremental session whose lexical and candidate products were checked
/// against a full reconstruction before being returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedIncrementalRecovery {
    session: RecoverySession,
    lexical_damage: Damage,
    boundary_damage: BoundaryDamage,
}

impl VerifiedIncrementalRecovery {
    pub fn session(&self) -> &RecoverySession {
        &self.session
    }

    pub const fn lexical_damage(&self) -> Damage {
        self.lexical_damage
    }

    pub const fn boundary_damage(&self) -> BoundaryDamage {
        self.boundary_damage
    }

    pub fn into_session(self) -> RecoverySession {
        self.session
    }
}

impl<'a> PublicationCandidate<'a> {
    pub const fn parsed(self) -> &'a ParsedNatDefinition {
        self.parsed
    }

    pub const fn generation(self) -> u64 {
        self.generation
    }

    pub const fn epoch(self) -> GrammarEpoch {
        self.epoch
    }
}

/// One atomically produced recovery observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoverySession {
    generation: u64,
    registry_epoch: GrammarEpoch,
    mode: RecoveryMode,
    recovery_spec: Option<RecoverySpec>,
    source_view: Option<SourceView>,
    lexical_run: Option<LexRun>,
    authoritative: AuthoritativeCommandStream,
    speculative: Option<SpeculativeBoundaryMap>,
    recovered: Vec<RecoveredSyntax>,
    journal: Vec<RecoveryJournalEntry>,
}

impl RecoverySession {
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    pub const fn mode(&self) -> RecoveryMode {
        self.mode
    }

    pub const fn registry_epoch(&self) -> GrammarEpoch {
        self.registry_epoch
    }

    pub fn recovery_spec(&self) -> Option<&RecoverySpec> {
        self.recovery_spec.as_ref()
    }

    pub fn source_view(&self) -> Option<&SourceView> {
        self.source_view.as_ref()
    }

    pub fn lexical_run(&self) -> Option<&LexRun> {
        self.lexical_run.as_ref()
    }

    pub fn authoritative(&self) -> &AuthoritativeCommandStream {
        &self.authoritative
    }

    pub fn speculative(&self) -> Option<&SpeculativeBoundaryMap> {
        self.speculative.as_ref()
    }

    pub fn recovered(&self) -> &[RecoveredSyntax] {
        &self.recovered
    }

    pub fn journal(&self) -> &[RecoveryJournalEntry] {
        &self.journal
    }

    /// Admit only the exact parser's accepted product under the same session and
    /// grammar identity. Recovered syntax remains editor-only even if a caller
    /// has inspected and acknowledged its diagnostics.
    pub fn publication_candidate(
        &self,
        expected_generation: u64,
        expected_epoch: GrammarEpoch,
    ) -> Result<PublicationCandidate<'_>, PublicationRefusal> {
        if self.generation != expected_generation {
            return Err(PublicationRefusal::StaleGeneration {
                session: self.generation,
                expected: expected_generation,
            });
        }
        let product_epoch = self
            .authoritative
            .boundaries
            .first()
            .map_or(expected_epoch, |boundary| boundary.epoch);
        if product_epoch != expected_epoch {
            return Err(PublicationRefusal::EpochMismatch {
                product: product_epoch,
                expected: expected_epoch,
            });
        }
        let parsed = self
            .authoritative
            .result
            .as_ref()
            .map_err(|_| PublicationRefusal::AuthoritativeRejected)?;
        if !self.recovered.is_empty() {
            return Err(PublicationRefusal::UnacknowledgedRecovery {
                markers: self.recovered.len(),
            });
        }
        Ok(PublicationCandidate {
            parsed,
            generation: self.generation,
            epoch: product_epoch,
        })
    }
}

fn exhausted<T>(unit: StructuralUnit, allowed: u64, observed: u64) -> Outcome<T> {
    Outcome::Inconclusive(Inconclusive::resource(ResourceUsage {
        reason: ResourceReason::StructuralBudget { unit },
        allowed,
        observed,
    }))
}

fn cancelled<T>(checkpoint: RecoveryCheckpoint) -> Outcome<T> {
    Outcome::Inconclusive(Inconclusive::cancelled(format!(
        "Vellum recovery at {checkpoint:?}"
    )))
}

fn cancellation_requested(
    cancellation: Option<&dyn Fn(RecoveryCheckpoint) -> bool>,
    checkpoint: RecoveryCheckpoint,
) -> bool {
    cancellation.is_some_and(|cancel| cancel(checkpoint))
}

fn token_matches(spec: &RecoverySpec, token: &LexedToken) -> bool {
    spec.resynchronization
        .iter()
        .any(|resynchronization| match (resynchronization, &token.kind) {
            (ResynchronizationToken::Symbol(expected), TokenKind::Symbol(actual)) => {
                expected == actual
            }
            (ResynchronizationToken::Identifier(expected), TokenKind::Ident(actual)) => {
                expected == actual
            }
            _ => false,
        })
}

fn normalized_error_position(error: &NatDefinitionParseError, view: &SourceView) -> BytePos {
    let original = match error {
        NatDefinitionParseError::Source(SourceError::NotUtf8 { at }) => *at,
        NatDefinitionParseError::Lexical { diagnostics } => diagnostics
            .first()
            .map_or(BytePos(view.original_len_bytes()), |diagnostic| {
                diagnostic.at
            }),
        NatDefinitionParseError::OutsideSeedGrammar { at, .. } => *at,
        NatDefinitionParseError::Build(_) => BytePos(view.original_len_bytes()),
    };
    view.from_original(original)
        .unwrap_or(BytePos(view.normalized().len_bytes()))
}

fn make_boundaries(
    run: &LexRun,
    view: &SourceView,
    registry: &Registry,
    spec: &RecoverySpec,
    parse: CommandParser,
) -> Vec<SpeculativeBoundary> {
    let mut starts = run
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Token(token) if token_matches(spec, token) => Some(token.extent.start()),
            Event::Trivia(_) | Event::Token(_) | Event::Refused { .. } => None,
        })
        .collect::<Vec<_>>();
    starts.sort_unstable();
    starts.dedup();
    starts
        .iter()
        .copied()
        .zip(
            starts
                .iter()
                .copied()
                .skip(1)
                .chain(std::iter::once(BytePos(view.normalized().len_bytes()))),
        )
        .filter_map(|(start, stop)| {
            let span = ByteSpan::new(start, stop)?;
            // A lexer-derived span of the same normalized text is always a
            // valid substring. A miss is a SourceText invariant break, not
            // invalid UTF-8; omitting the speculative slice is honest.
            let candidate = view.normalized().span_str(span)?;
            let observation = match parse(candidate.as_bytes()) {
                Ok(_) => SpeculativeObservation::AcceptedCommandShape,
                Err(error) => SpeculativeObservation::RejectedCommandShape(
                    error.rebase_from_normalized_slice(view, start),
                ),
            };
            Some(SpeculativeBoundary {
                span,
                epoch: registry.epoch_at_position(start),
                observation,
            })
        })
        .collect()
}

fn whole_span(view: &SourceView) -> ByteSpan {
    ByteSpan::new(BytePos(0), BytePos(view.normalized().len_bytes()))
        .expect("a source length is never before zero")
}

fn invalid_utf8_session(
    source: &[u8],
    generation: u64,
    registry: &Registry,
    spec: &RecoverySpec,
    mode: RecoveryMode,
    parse: CommandParser,
) -> RecoverySession {
    RecoverySession {
        generation,
        registry_epoch: registry.epoch(),
        mode,
        recovery_spec: (mode == RecoveryMode::Enabled).then_some(spec.clone()),
        source_view: None,
        lexical_run: None,
        authoritative: AuthoritativeCommandStream {
            result: parse(source),
            boundaries: Vec::new(),
        },
        speculative: None,
        recovered: Vec::new(),
        journal: Vec::new(),
    }
}

/// Recover a Nat-only command. The authoritative verdict is exactly
/// [`crate::parse_nat_definition`]; String and mixed Scalar source stay outside
/// that grammar.
pub fn parse_nat_definition_recovering(
    source: &[u8],
    generation: u64,
    registry: &Registry,
    spec: &RecoverySpec,
    mode: RecoveryMode,
    budget: RecoveryBudget,
    cancellation: Option<&dyn Fn(RecoveryCheckpoint) -> bool>,
) -> Outcome<Result<RecoverySession, RecoveryError>> {
    parse_command_recovering(
        parse_nat_definition,
        source,
        generation,
        registry,
        spec,
        mode,
        budget,
        cancellation,
    )
}

/// Recover a bounded Nat/String command. The authoritative verdict is exactly
/// [`crate::parse_definition`]. A String literal that the Nat-only door refuses
/// is an accepted command here.
pub fn parse_definition_recovering(
    source: &[u8],
    generation: u64,
    registry: &Registry,
    spec: &RecoverySpec,
    mode: RecoveryMode,
    budget: RecoveryBudget,
    cancellation: Option<&dyn Fn(RecoveryCheckpoint) -> bool>,
) -> Outcome<Result<RecoverySession, RecoveryError>> {
    parse_command_recovering(
        parse_definition,
        source,
        generation,
        registry,
        spec,
        mode,
        budget,
        cancellation,
    )
}

/// Run one exact command parser with an optional, non-authoritative recovery
/// observation.
///
/// Coordinates in the returned boundary products name the normalized
/// [`SourceView`]. The exact parser's diagnostics remain mapped to the original
/// bytes, preserving its existing public contract. The extra argument is the
/// exact parser; public wrappers keep the original seven-argument surface.
#[allow(clippy::too_many_arguments)]
fn parse_command_recovering(
    parse: CommandParser,
    source: &[u8],
    generation: u64,
    registry: &Registry,
    spec: &RecoverySpec,
    mode: RecoveryMode,
    budget: RecoveryBudget,
    cancellation: Option<&dyn Fn(RecoveryCheckpoint) -> bool>,
) -> Outcome<Result<RecoverySession, RecoveryError>> {
    if spec.category != command_category() {
        return Outcome::Complete(Err(RecoveryError::CategoryMismatch {
            expected: command_category(),
            actual: spec.category.clone(),
        }));
    }
    if cancellation_requested(cancellation, RecoveryCheckpoint::BeforeLex) {
        return cancelled(RecoveryCheckpoint::BeforeLex);
    }
    if source.len() as u64 > budget.lex.max_input_bytes {
        return exhausted(
            StructuralUnit::InputBytes,
            budget.lex.max_input_bytes,
            source.len() as u64,
        );
    }

    let original = match SourceText::from_utf8(source) {
        Ok(original) => original,
        Err(SourceError::NotUtf8 { .. }) => {
            return Outcome::Complete(Ok(invalid_utf8_session(
                source, generation, registry, spec, mode, parse,
            )));
        }
    };
    let view = SourceView::of(&original);
    let table = TokenTable::from_tokens(["def", ":="]);
    let run = match lex_run_bounded(view.normalized(), &table, budget.lex) {
        Outcome::Complete(run) => run,
        Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    };

    let mut processed = 0u64;
    for _ in &run.events {
        if cancellation_requested(cancellation, RecoveryCheckpoint::Event { processed }) {
            return cancelled(RecoveryCheckpoint::Event { processed });
        }
        processed += 1;
    }

    let result = parse(source);
    let exact_boundaries = if result.is_ok() {
        vec![CommandBoundary {
            span: whole_span(&view),
            epoch: registry.epoch_at_position(BytePos(0)),
        }]
    } else {
        Vec::new()
    };
    let authoritative = AuthoritativeCommandStream {
        result,
        boundaries: exact_boundaries,
    };

    let mut speculative = None;
    let mut recovered = Vec::new();
    let mut journal = Vec::new();
    if mode == RecoveryMode::Enabled {
        let boundaries = make_boundaries(&run, &view, registry, spec, parse);
        if boundaries.len() as u64 > budget.max_boundaries {
            return exhausted(
                StructuralUnit::ProducedNodes,
                budget.max_boundaries,
                boundaries.len() as u64,
            );
        }

        if let Err(error) = &authoritative.result {
            let at = normalized_error_position(error, &view);
            let fallback = boundaries
                .iter()
                .find(|boundary| boundary.span.start() <= at && at <= boundary.span.end())
                .map_or(ByteSpan::empty_at(at), |boundary| boundary.span);
            let mut repaired_spans = boundaries
                .iter()
                .filter_map(|boundary| {
                    matches!(
                        &boundary.observation,
                        SpeculativeObservation::RejectedCommandShape(_)
                    )
                    .then_some(boundary.span)
                })
                .collect::<Vec<_>>();
            if repaired_spans.is_empty() && boundaries.is_empty() {
                repaired_spans.push(fallback);
            }
            if repaired_spans.len() as u64 > budget.max_recovered_nodes {
                return exhausted(
                    StructuralUnit::ProducedNodes,
                    budget.max_recovered_nodes,
                    repaired_spans.len() as u64,
                );
            }
            for (id, span) in repaired_spans.into_iter().enumerate() {
                let epoch = registry.epoch_at_position(span.start());
                let marker = RecoveryMarker {
                    id: id as u64,
                    category: spec.category.clone(),
                    span,
                    epoch,
                };
                recovered.push(RecoveredSyntax {
                    marker: marker.clone(),
                    syntax: EpochSyntax::bind_uniform(
                        Syntax::node(spec.marker_kind.clone(), vec![Syntax::Missing]),
                        epoch,
                    ),
                });
            }
            journal.push(RecoveryJournalEntry {
                authoritative: authoritative.boundaries.clone(),
                speculative: boundaries.clone(),
                disagreement_span: whole_span(&view),
                markers: recovered
                    .iter()
                    .map(|syntax| syntax.marker.clone())
                    .collect(),
            });
        } else {
            let boundary_products_agree =
                authoritative.boundaries.len() == boundaries.len()
                    && authoritative.boundaries.iter().zip(&boundaries).all(
                        |(exact, candidate)| {
                            exact.span == candidate.span && exact.epoch == candidate.epoch
                        },
                    );
            if !boundary_products_agree {
                journal.push(RecoveryJournalEntry {
                    authoritative: authoritative.boundaries.clone(),
                    speculative: boundaries.clone(),
                    disagreement_span: whole_span(&view),
                    markers: Vec::new(),
                });
            }
        }
        speculative = Some(SpeculativeBoundaryMap { boundaries });
    }

    let checkpoint = RecoveryCheckpoint::BeforePublication { processed };
    if cancellation_requested(cancellation, checkpoint) {
        return cancelled(checkpoint);
    }
    Outcome::Complete(Ok(RecoverySession {
        generation,
        registry_epoch: registry.epoch(),
        mode,
        recovery_spec: (mode == RecoveryMode::Enabled).then_some(spec.clone()),
        source_view: Some(view),
        lexical_run: Some(run),
        authoritative,
        speculative,
        recovered,
        journal,
    }))
}

fn normalized_edit_is_exact(
    old: &SourceText,
    new: &SourceText,
    edit: NormalizedRecoveryEdit,
) -> bool {
    if edit.replaced.end().0 > old.len_bytes() {
        return false;
    }
    let Some(expected_new_len) = old
        .len_bytes()
        .checked_sub(edit.replaced.len_bytes())
        .and_then(|retained| retained.checked_add(edit.inserted_len))
    else {
        return false;
    };
    if expected_new_len != new.len_bytes() {
        return false;
    }
    let Some(new_suffix_start) = edit.replaced.start().0.checked_add(edit.inserted_len) else {
        return false;
    };
    let Some(old_prefix) =
        ByteSpan::new(BytePos(0), edit.replaced.start()).and_then(|span| old.span_str(span))
    else {
        return false;
    };
    let Some(new_prefix) =
        ByteSpan::new(BytePos(0), edit.replaced.start()).and_then(|span| new.span_str(span))
    else {
        return false;
    };
    let Some(old_suffix) = ByteSpan::new(edit.replaced.end(), BytePos(old.len_bytes()))
        .and_then(|span| old.span_str(span))
    else {
        return false;
    };
    let Some(new_suffix) = ByteSpan::new(BytePos(new_suffix_start), BytePos(new.len_bytes()))
        .and_then(|span| new.span_str(span))
    else {
        return false;
    };
    old_prefix == new_prefix && old_suffix == new_suffix
}

fn incremental_fault<T>(detail: &'static str) -> Outcome<T> {
    Outcome::InternalFault(InternalFault::new("FL-INV-01", detail))
}

/// Apply one normalized edit to a recovery session.
///
/// The lexer result is produced by [`relex_incremental`]. Candidate command
/// observations wholly before the edit are reused when their span and grammar
/// epoch still match; every other candidate is reparsed. This early
/// implementation also builds a full session and compares both products before
/// returning. That deliberately spends extra work to make the incremental
/// equivalence a production invariant while the Vellum seam is still young.
pub fn reparse_nat_definition_incremental(
    previous: &RecoverySession,
    new_source: &[u8],
    request: IncrementalRecoveryRequest<'_>,
) -> Outcome<Result<VerifiedIncrementalRecovery, RecoveryError>> {
    reparse_command_incremental(parse_nat_definition, previous, new_source, request)
}

/// Incremental recovery using [`crate::parse_definition`] as the exact parser.
pub fn reparse_definition_incremental(
    previous: &RecoverySession,
    new_source: &[u8],
    request: IncrementalRecoveryRequest<'_>,
) -> Outcome<Result<VerifiedIncrementalRecovery, RecoveryError>> {
    reparse_command_incremental(parse_definition, previous, new_source, request)
}

fn reparse_command_incremental(
    parse: CommandParser,
    previous: &RecoverySession,
    new_source: &[u8],
    request: IncrementalRecoveryRequest<'_>,
) -> Outcome<Result<VerifiedIncrementalRecovery, RecoveryError>> {
    let IncrementalRecoveryRequest {
        edit,
        registry,
        spec,
        mode,
        budget,
        cancellation,
    } = request;
    if previous.generation != edit.base_generation {
        return Outcome::Complete(Err(RecoveryError::StaleBaseGeneration {
            session: previous.generation,
            supplied: edit.base_generation,
        }));
    }
    if edit.next_generation <= edit.base_generation {
        return Outcome::Complete(Err(RecoveryError::NonMonotonicGeneration {
            base: edit.base_generation,
            next: edit.next_generation,
        }));
    }
    if previous.registry_epoch != edit.base_registry_epoch {
        return Outcome::Complete(Err(RecoveryError::StaleGrammarEpoch {
            session: previous.registry_epoch,
            supplied: edit.base_registry_epoch,
        }));
    }
    if registry.identity_at(edit.base_registry_epoch).is_none() {
        return Outcome::Complete(Err(RecoveryError::ForeignGrammarEpoch {
            supplied: edit.base_registry_epoch,
        }));
    }
    if spec.category != command_category() {
        return Outcome::Complete(Err(RecoveryError::CategoryMismatch {
            expected: command_category(),
            actual: spec.category.clone(),
        }));
    }
    if cancellation_requested(cancellation, RecoveryCheckpoint::BeforeLex) {
        return cancelled(RecoveryCheckpoint::BeforeLex);
    }
    if new_source.len() as u64 > budget.lex.max_input_bytes {
        return exhausted(
            StructuralUnit::InputBytes,
            budget.lex.max_input_bytes,
            new_source.len() as u64,
        );
    }

    let Some(previous_view) = previous.source_view.as_ref() else {
        return Outcome::Complete(Err(RecoveryError::IncrementalRestartRequired(
            IncrementalRestartReason::BaseHasNoLexicalSnapshot,
        )));
    };
    let Some(previous_run) = previous.lexical_run.as_ref() else {
        return Outcome::Complete(Err(RecoveryError::IncrementalRestartRequired(
            IncrementalRestartReason::BaseHasNoLexicalSnapshot,
        )));
    };
    let new_original = match SourceText::from_utf8(new_source) {
        Ok(source) => source,
        Err(SourceError::NotUtf8 { .. }) => {
            return Outcome::Complete(Err(RecoveryError::IncrementalRestartRequired(
                IncrementalRestartReason::NewSourceIsNotUtf8,
            )));
        }
    };
    let new_view = SourceView::of(&new_original);
    if !normalized_edit_is_exact(previous_view.normalized(), new_view.normalized(), edit) {
        return Outcome::Complete(Err(RecoveryError::InvalidNormalizedEdit {
            replaced: edit.replaced,
            old_len: previous_view.normalized().len_bytes(),
            inserted_len: edit.inserted_len,
            new_len: new_view.normalized().len_bytes(),
        }));
    }

    let table = TokenTable::from_tokens(["def", ":="]);
    let (incremental_run, lexical_damage) = relex_incremental(
        previous_run,
        edit.replaced,
        edit.inserted_len,
        new_view.normalized(),
        &table,
    );
    let event_count = incremental_run.events.len() as u64;
    if event_count > budget.lex.max_events {
        return exhausted(
            StructuralUnit::ProducedNodes,
            budget.lex.max_events,
            event_count,
        );
    }
    for processed in 0..event_count {
        let checkpoint = RecoveryCheckpoint::Event { processed };
        if cancellation_requested(cancellation, checkpoint) {
            return cancelled(checkpoint);
        }
    }

    let mut full_session = match parse_command_recovering(
        parse,
        new_source,
        edit.next_generation,
        registry,
        spec,
        mode,
        budget,
        None,
    ) {
        Outcome::Complete(Ok(session)) => session,
        Outcome::Complete(Err(error)) => return Outcome::Complete(Err(error)),
        Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    };
    let Some(full_run) = full_session.lexical_run.as_ref() else {
        return incremental_fault(
            "valid UTF-8 full recovery unexpectedly omitted its lexical snapshot",
        );
    };
    if &incremental_run != full_run {
        return incremental_fault(
            "incremental Vellum lexing disagreed with the full recovery session",
        );
    }

    let mut boundary_damage = BoundaryDamage {
        reused_prefix: 0,
        reparsed: 0,
    };
    if mode == RecoveryMode::Enabled {
        let Some(reference) = full_session.speculative.as_ref() else {
            return incremental_fault(
                "enabled full recovery unexpectedly omitted its boundary map",
            );
        };
        let can_reuse =
            previous.mode == RecoveryMode::Enabled && previous.recovery_spec.as_ref() == Some(spec);
        let previous_boundaries = previous
            .speculative
            .as_ref()
            .map_or(&[][..], SpeculativeBoundaryMap::boundaries);
        let mut verified_boundaries = Vec::with_capacity(reference.boundaries.len());
        for candidate in &reference.boundaries {
            let reusable = if can_reuse && candidate.span.end() <= edit.replaced.start() {
                previous_boundaries
                    .iter()
                    .find(|prior| prior.span == candidate.span && prior.epoch == candidate.epoch)
            } else {
                None
            };
            if let Some(prior) = reusable {
                if prior != candidate {
                    return incremental_fault(
                        "an unchanged candidate parse disagreed with its full reconstruction",
                    );
                }
                verified_boundaries.push(prior.clone());
                boundary_damage.reused_prefix += 1;
            } else {
                verified_boundaries.push(candidate.clone());
                boundary_damage.reparsed += 1;
            }
        }
        if verified_boundaries != reference.boundaries {
            return incremental_fault(
                "incremental candidate map disagreed with its full reconstruction",
            );
        }
        full_session.speculative = Some(SpeculativeBoundaryMap {
            boundaries: verified_boundaries,
        });
    }
    full_session.lexical_run = Some(incremental_run);

    let checkpoint = RecoveryCheckpoint::BeforePublication {
        processed: event_count,
    };
    if cancellation_requested(cancellation, checkpoint) {
        return cancelled(checkpoint);
    }
    Outcome::Complete(Ok(VerifiedIncrementalRecovery {
        session: full_session,
        lexical_damage,
        boundary_damage,
    }))
}

#[cfg(test)]
mod private_mutation_guards {
    use super::*;

    #[test]
    fn an_accepted_product_with_a_recovery_marker_is_still_unpublishable() {
        let registry = Registry::new();
        let spec = nat_definition_recovery_spec();
        let Outcome::Complete(Ok(mut session)) = parse_nat_definition_recovering(
            b"def answer := 42",
            1,
            &registry,
            &spec,
            RecoveryMode::Enabled,
            RecoveryBudget::generous(),
            None,
        ) else {
            panic!("clean seed command completes");
        };
        let epoch = registry.epoch_at_position(BytePos(0));
        let span = ByteSpan::empty_at(BytePos(0));
        let marker = RecoveryMarker {
            id: 0,
            category: command_category(),
            span,
            epoch,
        };
        session.recovered.push(RecoveredSyntax {
            marker,
            syntax: EpochSyntax::bind_uniform(
                Syntax::node(spec.marker_kind.clone(), vec![Syntax::Missing]),
                epoch,
            ),
        });

        assert!(matches!(
            session.publication_candidate(1, epoch),
            Err(PublicationRefusal::UnacknowledgedRecovery { markers: 1 })
        ));
    }
}
