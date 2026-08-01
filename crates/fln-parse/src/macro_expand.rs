//! Production quotation expansion over Vellum syntax (plan §9.2).
//!
//! The expansion is deliberately independent of transaction caching, which is
//! owned by the next W4 phase. This layer establishes the values that a
//! transaction will eventually journal: capture-safe syntax, stable generated
//! names, composed source origins, exact grammar/mode coordinates, and typed
//! diagnostics.
//!
//! Expansion is failure-atomic by construction. Work accumulates in a private
//! plan and [`MacroExpansion`] exists only after the final cancellation point and
//! a complete source-map validation. Cancellation or resource exhaustion is an
//! [`Outcome::Inconclusive`], malformed quotation input is a completed typed
//! refusal, and an invariant mismatch is an [`Outcome::InternalFault`]. None of
//! those arms contains partial syntax.

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_syntax::hygiene::{
    ExpansionPath, ExpansionSourceMap, HygieneError, MacroScope, OriginKind, SourceOrigin,
    SyntaxPath, add_macro_scope,
};
use fln_syntax::source::{ByteSpan, SourceInfo};
use fln_syntax::tree::{Preresolved, Syntax, SyntaxNodeKind};
use std::collections::BTreeSet;

use crate::registry::GrammarEpoch;
use crate::state::null_kind;

/// Whether syntax-quotation identifiers receive the current macro scope.
///
/// This is an elaboration option, not a product mode. All three modes carry the
/// same explicit value and therefore cannot silently choose different hygiene.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HygienePolicy {
    Enabled,
    Disabled,
}

/// Semantic coordinates of one macro expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroExpansionCoordinates {
    pub grammar_epoch: GrammarEpoch,
    pub mode: Mode,
    pub expansion_path: ExpansionPath,
}

/// Immutable quotation context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotationContext {
    pub name: Name,
    pub macro_scope: MacroScope,
    pub call_site: Option<ByteSpan>,
    pub canonical: bool,
    pub hygiene: HygienePolicy,
}

impl QuotationContext {
    fn output_info(&self) -> SourceInfo {
        self.call_site
            .map_or(SourceInfo::None, |span| SourceInfo::Synthetic {
                pos: span.start(),
                end_pos: span.end(),
                canonical: self.canonical,
            })
    }
}

/// Resource allowance for one quotation expansion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacroExpansionBudget {
    /// Template nodes plus syntax nodes walked inside literal/antiquoted trees.
    pub max_visited_nodes: u64,
    /// Nodes in the completed output tree.
    pub max_output_nodes: u64,
    /// Stable generated identifiers.
    pub max_generated_names: u64,
}

impl MacroExpansionBudget {
    pub const fn generous() -> MacroExpansionBudget {
        MacroExpansionBudget {
            max_visited_nodes: u64::MAX,
            max_output_nodes: u64::MAX,
            max_generated_names: u64::MAX,
        }
    }
}

/// Deterministic cancellation points.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroExpansionCheckpoint {
    BeforeTemplateNode { visited: u64 },
    BeforeSyntaxNode { visited: u64 },
    BeforePublication { visited: u64, produced: u64 },
}

impl MacroExpansionCheckpoint {
    fn progress(self) -> String {
        match self {
            MacroExpansionCheckpoint::BeforeTemplateNode { visited } => {
                format!("macro expansion before template node {visited}")
            }
            MacroExpansionCheckpoint::BeforeSyntaxNode { visited } => {
                format!("macro expansion before syntax node {visited}")
            }
            MacroExpansionCheckpoint::BeforePublication { visited, produced } => {
                format!(
                    "macro expansion before publication after {visited} visits and {produced} outputs"
                )
            }
        }
    }
}

/// Syntax together with a complete root-relative source map.
///
/// Fields are private so an antiquotation cannot smuggle a stale or partial map
/// into an otherwise authoritative expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedSyntax {
    syntax: Syntax,
    source_map: ExpansionSourceMap,
}

impl QuotedSyntax {
    /// Treat `syntax` as direct source input. Every node receives a literal
    /// origin, including nodes whose `SourceInfo` has no span.
    pub fn from_source(syntax: Syntax) -> QuotedSyntax {
        let source_map = map_existing_syntax(&syntax, OriginKind::Literal);
        QuotedSyntax { syntax, source_map }
    }

    /// Admit a caller-supplied source map only when it is total and exact.
    pub fn with_source_map(
        syntax: Syntax,
        source_map: ExpansionSourceMap,
    ) -> Result<QuotedSyntax, MacroExpansionError> {
        validate_source_map(&syntax, &source_map)?;
        Ok(QuotedSyntax { syntax, source_map })
    }

    pub fn syntax(&self) -> &Syntax {
        &self.syntax
    }

    pub fn source_map(&self) -> &ExpansionSourceMap {
        &self.source_map
    }
}

/// A syntax quotation with explicit antiquotation and splice boundaries.
pub enum QuotationTemplate {
    /// Literal quotation syntax. Identifier names are scoped when hygiene is
    /// enabled, and every output node points at both definition and call origins.
    Literal(Syntax),
    /// Insert one value exactly as supplied.
    Antiquotation {
        hole_info: SourceInfo,
        value: QuotedSyntax,
    },
    /// Flatten values into a null-kind node, matching the Reference's splice
    /// boundary. A splice anywhere else is a typed refusal.
    Splice {
        hole_info: SourceInfo,
        values: Vec<QuotedSyntax>,
    },
    /// A quotation-built syntax node.
    Node {
        definition_info: SourceInfo,
        kind: SyntaxNodeKind,
        args: Vec<QuotationTemplate>,
    },
    /// One identifier generated from a stable logical path.
    GeneratedIdent {
        definition_info: SourceInfo,
        raw_val: ByteSpan,
        base: Name,
        preresolved: Vec<Preresolved>,
        local_ordinal: u64,
    },
    /// A nested quotation. It shares the current Reference macro scope while
    /// extending only the stable quotation path.
    Nested {
        definition_info: SourceInfo,
        quotation_ordinal: u64,
        body: Box<QuotationTemplate>,
    },
}

impl Drop for QuotationTemplate {
    fn drop(&mut self) {
        // A quotation is user/metaprogram reachable and may be arbitrarily deep.
        // Drain recursive children onto a heap worklist before ordinary drop glue
        // sees them, including when cancellation abandons a partially visited
        // task stack.
        let mut pending = Vec::<Box<QuotationTemplate>>::new();
        detach_template_children(self, &mut pending);
        let mut drained = 0usize;
        while let Some(mut template) = pending.pop() {
            detach_template_children(&mut template, &mut pending);
            drained += 1;
            if drained.is_multiple_of(4096) {
                std::thread::yield_now();
            }
        }
    }
}

fn detach_template_children(
    template: &mut QuotationTemplate,
    pending: &mut Vec<Box<QuotationTemplate>>,
) {
    match template {
        QuotationTemplate::Node { args, .. } => {
            pending.extend(std::mem::take(args).into_iter().map(Box::new));
        }
        QuotationTemplate::Nested { body, .. } => {
            pending.push(std::mem::replace(
                body,
                Box::new(QuotationTemplate::Literal(Syntax::Missing)),
            ));
        }
        QuotationTemplate::Literal(_)
        | QuotationTemplate::Antiquotation { .. }
        | QuotationTemplate::Splice { .. }
        | QuotationTemplate::GeneratedIdent { .. } => {}
    }
}

/// Complete input to the production expander.
pub struct MacroExpansionInput {
    pub coordinates: MacroExpansionCoordinates,
    pub quotation: QuotationContext,
    pub template: QuotationTemplate,
}

/// One generated identifier, before and after macro-scope decoration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedName {
    pub path: ExpansionPath,
    pub stable: Name,
    pub hygienic: Name,
}

/// Productive work counters. These are semantic budget facts, not wall-clock
/// telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacroExpansionStats {
    pub visited_nodes: u64,
    pub output_nodes: u64,
}

/// Authoritative output of a completed expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroExpansion {
    coordinates: MacroExpansionCoordinates,
    syntax: Syntax,
    generated_names: Vec<GeneratedName>,
    source_map: ExpansionSourceMap,
    stats: MacroExpansionStats,
}

impl MacroExpansion {
    pub const fn coordinates(&self) -> &MacroExpansionCoordinates {
        &self.coordinates
    }

    pub const fn syntax(&self) -> &Syntax {
        &self.syntax
    }

    pub fn generated_names(&self) -> &[GeneratedName] {
        &self.generated_names
    }

    pub const fn source_map(&self) -> &ExpansionSourceMap {
        &self.source_map
    }

    pub const fn stats(&self) -> MacroExpansionStats {
        self.stats
    }

    pub fn into_quoted(self) -> QuotedSyntax {
        QuotedSyntax {
            syntax: self.syntax,
            source_map: self.source_map,
        }
    }
}

/// Why a quotation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroExpansionError {
    Hygiene(HygieneError),
    UnsupportedMissing {
        path: SyntaxPath,
    },
    UnexpectedSplice {
        path: SyntaxPath,
    },
    TopLevelSplice {
        produced: usize,
    },
    DuplicateGeneratedPath {
        path: ExpansionPath,
    },
    SourceMapMismatch {
        syntax_nodes: usize,
        mapped_nodes: usize,
    },
}

impl MacroExpansionError {
    /// Stable Reference-facing diagnostic text for the overlapping refusal
    /// surfaces.
    pub const fn message(&self) -> &'static str {
        match self {
            MacroExpansionError::Hygiene(_) => "malformed hygienic identifier",
            MacroExpansionError::UnsupportedMissing { .. } => "unsupported syntax",
            MacroExpansionError::UnexpectedSplice { .. } => "unexpected antiquotation splice",
            MacroExpansionError::TopLevelSplice { .. } => {
                "antiquotation splice requires a surrounding null node"
            }
            MacroExpansionError::DuplicateGeneratedPath { .. } => {
                "duplicate generated-name expansion path"
            }
            MacroExpansionError::SourceMapMismatch { .. } => {
                "antiquotation source map does not match its syntax"
            }
        }
    }
}

impl From<HygieneError> for MacroExpansionError {
    fn from(error: HygieneError) -> MacroExpansionError {
        MacroExpansionError::Hygiene(error)
    }
}

enum ExpansionStop {
    Refused(MacroExpansionError),
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

impl From<MacroExpansionError> for ExpansionStop {
    fn from(error: MacroExpansionError) -> ExpansionStop {
        ExpansionStop::Refused(error)
    }
}

impl From<HygieneError> for ExpansionStop {
    fn from(error: HygieneError) -> ExpansionStop {
        ExpansionStop::Refused(MacroExpansionError::Hygiene(error))
    }
}

struct MappedSyntax {
    syntax: Syntax,
    source_map: ExpansionSourceMap,
}

struct Fragment {
    items: Vec<MappedSyntax>,
}

impl Fragment {
    fn one(item: MappedSyntax) -> Fragment {
        Fragment { items: vec![item] }
    }
}

enum TemplateTask {
    Visit {
        template: QuotationTemplate,
        expansion_path: ExpansionPath,
    },
    FinishNode {
        definition_info: SourceInfo,
        kind: SyntaxNodeKind,
        child_count: usize,
        expansion_path: ExpansionPath,
    },
    FinishNested {
        definition_info: SourceInfo,
        expansion_path: ExpansionPath,
    },
}

enum LiteralTask<'a> {
    Visit {
        syntax: &'a Syntax,
        syntax_path: SyntaxPath,
    },
    FinishNode {
        kind: SyntaxNodeKind,
        child_start: usize,
    },
}

struct Expander<'a> {
    coordinates: MacroExpansionCoordinates,
    quotation: QuotationContext,
    budget: MacroExpansionBudget,
    cancellation: Option<&'a dyn Fn(MacroExpansionCheckpoint) -> bool>,
    visited: u64,
    produced: u64,
    generated_names: Vec<GeneratedName>,
    generated_paths: BTreeSet<ExpansionPath>,
}

impl Expander<'_> {
    fn observe_template(&mut self) -> Result<(), ExpansionStop> {
        let checkpoint = MacroExpansionCheckpoint::BeforeTemplateNode {
            visited: self.visited,
        };
        self.observe_visit(checkpoint)
    }

    fn observe_syntax(&mut self) -> Result<(), ExpansionStop> {
        let checkpoint = MacroExpansionCheckpoint::BeforeSyntaxNode {
            visited: self.visited,
        };
        self.observe_visit(checkpoint)
    }

    fn observe_visit(&mut self, checkpoint: MacroExpansionCheckpoint) -> Result<(), ExpansionStop> {
        if self.cancellation.is_some_and(|probe| probe(checkpoint)) {
            return Err(ExpansionStop::Inconclusive(Inconclusive::cancelled(
                checkpoint.progress(),
            )));
        }
        if self.visited == self.budget.max_visited_nodes {
            return Err(resource_stop(
                self.budget.max_visited_nodes,
                self.visited.saturating_add(1),
            ));
        }
        self.visited += 1;
        Ok(())
    }

    fn observe_output(&mut self) -> Result<(), ExpansionStop> {
        if self.produced == self.budget.max_output_nodes {
            return Err(resource_stop(
                self.budget.max_output_nodes,
                self.produced.saturating_add(1),
            ));
        }
        self.produced += 1;
        Ok(())
    }

    fn observe_generated(&self) -> Result<(), ExpansionStop> {
        if self.generated_names.len() as u64 == self.budget.max_generated_names {
            return Err(resource_stop(
                self.budget.max_generated_names,
                (self.generated_names.len() as u64).saturating_add(1),
            ));
        }
        Ok(())
    }

    fn call_origin(&self, expansion_path: &ExpansionPath) -> SourceOrigin {
        SourceOrigin::new(
            OriginKind::MacroCall,
            self.quotation.call_site,
            Some(expansion_path.clone()),
        )
    }

    fn definition_origin(&self, info: SourceInfo, expansion_path: &ExpansionPath) -> SourceOrigin {
        SourceOrigin::new(
            OriginKind::MacroDefinition,
            source_span(info),
            Some(expansion_path.clone()),
        )
    }

    fn expand_literal(
        &mut self,
        syntax: Syntax,
        expansion_path: &ExpansionPath,
    ) -> Result<MappedSyntax, ExpansionStop> {
        let mut tasks = vec![LiteralTask::Visit {
            syntax: &syntax,
            syntax_path: SyntaxPath::root(),
        }];
        let mut built = Vec::new();
        let mut source_map = ExpansionSourceMap::new();

        while let Some(task) = tasks.pop() {
            match task {
                LiteralTask::Visit {
                    syntax,
                    syntax_path,
                } => {
                    self.observe_syntax()?;
                    self.observe_output()?;
                    let info = syntax.info();
                    source_map.record(
                        syntax_path.clone(),
                        self.definition_origin(info, expansion_path),
                    );
                    source_map.record(syntax_path.clone(), self.call_origin(expansion_path));
                    match syntax {
                        Syntax::Missing => {
                            return Err(MacroExpansionError::UnsupportedMissing {
                                path: syntax_path,
                            }
                            .into());
                        }
                        Syntax::Node { kind, args, .. } => {
                            let child_start = built.len();
                            let child_paths = (0..args.len())
                                .map(|index| syntax_path.child(index as u64))
                                .collect::<Vec<_>>();
                            tasks.push(LiteralTask::FinishNode {
                                kind: kind.clone(),
                                child_start,
                            });
                            tasks.extend(args.iter().zip(child_paths).rev().map(
                                |(syntax, syntax_path)| LiteralTask::Visit {
                                    syntax,
                                    syntax_path,
                                },
                            ));
                        }
                        Syntax::Atom { val, .. } => {
                            built.push(Syntax::Atom {
                                info: self.quotation.output_info(),
                                val: val.clone(),
                            });
                        }
                        Syntax::Ident {
                            raw_val,
                            val,
                            preresolved,
                            ..
                        } => {
                            let val = match self.quotation.hygiene {
                                HygienePolicy::Enabled => add_macro_scope(
                                    &self.quotation.name,
                                    val,
                                    self.quotation.macro_scope,
                                )?,
                                HygienePolicy::Disabled => val.clone(),
                            };
                            built.push(Syntax::Ident {
                                info: self.quotation.output_info(),
                                raw_val: *raw_val,
                                val,
                                preresolved: preresolved.clone(),
                            });
                        }
                    }
                }
                LiteralTask::FinishNode { kind, child_start } => {
                    let args = built.split_off(child_start);
                    built.push(Syntax::Node {
                        info: self.quotation.output_info(),
                        kind,
                        args,
                    });
                }
            }
        }

        if built.len() != 1 {
            return Err(ExpansionStop::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-LITERAL-STACK",
                "one literal input did not produce exactly one syntax root",
            )));
        }
        let syntax = built.pop().ok_or_else(|| {
            ExpansionStop::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-LITERAL-STACK",
                "literal worklist completed without a syntax root",
            ))
        })?;
        Ok(MappedSyntax { syntax, source_map })
    }

    fn account_existing_syntax(&mut self, syntax: &Syntax) -> Result<(), ExpansionStop> {
        let mut pending = vec![syntax];
        while let Some(node) = pending.pop() {
            self.observe_syntax()?;
            self.observe_output()?;
            if let Syntax::Node { args, .. } = node {
                pending.extend(args.iter().rev());
            }
        }
        Ok(())
    }

    fn admit_quoted(
        &mut self,
        mut quoted: QuotedSyntax,
        wrapper_kind: OriginKind,
        wrapper_info: SourceInfo,
        expansion_path: &ExpansionPath,
    ) -> Result<MappedSyntax, ExpansionStop> {
        self.account_existing_syntax(&quoted.syntax)?;
        quoted.source_map.add_origin_to_all(SourceOrigin::new(
            wrapper_kind,
            source_span(wrapper_info),
            Some(expansion_path.clone()),
        ));
        Ok(MappedSyntax {
            syntax: quoted.syntax,
            source_map: quoted.source_map,
        })
    }

    fn generated_ident(
        &mut self,
        definition_info: SourceInfo,
        raw_val: ByteSpan,
        base: Name,
        preresolved: Vec<Preresolved>,
        local_ordinal: u64,
        expansion_path: &ExpansionPath,
    ) -> Result<MappedSyntax, ExpansionStop> {
        self.observe_output()?;
        self.observe_generated()?;
        let path = expansion_path.with_local_ordinal(local_ordinal);
        if !self.generated_paths.insert(path.clone()) {
            return Err(MacroExpansionError::DuplicateGeneratedPath { path }.into());
        }
        let stable = path.generated_name(&base);
        let hygienic = match self.quotation.hygiene {
            HygienePolicy::Enabled => {
                add_macro_scope(&self.quotation.name, &stable, self.quotation.macro_scope)?
            }
            HygienePolicy::Disabled => stable.clone(),
        };
        self.generated_names.push(GeneratedName {
            path: path.clone(),
            stable,
            hygienic: hygienic.clone(),
        });
        let mut source_map = ExpansionSourceMap::new();
        source_map.record(
            SyntaxPath::root(),
            self.definition_origin(definition_info, expansion_path),
        );
        source_map.record(SyntaxPath::root(), self.call_origin(expansion_path));
        Ok(MappedSyntax {
            syntax: Syntax::Ident {
                info: self.quotation.output_info(),
                raw_val,
                val: hygienic,
                preresolved,
            },
            source_map,
        })
    }

    fn expand(mut self, template: QuotationTemplate) -> Result<MacroExpansion, ExpansionStop> {
        let root_path = self.coordinates.expansion_path.clone();
        let mut tasks = vec![TemplateTask::Visit {
            template,
            expansion_path: root_path,
        }];
        let mut built = Vec::<Fragment>::new();

        while let Some(task) = tasks.pop() {
            match task {
                TemplateTask::Visit {
                    template,
                    expansion_path,
                } => {
                    self.observe_template()?;
                    let mut template = template;
                    match &mut template {
                        QuotationTemplate::Literal(syntax) => {
                            let syntax = std::mem::replace(syntax, Syntax::Missing);
                            let mapped = self.expand_literal(syntax, &expansion_path)?;
                            built.push(Fragment::one(mapped));
                        }
                        QuotationTemplate::Antiquotation { hole_info, value } => {
                            let hole_info = *hole_info;
                            let value = std::mem::replace(
                                value,
                                QuotedSyntax::from_source(Syntax::Missing),
                            );
                            let mapped = self.admit_quoted(
                                value,
                                OriginKind::Antiquotation,
                                hole_info,
                                &expansion_path,
                            )?;
                            built.push(Fragment::one(mapped));
                        }
                        QuotationTemplate::Splice { hole_info, values } => {
                            let hole_info = *hole_info;
                            let mut items = Vec::with_capacity(values.len());
                            for value in std::mem::take(values) {
                                items.push(self.admit_quoted(
                                    value,
                                    OriginKind::Antiquotation,
                                    hole_info,
                                    &expansion_path,
                                )?);
                            }
                            built.push(Fragment { items });
                        }
                        QuotationTemplate::Node {
                            definition_info,
                            kind,
                            args,
                        } => {
                            let definition_info = *definition_info;
                            let kind = std::mem::take(kind);
                            let args = std::mem::take(args);
                            if kind != null_kind()
                                && args
                                    .iter()
                                    .any(|arg| matches!(arg, QuotationTemplate::Splice { .. }))
                            {
                                return Err(MacroExpansionError::UnexpectedSplice {
                                    path: SyntaxPath::root(),
                                }
                                .into());
                            }
                            let child_count = args.len();
                            tasks.push(TemplateTask::FinishNode {
                                definition_info,
                                kind,
                                child_count,
                                expansion_path: expansion_path.clone(),
                            });
                            tasks.extend(args.into_iter().rev().map(|template| {
                                TemplateTask::Visit {
                                    template,
                                    expansion_path: expansion_path.clone(),
                                }
                            }));
                        }
                        QuotationTemplate::GeneratedIdent {
                            definition_info,
                            raw_val,
                            base,
                            preresolved,
                            local_ordinal,
                        } => {
                            let definition_info = *definition_info;
                            let raw_val = *raw_val;
                            let base = std::mem::take(base);
                            let preresolved = std::mem::take(preresolved);
                            let local_ordinal = *local_ordinal;
                            let mapped = self.generated_ident(
                                definition_info,
                                raw_val,
                                base,
                                preresolved,
                                local_ordinal,
                                &expansion_path,
                            )?;
                            built.push(Fragment::one(mapped));
                        }
                        QuotationTemplate::Nested {
                            definition_info,
                            quotation_ordinal,
                            body,
                        } => {
                            let definition_info = *definition_info;
                            let quotation_ordinal = *quotation_ordinal;
                            let body = std::mem::replace(
                                body,
                                Box::new(QuotationTemplate::Literal(Syntax::Missing)),
                            );
                            let nested_path = expansion_path.nested_quotation(quotation_ordinal);
                            tasks.push(TemplateTask::FinishNested {
                                definition_info,
                                expansion_path: nested_path.clone(),
                            });
                            tasks.push(TemplateTask::Visit {
                                template: *body,
                                expansion_path: nested_path,
                            });
                        }
                    }
                }
                TemplateTask::FinishNode {
                    definition_info,
                    kind,
                    child_count,
                    expansion_path,
                } => {
                    if child_count > built.len() {
                        return Err(ExpansionStop::InternalFault(InternalFault::new(
                            "FLN-W4-MACRO-TEMPLATE-STACK",
                            "node completion observed fewer fragments than children",
                        )));
                    }
                    let fragments = built.split_off(built.len() - child_count);
                    let mut args = Vec::new();
                    let mut source_map = ExpansionSourceMap::new();
                    for fragment in fragments {
                        for mapped in fragment.items {
                            let child_path = SyntaxPath::root().child(args.len() as u64);
                            source_map.extend_prefixed(&child_path, &mapped.source_map);
                            args.push(mapped.syntax);
                        }
                    }
                    self.observe_output()?;
                    source_map.record(
                        SyntaxPath::root(),
                        self.definition_origin(definition_info, &expansion_path),
                    );
                    source_map.record(SyntaxPath::root(), self.call_origin(&expansion_path));
                    built.push(Fragment::one(MappedSyntax {
                        syntax: Syntax::Node {
                            info: self.quotation.output_info(),
                            kind,
                            args,
                        },
                        source_map,
                    }));
                }
                TemplateTask::FinishNested {
                    definition_info,
                    expansion_path,
                } => {
                    let fragment = built.pop().ok_or_else(|| {
                        ExpansionStop::InternalFault(InternalFault::new(
                            "FLN-W4-MACRO-TEMPLATE-STACK",
                            "nested quotation completed without a fragment",
                        ))
                    })?;
                    if fragment.items.len() != 1 {
                        return Err(MacroExpansionError::TopLevelSplice {
                            produced: fragment.items.len(),
                        }
                        .into());
                    }
                    let quotation_origin = SourceOrigin::new(
                        OriginKind::Quotation,
                        source_span(definition_info),
                        Some(expansion_path),
                    );
                    let mut items = fragment.items;
                    let mut mapped = items.pop().ok_or_else(|| {
                        ExpansionStop::InternalFault(InternalFault::new(
                            "FLN-W4-MACRO-TEMPLATE-STACK",
                            "one-item nested fragment was empty",
                        ))
                    })?;
                    mapped.source_map.add_origin_to_all(quotation_origin);
                    built.push(Fragment::one(mapped));
                }
            }
        }

        if built.len() != 1 {
            return Err(ExpansionStop::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TEMPLATE-STACK",
                "one quotation input did not produce exactly one fragment",
            )));
        }
        let mut items = built
            .pop()
            .ok_or_else(|| {
                ExpansionStop::InternalFault(InternalFault::new(
                    "FLN-W4-MACRO-TEMPLATE-STACK",
                    "quotation worklist completed without a fragment",
                ))
            })?
            .items;
        if items.len() != 1 {
            return Err(MacroExpansionError::TopLevelSplice {
                produced: items.len(),
            }
            .into());
        }
        let mapped = items.pop().ok_or_else(|| {
            ExpansionStop::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TEMPLATE-STACK",
                "one-item root fragment was empty",
            ))
        })?;
        validate_constructed_source_map(&mapped)?;

        let checkpoint = MacroExpansionCheckpoint::BeforePublication {
            visited: self.visited,
            produced: self.produced,
        };
        if self.cancellation.is_some_and(|probe| probe(checkpoint)) {
            return Err(ExpansionStop::Inconclusive(Inconclusive::cancelled(
                checkpoint.progress(),
            )));
        }

        Ok(MacroExpansion {
            coordinates: self.coordinates,
            syntax: mapped.syntax,
            generated_names: self.generated_names,
            source_map: mapped.source_map,
            stats: MacroExpansionStats {
                visited_nodes: self.visited,
                output_nodes: self.produced,
            },
        })
    }
}

/// Expand a quotation without publishing partial work.
pub fn expand_quotation(
    input: MacroExpansionInput,
    budget: MacroExpansionBudget,
    cancellation: Option<&dyn Fn(MacroExpansionCheckpoint) -> bool>,
) -> Outcome<Result<MacroExpansion, MacroExpansionError>> {
    let expander = Expander {
        coordinates: input.coordinates,
        quotation: input.quotation,
        budget,
        cancellation,
        visited: 0,
        produced: 0,
        generated_names: Vec::new(),
        generated_paths: BTreeSet::new(),
    };
    match expander.expand(input.template) {
        Ok(expansion) => Outcome::Complete(Ok(expansion)),
        Err(ExpansionStop::Refused(error)) => Outcome::Complete(Err(error)),
        Err(ExpansionStop::Inconclusive(inconclusive)) => Outcome::Inconclusive(inconclusive),
        Err(ExpansionStop::InternalFault(fault)) => Outcome::InternalFault(fault),
    }
}

fn resource_stop(allowed: u64, observed: u64) -> ExpansionStop {
    ExpansionStop::Inconclusive(Inconclusive::resource(ResourceUsage {
        reason: ResourceReason::StructuralBudget {
            unit: StructuralUnit::ProducedNodes,
        },
        allowed,
        observed,
    }))
}

fn source_span(info: SourceInfo) -> Option<ByteSpan> {
    ByteSpan::new(info.pos(false)?, info.end_pos(false)?)
}

fn map_existing_syntax(syntax: &Syntax, kind: OriginKind) -> ExpansionSourceMap {
    let mut source_map = ExpansionSourceMap::new();
    let mut pending = vec![(syntax, SyntaxPath::root())];
    while let Some((node, path)) = pending.pop() {
        source_map.record(
            path.clone(),
            SourceOrigin::new(kind, source_span(node.info()), None),
        );
        if let Syntax::Node { args, .. } = node {
            pending.extend(
                args.iter()
                    .enumerate()
                    .rev()
                    .map(|(index, child)| (child, path.child(index as u64))),
            );
        }
    }
    source_map
}

fn syntax_paths(syntax: &Syntax) -> BTreeSet<SyntaxPath> {
    let mut paths = BTreeSet::new();
    let mut pending = vec![(syntax, SyntaxPath::root())];
    while let Some((node, path)) = pending.pop() {
        paths.insert(path.clone());
        if let Syntax::Node { args, .. } = node {
            pending.extend(
                args.iter()
                    .enumerate()
                    .rev()
                    .map(|(index, child)| (child, path.child(index as u64))),
            );
        }
    }
    paths
}

fn validate_source_map(
    syntax: &Syntax,
    source_map: &ExpansionSourceMap,
) -> Result<(), MacroExpansionError> {
    let syntax_paths = syntax_paths(syntax);
    let mapped_paths = source_map.paths().cloned().collect::<BTreeSet<_>>();
    if syntax_paths == mapped_paths {
        Ok(())
    } else {
        Err(MacroExpansionError::SourceMapMismatch {
            syntax_nodes: syntax_paths.len(),
            mapped_nodes: mapped_paths.len(),
        })
    }
}

fn validate_constructed_source_map(mapped: &MappedSyntax) -> Result<(), ExpansionStop> {
    validate_source_map(&mapped.syntax, &mapped.source_map).map_err(|error| {
        ExpansionStop::InternalFault(
            InternalFault::new(
                "FLN-W4-MACRO-SOURCE-MAP-TOTALITY",
                "the production expander constructed a non-total source map",
            )
            .with_evidence(error.message()),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_hash::domain::Digest;
    use fln_syntax::hygiene::{ExpansionOrigin, extract_macro_scopes};
    use fln_syntax::source::BytePos;

    fn span(start: usize, end: usize) -> ByteSpan {
        ByteSpan::new(BytePos(start), BytePos(end)).expect("forward span")
    }

    fn coordinates() -> MacroExpansionCoordinates {
        MacroExpansionCoordinates {
            grammar_epoch: GrammarEpoch::from_parts(7, Digest([7; 32])),
            mode: Mode::Faithful,
            expansion_path: ExpansionPath::root(
                ExpansionOrigin::new(Name::from_components(["Main"]), 3),
                2,
            ),
        }
    }

    fn context() -> QuotationContext {
        QuotationContext {
            name: Name::from_components(["Main", "decl", "_hygCtx"]),
            macro_scope: 11,
            call_site: Some(span(100, 110)),
            canonical: true,
            hygiene: HygienePolicy::Enabled,
        }
    }

    fn ident(name: &str, at: usize) -> Syntax {
        Syntax::Ident {
            info: SourceInfo::Original {
                leading: ByteSpan::empty_at(BytePos(at)),
                pos: BytePos(at),
                trailing: span(at + 1, at + 1),
                end_pos: BytePos(at + 1),
            },
            raw_val: span(at, at + 1),
            val: Name::from_components([name]),
            preresolved: Vec::new(),
        }
    }

    #[test]
    fn literal_identifiers_are_scoped_and_antiquotations_are_not_captured() {
        let template = QuotationTemplate::Node {
            definition_info: SourceInfo::Synthetic {
                pos: BytePos(1),
                end_pos: BytePos(9),
                canonical: true,
            },
            kind: null_kind(),
            args: vec![
                QuotationTemplate::Literal(ident("literal", 2)),
                QuotationTemplate::Antiquotation {
                    hole_info: SourceInfo::Synthetic {
                        pos: BytePos(5),
                        end_pos: BytePos(6),
                        canonical: true,
                    },
                    value: QuotedSyntax::from_source(ident("caller", 30)),
                },
            ],
        };
        let outcome = expand_quotation(
            MacroExpansionInput {
                coordinates: coordinates(),
                quotation: context(),
                template,
            },
            MacroExpansionBudget::generous(),
            None,
        );
        let expansion = match outcome {
            Outcome::Complete(Ok(expansion)) => expansion,
            other => panic!("expected completed expansion, got {other:?}"),
        };
        let Syntax::Node { args, .. } = expansion.syntax() else {
            panic!("expected node");
        };
        let Syntax::Ident {
            val: literal_name, ..
        } = &args[0]
        else {
            panic!("expected literal identifier");
        };
        assert_eq!(
            extract_macro_scopes(literal_name)
                .expect("well formed")
                .name
                .to_display_string(),
            "literal"
        );
        let Syntax::Ident {
            val: caller_name, ..
        } = &args[1]
        else {
            panic!("expected antiquoted identifier");
        };
        assert_eq!(caller_name.to_display_string(), "caller");
    }

    #[test]
    fn final_cancellation_and_resource_stops_publish_no_expansion() {
        let input = || MacroExpansionInput {
            coordinates: coordinates(),
            quotation: context(),
            template: QuotationTemplate::Literal(ident("x", 0)),
        };
        let cancelled = expand_quotation(
            input(),
            MacroExpansionBudget::generous(),
            Some(&|checkpoint| {
                matches!(
                    checkpoint,
                    MacroExpansionCheckpoint::BeforePublication { .. }
                )
            }),
        );
        assert!(matches!(cancelled, Outcome::Inconclusive(_)));

        let exhausted = expand_quotation(
            input(),
            MacroExpansionBudget {
                max_visited_nodes: 1,
                ..MacroExpansionBudget::generous()
            },
            None,
        );
        assert!(matches!(exhausted, Outcome::Inconclusive(_)));
    }

    #[test]
    fn a_source_map_drop_mutant_is_an_internal_fault_with_no_product() {
        let mutant = MappedSyntax {
            syntax: Syntax::atom(SourceInfo::None, "x"),
            source_map: ExpansionSourceMap::new(),
        };
        assert!(matches!(
            validate_constructed_source_map(&mutant),
            Err(ExpansionStop::InternalFault(_))
        ));
    }
}
