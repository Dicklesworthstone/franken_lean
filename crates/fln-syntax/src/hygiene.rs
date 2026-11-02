//! Macro hygiene identities and composed source origins (plan §9.1-§9.2).
//!
//! This module owns the substrate shared by Vellum's quotation expander and the
//! future Native Mirror:
//!
//! * [`MacroScopesView`], reexported from the shared Name substrate, is the
//!   total, stack-safe counterpart of the pinned
//!   Reference's `MacroScopesView`, `extractMacroScopes`, `review`, and
//!   `addMacroScope`.
//! * [`ExpansionPath`] makes generated names a function of logical expansion
//!   coordinates. Thread timing, allocation order, process identity, and wall
//!   clock have no representation in the type.
//! * [`ExpansionSourceMap`] retains origin *sets* and composes them at nested
//!   expansion boundaries. A single primary span is an explicit projection, not
//!   information discarded while expanding.
//!
//! The Reference treats malformed scope decorations as unreachable and panics.
//! FrankenLean cannot do that on artifact, plugin, or metaprogram input:
//! [`extract_macro_scopes`] returns a typed [`HygieneError`] while preserving the
//! exact Reference result for every well-formed name.

pub use fln_core::name::hygiene::{
    FIRST_FRONTEND_MACRO_SCOPE, HygieneError, MacroScope, MacroScopesView, add_macro_scope,
    extract_macro_scopes,
};
use fln_core::name::{LeafView, Name};
use std::collections::{BTreeMap, BTreeSet};

use crate::source::ByteSpan;

#[cfg(test)]
const MACRO_SCOPES_MARKER: &str = "_hyg";
#[cfg(test)]
const MACRO_SCOPES_SEPARATOR: &str = "_@";
const GENERATED_NAME_PREFIX: &str = "_uniq";
const GENERATED_NAME_SCHEMA: &str = "_fln_macro_path_v1";

#[derive(Debug, Clone, PartialEq, Eq)]
enum NameComponent {
    Str(String),
    Num { value: u64, overflowed: bool },
}

fn name_components(name: &Name) -> Vec<NameComponent> {
    let mut components = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        let component = match cursor.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(value) => NameComponent::Str(value.to_string()),
            LeafView::Num(value) => NameComponent::Num {
                value,
                overflowed: cursor.component_overflowed(),
            },
        };
        components.push(component);
        cursor = cursor.parent();
    }
    components.reverse();
    components
}

/// Stable identity of the command that initiated an expansion.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpansionOrigin {
    pub module: Name,
    pub command_ordinal: u64,
}

impl ExpansionOrigin {
    pub fn new(module: Name, command_ordinal: u64) -> ExpansionOrigin {
        ExpansionOrigin {
            module,
            command_ordinal,
        }
    }
}

/// A schedule-independent logical path to one generated name.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpansionPath {
    origin: ExpansionOrigin,
    invocations: Vec<u64>,
    quotations: Vec<u64>,
    local_ordinal: u64,
}

impl ExpansionPath {
    pub fn root(origin: ExpansionOrigin, invocation_ordinal: u64) -> ExpansionPath {
        ExpansionPath {
            origin,
            invocations: vec![invocation_ordinal],
            quotations: Vec::new(),
            local_ordinal: 0,
        }
    }

    pub fn nested_invocation(&self, invocation_ordinal: u64) -> ExpansionPath {
        let mut nested = self.clone();
        nested.invocations.push(invocation_ordinal);
        nested.quotations.clear();
        nested.local_ordinal = 0;
        nested
    }

    pub fn nested_quotation(&self, quotation_ordinal: u64) -> ExpansionPath {
        let mut nested = self.clone();
        nested.quotations.push(quotation_ordinal);
        nested.local_ordinal = 0;
        nested
    }

    pub fn with_local_ordinal(&self, local_ordinal: u64) -> ExpansionPath {
        let mut local = self.clone();
        local.local_ordinal = local_ordinal;
        local
    }

    pub const fn origin(&self) -> &ExpansionOrigin {
        &self.origin
    }

    pub fn invocations(&self) -> &[u64] {
        &self.invocations
    }

    pub fn quotations(&self) -> &[u64] {
        &self.quotations
    }

    pub const fn local_ordinal(&self) -> u64 {
        self.local_ordinal
    }

    /// Injective structural encoding under the familiar `_uniq` prefix.
    ///
    /// Every variable-length field carries a length and every `Name` component
    /// carries a constructor tag, so string `"7"` and numeric `7`, or a marker
    /// appearing inside user input, cannot collapse two logical paths.
    pub fn generated_name(&self, base: &Name) -> Name {
        let mut out = Name::str(Name::anonymous(), GENERATED_NAME_PREFIX);
        out = Name::str(out, GENERATED_NAME_SCHEMA);
        out = append_encoded_name(out, "_base", base);
        out = append_encoded_name(out, "_module", &self.origin.module);
        out = Name::str(out, "_command");
        out = Name::num(out, self.origin.command_ordinal);
        out = append_u64s(out, "_invocations", &self.invocations);
        out = append_u64s(out, "_quotations", &self.quotations);
        out = Name::str(out, "_local");
        Name::num(out, self.local_ordinal)
    }

    pub fn canonical(&self) -> String {
        let mut out = String::from("fln.expansion-path/1;");
        push_name(&mut out, &self.origin.module);
        push_u64(&mut out, self.origin.command_ordinal);
        push_u64_slice(&mut out, &self.invocations);
        push_u64_slice(&mut out, &self.quotations);
        push_u64(&mut out, self.local_ordinal);
        out
    }
}

fn append_encoded_name(mut out: Name, label: &str, name: &Name) -> Name {
    out = Name::str(out, label);
    let components = name_components(name);
    out = Name::num(out, components.len() as u64);
    for component in components {
        match component {
            NameComponent::Str(value) => {
                out = Name::str(out, "_str");
                out = Name::str(out, value);
            }
            NameComponent::Num {
                value,
                overflowed: false,
            } => {
                out = Name::str(out, "_num");
                out = Name::num(out, value);
            }
            NameComponent::Num {
                value,
                overflowed: true,
            } => {
                out = Name::str(out, "_overflowing_num");
                out = Name::num_overflowing(out, value);
            }
        }
    }
    out
}

fn append_u64s(mut out: Name, label: &str, values: &[u64]) -> Name {
    out = Name::str(out, label);
    out = Name::num(out, values.len() as u64);
    for value in values {
        out = Name::num(out, *value);
    }
    out
}

/// A root-relative path to one output syntax node.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxPath(Vec<u64>);

impl SyntaxPath {
    pub const fn root() -> SyntaxPath {
        SyntaxPath(Vec::new())
    }

    pub fn child(&self, ordinal: u64) -> SyntaxPath {
        let mut child = self.clone();
        child.0.push(ordinal);
        child
    }

    pub fn join(&self, suffix: &SyntaxPath) -> SyntaxPath {
        let mut joined = self.clone();
        joined.0.extend_from_slice(&suffix.0);
        joined
    }

    pub fn components(&self) -> &[u64] {
        &self.0
    }

    fn starts_with(&self, prefix: &SyntaxPath) -> bool {
        self.0.starts_with(&prefix.0)
    }
}

/// Why an output node points at a source span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OriginKind {
    Literal,
    MacroDefinition,
    MacroCall,
    Quotation,
    Antiquotation,
    Recovered,
}

/// One member of an output node's origin set.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceOrigin {
    pub kind: OriginKind,
    pub span: Option<ByteSpan>,
    pub expansion: Option<ExpansionPath>,
}

impl SourceOrigin {
    pub fn new(
        kind: OriginKind,
        span: Option<ByteSpan>,
        expansion: Option<ExpansionPath>,
    ) -> SourceOrigin {
        SourceOrigin {
            kind,
            span,
            expansion,
        }
    }
}

/// Complete origin set for one output node.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OriginSet(BTreeSet<SourceOrigin>);

impl OriginSet {
    pub fn insert(&mut self, origin: SourceOrigin) {
        self.0.insert(origin);
    }

    pub fn extend(&mut self, other: &OriginSet) {
        self.0.extend(other.0.iter().cloned());
    }

    pub fn iter(&self) -> impl Iterator<Item = &SourceOrigin> {
        self.0.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Explicit projection to the Reference-facing primary source span.
    ///
    /// Direct literal/antiquoted source wins. A quotation-produced token then
    /// projects to the macro call, followed by quotation and definition sites.
    /// Recovery is last because it is an editor explanation, never authority for
    /// bytes that were not accepted.
    pub fn primary_span(&self) -> Option<ByteSpan> {
        self.0
            .iter()
            .filter_map(|origin| origin.span.map(|span| (origin_priority(origin.kind), span)))
            .min()
            .map(|(_, span)| span)
    }
}

fn origin_priority(kind: OriginKind) -> u8 {
    match kind {
        OriginKind::Literal => 0,
        OriginKind::MacroCall => 1,
        OriginKind::Antiquotation => 2,
        OriginKind::Quotation => 3,
        OriginKind::MacroDefinition => 4,
        OriginKind::Recovered => 5,
    }
}

/// Output-path to complete origin-set map.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExpansionSourceMap {
    entries: BTreeMap<SyntaxPath, OriginSet>,
}

impl ExpansionSourceMap {
    pub fn new() -> ExpansionSourceMap {
        ExpansionSourceMap::default()
    }

    pub fn record(&mut self, path: SyntaxPath, origin: SourceOrigin) {
        self.entries.entry(path).or_default().insert(origin);
    }

    pub fn record_set(&mut self, path: SyntaxPath, origins: &OriginSet) {
        self.entries.entry(path).or_default().extend(origins);
    }

    pub fn origins(&self, path: &SyntaxPath) -> Option<&OriginSet> {
        self.entries.get(path)
    }

    pub fn paths(&self) -> impl Iterator<Item = &SyntaxPath> {
        self.entries.keys()
    }

    pub fn entries(&self) -> impl Iterator<Item = (&SyntaxPath, &OriginSet)> {
        self.entries.iter()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn add_origin_to_all(&mut self, origin: SourceOrigin) {
        for origins in self.entries.values_mut() {
            origins.insert(origin.clone());
        }
    }

    pub fn prefixed(&self, prefix: &SyntaxPath) -> ExpansionSourceMap {
        let mut prefixed = ExpansionSourceMap::new();
        for (path, origins) in &self.entries {
            prefixed.record_set(prefix.join(path), origins);
        }
        prefixed
    }

    pub fn extend_prefixed(&mut self, prefix: &SyntaxPath, nested: &ExpansionSourceMap) {
        for (path, origins) in &nested.entries {
            self.record_set(prefix.join(path), origins);
        }
    }

    /// Replace the subtree at `output_prefix` with `nested`, composing every
    /// nested origin set with the nearest inherited outer origin set.
    pub fn compose_at(
        &self,
        output_prefix: &SyntaxPath,
        nested: &ExpansionSourceMap,
    ) -> ExpansionSourceMap {
        let inherited = self
            .nearest_origins(output_prefix)
            .cloned()
            .unwrap_or_default();
        let mut composed = self.clone();
        composed
            .entries
            .retain(|path, _| !path.starts_with(output_prefix));
        for (path, origins) in &nested.entries {
            let mut joined = inherited.clone();
            joined.extend(origins);
            composed.record_set(output_prefix.join(path), &joined);
        }
        composed
    }

    fn nearest_origins(&self, path: &SyntaxPath) -> Option<&OriginSet> {
        let mut cursor = path.clone();
        loop {
            if let Some(origins) = self.entries.get(&cursor) {
                return Some(origins);
            }
            cursor.0.pop()?;
        }
    }

    /// Canonical semantic rows. Host paths, timing, and scheduler telemetry have
    /// no input parameter and therefore no route into this identity.
    pub fn canonical(&self) -> String {
        let mut out = String::from("fln.expansion-source-map/1;");
        push_u64(&mut out, self.entries.len() as u64);
        for (path, origins) in &self.entries {
            push_u64_slice(&mut out, path.components());
            push_u64(&mut out, origins.0.len() as u64);
            for origin in &origins.0 {
                out.push(match origin.kind {
                    OriginKind::Literal => 'L',
                    OriginKind::MacroDefinition => 'D',
                    OriginKind::MacroCall => 'C',
                    OriginKind::Quotation => 'Q',
                    OriginKind::Antiquotation => 'A',
                    OriginKind::Recovered => 'R',
                });
                match origin.span {
                    Some(span) => {
                        out.push('S');
                        push_u64(&mut out, span.start().0 as u64);
                        push_u64(&mut out, span.end().0 as u64);
                    }
                    None => out.push('N'),
                }
                match &origin.expansion {
                    Some(expansion) => {
                        out.push('E');
                        push_text(&mut out, &expansion.canonical());
                    }
                    None => out.push('N'),
                }
            }
        }
        out
    }
}

fn push_name(out: &mut String, name: &Name) {
    let components = name_components(name);
    push_u64(out, components.len() as u64);
    for component in components {
        match component {
            NameComponent::Str(value) => {
                out.push('S');
                push_text(out, &value);
            }
            NameComponent::Num {
                value,
                overflowed: false,
            } => {
                out.push('N');
                push_u64(out, value);
            }
            NameComponent::Num {
                value,
                overflowed: true,
            } => {
                out.push('O');
                push_u64(out, value);
            }
        }
    }
}

fn push_u64_slice(out: &mut String, values: &[u64]) {
    push_u64(out, values.len() as u64);
    for value in values {
        push_u64(out, *value);
    }
}

fn push_u64(out: &mut String, value: u64) {
    out.push_str(&value.to_string());
    out.push(';');
}

fn push_text(out: &mut String, value: &str) {
    push_u64(out, value.len() as u64);
    out.push_str(value);
    out.push(';');
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(parts: &[&str]) -> Name {
        Name::from_components(parts.iter().copied())
    }

    #[test]
    fn reference_scope_view_round_trips_context_transitions() {
        let plain = name(&["x"]);
        let first_context = name(&["Main", "decl", "_hygCtx"]);
        let second_context = name(&["Imported", "decl", "_hygCtx"]);
        let one = add_macro_scope(&first_context, &plain, 4).expect("well formed");
        let two = add_macro_scope(&first_context, &one, 9).expect("same context");
        let transitioned = add_macro_scope(&second_context, &two, 3).expect("context transition");
        let view = extract_macro_scopes(&transitioned).expect("extracts");

        assert_eq!(view.name, plain);
        assert_eq!(view.context, second_context);
        assert_eq!(view.scopes, vec![3]);
        assert_eq!(view.review(), transitioned);
        assert_eq!(view.imported.to_display_string(), "Main.decl._hygCtx.4.9");
    }

    #[test]
    fn malformed_hygienic_names_are_typed_refusals() {
        let marker_only = Name::str(
            Name::str(name(&["x"]), MACRO_SCOPES_SEPARATOR),
            MACRO_SCOPES_MARKER,
        );
        assert!(matches!(
            extract_macro_scopes(&marker_only),
            Err(HygieneError::EmptyScopeStack { .. })
        ));

        let no_separator = Name::num(Name::str(name(&["x", "Ctx"]), MACRO_SCOPES_MARKER), 1);
        assert!(matches!(
            extract_macro_scopes(&no_separator),
            Err(HygieneError::MissingSeparator { .. })
        ));
    }

    #[test]
    fn source_map_composition_retains_outer_and_inner_origins() {
        let outer_path = SyntaxPath::root().child(2);
        let outer_origin = SourceOrigin::new(
            OriginKind::MacroCall,
            ByteSpan::new(crate::source::BytePos(10), crate::source::BytePos(20)),
            None,
        );
        let mut outer = ExpansionSourceMap::new();
        outer.record(outer_path.clone(), outer_origin.clone());

        let inner_origin = SourceOrigin::new(
            OriginKind::MacroDefinition,
            ByteSpan::new(crate::source::BytePos(30), crate::source::BytePos(40)),
            None,
        );
        let mut inner = ExpansionSourceMap::new();
        inner.record(SyntaxPath::root().child(0), inner_origin.clone());

        let composed = outer.compose_at(&outer_path, &inner);
        let origins = composed
            .origins(&outer_path.child(0))
            .expect("composed child");
        assert!(origins.iter().any(|origin| origin == &outer_origin));
        assert!(origins.iter().any(|origin| origin == &inner_origin));
        assert_eq!(origins.primary_span(), outer_origin.span);
    }
}
