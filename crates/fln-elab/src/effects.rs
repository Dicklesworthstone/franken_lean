//! Command effect summaries and commutativity analysis (Bet B4, Plan §10.6).
//!
//! Every command executed in an elaboration region captures its input reads
//! and output writes as typed effects. These summaries govern whether commands
//! can run concurrently or must serialize across ordering barriers.
//!
//! Effect accuracy is verified by the perturbation engine ([`crate::perturbation`]).

use fln_core::name::Name;
use std::collections::HashSet;

/// The aspect of a declaration that was observed or queried.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeclAspect {
    /// Only the declaration's type was inspected.
    Type,
    /// The declaration's value / proof body was unfolded or inspected.
    Value,
    /// Attributes or metadata on the declaration were inspected.
    Attributes,
    /// The complete declaration was inspected (type, value, attributes).
    All,
}

/// A fine-grained effect captured during command elaboration.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CommandEffect {
    /// Read a declaration's type, value, or attributes.
    ReadsDecl { name: Name, aspect: DeclAspect },
    /// Queried type-class instances with a given head constant.
    ReadsInstances { class_head: Name },
    /// Read rules from a named simp set.
    ReadsSimpSet { simp_name: Name },
    /// Read productions in a syntax category.
    ReadsGrammar { category: Name },
    /// Read a compiler or toolchain option.
    ReadsOption { key: String },
    /// Admitted or published a new declaration.
    WritesDecl { name: Name },
    /// Registered a new type-class instance.
    WritesInstance {
        class_head: Name,
        instance_name: Name,
    },
    /// Extended a syntax category with new productions.
    WritesGrammar { category: Name },
    /// Mutated an environment extension.
    WritesEnvExtension { extension_name: Name },
    /// Invoked an ambient or toolchain capability.
    UsesCapability { capability_id: String },
    /// An opaque or unanalyzable effect (acts as a full ordering barrier).
    Opaque { reason: String },
}

impl CommandEffect {
    /// Whether this effect is an unanalyzable full barrier.
    pub fn is_barrier(&self) -> bool {
        matches!(self, CommandEffect::Opaque { .. })
    }

    /// Whether this is a write effect.
    pub fn is_write(&self) -> bool {
        matches!(
            self,
            CommandEffect::WritesDecl { .. }
                | CommandEffect::WritesInstance { .. }
                | CommandEffect::WritesGrammar { .. }
                | CommandEffect::WritesEnvExtension { .. }
                | CommandEffect::Opaque { .. }
        )
    }

    /// Whether this is a read effect.
    pub fn is_read(&self) -> bool {
        matches!(
            self,
            CommandEffect::ReadsDecl { .. }
                | CommandEffect::ReadsInstances { .. }
                | CommandEffect::ReadsSimpSet { .. }
                | CommandEffect::ReadsGrammar { .. }
                | CommandEffect::ReadsOption { .. }
        )
    }
}

/// A collection of typed effects capturing the complete footprint of a command.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EffectSummary {
    effects: Vec<CommandEffect>,
    is_demoted_to_opaque: bool,
    demote_reason: Option<String>,
}

impl EffectSummary {
    /// Create an empty effect summary.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a single effect.
    pub fn record(&mut self, effect: CommandEffect) {
        if !self.effects.contains(&effect) {
            self.effects.push(effect);
        }
    }

    /// Mark this summary as demoted to opaque (due to perturbation failure or unanalyzed effect).
    pub fn demote_to_opaque(&mut self, reason: String) {
        self.is_demoted_to_opaque = true;
        self.demote_reason = Some(reason.clone());
        self.record(CommandEffect::Opaque { reason });
    }

    /// Whether this summary represents an ordering barrier.
    pub fn is_barrier(&self) -> bool {
        self.is_demoted_to_opaque || self.effects.iter().any(CommandEffect::is_barrier)
    }

    /// All captured effects.
    pub fn effects(&self) -> &[CommandEffect] {
        &self.effects
    }

    /// Set of declarations read by this command.
    pub fn read_decls(&self) -> HashSet<&Name> {
        self.effects
            .iter()
            .filter_map(|e| match e {
                CommandEffect::ReadsDecl { name, .. } => Some(name),
                _ => None,
            })
            .collect()
    }

    /// Set of declarations written by this command.
    pub fn written_decls(&self) -> HashSet<&Name> {
        self.effects
            .iter()
            .filter_map(|e| match e {
                CommandEffect::WritesDecl { name } => Some(name),
                _ => None,
            })
            .collect()
    }

    /// Set of options read by this command.
    pub fn read_options(&self) -> HashSet<&str> {
        self.effects
            .iter()
            .filter_map(|e| match e {
                CommandEffect::ReadsOption { key } => Some(key.as_str()),
                _ => None,
            })
            .collect()
    }

    /// Check if two effect summaries commute (can safely run in parallel with no hazards).
    ///
    /// Commutativity requires:
    /// 1. Neither is a barrier (Opaque).
    /// 2. No Read-After-Write (RAW) conflict: `self` writes do not intersect `other` reads.
    /// 3. No Write-After-Read (WAR) conflict: `self` reads do not intersect `other` writes.
    /// 4. No Write-After-Write (WAW) conflict: `self` writes do not intersect `other` writes.
    pub fn commutes_with(&self, other: &EffectSummary) -> bool {
        if self.is_barrier() || other.is_barrier() {
            return false;
        }

        // Check declaration conflicts
        let self_w_decls = self.written_decls();
        let other_w_decls = other.written_decls();
        let self_r_decls = self.read_decls();
        let other_r_decls = other.read_decls();

        if !self_w_decls.is_disjoint(&other_w_decls) {
            return false; // WAW
        }
        if !self_w_decls.is_disjoint(&other_r_decls) {
            return false; // RAW/WAR
        }
        if !self_r_decls.is_disjoint(&other_w_decls) {
            return false; // WAR/RAW
        }

        // Check instance conflicts
        for eff1 in &self.effects {
            for eff2 in &other.effects {
                match (eff1, eff2) {
                    (
                        CommandEffect::WritesInstance { class_head: h1, .. },
                        CommandEffect::ReadsInstances { class_head: h2 },
                    )
                    | (
                        CommandEffect::ReadsInstances { class_head: h1 },
                        CommandEffect::WritesInstance { class_head: h2, .. },
                    )
                    | (
                        CommandEffect::WritesInstance { class_head: h1, .. },
                        CommandEffect::WritesInstance { class_head: h2, .. },
                    ) if h1 == h2 => return false,

                    (
                        CommandEffect::WritesGrammar { category: c1 },
                        CommandEffect::ReadsGrammar { category: c2 },
                    )
                    | (
                        CommandEffect::ReadsGrammar { category: c1 },
                        CommandEffect::WritesGrammar { category: c2 },
                    )
                    | (
                        CommandEffect::WritesGrammar { category: c1 },
                        CommandEffect::WritesGrammar { category: c2 },
                    ) if c1 == c2 => return false,

                    (
                        CommandEffect::WritesEnvExtension { extension_name: e1 },
                        CommandEffect::WritesEnvExtension { extension_name: e2 },
                    ) if e1 == e2 => return false,

                    _ => {}
                }
            }
        }

        true
    }
}
