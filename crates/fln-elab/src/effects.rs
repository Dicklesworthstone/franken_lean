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
    /// Whether this effect requires a full source-order barrier.
    ///
    /// Ambient capabilities have no rollback contract. Generic extension
    /// writes have no typed read key, so they may affect options, simp sets,
    /// instances, grammar, or declaration attributes.
    pub fn is_barrier(&self) -> bool {
        matches!(
            self,
            CommandEffect::Opaque { .. }
                | CommandEffect::UsesCapability { .. }
                | CommandEffect::WritesEnvExtension { .. }
        )
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

    /// Join another footprint without losing an opaque demotion.
    pub fn extend(&mut self, other: &Self) {
        for effect in &other.effects {
            self.record(effect.clone());
        }
        if other.is_demoted_to_opaque {
            self.is_demoted_to_opaque = true;
            if self.demote_reason.is_none() {
                self.demote_reason = other.demote_reason.clone();
            }
        }
    }

    /// Whether a product can be speculated or replayed without repeating an
    /// ambient action or omitting a state change not represented in the product.
    ///
    /// ElabUnitProduct carries declarations, but not instance/grammar/extension
    /// deltas. Those writers must execute once at their canonical position.
    pub fn is_replay_safe(&self) -> bool {
        !self.is_barrier()
            && self.effects.iter().all(|effect| {
                effect.is_read() || matches!(effect, CommandEffect::WritesDecl { .. })
            })
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
    /// 1. Neither is an opaque, ambient-capability, or generic-extension barrier.
    /// 2. No Read-After-Write (RAW) conflict: `self` writes do not intersect `other` reads.
    /// 3. No Write-After-Read (WAR) conflict: `self` reads do not intersect `other` writes.
    /// 4. No Write-After-Write (WAW) conflict: `self` writes do not intersect `other` writes.
    pub fn commutes_with(&self, other: &EffectSummary) -> bool {
        if self.is_barrier() || other.is_barrier() {
            return false;
        }

        // Compare typed keys directly during staged-product validation; avoid
        // allocating four temporary declaration sets for each comparison.
        for eff1 in &self.effects {
            for eff2 in &other.effects {
                match (eff1, eff2) {
                    (
                        CommandEffect::WritesDecl { name: n1 },
                        CommandEffect::ReadsDecl { name: n2, .. },
                    )
                    | (
                        CommandEffect::ReadsDecl { name: n1, .. },
                        CommandEffect::WritesDecl { name: n2 },
                    )
                    | (
                        CommandEffect::WritesDecl { name: n1 },
                        CommandEffect::WritesDecl { name: n2 },
                    ) if n1 == n2 => return false,

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

                    _ => {}
                }
            }
        }

        true
    }
}
