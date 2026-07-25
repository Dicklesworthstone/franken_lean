//! The Grimoire environment (plan §7.1): semantically the Reference's name→constant
//! map plus contract-registered extensions; mechanically ours — persistent maps with
//! structural sharing, so a snapshot is an O(1) clone and mutation after a fork is
//! invisible to the fork (the primitive under Athanor's speculative parallelism,
//! Lantern's per-request views, and Envoy's search trees).
//!
//! Every commit exposes two roots: the **logical root** (declarations + extension
//! deltas + options; the cache key the Ledger, receipts, and Envoy speak) and a
//! separate **operational-metadata root** — two hosts producing the same trusted
//! environment share a logical root even when their operational manifests differ.

use std::sync::Arc;

use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::{LogicalRoot, LogicalRootBuilder};

use crate::constants::{ConstantInfo, DefinitionSafety, QuotKind, ReducibilityHints};
use crate::extensions::{
    CheckpointError, CheckpointLimits, CheckpointSemantics, ExtensionCheckpoint,
    ExtensionDescriptor, ExtensionState,
};
#[cfg(test)]
use crate::extensions::{MergeSemantics, PayloadProvenance};
use crate::pmap::{CollisionBudget, CollisionExhausted, PKey, PMap};

/// Stable `Domain::DeclContent` tags. These are schema values, not Rust enum
/// discriminants: changing them requires an explicit identity/epoch decision.
#[forbid(clippy::as_conversions)]
const fn definition_safety_tag(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Unsafe => 0,
        DefinitionSafety::Safe => 1,
        DefinitionSafety::Partial => 2,
    }
}

#[forbid(clippy::as_conversions)]
const fn quot_kind_tag(kind: QuotKind) -> u8 {
    match kind {
        QuotKind::Type => 0,
        QuotKind::Ctor => 1,
        QuotKind::Lift => 2,
        QuotKind::Ind => 3,
    }
}

/// Lossless on FrankenLean's certified Rust targets, whose pointer widths are at
/// most 64 bits. This conversion stays outside the enum-tag cast prohibition so
/// that the policy does not introduce a fallible or panicking length path.
#[allow(clippy::as_conversions)]
const fn usize_to_u64(value: usize) -> u64 {
    value as u64
}

/// Write a mutual-block membership list into declaration identity.
///
/// The order and multiplicity are semantic input. Keep this as one forward pass:
/// no sorting, deduplication, or structure proportional to the containing
/// [`Environment`] belongs in declaration identity.
fn write_mutual_membership(w: &mut CanonWriter, members: &[Name]) {
    w.u64(usize_to_u64(members.len()));
    for member in members {
        member.write_body(w);
    }
}

impl PKey for Name {
    fn key_hash(&self) -> u64 {
        // The stored Reference-observable hash; collisions are handled by the trie's
        // buckets, equality stays structural.
        self.hash()
    }
}

/// Typed refusals — an environment mutation never panics and never silently drops.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvError {
    /// The kernel's already-declared law: one name, one constant.
    DuplicateDeclaration {
        name: Name,
    },
    DuplicateExtension {
        name: Name,
    },
    UnknownExtension {
        name: Name,
    },
    Checkpoint(CheckpointError),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::DuplicateDeclaration { name } => {
                write!(
                    f,
                    "constant `{}` is already declared",
                    name.to_display_string()
                )
            }
            EnvError::DuplicateExtension { name } => {
                write!(
                    f,
                    "extension `{}` is already registered",
                    name.to_display_string()
                )
            }
            EnvError::UnknownExtension { name } => {
                write!(
                    f,
                    "extension `{}` is not registered",
                    name.to_display_string()
                )
            }
            EnvError::Checkpoint(error) => error.fmt(f),
        }
    }
}

/// The typed outcome of a resource-bounded declaration admission (bead `fln-amv.13`).
///
/// Three-way by construction, so FL-INV-07's law is a type error to violate rather
/// than a convention to remember: a caller cannot read exhaustion as acceptance or as
/// rejection, because there is no `Result` whose `Err` means both. The distinction is
/// load-bearing — a rejection says *this declaration is not admissible*, while an
/// inconclusive says *we did not find out*, and only the first may ever be cached,
/// counted, or reported as a verdict.
#[derive(Debug, Clone, PartialEq)]
pub enum DeclAdmission {
    /// The declaration entered the returned environment.
    Admitted(Environment),
    /// A complete, resource-independent determination that the declaration is not
    /// admissible — today, the kernel's one-name-one-constant law.
    Rejected(EnvError),
    /// The adversarial-collision budget bound before any mutation. Not accepted, not
    /// rejected, not checked, not cacheable; the receiving environment is unchanged.
    /// A hash collision alone never produces this — only a collision large or heavy
    /// enough to exceed the reviewed envelope does.
    Inconclusive(CollisionExhausted),
}

impl DeclAdmission {
    /// Stable evidence label, matching the vocabulary
    /// [`DeclClosureStatus`](crate::decl_closure::DeclClosureStatus) already uses.
    pub fn outcome_label(&self) -> &'static str {
        match self {
            DeclAdmission::Admitted(_) => "admitted",
            DeclAdmission::Rejected(_) => "rejected",
            DeclAdmission::Inconclusive(_) => "inconclusive-collision-budget",
        }
    }

    /// Only an admitted declaration may feed a cache. Inconclusive outcomes are not
    /// publication-grade, and re-admitting one later must redo the work rather than
    /// replay a stored refusal.
    pub fn is_cacheable(&self) -> bool {
        matches!(self, DeclAdmission::Admitted(_))
    }

    /// The environment to carry forward, if any. `None` for both non-admitted arms —
    /// the caller keeps the environment it already held, unchanged.
    pub fn environment(&self) -> Option<&Environment> {
        match self {
            DeclAdmission::Admitted(environment) => Some(environment),
            DeclAdmission::Rejected(_) | DeclAdmission::Inconclusive(_) => None,
        }
    }

    /// Whether this outcome is in the inconclusive family. Kept explicit so evidence
    /// rows never have to pattern-match a shape that may gain arms later.
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, DeclAdmission::Inconclusive(_))
    }
}

/// The environment. `Clone` IS `snapshot`: O(1), fully isolated.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Environment {
    constants: PMap<Name, Arc<ConstantInfo>>,
    extensions: PMap<Name, Arc<ExtensionState>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment::default()
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    /// `Environment.find`.
    pub fn find(&self, name: &Name) -> Option<&ConstantInfo> {
        self.constants.get(name).map(Arc::as_ref)
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.constants.contains_key(name)
    }

    /// Add a constant. One name, one constant — a duplicate is a typed refusal
    /// (the kernel's admission law; nothing here can overwrite a declaration).
    ///
    /// This is the unbounded *semantic* operation: it never refuses a valid
    /// declaration merely because its 64-bit hash collides with another's. An
    /// admission boundary exposed to untrusted input must instead call
    /// [`Environment::try_add_decl_with_budget`], which bounds the adversarial
    /// full-hash-collision work without ever turning a collision into a rejection.
    pub fn add_decl(&self, info: ConstantInfo) -> Result<Environment, EnvError> {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return Err(EnvError::DuplicateDeclaration { name });
        }
        Ok(Environment {
            constants: self.constants.insert(name, Arc::new(info)),
            extensions: self.extensions.clone(),
        })
    }

    /// Resource-bounded declaration admission (bead `fln-amv.13`).
    ///
    /// `add_decl`'s duplicate law still applies and is evaluated first, because it
    /// is a complete determination that costs a single bounded lookup. Only then is
    /// the insertion preflighted against `budget`, so a crafted family of names
    /// sharing one `key_hash` cannot drive unbounded work through this boundary.
    ///
    /// Exhaustion is atomic and **inconclusive**, never a rejection: `self` is
    /// unchanged, nothing is published, and the caller learns that no verdict was
    /// reached about this declaration (FL-INV-07). Refusing the *insertion* is not
    /// the same as refusing the *declaration*, and the three-way
    /// [`DeclAdmission`] makes conflating them a type error rather than a
    /// convention.
    ///
    /// `expanded_weight` is supplied by the caller because a generic map cannot
    /// infer the semantic weight of an opaque declaration; the decoder or
    /// admission boundary that parsed it can.
    pub fn try_add_decl_with_budget(
        &self,
        info: ConstantInfo,
        expanded_weight: u64,
        budget: CollisionBudget,
    ) -> DeclAdmission {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return DeclAdmission::Rejected(EnvError::DuplicateDeclaration { name });
        }
        match self
            .constants
            .try_insert_with_budget(name, Arc::new(info), expanded_weight, budget)
        {
            Ok(constants) => DeclAdmission::Admitted(Environment {
                constants,
                extensions: self.extensions.clone(),
            }),
            Err(exhausted) => DeclAdmission::Inconclusive(exhausted),
        }
    }

    /// Register an extension with its declared contracts.
    pub fn register_extension(
        &self,
        descriptor: ExtensionDescriptor,
    ) -> Result<Environment, EnvError> {
        let name = descriptor.name.clone();
        if self.extensions.contains_key(&name) {
            return Err(EnvError::DuplicateExtension { name });
        }
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self
                .extensions
                .insert(name, Arc::new(ExtensionState::new(descriptor))),
        })
    }

    /// Append one replay entry to a registered extension.
    pub fn push_extension_entry(
        &self,
        extension: &Name,
        payload: impl Into<Arc<[u8]>>,
    ) -> Result<Environment, EnvError> {
        let Some(state) = self.extensions.get(extension) else {
            return Err(EnvError::UnknownExtension {
                name: extension.clone(),
            });
        };
        let next = state.push_entry(payload);
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(extension.clone(), Arc::new(next)),
        })
    }

    pub fn extension(&self, name: &Name) -> Option<&ExtensionState> {
        self.extensions.get(name).map(Arc::as_ref)
    }

    /// Capture one registered extension under its declared checkpoint contract.
    /// A suffix base is another immutable environment snapshot; full-journal mode
    /// requires `None` and carries no ambient extension history.
    pub fn checkpoint_extension(
        &self,
        extension: &Name,
        base: Option<&Environment>,
        limits: CheckpointLimits,
    ) -> Result<ExtensionCheckpoint, EnvError> {
        let state = self
            .extension(extension)
            .ok_or_else(|| EnvError::UnknownExtension {
                name: extension.clone(),
            })?;
        let base_state = match base {
            Some(base) => {
                Some(
                    base.extension(extension)
                        .ok_or_else(|| EnvError::UnknownExtension {
                            name: extension.clone(),
                        })?,
                )
            }
            None => None,
        };
        state
            .checkpoint(base_state, limits)
            .map_err(EnvError::Checkpoint)
    }

    /// Apply a checkpoint to the matching registry slot and return a new isolated
    /// environment snapshot. Declarations and unrelated extensions remain shared.
    pub fn apply_extension_checkpoint(
        &self,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
    ) -> Result<Environment, EnvError> {
        let name = &checkpoint.descriptor().name;
        let registered = self
            .extension(name)
            .ok_or_else(|| EnvError::UnknownExtension { name: name.clone() })?;
        if checkpoint.mode() == CheckpointSemantics::FullJournal
            && registered.descriptor != *checkpoint.descriptor()
        {
            let error = if registered.descriptor.name != checkpoint.descriptor().name {
                CheckpointError::ExtensionNameMismatch {
                    expected: checkpoint.descriptor().name.clone(),
                    actual: registered.descriptor.name.clone(),
                }
            } else {
                CheckpointError::ContractMismatch {
                    expected: checkpoint.descriptor().clone(),
                    actual: registered.descriptor.clone(),
                }
            };
            return Err(EnvError::Checkpoint(error));
        }
        let base = match checkpoint.mode() {
            CheckpointSemantics::JournalSuffix => Some(registered),
            CheckpointSemantics::FullJournal => None,
        };
        let restored =
            ExtensionState::restore(base, checkpoint, limits).map_err(EnvError::Checkpoint)?;
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(name.clone(), Arc::new(restored)),
        })
    }

    /// The canonical content digest of one constant (Domain::DeclContent): the
    /// deterministic projection the logical root aggregates. Byte-level olean parity
    /// is the codec's business; this digest is FrankenLean's own identity.
    #[forbid(clippy::as_conversions)]
    pub fn decl_content_digest(info: &ConstantInfo) -> Digest {
        let mut w = CanonWriter::new();
        w.str(info.kind_name());
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(usize_to_u64(base.level_params.len()));
        for p in &base.level_params {
            p.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Axiom(v) => w.bool(v.is_unsafe),
            ConstantInfo::Defn(v) => {
                v.value.write_body(&mut w);
                match v.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(h) => {
                        w.u8(2);
                        w.u32(h);
                    }
                }
                w.u8(definition_safety_tag(v.safety));
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Thm(v) => {
                v.value.write_body(&mut w);
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Opaque(v) => {
                v.value.write_body(&mut w);
                w.bool(v.is_unsafe);
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Quot(v) => w.u8(quot_kind_tag(v.kind)),
            ConstantInfo::Induct(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_nested);
                w.bool(v.is_rec);
                w.bool(v.is_unsafe);
                w.bool(v.is_reflexive);
                w.u64(usize_to_u64(v.ctors.len()));
                for n in &v.ctors {
                    n.write_body(&mut w);
                }
                // The mutual-inductive block is part of the declaration's content
                // (as it is for `Defn`/`Thm`): two inductives identical except for
                // their block grouping are distinct declarations and must not share
                // a content digest.
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Ctor(v) => {
                v.induct.write_body(&mut w);
                w.u32(v.cidx);
                w.u32(v.num_params);
                w.u32(v.num_fields);
                w.bool(v.is_unsafe);
            }
            ConstantInfo::Rec(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_motives);
                w.u32(v.num_minors);
                w.bool(v.k);
                w.bool(v.is_unsafe);
                w.u64(usize_to_u64(v.rules.len()));
                for rule in &v.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                // The mutual block is content here too (mirrors `Defn`/`Thm`).
                write_mutual_membership(&mut w, &v.all);
            }
        }
        hash(Domain::DeclContent, &w.into_bytes())
    }

    /// The logical root of this commit: declarations + extension deltas + options —
    /// and nothing else (wall-clock, paths, and schedule have no way in).
    pub fn logical_root(&self, options: &KVMap) -> LogicalRoot {
        let mut builder = LogicalRootBuilder::new();
        for (name, info) in self.constants.iter() {
            builder.add_decl(name, Environment::decl_content_digest(info));
        }
        for (name, state) in self.extensions.iter() {
            builder.add_extension_delta(name, state.content_digest());
        }
        builder.set_options(options);
        builder.finalize()
    }

    /// The operational-metadata root: host facts, paths, timings — everything the
    /// logical root deliberately excludes, digested separately so receipts can carry
    /// both without ever mixing them.
    pub fn operational_root(metadata: &KVMap) -> Digest {
        hash(Domain::OperationalMeta, &metadata.to_canonical_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{
        AxiomVal, ConstantVal, DefinitionVal, InductiveVal, OpaqueVal, QuotVal, RecursorRule,
        RecursorVal, TheoremVal,
    };
    use crate::pmap::CollisionResource;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::DataValue;
    use std::collections::HashSet;

    fn n(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn axiom(name: &str) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DeclarationTagCase {
        Definition(DefinitionSafety),
        Quotient(QuotKind),
    }

    impl DeclarationTagCase {
        const ALL: [DeclarationTagCase; 7] = [
            DeclarationTagCase::Definition(DefinitionSafety::Unsafe),
            DeclarationTagCase::Definition(DefinitionSafety::Safe),
            DeclarationTagCase::Definition(DefinitionSafety::Partial),
            DeclarationTagCase::Quotient(QuotKind::Type),
            DeclarationTagCase::Quotient(QuotKind::Ctor),
            DeclarationTagCase::Quotient(QuotKind::Lift),
            DeclarationTagCase::Quotient(QuotKind::Ind),
        ];

        const fn family(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(_) => "definition_safety",
                DeclarationTagCase::Quotient(_) => "quot_kind",
            }
        }

        const fn variant(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => "unsafe",
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => "safe",
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => "partial",
                DeclarationTagCase::Quotient(QuotKind::Type) => "type",
                DeclarationTagCase::Quotient(QuotKind::Ctor) => "ctor",
                DeclarationTagCase::Quotient(QuotKind::Lift) => "lift",
                DeclarationTagCase::Quotient(QuotKind::Ind) => "ind",
            }
        }

        const fn kind_name(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(_) => "definition",
                DeclarationTagCase::Quotient(_) => "quotient",
            }
        }

        const fn canonical_tag(self) -> u8 {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => 0,
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => 1,
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => 2,
                DeclarationTagCase::Quotient(QuotKind::Type) => 0,
                DeclarationTagCase::Quotient(QuotKind::Ctor) => 1,
                DeclarationTagCase::Quotient(QuotKind::Lift) => 2,
                DeclarationTagCase::Quotient(QuotKind::Ind) => 3,
            }
        }

        const fn production_tag(self) -> u8 {
            match self {
                DeclarationTagCase::Definition(safety) => definition_safety_tag(safety),
                DeclarationTagCase::Quotient(kind) => quot_kind_tag(kind),
            }
        }

        /// Frozen `rich-same-name-v1` complete-stream goldens. These constants
        /// prevent coordinated drift in both the production encoder and the
        /// independent in-file model from silently redefining declaration identity.
        const fn golden_stream_bytes(self) -> usize {
            match self {
                DeclarationTagCase::Definition(_) => 286,
                DeclarationTagCase::Quotient(_) => 157,
            }
        }

        const fn golden_stream_hash(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => {
                    "157d1d61733828db775de4ee898c84ab608f57ca609965b7d8aba3ef9e3a1a5e"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => {
                    "e3a242872a3ffd8c515331f5821c1b42f81780060413feb33f2d63ca8aeb697d"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => {
                    "00a37c5b26ce2df45b79a0e5ddc0b32fe7ba3fd16e2267a8b199a3a2a5421f52"
                }
                DeclarationTagCase::Quotient(QuotKind::Type) => {
                    "d85f3e7116bf264784bad45e2d9a9acc9ad69ca15c2387f73d390b51c1a52674"
                }
                DeclarationTagCase::Quotient(QuotKind::Ctor) => {
                    "7a209bee80a459d0eddd0e82ced0b96345895dfdf11cb420729783eff42fe0a0"
                }
                DeclarationTagCase::Quotient(QuotKind::Lift) => {
                    "706326aa022cfa4b76f80ea32c04ad0aef70d796da8762b86771b3b4d42937ad"
                }
                DeclarationTagCase::Quotient(QuotKind::Ind) => {
                    "32cecea0df45330f5ea249486eb8c0dd4ff236dc27ca90e79122de9f7e3d365a"
                }
            }
        }

        const fn golden_digest(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => {
                    "e6e48d3267b42c87425ac704373120f0c4624c591f6c3218412cdfd5464443ab"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => {
                    "5995ca5cc9f678192cb1700abb6bc18a87af673a6f3285cc9d55caa9b20bb6b0"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => {
                    "5a313316b29da1dab36b88cd02d1d52b96b025a3cb6b9682d0ba10eb59ae76d1"
                }
                DeclarationTagCase::Quotient(QuotKind::Type) => {
                    "64a010c5b799b51b464f4394db8f06a4d7f0c8f98a89bc634cddf3936f3a431f"
                }
                DeclarationTagCase::Quotient(QuotKind::Ctor) => {
                    "d8fc3394629ba859ee37b56dd6d937d787aa86b607b02941091a8699983e0589"
                }
                DeclarationTagCase::Quotient(QuotKind::Lift) => {
                    "804e0ddc5baea6f095d63662b95d303a11c7f33cc92c8d5c77efeb96df021706"
                }
                DeclarationTagCase::Quotient(QuotKind::Ind) => {
                    "7e0d5346e053845bda23a4fb2f3edf80f7daa3f86898a129d66d0531e0e22066"
                }
            }
        }

        const fn golden_root(self) -> &'static str {
            match self {
                DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => {
                    "87d17589cf2a1222d19498e2c4b398107043556cf546281992f223cb9f5a94a9"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Safe) => {
                    "69a4eda482d75712ead5edea8d70692319ac48b9b532b9944bd681e5d94b19ac"
                }
                DeclarationTagCase::Definition(DefinitionSafety::Partial) => {
                    "d234cc1f558ec38a8a8c6ba090236f2239dcd3694b38ea955262cb709016ec47"
                }
                DeclarationTagCase::Quotient(QuotKind::Type) => {
                    "4bf46c6cd5c5282272a303bed04d36d4a5c3d84684b3b588e821564368e10a54"
                }
                DeclarationTagCase::Quotient(QuotKind::Ctor) => {
                    "05b8fe41a9783da42b03c43ec645d7fd239f924ac1996c2112819d7046aa26fe"
                }
                DeclarationTagCase::Quotient(QuotKind::Lift) => {
                    "08dc046203aec4b81143baad0afcebd7655e77e9a4fc813d61fd67fb304edae5"
                }
                DeclarationTagCase::Quotient(QuotKind::Ind) => {
                    "4edbf7598d4cbc73861526c523b02b126a13eaaa29e5f16b6a4a5b55e39b6414"
                }
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DeclarationTagDigestModel {
        Canonical,
        OmitTag,
        DebugText,
        CastAfterSourceReorder,
        MoveTagAcrossAdjacentField,
        WrongDomain,
    }

    fn tagged_declaration(case: DeclarationTagCase, unique_name: bool) -> ConstantInfo {
        let name = if unique_name {
            format!("tagged.{}.{}", case.family(), case.variant())
        } else {
            "tagged".to_owned()
        };
        let name = Name::str(Name::anonymous(), name);
        let base = ConstantVal {
            name: name.clone(),
            level_params: vec![n("u"), n("v")],
            type_: Expr::app(
                Expr::sort(Level::param(n("u"))),
                Expr::const_(n("carrier"), vec![Level::param(n("v"))]),
            ),
        };
        match case {
            DeclarationTagCase::Definition(safety) => ConstantInfo::Defn(DefinitionVal {
                base,
                value: Expr::app(
                    Expr::const_(n("body"), vec![Level::param(n("u"))]),
                    Expr::sort(Level::param(n("v"))),
                ),
                hints: ReducibilityHints::Regular(0xa1b2_c3d4),
                safety,
                all: vec![name, n("peer")],
            }),
            DeclarationTagCase::Quotient(kind) => ConstantInfo::Quot(QuotVal { base, kind }),
        }
    }

    fn write_modeled_declaration_tag(
        w: &mut CanonWriter,
        case: DeclarationTagCase,
        model: DeclarationTagDigestModel,
    ) {
        match model {
            DeclarationTagDigestModel::OmitTag => {}
            DeclarationTagDigestModel::DebugText => w.str(case.variant()),
            DeclarationTagDigestModel::CastAfterSourceReorder => {
                let source_order_tag = match case {
                    DeclarationTagCase::Definition(DefinitionSafety::Unsafe) => 1,
                    DeclarationTagCase::Definition(DefinitionSafety::Safe) => 2,
                    DeclarationTagCase::Definition(DefinitionSafety::Partial) => 0,
                    DeclarationTagCase::Quotient(QuotKind::Type) => 1,
                    DeclarationTagCase::Quotient(QuotKind::Ctor) => 2,
                    DeclarationTagCase::Quotient(QuotKind::Lift) => 3,
                    DeclarationTagCase::Quotient(QuotKind::Ind) => 0,
                };
                w.u8(source_order_tag);
            }
            DeclarationTagDigestModel::Canonical
            | DeclarationTagDigestModel::MoveTagAcrossAdjacentField
            | DeclarationTagDigestModel::WrongDomain => w.u8(case.canonical_tag()),
        }
    }

    /// Control-flow-independent model of the complete Definition/Quotient
    /// declaration streams. It intentionally avoids production kind/base/tag and
    /// mutual-membership helpers.
    fn modeled_tagged_declaration_bytes(
        case: DeclarationTagCase,
        info: &ConstantInfo,
        model: DeclarationTagDigestModel,
    ) -> Vec<u8> {
        let base = match (case, info) {
            (DeclarationTagCase::Definition(_), ConstantInfo::Defn(value)) => &value.base,
            (DeclarationTagCase::Quotient(_), ConstantInfo::Quot(value)) => &value.base,
            _ => unreachable!("tagged declaration case and fixture must agree"),
        };
        let mut w = CanonWriter::new();
        w.str(case.kind_name());
        base.name.write_body(&mut w);
        w.u64(usize_to_u64(base.level_params.len()));
        for parameter in &base.level_params {
            parameter.write_body(&mut w);
        }
        if matches!(
            (case, model),
            (
                DeclarationTagCase::Quotient(_),
                DeclarationTagDigestModel::MoveTagAcrossAdjacentField
            )
        ) {
            write_modeled_declaration_tag(&mut w, case, model);
        }
        base.type_.write_body(&mut w);
        match (case, info) {
            (DeclarationTagCase::Definition(_), ConstantInfo::Defn(value)) => {
                value.value.write_body(&mut w);
                let move_tag_across_adjacent_field =
                    matches!(model, DeclarationTagDigestModel::MoveTagAcrossAdjacentField);
                if move_tag_across_adjacent_field {
                    write_modeled_declaration_tag(&mut w, case, model);
                }
                match value.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(height) => {
                        w.u8(2);
                        w.u32(height);
                    }
                }
                if !move_tag_across_adjacent_field {
                    write_modeled_declaration_tag(&mut w, case, model);
                }
                w.u64(usize_to_u64(value.all.len()));
                for member in &value.all {
                    member.write_body(&mut w);
                }
            }
            (DeclarationTagCase::Quotient(_), ConstantInfo::Quot(_)) => {
                if !matches!(model, DeclarationTagDigestModel::MoveTagAcrossAdjacentField) {
                    write_modeled_declaration_tag(&mut w, case, model);
                }
            }
            _ => unreachable!("tagged declaration case and fixture must agree"),
        }
        w.into_bytes()
    }

    fn modeled_tagged_declaration_digest(
        case: DeclarationTagCase,
        info: &ConstantInfo,
        model: DeclarationTagDigestModel,
    ) -> Digest {
        let bytes = modeled_tagged_declaration_bytes(case, info, model);
        let domain = if matches!(model, DeclarationTagDigestModel::WrongDomain) {
            Domain::Fixture
        } else {
            Domain::DeclContent
        };
        hash(domain, &bytes)
    }

    fn tagged_environment(cases: impl IntoIterator<Item = DeclarationTagCase>) -> Environment {
        let mut environment = Environment::new();
        for case in cases {
            environment = environment
                .add_decl(tagged_declaration(case, true))
                .expect("tagged declaration fixture builds");
        }
        environment
    }

    fn permuted_tag_cases(
        cases: &[DeclarationTagCase],
        worker_index: usize,
    ) -> Vec<DeclarationTagCase> {
        let start = worker_index % cases.len();
        let step = 1 + (worker_index / cases.len()) % (cases.len() - 1);
        (0..cases.len())
            .map(|offset| cases[(start + offset * step) % cases.len()])
            .collect()
    }

    fn tag_case_order_id(cases: &[DeclarationTagCase]) -> Digest {
        let mut w = CanonWriter::new();
        w.str("fln.test.declaration-tag-order");
        w.u16(1);
        w.u64(usize_to_u64(cases.len()));
        for case in cases {
            w.str(case.family());
            w.str(case.variant());
        }
        hash(Domain::Fixture, &w.into_bytes())
    }

    #[derive(Debug, Clone, Copy)]
    enum AllBearingKind {
        Definition,
        Theorem,
        Opaque,
        Inductive,
        Recursor,
    }

    impl AllBearingKind {
        const ALL: [AllBearingKind; 5] = [
            AllBearingKind::Definition,
            AllBearingKind::Theorem,
            AllBearingKind::Opaque,
            AllBearingKind::Inductive,
            AllBearingKind::Recursor,
        ];

        const fn label(self) -> &'static str {
            match self {
                AllBearingKind::Definition => "definition",
                AllBearingKind::Theorem => "theorem",
                AllBearingKind::Opaque => "opaque",
                AllBearingKind::Inductive => "inductive",
                AllBearingKind::Recursor => "recursor",
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    enum MembershipModel {
        Canonical,
        DropList,
        OmitCount,
        SortMembers,
    }

    fn all_bearing_decl(kind: AllBearingKind, all: Vec<Name>) -> ConstantInfo {
        let body = || Expr::const_(n("body"), vec![Level::param(n("u"))]);
        let base = || ConstantVal {
            name: n("d"),
            level_params: vec![n("u")],
            type_: Expr::sort(Level::param(n("u"))),
        };
        match kind {
            AllBearingKind::Definition => ConstantInfo::Defn(DefinitionVal {
                base: base(),
                value: body(),
                hints: ReducibilityHints::Regular(7),
                safety: DefinitionSafety::Partial,
                all,
            }),
            AllBearingKind::Theorem => ConstantInfo::Thm(TheoremVal {
                base: base(),
                value: body(),
                all,
            }),
            AllBearingKind::Opaque => ConstantInfo::Opaque(OpaqueVal {
                base: base(),
                value: body(),
                is_unsafe: true,
                all,
            }),
            AllBearingKind::Inductive => ConstantInfo::Induct(InductiveVal {
                base: base(),
                num_params: 2,
                num_indices: 1,
                all,
                ctors: vec![n("mk"), n("mkAlt")],
                num_nested: 3,
                is_rec: true,
                is_unsafe: true,
                is_reflexive: true,
            }),
            AllBearingKind::Recursor => ConstantInfo::Rec(RecursorVal {
                base: base(),
                all,
                num_params: 2,
                num_indices: 1,
                num_motives: 1,
                num_minors: 2,
                rules: vec![
                    RecursorRule {
                        ctor: n("mk"),
                        nfields: 3,
                        rhs: body(),
                    },
                    RecursorRule {
                        ctor: n("mkAlt"),
                        nfields: 4,
                        rhs: Expr::const_(n("bodyAlt"), vec![Level::zero()]),
                    },
                ],
                k: true,
                is_unsafe: true,
            }),
        }
    }

    fn write_membership_model(w: &mut CanonWriter, members: &[Name], model: MembershipModel) {
        match model {
            MembershipModel::Canonical => {
                w.u64(usize_to_u64(members.len()));
                for member in members {
                    member.write_body(w);
                }
            }
            MembershipModel::DropList => {}
            MembershipModel::OmitCount => {
                for member in members {
                    member.write_body(w);
                }
            }
            MembershipModel::SortMembers => {
                let mut sorted = members.to_vec();
                sorted.sort();
                w.u64(usize_to_u64(sorted.len()));
                for member in &sorted {
                    member.write_body(w);
                }
            }
        }
    }

    /// Control-flow-independent declaration layout model for the five variants
    /// carrying mutual-block membership. It intentionally shares only the primitive
    /// canonical codecs and registered hash implementation with production.
    fn modeled_all_bearing_digest(
        info: &ConstantInfo,
        membership_model: MembershipModel,
        domain: Domain,
    ) -> Digest {
        let mut w = CanonWriter::new();
        let kind_name = match info {
            ConstantInfo::Defn(_) => "definition",
            ConstantInfo::Thm(_) => "theorem",
            ConstantInfo::Opaque(_) => "opaque",
            ConstantInfo::Induct(_) => "inductive",
            ConstantInfo::Rec(_) => "recursor",
            _ => unreachable!("the model accepts only all-bearing declarations"),
        };
        w.str(kind_name);
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(usize_to_u64(base.level_params.len()));
        for parameter in &base.level_params {
            parameter.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Defn(value) => {
                value.value.write_body(&mut w);
                match value.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(height) => {
                        w.u8(2);
                        w.u32(height);
                    }
                }
                let safety_tag = match value.safety {
                    DefinitionSafety::Unsafe => 0,
                    DefinitionSafety::Safe => 1,
                    DefinitionSafety::Partial => 2,
                };
                w.u8(safety_tag);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Thm(value) => {
                value.value.write_body(&mut w);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Opaque(value) => {
                value.value.write_body(&mut w);
                w.bool(value.is_unsafe);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Induct(value) => {
                w.u32(value.num_params);
                w.u32(value.num_indices);
                w.u32(value.num_nested);
                w.bool(value.is_rec);
                w.bool(value.is_unsafe);
                w.bool(value.is_reflexive);
                w.u64(usize_to_u64(value.ctors.len()));
                for ctor in &value.ctors {
                    ctor.write_body(&mut w);
                }
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Rec(value) => {
                w.u32(value.num_params);
                w.u32(value.num_indices);
                w.u32(value.num_motives);
                w.u32(value.num_minors);
                w.bool(value.k);
                w.bool(value.is_unsafe);
                w.u64(usize_to_u64(value.rules.len()));
                for rule in &value.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                write_membership_model(&mut w, &value.all, membership_model);
            }
            _ => unreachable!("the model accepts only all-bearing declarations"),
        }
        hash(domain, &w.into_bytes())
    }

    fn canonical_name_body_bytes(names: &[Name]) -> usize {
        names
            .iter()
            .map(|name| {
                let mut w = CanonWriter::new();
                name.write_body(&mut w);
                w.into_bytes().len()
            })
            .sum()
    }

    fn descriptor(name: &str) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: n(name),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        }
    }

    #[test]
    fn add_find_and_the_one_name_one_constant_law() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        assert_eq!(env.len(), 1);
        assert_eq!(env.find(&n("a")).expect("found").kind_name(), "axiom");
        assert!(env.find(&n("b")).is_none());
        let dup = env.add_decl(axiom("a")).expect_err("duplicate refused");
        assert_eq!(dup, EnvError::DuplicateDeclaration { name: n("a") });
    }

    #[test]
    fn snapshots_are_isolated_forks() {
        let base = Environment::new().add_decl(axiom("a")).expect("adds");
        let fork = base.clone(); // O(1) snapshot
        let extended = base.add_decl(axiom("b")).expect("adds");
        assert_eq!(
            fork.len(),
            1,
            "mutation after fork is invisible to the fork"
        );
        assert_eq!(extended.len(), 2);
        assert!(fork.find(&n("b")).is_none());
        // And the fork can diverge independently.
        let fork2 = fork.add_decl(axiom("c")).expect("adds");
        assert!(extended.find(&n("c")).is_none());
        assert!(fork2.find(&n("b")).is_none());
    }

    #[test]
    fn logical_roots_are_insertion_order_independent_and_semantic() {
        let forward = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("c")))
            .expect("builds");
        let reverse = Environment::new()
            .add_decl(axiom("c"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("a")))
            .expect("builds");
        let opts = KVMap::new();
        assert_eq!(forward.logical_root(&opts), reverse.logical_root(&opts));

        // Different content ⇒ different root.
        let other = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .expect("builds");
        assert_ne!(forward.logical_root(&opts), other.logical_root(&opts));

        // Options are part of the logical root.
        let mut opts2 = KVMap::new();
        opts2.insert(n("maxHeartbeats"), DataValue::OfNat(400_000));
        assert_ne!(forward.logical_root(&opts), forward.logical_root(&opts2));
    }

    #[test]
    fn extension_entries_enter_the_logical_root_in_order() {
        let opts = KVMap::new();
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers");
        let one = env
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let two = one
            .push_extension_entry(&n("simpExt"), &b"e2"[..])
            .expect("pushes");
        assert_ne!(env.logical_root(&opts), one.logical_root(&opts));
        assert_ne!(one.logical_root(&opts), two.logical_root(&opts));
        // Replay order is preserved exactly.
        let entries: Vec<&[u8]> = two
            .extension(&n("simpExt"))
            .expect("registered")
            .entries()
            .map(|e| &*e.payload)
            .collect();
        assert_eq!(entries, vec![b"e1".as_slice(), b"e2"]);
        // Unknown extension is a typed refusal.
        assert_eq!(
            env.push_extension_entry(&n("ghost"), &b"x"[..]),
            Err(EnvError::UnknownExtension { name: n("ghost") })
        );
    }

    #[test]
    fn environment_checkpoint_apply_preserves_exact_roots_and_unrelated_state() {
        let limits = CheckpointLimits::new(100, 10_000);
        let base = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"base"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("base environment builds");
        let target = base
            .push_extension_entry(&n("simpExt"), &b"suffix-a"[..])
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"suffix-b"[..]))
            .expect("target environment builds");
        let checkpoint = target
            .checkpoint_extension(&n("simpExt"), Some(&base), limits)
            .expect("environment suffix captures");
        let restored = base
            .apply_extension_checkpoint(&checkpoint, limits)
            .expect("environment suffix applies");

        assert_eq!(restored, target);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            target.logical_root(&KVMap::new())
        );
        assert_eq!(restored.find(&n("a")), target.find(&n("a")));
        assert_eq!(
            restored.extension(&n("otherExt")),
            target.extension(&n("otherExt"))
        );

        let divergent = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"wrong"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("same-length divergent branch builds");
        assert!(matches!(
            divergent.apply_extension_checkpoint(&checkpoint, limits),
            Err(EnvError::Checkpoint(
                CheckpointError::BaseHistoryMismatch { .. }
            ))
        ));
        assert_eq!(
            divergent
                .extension(&n("simpExt"))
                .expect("still registered")
                .entries()
                .last()
                .expect("one entry")
                .payload
                .as_ref(),
            b"wrong"
        );
    }

    #[test]
    fn environment_full_checkpoint_replaces_only_the_registered_journal() {
        let limits = CheckpointLimits::new(100, 10_000);
        let full_descriptor = ExtensionDescriptor {
            checkpoint: CheckpointSemantics::FullJournal,
            ..descriptor("fullExt")
        };
        let destination = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(full_descriptor))
            .expect("destination builds");
        let source = destination
            .push_extension_entry(&n("fullExt"), &b"one"[..])
            .and_then(|env| env.push_extension_entry(&n("fullExt"), &b"two"[..]))
            .expect("source builds");
        let checkpoint = source
            .checkpoint_extension(&n("fullExt"), None, limits)
            .expect("full environment checkpoint captures");
        let restored = destination
            .apply_extension_checkpoint(&checkpoint, limits)
            .expect("full checkpoint applies without a semantic base");
        assert_eq!(restored, source);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            source.logical_root(&KVMap::new())
        );
        assert!(matches!(
            source.checkpoint_extension(&n("ghost"), None, limits),
            Err(EnvError::UnknownExtension { .. })
        ));
    }

    #[test]
    fn extension_contracts_enter_the_logical_root() {
        let root = |merge, checkpoint, provenance| {
            let descriptor = ExtensionDescriptor {
                name: n("contractExt"),
                merge,
                checkpoint,
                provenance,
            };
            Environment::new()
                .register_extension(descriptor)
                .and_then(|env| env.push_extension_entry(&n("contractExt"), &b"entry"[..]))
                .expect("extension environment builds")
                .logical_root(&KVMap::new())
        };

        let append = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let append_again = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_eq!(
            append, append_again,
            "identical extension contracts and journals have stable identity"
        );

        let set_union = root(
            MergeSemantics::SetUnion,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let review = root(
            MergeSemantics::ConflictsRequireReview,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, set_union, "merge semantics enter the root");
        assert_ne!(append, review, "merge semantics enter the root");
        assert_ne!(
            set_union, review,
            "every merge variant has distinct identity"
        );

        let full_journal = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::FullJournal,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, full_journal, "checkpoint semantics enter the root");

        let opaque = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Opaque,
        );
        assert_ne!(append, opaque, "payload provenance enters the root");
    }

    #[test]
    fn add_decl_preserves_extension_state() {
        // The mutant this kills: add_decl rebuilding the environment with empty
        // extensions (state silently dropped) — found surviving by the
        // env_snapshots E2E mutation lane, then pinned here forever.
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers")
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let with_decl = env.add_decl(axiom("a")).expect("adds");
        let state = with_decl
            .extension(&n("simpExt"))
            .expect("extension state survives add_decl");
        assert_eq!(state.len(), 1);
        // And the delta still reaches the logical root after the decl lands.
        let opts = KVMap::new();
        let bare = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.register_extension(descriptor("simpExt")))
            .expect("builds");
        assert_ne!(with_decl.logical_root(&opts), bare.logical_root(&opts));
    }

    #[test]
    fn operational_metadata_never_touches_the_logical_root() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        let opts = KVMap::new();
        let root = env.logical_root(&opts);

        let mut host_a = KVMap::new();
        host_a.insert(n("host"), DataValue::OfString("machine-a".into()));
        let mut host_b = KVMap::new();
        host_b.insert(n("host"), DataValue::OfString("machine-b".into()));

        // Same trusted environment, different hosts: same logical root, different
        // operational roots.
        assert_eq!(root, env.logical_root(&opts));
        assert_ne!(
            Environment::operational_root(&host_a),
            Environment::operational_root(&host_b)
        );
    }

    #[test]
    fn declaration_identity_tag_policy_is_const_exhaustive_and_cast_free() {
        const DEFINITION_TAGS: [u8; 3] = [
            definition_safety_tag(DefinitionSafety::Unsafe),
            definition_safety_tag(DefinitionSafety::Safe),
            definition_safety_tag(DefinitionSafety::Partial),
        ];
        const QUOTIENT_TAGS: [u8; 4] = [
            quot_kind_tag(QuotKind::Type),
            quot_kind_tag(QuotKind::Ctor),
            quot_kind_tag(QuotKind::Lift),
            quot_kind_tag(QuotKind::Ind),
        ];
        assert_eq!(DEFINITION_TAGS, [0, 1, 2]);
        assert_eq!(QUOTIENT_TAGS, [0, 1, 2, 3]);
        for case in DeclarationTagCase::ALL {
            assert_eq!(
                case.production_tag(),
                case.canonical_tag(),
                "production and independently frozen tag tables diverged for {}/{}",
                case.family(),
                case.variant()
            );
        }
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-work\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"closed-tag-projection-policy\",\
             \"claim_scope\":\"closed_enum_tag_projection_only\",\
             \"evidence\":\"const_exhaustive_match_plus_forbid_as_conversions\",\
             \"definition_variant_count\":3,\"quotient_variant_count\":4,\
             \"tag_helper_output_bytes\":1,\
             \"tag_helper_input_dependent_iterations\":0,\
             \"tag_helper_owned_allocations\":0,\
             \"tag_helper_independent_cancellation_points\":0,\
             \"tag_helper_separate_resource_limit_required\":false,\
             \"enclosing_decl_content_budget_claim\":\"not_made\",\
             \"enclosing_decl_content_budget_api\":\"absent\",\
             \"resource_followup\":\"franken_lean-j8h\",\
             \"status\":\"pass\"}}"
        );
    }

    #[test]
    fn declaration_identity_tag_matrix_matches_independent_model_and_roots() {
        let options = KVMap::new();
        let mut rows = Vec::with_capacity(DeclarationTagCase::ALL.len());
        for case in DeclarationTagCase::ALL {
            let info = tagged_declaration(case, false);
            let canonical_bytes =
                modeled_tagged_declaration_bytes(case, &info, DeclarationTagDigestModel::Canonical);
            let expected_digest = hash(Domain::DeclContent, &canonical_bytes);
            let actual_digest = Environment::decl_content_digest(&info);
            assert_eq!(
                actual_digest,
                expected_digest,
                "production declaration identity diverged from the independent model for {}/{}",
                case.family(),
                case.variant()
            );
            let repeated_digest =
                Environment::decl_content_digest(&tagged_declaration(case, false));
            assert_eq!(
                actual_digest,
                repeated_digest,
                "declaration digest was not repeatable for {}/{}",
                case.family(),
                case.variant()
            );

            let environment = Environment::new()
                .add_decl(info.clone())
                .expect("single tagged declaration fixture builds");
            let actual_root = environment.logical_root(&options);
            let mut expected_root_builder = LogicalRootBuilder::new();
            expected_root_builder.add_decl(info.name(), expected_digest);
            expected_root_builder.set_options(&options);
            let expected_root = expected_root_builder.finalize();
            assert_eq!(
                actual_root, expected_root,
                "tagged declaration digest did not propagate exactly into the logical root"
            );
            let repeated_root = Environment::new()
                .add_decl(tagged_declaration(case, false))
                .expect("repeated tagged declaration fixture builds")
                .logical_root(&options);
            assert_eq!(
                actual_root,
                repeated_root,
                "logical root was not repeatable for {}/{}",
                case.family(),
                case.variant()
            );

            let modeled_stream_hash = hash(Domain::Fixture, &canonical_bytes);
            assert_eq!(
                canonical_bytes.len(),
                case.golden_stream_bytes(),
                "complete modeled stream byte count drifted for {}/{}",
                case.family(),
                case.variant()
            );
            assert_eq!(
                modeled_stream_hash.to_hex(),
                case.golden_stream_hash(),
                "complete modeled stream hash drifted for {}/{}",
                case.family(),
                case.variant()
            );
            assert_eq!(
                actual_digest.to_hex(),
                case.golden_digest(),
                "declaration digest golden drifted for {}/{}",
                case.family(),
                case.variant()
            );
            assert_eq!(
                actual_root.0.to_hex(),
                case.golden_root(),
                "logical root golden drifted for {}/{}",
                case.family(),
                case.variant()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.declaration-tag-identity\",\"version\":1,\
                 \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
                 \"scenario\":\"rich-same-name-seven-row-matrix\",\
                 \"family\":\"{}\",\"variant\":\"{}\",\"canonical_tag\":{},\
                 \"fixture_id\":\"rich-same-name-v1\",\
                 \"modeled_canonical_stream_bytes\":{},\
                 \"modeled_canonical_stream_hash\":\"{modeled_stream_hash}\",\
                 \"expected_digest\":\"{expected_digest}\",\
                 \"actual_digest\":\"{actual_digest}\",\
                 \"repeated_digest\":\"{repeated_digest}\",\
                 \"expected_root\":\"{expected_root}\",\
                 \"actual_root\":\"{actual_root}\",\
                 \"repeated_root\":\"{repeated_root}\",\
                 \"frozen_stream_digest_root_goldens\":\"match\",\
                 \"root_propagation\":\"exact\",\"status\":\"pass\"}}",
                case.family(),
                case.variant(),
                case.canonical_tag(),
                canonical_bytes.len()
            );
            rows.push((case, actual_digest));
        }

        let unique_digests: HashSet<_> = rows.iter().map(|(_, digest)| *digest).collect();
        assert_eq!(
            unique_digests.len(),
            DeclarationTagCase::ALL.len(),
            "all seven declaration tag cases must have distinct content identity"
        );
        let mut pairwise_comparisons = 0usize;
        for (index, (lhs_case, lhs_digest)) in rows.iter().enumerate() {
            for (rhs_case, rhs_digest) in &rows[index + 1..] {
                assert_ne!(
                    lhs_digest,
                    rhs_digest,
                    "distinct tag cases aliased: {}/{} and {}/{}",
                    lhs_case.family(),
                    lhs_case.variant(),
                    rhs_case.family(),
                    rhs_case.variant()
                );
                pairwise_comparisons += 1;
            }
        }
        assert_eq!(pairwise_comparisons, 21);
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-identity-summary\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"rich-same-name-seven-row-matrix\",\
             \"case_count\":7,\"unique_digest_count\":7,\
             \"pairwise_comparisons\":{pairwise_comparisons},\
             \"expected_pairwise_comparisons\":21,\
             \"model\":\"independent-complete-definition-quotient-stream-v1\",\
             \"root_propagation\":\"production-environment-exact\",\
             \"status\":\"pass\"}}"
        );
    }

    #[test]
    fn declaration_identity_tag_named_mutants_are_discriminated() {
        let options = KVMap::new();
        let mut digest_discriminations = 0usize;
        let mut root_propagation_discriminations = 0usize;
        for case in DeclarationTagCase::ALL {
            let info = tagged_declaration(case, false);
            let canonical_bytes =
                modeled_tagged_declaration_bytes(case, &info, DeclarationTagDigestModel::Canonical);
            let canonical_digest = Environment::decl_content_digest(&info);
            assert_eq!(
                canonical_digest,
                hash(Domain::DeclContent, &canonical_bytes),
                "production digest must equal the independent canonical stream model"
            );
            let canonical_stream_hash = hash(Domain::Fixture, &canonical_bytes);
            let canonical_environment = Environment::new()
                .add_decl(info.clone())
                .expect("single tagged declaration fixture builds");
            let canonical_root = canonical_environment.logical_root(&options);
            let mut canonical_model_root_builder = LogicalRootBuilder::new();
            canonical_model_root_builder.add_decl(info.name(), canonical_digest);
            canonical_model_root_builder.set_options(&options);
            assert_eq!(
                canonical_root,
                canonical_model_root_builder.finalize(),
                "production logical root must propagate the canonical modeled digest exactly"
            );

            for (mutation, model) in [
                ("omit_tag", DeclarationTagDigestModel::OmitTag),
                ("debug_text", DeclarationTagDigestModel::DebugText),
                (
                    "cast_after_source_reorder",
                    DeclarationTagDigestModel::CastAfterSourceReorder,
                ),
                (
                    "move_tag_across_adjacent_field",
                    DeclarationTagDigestModel::MoveTagAcrossAdjacentField,
                ),
                ("wrong_domain", DeclarationTagDigestModel::WrongDomain),
            ] {
                let mutated_bytes = modeled_tagged_declaration_bytes(case, &info, model);
                let mutated_digest = modeled_tagged_declaration_digest(case, &info, model);
                assert_ne!(
                    canonical_digest,
                    mutated_digest,
                    "{mutation} mutant survived for {}/{}",
                    case.family(),
                    case.variant()
                );
                match model {
                    DeclarationTagDigestModel::OmitTag => {
                        assert_eq!(
                            canonical_bytes.len(),
                            mutated_bytes.len() + 1,
                            "omitting the fixed tag must remove exactly one byte"
                        );
                        assert_ne!(
                            mutated_bytes, canonical_bytes,
                            "omitting the fixed tag must change the modeled stream"
                        );
                    }
                    DeclarationTagDigestModel::DebugText => {
                        assert_eq!(
                            mutated_bytes.len(),
                            canonical_bytes.len() + 7 + case.variant().len(),
                            "debug text must replace one byte with a length-prefixed variant"
                        );
                        assert_ne!(
                            mutated_bytes, canonical_bytes,
                            "debug text must change the modeled stream"
                        );
                    }
                    DeclarationTagDigestModel::CastAfterSourceReorder
                    | DeclarationTagDigestModel::MoveTagAcrossAdjacentField => {
                        assert_eq!(
                            mutated_bytes.len(),
                            canonical_bytes.len(),
                            "{mutation} must isolate value/order rather than stream size"
                        );
                        assert_ne!(
                            mutated_bytes, canonical_bytes,
                            "{mutation} must change bytes while preserving stream size"
                        );
                    }
                    DeclarationTagDigestModel::WrongDomain => {
                        assert_eq!(
                            mutated_bytes, canonical_bytes,
                            "wrong-domain mutation must change only domain separation"
                        );
                    }
                    DeclarationTagDigestModel::Canonical => {
                        unreachable!("canonical is not a mutation")
                    }
                }

                let mutated_stream_hash = hash(Domain::Fixture, &mutated_bytes);
                let mut mutated_root_builder = LogicalRootBuilder::new();
                mutated_root_builder.add_decl(info.name(), mutated_digest);
                mutated_root_builder.set_options(&options);
                let mutated_root = mutated_root_builder.finalize();
                assert_ne!(
                    canonical_root,
                    mutated_root,
                    "{mutation} root-propagation mutant survived for {}/{}",
                    case.family(),
                    case.variant()
                );
                digest_discriminations += 1;
                root_propagation_discriminations += 1;
                eprintln!(
                    "{{\"schema\":\"fln.unit.declaration-tag-mutant\",\"version\":1,\
                     \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
                     \"scenario\":\"named-tag-identity-mutants\",\
                     \"family\":\"{}\",\"variant\":\"{}\",\
                     \"mutation\":\"{mutation}\",\"canonical_tag\":{},\
                     \"root_mutation\":\"failed_root_propagation\",\
                     \"modeled_canonical_stream_bytes\":{},\
                     \"modeled_mutated_stream_bytes\":{},\
                     \"modeled_canonical_stream_hash\":\"{canonical_stream_hash}\",\
                     \"modeled_mutated_stream_hash\":\"{mutated_stream_hash}\",\
                     \"canonical_digest\":\"{canonical_digest}\",\
                     \"mutated_digest\":\"{mutated_digest}\",\
                     \"production_canonical_root\":\"{canonical_root}\",\
                     \"modeled_mutated_root\":\"{mutated_root}\",\
                     \"expected_digest_relation\":\"different\",\
                     \"actual_digest_relation\":\"different\",\
                     \"expected_root_relation\":\"different\",\
                     \"actual_root_relation\":\"different\",\"status\":\"pass\"}}",
                    case.family(),
                    case.variant(),
                    case.canonical_tag(),
                    canonical_bytes.len(),
                    mutated_bytes.len()
                );
            }
        }
        assert_eq!(
            digest_discriminations, 35,
            "five digest mutants must be killed for all seven cases"
        );
        assert_eq!(
            root_propagation_discriminations, 35,
            "all five digest mutants must propagate to distinct roots for all seven cases"
        );
        eprintln!(
            "{{\"schema\":\"fln.unit.declaration-tag-mutants-summary\",\"version\":1,\
             \"bead\":\"fln-amv.12\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"named-tag-identity-mutants\",\
             \"case_count\":7,\"digest_mutation_classes\":5,\
             \"root_mutation_class\":\"failed_root_propagation\",\
             \"root_propagation_input_classes\":5,\
             \"digest_discriminations\":{digest_discriminations},\
             \"root_propagation_discriminations\":{root_propagation_discriminations},\
             \"total_discriminations\":{},\"status\":\"pass\"}}",
            digest_discriminations + root_propagation_discriminations
        );
    }

    #[test]
    fn declaration_identity_tag_is_stable_across_1_8_32_concurrent_complete_builds() {
        let cases = DeclarationTagCase::ALL.to_vec();
        let options = KVMap::new();
        let canonical_environment = tagged_environment(cases.iter().copied());

        let mut expected_root_builder = LogicalRootBuilder::new();
        for case in cases.iter().copied() {
            let info = tagged_declaration(case, true);
            let digest = modeled_tagged_declaration_digest(
                case,
                &info,
                DeclarationTagDigestModel::Canonical,
            );
            expected_root_builder.add_decl(info.name(), digest);
        }
        expected_root_builder.set_options(&options);
        let expected_root = expected_root_builder.finalize();
        assert_eq!(
            canonical_environment.logical_root(&options),
            expected_root,
            "canonical seven-declaration environment diverged from the aggregate model"
        );

        let omitted_root = tagged_environment(cases.iter().copied().skip(1)).logical_root(&options);
        assert_ne!(
            omitted_root, expected_root,
            "omitting one tagged declaration must change the aggregate root"
        );
        let mut source_order_root_builder = LogicalRootBuilder::new();
        for (index, case) in cases.iter().copied().enumerate() {
            let info = tagged_declaration(case, true);
            let model = if index == 0 {
                DeclarationTagDigestModel::CastAfterSourceReorder
            } else {
                DeclarationTagDigestModel::Canonical
            };
            source_order_root_builder.add_decl(
                info.name(),
                modeled_tagged_declaration_digest(case, &info, model),
            );
        }
        source_order_root_builder.set_options(&options);
        let source_order_root = source_order_root_builder.finalize();
        assert_ne!(
            source_order_root, expected_root,
            "one source-order-dependent tag must change the aggregate root"
        );

        for worker_count in [1usize, 8, 32] {
            let results = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker_index| {
                        let permutation = permuted_tag_cases(&cases, worker_index);
                        scope.spawn(move || {
                            let order_id = tag_case_order_id(&permutation);
                            let raw_order = permutation
                                .iter()
                                .map(|case| (case.family(), case.variant()))
                                .collect::<Vec<_>>();
                            let environment = tagged_environment(permutation.iter().copied());
                            let root = environment.logical_root(&KVMap::new());
                            (order_id, raw_order, environment, root)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("declaration tag worker joins"))
                    .collect::<Vec<_>>()
            });
            assert_eq!(results.len(), worker_count);
            let order_ids: HashSet<_> = results
                .iter()
                .map(|(order_id, _, _, _)| *order_id)
                .collect();
            let raw_orders: HashSet<_> = results
                .iter()
                .map(|(_, raw_order, _, _)| raw_order.clone())
                .collect();
            let distinct_full_permutations = raw_orders.len();
            assert_eq!(
                distinct_full_permutations, worker_count,
                "every worker must receive a distinct raw seven-case permutation"
            );
            assert_eq!(
                order_ids.len(),
                distinct_full_permutations,
                "hashed order ids must preserve the measured raw permutation cardinality"
            );

            let mut worker_roots = Vec::with_capacity(results.len());
            for (worker_index, (order_id, raw_order, environment, actual_root)) in
                results.iter().enumerate()
            {
                assert_eq!(
                    raw_order.len(),
                    DeclarationTagCase::ALL.len(),
                    "every worker order must contain all seven declaration-tag cases"
                );
                let raw_input_order_labels = raw_order
                    .iter()
                    .map(|(family, variant)| format!("{family}/{variant}"))
                    .collect::<Vec<_>>()
                    .join(">");
                assert_eq!(
                    environment, &canonical_environment,
                    "{worker_count}-worker environment diverged for order {order_id}"
                );
                assert_eq!(
                    *actual_root, expected_root,
                    "{worker_count}-worker root diverged for order {order_id}"
                );
                assert_eq!(
                    environment.logical_root(&options),
                    *actual_root,
                    "worker root was not repeatable"
                );
                for case in cases.iter().copied() {
                    let expected_info = tagged_declaration(case, true);
                    let actual_info = environment
                        .find(expected_info.name())
                        .expect("worker retains every tagged declaration");
                    assert_eq!(actual_info, &expected_info);
                    assert_eq!(
                        Environment::decl_content_digest(actual_info),
                        modeled_tagged_declaration_digest(
                            case,
                            &expected_info,
                            DeclarationTagDigestModel::Canonical,
                        ),
                        "worker declaration digest diverged for {}/{}",
                        case.family(),
                        case.variant()
                    );
                }
                worker_roots.push(*actual_root);
                eprintln!(
                    "{{\"schema\":\"fln.unit.declaration-tag-concurrent-build\",\
                     \"version\":1,\"bead\":\"fln-amv.12\",\
                     \"claim_type\":\"bounded_model\",\
                     \"scenario\":\"complete-environment-thread-matrix\",\
                     \"invariant_relation\":\"supports-local-environment-identity-slice\",\
                     \"gate_relation\":\"partial-component-evidence\",\
                     \"execution_model\":\"independent_complete_build_per_worker\",\
                     \"concurrent_worker_count\":{worker_count},\
                     \"worker_index\":{worker_index},\
                     \"input_order_id\":\"{order_id}\",\
                     \"raw_input_order_case_count\":{},\
                     \"raw_input_order_labels\":\"{raw_input_order_labels}\",\
                     \"declaration_cases\":7,\"actual_root\":\"{actual_root}\",\
                     \"expected_root\":\"{expected_root}\",\
                     \"full_environment_equal\":true,\
                     \"per_name_digest_equal\":true,\"status\":\"pass\"}}",
                    raw_order.len()
                );
            }

            let mut sorted_order_ids: Vec<_> = order_ids.into_iter().collect();
            sorted_order_ids.sort_unstable();
            let mut order_set_writer = CanonWriter::new();
            order_set_writer.str("fln.test.declaration-tag-order-set");
            order_set_writer.u16(1);
            order_set_writer.u64(usize_to_u64(sorted_order_ids.len()));
            for order_id in sorted_order_ids {
                order_set_writer.bytes(&order_id.0);
            }
            let order_set_hash = hash(Domain::Fixture, &order_set_writer.into_bytes());

            worker_roots.sort_unstable();
            let mut root_set_writer = CanonWriter::new();
            root_set_writer.str("fln.test.declaration-tag-worker-roots");
            root_set_writer.u16(1);
            root_set_writer.u64(usize_to_u64(worker_roots.len()));
            for root in worker_roots {
                root_set_writer.bytes(&root.0.0);
            }
            let worker_roots_hash = hash(Domain::Fixture, &root_set_writer.into_bytes());
            eprintln!(
                "{{\"schema\":\"fln.unit.declaration-tag-concurrent-build-summary\",\
                 \"version\":1,\"bead\":\"fln-amv.12\",\
                 \"claim_type\":\"bounded_model\",\
                 \"scenario\":\"complete-environment-thread-matrix\",\
                 \"invariant_relation\":\"supports-local-environment-identity-slice\",\
                 \"gate_relation\":\"partial-component-evidence\",\
                 \"permutation_scheme\":\"affine-modulo-seven-v1\",\
                 \"concurrent_worker_count\":{worker_count},\
                 \"productive_workers\":{},\"distinct_full_permutations\":{},\
                 \"declaration_cases_per_worker\":7,\
                 \"order_set_hash\":\"{order_set_hash}\",\
                 \"worker_roots_hash\":\"{worker_roots_hash}\",\
                 \"expected_root\":\"{expected_root}\",\
                 \"omitted_declaration_root\":\"{omitted_root}\",\
                 \"source_order_mutant_root\":\"{source_order_root}\",\
                 \"full_environment_equal\":true,\
                 \"per_name_digest_equal\":true,\
                 \"omission_negative_control\":\"pass\",\
                 \"source_order_negative_control\":\"pass\",\"status\":\"pass\"}}",
                results.len(),
                distinct_full_permutations
            );
        }
    }

    /// The `fln-amv.12` child matrix, as lane-consumable evidence.
    ///
    /// The unit coverage above already proves the substance; what it emits is
    /// `fln.unit.*` on stderr, which is a developer-facing summary rather than a
    /// record the shared env_snapshots lane can validate. This emits the same facts
    /// as `fln.e2e.declaration-tag-matrix/1` on stdout, one row per tag case plus a
    /// summary, so `fln-amv.14`'s authoritative bundle can carry a separately
    /// identifiable fln-amv.12 child instead of citing unit-only evidence.
    ///
    /// Every number here is produced by real work through the real API in this run.
    /// Nothing is restated from the unit test.
    #[test]
    fn declaration_tag_matrix_e2e_emits_detailed_real_path_evidence() {
        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );
        let options = KVMap::new();
        let started = std::time::Instant::now();
        let mut digests = Vec::with_capacity(DeclarationTagCase::ALL.len());

        for case in DeclarationTagCase::ALL {
            let case_started = std::time::Instant::now();
            let info = tagged_declaration(case, false);
            let canonical_bytes =
                modeled_tagged_declaration_bytes(case, &info, DeclarationTagDigestModel::Canonical);
            let expected_digest = hash(Domain::DeclContent, &canonical_bytes);
            let actual_digest = Environment::decl_content_digest(&info);
            let repeated_digest =
                Environment::decl_content_digest(&tagged_declaration(case, false));
            let stream_hash = hash(Domain::Fixture, &canonical_bytes);
            let environment = Environment::new()
                .add_decl(info.clone())
                .expect("single tagged declaration fixture builds");
            let actual_root = environment.logical_root(&options);
            let mut expected_root_builder = LogicalRootBuilder::new();
            expected_root_builder.add_decl(info.name(), expected_digest);
            expected_root_builder.set_options(&options);
            let expected_root = expected_root_builder.finalize();

            // The production tag must equal the frozen canonical tag: that identity is
            // the whole point of fln-amv.12, since `as u8` would silently track source
            // order instead.
            assert_eq!(
                case.production_tag(),
                case.canonical_tag(),
                "{}/{} production tag drifted from its frozen canonical tag",
                case.family(),
                case.variant()
            );
            assert_eq!(actual_digest, expected_digest);
            assert_eq!(actual_digest, repeated_digest);
            assert_eq!(actual_root, expected_root);
            assert_eq!(canonical_bytes.len(), case.golden_stream_bytes());
            assert_eq!(stream_hash.to_string(), case.golden_stream_hash());
            assert_eq!(actual_digest.to_string(), case.golden_digest());
            digests.push((case, actual_digest));

            println!(
                "{{\"schema\":\"fln.e2e.declaration-tag-matrix\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.12\",\"fln-amv.14\"],\
                 \"scenario\":\"declaration-tag-matrix\",\"case\":\"{}/{}\",\
                 \"family\":\"{}\",\"variant\":\"{}\",\"kind\":\"{}\",\
                 \"canonical_tag\":{},\"production_tag\":{},\
                 \"tag_source\":\"explicit_exhaustive_match\",\
                 \"stream_bytes\":{},\"golden_stream_bytes\":{},\
                 \"stream_hash\":\"{stream_hash}\",\"golden_stream_hash\":\"{}\",\
                 \"expected_digest\":\"{expected_digest}\",\"actual_digest\":\"{actual_digest}\",\
                 \"golden_digest\":\"{}\",\"repeated_digest\":\"{repeated_digest}\",\
                 \"digest_relation\":\"equal\",\"repeat_relation\":\"equal\",\
                 \"expected_root\":\"{expected_root}\",\"actual_root\":\"{actual_root}\",\
                 \"root_relation\":\"equal\",\"model\":\"independent-complete-stream-v1\",\
                 \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
                case.family(),
                case.variant(),
                case.family(),
                case.variant(),
                case.kind_name(),
                case.canonical_tag(),
                case.production_tag(),
                canonical_bytes.len(),
                case.golden_stream_bytes(),
                case.golden_stream_hash(),
                case.golden_digest(),
                case_started.elapsed().as_micros()
            );
        }

        // Pairwise distinctness, counted rather than asserted in bulk, so the record
        // states how much comparison actually happened.
        let mut pairwise_comparisons = 0usize;
        for (index, (_, lhs)) in digests.iter().enumerate() {
            for (_, rhs) in &digests[index + 1..] {
                assert_ne!(lhs, rhs, "two declaration tag cases aliased");
                pairwise_comparisons += 1;
            }
        }
        assert_eq!(pairwise_comparisons, 21);

        // The thread matrix, run for real: every worker builds the full seven-case
        // environment under its own permutation and must land on one root.
        let cases = DeclarationTagCase::ALL.to_vec();
        let canonical_environment = tagged_environment(cases.iter().copied());
        let canonical_root = canonical_environment.logical_root(&options);
        let mut thread_rows = Vec::new();
        for worker_count in [1usize, 8, 32] {
            let thread_started = std::time::Instant::now();
            let roots = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker_index| {
                        let permutation = permuted_tag_cases(&cases, worker_index);
                        scope.spawn(move || {
                            tagged_environment(permutation.iter().copied())
                                .logical_root(&KVMap::new())
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("tag matrix worker joins"))
                    .collect::<Vec<_>>()
            });
            assert_eq!(roots.len(), worker_count);
            let distinct: HashSet<_> = roots.iter().collect();
            assert_eq!(
                distinct.len(),
                1,
                "{worker_count} workers disagreed on the aggregate root"
            );
            assert_eq!(roots[0], canonical_root);
            thread_rows.push((worker_count, thread_started.elapsed().as_micros()));
            println!(
                "{{\"schema\":\"fln.e2e.declaration-tag-matrix\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.12\",\"fln-amv.14\"],\
                 \"scenario\":\"declaration-tag-thread-matrix\",\
                 \"worker_count\":{worker_count},\"distinct_root_count\":1,\
                 \"expected_root\":\"{canonical_root}\",\"actual_root\":\"{}\",\
                 \"root_relation\":\"equal\",\"order_independence\":\"proven\",\
                 \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
                roots[0],
                thread_started.elapsed().as_micros()
            );
        }

        // The named defect: one tag encoded by source-order cast instead of its frozen
        // value must move the aggregate root. Without this the matrix above would pass
        // just as happily against a cast-based encoder.
        let mut source_order_builder = LogicalRootBuilder::new();
        for (index, case) in cases.iter().copied().enumerate() {
            let info = tagged_declaration(case, true);
            let model = if index == 0 {
                DeclarationTagDigestModel::CastAfterSourceReorder
            } else {
                DeclarationTagDigestModel::Canonical
            };
            source_order_builder.add_decl(
                info.name(),
                modeled_tagged_declaration_digest(case, &info, model),
            );
        }
        source_order_builder.set_options(&options);
        let source_order_root = source_order_builder.finalize();
        assert_ne!(source_order_root, canonical_root);

        let omitted_root = tagged_environment(cases.iter().copied().skip(1)).logical_root(&options);
        assert_ne!(omitted_root, canonical_root);

        println!(
            "{{\"schema\":\"fln.e2e.declaration-tag-matrix\",\"version\":1,\
             \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.12\",\"fln-amv.14\"],\
             \"scenario\":\"declaration-tag-summary\",\"case_count\":{},\
             \"unique_digest_count\":{},\"pairwise_comparisons\":{pairwise_comparisons},\
             \"expected_pairwise_comparisons\":21,\"thread_matrix\":[1,8,32],\
             \"thread_matrix_roots_distinct\":1,\
             \"canonical_root\":\"{canonical_root}\",\
             \"source_order_defect_root\":\"{source_order_root}\",\
             \"source_order_defect_relation\":\"differs\",\
             \"omitted_declaration_root\":\"{omitted_root}\",\
             \"omitted_declaration_relation\":\"differs\",\
             \"named_defects_discriminated\":[\"cast_after_source_reorder\",\
             \"omitted_declaration\"],\"claim_type\":\"bounded_model\",\
             \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            DeclarationTagCase::ALL.len(),
            digests
                .iter()
                .map(|(_, digest)| *digest)
                .collect::<HashSet<_>>()
                .len(),
            started.elapsed().as_micros()
        );
        assert_eq!(thread_rows.len(), 3);
    }

    #[test]
    fn mutual_block_membership_changes_the_content_digest() {
        const LARGE_MEMBER_COUNT: usize = 4_096;
        let large_members: Vec<Name> = (0..LARGE_MEMBER_COUNT)
            .map(|index| Name::num(n("member"), usize_to_u64(index)))
            .collect();
        let boundary_cases = vec![
            ("empty", Vec::new()),
            ("singleton", vec![n("d")]),
            ("repeated", vec![n("d"), n("d")]),
            ("ordered", vec![n("d"), n("e")]),
            ("reordered", vec![n("e"), n("d")]),
            ("renamed", vec![n("d"), n("f")]),
            ("declared_large", large_members),
        ];
        let options = KVMap::new();

        for kind in AllBearingKind::ALL {
            let mut digests = Vec::with_capacity(boundary_cases.len());
            for (case, members) in &boundary_cases {
                let info = all_bearing_decl(kind, members.clone());
                let actual = Environment::decl_content_digest(&info);
                let expected = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                assert_eq!(
                    actual,
                    expected,
                    "{} {case} membership diverged from the independent canonical model",
                    kind.label()
                );

                let rebuilt = all_bearing_decl(kind, members.clone());
                assert_eq!(
                    actual,
                    Environment::decl_content_digest(&rebuilt),
                    "{} {case} membership was not repeatable",
                    kind.label()
                );

                let environment = Environment::new()
                    .add_decl(info)
                    .expect("fixture declaration is valid");
                let actual_root = environment.logical_root(&options);
                let mut expected_root = LogicalRootBuilder::new();
                expected_root.add_decl(rebuilt.name(), actual);
                expected_root.set_options(&options);
                assert_eq!(
                    actual_root,
                    expected_root.finalize(),
                    "{} {case} digest did not propagate exactly into the logical root",
                    kind.label()
                );
                let repeated_root = Environment::new()
                    .add_decl(rebuilt)
                    .expect("repeated fixture declaration is valid")
                    .logical_root(&options);
                assert_eq!(
                    actual_root,
                    repeated_root,
                    "{} {case} logical root was not repeatable",
                    kind.label()
                );
                digests.push(actual);
            }

            assert_ne!(
                digests[0],
                digests[1],
                "{} must distinguish empty and singleton membership",
                kind.label()
            );
            assert_ne!(
                digests[1],
                digests[2],
                "{} must preserve repeated membership",
                kind.label()
            );
            assert_ne!(
                digests[1],
                digests[3],
                "{} must distinguish solo and grouped membership",
                kind.label()
            );
            assert_ne!(
                digests[2],
                digests[3],
                "{} must distinguish multiplicity and member identity",
                kind.label()
            );
            assert_ne!(
                digests[3],
                digests[4],
                "{} must preserve membership order",
                kind.label()
            );
            assert_ne!(
                digests[3],
                digests[5],
                "{} must preserve member names",
                kind.label()
            );
            assert_ne!(
                digests[5],
                digests[6],
                "{} must cover the declared large-member boundary",
                kind.label()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-boundaries\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"kind\":\"{}\",\"case_count\":7,\"large_member_count\":4096,\
                 \"empty_digest\":\"{}\",\"solo_digest\":\"{}\",\
                 \"grouped_digest\":\"{}\",\"reordered_digest\":\"{}\",\
                 \"large_digest\":\"{}\",\"root_propagation\":\"exact\",\
                 \"repeatability\":\"pass\",\"status\":\"pass\"}}",
                kind.label(),
                digests[0],
                digests[1],
                digests[3],
                digests[4],
                digests[6]
            );
        }

        let opaque_solo = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d")],
        ));
        let opaque_grouped = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d"), n("e")],
        ));
        assert_ne!(
            opaque_solo, opaque_grouped,
            "OpaqueVal.all must distinguish the original solo-versus-grouped regression"
        );
    }

    #[test]
    fn mutual_block_membership_named_mutants_are_discriminated() {
        let witness = vec![n("e"), n("d"), n("e"), n("f")];
        let options = KVMap::new();

        for kind in AllBearingKind::ALL {
            let info = all_bearing_decl(kind, witness.clone());
            let canonical = Environment::decl_content_digest(&info);
            for (mutation, model) in [
                ("drop_membership", MembershipModel::DropList),
                ("omit_member_count", MembershipModel::OmitCount),
                ("reorder_membership", MembershipModel::SortMembers),
            ] {
                let mutated = modeled_all_bearing_digest(&info, model, Domain::DeclContent);
                assert_ne!(
                    canonical,
                    mutated,
                    "{mutation} mutant survived for {}",
                    kind.label()
                );
            }

            let wrong_domain =
                modeled_all_bearing_digest(&info, MembershipModel::Canonical, Domain::LogicalRoot);
            assert_ne!(
                canonical,
                wrong_domain,
                "wrong_digest_domain mutant survived for {}",
                kind.label()
            );

            let actual_root = Environment::new()
                .add_decl(info.clone())
                .expect("fixture declaration is valid")
                .logical_root(&options);
            let dropped_digest =
                modeled_all_bearing_digest(&info, MembershipModel::DropList, Domain::DeclContent);
            let mut dropped_root = LogicalRootBuilder::new();
            dropped_root.add_decl(info.name(), dropped_digest);
            dropped_root.set_options(&options);
            assert_ne!(
                actual_root,
                dropped_root.finalize(),
                "fail_to_propagate_membership mutant survived for {}",
                kind.label()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-mutants\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"kind\":\"{}\",\"witness_member_count\":4,\
                 \"canonical_digest\":\"{canonical}\",\"logical_root\":\"{actual_root}\",\
                 \"mutations\":[\"drop_membership\",\"omit_member_count\",\
                 \"reorder_membership\",\"wrong_digest_domain\",\
                 \"fail_to_propagate_membership\"],\"killed\":5,\
                 \"status\":\"pass\"}}",
                kind.label()
            );
        }
    }

    #[test]
    fn mutual_block_membership_matches_model_for_generated_cases() {
        const GENERATED_CASES: usize = 96;
        const MAX_GENERATED_MEMBERS: usize = 48;
        let mut assertions = 0usize;

        for case_index in 0..GENERATED_CASES {
            let member_count = (case_index * 17) % (MAX_GENERATED_MEMBERS + 1);
            let mut members: Vec<Name> = (0..member_count)
                .map(|member_index| {
                    let root = if (case_index + member_index) % 2 == 0 {
                        n("left")
                    } else {
                        n("right")
                    };
                    let numbered = Name::num(
                        root,
                        usize_to_u64((case_index * 13 + member_index * 7) % 11),
                    );
                    if (case_index + member_index) % 3 == 0 {
                        Name::str(numbered, "leaf")
                    } else {
                        numbered
                    }
                })
                .collect();

            if members.len() > 1 && case_index % 3 == 0 {
                let repeated = members[0].clone();
                let last = members.len() - 1;
                members[last] = repeated;
            }
            if !members.is_empty() {
                match case_index % 4 {
                    1 => members.reverse(),
                    2 => {
                        let shift = case_index % members.len();
                        members.rotate_left(shift);
                    }
                    3 => {
                        let shift = (case_index * 3) % members.len();
                        members.rotate_right(shift);
                    }
                    _ => {}
                }
            }

            for kind in AllBearingKind::ALL {
                let info = all_bearing_decl(kind, members.clone());
                let actual = Environment::decl_content_digest(&info);
                let expected = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                assert_eq!(
                    actual,
                    expected,
                    "generated case {case_index} diverged for {}",
                    kind.label()
                );
                assert_eq!(
                    actual,
                    Environment::decl_content_digest(&all_bearing_decl(kind, members.clone())),
                    "generated case {case_index} was not repeatable for {}",
                    kind.label()
                );
                assertions += 2;
            }
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.mutual-membership-generated\",\"version\":1,\
             \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
             \"generated_cases\":{GENERATED_CASES},\"variant_count\":5,\
             \"max_member_count\":{MAX_GENERATED_MEMBERS},\
             \"assertions\":{assertions},\"name_depth_max\":3,\
             \"features\":[\"duplicates\",\"string_components\",\"numeric_components\",\
             \"reversal\",\"rotation\"],\"status\":\"pass\"}}"
        );
    }

    #[test]
    fn mutual_membership_writer_has_canonical_stream_shape() {
        for member_count in [0usize, 1, 32, 4_096] {
            let members: Vec<Name> = (0..member_count)
                .map(|index| Name::num(n("member"), usize_to_u64(index)))
                .collect();
            let canonical_member_bytes = canonical_name_body_bytes(&members);

            let mut actual = CanonWriter::new();
            write_mutual_membership(&mut actual, &members);
            let actual = actual.into_bytes();

            let mut expected = CanonWriter::new();
            write_membership_model(&mut expected, &members, MembershipModel::Canonical);
            let expected = expected.into_bytes();

            assert_eq!(
                actual, expected,
                "membership writer must be exactly count plus one ordered body per member"
            );
            assert_eq!(
                actual.len(),
                8 + canonical_member_bytes,
                "membership stream work must grow with count-prefix plus canonical member bytes"
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-work\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"evidence\":\"canonical_stream_shape\",\
                 \"member_count\":{member_count},\
                 \"canonical_member_bytes\":{canonical_member_bytes},\
                 \"expected_stream_bytes\":{},\"observed_stream_bytes\":{},\
                 \"status\":\"pass\"}}",
                8 + canonical_member_bytes,
                actual.len()
            );
        }
    }

    #[test]
    fn logical_root_is_schedule_independent_across_threads() {
        let names: Vec<String> = (0..64).map(|i| format!("decl{i}")).collect();
        let sequential = {
            let mut env = Environment::new();
            for name in &names {
                env = env.add_decl(axiom(name)).expect("adds");
            }
            env.logical_root(&KVMap::new())
        };
        for threads in [2usize, 8] {
            let chunks: Vec<Vec<String>> = names
                .chunks(names.len().div_ceil(threads))
                .map(<[String]>::to_vec)
                .collect();
            let root = std::thread::scope(|scope| {
                let handles: Vec<_> = chunks
                    .iter()
                    .map(|chunk| scope.spawn(move || chunk.clone()))
                    .collect();
                let mut env = Environment::new();
                for handle in handles {
                    for name in handle.join().expect("worker") {
                        env = env.add_decl(axiom(&name)).expect("adds");
                    }
                }
                env.logical_root(&KVMap::new())
            });
            assert_eq!(root, sequential, "{threads}-thread interleaving diverged");
        }
    }

    /// The boundary an attacker actually reaches (bead `fln-amv.13`). The budget
    /// machinery living in `pmap` proves nothing if no admission path calls it, so
    /// this pins the wiring and the FL-INV-07 typing at `Environment`.
    ///
    /// A zero-entry budget is used to drive the refusal: real `Name` keys do not
    /// collide on demand — engineering one would be a hash collision — so the
    /// adversarial *family* is modelled in `pmap::tests` with keys that genuinely
    /// share a hash, while the boundary test drives the same refusal through the
    /// budget's zero case. Both exercise the identical production path.
    #[test]
    fn budgeted_admission_is_inconclusive_not_a_rejection_and_leaves_the_environment_intact() {
        let base = Environment::new()
            .add_decl(axiom("Held"))
            .expect("the baseline declaration admits");
        let before_root = base.logical_root(&KVMap::new());

        // Zero entries: no insertion can fit, so the envelope binds immediately.
        let zero = CollisionBudget {
            max_collision_entries: 0,
            ..CollisionBudget::UNBOUNDED
        };
        let outcome = base.try_add_decl_with_budget(axiom("Fresh"), 1, zero);

        assert!(
            outcome.is_inconclusive(),
            "expected inconclusive: {outcome:?}"
        );
        assert_eq!(outcome.outcome_label(), "inconclusive-collision-budget");
        // FL-INV-07: never acceptance, never rejection, never cacheable.
        assert!(!outcome.is_cacheable());
        assert_eq!(outcome.environment(), None);
        assert!(
            !matches!(outcome, DeclAdmission::Rejected(_)),
            "resource exhaustion must never be reported as a rejection"
        );
        let DeclAdmission::Inconclusive(exhausted) = &outcome else {
            unreachable!("asserted inconclusive above")
        };
        assert_eq!(exhausted.resource, CollisionResource::Entries);
        assert_eq!(exhausted.limit, 0);

        // Atomic: the receiver is untouched, down to its logical root.
        assert!(!base.contains(&n("Fresh")));
        assert!(base.contains(&n("Held")));
        assert_eq!(base.logical_root(&KVMap::new()), before_root);

        // Recovery proves the refusal was about the envelope, not the declaration:
        // the very same declaration admits once the budget allows it.
        let admitted = base.try_add_decl_with_budget(axiom("Fresh"), 1, CollisionBudget::UNBOUNDED);
        assert_eq!(admitted.outcome_label(), "admitted");
        assert!(admitted.is_cacheable());
        let grown = admitted
            .environment()
            .expect("an admitted outcome carries the environment");
        assert!(grown.contains(&n("Fresh")));
        assert_ne!(grown.logical_root(&KVMap::new()), before_root);

        // A duplicate is a *rejection* — a complete determination that costs one
        // bounded lookup — and stays a rejection under a budget that would otherwise
        // bind. Exhaustion must not be able to mask or masquerade as the kernel's
        // one-name-one-constant law, in either direction.
        for budget in [CollisionBudget::UNBOUNDED, zero] {
            let duplicate = base.try_add_decl_with_budget(axiom("Held"), 1, budget);
            assert_eq!(duplicate.outcome_label(), "rejected");
            assert!(!duplicate.is_inconclusive());
            assert!(!duplicate.is_cacheable());
            assert_eq!(duplicate.environment(), None);
            assert!(matches!(
                duplicate,
                DeclAdmission::Rejected(EnvError::DuplicateDeclaration { .. })
            ));
        }

        // The unbudgeted semantic operation is unchanged: it never refuses for
        // resource reasons, which is why the budgeted path had to be a sibling
        // rather than a replacement.
        assert!(base.add_decl(axiom("Fresh")).is_ok());
    }
}
