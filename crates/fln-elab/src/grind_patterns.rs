//! Explicit global E-matching triggers from the pin's grind_pattern command.
//!
//! Rows select applications of admitted proofs; they never confer proof
//! authority. Patterns are captured when registered, before later namespace or
//! reducibility changes. One row is one simultaneous multipattern, and repeated
//! registrations for the same declaration remain distinct and ordered.
mod captured;
mod codec;
pub(crate) use captured::{ground_pattern, is_wildcard, mark_ground, wildcard};
#[cfg(test)]
mod tests;

use crate::instances::InstanceRegistryError;
use fln_core::expr::{Expr, ExprNode};
use fln_core::level::{Level, LevelView};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::HashSet;

pub const MAX_PARAMETERS: u32 = 16;
pub const MAX_PATTERNS: usize = 32;
pub const MAX_ROWS: usize = 4096;
pub(crate) const MAX_SYMBOLS: usize = 4096;
const MAX_ENTRY_BYTES: usize = 256 * 1024;
const MAX_JOURNAL_BYTES: usize = 16 * 1024 * 1024;
const MAX_STEPS: usize = 1_000_000;
const MAGIC: &[u8] = b"FLNGRIND\x01";
const CAPTURED_MAGIC: &[u8] = b"FLNGRIND\x02";

/// The pin's normalized user multipattern and activation symbols, captured in
/// registration order. This is selection metadata, never a proof or declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapturedPatterns {
    pub patterns: Vec<Expr>,
    pub symbols: Vec<Name>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrindPattern {
    pub declaration: Name,
    /// All forall binders, including trailing propositional premises.
    pub num_params: u32,
    /// The data prefix instantiated by matching; remaining binders stay premises.
    pub data_params: u32,
    /// One simultaneous group, abstracted over the entire theorem telescope.
    /// Universe parameters retain the admitted declaration's parameter names.
    /// Open using subst_loose(num_params - data_params, data_locals), with locals
    /// in their original telescope order. No trailing proof variable may occur.
    pub patterns: Vec<Expr>,
    /// Legacy rows have no pinned snapshot and cannot be exported as .olean
    /// user patterns. New rows match this immutable normalized representation.
    pub captured: Option<CapturedPatterns>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrindPatternError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    Unsupported(&'static str),
}

impl std::fmt::Display for GrindPatternError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native grind-pattern journal"),
            Self::Limit => f.write_str("native grind-pattern resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "grind pattern refers to {}, which is not admitted",
                name.to_display_string()
            ),
            Self::Unsupported(feature) => write!(f, "unsupported grind pattern: {feature}"),
        }
    }
}
impl std::error::Error for GrindPatternError {}

type Error = GrindPatternError;

fn codec_error(error: InstanceRegistryError) -> Error {
    match error {
        InstanceRegistryError::Limit => Error::Limit,
        _ => Error::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "grindPatterns", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

fn spend(remaining: &mut usize) -> Result<(), Error> {
    *remaining = remaining.checked_sub(1).ok_or(Error::Limit)?;
    Ok(())
}

/// The current native matcher does not implement the pin's interpreted heads
/// or pattern gadgets. Refusing these is a capability boundary, not a claim
/// that every such pattern is invalid in Lean.
pub(crate) fn supported_head(name: &Name) -> bool {
    ![
        "Eq",
        "HEq",
        "Iff",
        "And",
        "Or",
        "Not",
        "Ne",
        "ite",
        "dite",
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "HDiv.hDiv",
        "HMod.hMod",
        "LT.lt",
        "LE.le",
        "[grind_dontcare]",
        "Lean.Grind.offset",
        "Lean.Grind.genPattern",
        "Lean.Grind.genHEqPattern",
        "Lean.Grind.eqBwdPattern",
        "Lean.Grind.nestedProof",
        "Lean.Grind.nestedDecidable",
    ]
    .iter()
    .any(|head| *name == Name::from_components(head.split('.')))
}

pub(crate) fn safe_proof_candidate(info: &ConstantInfo) -> bool {
    match info {
        ConstantInfo::Axiom(value) => !value.is_unsafe,
        ConstantInfo::Thm(_) => true,
        ConstantInfo::Defn(value) => value.safety == DefinitionSafety::Safe,
        ConstantInfo::Opaque(value) => !value.is_unsafe,
        ConstantInfo::Ctor(value) => !value.is_unsafe,
        _ => false,
    }
}

fn validate_level(level: &Level, parameters: &[Name], remaining: &mut usize) -> Result<(), Error> {
    let mut pending = vec![level];
    while let Some(level) = pending.pop() {
        spend(remaining)?;
        match level.view() {
            LevelView::Zero => {}
            LevelView::Param(name) if parameters.contains(name) => {}
            LevelView::Succ(inner) => pending.push(inner),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => pending.extend([a, b]),
            _ => return Err(Error::Malformed),
        }
    }
    Ok(())
}

fn validate_with(
    env: &Environment,
    row: &GrindPattern,
    remaining: &mut usize,
) -> Result<(), Error> {
    if row.num_params > MAX_PARAMETERS || row.patterns.len() > MAX_PATTERNS {
        return Err(Error::Limit);
    }
    if row.declaration.is_anonymous() || row.data_params > row.num_params || row.patterns.is_empty()
    {
        return Err(Error::Malformed);
    }
    let info = env
        .find(&row.declaration)
        .ok_or_else(|| Error::UnknownDeclaration(row.declaration.clone()))?;
    if !safe_proof_candidate(info) {
        return Err(Error::Unsupported(
            "an unsafe or non-proof declaration kind",
        ));
    }
    let level_parameters = &info.constant_val().level_params;
    let mut covered = vec![false; row.data_params as usize];
    let mut pending = Vec::new();
    for pattern in &row.patterns {
        let mut head = pattern;
        while let ExprNode::App { f, .. } = head.node() {
            spend(remaining)?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(Error::Unsupported(
                "a trigger without a constant application head",
            ));
        };
        if !supported_head(name) {
            return Err(Error::Unsupported("an interpreted trigger head"));
        }
        pending.push(pattern);
    }
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        spend(remaining)?;
        if !seen.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::BVar { idx }
                if *idx < row.num_params && *idx >= row.num_params - row.data_params =>
            {
                covered[(row.num_params - idx - 1) as usize] = true;
            }
            ExprNode::Const { name, levels } => {
                let declaration = env
                    .find(name)
                    .ok_or_else(|| Error::UnknownDeclaration(name.clone()))?;
                if levels.len() != declaration.constant_val().level_params.len() {
                    return Err(Error::Malformed);
                }
                for level in levels {
                    validate_level(level, level_parameters, remaining)?;
                }
            }
            ExprNode::Sort { level } => validate_level(level, level_parameters, remaining)?,
            ExprNode::App { f, a } => {
                let mut head = f;
                while let ExprNode::App { f, .. } = head.node() {
                    spend(remaining)?;
                    head = f;
                }
                if !matches!(head.node(), ExprNode::Const { name, .. } if supported_head(name)) {
                    return Err(Error::Unsupported(
                        "an interpreted or variable-headed subpattern",
                    ));
                }
                pending.extend([f, a]);
            }
            ExprNode::Lit { .. } => {}
            _ => {
                return Err(Error::Unsupported(
                    "a binder, proof variable, hole or unfolded projection",
                ));
            }
        }
    }
    if !covered.iter().all(|found| *found) {
        return Err(Error::Unsupported(
            "a data parameter not determined by the patterns",
        ));
    }
    if let Some(capture) = &row.captured {
        captured::validate_with(env, row, capture, remaining)?;
        captured::compatible(&row.patterns, &capture.patterns, remaining)?;
    }
    Ok(())
}

/// Structural checks for untrusted selection metadata. The compiler and matcher
/// additionally check the actual proposition and telescope in their local
/// context; serialized counts never authorize a proof application.
pub fn validate(env: &Environment, row: &GrindPattern) -> Result<(), Error> {
    let mut remaining = MAX_STEPS;
    validate_with(env, row, &mut remaining)
}

/// Check a normalized foreign snapshot before opening any of its indices.
pub(crate) fn validate_capture(
    env: &Environment,
    row: &GrindPattern,
    capture: &CapturedPatterns,
) -> Result<(), Error> {
    if row.num_params > MAX_PARAMETERS {
        return Err(Error::Limit);
    }
    if row.data_params > row.num_params {
        return Err(Error::Malformed);
    }
    let mut remaining = MAX_STEPS;
    captured::validate_with(env, row, capture, &mut remaining)
}

/// Append completely compiled rows as one transaction. Neither a failed
/// compilation nor an encoding/validation cutoff publishes a partial batch.
pub fn register(env: &Environment, rows: &[GrindPattern]) -> Result<Environment, Error> {
    read(env)?;
    let name = journal_name();
    let previous = env.extension(&name).map_or(0, |extension| extension.len());
    if rows.len() > MAX_ROWS.saturating_sub(previous) {
        return Err(Error::Limit);
    }
    let mut total = 0usize;
    for (entry, _) in env.metadata_validation_entries(&name) {
        total = total.checked_add(entry.payload.len()).ok_or(Error::Limit)?;
    }
    let mut payloads = Vec::new();
    let mut remaining = MAX_STEPS;
    for row in rows {
        validate_with(env, row, &mut remaining)?;
        let payload = codec::encode(row)?;
        total = total.checked_add(payload.len()).ok_or(Error::Limit)?;
        if total > MAX_JOURNAL_BYTES {
            return Err(Error::Limit);
        }
        payloads.push(payload);
    }
    if payloads.is_empty() {
        return Ok(env.clone());
    }
    let mut next = if env.extension(&name).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| Error::Malformed)?
    } else {
        env.clone()
    };
    for payload in payloads {
        next = next
            .push_extension_entry(&name, payload)
            .map_err(|_| Error::Malformed)?;
    }
    // Validate the exact serialized, cumulative result before publication. A
    // fresh append budget cannot authorize a journal the reader must refuse.
    read(&next)?;
    Ok(next)
}

/// Validate the complete journal before presenting any rows. A projected view
/// omits targets that are themselves hidden, but cannot silently discard a
/// visible theorem's pattern just because one of its symbols is unavailable.
pub fn read(env: &Environment) -> Result<Vec<GrindPattern>, Error> {
    let name = journal_name();
    let Some(extension) = env.extension(&name) else {
        return Ok(Vec::new());
    };
    if extension.descriptor != descriptor() {
        return Err(Error::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(Error::Limit);
    }
    let mut remaining = MAX_STEPS;
    let mut total = 0usize;
    let mut rows = Vec::new();
    for (entry, validation) in env.metadata_validation_entries(&name) {
        total = total.checked_add(entry.payload.len()).ok_or(Error::Limit)?;
        if total > MAX_JOURNAL_BYTES {
            return Err(Error::Limit);
        }
        let row = codec::decode(&entry.payload)?;
        validate_with(validation, &row, &mut remaining)?;
        if env.contains(&row.declaration) {
            validate_with(env, &row, &mut remaining)?;
            rows.push(row);
        }
    }
    Ok(rows)
}
