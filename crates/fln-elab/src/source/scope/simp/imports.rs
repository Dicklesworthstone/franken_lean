//! Proof-aware import events over the same immutable native simp journal.
//! Persist every event: a redundant registration or erasure in the union of
//! imports can become effective when replayed in a source module's own context.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportedSimpRule {
    Proof {
        origin: Name,
        proof: Name,
        priority: u32,
    },
    Unfold {
        declaration: Name,
    },
    Erase {
        declaration: Name,
    },
}

impl ImportedSimpRule {
    /// Validate one operation against fixed admitted declarations without reading
    /// or changing the journal. Consumers may defer UnsupportedDeclaration, but
    /// must propagate malformed input, missing names and resource exhaustion.
    /// This selects metadata; it does not check or admit a proof.
    pub fn validate(&self, env: &Environment) -> Result<(), SimpSetError> {
        self.payload(env).map(|_| ())
    }

    fn payload(&self, env: &Environment) -> Result<Vec<u8>, SimpSetError> {
        let origin = match self {
            ImportedSimpRule::Proof { origin, .. } => origin,
            ImportedSimpRule::Unfold { declaration } | ImportedSimpRule::Erase { declaration } => {
                declaration
            }
        };
        if !env.contains(origin) {
            return Err(SimpSetError::UnknownDeclaration(origin.clone()));
        }
        let payload = match self {
            ImportedSimpRule::Proof {
                origin,
                proof,
                priority,
            } => {
                validate_proof(env, proof)?;
                proof_payload(origin, proof, *priority)?
            }
            ImportedSimpRule::Unfold { declaration } => {
                if !matches!(env.find(declaration), Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe)
                {
                    return Err(SimpSetError::UnsupportedDeclaration(declaration.clone()));
                }
                source_payload(declaration, Some((1000, false)))?
            }
            ImportedSimpRule::Erase { declaration } => source_payload(declaration, None)?,
        };
        Ok(payload)
    }
}

pub(super) fn validate_proof(env: &Environment, proof: &Name) -> Result<(), SimpSetError> {
    match env.find(proof) {
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
            // Safe data-valued definitions are not proofs. This bounded shape
            // test only selects Eq/Iff evidence; ordinary elaboration and both
            // declaration checkers remain responsible for every actual use.
            let mut ty = &definition.base.type_;
            let mut applications = 0usize;
            for _ in 0..MAX_ROWS {
                match ty.node() {
                    ExprNode::MData { expr, .. } => ty = expr,
                    ExprNode::ForallE { body, .. } if applications == 0 => ty = body,
                    ExprNode::App { f, .. } => {
                        applications += 1;
                        ty = f;
                    }
                    ExprNode::Const { name, levels }
                        if (*name == Name::from_components(["Eq"])
                            && applications == 3
                            && levels.len() == 1)
                            || (*name == Name::from_components(["Iff"])
                                && applications == 2
                                && levels.is_empty()) =>
                    {
                        return Ok(());
                    }
                    _ => return Err(SimpSetError::UnsupportedDeclaration(proof.clone())),
                }
            }
            Err(SimpSetError::Limit)
        }
        // Preserve the native validator's supported proposition forms for
        // theorems and axioms instead of narrowing ordinary source simp.
        _ => validate(env, proof, false),
    }
}

fn proof_payload(origin: &Name, proof: &Name, priority: u32) -> Result<Vec<u8>, SimpSetError> {
    let mut payload = PROOF_MAGIC.to_vec();
    payload.push(2);
    for name in [origin, proof] {
        if name.is_anonymous() {
            return Err(SimpSetError::Malformed);
        }
        crate::instances::write_name(name, &mut payload).map_err(|error| match error {
            crate::instances::InstanceRegistryError::Limit => SimpSetError::Limit,
            _ => SimpSetError::Malformed,
        })?;
        if payload.len().saturating_add(5) > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
    }
    payload.extend(priority.to_le_bytes());
    payload.push(0); // proof is already oriented: never reverse it a second time
    Ok(payload)
}

/// Append checked import operations, reading the pre-existing journal once per
/// batch. No declaration is created and the input environment is never mutated.
/// Events are retained even when they do not change the currently active set.
pub fn import_rules(
    env: &Environment,
    rules: &[ImportedSimpRule],
) -> Result<Environment, SimpSetError> {
    read(env)?;
    let count = env
        .extension(&descriptor().name)
        .map_or(0, |state| state.len());
    if count
        .checked_add(rules.len())
        .is_none_or(|count| count > MAX_ROWS)
    {
        return Err(SimpSetError::Limit);
    }
    let mut next = env.clone();
    for rule in rules {
        let payload = rule.payload(env)?;
        next = append(&next, payload)?;
    }
    Ok(next)
}

/// Select an admitted proof while keeping the attribute's distinct erase origin.
pub fn register_imported_proof(
    env: &Environment,
    origin: &Name,
    proof: &Name,
    priority: u32,
) -> Result<Environment, SimpSetError> {
    import_rules(
        env,
        &[ImportedSimpRule::Proof {
            origin: origin.clone(),
            proof: proof.clone(),
            priority,
        }],
    )
}

#[cfg(test)]
mod tests;
