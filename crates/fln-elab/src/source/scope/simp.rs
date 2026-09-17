//! Native source simp sets, attached to immutable environment snapshots.
//!
//! This is a versioned source journal, not the Reference's serialized extension.
//! Entries select existing safe definitions or equality lemmas; they carry no
//! proof authority. The ordinary elaborator and both checkers validate all uses.
use fln_core::{expr::ExprNode, name::Name};
use fln_env::{
    constants::{ConstantInfo, DefinitionSafety},
    environment::Environment,
    extensions::{CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance},
};
use std::collections::BTreeMap;

const MAGIC: &[u8] = b"FLNSIMP\x01";
const MAX_ROWS: usize = 4096;
const MAX_BYTES: usize = 16384;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpSetError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    UnsupportedDeclaration(Name),
}
impl std::fmt::Display for SimpSetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native source simp set"),
            Self::Limit => f.write_str("native source simp set resource limit"),
            Self::UnknownDeclaration(n) => {
                write!(f, "unknown simp declaration {}", n.to_display_string())
            }
            Self::UnsupportedDeclaration(n) => write!(
                f,
                "simp requires a safe definition or equality lemma: {}",
                n.to_display_string()
            ),
        }
    }
}
impl std::error::Error for SimpSetError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpEntry {
    pub declaration: Name,
    pub priority: u32,
    pub reverse: bool,
    pub order: usize,
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: Name::from_components(["FrankenLean", "sourceSimp", "v1"]),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}
fn validate(env: &Environment, name: &Name, reverse: bool) -> Result<(), SimpSetError> {
    let info = env
        .find(name)
        .ok_or_else(|| SimpSetError::UnknownDeclaration(name.clone()))?;
    let mut ty = match info {
        ConstantInfo::Defn(d) if d.safety == DefinitionSafety::Safe && !reverse => return Ok(()),
        ConstantInfo::Thm(t) => &t.base.type_,
        ConstantInfo::Axiom(a) if !a.is_unsafe => &a.base.type_,
        _ => return Err(SimpSetError::UnsupportedDeclaration(name.clone())),
    };
    // Keep this admission-independent classifier bounded. Alias-normalized and
    // iff/propositional rule compilation are separate, unsupported profiles.
    let mut applications = 0;
    for _ in 0..MAX_ROWS {
        match ty.node() {
            ExprNode::MData { expr, .. } => ty = expr,
            ExprNode::ForallE { body, .. } if applications == 0 => ty = body,
            ExprNode::App { f, .. } => {
                applications += 1;
                ty = f;
            }
            ExprNode::Const { name: head, .. }
                if *head == Name::from_components(["Eq"]) && applications == 3 =>
            {
                return Ok(());
            }
            _ => return Err(SimpSetError::UnsupportedDeclaration(name.clone())),
        }
    }
    Err(SimpSetError::Limit)
}
fn take<'a>(bytes: &mut &'a [u8], n: usize) -> Result<&'a [u8], SimpSetError> {
    if bytes.len() < n {
        return Err(SimpSetError::Malformed);
    }
    let (head, tail) = bytes.split_at(n);
    *bytes = tail;
    Ok(head)
}
fn number(bytes: &mut &[u8]) -> Result<u32, SimpSetError> {
    Ok(u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| SimpSetError::Malformed)?,
    ))
}
fn read_name(bytes: &mut &[u8]) -> Result<Name, SimpSetError> {
    let count = number(bytes)? as usize;
    if count == 0 || count > 256 {
        return Err(SimpSetError::Malformed);
    }
    let mut name = Name::anonymous();
    for _ in 0..count {
        let len = number(bytes)? as usize;
        if len == 0 || len > MAX_BYTES {
            return Err(SimpSetError::Malformed);
        }
        let part = std::str::from_utf8(take(bytes, len)?).map_err(|_| SimpSetError::Malformed)?;
        name = Name::str(name, part);
    }
    Ok(name)
}

/// Read active rows in deterministic priority order (newer ties first).
/// Corrupt entries and dangling references are errors, never an empty simp set.
pub fn read(env: &Environment) -> Result<Vec<SimpEntry>, SimpSetError> {
    let expected = descriptor();
    let Some(extension) = env.extension(&expected.name) else {
        return Ok(Vec::new());
    };
    if extension.descriptor != expected {
        return Err(SimpSetError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(SimpSetError::Limit);
    }
    let mut active = BTreeMap::new();
    for (order, row) in extension.entries().enumerate() {
        if row.payload.len() > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
        let mut bytes: &[u8] = &row.payload;
        if take(&mut bytes, MAGIC.len())? != MAGIC {
            return Err(SimpSetError::Malformed);
        }
        let operation = take(&mut bytes, 1)?[0];
        let declaration = read_name(&mut bytes)?;
        let priority = number(&mut bytes)?;
        let reverse = match take(&mut bytes, 1)?[0] {
            0 => false,
            1 => true,
            _ => return Err(SimpSetError::Malformed),
        };
        if !bytes.is_empty() {
            return Err(SimpSetError::Malformed);
        }
        match operation {
            0 => {
                validate(env, &declaration, reverse)?;
                active.insert(
                    declaration.clone(),
                    SimpEntry {
                        declaration,
                        priority,
                        reverse,
                        order,
                    },
                );
            }
            1 if priority == 0 && !reverse => {
                if !env.contains(&declaration) {
                    return Err(SimpSetError::UnknownDeclaration(declaration));
                }
                active.remove(&declaration);
            }
            _ => return Err(SimpSetError::Malformed),
        }
    }
    let mut rows: Vec<SimpEntry> = active.into_values().collect();
    rows.sort_by(|a, b| {
        b.priority
            .cmp(&a.priority)
            .then_with(|| b.order.cmp(&a.order))
    });
    Ok(rows)
}

/// Add/update an already admitted rule, or erase it with `None`. The returned
/// environment owns the change; the caller's environment is never mutated.
pub fn update(
    env: &Environment,
    declaration: &Name,
    rule: Option<(u32, bool)>,
) -> Result<Environment, SimpSetError> {
    let rows = read(env)?;
    let current = rows.iter().find(|r| &r.declaration == declaration);
    if !env.contains(declaration) {
        return Err(SimpSetError::UnknownDeclaration(declaration.clone()));
    }
    if let Some((priority, reverse)) = rule {
        validate(env, declaration, reverse)?;
        if current.is_some_and(|r| r.priority == priority && r.reverse == reverse) {
            return Ok(env.clone());
        }
    } else if current.is_none() {
        return Ok(env.clone());
    }
    let expected = descriptor();
    if env
        .extension(&expected.name)
        .is_some_and(|ext| ext.len() >= MAX_ROWS)
    {
        return Err(SimpSetError::Limit);
    }
    let parts = super::components(declaration).map_err(|_| SimpSetError::Limit)?;
    if parts.is_empty() {
        return Err(SimpSetError::Malformed);
    }
    let size = parts
        .iter()
        .try_fold(MAGIC.len() + 10, |n, s| n.checked_add(4 + s.len()))
        .ok_or(SimpSetError::Limit)?;
    if size > MAX_BYTES {
        return Err(SimpSetError::Limit);
    }
    let mut payload = MAGIC.to_vec();
    payload.push(u8::from(rule.is_none()));
    payload.extend((parts.len() as u32).to_le_bytes());
    for part in parts {
        payload.extend((part.len() as u32).to_le_bytes());
        payload.extend(part.as_bytes());
    }
    let (priority, reverse) = rule.unwrap_or((0, false));
    payload.extend(priority.to_le_bytes());
    payload.push(u8::from(reverse));
    let env = if env.extension(&expected.name).is_none() {
        env.register_extension(expected.clone())
            .map_err(|_| SimpSetError::Malformed)?
    } else {
        env.clone()
    };
    env.push_extension_entry(&expected.name, payload)
        .map_err(|_| SimpSetError::Malformed)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unknown_and_corrupt_sets_fail_closed() {
        let env = Environment::new();
        assert!(read(&env).unwrap().is_empty());
        assert!(matches!(
            update(
                &env,
                &Name::from_components(["missing"]),
                Some((1000, false))
            ),
            Err(SimpSetError::UnknownDeclaration(_))
        ));
        for bytes in [vec![], MAGIC.to_vec(), b"FLNSIMP\x02".to_vec()] {
            let env = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&descriptor().name, bytes)
                .unwrap();
            assert_eq!(read(&env), Err(SimpSetError::Malformed));
        }
    }
}
