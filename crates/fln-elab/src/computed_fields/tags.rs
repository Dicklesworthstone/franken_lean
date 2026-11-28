//! Persistent membership in the pin's `computed_field` tag attribute.
//!
//! These unordered tags preserve source/artifact metadata. They do not encode
//! cache order or authorize executable replacement: that requires the separate
//! checked-generation journal and its exact inventory validation.

use crate::NatDefinitionElabError;
use crate::source::SourceInferenceError;
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const TAG_MAGIC: &[u8] = b"FLNCFIELD\x01";
/// Maximum rows in the native computed-field tag journal.
pub const MAX_TAGS: usize = 65_536;
const MAX_TAG_BYTES: usize = 65_536;

fn failure(error: SourceInferenceError) -> NatDefinitionElabError {
    NatDefinitionElabError::Inference(error)
}

fn refused(what: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected: what }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceComputedFields", "v1"])
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
    candidate == &descriptor()
}

fn tag_definition(env: &Environment, name: &Name) -> Result<(), NatDefinitionElabError> {
    match env.find(name) {
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
            Ok(())
        }
        _ => Err(refused(
            "an admitted safe definition for a computed-field tag",
        )),
    }
}

/// A public module may retain the checked signature while hiding the logical
/// field's body. Reading this data-only tag accepts that interface; creating a
/// tag still requires the actual safe definition in the checked full world.
fn tag_interface(env: &Environment, name: &Name) -> Result<(), NatDefinitionElabError> {
    match env.find(name) {
        Some(ConstantInfo::Axiom(axiom)) if !axiom.is_unsafe => Ok(()),
        _ => tag_definition(env, name),
    }
}

fn tag_codec(error: crate::instances::InstanceRegistryError) -> NatDefinitionElabError {
    match error {
        crate::instances::InstanceRegistryError::Limit => {
            failure(SourceInferenceError::ResourceLimit)
        }
        _ => refused("a valid computed-field tag journal"),
    }
}

fn append(env: &Environment, field: &Name) -> Result<Environment, NatDefinitionElabError> {
    let mut payload = TAG_MAGIC.to_vec();
    crate::instances::write_name(field, &mut payload).map_err(tag_codec)?;
    if payload.len() > MAX_TAG_BYTES {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let env = match env.extension(&journal_name()) {
        Some(extension) if !supports(&extension.descriptor) => {
            return Err(refused("a valid computed-field tag journal"));
        }
        Some(extension) if extension.len() >= MAX_TAGS => {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| refused("a computed-field tag extension"))?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| refused("a computed-field tag journal entry"))
}

/// Activate an already checked artifact's tag. This records membership only;
/// it does not generate declarations or grant any executable replacement.
/// Source attributes cannot call this entry point.
pub fn register_imported(
    env: &Environment,
    field: &Name,
) -> Result<Environment, NatDefinitionElabError> {
    tag_definition(env, field)?;
    append(env, field)
}

/// Preserve tags after the caller has validated the complete generated bundle.
/// The public projection can hide a getter body, but must retain its exact
/// checked signature. This never reconstructs ordered generation provenance.
pub(super) fn register_generated(
    env: &Environment,
    checked: &Environment,
    fields: &[Name],
) -> Result<Environment, NatDefinitionElabError> {
    let mut existing = read_tags(env)?;
    let mut result = env.clone();
    for field in fields {
        tag_definition(checked, field)?;
        let Some(ConstantInfo::Defn(expected)) = checked.find(field) else {
            return Err(refused("a checked computed-field definition"));
        };
        match result.find(field) {
            Some(ConstantInfo::Defn(actual)) if actual == expected => {}
            Some(ConstantInfo::Axiom(actual))
                if !actual.is_unsafe && actual.base == expected.base => {}
            _ => return Err(refused("an unchanged computed-field public signature")),
        }
        if existing.insert(field.clone()) {
            result = append(&result, field)?;
        }
    }
    Ok(result)
}

/// Read and validate the complete native tag set, including entries retained in
/// an imported module's checked private validation world.
pub fn read_tags(env: &Environment) -> Result<BTreeSet<Name>, NatDefinitionElabError> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(BTreeSet::new());
    };
    if !supports(&extension.descriptor) {
        return Err(refused("a valid computed-field tag journal"));
    }
    if extension.len() > MAX_TAGS {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut names = BTreeSet::new();
    for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
        if entry.payload.len() > MAX_TAG_BYTES {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut bytes = entry
            .payload
            .strip_prefix(TAG_MAGIC)
            .ok_or_else(|| refused("a valid computed-field tag journal entry"))?;
        let name = crate::instances::read_name(&mut bytes).map_err(tag_codec)?;
        if !bytes.is_empty() {
            return Err(refused("one name per computed-field tag entry"));
        }
        tag_interface(validation, &name)?;
        names.insert(name);
    }
    names.retain(|name| env.contains(name));
    Ok(names)
}

/// The same tag contract with a caller-owned work allowance. Charge one initial
/// tick and every payload byte plus one tick per row before decoding any data.
/// This does not reinterpret membership as native generation provenance.
pub fn read(
    env: &Environment,
    budget: crate::records::RecordBudget,
) -> Result<Vec<Name>, super::ComputedFieldError> {
    let mut remaining = budget
        .max_nodes
        .checked_sub(1)
        .ok_or(super::ComputedFieldError::ResourceLimit)?;
    if let Some(extension) = env.extension(&journal_name()) {
        for entry in extension.entries() {
            remaining = remaining
                .checked_sub(entry.payload.len().saturating_add(1))
                .ok_or(super::ComputedFieldError::ResourceLimit)?;
        }
    }
    read_tags(env)
        .map(|names| names.into_iter().collect())
        .map_err(|error| match error {
            NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit) => {
                super::ComputedFieldError::ResourceLimit
            }
            NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)) => {
                super::ComputedFieldError::Reduction(error)
            }
            _ => super::ComputedFieldError::InvalidInventory,
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::records::RecordBudget;
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints};

    #[test]
    fn imported_tag_does_not_create_native_generation_provenance() {
        let field = Name::from_components(["Foreign", "hash"]);
        let env = Environment::new()
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: field.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![field.clone()],
            }))
            .unwrap();
        let tagged = register_imported(&env, &field).unwrap();
        let budget = RecordBudget::default();
        assert_eq!(read(&tagged, budget).unwrap(), vec![field.clone()]);
        assert!(super::super::families(&tagged, budget).unwrap().is_empty());
        let payload_work = tagged
            .extension(&journal_name())
            .unwrap()
            .entries()
            .map(|entry| entry.payload.len() + 1)
            .sum::<usize>();
        assert_eq!(
            read(
                &tagged,
                RecordBudget {
                    max_nodes: payload_work,
                    ..budget
                }
            ),
            Err(super::super::ComputedFieldError::ResourceLimit)
        );
        assert_eq!(
            read(
                &tagged,
                RecordBudget {
                    max_nodes: payload_work + 1,
                    ..budget
                }
            )
            .unwrap(),
            vec![field]
        );
        assert!(read_tags(&env).unwrap().is_empty());
    }
}
