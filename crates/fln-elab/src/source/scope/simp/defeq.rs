//! Native source reflexivity tags. These are selection metadata, not proofs.
//!
//! The pin infers its default dsimp tag for naked `:= rfl`, but not `:= (rfl)`
//! or `:= by rfl`. Preserve that distinction after syntax has been discarded.
//! Before recording a tag, verify the admitted theorem's structural reflexivity
//! proof and generic definitional equality. User-written `:= rfl` is the pin's
//! explicit defeq-attribute path (MutualDef.elabMutualDef), not its stricter
//! generated-theorem inference path. Module replay keeps this bounded journal.
use super::super::super::*;
use fln_env::constants::ConstantInfo;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNDSIMP\x01";
const MAX_ROWS: usize = 4096;
const MAX_ENTRY_BYTES: usize = 16 * 1024;

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: Name::from_components(["FrankenLean", "sourceDefEq", "v1"]),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}
fn malformed() -> NatDefinitionElabError {
    failure(SourceInferenceError::SimpSet(
        super::SimpSetError::Malformed,
    ))
}
fn limit() -> NatDefinitionElabError {
    failure(SourceInferenceError::SimpSet(super::SimpSetError::Limit))
}
fn codec(error: crate::instances::InstanceRegistryError) -> NatDefinitionElabError {
    match error {
        crate::instances::InstanceRegistryError::Limit => limit(),
        _ => malformed(),
    }
}

/// Only the original naked syntax requests automatic inference. Definitions,
/// examples, parentheses, tactic blocks and macros are not guessed equivalent.
pub fn direct_rfl(syntax: &Syntax) -> bool {
    let Syntax::Node { kind, args, .. } = syntax else {
        return false;
    };
    if kind != &parser_kind(&["Command", "declaration"]) {
        return false;
    }
    let [_, Syntax::Node { kind, args, .. }] = args.as_slice() else {
        return false;
    };
    if kind != &parser_kind(&["Command", "theorem"]) {
        return false;
    }
    let [_, _, _, Syntax::Node { kind, args, .. }] = args.as_slice() else {
        return false;
    };
    if kind != &parser_kind(&["Command", "declValSimple"]) {
        return false;
    }
    let [
        Syntax::Atom {
            val: assignment, ..
        },
        Syntax::Ident { val, .. },
        suffix,
        clause,
    ] = args.as_slice()
    else {
        return false;
    };
    assignment == ":="
        && val == &Name::from_components(["rfl"])
        && expect_empty_null(clause, "no where clause").is_ok()
        && matches!(suffix, Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Termination", "suffix"])
            && args.len() == 2
            && args.iter().all(|arg| expect_empty_null(arg, "no termination hint").is_ok()))
}

/// Read once per tactic; charge bounded name-decoding work before retaining it.
/// Corrupt, oversized or dangling metadata is an error, never an empty rule set.
pub(in crate::source) fn read(
    environment: &Environment,
    mut tick: impl FnMut() -> Result<(), NatDefinitionElabError>,
) -> Result<BTreeSet<Name>, NatDefinitionElabError> {
    let mut names = BTreeSet::new();
    let descriptor = descriptor();
    let Some(state) = environment.extension(&descriptor.name) else {
        return Ok(names);
    };
    if state.descriptor != descriptor {
        return Err(malformed());
    }
    if state.len() > MAX_ROWS {
        return Err(limit());
    }
    for entry in state.entries() {
        tick()?;
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(limit());
        }
        for _ in entry.payload.chunks(64) {
            tick()?;
        }
        let mut bytes = entry.payload.strip_prefix(MAGIC).ok_or_else(malformed)?;
        let name = crate::instances::read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty()
            || !matches!(environment.find(&name), Some(ConstantInfo::Thm(_)))
            || !names.insert(name)
        {
            return Err(malformed());
        }
    }
    Ok(names)
}

/// Called only on the successor of checked source theorem admission. No
/// declaration is created, and no caller-supplied boolean can authorize a tag.
pub fn infer(
    environment: &Environment,
    name: &Name,
    kernel: Budget,
) -> Result<Environment, NatDefinitionElabError> {
    let Some(ConstantInfo::Thm(theorem)) = environment.find(name) else {
        // Public module theorem interfaces may deliberately conceal the body.
        // Lack of a body is not evidence that its proof is reflexive.
        return Ok(environment.clone());
    };
    let mut context = Context::new(environment, kernel);
    let tagged = read(environment, || context.tick())?;
    if tagged.contains(name) {
        return Ok(environment.clone());
    }
    let proof = Typed {
        value: theorem.value.clone(),
        type_: theorem.base.type_.clone(),
    };
    if !context.dsimp_rfl_proof(proof, &tagged)?
        || !context.dsimp_generic_defeq(&theorem.base.type_, &theorem.base.level_params)?
    {
        return Ok(environment.clone());
    }
    let mut payload = MAGIC.to_vec();
    crate::instances::write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES || tagged.len() >= MAX_ROWS {
        return Err(limit());
    }
    let descriptor = descriptor();
    let environment = if environment.extension(&descriptor.name).is_none() {
        environment
            .register_extension(descriptor.clone())
            .map_err(|_| malformed())?
    } else {
        environment.clone()
    };
    environment
        .push_extension_entry(&descriptor.name, payload)
        .map_err(|_| malformed())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_tag_inference_requires_naked_rfl_not_equivalent_syntax() {
        for (body, expected) in [("rfl", true), ("(rfl)", false), ("by rfl", false)] {
            let source = format!("theorem t (A : Type) (x : A) : x = x := {body}");
            let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
            assert_eq!(direct_rfl(parsed.syntax()), expected, "{source}");
        }
        let parsed =
            fln_parse::parse_definition(b"def value (A : Type) (x : A) : x = x := rfl").unwrap();
        assert!(!direct_rfl(parsed.syntax()));
    }

    #[test]
    fn malformed_and_dangling_metadata_never_become_an_empty_set() {
        let descriptor = descriptor();
        let environment = Environment::new()
            .register_extension(descriptor.clone())
            .unwrap();
        let invalid = environment
            .push_extension_entry(&descriptor.name, b"bad".to_vec())
            .unwrap();
        assert!(read(&invalid, || Ok(())).is_err());
        let mut payload = MAGIC.to_vec();
        crate::instances::write_name(&Name::from_components(["missing"]), &mut payload).unwrap();
        let dangling = environment
            .push_extension_entry(&descriptor.name, payload)
            .unwrap();
        assert!(read(&dangling, || Ok(())).is_err());
        assert!(read(&environment, || Ok(())).unwrap().is_empty());
    }

    #[test]
    fn oversized_rows_and_interrupted_reads_are_refusals() {
        let descriptor = descriptor();
        let environment = Environment::new()
            .register_extension(descriptor.clone())
            .unwrap();
        let oversized = environment
            .push_extension_entry(&descriptor.name, vec![0; MAX_ENTRY_BYTES + 1])
            .unwrap();
        assert!(matches!(
            read(&oversized, || Ok(())),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::SimpSet(super::super::SimpSetError::Limit)
            ))
        ));
        let invalid = environment
            .push_extension_entry(&descriptor.name, MAGIC.to_vec())
            .unwrap();
        let problem = read(&invalid, || {
            Err(failure(SourceInferenceError::ResourceLimit))
        })
        .unwrap_err();
        assert!(matches!(
            problem,
            NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)
        ));
    }
}
