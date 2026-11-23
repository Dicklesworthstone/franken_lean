//! The late constructor generator is a global builtin request, not a tag to
//! store on the target. Preserve its canonical command and reject other effects.
use super::*;

const MAX_REQUESTS: usize = 4096;

fn refused(expected: &'static str) -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected }
}

/// The repetition count and target order of one standalone command. The pin
/// visits declarations in order, applying each listed attribute to each one.
pub fn command(syntax: &Syntax) -> Result<(usize, Vec<Name>), NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "attribute"]),
        5,
        "attribute command",
    )?;
    expect_atom(&parts[0], "attribute", "attribute keyword")?;
    expect_atom(&parts[1], "[", "attribute opener")?;
    expect_atom(&parts[3], "]", "attribute closer")?;
    let attributes = expect_null_args(&parts[2], "attribute list")?;
    if attributes.len() > MAX_REQUESTS * 2 {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    if attributes.is_empty() || attributes.len() % 2 == 0 {
        return Err(refused("a nonempty attribute list"));
    }
    let mut repetitions = 0usize;
    for (index, attribute) in attributes.iter().enumerate() {
        if index % 2 != 0 {
            expect_atom(attribute, ",", "attribute separator")?;
            continue;
        }
        let instance = expect_node(
            attribute,
            &parser_kind(&["Term", "attrInstance"]),
            2,
            "global gen_constructor_elims attribute",
        )?;
        let kind = expect_node(
            &instance[0],
            &parser_kind(&["Term", "attrKind"]),
            1,
            "attribute kind",
        )?;
        expect_empty_null(&kind[0], "global gen_constructor_elims attribute")?;
        let simple = expect_node(
            &instance[1],
            &parser_kind(&["Attr", "simple"]),
            2,
            "gen_constructor_elims attribute",
        )?;
        let Syntax::Ident { val, .. } = &simple[0] else {
            return Err(refused("gen_constructor_elims attribute"));
        };
        if val != &Name::from_components(["gen_constructor_elims"]) {
            return Err(refused("gen_constructor_elims attribute"));
        }
        expect_empty_null(&simple[1], "gen_constructor_elims without arguments")?;
        repetitions += 1;
    }
    let targets = expect_null_args(&parts[4], "attribute declarations")?;
    if targets.len() > MAX_REQUESTS / repetitions {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    if targets.is_empty() {
        return Err(refused("attribute declarations"));
    }
    let targets = targets
        .iter()
        .map(|syntax| {
            let Syntax::Ident { val, .. } = syntax else {
                return Err(refused("an attribute declaration name"));
            };
            Ok(val.clone())
        })
        .collect::<Result<_, _>>()?;
    Ok((repetitions, targets))
}
