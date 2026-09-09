//! Canonical named-instance syntax; publication remains outside elaboration.
use super::*;
pub(super) struct Parts<'a> {
    pub keyword: &'a Syntax,
    pub id: &'a Syntax,
    pub signature: &'a Syntax,
    pub value: &'a Syntax,
    pub priority: u32,
}
pub(super) fn parts(syntax: &Syntax) -> Result<Parts<'_>, NatDefinitionElabError> {
    let args = expect_node(
        syntax,
        &parser_kind(&["Command", "instance"]),
        6,
        "named instance",
    )?;
    let attr = expect_node(
        &args[0],
        &parser_kind(&["Term", "attrKind"]),
        1,
        "global instance scope",
    )?;
    expect_empty_null(&attr[0], "global instance scope")?;
    expect_atom(&args[1], "instance", "instance keyword")?;
    let priority = match expect_null_args(&args[2], "instance priority")? {
        [] => 1000,
        [syntax] => {
            let p = expect_node(
                syntax,
                &parser_kind(&["Command", "namedPrio"]),
                5,
                "numeric instance priority",
            )?;
            expect_atom(&p[0], "(", "priority opener")?;
            expect_atom(&p[1], "priority", "priority keyword")?;
            expect_atom(&p[2], ":=", "priority assignment")?;
            expect_atom(&p[4], ")", "priority closer")?;
            let num = expect_node(
                &p[3],
                &Name::from_components(["num"]),
                1,
                "priority numeral",
            )?;
            let Syntax::Atom { val, .. } = &num[0] else {
                return Err(failure(SourceInferenceError::Scope));
            };
            // This bounded profile supports nonnegative decimal u32 priorities.
            if val.is_empty() || !val.bytes().all(|b| b.is_ascii_digit()) {
                return Err(failure(SourceInferenceError::Scope));
            }
            val.parse::<u32>()
                .map_err(|_| failure(SourceInferenceError::Scope))?
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let [id] = expect_null_args(&args[3], "explicit instance name")? else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    Ok(Parts {
        keyword: &args[1],
        id,
        signature: &args[4],
        value: &args[5],
        priority,
    })
}
pub(super) fn registration(syntax: &Syntax) -> Result<Option<(Name, u32)>, NatDefinitionElabError> {
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "declaration",
    )?;
    if !matches!(&declaration[1],Syntax::Node{kind,..} if kind==&parser_kind(&["Command","instance"]))
    {
        return Ok(None);
    }
    let parts = parts(&declaration[1])?;
    let id = expect_node(
        parts.id,
        &parser_kind(&["Command", "declId"]),
        2,
        "instance identifier",
    )?;
    expect_empty_null(&id[1], "absent explicit universe declaration")?;
    let Syntax::Ident { val, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if val.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    Ok(Some((val.clone(), parts.priority)))
}
