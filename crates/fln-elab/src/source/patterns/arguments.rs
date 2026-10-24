//! Constructor argument labels survive matrix planning until the discriminant determines
//! the actual constructor. The checked matcher and pattern-typing model use one telescope
//! order, including named implicit fields (`Lean/Elab/PatternVar.lean:processCtorAppContext`).
use super::*;
use fln_env::constants::ConstructorVal;
use std::collections::VecDeque;
use std::sync::Arc;

/// The label is not a binding: erase its macro scopes as `expandArgs` does. The value keeps
/// its exact syntax and scopes so a pattern variable cannot capture a caller's local.
pub(in crate::source) fn named_argument(
    syntax: &Syntax,
) -> Result<Option<(Name, &Syntax)>, NatDefinitionElabError> {
    let kind = parser_kind(&["Term", "namedArgument"]);
    if syntax.kind() != Some(&kind) {
        return Ok(None);
    }
    let parts = expect_node(syntax, &kind, 5, "named constructor argument")?;
    expect_atom(&parts[0], "(", "named constructor argument opener")?;
    expect_atom(&parts[2], ":=", "named constructor argument assignment")?;
    expect_atom(&parts[4], ")", "named constructor argument closer")?;
    let Syntax::Ident { val, .. } = &parts[1] else {
        return Err(invalid());
    };
    let name = val.erase_macro_scopes();
    if name.is_anonymous() {
        return Err(invalid());
    }
    Ok(Some((name, &parts[3])))
}

/// `None` is an omitted implicit argument, or a wildcard supplied by `..`. Every slot is a
/// real binder of the admitted constructor; a named argument never changes binder order.
pub(in crate::source) fn normalize<'a>(
    cx: &mut Context,
    arguments: &[&'a Syntax],
    constructor: &ConstructorVal,
) -> Result<Vec<Option<&'a Syntax>>, NatDefinitionElabError> {
    let mut positional = VecDeque::new();
    let mut named = Vec::new();
    let mut names = HashSet::new();
    let mut ellipsis = false;
    for (index, argument) in arguments.iter().enumerate() {
        cx.tick()?;
        if application::is_ellipsis(argument) {
            let [atom] = expect_node(
                argument,
                &parser_kind(&["Term", "ellipsis"]),
                1,
                "constructor ellipsis",
            )?
            else {
                return Err(invalid());
            };
            expect_atom(atom, "..", "constructor ellipsis")?;
            if index + 1 != arguments.len() {
                return Err(invalid());
            }
            ellipsis = true;
        } else if let Some((name, value)) = named_argument(argument)? {
            if !names.insert(name.clone()) {
                return Err(failure(SourceInferenceError::DuplicateNamedArgument(name)));
            }
            named.push((name, value));
        } else {
            positional.push_back(*argument);
        }
    }
    let mut type_ = constructor.base.type_.clone();
    let mut slots = Vec::new();
    let mut missing = false;
    while let ExprNode::ForallE {
        binder_name,
        binder_info,
        body,
        ..
    } = type_.node()
    {
        cx.tick()?;
        let argument = if let Some(index) = named.iter().position(|(name, _)| name == binder_name) {
            Some(named.remove(index).1)
        } else if *binder_info == BinderInfo::Default {
            let argument = positional.pop_front();
            missing |= argument.is_none() && !ellipsis;
            argument
        } else {
            None
        };
        slots.push(argument);
        type_ = body.clone();
    }
    if let Some((name, _)) = named.into_iter().next() {
        return Err(failure(SourceInferenceError::InvalidNamedArgument(name)));
    }
    if missing || !positional.is_empty() {
        return Err(failure(SourceInferenceError::Match(
            matching::MatchError::WrongArity,
        )));
    }
    if slots.len() != constructor.num_params as usize + constructor.num_fields as usize {
        return Err(invalid());
    }
    Ok(slots)
}

/// Positional arguments skip the labels already supplied in their own row. Retaining that
/// set is necessary: `c (b := p) q` and `c q p` can name the same physical field, but only the
/// typed matcher knows which one. Named slots themselves have a stable identity across rows.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum Slot {
    Named(Name),
    Positional(usize, Arc<[Name]>),
}
pub(super) fn slots(labels: &[Option<Name>]) -> Vec<Slot> {
    let mut names: Vec<_> = labels.iter().flatten().cloned().collect();
    names.sort();
    let names: Arc<[Name]> = names.into();
    let mut positional = 0;
    labels
        .iter()
        .map(|label| match label {
            Some(name) => Slot::Named(name.clone()),
            None => {
                let slot = Slot::Positional(positional, names.clone());
                positional += 1;
                slot
            }
        })
        .collect()
}

pub(super) fn argument(label: &Option<Name>, value: Syntax) -> Syntax {
    match label {
        None => value,
        Some(name) => Syntax::node(
            parser_kind(&["Term", "namedArgument"]),
            vec![
                atom("("),
                identifier(name.clone()),
                atom(":="),
                value,
                atom(")"),
            ],
        ),
    }
}
