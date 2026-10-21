//! Bounded quotation construction, including mixed fixed and repeated parts.
//!
//! `Lean.Elab.Quotation.quoteSyntax` appends splice arrays only at null-node
//! child slots. It does not wrap them as scalar arguments or repair separators.
//! Preserve that shape while keeping all inserted caller syntax unhygienized.
use super::*;
use std::borrow::Cow;

pub(in crate::extensions) fn checked(
    contents: &Syntax,
    variables: &[(Vec<usize>, Name)],
) -> Result<Syntax, &'static str> {
    let mut pending = vec![(contents, false)];
    let mut visited = 0;
    while let Some((syntax, sequence_slot)) = pending.pop() {
        charge(&mut visited)?;
        if let Some(sequence) = repetition::suffix(syntax)? {
            if !sequence_slot {
                return Err("a repetition splice outside its sequence");
            }
            let name = macro_variable(&sequence.name()?);
            if !variables.iter().any(|(_, variable)| *variable == name) {
                return Err("a repetition capture of no macro variable");
            }
            continue;
        }
        if let Syntax::Node { kind, args, .. } = syntax {
            let leaf = components(kind).last().cloned().unwrap_or_default();
            if leaf == "antiquot" {
                let name = antiquotation_name(syntax).ok_or("an antiquotation of an expression")?;
                if !variables
                    .iter()
                    .any(|(_, variable)| *variable == macro_variable(&name))
                {
                    return Err("an antiquotation of no macro variable");
                }
                continue;
            }
            if leaf.contains("antiquot")
                || matches!(leaf.as_str(), "quot" | "quotSeq" | "dynamicQuot")
            {
                return Err("a splice or a nested quotation in a macro template");
            }
            let sequence = null_args(syntax).is_some();
            pending.extend(args.iter().map(|child| (child, sequence)));
        }
    }
    replace_antiquotations(contents)
}

pub(super) fn charge(visited: &mut usize) -> Result<(), &'static str> {
    *visited = visited
        .checked_add(1)
        .ok_or("macro template work overflow")?;
    if *visited > MAX_TEMPLATE_NODES {
        return Err("a macro template past the node budget");
    }
    Ok(())
}

/// Multiple splices may duplicate large subtrees, not merely many top-level
/// elements. Charge their expanded node weight before allocating each copy.
pub(super) fn copy_capture(value: &Syntax, visited: &mut usize) -> Result<Syntax, &'static str> {
    let mut pending = vec![value];
    while let Some(node) = pending.pop() {
        charge(visited)?;
        if let Syntax::Node { args, .. } = node {
            if args.len() > MAX_TEMPLATE_NODES.saturating_sub(*visited) {
                return Err("a captured template value past the node budget");
            }
            pending.extend(args);
        }
    }
    Ok(value.clone())
}

/// Convert captures to private macro-variable names without changing the
/// surrounding syntax. Splice nodes survive compilation and journal replay.
fn replace_antiquotations(contents: &Syntax) -> Result<Syntax, &'static str> {
    enum Step<'a> {
        Visit(&'a Syntax),
        Build(SourceInfo, &'a Name, usize),
    }
    let mut steps = vec![Step::Visit(contents)];
    let mut built = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(syntax) => {
                if let Some(sequence) = repetition::suffix(syntax)? {
                    built.push(sequence.template()?);
                    continue;
                }
                match (antiquotation_name(syntax), syntax) {
                    (Some(name), _) => built.push(synthetic_ident(macro_variable(&name))),
                    (None, Syntax::Node { info, kind, args }) => {
                        steps.push(Step::Build(*info, kind, args.len()));
                        steps.extend(args.iter().rev().map(Step::Visit));
                    }
                    (None, leaf) => built.push(leaf.clone()),
                }
            }
            Step::Build(info, kind, count) => {
                let start = built
                    .len()
                    .checked_sub(count)
                    .ok_or("invalid template stack")?;
                let args = built.split_off(start);
                built.push(Syntax::Node {
                    info,
                    kind: kind.clone(),
                    args,
                });
            }
        }
    }
    built.pop().ok_or("an empty macro template")
}

pub(in crate::extensions) fn instantiate(
    rule: &NotationRule,
    args: &[Syntax],
    context: &Name,
    scope: u64,
) -> Result<Syntax, &'static str> {
    let mut visited = 0;
    let bound: BTreeMap<&Name, Cow<'_, Syntax>> = rule
        .variables
        .iter()
        .map(|(path, name)| {
            repetition::resolve(rule.pattern.as_ref(), args, path, &mut visited)
                .map(|child| (name, child))
        })
        .collect::<Result<_, _>>()?;
    enum Step<'a> {
        Visit(&'a Syntax),
        Raw(&'a Syntax),
        Splice(repetition::Sequence<'a>),
        Build(SourceInfo, &'a Name, &'a [Syntax]),
    }
    let mut steps = vec![Step::Visit(&rule.rhs)];
    let mut built = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(syntax @ Syntax::Node { info, kind, args }) => {
                charge(&mut visited)?;
                if repetition::suffix(syntax)?.is_some() {
                    return Err("a repetition splice outside its sequence");
                }
                steps.push(Step::Build(*info, kind, args));
                let sequence = null_args(syntax).is_some();
                for (index, child) in args.iter().enumerate().rev() {
                    if sequence && let Some(part) = repetition::suffix(child)? {
                        steps.push(Step::Splice(part));
                    } else if raw_identifier_slot(kind, index) {
                        steps.push(Step::Raw(child));
                    } else {
                        steps.push(Step::Visit(child));
                    }
                }
            }
            Step::Splice(sequence) => {
                let name = sequence.name()?;
                let value = bound
                    .get(&name)
                    .map(AsRef::as_ref)
                    .ok_or("an unbound repetition capture")?;
                if !sequence.accepts(value, &mut visited)? {
                    return Err("a repetition capture with incompatible sequence framing");
                }
                built.push(copy_capture(value, &mut visited)?);
            }
            // Labels retain raw-name semantics. Both labels and ordinary
            // captures insert the exact source tree, without another scope.
            Step::Raw(Syntax::Ident { val, .. }) | Step::Visit(Syntax::Ident { val, .. })
                if bound.contains_key(val) =>
            {
                charge(&mut visited)?;
                built.push(copy_capture(bound[val].as_ref(), &mut visited)?);
            }
            Step::Raw(leaf) => {
                charge(&mut visited)?;
                built.push(leaf.clone());
            }
            Step::Visit(ident @ Syntax::Ident { val, .. }) if val.is_anonymous() => {
                charge(&mut visited)?;
                built.push(ident.clone());
            }
            Step::Visit(Syntax::Ident {
                info,
                raw_val,
                val,
                preresolved,
            }) => {
                charge(&mut visited)?;
                built.push(Syntax::Ident {
                    info: *info,
                    raw_val: *raw_val,
                    val: fln_syntax::hygiene::add_macro_scope(context, val, scope)
                        .map_err(|_| "a template name that cannot take a macro scope")?,
                    preresolved: preresolved.clone(),
                });
            }
            Step::Visit(leaf) => {
                charge(&mut visited)?;
                built.push(leaf.clone());
            }
            Step::Build(info, kind, original) => {
                let start = built
                    .len()
                    .checked_sub(original.len())
                    .ok_or("invalid template construction stack")?;
                let values = built.split_off(start);
                let mut args = Vec::new();
                for (part, mut value) in original.iter().zip(values) {
                    if *kind == Name::from_components(["null"])
                        && repetition::suffix(part)?.is_some()
                    {
                        let Syntax::Node { args: elements, .. } = &mut value else {
                            return Err("a splice value without sequence children");
                        };
                        // Even an empty splice leaves surrounding separator
                        // atoms alone, exactly as quoteSyntax's append does.
                        args.append(elements);
                    } else {
                        args.push(value);
                    }
                }
                built.push(Syntax::Node {
                    info,
                    kind: kind.clone(),
                    args,
                });
            }
        }
    }
    if built.len() != 1 {
        return Err("invalid template result count");
    }
    built.pop().ok_or("an empty template")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn splice(name: &str) -> Syntax {
        Syntax::node(
            Name::from_components(["many", "antiquot_suffix_splice"]),
            vec![
                Syntax::node(
                    Name::from_components(["num", "antiquot"]),
                    vec![
                        Syntax::atom(SourceInfo::None, "$"),
                        null_node(vec![]),
                        synthetic_ident(Name::from_components([name])),
                        null_node(vec![]),
                    ],
                ),
                Syntax::atom(SourceInfo::None, "*"),
            ],
        )
    }

    fn rule(rhs: Syntax) -> NotationRule {
        let variables = vec![(vec![0], macro_variable(&Name::from_components(["xs"])))];
        let rhs = checked(&rhs, &variables).unwrap();
        NotationRule {
            variables,
            rhs,
            prechecked: false,
            pattern: None,
            source: None,
            fallbacks: vec![],
        }
    }

    #[test]
    fn composed_splices_preserve_original_leaves_and_do_not_flatten_scalar_nulls() {
        let scalar = null_node(vec![Syntax::atom(SourceInfo::None, "scalar")]);
        let sequence = null_node(vec![Syntax::atom(SourceInfo::None, "a"), Syntax::Missing]);
        let template = rule(null_node(vec![
            scalar.clone(),
            splice("xs"),
            splice("xs"),
            scalar.clone(),
        ]));
        let result = instantiate(
            &template,
            std::slice::from_ref(&sequence),
            &Name::anonymous(),
            1,
        )
        .unwrap();
        let mut expected = vec![scalar.clone()];
        expected.extend_from_slice(null_args(&sequence).unwrap());
        expected.extend_from_slice(null_args(&sequence).unwrap());
        expected.push(scalar.clone());
        assert_eq!(result, null_node(expected));
        assert_eq!(
            instantiate(&template, &[null_node(vec![])], &Name::anonymous(), 2).unwrap(),
            null_node(vec![scalar.clone(), scalar])
        );
    }

    #[test]
    fn sequence_construction_shares_one_budget_across_all_splices() {
        let template = rule(null_node(vec![splice("xs"), splice("xs"), splice("xs")]));
        let too_large = null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES / 2]);
        assert!(instantiate(&template, &[too_large], &Name::anonymous(), 1).is_err());
        let small = null_node(vec![Syntax::Missing; 3]);
        let expected = null_node(vec![Syntax::Missing; 9]);
        for _ in 0..2 {
            assert_eq!(
                instantiate(
                    &template,
                    std::slice::from_ref(&small),
                    &Name::anonymous(),
                    1
                )
                .unwrap(),
                expected
            );
        }
    }

    #[test]
    fn nested_capture_weight_is_charged_before_duplication() {
        let template = rule(null_node(vec![splice("xs"), splice("xs")]));
        let large = null_node(vec![Syntax::node(
            Name::from_components(["large"]),
            vec![Syntax::Missing; MAX_TEMPLATE_NODES / 2],
        )]);
        assert!(instantiate(&template, &[large], &Name::anonymous(), 1).is_err());
        assert!(instantiate(&template, &[null_node(vec![])], &Name::anonymous(), 1).is_ok());
    }

    #[test]
    fn splice_slots_are_not_inferred_from_arbitrary_node_children() {
        let variables = vec![(vec![0], macro_variable(&Name::from_components(["xs"])))];
        let scalar = Syntax::node(Name::from_components(["ordinary"]), vec![splice("xs")]);
        assert!(checked(&scalar, &variables).is_err());
        assert!(checked(&null_node(vec![splice("unknown")]), &variables).is_err());
        let mut compiled = rule(null_node(vec![splice("xs")]));
        let bad_child = node_args(&compiled.rhs).unwrap()[0].clone();
        compiled.rhs = Syntax::node(Name::from_components(["ordinary"]), vec![bad_child]);
        assert!(instantiate(&compiled, &[null_node(vec![])], &Name::anonymous(), 1).is_err());
    }
}
