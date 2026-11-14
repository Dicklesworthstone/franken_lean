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
        if let Some(iteration) = repetition::iteration(syntax)?
            && repetition::suffix(syntax)?.is_none()
        {
            if !sequence_slot {
                return Err("a bracketed repetition splice outside its sequence");
            }
            iteration.body_variables(antiquotation_name, &mut visited)?;
            pending.push((iteration.body, false));
            continue;
        }
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
            if escaped_antiquotation(syntax)? {
                let (body, _, framing) = escaped_capture_body(syntax)?;
                for _ in 0..framing {
                    charge(&mut visited)?;
                }
                pending.push((body, false));
                continue;
            }
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
            if leaf.contains("antiquot") && leaf != "antiquot" {
                return Err("an unsupported splice in a macro template");
            }
            let sequence = null_args(syntax).is_some();
            pending.extend(args.iter().map(|child| (child, sequence)));
        }
    }
    replace_antiquotations(contents)
}

pub(in crate::extensions) fn is_repetition(syntax: &Syntax) -> Result<bool, &'static str> {
    Ok(repetition::suffix(syntax)?.is_some() || repetition::iteration(syntax)?.is_some())
}

pub(in crate::extensions) fn charge(visited: &mut usize) -> Result<(), &'static str> {
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
pub(in crate::extensions) fn copy_capture(
    value: &Syntax,
    visited: &mut usize,
) -> Result<Syntax, &'static str> {
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
        Build(SourceInfo, &'a Name, usize, bool),
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
                        steps.push(Step::Build(
                            *info,
                            kind,
                            args.len(),
                            escaped_antiquotation(syntax)?,
                        ));
                        steps.extend(args.iter().rev().map(Step::Visit));
                    }
                    (None, leaf) => built.push(leaf.clone()),
                }
            }
            Step::Build(info, kind, count, escaped) => {
                let start = built
                    .len()
                    .checked_sub(count)
                    .ok_or("invalid template stack")?;
                let mut args = built.split_off(start);
                if escaped {
                    // The pin's unescapeAntiquot removes exactly one dollar.
                    // Do not revisit the resulting node: its capture belongs
                    // to the generated macro, while captures in its children
                    // have already been processed by this quotation.
                    let Syntax::Node { args: escapes, .. } = &mut args[1] else {
                        return Err("a malformed escaped antiquotation");
                    };
                    escapes.pop();
                }
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

fn instantiate_iteration_body(
    syntax: &Syntax,
    bound: &BTreeMap<&Name, &Syntax>,
    context: &Name,
    scope: u64,
    visited: &mut usize,
    raw: bool,
) -> Result<Syntax, &'static str> {
    charge(visited)?;
    match syntax {
        Syntax::Ident { val, .. } if bound.contains_key(val) => copy_capture(bound[val], visited),
        Syntax::Ident { .. } if raw => Ok(syntax.clone()),
        ident @ Syntax::Ident { val, .. } if val.is_anonymous() => Ok(ident.clone()),
        Syntax::Ident {
            info,
            raw_val,
            val,
            preresolved,
        } => Ok(Syntax::Ident {
            info: *info,
            raw_val: raw_val.clone(),
            val: fln_syntax::hygiene::add_macro_scope(context, val, scope)
                .map_err(|_| "a template name that cannot take a macro scope")?,
            preresolved: preresolved.clone(),
        }),
        Syntax::Node { info, kind, args } => {
            let mut built = Vec::with_capacity(args.len());
            for (index, child) in args.iter().enumerate() {
                built.push(instantiate_iteration_body(
                    child,
                    bound,
                    context,
                    scope,
                    visited,
                    raw_identifier_slot(kind, index),
                )?);
            }
            Ok(Syntax::Node {
                info: *info,
                kind: kind.clone(),
                args: built,
            })
        }
        leaf => Ok(leaf.clone()),
    }
}

pub(in crate::extensions) fn instantiate(
    rule: &NotationRule,
    args: &[Syntax],
    context: &Name,
    scope: u64,
) -> Result<Syntax, &'static str> {
    instantiate_rhs(rule, &rule.rhs, args, context, scope)
}

pub(in crate::extensions) fn instantiate_rhs(
    rule: &NotationRule,
    rhs: &Syntax,
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
        Iteration(repetition::Iteration<'a>),
        Build(SourceInfo, &'a Name, &'a [Syntax]),
    }
    let mut steps = vec![Step::Visit(rhs)];
    let mut built = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(syntax @ Syntax::Node { info, kind, args }) => {
                charge(&mut visited)?;
                if repetition::iteration(syntax)?.is_some() || repetition::suffix(syntax)?.is_some()
                {
                    return Err("a repetition splice outside its sequence");
                }
                steps.push(Step::Build(*info, kind, args));
                let sequence = null_args(syntax).is_some();
                for (index, child) in args.iter().enumerate().rev() {
                    if sequence
                        && let Some(part) = repetition::iteration(child)?
                        && repetition::suffix(child)?.is_none()
                    {
                        steps.push(Step::Iteration(part));
                    } else if sequence && let Some(part) = repetition::suffix(child)? {
                        steps.push(Step::Splice(part));
                    } else if raw_identifier_slot(kind, index) {
                        steps.push(Step::Raw(child));
                    } else {
                        steps.push(Step::Visit(child));
                    }
                }
            }
            Step::Iteration(iteration) => {
                let variables = iteration.body_variables(
                    |syntax| match syntax {
                        Syntax::Ident { val, .. } if bound.contains_key(val) => Some(val.clone()),
                        _ => None,
                    },
                    &mut visited,
                )?;
                let values = variables
                    .iter()
                    .map(|name| {
                        let value = bound
                            .get(name)
                            .map(AsRef::as_ref)
                            .ok_or("an unbound bracketed repetition capture")?;
                        iteration
                            .values(value, &mut visited)
                            .map(|items| (name, items))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(body) = null_args(iteration.body) else {
                    return Err("a bracketed template body outside a sequence");
                };
                if !iteration.is_optional() && body.len() != 1 {
                    return Err("a bracketed template iteration outside the single-body subset");
                }
                // Quotation.quoteSyntax zips all captured arrays before mapping
                // the body, so an empty or shorter capture truncates every one.
                // Optional captures have at most one element each: emit every
                // body node exactly when all options are present, otherwise none.
                let count = values
                    .iter()
                    .map(|(_, items)| items.len())
                    .min()
                    .ok_or("a bracketed template iteration without a bound capture")?;
                let mut elements = Vec::new();
                for index in 0..count {
                    let bindings = values
                        .iter()
                        .map(|(name, items)| {
                            charge(&mut visited)?;
                            Ok((*name, items[index]))
                        })
                        .collect::<Result<BTreeMap<_, _>, &'static str>>()?;
                    if index > 0
                        && let Some(separator) = iteration.separator()
                    {
                        charge(&mut visited)?;
                        let info = match iteration.suffix_node {
                            Syntax::Node { args, .. } => args
                                .get(1)
                                .and_then(|syntax| match syntax {
                                    Syntax::Atom { info, .. } => Some(*info),
                                    _ => None,
                                })
                                .unwrap_or(SourceInfo::None),
                            _ => SourceInfo::None,
                        };
                        elements.push(Syntax::atom(info, separator));
                    }
                    for part in body {
                        elements.push(instantiate_iteration_body(
                            part,
                            &bindings,
                            context,
                            scope,
                            &mut visited,
                            false,
                        )?);
                    }
                }
                built.push(null_node(elements));
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
                    raw_val: raw_val.clone(),
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
                        && (repetition::suffix(part)?.is_some()
                            || repetition::iteration(part)?.is_some())
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

    fn antiquot(name: &str) -> Syntax {
        Syntax::node(
            Name::from_components(["num", "antiquot"]),
            vec![
                Syntax::atom(SourceInfo::None, "$"),
                null_node(vec![]),
                synthetic_ident(Name::from_components([name])),
                null_node(vec![]),
            ],
        )
    }

    fn splice(name: &str) -> Syntax {
        Syntax::node(
            Name::from_components(["many", "antiquot_suffix_splice"]),
            vec![antiquot(name), Syntax::atom(SourceInfo::None, "*")],
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
            starts_registration: true,
            fallbacks: vec![],
        }
    }

    fn iteration_template(captures: Vec<Syntax>) -> Syntax {
        null_node(vec![Syntax::node(
            Name::from_components(["many", "antiquot_scope"]),
            vec![
                null_node(vec![Syntax::node(
                    Name::from_components(["pair"]),
                    captures,
                )]),
                Syntax::atom(SourceInfo::None, "*"),
            ],
        )])
    }

    fn zipped_rule() -> NotationRule {
        let variables = ["xs", "ys"]
            .into_iter()
            .enumerate()
            .map(|(index, name)| (vec![index], macro_variable(&Name::from_components([name]))))
            .collect::<Vec<_>>();
        let rhs = iteration_template(vec![antiquot("xs"), antiquot("ys")]);
        NotationRule {
            rhs: checked(&rhs, &variables).unwrap(),
            variables,
            prechecked: false,
            pattern: None,
            source: None,
            starts_registration: true,
            fallbacks: vec![],
        }
    }

    #[test]
    fn zipped_iterations_copy_nested_captures_without_extra_scopes() {
        let rule = zipped_rule();
        let xs = [
            Syntax::node(
                Name::from_components(["nested"]),
                vec![synthetic_ident(Name::from_components(["caller"]))],
            ),
            null_node(vec![Syntax::Missing]),
            Syntax::Missing,
        ];
        let ys = [Syntax::atom(SourceInfo::None, "first"), Syntax::Missing];
        let result = instantiate(
            &rule,
            &[null_node(xs.to_vec()), null_node(ys.to_vec())],
            &Name::from_components(["definition"]),
            9,
        )
        .unwrap();
        let expected = null_node(
            xs.iter()
                .zip(&ys)
                .map(|(x, y)| {
                    Syntax::node(Name::from_components(["pair"]), vec![x.clone(), y.clone()])
                })
                .collect(),
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn zipped_iterations_bound_all_capture_scans_and_duplicated_subtrees() {
        let rule = zipped_rule();
        for args in [
            [
                null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES / 2]),
                null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES / 2]),
            ],
            [
                null_node(vec![Syntax::node(
                    Name::from_components(["large"]),
                    vec![Syntax::Missing; MAX_TEMPLATE_NODES / 2],
                )]),
                null_node(vec![Syntax::node(
                    Name::from_components(["large"]),
                    vec![Syntax::Missing; MAX_TEMPLATE_NODES / 2],
                )]),
            ],
            [
                null_node(vec![]),
                null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES]),
            ],
        ] {
            let reason = instantiate(&rule, &args, &Name::anonymous(), 1).unwrap_err();
            assert!(reason.contains("budget"), "{reason}");
        }
        assert!(
            instantiate(
                &rule,
                &[null_node(vec![]), Syntax::Missing],
                &Name::anonymous(),
                1,
            )
            .is_err(),
            "an empty capture must not hide an invalid second binding"
        );
        assert_eq!(
            instantiate(
                &rule,
                &[null_node(vec![]), null_node(vec![Syntax::Missing])],
                &Name::anonymous(),
                1,
            )
            .unwrap(),
            null_node(vec![])
        );
    }

    #[test]
    fn duplicate_iteration_captures_refuse_during_checking_and_journal_replay() {
        let mut rule = zipped_rule();
        for names in [["xs", "xs"].as_slice(), ["xs", "ys", "xs"].as_slice()] {
            let rhs = iteration_template(names.iter().map(|name| antiquot(name)).collect());
            assert_eq!(
                checked(&rhs, &rule.variables),
                Err(repetition::DUPLICATE_ITERATION_CAPTURE)
            );
            // A journal can carry an already-compiled tree. Runtime validation
            // must retain the same rejection even if it bypasses `checked`.
            rule.rhs = replace_antiquotations(&rhs).unwrap();
            assert_eq!(
                instantiate(
                    &rule,
                    &[
                        null_node(vec![Syntax::Missing]),
                        null_node(vec![Syntax::Missing]),
                    ],
                    &Name::anonymous(),
                    1,
                ),
                Err(repetition::DUPLICATE_ITERATION_CAPTURE)
            );
        }
    }

    #[test]
    fn optional_iterations_emit_the_whole_body_only_when_every_capture_exists() {
        let mut rule = zipped_rule();
        let rhs = null_node(vec![Syntax::node(
            Name::from_components(["optional", "antiquot_scope"]),
            vec![
                null_node(vec![
                    Syntax::atom(SourceInfo::None, "value"),
                    Syntax::node(
                        Name::from_components(["pair"]),
                        vec![antiquot("xs"), antiquot("ys")],
                    ),
                ]),
                Syntax::atom(SourceInfo::None, "?"),
            ],
        )]);
        rule.rhs = checked(&rhs, &rule.variables).unwrap();
        let x = synthetic_ident(Name::from_components(["caller"]));
        let y = Syntax::atom(SourceInfo::None, "original");
        let some_x = null_node(vec![x.clone()]);
        let some_y = null_node(vec![y.clone()]);
        let none = null_node(vec![]);
        assert_eq!(
            instantiate(
                &rule,
                &[some_x.clone(), some_y.clone()],
                &Name::anonymous(),
                1
            )
            .unwrap(),
            null_node(vec![
                Syntax::atom(SourceInfo::None, "value"),
                Syntax::node(Name::from_components(["pair"]), vec![x, y]),
            ])
        );
        for args in [
            [none.clone(), some_y],
            [some_x, none.clone()],
            [none.clone(), none.clone()],
        ] {
            assert_eq!(
                instantiate(&rule, &args, &Name::anonymous(), 1).unwrap(),
                none
            );
        }
        for invalid in [Syntax::Missing, null_node(vec![Syntax::Missing; 2])] {
            assert!(
                instantiate(&rule, &[none.clone(), invalid], &Name::anonymous(), 1).is_err(),
                "an absent option must not hide an invalid second binding"
            );
        }
        let large = null_node(vec![Syntax::node(
            Name::from_components(["large"]),
            vec![Syntax::Missing; MAX_TEMPLATE_NODES],
        )]);
        assert!(
            instantiate(
                &rule,
                &[null_node(vec![Syntax::Missing]), large],
                &Name::anonymous(),
                1,
            )
            .unwrap_err()
            .contains("budget")
        );
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
    fn escaped_literal_framing_is_validated_and_charged() {
        let mut escaped = antiquot("future");
        let Syntax::Node { args, .. } = &mut escaped else {
            panic!("an antiquotation is a node");
        };
        args[1] = null_node(vec![Syntax::atom(SourceInfo::None, "$"); MAX_TEMPLATE_NODES]);
        assert!(checked(&escaped, &[]).unwrap_err().contains("budget"));
        assert!(
            super::super::variables(std::slice::from_ref(&escaped))
                .unwrap_err()
                .contains("budget")
        );
        for malformed in [
            null_node(vec![Syntax::Missing]),
            Syntax::node(
                Name::from_components(["antiquotName"]),
                vec![
                    Syntax::atom(SourceInfo::None, "?"),
                    Syntax::atom(SourceInfo::None, "num"),
                ],
            ),
        ] {
            let mut escaped = antiquot("future");
            let Syntax::Node { args, .. } = &mut escaped else {
                panic!("an antiquotation is a node");
            };
            args[1] = null_node(vec![Syntax::atom(SourceInfo::None, "$")]);
            args[3] = malformed;
            assert!(checked(&escaped, &[]).is_err());
            assert!(super::super::variables(std::slice::from_ref(&escaped)).is_err());
        }
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
