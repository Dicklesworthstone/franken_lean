//! Definition patterns are normalized only from admitted `[match_pattern]`
//! targets. Fresh symbolic arguments retain source patterns through beta,
//! delta, let, projection and recursor reduction. The resulting constructor
//! tree is compiled by the ordinary checked matrix backend; original rows
//! separately retain their type obligations.
use super::*;
use fln_env::constants::DefinitionVal;
use std::collections::BTreeSet;

pub(in crate::source) fn unsupported(reason: &'static str) -> NatDefinitionElabError {
    failure(SourceInferenceError::Match(
        matching::MatchError::UnsupportedDefinitionPattern(reason),
    ))
}

pub(in crate::source) fn hole(syntax: &Syntax) -> bool {
    matches!(syntax.kind(), Some(kind)
        if kind == &parser_kind(&["Term", "hole"])
            || kind == &parser_kind(&["Term", "syntheticHole"]))
}

/// Syntax labels, type annotations and application heads are not pattern
/// variables. Only their value positions are traversed or rewritten.
fn child_is_pattern(kind: &Name, index: usize) -> bool {
    if kind == &parser_kind(&["Term", "app"]) {
        index == 1
    } else if kind == &parser_kind(&["Term", "namedArgument"])
        || kind == &parser_kind(&["Term", "namedPattern"])
    {
        index == 3
    } else if kind == &parser_kind(&["Term", "paren"])
        || kind == &parser_kind(&["Term", "typeAscription"])
        || kind == &parser_kind(&["Term", "structInstField"])
        || kind == &parser_kind(&["Term", "matchAlt"])
    {
        index == 1
    } else if kind == &parser_kind(&["Term", "structInst"])
        || kind == &parser_kind(&["Term", "structInstFieldDef"])
    {
        index == 2
    } else {
        !["dotIdent", "explicitUniv", "inaccessible", "structInstLVal"]
            .iter()
            .any(|label| kind == &parser_kind(&["Term", label]))
    }
}

pub(in crate::source) fn application_parts(
    syntax: &Syntax,
) -> Result<(&Syntax, Vec<&Syntax>, bool), NatDefinitionElabError> {
    let (mut head, arguments) = if syntax.kind() == Some(&parser_kind(&["Term", "app"])) {
        let [head, arguments] = expect_node(
            syntax,
            &parser_kind(&["Term", "app"]),
            2,
            "definition pattern application",
        )?
        else {
            return Err(invalid());
        };
        (
            head,
            expect_null_args(arguments, "definition pattern arguments")?
                .iter()
                .collect(),
        )
    } else {
        (syntax, Vec::new())
    };
    while let Some(inner) = parenthesized_inner(head)? {
        head = inner;
    }
    let explicit = head.kind() == Some(&parser_kind(&["Term", "explicit"]));
    if explicit {
        let [at, inner] = expect_node(
            head,
            &parser_kind(&["Term", "explicit"]),
            2,
            "explicit definition pattern",
        )?
        else {
            return Err(invalid());
        };
        expect_atom(at, "@", "explicit definition pattern")?;
        head = inner;
    }
    Ok((head, arguments, explicit))
}

struct Symbol {
    source: Option<Syntax>,
    accessible: bool,
    used: bool,
}

impl Context {
    pub(in crate::source) fn pattern_definition(
        &mut self,
        name: &Name,
    ) -> Result<Option<DefinitionVal>, NatDefinitionElabError> {
        let tags = crate::match_pattern::read(&self.txn.env)
            .map_err(scope::executable::match_pattern_error)?;
        self.pattern_definition_in(name, &tags)
    }

    fn pattern_definition_in(
        &mut self,
        name: &Name,
        tags: &BTreeSet<Name>,
    ) -> Result<Option<DefinitionVal>, NatDefinitionElabError> {
        if !tags.contains(name) {
            return Ok(None);
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name) else {
            return Err(unsupported(
                "a match_pattern body is not exposed in this environment",
            ));
        };
        if definition.safety != DefinitionSafety::Safe {
            return Err(unsupported(
                "unsafe or partial definitions cannot be unfolded as patterns",
            ));
        }
        let reducibility = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        if reducibility.status(name) == crate::reducibility::Reducibility::Irreducible {
            return Err(unsupported(
                "an irreducible definition remains inaccessible in source patterns",
            ));
        }
        Ok(Some(definition.clone()))
    }

    pub(in crate::source) fn has_definition_patterns(
        &mut self,
        syntax: &[Syntax],
    ) -> Result<bool, NatDefinitionElabError> {
        let tags = crate::match_pattern::read(&self.txn.env)
            .map_err(scope::executable::match_pattern_error)?;
        if tags.is_empty() {
            return Ok(false);
        }
        let mut pending: Vec<_> = syntax.iter().collect();
        while let Some(syntax) = pending.pop() {
            self.tick()?;
            let (head, _, _) = application_parts(syntax)?;
            if matches!(head, Syntax::Ident { .. }) {
                let (resolved, _) = self.resolve_unambiguous_identifier_name(head)?;
                if resolved.is_some_and(|name| tags.contains(&name)) {
                    return Ok(true);
                }
            }
            if let Syntax::Node { kind, args, .. } = syntax {
                pending.extend(
                    args.iter()
                        .enumerate()
                        .filter_map(|(i, arg)| child_is_pattern(kind, i).then_some(arg)),
                );
            }
        }
        Ok(false)
    }

    pub(super) fn expand_definition_pattern_row(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Syntax>, NatDefinitionElabError> {
        let tags = crate::match_pattern::read(&self.txn.env)
            .map_err(scope::executable::match_pattern_error)?;
        if tags.is_empty() {
            return Ok(None);
        }
        enum Task {
            Visit(Syntax, bool),
            Build(SourceInfo, Name, usize),
        }
        let mut pending = vec![Task::Visit(self.copy_pattern_syntax(syntax)?, true)];
        let mut values = Vec::new();
        let mut changed = false;
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Visit(syntax, false) => values.push(syntax),
                Task::Visit(mut syntax, true) => {
                    let (head, arguments, explicit) = application_parts(&syntax)?;
                    if matches!(head, Syntax::Ident { .. }) {
                        let (name, _) = self.resolve_unambiguous_identifier_name(head)?;
                        if let Some(name) = name
                            && let Some(definition) = self.pattern_definition_in(&name, &tags)?
                        {
                            let expanded = self.expand_definition_pattern(
                                &definition,
                                &arguments,
                                explicit,
                                &tags,
                            )?;
                            changed = true;
                            pending.push(Task::Visit(expanded, true));
                            continue;
                        }
                    }
                    if let Syntax::Node { info, kind, args } = &mut syntax {
                        let (info, kind, args) = (*info, kind.clone(), std::mem::take(args));
                        pending.push(Task::Build(info, kind.clone(), values.len()));
                        pending.extend(
                            args.into_iter()
                                .enumerate()
                                .rev()
                                .map(|(i, arg)| Task::Visit(arg, child_is_pattern(&kind, i))),
                        );
                    } else {
                        values.push(syntax);
                    }
                }
                Task::Build(info, kind, start) => {
                    let args = values.split_off(start);
                    values.push(Syntax::Node { info, kind, args });
                }
            }
        }
        let value = values.pop().ok_or_else(invalid)?;
        Ok(changed.then_some(value))
    }

    fn definition_pattern_whnf(
        &mut self,
        expression: &Expr,
        tags: &BTreeSet<Name>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut expression = expression.clone();
        loop {
            self.tick()?;
            // Reduction is speculative and cannot assign caller metavariables.
            // Synthetic arguments are neutral, just as in pattern_typing.
            let mut trial = self.clone();
            let reduced =
                trial.whnf_with_transparency(&expression, UnificationTransparency::Default, false);
            self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            expression = reduced?;
            let (head, arguments) = operators::spine(&expression);
            let ExprNode::Const { name, levels } = head.node() else {
                return Ok(expression);
            };
            let Some(definition) = self.pattern_definition_in(name, tags)? else {
                return Ok(expression);
            };
            if levels.len() != definition.base.level_params.len() {
                return Err(invalid());
            }
            let mut value =
                self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
            for argument in arguments {
                self.tick()?;
                value = Expr::app(value, argument.clone());
            }
            if value == expression {
                return Err(unsupported(
                    "a tagged definition does not expose a constructor pattern",
                ));
            }
            expression = value;
        }
    }

    fn expand_definition_pattern(
        &mut self,
        definition: &DefinitionVal,
        arguments: &[&Syntax],
        explicit: bool,
        tags: &BTreeSet<Name>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let arguments =
            arguments::normalize_telescope(self, arguments, &definition.base.type_, explicit)?;
        let mut symbols = HashMap::new();
        let mut type_ = definition.base.type_.clone();
        let mut value = definition.value.clone();
        for argument in arguments {
            self.tick()?;
            let ExprNode::ForallE {
                binder_info,
                binder_type,
                body,
                ..
            } = type_.node()
            else {
                return Err(invalid());
            };
            let accessible = *binder_info == BinderInfo::Default;
            // A closed Nat argument may drive a recursor (Nat.add n 1). Only
            // the admitted binder type permits literal evaluation; other
            // overloaded numerals remain source patterns with their types.
            let natural = argument.and_then(|syntax| {
                if syntax.kind() != Some(&Name::from_components(["num"])) {
                    return None;
                }
                let Syntax::Node { args, .. } = syntax else {
                    return None;
                };
                let [Syntax::Atom { val, .. }] = args.as_slice() else {
                    return None;
                };
                decode_natural(val).ok()
            });
            let natural = if natural.is_some()
                && self.definition_pattern_whnf(binder_type, tags)? == nat_const()
            {
                natural
            } else {
                None
            };
            let expression = if let Some(natural) = natural {
                Expr::lit(natural)
            } else {
                let id = FVarId(self.fresh_name()?);
                symbols.insert(
                    id.clone(),
                    Symbol {
                        source: argument
                            .map(|syntax| self.copy_pattern_syntax(syntax))
                            .transpose()?,
                        accessible,
                        used: false,
                    },
                );
                Expr::fvar(id)
            };
            type_ = self.substitute(&body.clone(), &expression)?;
            value = Expr::app(value, expression);
        }
        enum Task {
            Visit(Expr, bool),
            Constructor(Name, Vec<Option<Name>>, usize),
        }
        let mut pending = vec![Task::Visit(value, false)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Constructor(name, labels, start) => {
                    let fields = values
                        .split_off(start)
                        .into_iter()
                        .zip(labels)
                        .map(|(value, label)| arguments::argument(&label, value))
                        .collect::<Vec<_>>();
                    let head = identifier(Name::from_components(["_root_"]).append_core(&name));
                    values.push(if fields.is_empty() {
                        head
                    } else {
                        Syntax::node(parser_kind(&["Term", "app"]), vec![head, null(fields)])
                    });
                }
                Task::Visit(value, inferred) => {
                    let value = self.definition_pattern_whnf(&value, tags)?;
                    if let ExprNode::FVar { id } = value.node() {
                        let symbol = symbols.get_mut(id).ok_or_else(|| {
                            unsupported("a definition pattern contains an unrelated free variable")
                        })?;
                        if symbol.used {
                            return Err(unsupported(
                                "repeated symbolic definition-pattern arguments require a shared field constraint",
                            ));
                        }
                        symbol.used = true;
                        if !symbol.accessible {
                            if inferred {
                                if symbol.source.as_ref().is_some_and(|syntax| !hole(syntax)) {
                                    return Err(unsupported(
                                        "a supplied implicit definition-pattern value must retain its index constraint",
                                    ));
                                }
                                // Constructor indices determine this field
                                // (e.g. Eq.refl's value in Prelude.rfl). Keep an
                                // inference hole, never a new source binding.
                                values.push(wildcard());
                                continue;
                            }
                            return Err(unsupported(
                                "an inferred implicit argument remains in an accessible pattern field",
                            ));
                        }
                        values.push(match &symbol.source {
                            Some(source) => self.copy_pattern_syntax(source)?,
                            None => wildcard(),
                        });
                        continue;
                    }
                    if let ExprNode::Lit {
                        literal: Literal::Nat(natural),
                    } = value.node()
                    {
                        values.push(self.finite_literal_syntax(natural)?);
                        continue;
                    }
                    if let ExprNode::Lit {
                        literal: Literal::Str(text),
                    } = value.node()
                    {
                        let mut spelling = String::from("\"");
                        for character in text.chars() {
                            self.tick()?;
                            match character {
                                '\\' => spelling.push_str("\\\\"),
                                '"' => spelling.push_str("\\\""),
                                '\n' => spelling.push_str("\\n"),
                                '\r' => spelling.push_str("\\r"),
                                '\t' => spelling.push_str("\\t"),
                                c if c.is_control() => {
                                    use std::fmt::Write;
                                    write!(&mut spelling, "\\u{:04x}", u32::from(c))
                                        .expect("String write");
                                }
                                c => spelling.push(c),
                            }
                        }
                        spelling.push('"');
                        values.push(Syntax::node(
                            Name::from_components(["str"]),
                            vec![atom(&spelling)],
                        ));
                        continue;
                    }
                    let (head, arguments) = operators::spine(&value);
                    let ExprNode::Const { name, .. } = head.node() else {
                        return Err(unsupported(
                            "a tagged definition does not reduce to a constructor or literal pattern",
                        ));
                    };
                    let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name).cloned()
                    else {
                        return Err(unsupported(
                            "a tagged definition is stuck before exposing a constructor pattern",
                        ));
                    };
                    if arguments.len()
                        != constructor.num_params as usize + constructor.num_fields as usize
                    {
                        return Err(invalid());
                    }
                    let determined =
                        self.definition_pattern_indices(&constructor.base.type_, arguments.len())?;
                    let mut type_ = constructor.base.type_.clone();
                    let mut labels = Vec::new();
                    let mut fields = Vec::new();
                    for (index, argument) in arguments.into_iter().enumerate() {
                        self.tick()?;
                        let ExprNode::ForallE {
                            binder_name,
                            binder_info,
                            body,
                            ..
                        } = type_.node()
                        else {
                            return Err(invalid());
                        };
                        if index < constructor.num_params as usize {
                            if *binder_info == BinderInfo::Default {
                                let id = FVarId(self.fresh_name()?);
                                symbols.insert(
                                    id.clone(),
                                    Symbol {
                                        source: None,
                                        accessible: true,
                                        used: false,
                                    },
                                );
                                labels.push(None);
                                fields.push((Expr::fvar(id), false));
                            }
                        } else {
                            labels.push(
                                (*binder_info != BinderInfo::Default).then(|| binder_name.clone()),
                            );
                            fields.push((argument.clone(), inferred || determined[index]));
                        }
                        type_ = body.clone();
                    }
                    pending.push(Task::Constructor(name.clone(), labels, values.len()));
                    pending.extend(
                        fields
                            .into_iter()
                            .rev()
                            .map(|(value, inferred)| Task::Visit(value, inferred)),
                    );
                }
            }
        }
        for symbol in symbols
            .values()
            .filter(|symbol| symbol.accessible && !symbol.used)
        {
            let Some(source) = symbol.source.as_ref().filter(|source| !hole(source)) else {
                continue;
            };
            // Discarding a constant or wildcard loses no source binding. Its
            // original parameter type is still replayed. A discarded variable
            // is forbidden even when the branch never references it.
            if self.has_definition_patterns(std::slice::from_ref(source))? {
                return Err(unsupported(
                    "an erased nested definition pattern requires original binder collection",
                ));
            }
            let mut arena = vec![Pattern::Bind(None)];
            self.matrix_pattern(source, &mut arena)?;
            if arena
                .iter()
                .any(|pattern| matches!(pattern, Pattern::Bind(Some(_)) | Pattern::Named { .. }))
            {
                return Err(failure(SourceInferenceError::Match(
                    matching::MatchError::InaccessiblePatternVariable,
                )));
            }
        }
        values.pop().ok_or_else(invalid)
    }

    /// Fields occurring in the constructor's result are determined by its
    /// indices. Only these may retain an inferred implicit alias argument.
    /// The original-pattern replay still has to solve the actual type equation.
    fn definition_pattern_indices(
        &mut self,
        type_: &Expr,
        count: usize,
    ) -> Result<Vec<bool>, NatDefinitionElabError> {
        let mut result = type_;
        for _ in 0..count {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = result.node() else {
                return Err(invalid());
            };
            result = body;
        }
        let mut determined = vec![false; count];
        let mut pending = vec![(result, 0usize)];
        while let Some((expr, depth)) = pending.pop() {
            self.tick()?;
            match expr.node() {
                ExprNode::BVar { idx } => {
                    if let Some(index) = (*idx as usize).checked_sub(depth)
                        && index < count
                    {
                        determined[count - index - 1] = true;
                    }
                }
                ExprNode::App { f, a } => pending.extend([(f, depth), (a, depth)]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    pending.push((binder_type, depth));
                    pending.push((
                        body,
                        depth
                            .checked_add(1)
                            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?,
                    ));
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    pending.extend([(type_, depth), (value, depth)]);
                    pending.push((
                        body,
                        depth
                            .checked_add(1)
                            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?,
                    ));
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    pending.push((expr, depth))
                }
                _ => {}
            }
        }
        Ok(determined)
    }
}
