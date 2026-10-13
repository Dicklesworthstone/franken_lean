//! Put an application context inside a structural recursor's minor premises.
//!
//! `C[match n with ...]` cannot reuse the inner match's induction hypothesis:
//! the recursive name denotes the result of the whole `C[...]`. Compile the
//! surrounding core expression once, then replace every root minor `b` by an
//! application of that same typed context. The
//! matrix's constructor fields have private numeric names; source pattern
//! aliases remain scoped inside `b`, so they cannot capture names in `C`.
//! Only binder-free application/operator/parenthesis contexts commute here.
//! The existing recursion compiler still checks every actual recursive call.
use super::*;

#[derive(Clone)]
pub(super) struct Capture {
    local: LocalDecl,
    source: Typed,
}

pub(super) struct Build {
    pub(super) helper: LocalDecl,
    pub(super) obligation: Typed,
    arguments: Vec<Name>,
}

fn identifier(name: Name) -> Syntax {
    Syntax::Ident {
        info: fln_syntax::source::SourceInfo::None,
        raw_val: fln_syntax::source::ByteSpan::default(),
        val: name,
        preresolved: Vec::new(),
    }
}

impl Context {
    /// Preserve the selected match as a checked local definition while the
    /// ordinary term driver elaborates its surrounding application. Its actual
    /// value remains available for dependent conversion and instance selection.
    pub(in crate::source) fn capture_recursive_context(
        &mut self,
        source: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        if !self
            .recursion
            .as_ref()
            .is_some_and(|recursion| !recursion.pending && recursion.contextual_capture.is_none())
        {
            return Err(failure(SourceInferenceError::Scope));
        }
        let id = FVarId(self.fresh_name()?);
        self.txn.lctx.add_let(
            id.clone(),
            Name::anonymous(),
            source.type_.clone(),
            source.value.clone(),
        );
        let local = self
            .txn
            .lctx
            .find(&id)
            .expect("captured contextual match")
            .clone();
        self.recursion
            .as_mut()
            .expect("contextual recursion")
            .contextual_capture = Some(Capture {
            local,
            source: source.clone(),
        });
        Ok(Typed {
            value: Expr::fvar(id),
            type_: source.type_,
        })
    }

    /// Elaborate the surrounding application exactly once, retaining its actual
    /// implicit arguments, instances and coercions in a checked core lambda.
    /// Merely copying source context could choose different valid overloads in
    /// different branches. A separate original-body lambda obligation preserves
    /// typing of the selected match before structural lowering as well.
    pub(super) fn prepare_contextual_recursion(
        &mut self,
        syntax: &Syntax,
        path: &[usize],
        expected: Option<Expr>,
    ) -> Result<Build, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("prepared contextual recursion");
        let saved = self.txn.lctx.clone();
        self.recursion
            .as_mut()
            .expect("prepared contextual recursion")
            .pending = false;
        let mut selected = syntax;
        for &index in path {
            self.tick()?;
            let Syntax::Node { args, .. } = selected else {
                return Err(failure(SourceInferenceError::Scope));
            };
            selected = args
                .get(index)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        }
        let selected = self.copy_pattern_syntax(selected)?;
        let capture = Syntax::node(
            parser_kind(&["Term", "recursiveContextCapture"]),
            vec![selected],
        );
        let marked = self.fill_recursive_context(syntax, path, capture)?;
        let original = self.term(&marked, expected)?;
        self.resolve_instances_with_defaults()?;
        self.flush(true)?;
        let capture = self
            .recursion
            .as_mut()
            .expect("contextual recursion")
            .contextual_capture
            .take()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        self.recursion = Some(recursion.clone());
        let original_value = self.instantiate(&original.value)?;
        let original_type = self.instantiate(&original.type_)?;
        let slot_type = self.instantiate(&capture.local.type_)?;
        let slot_value = self.instantiate(&capture.source.value)?;
        let context_body = original_value
            .abstract_fvar(&capture.local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let context_type = original_type
            .abstract_fvar(&capture.local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let witness_type = self.substitute(&context_type, &slot_value)?;
        let witness = Expr::let_e(
            Name::anonymous(),
            slot_type.clone(),
            slot_value,
            context_body.clone(),
            false,
        );
        let value = witness
            .abstract_fvar(&recursion.marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let type_ = witness_type
            .abstract_fvar(&recursion.marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let domain = self.instantiate(&recursion.reference.type_)?;
        let obligation = Typed {
            value: Expr::lam(
                Name::anonymous(),
                domain.clone(),
                value,
                BinderInfo::Default,
            ),
            type_: Expr::forall_e(Name::anonymous(), domain, type_, BinderInfo::Default),
        };
        let mut helper_value = Expr::lam(
            Name::anonymous(),
            slot_type.clone(),
            context_body,
            BinderInfo::Default,
        );
        let mut helper_type = Expr::forall_e(
            Name::anonymous(),
            slot_type,
            context_type,
            BinderInfo::Default,
        );
        // If reduction in the surrounding context re-exposes a recursive call,
        // it is no longer confined to the selected match's hypotheses.
        if self
            .elimination_reads(&helper_value)?
            .contains(&recursion.marker)
            || self
                .elimination_reads(&helper_type)?
                .contains(&recursion.marker)
        {
            return Err(error(RecursionError::NotDecreasing));
        }
        let mut arguments = Vec::new();
        for parameter in recursion.parameters.iter().rev() {
            self.tick()?;
            if parameter.user_name.is_anonymous() {
                if self
                    .elimination_reads(&helper_value)?
                    .contains(&parameter.id)
                    || self
                        .elimination_reads(&helper_type)?
                        .contains(&parameter.id)
                {
                    return Err(error(RecursionError::RootMatchRequired));
                }
                continue;
            }
            let domain = self.instantiate(&parameter.type_)?;
            helper_value = Expr::lam(
                parameter.user_name.clone(),
                domain.clone(),
                helper_value
                    .abstract_fvar(&parameter.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
            helper_type = Expr::forall_e(
                parameter.user_name.clone(),
                domain,
                helper_type
                    .abstract_fvar(&parameter.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
            arguments.push(parameter.user_name.clone());
        }
        arguments.reverse();
        self.txn.lctx = saved;
        let serial = self.next;
        let id = FVarId(self.fresh_name()?);
        let name = Name::num(Name::anonymous(), serial);
        self.txn
            .lctx
            .add_let(id.clone(), name, helper_type, helper_value);
        let helper = self
            .txn
            .lctx
            .find(&id)
            .expect("typed recursive context helper")
            .clone();
        Ok(Build {
            helper,
            obligation,
            arguments,
        })
    }

    pub(super) fn contextual_recursive_match<'a>(
        &mut self,
        parameters: &[LocalDecl],
        syntax: &'a Syntax,
    ) -> Result<(&'a Syntax, Vec<usize>), NatDefinitionElabError> {
        let mut root = syntax;
        while let Some(inner) = parenthesized_inner(root)? {
            self.tick()?;
            root = inner;
        }
        if root.kind() == Some(&parser_kind(&["Term", "match"])) {
            return Ok((syntax, Vec::new()));
        }
        let mut pending = vec![(syntax, Vec::new())];
        while let Some((node, path)) = pending.pop() {
            self.tick()?;
            if node.kind() == Some(&parser_kind(&["Term", "match"])) {
                if !self.recursion_columns(parameters, node)?.is_empty() {
                    return Ok((node, path));
                }
                // Do not discover a different lexical owner in a match branch.
                continue;
            }
            let Syntax::Node { kind, args, .. } = node else {
                continue;
            };
            if let Some(inner) = parenthesized_inner(node)? {
                let index = args
                    .iter()
                    .position(|arg| std::ptr::eq(arg, inner))
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                let mut path = path;
                path.push(index);
                pending.push((inner, path));
            } else if kind == &parser_kind(&["Term", "app"])
                || kind == &Name::from_components(["null"])
                || operators::pin_notation(kind).is_some()
                || bounded_infix_intrinsic(kind, true).is_some()
            {
                for (index, child) in args.iter().enumerate().rev() {
                    self.tick()?;
                    // Account for path copies as well as visited syntax. No
                    // recursive host walk or unmetered quadratic construction.
                    for _ in &path {
                        self.tick()?;
                    }
                    let mut child_path = path.clone();
                    child_path.push(index);
                    pending.push((child, child_path));
                }
            }
        }
        Err(error(RecursionError::RootMatchRequired))
    }

    pub(super) fn distribute_recursive_context(
        &mut self,
        selected: &Syntax,
        column: usize,
        build: &Build,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut required = Vec::new();
        let mut matrix = self.compile_pattern_matrix(selected, &mut required, Some(column))?;
        self.recursion
            .as_mut()
            .expect("prepared contextual recursion")
            .matrix = true;
        let Syntax::Node { kind, args, .. } = &mut matrix else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if kind != &parser_kind(&["Term", "matchMatrix"]) || args.len() != 6 {
            return Err(error(RecursionError::RootMatchRequired));
        }
        let Syntax::Node {
            args: alternatives, ..
        } = &mut args[5]
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let [
            Syntax::Node {
                args: alternatives, ..
            },
        ] = alternatives.as_mut_slice()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        for alternative in alternatives {
            self.tick()?;
            let Syntax::Node { args, .. } = alternative else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if args.len() != 4 {
                return Err(failure(SourceInferenceError::Scope));
            }
            let branch = std::mem::replace(&mut args[3], Syntax::Missing);
            let mut arguments = Vec::new();
            for name in &build.arguments {
                self.tick()?;
                arguments.push(identifier(name.clone()));
            }
            arguments.push(branch);
            args[3] = Syntax::node(
                parser_kind(&["Term", "app"]),
                vec![
                    identifier(build.helper.user_name.clone()),
                    Syntax::node(Name::from_components(["null"]), arguments),
                ],
            );
        }
        Ok(Syntax::node(
            parser_kind(&["Term", "matrixScope"]),
            vec![
                Syntax::node(
                    Name::from_components(["null"]),
                    required
                        .into_iter()
                        .map(|name| Syntax::Ident {
                            info: fln_syntax::source::SourceInfo::None,
                            raw_val: fln_syntax::source::ByteSpan::default(),
                            val: name,
                            preresolved: Vec::new(),
                        })
                        .collect(),
                ),
                matrix,
            ],
        ))
    }

    fn fill_recursive_context(
        &mut self,
        whole: &Syntax,
        path: &[usize],
        mut body: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut ancestors = Vec::new();
        let mut node = whole;
        for &index in path {
            self.tick()?;
            let Syntax::Node { info, kind, args } = node else {
                return Err(failure(SourceInferenceError::Scope));
            };
            ancestors.push((*info, kind, args, index));
            node = args
                .get(index)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        }
        for (info, kind, args, replaced) in ancestors.into_iter().rev() {
            self.tick()?;
            let mut children = Vec::with_capacity(args.len());
            let mut replacement = Some(body);
            for (index, child) in args.iter().enumerate() {
                self.tick()?;
                children.push(if index == replaced {
                    replacement.take().expect("one contextual match slot")
                } else {
                    self.copy_pattern_syntax(child)?
                });
            }
            body = Syntax::Node {
                info,
                kind: kind.clone(),
                args: children,
            };
        }
        Ok(body)
    }
}
