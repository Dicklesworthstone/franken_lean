//! Value defaults follow the pin's `expandBinderModifier` and
//! `ElabAppArgs.processExplicitArg`. A default is an ordinary checked term
//! stored in `optParam`, not a side table or an unchecked elaborator value.
use super::*;
use fln_syntax::source::{ByteSpan, SourceInfo};

mod quotation;
mod tactic;
pub(super) use tactic::AutoParameter;

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}

/// `Expr.getOptParamDefault?` is a syntactic observation. In particular, do
/// not unfold the parameter's domain and lose the annotation before reading it.
pub(super) fn default_value(domain: &Expr) -> Option<&Expr> {
    let ExprNode::App { f, a: value } = domain.node() else {
        return None;
    };
    let ExprNode::App { f, .. } = f.node() else {
        return None;
    };
    matches!(f.node(), ExprNode::Const { name, .. }
        if name == &Name::from_components(["optParam"]))
    .then_some(value)
}

/// `Expr.isAutoParam` is syntactic, matching `default_value` and `App.lean:472`.
pub(super) fn auto_tactic(domain: &Expr) -> Option<&Expr> {
    let ExprNode::App { f, a: tactic } = domain.node() else {
        return None;
    };
    let ExprNode::App { f, .. } = f.node() else {
        return None;
    };
    matches!(f.node(), ExprNode::Const { name, .. }
        if name == &Name::from_components(["autoParam"]))
    .then_some(tactic)
}

pub(super) fn is_auto_param(domain: &Expr) -> bool {
    auto_tactic(domain).is_some()
}

impl Context {
    /// Expand one already-rebuilt binder. The ordinary application worklist
    /// checks the annotation. Root qualification keeps a local optParam or
    /// autoParam from capturing the generated application, as at the pin.
    pub(super) fn expand_optional_binder_node(
        &mut self,
        mut syntax: Syntax,
        pattern: bool,
        allow_tactic: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if pattern {
            return Ok(syntax);
        }
        if syntax.kind() != Some(&parser_kind(&["Term", "explicitBinder"])) {
            return Ok(syntax);
        }
        self.tick()?;
        let parts = expect_node(
            &syntax,
            &parser_kind(&["Term", "explicitBinder"]),
            5,
            "explicit binder",
        )?;
        let modifier = expect_null_args(&parts[3], "optional binder modifier")?;
        let [modifier] = modifier else {
            return Ok(syntax);
        };
        let (annotation_name, value) =
            if modifier.kind() == Some(&parser_kind(&["Term", "binderDefault"])) {
                let modifier = expect_node(
                    modifier,
                    &parser_kind(&["Term", "binderDefault"]),
                    2,
                    "value binder default",
                )?;
                expect_atom(&modifier[0], ":=", "binder default assignment")?;
                ("optParam", modifier[1].clone())
            } else if modifier.kind() == Some(&parser_kind(&["Term", "binderTactic"])) {
                // Each name has its own quoted declaration at the pin. A
                // grouped binder is split by its enclosing null telescope.
                if !allow_tactic
                    || expect_null_args(&parts[1], "binder names")?.len() > 1
                    || (self.aux_names.is_none() && self.diagnostic_declaration.is_none())
                {
                    return Ok(syntax);
                }
                let modifier = expect_node(
                    modifier,
                    &parser_kind(&["Term", "binderTactic"]),
                    3,
                    "tactic binder default",
                )?;
                expect_atom(&modifier[0], ":=", "binder tactic assignment")?;
                expect_atom(&modifier[1], "by", "binder tactic introducer")?;
                let name = self.declare_auto_tactic(&modifier[2])?;
                (
                    "autoParam",
                    Syntax::Ident {
                        info: SourceInfo::None,
                        raw_val: ByteSpan::default().into(),
                        val: Name::from_components(["_root_"]).append_core(&name),
                        preresolved: Vec::new(),
                    },
                )
            } else {
                return Ok(syntax);
            };
        let type_parts = expect_null_args(&parts[2], "binder type")?;
        let domain = match type_parts {
            [] => Syntax::node(
                parser_kind(&["Term", "hole"]),
                vec![Syntax::atom(SourceInfo::None, "_")],
            ),
            [colon, domain] => {
                expect_atom(colon, ":", "binder type ascription")?;
                domain.clone()
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        let annotation = Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![
                Syntax::Ident {
                    info: SourceInfo::None,
                    raw_val: ByteSpan::default().into(),
                    val: Name::from_components(["_root_", annotation_name]),
                    preresolved: Vec::new(),
                },
                null(vec![domain, value]),
            ],
        );
        let Syntax::Node { args, .. } = &mut syntax else {
            unreachable!("validated binder");
        };
        args[2] = null(vec![Syntax::atom(SourceInfo::None, ":"), annotation]);
        args[3] = null(Vec::new());
        Ok(syntax)
    }

    /// elabBindersAux prepares one original bracket at a time. Its
    /// toBinderViews declares every grouped quote before elaborating any of
    /// those domains, while earlier brackets have already bound their locals.
    pub(super) fn declaration_binder_views(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Vec<Syntax>, NatDefinitionElabError> {
        let binder = self.copy_pattern_syntax(syntax)?;
        let grouped = self.expand_grouped_tactic_binders(null(vec![binder]))?;
        let Syntax::Node { args, .. } = grouped else {
            unreachable!("constructed null binder telescope");
        };
        let mut views = Vec::with_capacity(args.len());
        for binder in args {
            views.push(self.expand_optional_binder_node(binder, false, true)?);
        }
        Ok(views)
    }

    /// toBinderViews expands the modifier separately for every identifier.
    /// Splitting only grouped tactic binders leaves ordinary binder elaboration
    /// intact while giving each quote the same auxiliary identity as the pin.
    fn expand_grouped_tactic_binders(
        &mut self,
        mut syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let Syntax::Node { args, .. } = &mut syntax else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut expanded = Vec::with_capacity(args.len());
        for binder in std::mem::take(args) {
            self.tick()?;
            let split = match &binder {
                Syntax::Node { kind, args, .. }
                    if kind == &parser_kind(&["Term", "explicitBinder"]) && args.len() == 5 =>
                {
                    let modifier = expect_null_args(&args[3], "optional binder modifier")?;
                    matches!(modifier, [modifier]
                        if modifier.kind() == Some(&parser_kind(&["Term", "binderTactic"])))
                        && expect_null_args(&args[1], "binder names")?.len() > 1
                }
                _ => false,
            };
            if !split {
                expanded.push(binder);
                continue;
            }
            let Syntax::Node { args: parts, .. } = &binder else {
                unreachable!("validated explicit binder");
            };
            for identifier in expect_null_args(&parts[1], "binder names")? {
                let mut single = self.copy_pattern_syntax(&binder)?;
                let Syntax::Node { args, .. } = &mut single else {
                    unreachable!("copied explicit binder");
                };
                args[1] = null(vec![identifier.clone()]);
                expanded.push(single);
            }
        }
        *args = expanded;
        Ok(syntax)
    }

    /// Look through the actual function telescope, opening dependent domains
    /// under fresh locals. This scan grants no unification assignment or
    /// declaration; all work remains charged to the calling transaction.
    pub(super) fn has_optional_parameter(
        &mut self,
        type_: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.has_optional_parameter_with(type_, true)
    }

    /// `hasOptAutoParams` (`Lean/Elab/App.lean:484`): like
    /// `has_optional_parameter`, recognizing both annotation forms when
    /// deciding whether early expected-type propagation must postpone.
    pub(super) fn has_optional_or_auto_parameter(
        &mut self,
        type_: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.has_optional_parameter_with(type_, true)
    }

    fn has_optional_parameter_with(
        &mut self,
        type_: &Expr,
        include_auto: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut cursor = type_.clone();
            loop {
                self.tick()?;
                let reduced = self.whnf(&cursor)?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = reduced.node()
                else {
                    return Ok(false);
                };
                if default_value(binder_type).is_some()
                    || (include_auto && is_auto_param(binder_type))
                {
                    return Ok(true);
                }
                let id = FVarId(self.fresh_name()?);
                let name = self.fresh_name()?;
                self.txn
                    .lctx
                    .add_param(id.clone(), name, binder_type.clone(), *binder_info);
                cursor = self.substitute(body, &Expr::fvar(id))?;
            }
        })();
        self.txn.lctx = saved;
        result
    }

    /// A bare identifier uses the application's default machinery, while
    /// lambda construction retains its own complete function telescope.
    pub(super) fn finish_optional_term(
        &mut self,
        term: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if self.has_optional_parameter(&term.type_)? {
            self.finish_optional_application(term, expected)
        } else {
            self.finish_term(term, expected)
        }
    }

    pub(super) fn finish_optional_application(
        &mut self,
        term: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let mut state = self.start_named_application(term, &[], expected.cloned(), false)?;
        // There are no written arguments. The common telescope loop supplies
        // defaults, implicits and fresh eta binders. Quoted tactic defaults
        // run at application completion, after its type constraints are known.
        let result = (|| {
            if self.next_named_argument(&mut state)?.is_some() {
                return Err(failure(SourceInferenceError::Scope));
            }
            self.finish_named_application(state)
        })();
        self.txn.lctx = saved;
        result
    }
}
