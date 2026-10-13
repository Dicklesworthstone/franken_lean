//! Value defaults follow the pin's `expandBinderModifier` and
//! `ElabAppArgs.processExplicitArg`. A default is an ordinary checked term
//! stored in `optParam`, not a side table or an unchecked elaborator value.
use super::*;
use fln_syntax::source::{ByteSpan, SourceInfo};

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

impl Context {
    /// Expand one already-rebuilt binder, using the ordinary application
    /// worklist to check both its type and its default. The global qualification
    /// has the pin's quotation hygiene: a local `optParam` cannot capture it.
    /// Tactic defaults retain their node and the existing explicit refusal;
    /// they need a quoted `Lean.Syntax` declaration, not an eager proof value.
    pub(super) fn expand_optional_binder_node(
        &mut self,
        mut syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if pattern || syntax.kind() != Some(&parser_kind(&["Term", "explicitBinder"])) {
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
        if modifier.kind() != Some(&parser_kind(&["Term", "binderDefault"])) {
            return Ok(syntax);
        }
        let modifier = expect_node(
            modifier,
            &parser_kind(&["Term", "binderDefault"]),
            2,
            "value binder default",
        )?;
        expect_atom(&modifier[0], ":=", "binder default assignment")?;
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
                    raw_val: ByteSpan::default(),
                    val: Name::from_components(["_root_", "optParam"]),
                    preresolved: Vec::new(),
                },
                null(vec![domain, modifier[1].clone()]),
            ],
        );
        let Syntax::Node { args, .. } = &mut syntax else {
            unreachable!("validated binder");
        };
        args[2] = null(vec![Syntax::atom(SourceInfo::None, ":"), annotation]);
        args[3] = null(Vec::new());
        Ok(syntax)
    }

    /// Look through the actual function telescope, opening dependent domains
    /// under fresh locals. This scan grants no unification assignment or
    /// declaration; all work remains charged to the calling transaction.
    pub(super) fn has_optional_parameter(
        &mut self,
        type_: &Expr,
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
                if default_value(binder_type).is_some() {
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
        // defaults, implicits and fresh eta binders without recursively
        // entering source elaboration.
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
