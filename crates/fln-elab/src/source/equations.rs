//! Equation-style declarations use the existing typed pattern-matrix compiler.
//!
//! Open the declared function telescope before choosing any branch. Hidden
//! binders retain their binder information; pattern columns consume explicit
//! binders only. Original alternative syntax is retained, and generated names
//! are not source identifier spellings. The resulting root match participates
//! in the ordinary structural-recursion and declaration-admission paths.
use super::*;
use fln_syntax::source::{ByteSpan, SourceInfo};

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}
fn atom(value: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, value)
}
fn ident(name: Name) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        val: name,
        preresolved: Vec::new(),
    }
}

impl Context {
    /// Produce a typed header plus an ordinary source match, without source
    /// reparsing or using constructors to guess missing argument types.
    pub(super) fn equation_function(
        &mut self,
        alternatives: &Syntax,
        declared_type: &Expr,
        parameters: &mut Vec<LocalDecl>,
    ) -> Result<(Syntax, Expr), NatDefinitionElabError> {
        let parts = expect_node(
            alternatives,
            &parser_kind(&["Term", "matchAlts"]),
            1,
            "equation alternatives",
        )?;
        let rows = expect_null_args(&parts[0], "equation rows")?;
        let mut arity = None;
        for row in rows {
            self.tick()?;
            let row = expect_node(row, &parser_kind(&["Term", "matchAlt"]), 4, "equation")?;
            expect_atom(&row[0], "|", "equation pipe")?;
            expect_atom(&row[2], "=>", "equation arrow")?;
            let [patterns] = expect_null_args(&row[1], "equation patterns")? else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let patterns = expect_null_args(patterns, "equation columns")?;
            if patterns.is_empty() || patterns.len() % 2 == 0 {
                return Err(failure(SourceInferenceError::Scope));
            }
            for comma in patterns.iter().skip(1).step_by(2) {
                self.tick()?;
                expect_atom(comma, ",", "equation separator")?;
            }
            let count = patterns.len().div_ceil(2);
            if arity
                .replace(count)
                .is_some_and(|previous| previous != count)
            {
                return Err(failure(SourceInferenceError::Scope));
            }
        }
        let arity = arity.ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let mut explicit = 0;
        let mut result_type = declared_type.clone();
        let mut discriminants = Vec::new();
        while explicit < arity {
            self.tick()?;
            let ty = self.whnf(&result_type)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = ty.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            if *binder_info == BinderInfo::InstImplicit {
                self.validate_instance_binder(binder_type)?;
            }
            let serial = self.next;
            let id = FVarId(self.fresh_name()?);
            let name = Name::num(Name::anonymous(), serial);
            self.txn
                .lctx
                .add_param(id.clone(), name.clone(), binder_type.clone(), *binder_info);
            parameters.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("inserted equation parameter")
                    .clone(),
            );
            result_type = self.substitute(body, &Expr::fvar(id))?;
            if *binder_info == BinderInfo::Default {
                if explicit != 0 {
                    discriminants.push(atom(","));
                }
                discriminants.push(Syntax::node(
                    parser_kind(&["Term", "matchDiscr"]),
                    vec![null(vec![]), ident(name)],
                ));
                explicit += 1;
            }
        }
        // Count retained syntax against the same request budget before copying.
        let mut pending = vec![alternatives];
        while let Some(syntax) = pending.pop() {
            self.tick()?;
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        let body = Syntax::node(
            parser_kind(&["Term", "match"]),
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(discriminants),
                atom("with"),
                alternatives.clone(),
            ],
        );
        Ok((body, result_type))
    }
}
