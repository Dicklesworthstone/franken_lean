//! Written lambda parameters participate in structural recursion.
//!
//! Only a leading lambda spine is opened. Its annotations, implicit prefix,
//! dependent domains and final closure use the ordinary lambda elaborator.
//! No lambda is moved across an application, let, match branch or effect.
use super::*;

impl Context {
    /// Look through source parentheses and leading lambdas without entering
    /// their domains. Pattern preprocessing uses this same boundary to retain
    /// a local recursive match until its actual parameters have been opened.
    pub(in crate::source) fn recursive_lambda_body<'a>(
        &mut self,
        mut syntax: &'a Syntax,
    ) -> Result<&'a Syntax, NatDefinitionElabError> {
        loop {
            self.tick()?;
            if let Some(inner) = parenthesized_inner(syntax)? {
                syntax = inner;
                continue;
            }
            if syntax.kind() != Some(&parser_kind(&["Term", "fun"])) {
                return Ok(syntax);
            }
            let parts = expect_node(
                syntax,
                &parser_kind(&["Term", "fun"]),
                2,
                "recursive lambda",
            )?;
            // Pattern functions are expanded by the ordinary matrix pass.
            // Their alternatives are not a written binder telescope to open.
            if parts[1].kind() != Some(&parser_kind(&["Term", "basicFun"])) {
                return Ok(syntax);
            }
            let parts = expect_node(
                &parts[1],
                &parser_kind(&["Term", "basicFun"]),
                4,
                "recursive lambda body",
            )?;
            syntax = &parts[3];
        }
    }

    pub(in crate::source) fn open_recursive_lambdas<'a>(
        &mut self,
        mut syntax: &'a Syntax,
        mut expected: Option<Expr>,
        parameters: &mut Vec<LocalDecl>,
    ) -> Result<(&'a Syntax, Option<Expr>, Vec<binders::Telescope<'a>>), NatDefinitionElabError>
    {
        let mut lambdas = Vec::new();
        loop {
            self.tick()?;
            if let Some(inner) = parenthesized_inner(syntax)? {
                syntax = inner;
                continue;
            }
            if syntax.kind() != Some(&parser_kind(&["Term", "fun"])) {
                break;
            }
            let parts = expect_node(
                syntax,
                &parser_kind(&["Term", "fun"]),
                2,
                "recursive lambda",
            )?;
            if parts[1].kind() != Some(&parser_kind(&["Term", "basicFun"])) {
                break;
            }
            let mut lambda = self.start_telescope(syntax, expected, true)?;
            while let Some(annotation) = self.next_telescope_domain(&mut lambda)? {
                let type_expected = self.type_expected()?;
                let domain = self.term(annotation, Some(type_expected))?;
                self.open_telescope_group(&mut lambda, Some(domain))?;
            }
            expected = self.telescope_body_expected(&lambda)?;
            parameters.extend_from_slice(lambda.parameters());
            syntax = lambda.body;
            lambdas.push(lambda);
        }
        Ok((syntax, expected, lambdas))
    }

    pub(in crate::source) fn close_recursive_lambdas(
        &mut self,
        lambdas: &[binders::Telescope<'_>],
        mut body: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        for lambda in lambdas.iter().rev() {
            self.tick()?;
            body = self.finish_telescope(lambda.clone(), body)?;
        }
        Ok(body)
    }
}
