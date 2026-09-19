//! Nonrecursive local functions use the same parameter elaboration and ordinary
//! let-expression checks as declarations. No generated global or axiom is used.
use super::*;

pub(super) struct Binding<'a> {
    pub name: Name,
    pub opaque: bool,
    pub parameters: &'a Syntax,
    pub annotation: Option<&'a Syntax>,
    pub value: &'a Syntax,
    pub body: &'a Syntax,
}

pub(super) struct Build<'a> {
    pub binding: Binding<'a>,
    pub expected: Option<Expr>,
    pub result_type: Option<Expr>,
    parameters: Vec<LocalDecl>,
    saved: LocalContext,
}

impl Context {
    pub(super) fn start_local_function<'a>(
        &mut self,
        binding: Binding<'a>,
        expected: Option<Expr>,
    ) -> Result<Build<'a>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let parameters = self.bind_parameters(binding.parameters)?;
        // The function's own name is intentionally not in scope in its value.
        // An outer binding of the same name retains normal lexical visibility.
        Ok(Build {
            binding,
            expected,
            result_type: None,
            parameters,
            saved,
        })
    }

    pub(super) fn close_local_function(
        &mut self,
        build: &Build<'_>,
        mut value: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.flush(false)?;
        value.value = self.instantiate(&value.value)?;
        value.type_ = self.instantiate(build.result_type.as_ref().unwrap_or(&value.type_))?;
        for local in build.parameters.iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            value.value = value
                .value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value.type_ = value
                .type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value.value = Expr::lam(
                local.user_name.clone(),
                domain.clone(),
                value.value,
                local.binder_info,
            );
            value.type_ = Expr::forall_e(
                local.user_name.clone(),
                domain,
                value.type_,
                local.binder_info,
            );
        }
        self.txn.lctx = build.saved.clone();
        // An explicit result remains in the let-bound function's full type.
        // K1 therefore checks it even when the enclosing body never calls f.
        Ok(value)
    }
}
