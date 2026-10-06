//! Preserve ordinary source typing before structural recursion rebinds locals.
//!
//! The self name is only an abstract local with the declared function type.
//! A checked proof retains the original body as an unused let initializer, so
//! both checkers validate it and runtime proof erasure removes the obligation.
use super::*;

impl Context {
    pub(super) fn original_recursive_body_obligation(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("prepared structural candidate");
        let locals = self.txn.lctx.clone();
        // Ordinary matching keeps the original header locals. In particular,
        // `xs : Vec A n` is not silently replaced by a constructor whose result
        // index makes an otherwise invalid source branch typecheck.
        self.recursion
            .as_mut()
            .expect("prepared structural candidate")
            .pending = false;
        let original = self.term(syntax, expected)?;
        self.resolve_instances_with_defaults()?;
        self.flush(true)?;
        let value = self
            .instantiate(&original.value)?
            .abstract_fvar(&recursion.marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let type_ = self
            .instantiate(&original.type_)?
            .abstract_fvar(&recursion.marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let domain = self.instantiate(&recursion.reference.type_)?;
        self.txn.lctx = locals;
        self.recursion = Some(recursion);

        // No declaration of True, Eq, or another seed constant is required.
        // The closed proposition is (P : Prop) -> P -> P. Under the proof
        // binder, #1 denotes P and #0 denotes its proof. The value below uses
        // #0 as P in the inner binder's domain, then #0 as its proof in the body.
        let p = Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?;
        let outer_p = Expr::bvar(1).map_err(|_| failure(SourceInferenceError::Scope))?;
        let proposition = Expr::forall_e(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::forall_e(Name::anonymous(), p.clone(), outer_p, BinderInfo::Default),
            BinderInfo::Default,
        );
        let proof = Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::lam(Name::anonymous(), p.clone(), p, BinderInfo::Default),
            BinderInfo::Default,
        );
        // `value` and `type_` are open only over #0 = self (and the original
        // header FVars). The checked initializer occurs before its let binder;
        // the closed proof has no references to shift under that binder.
        let checked = Expr::let_e(Name::anonymous(), type_, value, proof, false);
        Ok(Typed {
            value: Expr::lam(
                Name::anonymous(),
                domain.clone(),
                checked,
                BinderInfo::Default,
            ),
            type_: Expr::forall_e(Name::anonymous(), domain, proposition, BinderInfo::Default),
        })
    }
}
