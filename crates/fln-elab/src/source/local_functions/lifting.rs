//! Named, closed candidates for let-rec/where helpers. No environment mutation.
//! The inlined owner remains the same checked term; these independently checked
//! closures expose the pin's owner.helper source interface after admission.
use super::*;

const MAX_LIFTED_FUNCTIONS: usize = 256;

#[derive(Clone, Default)]
pub(in crate::source) struct Lifting {
    pub parent: Option<Name>,
    names: HashSet<Name>,
    pub(super) closed: Vec<Closed>,
}

#[derive(Clone)]
pub(super) struct Closed {
    pub name: Name,
    pub term: Typed,
    pub context: LocalContext,
}

impl Lifting {
    pub fn roots(&self) -> impl Iterator<Item = Expr> + '_ {
        self.closed
            .iter()
            .flat_map(|closed| [closed.term.type_.clone(), closed.term.value.clone()])
    }
}

impl Context {
    pub(super) fn reserve_local_function_name(
        &mut self,
        short: &Name,
    ) -> Result<Option<Name>, NatDefinitionElabError> {
        self.tick()?;
        // An enclosing structural/well-founded lowering may elaborate the
        // same source twice and specialize it to private recursion callbacks.
        // Those compiler-local closures retain the existing inline behavior;
        // they are not a sound owner.helper interface without closure of the
        // enclosing recursive group. Do not publish a specialized impostor.
        if self.recursion.is_some() || self.well_founded.is_some() {
            return Ok(None);
        }
        let Some(parent) = &self.local_function_lifting.parent else {
            return Ok(None);
        };
        if self.local_function_lifting.names.len() >= MAX_LIFTED_FUNCTIONS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let name = parent.append_core(short);
        if self.txn.env.contains(&name) || !self.local_function_lifting.names.insert(name.clone()) {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a fresh local recursive declaration name",
            });
        }
        Ok(Some(name))
    }

    pub(in crate::source) fn lift_local_functions(
        &mut self,
        owner: &Declaration,
    ) -> Result<Vec<Declaration>, NatDefinitionElabError> {
        let safety = match owner {
            Declaration::Defn(value) => value.safety,
            Declaration::Thm(_) | Declaration::Opaque(_) | Declaration::Axiom(_) => {
                DefinitionSafety::Safe
            }
            _ if self.local_function_lifting.closed.is_empty() => return Ok(Vec::new()),
            _ => {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "local helper lifting for an independently checked declaration",
                });
            }
        };
        let closed = std::mem::take(&mut self.local_function_lifting.closed);
        let mut result = Vec::new();
        for Closed {
            name,
            term,
            context,
        } in closed
        {
            self.tick()?;
            let mut term = self.finish(term)?;
            // Instance synthesis in the continuation can reveal captures that
            // were absent when the opaque local value was first produced.
            // Recompute transitive captures against its exact saved telescope.
            let mut reads = self.elimination_reads(&term.value)?;
            reads.extend(self.elimination_reads(&term.type_)?);
            let mut captures = Vec::new();
            for local in context.decls().iter().rev() {
                self.tick()?;
                if reads.contains(&local.id) {
                    let domain = self.instantiate(&local.type_)?;
                    reads.extend(self.elimination_reads(&domain)?);
                    if let Some(value) = &local.value {
                        let value = self.instantiate(value)?;
                        reads.extend(self.elimination_reads(&value)?);
                    }
                    captures.push(local.clone());
                }
            }
            for local in captures {
                self.tick()?;
                let domain = self.instantiate(&local.type_)?;
                term.value = Expr::lam(
                    local.user_name.clone(),
                    domain.clone(),
                    term.value
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
                term.type_ = Expr::forall_e(
                    local.user_name,
                    domain,
                    term.type_
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
            if term.value.has_fvar()
                || term.type_.has_fvar()
                || term.value.has_loose_bvars()
                || term.type_.has_loose_bvars()
            {
                return Err(failure(SourceInferenceError::Scope));
            }
            // Explicit parameters belong to the owner, not every helper.
            // An unused owner universe must not force an unused-helper error.
            let explicit = self.explicit_levels;
            self.explicit_levels = 0;
            let level_params = self.declaration_levels(&[term.type_.clone(), term.value.clone()]);
            self.explicit_levels = explicit;
            let level_params = level_params?;
            let base = ConstantVal {
                name: name.clone(),
                level_params,
                type_: term.type_,
            };
            let sort = self
                .known_type(&base.type_)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let proof = matches!(self.whnf(&sort)?.node(), ExprNode::Sort { level } if level.is_always_zero());
            if proof && safety == DefinitionSafety::Safe {
                result.push(Declaration::Thm(fln_env::constants::TheoremVal {
                    base,
                    value: term.value,
                    all: vec![name],
                }));
            } else {
                result.push(Declaration::Defn(DefinitionVal {
                    base,
                    value: term.value,
                    hints: ReducibilityHints::Regular(1),
                    safety,
                    all: vec![name],
                }));
            }
        }
        // A course-of-values definition's executable companion is admitted after every
        // lifted helper its original body may call.
        if let Declaration::Defn(definition) = owner
            && definition.safety == DefinitionSafety::Safe
            && self.course_definitions.contains(&definition.base.name)
            && !self
                .txn
                .env
                .contains(&Name::str(definition.base.name.clone(), "_unsafe_rec"))
            && let Some(companion) = super::super::recursion::structural_companion(definition)
        {
            result.push(Declaration::Mutual(vec![companion]));
        }
        Ok(result)
    }
}
