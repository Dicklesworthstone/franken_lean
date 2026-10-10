//! Resolve explicit executable replacements after admission and before code
//! specialization. Type reduction, dictionaries used as type metadata, and the
//! original environments seen by either checker keep their logical definitions.
use super::*;
use fln_elab::implemented_by::{ImplementedByError, ImplementedByReadError, ImplementedByTable};

impl Preparation<'_> {
    fn implementations(&mut self) -> Result<&ImplementedByTable, IngressError> {
        if self.implementations.is_none() {
            let table = ImplementedByTable::read_metered(self.environment, |amount| {
                let observed = self.visited.saturating_add(amount);
                if observed > self.limits.max_nodes {
                    return Err(IngressError::ResourceLimit {
                        resource: IngressResource::Nodes,
                        limit: self.limits.max_nodes,
                        observed,
                    });
                }
                self.visited = observed;
                Ok(())
            })
            .map_err(|error| match error {
                ImplementedByReadError::Budget(error) => error,
                ImplementedByReadError::Registry(ImplementedByError::Limit) => {
                    IngressError::MetadataResourceExhausted {
                        kind: "native implemented_by journal capacity or validation",
                    }
                }
                ImplementedByReadError::Registry(ImplementedByError::Cycle(_)) => {
                    unsupported("implemented_by replacement cycle")
                }
                ImplementedByReadError::Registry(_) => {
                    unsupported("invalid native implemented_by journal")
                }
            })?;
            self.implementations = Some(table);
        }
        Ok(self
            .implementations
            .as_ref()
            .expect("only validated implementation tables are cached"))
    }

    /// Static dictionary evidence cannot unfold the logical body of an
    /// executable replacement. Leave such values on the ordinary execution
    /// path; substituting replacement fields into dependent types would also
    /// change the logical type plane.
    pub(super) fn has_implementation(&mut self, name: &Name) -> Result<bool, IngressError> {
        Ok(self.implementations()?.get(name).is_some())
    }

    /// An attribute authorizes selecting this checked target, not executing an
    /// opaque inhabitant, unsafe body, unknown extern, or foreign IR. Exact
    /// native contracts may authorize an opaque target; supported partial
    /// definitions continue through their existing complete-group gate.
    pub(super) fn implementation_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        let Some(target) = self.implementations()?.implementation(requested).cloned() else {
            return Ok(None);
        };
        self.tick()?;
        let safe_target = match self.environment.find(&target) {
            Some(ConstantInfo::Defn(value)) => value.safety != DefinitionSafety::Unsafe,
            Some(ConstantInfo::Opaque(value)) => !value.is_unsafe,
            Some(ConstantInfo::Axiom(value)) => !value.is_unsafe,
            _ => false,
        };
        if !safe_target {
            return Err(unsupported(
                "implemented_by target has no supported safe or partial executable body",
            ));
        }
        // A replacement retains the target's ordinary execution authority.
        // Generic intrinsics compare their complete admitted models. File IO
        // uses a separate checked adapter, including the opaque declaration,
        // extern ownership, world/result models and binary conversion closure.
        // Recognizer errors remain refusals; none may fall back to an opaque
        // default or an ordinary body after a failed native contract.
        let native = executable_intrinsic_binding_cached(
            self.environment,
            &target,
            &mut self.visited,
            self.limits,
            &mut self.externs,
        )?
        .is_some()
            || match source_intrinsics::io::fs::Operation::from_name(&target) {
                Some(operation) => source_intrinsics::io::fs::primitive_matches(
                    self.environment,
                    operation,
                    &mut self.externs,
                    &mut self.visited,
                    self.limits,
                )?,
                None => false,
            };
        if native {
            return Ok(Some(target));
        }
        // `target` is a terminal table entry: this call cannot recurse through
        // another replacement. It applies the existing safe/partial body gate.
        if self.executable_definition(&target)?.is_none() {
            return Err(unsupported(
                "implemented_by target has no supported safe or partial executable body",
            ));
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            &target,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(&target).is_some())
        {
            return Err(unsupported(
                "implemented_by target extern has no supported native implementation",
            ));
        }
        Ok(Some(target))
    }

    /// Rewrite only the executable head. Universes and argument evaluation
    /// order stay exactly as supplied; type/proof syntax is never traversed.
    pub(super) fn implemented_by_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(target) = self.implementation_target(name)? else {
            return Ok(None);
        };
        let source = self
            .environment
            .find(name)
            .ok_or_else(|| unsupported("implemented_by source is absent"))?;
        if levels.len() != source.constant_val().level_params.len() {
            return Err(unsupported("implemented_by call universe arity"));
        }
        if args.len() > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: args.len(),
            });
        }
        Ok(Some(
            args.iter()
                .cloned()
                .fold(Expr::const_(target, levels.clone()), Expr::app),
        ))
    }
}
