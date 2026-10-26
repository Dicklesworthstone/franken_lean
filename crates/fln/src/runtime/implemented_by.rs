//! Resolve explicit executable replacements after admission and before code
//! specialization. Type reduction, dictionaries used as type metadata, and the
//! original environments seen by either checker keep their logical definitions.
use super::*;
use fln_elab::implemented_by::{ImplementedByError, ImplementedByReadError, ImplementedByTable};

impl Preparation<'_> {
    /// Inert-value inspection may retain an extern name but must not replace it
    /// with its logical body. Actual execution still needs a complete native
    /// contract; this query grants no implementation or ABI authority.
    pub(super) fn has_extern_attribute(&mut self, name: &Name) -> Result<bool, IngressError> {
        source_intrinsics::read_extern_attributes(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        Ok(self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(name).is_some()))
    }

    pub(super) fn implementations(&mut self) -> Result<&ImplementedByTable, IngressError> {
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

    /// Static dictionaries cannot unfold a logical body replaced by an
    /// initializer, explicit implementation, or recursive executable companion.
    /// Leave these values on the execution path; neither body may replace
    /// dependent type metadata or become an inert projected field.
    pub(super) fn has_implementation(&mut self, name: &Name) -> Result<bool, IngressError> {
        Ok(self
            .runtime_initializers
            .is_some_and(|names| names.contains(name))
            || self.implementations()?.get(name).is_some()
            || self.has_recursive_companion(name)?
            || self.well_founded_fix_target(name)?.is_some())
    }

    /// Keep explicit implementations first. The admitted fixpoint equation is
    /// consulted only for its exact source, and a present recursive companion
    /// retains ordinary linkage validation and selection at the call site.
    pub(super) fn executable_replacement(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        match self.implementation_target(requested)? {
            Some(target) => Ok(Some(target)),
            None => self.well_founded_fix_target(requested),
        }
    }

    /// An attribute selects a target without granting new execution authority.
    /// Admitted unsafe definitions use the same body, initializer and companion
    /// checks as direct calls. Opaque targets still require their existing
    /// authority; unknown externs and foreign IR never become body fallbacks.
    pub(super) fn implementation_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        let parent = self.recursive_parent_candidate(requested);
        if self
            .implementations()?
            .get(parent.as_ref().unwrap_or(requested))
            .is_none()
        {
            return Ok(None);
        }
        let mut target = requested.clone();
        let mut replaced = false;
        let mut seen = HashSet::new();
        loop {
            self.tick()?;
            if let Some(parent) = self.recursive_parent(&target)? {
                target = parent;
            }
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            if !seen.insert(target.clone()) {
                return Err(unsupported("implemented_by recursive companion cycle"));
            }
            let Some(next) = self.implementations()?.get(&target).cloned() else {
                break;
            };
            // Only these exact explicit edges admit checked logical Array
            // adapters. Other replacements retain generic selection of their
            // own executable bodies, without acquiring an Array adapter.
            if array_iteration::canonical_pair(&target, &next) {
                return self.array_iteration_target().map(Some);
            }
            if array_fold::canonical_pair(&target, &next) {
                return self.array_fold_target().map(Some);
            }
            replaced = true;
            target = next;
        }
        if !replaced {
            return Ok(None);
        }
        self.tick()?;
        let executable_target = match self.environment.find(&target) {
            // The pin's principal use of `implemented_by` is an unsafe
            // implementation behind a safe logical interface. Selection does
            // not unfold that implementation in either checker: below it must
            // pass the ordinary executable-body and selected-extern gates.
            Some(ConstantInfo::Defn(_)) => true,
            Some(ConstantInfo::Opaque(value)) => !value.is_unsafe,
            Some(ConstantInfo::Axiom(value)) => !value.is_unsafe,
            Some(ConstantInfo::Ctor(value)) => !value.is_unsafe,
            _ => false,
        };
        if !executable_target {
            return Err(unsupported(
                "implemented_by target has no supported executable body",
            ));
        }
        if matches!(self.environment.find(&target), Some(ConstantInfo::Ctor(_))) {
            // A constructor such as Nat.succ has no definition body. Preserve
            // its extern gate, then use ordinary constructor/native lowering.
            source_intrinsics::check_selected_extern_attribute(
                self.environment,
                &target,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?;
            return Ok(Some(target));
        }
        // A replacement retains the target's ordinary execution authority.
        // Generic intrinsics compare their complete admitted models. File IO
        // uses a separate checked adapter, including the opaque declaration,
        // extern ownership, world/result models and binary conversion closure.
        // Pure word adapters have their own exact data/dependency contract.
        // Recognizer errors remain refusals; none may fall back to an opaque
        // default or an ordinary body after a failed native contract.
        let native = self.native_intrinsic_binding(&target)?.is_some()
            || self.native_natural_decision_target(&target)?.is_some()
            || self.native_char_of_nat_target(&target)?.is_some()
            || self.native_array_access_target(&target)?.is_some()
            || self.bounded_word_contract(&target)?
            || match source_intrinsics::io::fs::Operation::from_name(&target) {
                Some(operation) => source_intrinsics::io::fs::primitive_matches(
                    self.environment,
                    operation,
                    &mut self.externs,
                    &mut self.visited,
                    self.limits,
                )?,
                None => source_intrinsics::io::fs::word_matches(
                    self.environment,
                    &target,
                    &mut self.externs,
                    &mut self.visited,
                    self.limits,
                )?,
            }
            || source_intrinsics::string_from_list::contract_matches(
                self.environment,
                &target,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?;
        if native {
            return Ok(Some(target));
        }
        // Attribute and companion-parent edges were resolved iteratively above.
        // Only the raw body/linkage gate runs here, never recursive lookup.
        if self.recursive_definition(&target)?.is_none() {
            return Err(unsupported(
                "implemented_by target has no supported executable body",
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

    /// Rewrite only the executable head, giving explicit attributes precedence
    /// over a recursive companion. Universes and argument order are retained;
    /// type and proof syntax are never traversed by this selector.
    pub(super) fn implemented_by_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let target = match self.executable_replacement(name)? {
            Some(target) => Some(target),
            None => self.recursive_companion_target(name)?,
        };
        let Some(target) = target else {
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
