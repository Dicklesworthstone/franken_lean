//! Resolve explicit executable replacements after admission and before code
//! specialization. Type reduction, dictionaries used as type metadata, and the
//! original environments seen by either checker keep their logical definitions.
use super::*;
use fln_elab::implemented_by::{ImplementedByError, ImplementedByReadError, ImplementedByTable};

// Generated from the actual decoded pin, including declaration bodies, explicit
// implementation edges, extern presence and recursive companions. Reproduce:
// FLN_DUMP_NATIVE_NAME_CONTRACTS=1 cargo test -p fln --lib
// runtime::implemented_by::tests::pinned_name_contract_rows_come_from_the_actual_decoded_closure
// -- --exact --nocapture
const NAME_CONTRACT: &str = include_str!("implemented_by_names.txt");
const NAME_OPERATIONS: [&str; 4] = [
    "Lean.Name.anonymous",
    "Lean.Name.str",
    "Lean.Name.num",
    "Lean.Name.casesOn",
];

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

    /// Computed Name fields are a cache, not part of its source data layout.
    /// The pin's unsafe constructor/eliminator overrides store hashes in another
    /// inductive and cast between it and Name. Our ordinary constructors and
    /// recursor use the logical layout. Hash execution keeps its own explicit
    /// implementation selection and is outside this representation adapter.
    /// Select that representation only for the complete pinned implementation
    /// model; an arbitrary implemented_by edge is never a body fallback.
    fn logical_name_implementation(&mut self, requested: &Name) -> Result<bool, IngressError> {
        if !NAME_OPERATIONS
            .iter()
            .any(|label| requested == &name(label))
        {
            return Ok(false);
        }
        let expected = Name::str(requested.clone(), "_override");
        if self.implementations()?.get(requested) != Some(&expected) {
            return Ok(false);
        }
        // Selection still observes the executable target's computability
        // contract before replacing its representation-specific body.
        self.check_noncomputable_head(&Expr::const_(expected, vec![]))?;
        self.tick()?;
        if !self.name_model_checked {
            // This checker walks the same five-column contract format as the
            // Array adapters. It is independent of the inventory's subject.
            source_intrinsics::array_iteration::matches_inventory(
                NAME_CONTRACT,
                self.environment,
                self.implementations.as_ref().expect("validated selections"),
                self.runtime_initializers,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )
            .map_err(|error| match error {
                IngressError::UnsupportedNode { .. } => {
                    unsupported("computed Name implementation differs from its pinned contract")
                }
                other => other,
            })?;
            self.name_model_checked = true;
        }
        Ok(true)
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
        if self.logical_name_implementation(requested)? {
            return Ok(None);
        }
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
            if arrays::canonical_modify_pair(&target, &next) {
                return self.array_modify_target().map(Some);
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
            || self.native_array_operation(&target)?
            || self.legacy_array_access_target(&target)?.is_some()
            || self.bounded_word_contract(&target)?
            || self.hash_mixer_contract(&target)?
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_name_contract_rows_come_from_the_actual_decoded_closure() {
        crate::runtime::array_iteration::with_fixture(|environment| {
            let rows = crate::runtime::arrays::extraction::rows_from(
                environment,
                NAME_OPERATIONS.into_iter().chain(["Lean.Name.hash"]),
            );
            assert!(!rows.is_empty());
            if std::env::var_os("FLN_DUMP_NATIVE_NAME_CONTRACTS").is_some() {
                for row in &rows {
                    println!("NAME_CONTRACT\t{row}");
                }
            }
            assert_eq!(rows.join("\n") + "\n", NAME_CONTRACT);
        });
    }

    #[test]
    fn pinned_computed_names_keep_logical_layout_without_changing_declarations() {
        crate::runtime::array_iteration::with_fixture(|environment| {
            let count = environment.constants().count();
            let originals: Vec<_> = NAME_OPERATIONS
                .iter()
                .map(|label| environment.find(&name(label)).unwrap().clone())
                .collect();
            let mut preparation = Preparation::new(environment, IngressLimits::default());
            assert!(!preparation.name_model_checked);
            for label in NAME_OPERATIONS {
                assert_eq!(
                    preparation.implementation_target(&name(label)).unwrap(),
                    None
                );
                assert!(preparation.name_model_checked);
            }
            assert!(
                !preparation
                    .logical_name_implementation(&name("Lean.Name.hash"))
                    .unwrap()
            );
            assert_eq!(environment.constants().count(), count);
            for original in originals {
                assert_eq!(environment.find(original.name()), Some(&original));
            }
            assert!(preparation.lambdas.is_empty());
            assert!(preparation.constructors.is_empty());
        });
    }

    fn refused_name_model(environment: &Environment) {
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        assert!(matches!(
            preparation.implementation_target(&name("Lean.Name.str")),
            Err(IngressError::UnsupportedNode {
                kind: "computed Name implementation differs from its pinned contract",
            })
        ));
        assert!(!preparation.name_model_checked);
        assert!(preparation.lambdas.is_empty());
        assert!(preparation.constructors.is_empty());
    }

    #[test]
    fn changed_computed_name_bodies_and_execution_metadata_are_refused() {
        use crate::runtime::array_iteration::replace;
        use fln_elab::externs::{self, ExternEntry};
        use fln_elab::implemented_by;

        crate::runtime::array_iteration::with_fixture(|environment| {
            let Some(ConstantInfo::Defn(original)) =
                environment.find(&name("Lean.Name.str._override"))
            else {
                panic!("the actual computed constructor override is a definition");
            };
            let mut changed = original.clone();
            changed.value = Expr::app(
                Expr::lam(
                    Name::anonymous(),
                    changed.base.type_.clone(),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                changed.value,
            );
            refused_name_model(&replace(environment, ConstantInfo::Defn(changed)));

            let Some(ConstantInfo::Opaque(original)) = environment.find(&name("mixHash")) else {
                panic!("the actual hash mixer is opaque");
            };
            let mut alternate = original.clone();
            alternate.base.name = name("alternateNameHashMixer");
            alternate.all = vec![alternate.base.name.clone()];
            let alternate_name = alternate.base.name.clone();
            let changed = environment
                .add_decl(ConstantInfo::Opaque(alternate))
                .unwrap();
            let changed =
                implemented_by::register(&changed, &name("mixHash"), &alternate_name).unwrap();
            assert_eq!(
                environment.entry(&name("mixHash")).unwrap().digest(),
                changed.entry(&name("mixHash")).unwrap().digest()
            );
            refused_name_model(&changed);

            let changed = externs::register(
                environment,
                &name("Lean.Name.str._override"),
                vec![ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_computed_name_constructor".to_owned(),
                }],
            )
            .unwrap();
            refused_name_model(&changed);

            let Some(ConstantInfo::Defn(original)) = environment.find(&name("Lean.Name.hash"))
            else {
                panic!("the admitted logical hash has a body");
            };
            let mut companion = original.clone();
            companion.base.name = name("Lean.Name.hash._unsafe_rec");
            companion.all = vec![companion.base.name.clone()];
            assert!(!environment.contains(&companion.base.name));
            let changed = environment.add_decl(ConstantInfo::Defn(companion)).unwrap();
            refused_name_model(&changed);

            // A changed family layout is refused even when the selected edge
            // and every name still match. This is a private model-boundary
            // mutant, not a declaration admitted by either public checker.
            let Some(ConstantInfo::Ctor(original)) = environment.find(&name("Lean.Name.str"))
            else {
                panic!("the logical Name string node is a constructor");
            };
            let mut changed = original.clone();
            changed.num_fields += 1;
            refused_name_model(&replace(environment, ConstantInfo::Ctor(changed)));
        });
    }

    #[test]
    fn computed_name_validation_preserves_budget_and_initializer_refusals() {
        crate::runtime::array_iteration::with_fixture(|environment| {
            let mut preparation = Preparation::new(environment, IngressLimits::default());
            preparation.implementations().unwrap();
            preparation.limits.max_nodes = preparation.visited;
            assert!(matches!(
                preparation.implementation_target(&name("Lean.Name.str")),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(!preparation.name_model_checked);
            preparation.limits = IngressLimits::default();
            assert_eq!(
                preparation
                    .implementation_target(&name("Lean.Name.str"))
                    .unwrap(),
                None
            );
            assert!(preparation.name_model_checked);

            let initializers = BTreeSet::from([name("mixHash")]);
            let mut preparation = preparation.with_runtime_initializers(&initializers);
            assert!(!preparation.name_model_checked);
            assert!(matches!(
                preparation.implementation_target(&name("Lean.Name.str")),
                Err(IngressError::UnsupportedNode {
                    kind: "computed Name implementation differs from its pinned contract",
                })
            ));
            assert!(!preparation.name_model_checked);
        });
    }

    #[test]
    fn noncomputable_computed_name_targets_are_not_hidden_by_the_adapter() {
        crate::runtime::array_iteration::with_fixture(|environment| {
            let changed =
                fln_elab::noncomputable::register(environment, &name("Lean.Name.str._override"))
                    .unwrap();
            let mut preparation = Preparation::new(&changed, IngressLimits::default());
            assert!(matches!(
                preparation.implementation_target(&name("Lean.Name.str")),
                Err(IngressError::UnsupportedNode {
                    kind: "noncomputable runtime dependency",
                })
            ));
            assert!(!preparation.name_model_checked);
            assert!(preparation.lambdas.is_empty());
            assert!(preparation.constructors.is_empty());
        });
    }
}
