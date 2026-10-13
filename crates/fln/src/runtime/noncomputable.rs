//! Check executable references before dictionary specialization can erase them.
//! Logical types and proofs retain their ordinary reduction behavior: callers
//! enter this check only after proof erasure and after explicit implementation
//! selection. A tag never grants access to a native external implementation.
use super::*;

impl Preparation<'_> {
    pub(super) fn check_noncomputable_head(&mut self, head: &Expr) -> Result<(), IngressError> {
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(());
        };
        if self.noncomputable.is_none() {
            // Bound the metadata work before decoding. Failed or partial reads
            // never populate the cache, which belongs to this immutable environment.
            if let Some(state) = self
                .environment
                .extension(&fln_elab::noncomputable::journal_name())
            {
                for entry in state.entries() {
                    let observed = self
                        .visited
                        .saturating_add(1)
                        .saturating_add(entry.payload.len());
                    if observed > self.limits.max_nodes {
                        return Err(IngressError::ResourceLimit {
                            resource: IngressResource::Nodes,
                            limit: self.limits.max_nodes,
                            observed,
                        });
                    }
                    self.visited = observed;
                }
            }
            let names =
                fln_elab::noncomputable::read(self.environment).map_err(|error| match error {
                    fln_elab::noncomputable::NoncomputableError::Limit => {
                        IngressError::MetadataResourceExhausted {
                            kind: "native noncomputable journal capacity",
                        }
                    }
                    _ => unsupported("malformed native noncomputable journal"),
                })?;
            self.noncomputable = Some(names);
        }
        if !self
            .noncomputable
            .as_ref()
            .is_some_and(|names| names.contains(name))
        {
            return Ok(());
        }
        // The pin's checkComputable permits extern declarations. The ordinary
        // native-contract and catalog gates must still authorize their runtime
        // implementation; this exception does not execute their logical body.
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            name,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(name).is_some())
        {
            return Ok(());
        }
        Err(unsupported("noncomputable runtime dependency"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::constants::{AxiomVal, ConstantVal};

    fn environment() -> Environment {
        let env = Environment::new()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name("secret"),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap();
        fln_elab::noncomputable::register(&env, &name("secret")).unwrap()
    }

    #[test]
    fn budget_stops_do_not_cache_a_partial_noncomputable_view() {
        let env = environment();
        let head = Expr::const_(name("secret"), vec![]);
        let mut limits = IngressLimits::default();
        limits.max_nodes = 0;
        let mut preparation = Preparation::new(&env, limits);
        for _ in 0..2 {
            assert!(matches!(
                preparation.check_noncomputable_head(&head),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    ..
                })
            ));
            assert!(preparation.noncomputable.is_none());
        }
        let mut retry = Preparation::new(&env, IngressLimits::default());
        assert!(matches!(
            retry.check_noncomputable_head(&head),
            Err(IngressError::UnsupportedNode {
                kind: "noncomputable runtime dependency"
            })
        ));
        assert!(
            retry
                .noncomputable
                .as_ref()
                .unwrap()
                .contains(&name("secret"))
        );
    }

    #[test]
    fn malformed_metadata_never_becomes_an_empty_cached_set() {
        let env = environment()
            .push_extension_entry(&fln_elab::noncomputable::journal_name(), b"broken".to_vec())
            .unwrap();
        let mut preparation = Preparation::new(&env, IngressLimits::default());
        for _ in 0..2 {
            assert!(matches!(
                preparation.check_noncomputable_head(&Expr::const_(name("other"), vec![])),
                Err(IngressError::UnsupportedNode {
                    kind: "malformed native noncomputable journal"
                })
            ));
            assert!(preparation.noncomputable.is_none());
        }
    }

    #[test]
    fn a_complete_metadata_view_is_reused_only_inside_its_preparation() {
        let env = environment();
        let head = Expr::const_(name("other"), vec![]);
        let mut preparation = Preparation::new(&env, IngressLimits::default());
        preparation.check_noncomputable_head(&head).unwrap();
        let charged = preparation.visited;
        assert!(charged > 0);
        preparation.check_noncomputable_head(&head).unwrap();
        assert_eq!(preparation.visited, charged);
        let empty = Environment::new();
        let mut independent = Preparation::new(&empty, IngressLimits::default());
        independent
            .check_noncomputable_head(&Expr::const_(name("secret"), vec![]))
            .unwrap();
        assert!(independent.noncomputable.unwrap().is_empty());
        assert!(preparation.noncomputable.unwrap().contains(&name("secret")));
    }
}
