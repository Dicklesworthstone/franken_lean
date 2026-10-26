//! The pin's default simp journal, including oriented proofs and scoped entries.
//! Layouts come from the checked source-extension extraction; every supporting
//! object is charged to the ordinary module writer's cumulative budgets.
use super::*;

impl Encoder {
    fn simp_names(&mut self, names: &[Name]) -> WResult<Obj> {
        self.source_array_bound(names.len())?;
        let mut seen = HashSet::new();
        let mut values = Vec::with_capacity(names.len());
        for name in names {
            if name.is_anonymous() || !seen.insert(name.clone()) {
                return Err(WriteError::Contract {
                    what: "anonymous or duplicate simp name",
                });
            }
            values.push(self.name(name)?);
        }
        self.array(values)
    }

    fn simp_theorem(&mut self, theorem: &SimpTheorem) -> WResult<Obj> {
        if theorem.origin.is_anonymous()
            || theorem.proof.has_expr_mvar()
            || theorem.proof.has_level_mvar()
            || theorem.proof.has_fvar()
            || theorem.proof.has_loose_bvars()
        {
            return Err(WriteError::Contract {
                what: "invalid persistent simp origin or nonclosed proof",
            });
        }
        let keys = self.discr_tree_keys(&theorem.keys)?;
        let level_params = self.simp_names(&theorem.level_params)?;
        let proof = self.expression(&theorem.proof)?;
        let priority = self.nat_u64(u64::from(theorem.priority))?;
        let mut origin_fields: Vec<_> = (0..layout::SIMP_ORIGIN_DECL_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect();
        origin_fields[layout::SIMP_ORIGIN_DECL_NAME] = self.name(&theorem.origin)?;
        let mut origin_flags = [0; layout::SIMP_ORIGIN_DECL_INV_SCALAR + 1];
        origin_flags[layout::SIMP_ORIGIN_DECL_POST_SCALAR] = u8::from(theorem.post);
        origin_flags[layout::SIMP_ORIGIN_DECL_INV_SCALAR] = u8::from(theorem.origin_reverse);
        let origin = self.ctor(layout::SIMP_ORIGIN_DECL, origin_fields, &origin_flags)?;

        let mut fields: Vec<_> = (0..layout::SIMP_THM_POINTERS)
            .map(|_| Obj::mk_nat(0))
            .collect();
        fields[layout::SIMP_THM_KEYS] = keys;
        fields[layout::SIMP_THM_LEVEL_PARAMS] = level_params;
        fields[layout::SIMP_THM_PROOF] = proof;
        fields[layout::SIMP_THM_PRIORITY] = priority;
        fields[layout::SIMP_THM_ORIGIN] = origin;
        let mut scalars = [0; layout::SIMP_THM_SCALAR_BYTES];
        scalars[layout::SIMP_THM_POST_SCALAR] = u8::from(theorem.post);
        scalars[layout::SIMP_THM_PERM_SCALAR] = u8::from(theorem.permutation);
        scalars[layout::SIMP_THM_RFL_SCALAR] = u8::from(theorem.reflexive);
        scalars[layout::SIMP_THM_BACKWARD_RFL_SCALAR] = u8::from(theorem.backward_reflexive);
        self.ctor(0, fields, &scalars)
    }

    pub(super) fn simp_block(&mut self, simps: &[SimpEntry]) -> WResult<Obj> {
        self.source_array_bound(simps.len())?;
        let mut entries = Vec::with_capacity(simps.len());
        for simp in simps {
            if simp.scope.as_ref().is_some_and(Name::is_anonymous) {
                return Err(WriteError::Contract {
                    what: "anonymous simp scope",
                });
            }
            let entry = match &simp.kind {
                SimpKind::Theorem(theorem) => {
                    let theorem = self.simp_theorem(theorem)?;
                    self.ctor(layout::SIMP_ENTRY_THM, vec![theorem], &[])?
                }
                SimpKind::Unfold(declaration) => {
                    if declaration.is_anonymous() {
                        return Err(WriteError::Contract {
                            what: "anonymous simp unfolding declaration",
                        });
                    }
                    let declaration = self.name(declaration)?;
                    self.ctor(layout::SIMP_ENTRY_TO_UNFOLD, vec![declaration], &[])?
                }
                SimpKind::UnfoldTheorems {
                    declaration,
                    theorems,
                } => {
                    if declaration.is_anonymous() {
                        return Err(WriteError::Contract {
                            what: "anonymous simp equation declaration",
                        });
                    }
                    let declaration = self.name(declaration)?;
                    let theorems = self.simp_names(theorems)?;
                    self.ctor(
                        layout::SIMP_ENTRY_TO_UNFOLD_THMS,
                        vec![declaration, theorems],
                        &[],
                    )?
                }
            };
            entries.push(match &simp.scope {
                Some(scope) => {
                    let scope = self.name(scope)?;
                    self.ctor(layout::SCOPE_SCOPED, vec![scope, entry], &[])?
                }
                None => self.ctor(layout::SCOPE_GLOBAL, vec![entry], &[])?,
            });
        }
        let entries = self.array(entries)?;
        let name = self.name(&Name::from_components(layout::SIMP_EXTENSION.split('.')))?;
        self.ctor(0, vec![name, entries], &[])
    }
}
