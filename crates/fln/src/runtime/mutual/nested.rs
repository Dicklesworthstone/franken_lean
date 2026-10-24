//! Nested auxiliaries are applications, not new datatype declarations. Recover
//! their identities and order from the admitted recursor's motive telescope,
//! then reuse the ordinary mutual case/fold lowering and checked layout graph.
use super::*;

impl Preparation<'_> {
    pub(in crate::runtime) fn nested_group(
        &mut self,
        rec: &RecursorVal,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Group>, IngressError> {
        let Some(owner) = rec.all.first() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(owner)) = self.environment.find(owner) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || owner.is_unsafe
            || owner.num_nested == 0
            || owner.all != rec.all
            || owner.num_params != rec.num_params
            || rec.num_motives as usize != rec.all.len().saturating_add(owner.num_nested as usize)
            || rec.num_indices != 0
            || levels.len() != rec.base.level_params.len()
        {
            return Ok(None);
        }
        let prefix = (rec.num_params as usize)
            .checked_add(rec.num_motives as usize)
            .ok_or_else(|| unsupported("nested recursor prefix"))?;
        let major = prefix
            .checked_add(rec.num_minors as usize)
            .ok_or_else(|| unsupported("nested recursor arity"))?;
        let arity = major
            .checked_add(1)
            .ok_or_else(|| unsupported("nested recursor arity"))?;
        if args.len() < arity {
            return Ok(None);
        }
        let mut telescope =
            self.universe_instance(&rec.base.type_, &rec.base.level_params, levels)?;
        let mut shapes = Vec::new();
        let mut seen = HashSet::new();
        for (position, argument) in args[..major].iter().enumerate() {
            self.tick()?;
            let normal = self.type_head(&telescope)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if (rec.num_params as usize..prefix).contains(&position) {
                // This lane requires no index telescope. An indexed auxiliary
                // is not represented by pretending its index is a data field.
                let motive = self.type_head(binder_type)?;
                let ExprNode::ForallE {
                    binder_type: family,
                    body: sort,
                    ..
                } = motive.node()
                else {
                    return Ok(None);
                };
                if !matches!(sort.node(), ExprNode::Sort { .. }) {
                    return Ok(None);
                }
                let source = self.erase_data_indices(family)?;
                let (head, _) = self.spine(&source)?;
                let ExprNode::Const { name, .. } = head.node() else {
                    return Ok(None);
                };
                let Some(ConstantInfo::Induct(info)) = self.environment.find(name) else {
                    return Ok(None);
                };
                let index = position - rec.num_params as usize;
                if info.is_unsafe
                    || info.num_indices != 0
                    || (index < rec.all.len() && name != &rec.all[index])
                    || !seen.insert(source.clone())
                {
                    return Ok(None);
                }
                if self.value_type(&source)? != Some(ValueType::Constructor) {
                    return Ok(None);
                }
                let Some(shape) = self.record_shape(&source)? else {
                    return Ok(None);
                };
                reserve(&mut shapes, self.limits.max_context_depth)?;
                shapes.push(shape);
            }
            telescope = self.substitution(body, argument)?;
        }
        let normal = self.type_head(&telescope)?;
        let ExprNode::ForallE { binder_type, .. } = normal.node() else {
            return Ok(None);
        };
        let source = self.erase_data_indices(binder_type)?;
        // List (List Tree) and List Tree share constructor names. The actual
        // major TYPE selects the member, never a recursor spelling or a first
        // matching constructor name which would conflate those instantiations.
        let Some(selected) = shapes.iter().position(|shape| shape.source == source) else {
            return Ok(None);
        };
        let mut total = 0usize;
        let mut minor_offset = 0usize;
        let mut indices = Vec::new();
        for (index, shape) in shapes.iter().enumerate() {
            self.tick()?;
            if index == selected {
                minor_offset = total;
            }
            total = total
                .checked_add(shape.constructors.len())
                .ok_or_else(|| unsupported("nested constructor count"))?;
            reserve(&mut indices, self.limits.max_context_depth)?;
            indices.push(Vec::new());
        }
        let shape = &shapes[selected];
        if total != rec.num_minors as usize || rec.rules.len() != shape.constructors.len() {
            return Ok(None);
        }
        for (rule, constructor) in rec.rules.iter().zip(&shape.constructors) {
            self.tick()?;
            if rule.ctor != constructor.original
                || rule.nfields as usize != constructor.fields.len()
            {
                return Ok(None);
            }
        }
        Ok(Some(Group {
            shapes,
            selected,
            indices,
            minor_offset,
            arity,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn environment() -> Environment {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
            .check_source_files(&[b"inductive Seq (A : Type) where | nil | cons (head : A) (tail : Seq A)\ninductive Rose (A : Type) where | node (value : A) (children : Seq (Rose A))"],
                &KVMap::new(), SourceCheckLimits::new(limits))
            .unwrap().into_complete().unwrap().engine.environment().clone()
    }
    fn rose(element: &str) -> Expr {
        Expr::app(
            Expr::const_(name("Rose"), vec![]),
            Expr::const_(name(element), vec![]),
        )
    }
    #[test]
    fn nested_layouts_close_the_cycle_without_conflating_element_specializations() {
        let env = environment();
        let mut prep = Preparation::new(&env, IngressLimits::default());
        assert_eq!(
            prep.value_type(&rose("Nat")).unwrap(),
            Some(ValueType::Constructor)
        );
        assert_eq!(prep.constructors.len(), 3);
        let original = prep.constructors.clone();
        let list = Expr::app(Expr::const_(name("Seq"), vec![]), rose("Nat"));
        assert_eq!(
            prep.value_type(&list).unwrap(),
            Some(ValueType::Constructor)
        );
        assert_eq!(prep.constructors, original);
        assert_eq!(
            prep.value_type(&rose("String")).unwrap(),
            Some(ValueType::Constructor)
        );
        assert_eq!(prep.constructors.len(), 6);
        assert!(
            prep.constructors
                .iter()
                .any(|ctor| ctor.fields.first() == Some(&ValueType::String))
        );
        assert!(
            prep.constructors
                .iter()
                .any(|ctor| ctor.fields.first() == Some(&ValueType::Nat))
        );
    }
    #[test]
    fn nested_discovery_exhaustion_rolls_back_every_executable_anchor() {
        let env = environment();
        for bound in [0, 1, 2] {
            let mut prep = Preparation::new(
                &env,
                IngressLimits {
                    fir: fln_comp::fir::ValidationLimits {
                        max_constructors: bound,
                        ..IngressLimits::default().fir
                    },
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                prep.value_type(&rose("Nat")),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(prep.value_types.records.is_empty());
            assert!(prep.value_types.closures.is_empty());
            assert!(prep.constructors.is_empty() && prep.interfaces.is_empty());
            prep.limits = IngressLimits::default();
            assert_eq!(
                prep.value_type(&rose("Nat")).unwrap(),
                Some(ValueType::Constructor)
            );
            let mut clean = Preparation::new(&env, IngressLimits::default());
            assert_eq!(
                clean.value_type(&rose("Nat")).unwrap(),
                Some(ValueType::Constructor)
            );
            assert_eq!(prep.constructors, clean.constructors);
            assert_eq!(prep.interfaces, clean.interfaces);
        }
    }
}
