//! Explicit source recursors retained through macro-inline substitution.
//!
//! Mark occurrences, not names in an enclosing caller: a macro's generated
//! match must not inherit the recursor names of an argument it discards. The
//! ordinary Expr MData codec preserves these additive restrictions in artifacts.
use super::*;
use fln_core::options::{DataValue, KVMap};
use std::collections::HashMap;

fn prefix() -> Name {
    Name::from_components(["FrankenLean", "sourceRecursor"])
}

fn key() -> Name {
    Name::str(prefix(), "v1")
}

fn already_marked(data: &KVMap, value: &Expr) -> bool {
    matches!(data.entries(), [(tag, DataValue::OfName(marked))]
        if *tag == key()
            && matches!(value.node(), ExprNode::Const { name, .. } if name == marked))
}

fn children(value: &Expr) -> [Option<&Expr>; 3] {
    match value.node() {
        ExprNode::App { f, a } => [Some(f), Some(a), None],
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => [Some(binder_type), Some(body), None],
        ExprNode::LetE {
            type_, value, body, ..
        } => [Some(type_), Some(value), Some(body)],
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
        _ => [None, None, None],
    }
}

impl Context {
    /// Bound discovery too: KVMap allows duplicate keys and arbitrarily nested
    /// names. Unknown versions in our reserved namespace are not ordinary data.
    pub(super) fn has_source_rec_provenance(
        &mut self,
        data: &KVMap,
    ) -> Result<bool, NatDefinitionElabError> {
        let prefix = prefix();
        for (name, _) in data.entries() {
            let mut name = name.clone();
            while !name.is_anonymous() {
                self.tick()?;
                if name == prefix {
                    return Ok(true);
                }
                name = name.parent();
            }
        }
        Ok(false)
    }

    /// A surviving marker can only require the existing recursor check. It
    /// cannot rename a dependency, erase a value, or authorize an implementation.
    pub(super) fn source_rec_provenance(
        &mut self,
        data: &KVMap,
        value: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if !self.has_source_rec_provenance(data)? {
            return Ok(false);
        }
        let invalid = || failure(SourceInferenceError::InvalidMacroInlineProvenance);
        if !already_marked(data, value) {
            return Err(invalid());
        }
        let ExprNode::Const { name, .. } = value.node() else {
            return Err(invalid());
        };
        match self.txn.env.find(name) {
            Some(ConstantInfo::Rec(_)) => Ok(true),
            Some(ConstantInfo::Defn(_)) => {
                let Some((tagged, recursor)) = auxiliary_origin(name) else {
                    return Err(invalid());
                };
                if self.is_auxiliary_recursor(&tagged)?
                    && matches!(self.txn.env.find(&recursor), Some(ConstantInfo::Rec(_)))
                {
                    Ok(true)
                } else {
                    Err(invalid())
                }
            }
            _ => Err(invalid()),
        }
    }

    /// Retain source occurrence information before beta substitution. Existing
    /// markers remain data until their occurrence survives and is visited;
    /// discarded macro arguments must not become eager dependency checks.
    pub(in crate::source) fn mark_source_recursors(
        &mut self,
        root: &Expr,
        names: &[Name],
    ) -> Result<Expr, NatDefinitionElabError> {
        if names.is_empty() {
            return Ok(root.clone());
        }
        let mut named = BTreeSet::new();
        for name in names {
            self.tick()?;
            named.insert(name.clone());
        }
        let mut done = HashMap::<usize, Expr>::new();
        let mut work = vec![(root, false)];
        while let Some((value, exit)) = work.pop() {
            self.tick()?;
            let id = value.allocation_identity();
            if done.contains_key(&id) {
                continue;
            }
            if !exit {
                if let ExprNode::Const { name, .. } = value.node()
                    && named.contains(name)
                {
                    let data = KVMap::from_entries(vec![(key(), DataValue::OfName(name.clone()))]);
                    done.insert(id, Expr::mdata(data, value.clone()));
                    continue;
                }
                if let ExprNode::MData { data, expr } = value.node()
                    && already_marked(data, expr)
                {
                    done.insert(id, value.clone());
                    continue;
                }
                work.push((value, true));
                work.extend(
                    children(value)
                        .into_iter()
                        .flatten()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let child = |expr: &Expr| done[&expr.allocation_identity()].clone();
            if children(value)
                .into_iter()
                .flatten()
                .all(|expr| child(expr).allocation_identity() == expr.allocation_identity())
            {
                done.insert(id, value.clone());
                continue;
            }
            let rebuilt = match value.node() {
                ExprNode::App { f, a } => Expr::app(child(f), child(a)),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    child(binder_type),
                    child(body),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    child(binder_type),
                    child(body),
                    *binder_info,
                ),
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => Expr::let_e(
                    decl_name.clone(),
                    child(type_),
                    child(value),
                    child(body),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, child(expr)),
                _ => value.clone(),
            };
            done.insert(id, rebuilt);
        }
        Ok(done
            .remove(&root.allocation_identity())
            .expect("completed provenance traversal"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(label: &str) -> Name {
        Name::from_components(label.split('.'))
    }

    fn marker(name: &Name) -> KVMap {
        KVMap::from_entries(vec![(key(), DataValue::OfName(name.clone()))])
    }

    fn recursor_environment() -> fln_env::environment::Environment {
        let mut env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let Declaration::Inductive(boolean) = crate::seed::bool_seed_declaration() else {
            unreachable!();
        };
        for info in boolean
            .types
            .into_iter()
            .map(ConstantInfo::Induct)
            .chain(boolean.ctors.into_iter().map(ConstantInfo::Ctor))
            .chain(boolean.recursors.into_iter().map(ConstantInfo::Rec))
        {
            env = env.add_decl(info).unwrap();
        }
        env
    }

    #[test]
    fn macro_inline_provenance_refuses_malformed_or_forged_active_markers() {
        let env = recursor_environment();
        let recursor = n("Bool.rec");
        let value = Expr::const_(recursor.clone(), vec![Level::zero()]);
        assert_eq!(
            Context::new(&env, Budget::DEFAULT).source_rec_provenance(&marker(&recursor), &value),
            Ok(true)
        );
        for data in [
            KVMap::from_entries(vec![(key(), DataValue::OfNat(u64::MAX))]),
            KVMap::from_entries(vec![
                (key(), DataValue::OfName(recursor.clone())),
                (key(), DataValue::OfName(recursor.clone())),
            ]),
            KVMap::from_entries(vec![
                (key(), DataValue::OfName(recursor.clone())),
                (n("foreign"), DataValue::OfBool(true)),
            ]),
            KVMap::from_entries(vec![(
                Name::str(prefix(), "v2"),
                DataValue::OfName(recursor.clone()),
            )]),
            marker(&n("Nat.zero")),
        ] {
            assert!(matches!(
                Context::new(&env, Budget::DEFAULT).source_rec_provenance(&data, &value),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::InvalidMacroInlineProvenance
                ))
            ));
        }
        let zero = Expr::const_(n("Nat.zero"), vec![]);
        assert!(matches!(
            Context::new(&env, Budget::DEFAULT)
                .source_rec_provenance(&marker(&n("Nat.zero")), &zero),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::InvalidMacroInlineProvenance
            ))
        ));
        let mut limited = Context::new(&env, Budget::DEFAULT);
        limited.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            limited.source_rec_provenance(&marker(&recursor), &value),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }

    #[test]
    fn macro_inline_occurrence_marking_is_bounded_and_preserves_sharing() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let recursor = n("Nat.rec");
        let shared = Expr::const_(recursor.clone(), vec![Level::zero()]);
        let value = Expr::app(shared.clone(), shared);
        let mut complete = Context::new(&env, Budget::DEFAULT);
        let marked = complete
            .mark_source_recursors(&value, std::slice::from_ref(&recursor))
            .unwrap();
        let ExprNode::App { f, a } = marked.node() else {
            panic!("application preserved")
        };
        assert_eq!(f.allocation_identity(), a.allocation_identity());
        assert!(matches!(f.node(), ExprNode::MData { .. }));
        for allowance in 1..complete.txn.budget.heartbeats_consumed {
            let mut limited = Context::new(&env, Budget::DEFAULT);
            limited.txn.budget.max_heartbeats = allowance;
            let locals = limited.txn.lctx.clone();
            assert!(matches!(
                limited.mark_source_recursors(&value, std::slice::from_ref(&recursor)),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ));
            assert_eq!(limited.txn.lctx, locals);
            assert_eq!(limited.txn.env, env);
        }
    }

    #[test]
    fn macro_inline_explicit_occurrence_is_checked_after_an_unmarked_shared_node() {
        let env = recursor_environment();
        let recursor = n("Bool.rec");
        let Some(ConstantInfo::Rec(info)) = env.find(&recursor) else {
            panic!("Bool recursor")
        };
        let type_ = info.base.type_.clone();
        let levels = info
            .base
            .level_params
            .iter()
            .map(|name| Level::param(name.clone()))
            .collect();
        let value = Expr::const_(recursor.clone(), levels);
        let body = Expr::let_e(
            n("unmarked"),
            type_.clone(),
            value.clone(),
            Expr::mdata(marker(&recursor), value),
            false,
        );
        assert!(matches!(
            Context::new(&env, Budget::DEFAULT).check_definition_codegen(&Typed { type_, value: body }),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::UnsupportedRecursor(name)))
                if name == recursor
        ));
    }
}
