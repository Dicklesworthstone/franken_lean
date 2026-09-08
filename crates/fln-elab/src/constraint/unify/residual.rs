//! Conditional assignment checking for native unification.
//!
//! An assignment may mention unsolved metavariables. Instead of treating those
//! holes as constants or declaring them solved, build a universally quantified
//! typing obligation over their declared types. The ordinary kernel checks that
//! obligation. Locals and residual holes share a dependency graph: a type hole
//! may precede a local whose type mentions it, while a residual value may itself
//! depend on earlier locals. Scope compatibility includes the residual's entire
//! declared context, not just the free variables visible in its type.

use super::{Engine, UnificationDeferred, UnificationError};
use crate::lctx::LocalContext;
use crate::mvar::{AssignmentJustification, MetavarStore};
use fln_core::expr::{BinderInfo, Expr, FVarId, MVarId};
use fln_core::name::Name;
use std::cmp::Ordering;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Binding {
    Local(FVarId),
    Residual(MVarId),
}

struct PreparedBinding {
    binding: Binding,
    user_name: Name,
    domain: Expr,
    value: Option<Expr>,
    style: BinderInfo,
}

enum Task {
    Enter(Binding),
    Exit(PreparedBinding),
}

fn name_order(left: &Name, right: &Name) -> Ordering {
    if left == right {
        Ordering::Equal
    } else if left.lt(right) {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

fn binding_order(left: &Binding, right: &Binding) -> Ordering {
    match (left, right) {
        (Binding::Local(a), Binding::Local(b)) => name_order(&a.0, &b.0),
        (Binding::Residual(a), Binding::Residual(b)) => name_order(&a.0, &b.0),
        (Binding::Local(_), Binding::Residual(_)) => Ordering::Less,
        (Binding::Residual(_), Binding::Local(_)) => Ordering::Greater,
    }
}

impl Engine<'_> {
    fn validation_instantiate(
        &mut self,
        expr: &Expr,
        store: &MetavarStore,
    ) -> Result<Expr, UnificationError> {
        self.scan(expr)?;
        let expanded = store.instantiate(expr);
        self.scan(&expanded)?;
        let remaining = self
            .budget
            .max_visited_nodes
            .saturating_sub(self.meter.nodes);
        let result = self
            .work
            .universes
            .instantiate_expr_with_limit(&expanded, remaining)
            .map_err(UnificationError::Universe)?;
        self.scan(&result)?;
        Ok(result)
    }

    fn binding_reads(&mut self, expr: &Expr) -> Result<Vec<Binding>, UnificationError> {
        let expanded = self.instantiate(expr)?;
        let facts = self.scan(&expanded)?;
        let mut reads: Vec<_> = facts.fvars.into_iter().map(Binding::Local).collect();
        reads.extend(
            self.work
                .mvars
                .collect_mvars(&expanded)
                .into_iter()
                .map(Binding::Residual),
        );
        reads.sort_by(binding_order);
        reads.dedup();
        Ok(reads)
    }

    fn prepare_binding(
        &mut self,
        binding: Binding,
        target: &MVarId,
        allowed: &LocalContext,
        target_depth: u32,
    ) -> Result<(PreparedBinding, Vec<Binding>), UnificationError> {
        self.meter.tick()?;
        let (prepared, mut dependencies) = match &binding {
            Binding::Local(id) => {
                let position = allowed
                    .decls()
                    .iter()
                    .position(|local| &local.id == id)
                    .ok_or_else(|| {
                        UnificationError::Deferred(UnificationDeferred::EscapingLocal(
                            target.clone(),
                        ))
                    })?;
                let local = &allowed.decls()[position];
                let mut dependencies = Vec::new();
                // Preserve the original ordering of local declarations. Residual
                // type holes may be inserted before them, never reorder them.
                if position > 0 {
                    dependencies.push(Binding::Local(allowed.decls()[position - 1].id.clone()));
                }
                (
                    PreparedBinding {
                        binding: binding.clone(),
                        user_name: local.user_name.clone(),
                        domain: local.type_.clone(),
                        value: local.value.clone(),
                        style: local.binder_info,
                    },
                    dependencies,
                )
            }
            Binding::Residual(id) => {
                let declaration = self.work.mvars.get_decl(id).cloned().ok_or_else(|| {
                    UnificationError::Deferred(UnificationDeferred::UnknownMetavariable(id.clone()))
                })?;
                if declaration.depth > target_depth
                    || declaration.depth > self.budget.max_metavar_depth
                {
                    return Err(UnificationError::Deferred(
                        UnificationDeferred::MetavariableDepth(id.clone()),
                    ));
                }
                let mut dependencies = Vec::new();
                let mut seen = HashSet::new();
                for local in declaration.lctx.decls() {
                    self.meter.tick()?;
                    if !seen.insert(local.id.clone()) || allowed.find(&local.id) != Some(local) {
                        return Err(UnificationError::Deferred(
                            UnificationDeferred::EscapingLocal(target.clone()),
                        ));
                    }
                    dependencies.push(Binding::Local(local.id.clone()));
                }
                (
                    PreparedBinding {
                        binding: binding.clone(),
                        user_name: declaration.user_name,
                        domain: declaration.type_,
                        value: None,
                        style: BinderInfo::Default,
                    },
                    dependencies,
                )
            }
        };
        dependencies.extend(self.binding_reads(&prepared.domain)?);
        if let Some(value) = &prepared.value {
            dependencies.extend(self.binding_reads(value)?);
        }
        dependencies.sort_by(binding_order);
        dependencies.dedup();
        Ok((prepared, dependencies))
    }

    /// Return one closed conditional typing obligation and the exact residual
    /// metavariables quantified by it. The returned expressions are temporary
    /// kernel inputs; neither these binders nor the validation store is published.
    pub(super) fn prepare_assignment_check(
        &mut self,
        target: &MVarId,
    ) -> Result<(Expr, Expr, Vec<MVarId>), UnificationError> {
        let declaration = self
            .work
            .mvars
            .get_decl(target)
            .cloned()
            .expect("the unifier assigns only declared metavariables");
        let raw_value = self
            .work
            .mvars
            .get_assigned_expr(target)
            .cloned()
            .expect("a reported assignment exists");
        let mut roots = self.binding_reads(&raw_value)?;
        roots.extend(self.binding_reads(&declaration.type_)?);
        let mut local_ids = HashSet::new();
        for (index, local) in declaration.lctx.decls().iter().enumerate() {
            self.meter.tick()?;
            if !local_ids.insert(local.id.clone()) || local.index != index {
                return Err(UnificationError::Deferred(
                    UnificationDeferred::InvalidLocalContext,
                ));
            }
            roots.push(Binding::Local(local.id.clone()));
        }
        roots.sort_by(binding_order);
        roots.dedup();
        let mut tasks: Vec<_> = roots.into_iter().rev().map(Task::Enter).collect();
        let mut visiting = HashSet::new();
        let mut finished = HashSet::new();
        let mut validation_store = self.work.mvars.clone();
        let mut telescope = LocalContext::new();
        let mut residuals = Vec::new();
        while let Some(task) = tasks.pop() {
            self.meter.tick()?;
            match task {
                Task::Enter(binding) => {
                    if finished.contains(&binding) {
                        continue;
                    }
                    if !visiting.insert(binding.clone()) {
                        return Err(UnificationError::Deferred(
                            UnificationDeferred::UnresolvedAssignmentType(target.clone()),
                        ));
                    }
                    let (prepared, dependencies) = self.prepare_binding(
                        binding,
                        target,
                        &declaration.lctx,
                        declaration.depth,
                    )?;
                    tasks.push(Task::Exit(prepared));
                    tasks.extend(dependencies.into_iter().rev().map(Task::Enter));
                }
                Task::Exit(prepared) => {
                    let domain =
                        self.validation_instantiate(&prepared.domain, &validation_store)?;
                    let value = prepared
                        .value
                        .as_ref()
                        .map(|value| self.validation_instantiate(value, &validation_store))
                        .transpose()?;
                    for expr in std::iter::once(&domain).chain(value.iter()) {
                        if expr.has_expr_mvar() || expr.has_level_mvar() || expr.has_loose_bvars() {
                            return Err(UnificationError::Deferred(
                                UnificationDeferred::UnresolvedAssignmentType(target.clone()),
                            ));
                        }
                        if self
                            .scan(expr)?
                            .fvars
                            .iter()
                            .any(|id| !telescope.contains(id))
                        {
                            return Err(UnificationError::Deferred(
                                UnificationDeferred::EscapingLocal(target.clone()),
                            ));
                        }
                    }
                    match &prepared.binding {
                        Binding::Local(id) => {
                            if let Some(value) = value {
                                telescope.add_let(id.clone(), prepared.user_name, domain, value);
                            } else {
                                telescope.add_param(
                                    id.clone(),
                                    prepared.user_name,
                                    domain,
                                    prepared.style,
                                );
                            }
                        }
                        Binding::Residual(id) => {
                            let fresh = self.fresh()?;
                            // A residual is represented by a universally bound
                            // local only in this validation copy. Opaque goals
                            // remain unassigned and opaque in the actual store.
                            validation_store
                                .assign(
                                    id.clone(),
                                    Expr::fvar(fresh.clone()),
                                    AssignmentJustification::UserGiven,
                                )
                                .map_err(UnificationError::Metavariable)?;
                            telescope.add_param(
                                fresh,
                                prepared.user_name,
                                domain,
                                BinderInfo::Default,
                            );
                            residuals.push(id.clone());
                        }
                    }
                    visiting.remove(&prepared.binding);
                    finished.insert(prepared.binding);
                }
            }
        }
        let mut value = self.validation_instantiate(&raw_value, &validation_store)?;
        let mut type_ = self.validation_instantiate(&declaration.type_, &validation_store)?;
        for local in telescope.decls().iter().rev() {
            self.meter.tick()?;
            self.scan(&value)?;
            self.scan(&type_)?;
            value = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            type_ = type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| UnificationError::ExpressionScope)?;
            if let Some(local_value) = &local.value {
                value = Expr::let_e(
                    local.user_name.clone(),
                    local.type_.clone(),
                    local_value.clone(),
                    value,
                    false,
                );
                type_ = Expr::let_e(
                    local.user_name.clone(),
                    local.type_.clone(),
                    local_value.clone(),
                    type_,
                    false,
                );
            } else {
                value = Expr::lam(
                    local.user_name.clone(),
                    local.type_.clone(),
                    value,
                    local.binder_info,
                );
                type_ = Expr::forall_e(
                    local.user_name.clone(),
                    local.type_.clone(),
                    type_,
                    local.binder_info,
                );
            }
        }
        Ok((value, type_, residuals))
    }
}

#[cfg(test)]
mod tests {
    use super::super::UnificationBudget;
    use super::*;
    use crate::mvar::MetavarKind;
    use crate::seed::bootstrap_nat_environment;
    use crate::txn::ElabTxn;
    use fln_core::expr::{Literal, NatLit};
    use fln_core::level::Level;
    use fln_core::options::KVMap;
    use fln_kernel::verdict::Budget;

    fn name(value: &str) -> Name {
        Name::from_components([value])
    }
    fn nat() -> Expr {
        Expr::const_(name("Nat"), Vec::new())
    }
    fn number(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }
    fn budget() -> UnificationBudget {
        UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
    }
    fn transaction() -> ElabTxn {
        ElabTxn::new(
            bootstrap_nat_environment(budget().kernel).unwrap(),
            KVMap::new(),
            12,
        )
    }
    fn declare(txn: &mut ElabTxn, text: &str, type_: Expr, kind: MetavarKind) -> MVarId {
        let id = MVarId(name(text));
        txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            type_,
            txn.lctx.clone(),
            kind,
            0,
            None,
        );
        id
    }
    fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> FVarId {
        let id = FVarId(name(text));
        txn.lctx
            .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
        id
    }

    #[test]
    fn partial_alias_is_checked_but_its_residual_is_not_solved() {
        let mut txn = transaction();
        let a = declare(&mut txn, "a", nat(), MetavarKind::Natural);
        let b = declare(&mut txn, "b", nat(), MetavarKind::Natural);
        let before_lctx = txn.lctx.clone();
        let before_env = txn.env.clone();
        let report = txn
            .unify(&Expr::mvar(a.clone()), &Expr::mvar(b.clone()), budget())
            .unwrap();
        assert_eq!(report.residual_metavariables, vec![b.clone()]);
        assert_eq!(report.kernel_checks, 1);
        assert_eq!(
            txn.mvars.get_assigned_expr(&a),
            Some(&Expr::mvar(b.clone()))
        );
        assert!(!txn.mvars.is_assigned(&b));
        assert_eq!(txn.lctx, before_lctx);
        assert_eq!(txn.env, before_env);
        txn.unify(&Expr::mvar(b), &number(7), budget()).unwrap();
        assert_eq!(txn.instantiate_expr(&Expr::mvar(a)).unwrap(), number(7));
    }

    #[test]
    fn dependent_residual_types_are_abstracted_before_their_values() {
        let mut txn = transaction();
        let t = declare(
            &mut txn,
            "type",
            Expr::sort(Level::one()),
            MetavarKind::Natural,
        );
        let b = declare(
            &mut txn,
            "value",
            Expr::mvar(t.clone()),
            MetavarKind::Natural,
        );
        let a = declare(
            &mut txn,
            "target",
            Expr::mvar(t.clone()),
            MetavarKind::Natural,
        );
        let report = txn
            .unify(&Expr::mvar(a), &Expr::mvar(b.clone()), budget())
            .unwrap();
        assert_eq!(report.residual_metavariables, vec![t.clone(), b.clone()]);
        assert!(!txn.mvars.is_assigned(&t));
        assert!(!txn.mvars.is_assigned(&b));
    }

    #[test]
    fn residual_and_local_binders_are_topologically_interleaved() {
        let mut txn = transaction();
        let t = declare(
            &mut txn,
            "type",
            Expr::sort(Level::one()),
            MetavarKind::Natural,
        );
        local(&mut txn, "x", Expr::mvar(t.clone()));
        let b = declare(&mut txn, "b", Expr::mvar(t.clone()), MetavarKind::Natural);
        let a = declare(&mut txn, "a", Expr::mvar(t.clone()), MetavarKind::Natural);
        let report = txn
            .unify(&Expr::mvar(a), &Expr::mvar(b.clone()), budget())
            .unwrap();
        assert_eq!(report.residual_metavariables, vec![t.clone(), b.clone()]);
        assert!(!txn.mvars.is_assigned(&b));
        assert!(!txn.mvars.is_assigned(&t));
        assert_eq!(txn.lctx.len(), 1);
    }

    #[test]
    fn residual_context_cannot_hide_a_newer_free_variable() {
        let mut txn = transaction();
        let a = declare(&mut txn, "older", nat(), MetavarKind::Natural);
        local(&mut txn, "later", nat());
        let b = declare(&mut txn, "newer", nat(), MetavarKind::Natural);
        let before_mvars = txn.mvars.clone();
        let before_queue = txn.constraints.clone();
        assert!(matches!(
            txn.unify(&Expr::mvar(a), &Expr::mvar(b), budget()),
            Err(UnificationError::Deferred(
                UnificationDeferred::EscapingLocal(_)
            ))
        ));
        assert_eq!(txn.mvars, before_mvars);
        assert_eq!(txn.constraints, before_queue);
    }

    #[test]
    fn opaque_residuals_remain_opaque_in_the_real_store() {
        let mut txn = transaction();
        let a = declare(&mut txn, "a", nat(), MetavarKind::Natural);
        let b = declare(&mut txn, "opaque", nat(), MetavarKind::SyntheticOpaque);
        let report = txn
            .unify(&Expr::mvar(a), &Expr::mvar(b.clone()), budget())
            .unwrap();
        assert_eq!(report.residual_metavariables, vec![b.clone()]);
        assert!(!txn.mvars.is_assigned(&b));
        assert_eq!(
            txn.mvars.get_decl(&b).unwrap().kind,
            MetavarKind::SyntheticOpaque
        );
    }

    #[test]
    fn a_failed_conditional_check_defers_instead_of_rejecting_an_unsolved_type() {
        let mut txn = transaction();
        let t = declare(
            &mut txn,
            "type",
            Expr::sort(Level::one()),
            MetavarKind::Natural,
        );
        let a = declare(&mut txn, "a", Expr::mvar(t.clone()), MetavarKind::Natural);
        let before = txn.mvars.clone();
        assert!(matches!(
            txn.unify(&Expr::mvar(a), &number(9), budget()),
            Err(UnificationError::Deferred(
                UnificationDeferred::UnresolvedAssignmentType(_)
            ))
        ));
        assert_eq!(txn.mvars, before);
        assert!(!txn.mvars.is_assigned(&t));
    }

    #[test]
    fn declaration_type_cycles_are_not_followed_forever() {
        let mut txn = transaction();
        let b = MVarId(name("b"));
        let c = MVarId(name("c"));
        txn.mvars.declare(
            b.clone(),
            b.0.clone(),
            Expr::mvar(c.clone()),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        txn.mvars.declare(
            c.clone(),
            c.0.clone(),
            Expr::mvar(b.clone()),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let a = declare(&mut txn, "a", nat(), MetavarKind::Natural);
        let before = txn.mvars.clone();
        assert!(matches!(
            txn.unify(&Expr::mvar(a), &Expr::mvar(b), budget()),
            Err(UnificationError::Deferred(
                UnificationDeferred::UnresolvedAssignmentType(_)
            ))
        ));
        assert_eq!(txn.mvars, before);
    }

    #[test]
    fn dependent_function_patterns_can_retain_a_typed_residual_body() {
        let mut txn = transaction();
        let b = declare(&mut txn, "body", nat(), MetavarKind::Natural);
        let f = declare(
            &mut txn,
            "function",
            Expr::forall_e(name("x"), nat(), nat(), BinderInfo::Default),
            MetavarKind::Natural,
        );
        let x = local(&mut txn, "x", nat());
        let lhs = Expr::app(Expr::mvar(f.clone()), Expr::fvar(x));
        let report = txn.unify(&lhs, &Expr::mvar(b.clone()), budget()).unwrap();
        assert_eq!(report.residual_metavariables, vec![b.clone()]);
        assert!(!txn.mvars.is_assigned(&b));
        let assignment = txn.mvars.get_assigned_expr(&f).unwrap();
        assert!(!assignment.has_fvar());
        assert!(assignment.has_expr_mvar());
    }
}
