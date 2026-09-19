//! Execution of explicit delayed-assignment queue rows (plan 10.1/10.2).
//!
//! A delayed assignment has a designated output. It is not an unoriented DefEq
//! that may silently assign the value's holes instead. Build its typed telescope,
//! try only the requested assignment, and replay the original relation. Ordinary
//! equation/type progress can unblock another attempt; neither a refusal nor an
//! assigned target lets the queue bypass the parent's K1 publication barrier.
use super::*;

pub(in crate::constraint) struct DelayedConstraint {
    pub id: ConstraintId,
    pub mvar: MVarId,
    pub fvars: Vec<FVarId>,
    pub val: Expr,
    pub depth: u32,
}

impl Engine<'_> {
    pub(super) fn resume_delayed_assignment(
        &mut self,
        obligation: &DelayedConstraint,
        pending: &mut VecDeque<Equation>,
    ) -> Result<(), UnificationError> {
        self.meter.node()?;
        let declaration = self.work.mvars.get_decl(&obligation.mvar).ok_or_else(|| {
            UnificationError::Deferred(UnificationDeferred::UnknownMetavariable(
                obligation.mvar.clone(),
            ))
        })?;
        if declaration.depth > obligation.depth || declaration.depth > self.budget.max_metavar_depth
        {
            return Err(UnificationError::Deferred(
                UnificationDeferred::MetavariableDepth(obligation.mvar.clone()),
            ));
        }
        if declaration.kind == MetavarKind::SyntheticOpaque
            && !self.work.mvars.is_assigned(&obligation.mvar)
        {
            return Err(UnificationError::Deferred(
                UnificationDeferred::OpaqueMetavariable(obligation.mvar.clone()),
            ));
        }
        let mut type_ = declaration.type_.clone();
        for _ in self.work.lctx.decls() {
            self.meter.node()?;
        }
        let locals = self.work.lctx.clone();
        let mut distinct = HashSet::new();
        let mut applied = Expr::mvar(obligation.mvar.clone());
        let mut staged = VecDeque::new();
        for id in &obligation.fvars {
            self.meter.node()?;
            let Some(local) = locals.find(id) else {
                return Err(UnificationError::Deferred(UnificationDeferred::NotAPattern));
            };
            if local.is_let() || !distinct.insert(id.clone()) {
                return Err(UnificationError::Deferred(UnificationDeferred::NotAPattern));
            }
            type_ = self.whnf(&type_, &locals)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                return Err(UnificationError::Deferred(UnificationDeferred::NotAPattern));
            };
            // K1 checks the resulting lambda at its declared domain. Also check
            // that the actual local passed to that domain has the right type:
            // lambda abstraction alone could otherwise hide a malformed row.
            for _ in locals.decls() {
                self.meter.node()?;
            }
            staged.push_back((local.type_.clone(), binder_type.clone(), locals.clone()));
            let argument = Expr::fvar(id.clone());
            type_ = self.substitute(body, &argument)?;
            applied = Expr::app(applied, argument);
        }
        self.scan(&applied)?;
        if !self.work.mvars.is_assigned(&obligation.mvar)
            && !self.pattern(&applied, &obligation.val, &locals, &mut staged)?
        {
            return Err(UnificationError::Deferred(
                UnificationDeferred::UnresolvedDelayedAssignment(obligation.id),
            ));
        }
        // Discharge only after checking the original application as well as its
        // necessary domain/type equations. Each retry is generation-gated by
        // solve; a blocked request never reschedules itself without progress.
        staged.push_back((applied, obligation.val.clone(), locals));
        pending.extend(staged);
        Ok(())
    }
}
