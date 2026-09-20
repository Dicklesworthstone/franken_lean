//! Ground instance answers, scoped to one search invocation.
//!
//! This is deliberately not a persistent cache: the environment, registry,
//! source options and ambient instance eligibility are fixed by the caller.
//! Exact local declarations and the active cycle-detection path are part of
//! each key. In particular, a dictionary selected below a cycle is not reused
//! where that cycle is absent (which could select a higher-priority instance).
//! Open original goals, newly opened binders and pending equations remain
//! untabled. Fixed output goals can share a solved answer, but must replay the
//! prepared output-hole equations transactionally before using it.
//! Exhausted entries mean every candidate was tried under that exact key, not
//! that a resource limit, cancellation or temporarily blocked input was seen.
use super::*;
use std::collections::HashMap;

const MAX_ENTRIES: usize = MAX_CANDIDATE_ATTEMPTS;
const MAX_KEY_UNITS: usize = 65_536;

#[derive(Clone, PartialEq, Eq)]
struct Key {
    expected: Expr,
    locals: LocalContext,
    ancestors: Vec<Expr>,
}

impl Key {
    fn units(&self) -> usize {
        1 + self.locals.len() + self.ancestors.len()
    }
}

fn ground(expr: &Expr) -> bool {
    !expr.has_expr_mvar() && !expr.has_level_mvar()
}

// A prepared target may differ from its ground original only at explicit
// output slots. Their fresh holes correspond to the top-level placeholders
// introduced by prepare_instance_target, never to arbitrary unknown inputs.
fn replayable_target(context: &mut Context, frame: &Frame) -> Result<bool, NatDefinitionElabError> {
    if ground(&frame.target) {
        return Ok(true);
    }
    if !ground(&frame.key) {
        return Ok(false);
    }
    let mut target = &frame.target;
    let mut shape = &frame.key;
    loop {
        context.tick()?;
        match (target.node(), shape.node()) {
            (ExprNode::App { f: tf, a: ta }, ExprNode::App { f: sf, a: sa }) => {
                let output = matches!(sa.node(), ExprNode::BVar { idx: 0 })
                    && matches!(ta.node(), ExprNode::MVar { .. });
                if !output && (ta != sa || !ground(ta)) {
                    return Ok(false);
                }
                target = tf;
                shape = sf;
            }
            _ => return Ok(target == shape && ground(target)),
        }
    }
}

fn replay_outputs(context: &mut Context, frame: &Frame) -> Result<bool, NatDefinitionElabError> {
    if ground(&frame.target) {
        return Ok(true);
    }
    // This is after selection of a previously completed answer at this exact
    // expected type. It must not feed known outputs into candidate selection.
    let mut trial = context.clone();
    trial.equations.push(SourceEquation::selection(
        frame.expected.clone(),
        frame.target.clone(),
    ));
    let result = trial.flush(true);
    context.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
    match result {
        Ok(()) => {
            *context = trial;
            Ok(true)
        }
        // A replay that cannot reconstruct the assignments is merely a cache
        // miss. Drop all speculative state, but never refund its charged work.
        Err(error) if nonmatch(&error) => Ok(false),
        Err(error) => Err(error),
    }
}

fn key(
    context: &mut Context,
    frame: &Frame,
    ancestors: &[Frame],
) -> Result<Option<Key>, NatDefinitionElabError> {
    context.tick()?;
    // The root may have a forced default-instance candidate. Never table it.
    if ancestors.is_empty()
        || !frame.binders.is_empty()
        || !frame.base.equations.is_empty()
        || !ground(&frame.expected)
    {
        return Ok(None);
    }
    if !replayable_target(context, frame)? {
        return Ok(None);
    }
    let locals = &frame.base.txn.lctx;
    if 1 + locals.len() + ancestors.len() > MAX_KEY_UNITS {
        return Ok(None);
    }
    for local in locals.decls() {
        context.tick()?;
        if !ground(&local.type_) || local.value.as_ref().is_some_and(|value| !ground(value)) {
            return Ok(None);
        }
    }
    for ancestor in ancestors {
        context.tick()?;
        if !ground(&ancestor.key) {
            return Ok(None);
        }
    }
    Ok(Some(Key {
        expected: frame.expected.clone(),
        locals: locals.clone(),
        ancestors: ancestors.iter().map(|frame| frame.key.clone()).collect(),
    }))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Answer {
    Solved(Expr),
    Exhausted,
}

#[derive(Default)]
pub(super) struct GroundTable {
    // Hashing selects a bucket only. Equality checks the complete key; no
    // result depends on hash iteration order or hash collision resistance.
    answers: HashMap<Expr, Vec<(Key, Answer)>>,
    entries: usize,
    key_units: usize,
}

impl GroundTable {
    pub(super) fn lookup(
        &self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
    ) -> Result<Option<Answer>, NatDefinitionElabError> {
        let Some(key) = key(context, frame, ancestors)? else {
            return Ok(None);
        };
        if let Some(bucket) = self.answers.get(&key.expected) {
            for (stored, value) in bucket {
                context.tick()?;
                if stored == &key {
                    let usable = match value {
                        Answer::Solved(_) => replay_outputs(context, frame)?,
                        // Negative answers do not summarize output selection.
                        Answer::Exhausted => ground(&frame.target),
                    };
                    return Ok(usable.then(|| value.clone()));
                }
            }
        }
        Ok(None)
    }

    pub(super) fn remember(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
        value: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !ground(value) {
            return Ok(());
        }
        self.insert(context, frame, ancestors, Answer::Solved(value.clone()))
    }

    /// Called only after candidate enumeration is exhausted. Roots, open goals
    /// and contexts with unresolved obligations are excluded by the same key
    /// eligibility rule as positive answers. There is no entry for a resource
    /// stop: those return immediately from search, before this boundary.
    pub(super) fn exhausted(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
    ) -> Result<(), NatDefinitionElabError> {
        if !ground(&frame.target) {
            return Ok(());
        }
        self.insert(context, frame, ancestors, Answer::Exhausted)
    }

    fn insert(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
        answer: Answer,
    ) -> Result<(), NatDefinitionElabError> {
        if self.entries >= MAX_ENTRIES {
            return Ok(());
        }
        let Some(key) = key(context, frame, ancestors)? else {
            return Ok(());
        };
        let units = key.units();
        if units > MAX_KEY_UNITS - self.key_units {
            // Full tables merely disable the optimization, not the search.
            return Ok(());
        }
        let bucket = self.answers.entry(key.expected.clone()).or_default();
        for (stored, _) in bucket.iter() {
            context.tick()?;
            if stored == &key {
                return Ok(());
            }
        }
        bucket.push((key, answer));
        self.entries += 1;
        self.key_units += units;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn constant(name: &str) -> Expr {
        Expr::const_(Name::from_components([name]), vec![])
    }
    fn frame(name: &str) -> Frame {
        Frame {
            goal: MVarId(Name::from_components(["goal"])),
            target: constant(name),
            expected: constant(name),
            key: constant(name),
            binders: vec![],
            base: context(),
            candidates: vec![],
            cursor: 0,
            chosen: None,
            children: vec![],
            resumable: false,
        }
    }

    #[test]
    fn exact_answer_is_shared_but_cycle_paths_are_not() {
        let mut context = context();
        let mut table = GroundTable::default();
        let target = frame("C");
        let path = [frame("Root"), frame("A")];
        let value = constant("dictionary");
        table
            .remember(&mut context, &target, &path, &value)
            .unwrap();
        assert_eq!(
            table.lookup(&mut context, &target, &path).unwrap(),
            Some(Answer::Solved(value))
        );
        for other in [vec![], vec![frame("Root")], vec![frame("Root"), frame("B")]] {
            assert!(
                table
                    .lookup(&mut context, &target, &other)
                    .unwrap()
                    .is_none()
            );
        }
        assert!(
            table
                .lookup(&mut context, &frame("Other"), &path)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn exhaustion_is_scoped_and_never_hides_open_goals() {
        let mut context = context();
        let mut table = GroundTable::default();
        let target = frame("C");
        let path = [frame("Root"), frame("A")];
        table.exhausted(&mut context, &target, &path).unwrap();
        assert_eq!(
            table.lookup(&mut context, &target, &path).unwrap(),
            Some(Answer::Exhausted)
        );
        assert!(
            table
                .lookup(&mut context, &target, &[frame("Root")])
                .unwrap()
                .is_none()
        );
        let mut open = frame("C");
        open.target = Expr::mvar(MVarId(Name::from_components(["open"])));
        table.exhausted(&mut context, &open, &path).unwrap();
        assert!(table.lookup(&mut context, &open, &path).unwrap().is_none());
        assert_eq!(table.entries, 1);
        let fresh = GroundTable::default();
        assert!(
            fresh
                .lookup(&mut context, &target, &path)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn only_explicit_output_slots_can_replay_and_failure_is_not_tabled() {
        let mut context = context();
        let mut table = GroundTable::default();
        let path = [frame("Root")];
        let mut target = frame("C");
        let hole = Expr::mvar(MVarId(Name::from_components(["output"])));
        target.expected = Expr::app(constant("C"), constant("Nat"));
        target.target = Expr::app(constant("C"), hole.clone());
        target.key = Expr::app(constant("C"), Expr::bvar(0).unwrap());
        assert!(key(&mut context, &target, &path).unwrap().is_some());
        table.exhausted(&mut context, &target, &path).unwrap();
        assert_eq!(table.entries, 0);
        target.key = target.target.clone();
        assert!(key(&mut context, &target, &path).unwrap().is_none());
        target.key = Expr::app(constant("C"), Expr::bvar(0).unwrap());
        target.expected = Expr::app(constant("C"), hole);
        assert!(key(&mut context, &target, &path).unwrap().is_none());
    }

    #[test]
    fn resource_exhaustion_never_publishes_a_negative_answer() {
        let mut context = context();
        let mut table = GroundTable::default();
        let target = frame("C");
        let path = [frame("Root")];
        context.tick().unwrap(); // A zero limit denotes an unlimited budget.
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed;
        assert!(table.exhausted(&mut context, &target, &path).is_err());
        assert_eq!(table.entries, 0);
        assert!(table.answers.is_empty());
    }

    #[test]
    fn local_let_values_and_instance_recency_are_part_of_the_key() {
        let mut context = context();
        let mut table = GroundTable::default();
        let mut target = frame("C");
        let id = FVarId(Name::from_components(["local"]));
        target
            .base
            .txn
            .lctx
            .add_let(id.clone(), id.0.clone(), constant("C"), constant("one"));
        let path = [frame("Root")];
        table
            .remember(&mut context, &target, &path, &Expr::fvar(id.clone()))
            .unwrap();
        let mut other = frame("C");
        other
            .base
            .txn
            .lctx
            .add_let(id.clone(), id.0.clone(), constant("C"), constant("two"));
        assert!(table.lookup(&mut context, &other, &path).unwrap().is_none());
        let newer = FVarId(Name::from_components(["newer"]));
        target.base.txn.lctx.add_param(
            newer.clone(),
            newer.0,
            constant("C"),
            BinderInfo::InstImplicit,
        );
        assert!(
            table
                .lookup(&mut context, &target, &path)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn unresolved_goals_contexts_and_values_never_enter_the_table() {
        let mut context = context();
        let mut table = GroundTable::default();
        let path = [frame("Root")];
        let hole = Expr::mvar(MVarId(Name::from_components(["hole"])));
        let mut target = frame("C");
        target.target = hole.clone();
        table
            .remember(&mut context, &target, &path, &constant("v"))
            .unwrap();
        target.target = constant("C");
        target.expected = hole.clone();
        table
            .remember(&mut context, &target, &path, &constant("v"))
            .unwrap();
        target.expected = constant("C");
        table.remember(&mut context, &target, &path, &hole).unwrap();
        let id = FVarId(Name::from_components(["local"]));
        target
            .base
            .txn
            .lctx
            .add_param(id.clone(), id.0, hole, BinderInfo::Default);
        table
            .remember(&mut context, &target, &path, &constant("v"))
            .unwrap();
        assert_eq!(table.entries, 0);
    }

    #[test]
    fn capacity_only_disables_insertion_and_lookups_charge_work() {
        let mut context = context();
        let target = frame("C");
        let path = [frame("Root")];
        let mut table = GroundTable {
            key_units: MAX_KEY_UNITS,
            ..GroundTable::default()
        };
        table
            .remember(&mut context, &target, &path, &constant("v"))
            .unwrap();
        assert_eq!(table.entries, 0);
        let before = context.txn.budget.heartbeats_consumed;
        assert!(
            table
                .lookup(&mut context, &target, &path)
                .unwrap()
                .is_none()
        );
        assert!(context.txn.budget.heartbeats_consumed > before);
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed;
        assert!(table.lookup(&mut context, &target, &path).is_err());
    }
}
