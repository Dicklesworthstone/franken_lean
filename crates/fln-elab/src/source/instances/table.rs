//! Ground instance answers, scoped to one search invocation.
//!
//! This is deliberately not a persistent cache: the environment, registry,
//! source options and ambient instance eligibility are fixed by the caller.
//! Exact local declarations and the active cycle-detection path are part of
//! each key. In particular, a dictionary selected below a cycle is not reused
//! where that cycle is absent (which could select a higher-priority instance).
//! Open goals, newly opened binders and pending equations remain untabled.
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

fn key(
    context: &mut Context,
    frame: &Frame,
    ancestors: &[Frame],
) -> Result<Option<Key>, NatDefinitionElabError> {
    context.tick()?;
    // The root may have a forced default-instance candidate. Never table it.
    // Requiring the prepared target to be ground also excludes the fresh
    // output holes whose assignments a shortcut would otherwise have to replay.
    if ancestors.is_empty()
        || !frame.binders.is_empty()
        || !frame.base.equations.is_empty()
        || !ground(&frame.expected)
        || !ground(&frame.target)
    {
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

#[derive(Default)]
pub(super) struct GroundTable {
    // Hashing selects a bucket only. Equality checks the complete key; no
    // result depends on hash iteration order or hash collision resistance.
    answers: HashMap<Expr, Vec<(Key, Expr)>>,
    entries: usize,
    key_units: usize,
}

impl GroundTable {
    pub(super) fn lookup(
        &self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(key) = key(context, frame, ancestors)? else {
            return Ok(None);
        };
        if let Some(bucket) = self.answers.get(&key.expected) {
            for (stored, value) in bucket {
                context.tick()?;
                if stored == &key {
                    return Ok(Some(value.clone()));
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
        if self.entries >= MAX_ENTRIES || !ground(value) {
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
        bucket.push((key, value.clone()));
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
            Some(value)
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
