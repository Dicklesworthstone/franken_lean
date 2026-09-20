//! Completed instance answers, scoped to one search invocation.
//!
//! This is deliberately not a persistent cache: the environment, registry,
//! source options and ambient instance eligibility are fixed by the caller.
//! Exact local declarations and the active cycle-detection path are part of
//! each key. In particular, a dictionary selected below a cycle is not reused
//! where that cycle is absent (which could select a higher-priority instance).
//! Fresh, typed output holes are alpha-keyed; their selected values are replayed
//! by native unification, never by copying assignments. Cached open answers keep
//! lazy search continuations. Independent universe variants may share answer
//! keys without changing cycle-key equality. Open inputs, newly opened binders and
//! pending equations remain untabled.
//! Exhausted entries mean every candidate was tried under that exact key, not
//! that a resource limit, cancellation or temporarily blocked input was seen.
use super::*;
use std::collections::HashMap;

mod outputs;

const MAX_ENTRIES: usize = MAX_CANDIDATE_ATTEMPTS;
const MAX_KEY_UNITS: usize = 65_536;

#[derive(Clone, PartialEq, Eq)]
struct Key {
    expected: Expr,
    output_types: Vec<Expr>,
    syntax_units: usize,
    locals: LocalContext,
    ancestors: Vec<(Expr, Vec<Expr>)>,
}

impl Key {
    fn units(&self) -> usize {
        1 + self.syntax_units
            + self.output_types.len()
            + self.locals.len()
            + self
                .ancestors
                .iter()
                .map(|(_, types)| 1 + types.len())
                .sum::<usize>()
    }
}

fn ground(expr: &Expr) -> bool {
    !expr.has_expr_mvar() && !expr.has_level_mvar()
}

// Output slots are replaced by preparation; semi-output slots retain their
// original structure. Unknown ordinary inputs never reach a prepared frame.
fn replayable_target(context: &mut Context, frame: &Frame) -> Result<bool, NatDefinitionElabError> {
    if !frame.target.has_expr_mvar() {
        return Ok(true);
    }
    let mut target = &frame.target;
    let mut shape = &frame.key;
    let mut expected = &frame.expected;
    loop {
        context.tick()?;
        match (target.node(), shape.node(), expected.node()) {
            (
                ExprNode::App { f: tf, a: ta },
                ExprNode::App { f: sf, a: sa },
                ExprNode::App { f: ef, a: ea },
            ) => {
                let output = matches!(sa.node(), ExprNode::BVar { .. })
                    && matches!(ta.node(), ExprNode::MVar { .. });
                if !output && (ta != sa || ta != ea) {
                    return Ok(false);
                }
                target = tf;
                shape = sf;
                expected = ef;
            }
            _ => return Ok(target == shape && target == expected && !target.has_expr_mvar()),
        }
    }
}

fn ground_locals(
    context: &mut Context,
    locals: &LocalContext,
) -> Result<bool, NatDefinitionElabError> {
    for local in locals.decls() {
        context.tick()?;
        if !ground(&local.type_) || local.value.as_ref().is_some_and(|value| !ground(value)) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Fresh output names are not progress. Variant checks preserve the complete
/// pattern, aliasing, declared hole types and local scope; they assign nothing.
pub(super) fn same_goal(
    context: &mut Context,
    left: &Frame,
    right: &Frame,
) -> Result<bool, NatDefinitionElabError> {
    context.tick()?;
    if left.key == right.key {
        return Ok(true);
    }
    if !left.binders.is_empty()
        || !right.binders.is_empty()
        || left.base.txn.lctx != right.base.txn.lctx
        || !ground_locals(context, &left.base.txn.lctx)?
    {
        return Ok(false);
    }
    let Some(left) = outputs::cycle_key(context, left)? else {
        return Ok(false);
    };
    let Some(right) = outputs::cycle_key(context, right)? else {
        return Ok(false);
    };
    Ok(left.expected == right.expected && left.types == right.types)
}

fn replay_outputs(
    context: &mut Context,
    frame: &Frame,
    type_: &Expr,
) -> Result<bool, NatDefinitionElabError> {
    if ground(&frame.target) && frame.expected == *type_ {
        return Ok(true);
    }
    // Match a completed answer to BOTH the prepared target and original goal.
    // This propagates fresh outputs, without feeding known output values into
    // candidate selection or copying an old search's metavariable assignments.
    let mut trial = context.clone();
    trial.equations.push(SourceEquation::selection(
        type_.clone(),
        frame.target.clone(),
    ));
    trial.equations.push(SourceEquation::selection(
        type_.clone(),
        frame.expected.clone(),
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
    if ancestors.is_empty() || !frame.binders.is_empty() || !frame.base.equations.is_empty() {
        return Ok(None);
    }
    if !replayable_target(context, frame)? {
        return Ok(None);
    }
    let locals = &frame.base.txn.lctx;
    if 1 + locals.len() + ancestors.len() > MAX_KEY_UNITS {
        return Ok(None);
    }
    if !ground_locals(context, locals)? {
        return Ok(None);
    }
    let Some(canonical) = outputs::canonical_with_ancestors(context, frame, ancestors)? else {
        return Ok(None);
    };
    let mut syntax_units = canonical.units;
    let mut path = Vec::with_capacity(ancestors.len());
    let mut units = 1 + locals.len() + canonical.types.len() + syntax_units;
    for ancestor in ancestors {
        context.tick()?;
        let key = if !ancestor.key.has_expr_mvar() {
            // Such an open-universe ancestor participates only in exact cycle
            // equality. Keep its saved syntax, not the latest assignments.
            outputs::Canonical {
                expected: ancestor.key.clone(),
                types: Vec::new(),
                units: 0,
            }
        } else {
            let Some(key) = outputs::cycle_key(context, ancestor)? else {
                return Ok(None);
            };
            key
        };
        units += 1 + key.types.len() + key.units;
        if units > MAX_KEY_UNITS {
            return Ok(None);
        }
        syntax_units += key.units;
        path.push((key.expected, key.types));
    }
    Ok(Some(Key {
        expected: canonical.expected,
        output_types: canonical.types,
        syntax_units,
        locals: locals.clone(),
        ancestors: path,
    }))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Answer {
    Solved(Expr),
    Exhausted,
}

#[derive(Clone)]
struct Entry {
    answer: Answer,
    // Selected ground target for solved entries; key data for exhausted entries.
    // Exhausted entries never replay this field as a typing equation.
    type_: Expr,
}

#[derive(Default)]
pub(super) struct GroundTable {
    // Hashing selects a bucket only. Equality checks the complete key; no
    // result depends on hash iteration order or hash collision resistance.
    answers: HashMap<Expr, Vec<(Key, Entry)>>,
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
                    let usable = match &value.answer {
                        Answer::Solved(_) => replay_outputs(context, frame, &value.type_)?,
                        // Only complete, answer-free enumeration creates this
                        // entry. It is valid for the exact typed open query too.
                        Answer::Exhausted => true,
                    };
                    return Ok(usable.then(|| value.answer.clone()));
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
        let type_ = context.instantiate(&frame.target)?;
        if !ground(&type_) {
            return Ok(());
        }
        self.insert(
            context,
            frame,
            ancestors,
            Answer::Solved(value.clone()),
            type_,
        )
    }

    /// Called only after candidate enumeration is exhausted without an answer.
    /// Running out of alternatives after an earlier successful answer is NOT
    /// an empty result. Roots and ineligible open queries remain excluded, and
    /// resource stops return from search before this publication boundary.
    pub(super) fn exhausted(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
    ) -> Result<(), NatDefinitionElabError> {
        if frame.returned {
            return Ok(());
        }
        self.insert(
            context,
            frame,
            ancestors,
            Answer::Exhausted,
            frame.key.clone(),
        )
    }

    fn insert(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        ancestors: &[Frame],
        answer: Answer,
        type_: Expr,
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
        bucket.push((key, Entry { answer, type_ }));
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
            replay_first: false,
            returned: false,
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
    fn only_explicit_output_slots_can_replay_or_share_complete_exhaustion() {
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
        assert_eq!(table.entries, 1);
        assert_eq!(
            table.lookup(&mut context, &target, &path).unwrap(),
            Some(Answer::Exhausted)
        );
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
    fn open_outputs(names: &[&str], type_: Expr) -> Frame {
        let mut result = frame("C");
        for name in names {
            let id = MVarId(Name::from_components([*name]));
            result.base.txn.mvars.declare(
                id.clone(),
                id.0.clone(),
                type_.clone(),
                LocalContext::new(),
                MetavarKind::Natural,
                0,
                None,
            );
            let hole = Expr::mvar(id);
            result.expected = Expr::app(result.expected, hole.clone());
            result.target = Expr::app(result.target, hole);
            result.key = Expr::app(result.key, Expr::bvar(0).unwrap());
        }
        result
    }

    #[test]
    fn output_keys_preserve_alias_patterns_and_declared_types() {
        let mut context = context();
        let path = [frame("Root")];
        let first = open_outputs(&["x", "y"], Expr::sort(Level::one()));
        let renamed = open_outputs(&["a", "b"], Expr::sort(Level::one()));
        let aliased = open_outputs(&["a", "a"], Expr::sort(Level::one()));
        let differently_typed = open_outputs(&["a", "b"], Expr::sort(Level::zero()));
        let first_key = key(&mut context, &first, &path).unwrap().unwrap();
        assert!(Some(first_key.clone()) == key(&mut context, &renamed, &path).unwrap());
        assert!(Some(first_key.clone()) != key(&mut context, &aliased, &path).unwrap());
        assert!(Some(first_key) != key(&mut context, &differently_typed, &path).unwrap());
        assert!(first.expected.has_expr_mvar());
        assert!(renamed.expected.has_expr_mvar());
    }

    #[test]
    fn open_output_keys_refuse_opaque_deep_or_foreign_holes() {
        let mut context = context();
        let path = [frame("Root")];
        let id = MVarId(Name::from_components(["x"]));
        for (kind, depth) in [(MetavarKind::SyntheticOpaque, 0), (MetavarKind::Natural, 1)] {
            let mut target = open_outputs(&["x"], Expr::sort(Level::one()));
            target.base.txn.mvars.declare(
                id.clone(),
                id.0.clone(),
                Expr::sort(Level::one()),
                LocalContext::new(),
                kind,
                depth,
                None,
            );
            assert!(key(&mut context, &target, &path).unwrap().is_none());
        }
        let mut target = open_outputs(&["x"], Expr::sort(Level::one()));
        let local = FVarId(Name::from_components(["newer"]));
        target
            .base
            .txn
            .lctx
            .add_param(local.clone(), local.0, constant("C"), BinderInfo::Default);
        assert!(key(&mut context, &target, &path).unwrap().is_none());
        let target = open_outputs(
            &["x"],
            Expr::mvar(MVarId(Name::from_components(["unknownType"]))),
        );
        assert!(key(&mut context, &target, &path).unwrap().is_none());
    }

    #[test]
    fn spent_replay_work_survives_failure_without_assignments_or_equations() {
        let mut context = context();
        let target = open_outputs(&["x"], Expr::sort(Level::one()));
        context.txn.mvars = target.base.txn.mvars.clone();
        let before_mvars = context.txn.mvars.clone();
        let before_levels = context.txn.universes.clone();
        let before_work = context.txn.budget.heartbeats_consumed;
        let incompatible = Expr::app(constant("Other"), Expr::sort(Level::zero()));
        assert!(!replay_outputs(&mut context, &target, &incompatible).unwrap());
        assert_eq!(context.txn.mvars, before_mvars);
        assert_eq!(context.txn.universes, before_levels);
        assert!(context.equations.is_empty());
        assert!(context.txn.budget.heartbeats_consumed > before_work);
    }

    #[test]
    fn open_key_construction_stops_at_the_same_work_budget() {
        let mut context = context();
        let target = open_outputs(&["x", "y"], Expr::sort(Level::one()));
        let path = [frame("Root")];
        let before = target.base.txn.mvars.clone();
        context.txn.budget.max_heartbeats = 2;
        assert!(key(&mut context, &target, &path).is_err());
        assert_eq!(target.base.txn.mvars, before);
        assert!(context.txn.mvars.is_empty());
    }
    #[test]
    fn exhausted_output_queries_share_only_exact_typed_variants() {
        let mut context = context();
        let mut table = GroundTable::default();
        let path = [frame("Root")];
        let first = open_outputs(&["x"], Expr::sort(Level::one()));
        let renamed = open_outputs(&["y"], Expr::sort(Level::one()));
        table.exhausted(&mut context, &first, &path).unwrap();
        assert_eq!(
            table.lookup(&mut context, &renamed, &path).unwrap(),
            Some(Answer::Exhausted)
        );
        let different = open_outputs(&["y"], Expr::sort(Level::zero()));
        assert!(
            table
                .lookup(&mut context, &different, &path)
                .unwrap()
                .is_none()
        );
        assert!(
            table
                .lookup(&mut context, &renamed, &[frame("Other")])
                .unwrap()
                .is_none()
        );
        assert!(context.txn.mvars.is_empty());
    }

    #[test]
    fn running_out_of_alternatives_is_not_an_empty_search_result() {
        let mut context = context();
        let mut table = GroundTable::default();
        let path = [frame("Root")];
        let mut target = open_outputs(&["x"], Expr::sort(Level::one()));
        target.returned = true;
        // The first answer might not have been inserted (e.g. the key was
        // ineligible). Exhausting its continuation must not create a negative.
        table.exhausted(&mut context, &target, &path).unwrap();
        assert_eq!(table.entries, 0);
        assert!(
            table
                .lookup(&mut context, &target, &path)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn open_negative_key_exhaustion_publishes_nothing() {
        let mut context = context();
        let mut table = GroundTable::default();
        let target = open_outputs(&["x"], Expr::sort(Level::one()));
        let path = [frame("Root")];
        context.txn.budget.max_heartbeats = 3;
        assert!(table.exhausted(&mut context, &target, &path).is_err());
        assert!(table.answers.is_empty());
        assert_eq!(table.entries, 0);
        assert!(context.txn.mvars.is_empty());
    }

    #[test]
    fn semi_variants_preserve_hole_types_aliases_and_cycle_paths() {
        let mut context = context();
        let semi = |names: &[&str], type_: Expr| {
            let mut frame = open_outputs(names, type_);
            frame.key = frame.expected.clone();
            frame
        };
        let first = semi(&["x", "y"], Expr::sort(Level::one()));
        let renamed = semi(&["a", "b"], Expr::sort(Level::one()));
        let aliased = semi(&["a", "a"], Expr::sort(Level::one()));
        let different = semi(&["a", "b"], Expr::sort(Level::zero()));
        assert!(same_goal(&mut context, &first, &renamed).unwrap());
        assert!(!same_goal(&mut context, &first, &aliased).unwrap());
        assert!(!same_goal(&mut context, &first, &different).unwrap());
        let target = frame("Goal");
        let first_key = key(&mut context, &target, &[first]).unwrap().unwrap();
        assert!(Some(first_key.clone()) == key(&mut context, &target, &[renamed]).unwrap());
        assert!(Some(first_key.clone()) != key(&mut context, &target, &[aliased]).unwrap());
        assert!(Some(first_key) != key(&mut context, &target, &[different]).unwrap());
        assert!(context.txn.mvars.is_empty());
    }

    #[test]
    fn variant_cycles_do_not_cross_local_scopes_or_resource_stops() {
        let mut context = context();
        let mut first = open_outputs(&["x"], Expr::sort(Level::one()));
        first.key = first.expected.clone();
        let mut second = open_outputs(&["y"], Expr::sort(Level::one()));
        second.key = second.expected.clone();
        let id = FVarId(Name::from_components(["local"]));
        second
            .base
            .txn
            .lctx
            .add_param(id.clone(), id.0, constant("Nat"), BinderInfo::Default);
        assert!(!same_goal(&mut context, &first, &second).unwrap());
        second.base.txn.lctx = LocalContext::new();
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 1;
        let before = context.txn.mvars.clone();
        assert!(same_goal(&mut context, &first, &second).is_err());
        assert_eq!(context.txn.mvars, before);
    }

    #[test]
    fn universe_answer_variants_do_not_become_new_cycle_equivalences() {
        let mut context = context();
        let u = Level::mvar(LMVarId(Name::from_components(["u"])));
        let v = Level::mvar(LMVarId(Name::from_components(["v"])));
        let mut first = open_outputs(&["a"], Expr::sort(u));
        let mut second = open_outputs(&["b"], Expr::sort(v));
        // Semi-output variables retain their type graphs in cycle comparisons.
        first.key = first.expected.clone();
        second.key = second.expected.clone();
        assert!(!same_goal(&mut context, &first, &second).unwrap());
        assert!(same_goal(&mut context, &first, &first).unwrap());
        let path = [frame("Root")];
        let first_key = key(&mut context, &first, &path).unwrap().unwrap();
        assert!(Some(first_key) == key(&mut context, &second, &path).unwrap());
        assert!(context.txn.mvars.is_empty());
        assert!(context.txn.universes.is_empty());
    }

    #[test]
    fn exact_open_universe_ancestor_paths_still_separate_exhausted_answers() {
        let mut context = context();
        let query = open_outputs(&["a"], Expr::sort(Level::one()));
        let mut first_path = frame("Root");
        first_path.key = Expr::const_(
            Name::from_components(["Root"]),
            vec![Level::mvar(LMVarId(Name::from_components(["u"])))],
        );
        let mut second_path = frame("Root");
        second_path.key = Expr::const_(
            Name::from_components(["Root"]),
            vec![Level::mvar(LMVarId(Name::from_components(["v"])))],
        );
        let first_path = [first_path];
        let second_path = [second_path];
        let mut table = GroundTable::default();
        table.exhausted(&mut context, &query, &first_path).unwrap();
        assert_eq!(
            table.lookup(&mut context, &query, &first_path).unwrap(),
            Some(Answer::Exhausted)
        );
        assert!(
            table
                .lookup(&mut context, &query, &second_path)
                .unwrap()
                .is_none()
        );
        assert_eq!(table.entries, 1);
    }
}
