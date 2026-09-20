//! Scope-aware output templates. Loose variables are private key placeholders,
//! raised under each binder; templates never enter the unifier or the kernel.
use super::*;

mod levels;

struct HoleSlot {
    position: u32,
    complete: bool,
}

enum HoleStep {
    Ready(Expr),
    CheckType(Expr),
}

#[derive(Default)]
pub(super) struct Templates {
    holes: HashMap<MVarId, HoleSlot>,
    pub types: Vec<Expr>,
    done: HashMap<(Expr, u32), Expr>,
    levels: levels::LevelTemplates,
}

impl Templates {
    pub fn anchor(
        &mut self,
        context: &mut Context,
        ancestors: &[Frame],
    ) -> Result<bool, NatDefinitionElabError> {
        self.levels.anchor(context, ancestors)
    }

    pub fn units(&self) -> usize {
        self.done.len() + self.levels.units()
    }

    // Hole types belong to the frame's saved context, not to any lexical binder
    // in the expression currently being traversed. Check their complete graph
    // at depth zero on the same heap worklist. An unfinished slot is a cycle,
    // not a usable forward declaration. Nothing is assigned in either context.
    fn hole(&mut self, frame: &Frame, id: &MVarId, depth: u32, finish: bool) -> Option<HoleStep> {
        if finish {
            let slot = self.holes.get_mut(id)?;
            let original_type = &frame.base.txn.mvars.get_decl(id)?.type_;
            let type_ = self.done.get(&(original_type.clone(), 0))?;
            self.types[slot.position as usize - 1] = type_.clone();
            slot.complete = true;
            return Some(HoleStep::Ready(
                Expr::bvar(depth.checked_add(slot.position)?).ok()?,
            ));
        }
        if let Some(slot) = self.holes.get(id) {
            if !slot.complete {
                return None;
            }
            return Some(HoleStep::Ready(
                Expr::bvar(depth.checked_add(slot.position)?).ok()?,
            ));
        }
        let decl = frame.base.txn.mvars.get_decl(id)?;
        if decl.kind != MetavarKind::Natural
            || decl.depth != 0
            || decl.delayed.is_some()
            || frame.base.txn.mvars.is_assigned(id)
            || decl.lctx != frame.base.txn.lctx
            || decl.type_.has_loose_bvars()
        {
            return None;
        }
        let position = u32::try_from(self.types.len() + 1).ok()?;
        self.types.push(decl.type_.clone());
        self.holes.insert(
            id.clone(),
            HoleSlot {
                position,
                complete: false,
            },
        );
        Some(HoleStep::CheckType(decl.type_.clone()))
    }

    /// Every expression container is traversed by heap continuation. Memoization
    /// is scoped by binder depth, so shared open syntax cannot capture a binder.
    /// A full key budget disables reuse rather than terminating instance search.
    pub fn rewrite(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        root: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut pending = vec![(root.clone(), 0u32, false)];
        while let Some((expr, depth, finish)) = pending.pop() {
            context.tick()?;
            let key = (expr.clone(), depth);
            if self.done.contains_key(&key) {
                continue;
            }
            if self.units() + self.holes.len() + pending.len() >= MAX_KEY_UNITS {
                return Ok(None);
            }
            if ground(&expr) {
                self.done.insert(key, expr);
                continue;
            }
            match expr.node() {
                ExprNode::Sort { level } => {
                    let Some(level) = self.levels.rewrite(context, frame, level)? else {
                        return Ok(None);
                    };
                    self.done.insert(key, Expr::sort(level));
                    continue;
                }
                ExprNode::Const { name, levels } => {
                    if levels.len() > MAX_KEY_UNITS.saturating_sub(self.units()) {
                        return Ok(None);
                    }
                    let mut rewritten = Vec::with_capacity(levels.len());
                    for level in levels {
                        let Some(level) = self.levels.rewrite(context, frame, level)? else {
                            return Ok(None);
                        };
                        rewritten.push(level);
                    }
                    self.done.insert(key, Expr::const_(name.clone(), rewritten));
                    continue;
                }
                _ => {}
            }
            if let ExprNode::MVar { id } = expr.node() {
                match self.hole(frame, id, depth, finish) {
                    Some(HoleStep::Ready(value)) => {
                        self.done.insert(key, value);
                    }
                    Some(HoleStep::CheckType(type_)) => {
                        pending.push((expr, depth, true));
                        pending.push((type_, 0, false));
                    }
                    None => return Ok(None),
                }
                continue;
            }
            if !finish {
                pending.push((expr.clone(), depth, true));
                match expr.node() {
                    ExprNode::App { f, a } => {
                        pending.push((a.clone(), depth, false));
                        pending.push((f.clone(), depth, false));
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        pending.push((body.clone(), depth + 1, false));
                        pending.push((binder_type.clone(), depth, false));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        pending.push((body.clone(), depth + 1, false));
                        pending.push((value.clone(), depth, false));
                        pending.push((type_.clone(), depth, false));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        pending.push((expr.clone(), depth, false));
                    }
                    _ => return Ok(None),
                }
                continue;
            }
            let child = |expr: &Expr, depth: u32| {
                self.done
                    .get(&(expr.clone(), depth))
                    .expect("planned output child")
                    .clone()
            };
            let value = match expr.node() {
                ExprNode::App { f, a } => Expr::app(child(f, depth), child(a, depth)),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    child(binder_type, depth),
                    child(body, depth + 1),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    child(binder_type, depth),
                    child(body, depth + 1),
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
                    child(type_, depth),
                    child(value, depth),
                    child(body, depth + 1),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr, depth)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, child(expr, depth)),
                _ => return Ok(None),
            };
            self.done.insert(key, value);
        }
        Ok(self.done.get(&(root.clone(), 0)).cloned())
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
    fn frame(pattern: Expr) -> Frame {
        let mut base = context();
        let id = MVarId(Name::from_components(["x"]));
        base.txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            Expr::sort(Level::one()),
            LocalContext::new(),
            MetavarKind::Natural,
            0,
            None,
        );
        Frame {
            goal: MVarId(Name::from_components(["goal"])),
            target: Expr::app(constant("C"), Expr::mvar(id)),
            expected: Expr::app(constant("C"), pattern),
            key: Expr::app(constant("C"), Expr::bvar(0).unwrap()),
            binders: Vec::new(),
            base,
            candidates: Vec::new(),
            cursor: 0,
            chosen: None,
            children: Vec::new(),
            resumable: true,
            replay_first: false,
            returned: false,
        }
    }
    fn hole() -> Expr {
        Expr::mvar(MVarId(Name::from_components(["x"])))
    }

    #[test]
    fn every_container_preserves_its_data_and_raises_only_key_placeholders() {
        let nat = constant("Nat");
        let name = Name::from_components(["n"]);
        let x = hole();
        let marker = Expr::bvar(1).unwrap();
        let raised = Expr::bvar(2).unwrap();
        let identity = Expr::lam(
            name.clone(),
            nat.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let pairs = [
            (
                Expr::app(identity.clone(), x.clone()),
                Expr::app(identity, marker.clone()),
            ),
            (
                Expr::lam(name.clone(), nat.clone(), x.clone(), BinderInfo::Implicit),
                Expr::lam(
                    name.clone(),
                    nat.clone(),
                    raised.clone(),
                    BinderInfo::Implicit,
                ),
            ),
            (
                Expr::forall_e(
                    name.clone(),
                    nat.clone(),
                    x.clone(),
                    BinderInfo::InstImplicit,
                ),
                Expr::forall_e(
                    name.clone(),
                    nat.clone(),
                    raised.clone(),
                    BinderInfo::InstImplicit,
                ),
            ),
            (
                Expr::let_e(name.clone(), x.clone(), x.clone(), x.clone(), true),
                Expr::let_e(name.clone(), marker.clone(), marker.clone(), raised, true),
            ),
            (
                Expr::mdata(KVMap::new(), x.clone()),
                Expr::mdata(KVMap::new(), marker.clone()),
            ),
            (Expr::proj(name.clone(), 5, x), Expr::proj(name, 5, marker)),
        ];
        let mut context = context();
        for (pattern, expected) in pairs {
            let input = frame(pattern);
            let before = input.base.txn.mvars.clone();
            let output = canonical(&mut context, &input).unwrap().unwrap();
            assert_eq!(output.expected, Expr::app(constant("C"), expected));
            assert_eq!(output.types, vec![Expr::sort(Level::one())]);
            assert!(output.units > 1);
            assert_eq!(input.base.txn.mvars, before);
        }
    }

    #[test]
    fn shared_holes_under_distinct_binder_depths_do_not_capture_locals() {
        let name = Name::from_components(["n"]);
        let pattern = Expr::app(
            hole(),
            Expr::lam(name.clone(), constant("Nat"), hole(), BinderInfo::Default),
        );
        let output = canonical(&mut context(), &frame(pattern)).unwrap().unwrap();
        let expected = Expr::app(
            Expr::bvar(1).unwrap(),
            Expr::lam(
                name,
                constant("Nat"),
                Expr::bvar(2).unwrap(),
                BinderInfo::Default,
            ),
        );
        assert_eq!(output.expected, Expr::app(constant("C"), expected));
        assert_eq!(output.types.len(), 1);
    }

    #[test]
    fn shared_output_dags_are_linear_and_deep_binders_use_the_heap() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut pattern = hole();
                for _ in 0..40 {
                    pattern = Expr::app(Expr::app(constant("Pair"), pattern.clone()), pattern);
                }
                let mut context = context();
                context.txn.budget.max_heartbeats = 1000;
                let result = canonical(&mut context, &frame(pattern)).unwrap().unwrap();
                assert!(result.units < 200);
                assert!(!result.expected.has_expr_mvar());
                assert_eq!(result.types.len(), 1);
                let mut pattern = hole();
                for _ in 0..2000 {
                    pattern = Expr::forall_e(
                        Name::anonymous(),
                        constant("Nat"),
                        pattern,
                        BinderInfo::Default,
                    );
                }
                context.txn.budget.max_heartbeats = 20_000;
                let result = canonical(&mut context, &frame(pattern)).unwrap().unwrap();
                assert!(result.units < 5000);
                assert_eq!(result.types.len(), 1);
                assert!(result.expected.has_loose_bvars());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn key_resources_never_mutate_the_live_or_original_hole_stores() {
        let mut pattern = hole();
        for _ in 0..30 {
            pattern = Expr::app(constant("Box"), pattern);
        }
        let input = frame(pattern);
        let before = input.base.txn.mvars.clone();
        let mut context = context();
        context.txn.budget.max_heartbeats = 10;
        assert!(canonical(&mut context, &input).is_err());
        assert_eq!(input.base.txn.mvars, before);
        assert!(context.txn.mvars.is_empty());
        context.txn.budget.max_heartbeats = 0;
        let mut table = GroundTable {
            key_units: MAX_KEY_UNITS - 5,
            ..GroundTable::default()
        };
        table
            .exhausted(&mut context, &input, &[frame(constant("Root"))])
            .unwrap();
        assert_eq!(table.entries, 0);
        assert!(table.answers.is_empty());
    }

    #[test]
    fn preexisting_loose_variables_cannot_impersonate_template_holes() {
        let mut context = context();
        for pattern in [
            Expr::bvar(1).unwrap(),
            Expr::app(hole(), Expr::bvar(0).unwrap()),
        ] {
            assert!(canonical(&mut context, &frame(pattern)).unwrap().is_none());
        }
        let input = frame(Expr::app(
            constant("Box"),
            Expr::mvar(MVarId(Name::from_components(["foreign"]))),
        ));
        assert!(canonical(&mut context, &input).unwrap().is_none());
    }

    fn declare(input: &mut Frame, name: &str, type_: Expr) -> Expr {
        let id = MVarId(Name::from_components([name]));
        input.base.txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            type_,
            input.base.txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        Expr::mvar(id)
    }

    fn dependent_pattern(type_name: &str, value_name: &str) -> Frame {
        let mut input = frame(constant("unused"));
        let type_ = declare(&mut input, type_name, Expr::sort(Level::one()));
        let value = declare(&mut input, value_name, type_.clone());
        input.expected = Expr::app(Expr::app(constant("D"), type_), value);
        input.target = input.expected.clone();
        input.key = Expr::app(
            Expr::app(constant("D"), Expr::bvar(0).unwrap()),
            Expr::bvar(0).unwrap(),
        );
        input
    }

    #[test]
    fn dependent_keys_share_exact_typed_graphs_not_generated_hole_names() {
        let first = dependent_pattern("A", "a");
        let second = dependent_pattern("B", "b");
        let mut context = context();
        let left = canonical(&mut context, &first).unwrap().unwrap();
        let right = canonical(&mut context, &second).unwrap().unwrap();
        assert_eq!(left.expected, right.expected);
        assert_eq!(left.types, right.types);
        assert_eq!(
            left.types,
            vec![Expr::sort(Level::one()), Expr::bvar(1).unwrap()]
        );
        // Same apparent goal shape, but a is declared in a different type.
        let mut other = dependent_pattern("A", "a");
        let foreign_type = declare(&mut other, "B", Expr::sort(Level::one()));
        declare(&mut other, "a", foreign_type);
        let other = canonical(&mut context, &other).unwrap().unwrap();
        assert_eq!(left.expected, other.expected);
        assert_ne!(left.types, other.types);
        assert_eq!(other.types.len(), 3);
    }

    #[test]
    fn type_dependencies_are_discovered_even_when_only_the_value_is_visible() {
        let mut input = frame(constant("unused"));
        let type_ = declare(&mut input, "A", Expr::sort(Level::one()));
        let value = declare(&mut input, "a", type_);
        let pattern = Expr::lam(
            Name::anonymous(),
            constant("Nat"),
            value,
            BinderInfo::Default,
        );
        input.expected = Expr::app(constant("C"), pattern);
        let result = canonical(&mut context(), &input).unwrap().unwrap();
        assert_eq!(
            result.types,
            vec![Expr::bvar(2).unwrap(), Expr::sort(Level::one())]
        );
        // The value placeholder is raised under the lambda, its saved type is not.
        assert_eq!(
            result.expected,
            Expr::app(
                constant("C"),
                Expr::lam(
                    Name::anonymous(),
                    constant("Nat"),
                    Expr::bvar(2).unwrap(),
                    BinderInfo::Default,
                )
            )
        );
    }

    #[test]
    fn cyclic_hole_typing_dependencies_are_not_accepted_as_forward_declarations() {
        for mutual in [false, true] {
            let mut input = frame(hole());
            let next = if mutual { "y" } else { "x" };
            declare(
                &mut input,
                "x",
                Expr::mvar(MVarId(Name::from_components([next]))),
            );
            if mutual {
                declare(&mut input, "y", hole());
            }
            let before = input.base.txn.mvars.clone();
            let mut context = context();
            context.txn.budget.max_heartbeats = 100;
            assert!(canonical(&mut context, &input).unwrap().is_none());
            assert_eq!(input.base.txn.mvars, before);
            assert!(context.txn.mvars.is_empty());
        }
    }

    #[test]
    fn dependency_holes_keep_kind_depth_and_scope_refusals() {
        for (kind, depth, foreign_scope) in [
            (MetavarKind::SyntheticOpaque, 0, false),
            (MetavarKind::Natural, 1, false),
            (MetavarKind::Natural, 0, true),
        ] {
            let mut input = dependent_pattern("A", "a");
            let id = MVarId(Name::from_components(["A"]));
            let mut locals = LocalContext::new();
            if foreign_scope {
                let fvar = FVarId(Name::from_components(["private"]));
                locals.add_param(fvar.clone(), fvar.0, constant("Nat"), BinderInfo::Default);
            }
            input.base.txn.mvars.declare(
                id.clone(),
                id.0,
                Expr::sort(Level::one()),
                locals,
                kind,
                depth,
                None,
            );
            assert!(canonical(&mut context(), &input).unwrap().is_none());
        }
        let mut input = dependent_pattern("A", "a");
        declare(&mut input, "A", Expr::bvar(1).unwrap());
        assert!(canonical(&mut context(), &input).unwrap().is_none());
    }

    #[test]
    fn deep_and_shared_hole_type_graphs_are_heap_bound_and_metered() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut input = frame(hole());
                let mut current = Expr::sort(Level::one());
                for n in 0..2000 {
                    current = declare(&mut input, &format!("T{n}"), current);
                }
                declare(&mut input, "x", current);
                let original = input.base.txn.mvars.clone();
                let mut context = context();
                context.txn.budget.max_heartbeats = 20_000;
                let result = canonical(&mut context, &input).unwrap().unwrap();
                assert_eq!(result.types.len(), 2001);
                assert!(result.units < 5000);
                assert!(result.types.iter().all(|type_| !type_.has_expr_mvar()));
                assert_eq!(input.base.txn.mvars, original);
                // Term and typing walks share one budget, rather than restarting
                // it for every declaration in the dependency graph.
                context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 20;
                assert!(canonical(&mut context, &input).is_err());
                assert_eq!(input.base.txn.mvars, original);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    fn uvar(name: &str) -> Level {
        Level::mvar(LMVarId(Name::from_components([name])))
    }
    fn polymorphic_frame(name: &str) -> Frame {
        let mut input = frame(hole());
        let level = uvar(name);
        declare(&mut input, "x", Expr::sort(level.clone()));
        let head = Expr::const_(Name::from_components(["C"]), vec![level]);
        input.expected = Expr::app(head.clone(), hole());
        input.target = input.expected.clone();
        input.key = Expr::app(head, Expr::bvar(0).unwrap());
        input
    }

    #[test]
    fn universe_variants_preserve_shared_level_holes_and_rigid_parameters() {
        let first = polymorphic_frame("u");
        let second = polymorphic_frame("v");
        let left = canonical(&mut context(), &first).unwrap().unwrap();
        let right = canonical(&mut context(), &second).unwrap().unwrap();
        assert_eq!(left.expected, right.expected);
        assert_eq!(left.types, right.types);
        let mut separate = polymorphic_frame("u");
        declare(&mut separate, "x", Expr::sort(uvar("v")));
        let separate = canonical(&mut context(), &separate).unwrap().unwrap();
        assert_eq!(left.expected, separate.expected);
        assert_ne!(left.types, separate.types);
        let mut rigid = polymorphic_frame("u");
        // Even a rigid parameter spelled exactly like a private key variable
        // must not be treated as an inference hole.
        declare(
            &mut rigid,
            "x",
            Expr::sort(Level::param(Name::num(Name::anonymous(), 0))),
        );
        let rigid = canonical(&mut context(), &rigid).unwrap().unwrap();
        assert_ne!(left.types, rigid.types);
    }

    #[test]
    fn saved_universe_assignments_not_current_mutable_state_determine_the_key() {
        let mut input = polymorphic_frame("u");
        let id = LMVarId(Name::from_components(["u"]));
        input.base.txn.universes.assign(id.clone(), Level::one());
        let original = input.base.txn.universes.clone();
        let mut context = context();
        context.txn.universes.assign(id.clone(), Level::zero());
        let current = context.txn.universes.clone();
        let output = canonical(&mut context, &input).unwrap().unwrap();
        assert_eq!(output.types, vec![Expr::sort(Level::one())]);
        assert_eq!(input.base.txn.universes, original);
        assert_eq!(context.txn.universes, current);
        input.base.txn.universes.assign(id, Level::zero());
        let other = canonical(&mut context, &input).unwrap().unwrap();
        assert_ne!(output.expected, other.expected);
        assert_ne!(output.types, other.types);
    }

    #[test]
    fn active_cycle_universes_are_anchored_but_unrelated_path_holes_are_not() {
        let input = polymorphic_frame("query");
        let unrelated = polymorphic_frame("ancestor");
        assert!(
            canonical_with_ancestors(&mut context(), &input, &[unrelated])
                .unwrap()
                .is_some()
        );
        let mut related = frame(constant("unrelated"));
        // Anchor discovery traverses nested expression containers too.
        related.key = Expr::lam(
            Name::anonymous(),
            constant("Nat"),
            Expr::sort(uvar("query")),
            BinderInfo::Default,
        );
        assert!(
            canonical_with_ancestors(&mut context(), &input, &[related])
                .unwrap()
                .is_none()
        );
        let input = polymorphic_frame("query");
        let mut negative = GroundTable::default();
        negative
            .exhausted(&mut context(), &input, &[polymorphic_frame("query")])
            .unwrap();
        assert_eq!(negative.entries, 0);
    }

    #[test]
    fn cyclic_universe_assignments_cannot_become_a_completed_or_negative_key() {
        let mut input = polymorphic_frame("u");
        input.base.txn.universes.assign(
            LMVarId(Name::from_components(["u"])),
            Level::max(uvar("v"), Level::one()).unwrap(),
        );
        input
            .base
            .txn
            .universes
            .assign(LMVarId(Name::from_components(["v"])), uvar("u"));
        let before = input.base.txn.universes.clone();
        let mut context = context();
        context.txn.budget.max_heartbeats = 100;
        assert!(canonical(&mut context, &input).unwrap().is_none());
        let mut table = GroundTable::default();
        table
            .exhausted(&mut context, &input, &[frame(constant("Root"))])
            .unwrap();
        assert_eq!(table.entries, 0);
        assert_eq!(input.base.txn.universes, before);
    }

    #[test]
    fn universe_level_constructors_are_not_erased_or_solved_by_key_building() {
        let mut input = polymorphic_frame("head");
        let first = Level::imax(
            Level::max(uvar("u"), uvar("v")).unwrap(),
            uvar("u").succ().unwrap(),
        )
        .unwrap();
        declare(&mut input, "x", Expr::sort(first));
        let output = canonical(&mut context(), &input).unwrap().unwrap();
        let private = |n| Level::mvar(LMVarId(Name::num(Name::anonymous(), n)));
        assert_eq!(
            output.types,
            vec![Expr::sort(
                Level::imax(
                    Level::max(private(1), private(2)).unwrap(),
                    private(1).succ().unwrap(),
                )
                .unwrap()
            )]
        );
        assert!(input.base.txn.universes.is_empty());
        assert!(output.types[0].has_level_mvar()); // Only private key data.
    }

    #[test]
    fn deep_universe_aliases_and_shared_levels_stay_metered_and_stack_safe() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut input = polymorphic_frame("u");
                let mut level = uvar("leaf");
                for n in 0..1500 {
                    let id = LMVarId(Name::num(Name::from_components(["chain"]), n));
                    input.base.txn.universes.assign(id.clone(), level);
                    level = Level::mvar(id);
                }
                for _ in 0..35 {
                    level = Level::max(level.clone(), level).unwrap();
                }
                declare(&mut input, "x", Expr::sort(level));
                let mut context = context();
                context.txn.budget.max_heartbeats = 10_000;
                let result = canonical(&mut context, &input).unwrap().unwrap();
                assert!(result.units < 4000);
                assert!(result.types[0].has_level_mvar());
                let before = input.base.txn.universes.clone();
                context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 10;
                assert!(canonical(&mut context, &input).is_err());
                assert_eq!(input.base.txn.universes, before);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
