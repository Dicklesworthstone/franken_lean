//! Ordered rewriting with permutation rules, as the pin's simplifier does it.
//!
//! A simp rule whose two sides are equal up to its pattern variables is a *permutation* rule
//! (`isPerm`, vendored `src/Lean/Meta/Tactic/Simp/SimpTheorems.lean:292-304`, set on the
//! theorem by `mkSimpTheoremKeys`, `:384-404`). It rewrites a term only when the instantiated
//! result is smaller in the pin's term order (`tryTheoremCore`,
//! `src/Lean/Meta/Tactic/Simp/Rewrite.lean:143-150`: `unless ← acLt rhs e .reduceSimpleOnly`).
//! That order is `acLt` (`src/Lean/Meta/ACLt.lean`), an LPO-like ordering ported here case by
//! case: `lt`, `lpo`, `allChildrenLt`, `someChildGe`, `lexSameCtor`, `ltApp` and `ltPair`, with
//! instance-implicit arguments ignored (`getParamsInfo`'s `isInstance`) and each compared term
//! reduced by `DiscrTree.reduce` at reducible transparency with neither iota nor projection
//! reduction (`ReduceMode.reduceSimpleOnly`).
//!
//! With a permutation rule the order in which rules are tried decides the normal form
//! (`Nat.add_assoc` before `Nat.add_comm` at `a + b + c` leaves `a + (b + c)`, after it
//! `c + (a + b)`), so a rule set holding one takes its rewrites in the pin's order
//! ([`Context::simp_first_rewrite`]): the node `Simp.simpLoop`'s post-order traversal reaches
//! first, and there the candidate `rewrite?` tries first.
//!
//! The pin's functions are mutually recursive on the native stack. Here every comparison is a
//! frame on a heap stack: a frame is the ordered list of the `lt` calls its function makes,
//! each with what its result does (go on, or return a verdict), so the depth of the compared
//! terms never reaches the native stack. Every step charges a heartbeat, as the pin's
//! `checkSystem "Lean.Meta.acLt"` does at each `lpo`; exhausting them is the typed
//! resource limit (FL-INV-07), never an answer.

use super::*;

/// The most reducible-definition unfoldings and eta reductions one `reduce` performs.
const MAX_REDUCTIONS: usize = 1 << 10;

/// What one `lt` result does to the sequence of comparisons it belongs to.
#[derive(Clone, Copy)]
enum Then {
    Next,
    Return(bool),
}

enum Step {
    /// `lt x y`, then the first action when it holds and the second when it does not.
    Lt(Expr, Expr, Then, Then),
    Return(bool),
}

/// One pending function body: its comparisons in order, and the one running.
struct Frame {
    steps: Vec<Step>,
    at: usize,
}

/// What one comparison reads repeatedly: the reducibility table, the class registry, and each
/// function's instance-implicit parameters (the pin caches `getFunInfo` the same way).
struct AcState {
    table: Arc<crate::reducibility::ReducibilityTable>,
    registry: Arc<crate::instances::InstanceRegistry>,
    instances: HashMap<(Expr, usize), Vec<bool>>,
}

/// The result of entering `lt`: decided at once, or a body to run.
enum Entered {
    Value(bool),
    Frame(Frame),
}

/// `Expr.ctorWeight` (`ACLt.lean:14-26`).
fn ctor_weight(e: &Expr) -> u8 {
    match e.node() {
        ExprNode::BVar { .. } => 0,
        ExprNode::FVar { .. } => 1,
        ExprNode::MVar { .. } => 2,
        ExprNode::Sort { .. } => 3,
        ExprNode::Const { .. } => 4,
        ExprNode::Lit { .. } => 5,
        ExprNode::MData { .. } => 6,
        ExprNode::Proj { .. } => 7,
        ExprNode::App { .. } => 8,
        ExprNode::Lam { .. } => 9,
        ExprNode::ForallE { .. } => 10,
        ExprNode::LetE { .. } => 11,
    }
}

/// `Expr.withApp`: the function and the arguments of an application spine. Metadata is not
/// looked through, as `getAppFn` does not.
fn app_spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut head = e;
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    (head.clone(), args)
}

/// `Expr.etaExpandedStrict?` (`src/Lean/Expr.lean:1675-1693`): `fun x₁ … xₙ => f x₁ … xₙ` as
/// `f`, when `f` mentions none of the bound variables.
fn eta_expanded_strict(e: &Expr) -> Option<Expr> {
    let mut body = e;
    let mut binders = 0u32;
    while let ExprNode::Lam { body: next, .. } = body.node() {
        body = next;
        binders += 1;
    }
    if binders == 0 {
        return None;
    }
    let mut function = body;
    for index in 0..binders {
        let ExprNode::App { f, a } = function.node() else {
            return None;
        };
        if !matches!(a.node(), ExprNode::BVar { idx } if *idx == index) {
            return None;
        }
        function = f;
    }
    (!function.has_loose_bvars()).then(|| function.clone())
}

/// `Expr.betaRev` of `function` at `args` (in application order): as many leading lambdas as
/// there are arguments are instantiated, and the rest of the arguments are applied.
fn beta(function: &Expr, args: &[Expr]) -> Option<Expr> {
    let mut body = function;
    let mut taken = 0usize;
    while taken < args.len()
        && let ExprNode::Lam { body: next, .. } = body.node()
    {
        body = next;
        taken += 1;
    }
    // `subst_loose` replaces bvar `n - 1 - j` by `substs[j]`: the outermost binder takes the
    // first argument.
    let substituted = body.subst_loose(0, &args[..taken]).ok()?;
    Some(args[taken..].iter().fold(substituted, |function, arg| {
        Expr::app(function, arg.clone())
    }))
}

/// How early the pin's simplifier reaches a rewrite. `Simp.simpLoop` (vendored
/// `src/Lean/Meta/Tactic/Simp/Main.lean:654-686`) rewrites a node after its arguments, so
/// occurrences come in post-order. An unfolded definition goes first (it is definitional and
/// unfolds every occurrence at once); occurrences this engine finds only beneath a binder, after
/// every other; the simplification procedures and then `+arith`'s normalization, which the pin
/// runs after the rules in that order (`Rewrite.lean:542-546`), last.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum SimpReach {
    /// A conditional's default pre-simproc runs before visiting its branches.
    Conditional,
    /// `simpUsingDecide`, which runs before a node's other rewrites (`decide.rs`).
    Decide,
    Unfold,
    /// The occurrence's one-based post-order ordinal in the target.
    Node(usize),
    Binder,
    /// The `Nat` simplification procedures (`simproc.rs`), which run after every theorem.
    Procedure,
    Arith,
}

/// A rule's rewrite and where it happens, or `None` where the rule does not rewrite.
pub(super) type SimpRewrite<T> = Option<(T, SimpPlace)>;

/// Where a simp rule rewrote, and its pattern with its holes open (its discrimination-tree path).
#[derive(Clone)]
pub(super) struct SimpPlace {
    pub(super) reach: SimpReach,
    pub(super) pattern: Option<Expr>,
}

impl SimpPlace {
    pub(super) fn of(reach: SimpReach) -> Self {
        Self {
            reach,
            pattern: None,
        }
    }
}

/// `isPerm` read off a rule's admitted statement, its binders' variables standing for the
/// pattern variables: whether `rules` can hold a permutation rule.
fn statement_is_perm(statement: &Expr) -> bool {
    let mut body = statement;
    while let ExprNode::ForallE { body: next, .. } | ExprNode::MData { expr: next, .. } =
        body.node()
    {
        body = next;
    }
    let (head, args) = app_spine(body);
    let ExprNode::Const { name, .. } = head.node() else {
        return false;
    };
    let (lhs, rhs) = if *name == Name::from_components(["Eq"]) && args.len() == 3 {
        (&args[1], &args[2])
    } else if *name == Name::from_components(["Iff"]) && args.len() == 2 {
        (&args[0], &args[1])
    } else {
        return false;
    };
    let mut pending = vec![(lhs.clone(), rhs.clone())];
    let mut visited = HashSet::new();
    while let Some((s, t)) = pending.pop() {
        if !visited.insert((s.allocation_identity(), t.allocation_identity())) {
            continue;
        }
        match (s.node(), t.node()) {
            (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
                pending.push((f1.clone(), f2.clone()));
                pending.push((a1.clone(), a2.clone()));
            }
            (ExprNode::MData { expr, .. }, _) => pending.push((expr.clone(), t.clone())),
            (_, ExprNode::MData { expr, .. }) => pending.push((s.clone(), expr.clone())),
            (
                ExprNode::BVar { .. } | ExprNode::MVar { .. },
                ExprNode::BVar { .. } | ExprNode::MVar { .. },
            ) => {}
            (
                ExprNode::ForallE {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            )
            | (
                ExprNode::Lam {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                ExprNode::Lam {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            ) => {
                pending.push((d1.clone(), d2.clone()));
                pending.push((b1.clone(), b2.clone()));
            }
            (
                ExprNode::Proj {
                    idx: i, expr: x, ..
                },
                ExprNode::Proj {
                    idx: j, expr: y, ..
                },
            ) => {
                if i != j {
                    return false;
                }
                pending.push((x.clone(), y.clone()));
            }
            _ => {
                if s != t {
                    return false;
                }
            }
        }
    }
    true
}

impl Context {
    /// Whether `rules` hold a permutation rule, read from each rule's statement. Without one,
    /// rules are taken in this engine's order (the first that applies), as before ordered
    /// rewriting: the registered `Init` set holds none (measured at v4.32.0, under `import Lean`
    /// only `Std.HashSet.forIn_eq_forIn` is one). A registered theorem's answer is memoized
    /// with its keys and charges nothing, as reading its keys does not.
    pub(super) fn simp_rules_permute(
        &mut self,
        rules: &[SimpRule<'_>],
    ) -> Result<bool, NatDefinitionElabError> {
        let environment = simp_key_environment(&self.txn.env);
        {
            let cache = Arc::clone(&self.simp_key_cache.0);
            let mut memo = cache.lock().unwrap_or_else(PoisonError::into_inner);
            if memo.environment.as_ref() != Some(&environment) {
                *memo = SimpKeyMemo {
                    environment: Some(environment),
                    ..SimpKeyMemo::default()
                };
            }
            for rule in rules {
                let Some(entry) = simp_rule_entry(rule) else {
                    continue;
                };
                let declaration = entry.proof.as_ref().unwrap_or(&entry.declaration);
                let perm = *memo.perms.entry(declaration.clone()).or_insert_with(|| {
                    self.txn
                        .env
                        .find(declaration)
                        .is_some_and(|info| statement_is_perm(&info.constant_val().type_))
                });
                if perm {
                    return Ok(true);
                }
            }
        }
        for rule in rules {
            let statement = match rule {
                SimpRule::Arith
                | SimpRule::Decide
                | SimpRule::Conditional { .. }
                | SimpRule::Simprocs(_)
                | SimpRule::Global(_) => continue,
                SimpRule::Explicit(explicit) if explicit.global.is_some() => continue,
                SimpRule::Local(id) => {
                    let Some(local) = self.txn.lctx.find(id) else {
                        continue;
                    };
                    local.type_.clone()
                }
                SimpRule::Explicit(_) => {
                    self.tick()?;
                    let mut trial = self.rewrite_trial();
                    let statement = (|| {
                        let term = trial.selected_simp_term(rule)?;
                        trial.instantiate(&term.type_)
                    })();
                    self.charge_rewrite_trial(&trial);
                    match statement {
                        Ok(statement) => statement,
                        // The rule's own use reports the refusal.
                        Err(_) => continue,
                    }
                }
            };
            if statement_is_perm(&statement) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The rewrite the pin's simplifier performs first among those `try_rule` finds for the
    /// `admitted` rules, with the elaboration state it leaves, and its rule's index. When
    /// `permute` is false this is the first rule (in `rules`' order) that rewrites, as the
    /// engine always took; otherwise every rule is tried and [`Self::simp_place_precedes`]
    /// chooses. A rule that does not rewrite charges its work and changes nothing.
    pub(super) fn simp_first_rewrite<T>(
        &mut self,
        rules: &[SimpRule<'_>],
        permute: bool,
        mut admitted: impl FnMut(&mut Self, &SimpRule<'_>) -> Result<bool, NatDefinitionElabError>,
        mut try_rule: impl FnMut(
            &mut Self,
            &SimpRule<'_>,
        ) -> Result<SimpRewrite<T>, NatDefinitionElabError>,
    ) -> Result<Option<(usize, T)>, NatDefinitionElabError> {
        let mut chosen: Option<(Self, usize, T, SimpPlace)> = None;
        for (index, rule) in rules.iter().enumerate() {
            if !admitted(self, rule)? {
                continue;
            }
            self.tick()?;
            let original = self.rewrite_trial();
            // Only an occurrence no later than the chosen one can still be chosen.
            self.simp_reach_limit = match chosen.as_ref().map(|(_, _, _, place)| place.reach) {
                Some(SimpReach::Unfold) => Some(0),
                Some(SimpReach::Node(position)) => Some(position),
                _ => None,
            };
            let tried = try_rule(self, rule);
            self.simp_reach_limit = None;
            let Some((found, place)) = tried? else {
                self.restore_simp_trial(original);
                continue;
            };
            if !permute || place.reach == SimpReach::Conditional {
                return Ok(Some((index, found)));
            }
            let earlier = match &chosen {
                None => true,
                Some((_, at, _, other)) => {
                    self.simp_place_precedes(rules, index, &place, *at, other)?
                }
            };
            if earlier {
                chosen = Some((self.rewrite_trial(), index, found, place));
            }
            self.restore_simp_trial(original);
        }
        let Some((state, index, found, _)) = chosen else {
            return Ok(None);
        };
        self.restore_simp_trial(state);
        Ok(Some((index, found)))
    }

    /// Whether the pin rewrites with `rules[a]` at `at_a` before `rules[b]` at `at_b`: the node
    /// it reaches first, and at one node the candidate `rewrite?` tries first (vendored
    /// `src/Lean/Meta/Tactic/Simp/Rewrite.lean:226-262`): the higher priority, then the
    /// discrimination tree's order, where at the first place two paths differ a variable key
    /// comes first (`getMatchLoop` visits the star child before the others,
    /// `src/Lean/Meta/DiscrTree/Main.lean`), then insertion order: the registered set, then
    /// the call's arguments. Two paths this cannot place keep `rules`' order.
    pub(super) fn simp_place_precedes(
        &mut self,
        rules: &[SimpRule<'_>],
        a: usize,
        at_a: &SimpPlace,
        b: usize,
        at_b: &SimpPlace,
    ) -> Result<bool, NatDefinitionElabError> {
        if at_a.reach != at_b.reach {
            return Ok(at_a.reach < at_b.reach);
        }
        let priority = |rule: &SimpRule<'_>| match rule {
            SimpRule::Global(entry) => entry.priority,
            _ => 1000,
        };
        let (p, q) = (priority(&rules[a]), priority(&rules[b]));
        if p != q {
            return Ok(p > q);
        }
        if let (Some(x), Some(y)) = (&at_a.pattern, &at_b.pattern) {
            match self.simp_pattern_order(x, y)? {
                Some(std::cmp::Ordering::Less) => return Ok(true),
                Some(std::cmp::Ordering::Greater) => return Ok(false),
                Some(std::cmp::Ordering::Equal) => {}
                None => return Ok(a < b),
            }
        } else {
            return Ok(a < b);
        }
        let registered = |index: usize| matches!(rules[index], SimpRule::Global(_));
        let rank = |index: usize| {
            let before = rules[..index]
                .iter()
                .filter(|rule| matches!(rule, SimpRule::Global(_)))
                .count();
            if registered(index) {
                before
            } else {
                let globals = rules
                    .iter()
                    .filter(|rule| matches!(rule, SimpRule::Global(_)))
                    .count();
                globals + (index - before)
            }
        };
        Ok(rank(a) < rank(b))
    }

    /// The order of two patterns' discrimination-tree paths at their first difference, read
    /// in pre-order with instance-implicit arguments unkeyed: a hole (a variable key) comes
    /// first. `None` where neither is a hole and their keys differ.
    fn simp_pattern_order(
        &mut self,
        x: &Expr,
        y: &Expr,
    ) -> Result<Option<std::cmp::Ordering>, NatDefinitionElabError> {
        use std::cmp::Ordering;
        let mut state = self.ac_state()?;
        let mut pending = vec![(x.clone(), y.clone())];
        while let Some((mut x, mut y)) = pending.pop() {
            self.tick()?;
            while let ExprNode::MData { expr, .. } = x.node() {
                x = expr.clone();
            }
            while let ExprNode::MData { expr, .. } = y.node() {
                y = expr.clone();
            }
            let hole = |e: &Expr| matches!(e.node(), ExprNode::MVar { .. });
            match (hole(&x), hole(&y)) {
                (true, true) => continue,
                (true, false) => return Ok(Some(Ordering::Less)),
                (false, true) => return Ok(Some(Ordering::Greater)),
                (false, false) => {}
            }
            let (x_head, x_args) = app_spine(&x);
            let (y_head, y_args) = app_spine(&y);
            let same = x_args.len() == y_args.len()
                && match (x_head.node(), y_head.node()) {
                    (ExprNode::Const { name: m, .. }, ExprNode::Const { name: n, .. }) => m == n,
                    (ExprNode::FVar { id: m }, ExprNode::FVar { id: n }) => m == n,
                    (ExprNode::BVar { idx: m }, ExprNode::BVar { idx: n }) => m == n,
                    (ExprNode::Lit { literal: m }, ExprNode::Lit { literal: n }) => m == n,
                    (ExprNode::Sort { .. }, ExprNode::Sort { .. })
                    | (ExprNode::Lam { .. }, ExprNode::Lam { .. })
                    | (ExprNode::ForallE { .. }, ExprNode::ForallE { .. }) => true,
                    (
                        ExprNode::Proj {
                            struct_name: m,
                            idx: i,
                            expr: e,
                        },
                        ExprNode::Proj {
                            struct_name: n,
                            idx: j,
                            expr: f,
                        },
                    ) if m == n && i == j => {
                        pending.push((e.clone(), f.clone()));
                        true
                    }
                    _ => false,
                };
            if !same {
                return Ok(None);
            }
            let infos = self.ac_param_instances(&x_head, &x_args, &mut state)?;
            for (index, (u, v)) in x_args.into_iter().zip(y_args).enumerate().rev() {
                if !infos.get(index).copied().unwrap_or(false) {
                    pending.push((u, v));
                }
            }
        }
        Ok(Some(Ordering::Equal))
    }

    /// `acLt a b .reduceSimpleOnly` (`ACLt.lean:189-191`): whether `a` precedes `b`.
    pub(in crate::source) fn simp_ac_lt(
        &mut self,
        a: &Expr,
        b: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut state = self.ac_state()?;
        let mut stack = match self.ac_lt_enter(a, b, &mut state)? {
            Entered::Value(value) => return Ok(value),
            Entered::Frame(frame) => vec![frame],
        };
        // The verdict the top frame's running step is waiting for.
        let mut returned: Option<bool> = None;
        loop {
            self.tick()?;
            let frame = stack
                .last_mut()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let step = frame
                .steps
                .get(frame.at)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let finished = if let Some(value) = returned.take() {
                let Step::Lt(_, _, on_true, on_false) = step else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                match if value { *on_true } else { *on_false } {
                    Then::Next => {
                        frame.at += 1;
                        None
                    }
                    Then::Return(verdict) => Some(verdict),
                }
            } else {
                match step {
                    Step::Return(verdict) => Some(*verdict),
                    Step::Lt(x, y, ..) => {
                        let (x, y) = (x.clone(), y.clone());
                        match self.ac_lt_enter(&x, &y, &mut state)? {
                            Entered::Value(value) => returned = Some(value),
                            Entered::Frame(frame) => stack.push(frame),
                        }
                        None
                    }
                }
            };
            if let Some(verdict) = finished {
                stack.pop();
                if stack.is_empty() {
                    return Ok(verdict);
                }
                returned = Some(verdict);
            }
        }
    }

    fn ac_state(&mut self) -> Result<AcState, NatDefinitionElabError> {
        self.tick()?;
        let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        Ok(AcState {
            table,
            registry: self.instance_registry()?,
            instances: HashMap::new(),
        })
    }

    /// `lt` (`ACLt.lean:63-74`): structurally equal terms are not ordered, metadata is ignored,
    /// and otherwise `lpo` compares the two reduced terms.
    fn ac_lt_enter(
        &mut self,
        a: &Expr,
        b: &Expr,
        state: &mut AcState,
    ) -> Result<Entered, NatDefinitionElabError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        loop {
            self.tick()?;
            if self.rewrite_same(&a, &b)? {
                return Ok(Entered::Value(false));
            }
            if let ExprNode::MData { expr, .. } = a.node() {
                a = expr.clone();
            } else if let ExprNode::MData { expr, .. } = b.node() {
                b = expr.clone();
            } else {
                break;
            }
        }
        let a = self.ac_reduce(&a, state)?;
        let b = self.ac_reduce(&b, state)?;
        self.ac_lpo(a, b, state).map(Entered::Frame)
    }

    /// `lpo` (`ACLt.lean:168-184`) as its sequence of comparisons.
    fn ac_lpo(
        &mut self,
        a: Expr,
        b: Expr,
        state: &mut AcState,
    ) -> Result<Frame, NatDefinitionElabError> {
        let mut steps = Vec::new();
        // Case 1, `someChildGe b a`: some child of `b` is not below `a`.
        for child in self.ac_children(&b, state)? {
            steps.push(Step::Lt(child, a.clone(), Then::Next, Then::Return(true)));
        }
        let (weight_a, weight_b) = (ctor_weight(&a), ctor_weight(&b));
        if weight_a > weight_b {
            steps.push(Step::Return(false));
            return Ok(Frame { steps, at: 0 });
        }
        // Cases 2 and 3 both need every child of `a` below `b`.
        for child in self.ac_children(&a, state)? {
            steps.push(Step::Lt(child, b.clone(), Then::Next, Then::Return(false)));
        }
        if weight_a < weight_b {
            steps.push(Step::Return(true));
        } else {
            self.ac_lex_same_ctor(&a, &b, state, &mut steps)?;
        }
        Ok(Frame { steps, at: 0 })
    }

    /// The children `allChildrenLt` compares (`ACLt.lean:146-161`): a projection's structure,
    /// an application's arguments but its instance-implicit ones, a binder's domain and body,
    /// a `let`'s value and body.
    fn ac_children(
        &mut self,
        e: &Expr,
        state: &mut AcState,
    ) -> Result<Vec<Expr>, NatDefinitionElabError> {
        Ok(match e.node() {
            ExprNode::Proj { expr, .. } => vec![expr.clone()],
            ExprNode::App { .. } => {
                let (function, args) = app_spine(e);
                let infos = self.ac_param_instances(&function, &args, state)?;
                args.into_iter()
                    .enumerate()
                    .filter(|(index, _)| !infos.get(*index).copied().unwrap_or(false))
                    .map(|(_, arg)| arg)
                    .collect()
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => vec![binder_type.clone(), body.clone()],
            ExprNode::LetE { value, body, .. } => vec![value.clone(), body.clone()],
            _ => Vec::new(),
        })
    }

    /// `lexSameCtor` (`ACLt.lean:125-144`), for two terms of one constructor weight.
    fn ac_lex_same_ctor(
        &mut self,
        a: &Expr,
        b: &Expr,
        state: &mut AcState,
        steps: &mut Vec<Step>,
    ) -> Result<(), NatDefinitionElabError> {
        let verdict = match (a.node(), b.node()) {
            (ExprNode::BVar { idx: i }, ExprNode::BVar { idx: j }) => i < j,
            // Declaration order, not the name order of the identifiers (lean4#12136).
            (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) => {
                let position = |id: &FVarId| {
                    self.txn
                        .lctx
                        .decls()
                        .iter()
                        .position(|local| &local.id == id)
                };
                match (position(x), position(y)) {
                    (Some(i), Some(j)) => i < j,
                    _ => return Err(failure(SourceInferenceError::Scope)),
                }
            }
            (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) => x.0 < y.0,
            (ExprNode::Sort { level: u }, ExprNode::Sort { level: v }) => u.norm_lt(v),
            // Universe levels are ignored.
            (ExprNode::Const { name: x, .. }, ExprNode::Const { name: y, .. }) => x < y,
            (ExprNode::Lit { literal: x }, ExprNode::Lit { literal: y }) => x.lt(y),
            (
                ExprNode::Proj {
                    idx: i, expr: x, ..
                },
                ExprNode::Proj {
                    idx: j, expr: y, ..
                },
            ) => {
                if i == j {
                    steps.push(Step::Lt(
                        x.clone(),
                        y.clone(),
                        Then::Return(true),
                        Then::Return(false),
                    ));
                    return Ok(());
                }
                i < j
            }
            (ExprNode::App { .. }, ExprNode::App { .. }) => {
                return self.ac_lt_app(a, b, state, steps);
            }
            (
                ExprNode::Lam {
                    binder_type: d1,
                    body: e1,
                    ..
                },
                ExprNode::Lam {
                    binder_type: d2,
                    body: e2,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: d1,
                    body: e1,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: d2,
                    body: e2,
                    ..
                },
            )
            | (
                ExprNode::LetE {
                    value: d1,
                    body: e1,
                    ..
                },
                ExprNode::LetE {
                    value: d2,
                    body: e2,
                    ..
                },
            ) => {
                ac_lt_pair(d1, e1, d2, e2, steps);
                return Ok(());
            }
            // `lt` removes metadata before `lpo`, and equal weights are one constructor.
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        steps.push(Step::Return(verdict));
        Ok(())
    }

    /// `ltApp` (`ACLt.lean:95-123`): the functions, then the argument count, then the
    /// arguments left to right, instance-implicit ones skipped.
    fn ac_lt_app(
        &mut self,
        a: &Expr,
        b: &Expr,
        state: &mut AcState,
        steps: &mut Vec<Step>,
    ) -> Result<(), NatDefinitionElabError> {
        let (a_function, a_args) = app_spine(a);
        let (b_function, b_args) = app_spine(b);
        steps.push(Step::Lt(
            a_function.clone(),
            b_function.clone(),
            Then::Return(true),
            Then::Next,
        ));
        steps.push(Step::Lt(
            b_function,
            a_function.clone(),
            Then::Return(false),
            Then::Next,
        ));
        if a_args.len() != b_args.len() {
            steps.push(Step::Return(a_args.len() < b_args.len()));
            return Ok(());
        }
        let infos = self.ac_param_instances(&a_function, &a_args, state)?;
        for (index, (x, y)) in a_args.into_iter().zip(b_args).enumerate() {
            if infos.get(index).copied().unwrap_or(false) {
                continue;
            }
            steps.push(Step::Lt(
                x.clone(),
                y.clone(),
                Then::Return(true),
                Then::Next,
            ));
            steps.push(Step::Lt(y, x, Then::Return(false), Then::Next));
        }
        steps.push(Step::Return(false));
        Ok(())
    }

    /// `getParamsInfo f args.size` (`ACLt.lean:83-93`) reduced to what `acLt` reads: whether
    /// each parameter is an instance (`getFunInfoNArgs`, `src/Lean/Meta/FunInfo.lean:74-138`:
    /// its type is a class and its binder is not explicit). Shorter than `args` when the
    /// function's type exposes fewer parameters; empty for a function with loose bound
    /// variables, whose type the pin does not infer.
    fn ac_param_instances(
        &mut self,
        function: &Expr,
        args: &[Expr],
        state: &mut AcState,
    ) -> Result<Vec<bool>, NatDefinitionElabError> {
        if function.has_loose_bvars() {
            return Ok(Vec::new());
        }
        let key = (function.clone(), args.len());
        if let Some(found) = state.instances.get(&key) {
            return Ok(found.clone());
        }
        let Some(mut type_) = self.known_type(function)? else {
            return Ok(Vec::new());
        };
        type_ = self.instantiate(&type_)?;
        let registry = Arc::clone(&state.registry);
        let mut flags = Vec::new();
        // Whether a reduction ran on the type instantiated at this application's arguments
        // (the pin's telescope opens fresh locals instead): such a result is not reused.
        let mut specialized = false;
        while flags.len() < args.len() {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                if type_.has_loose_bvars() {
                    // The outermost consumed binder takes the first argument.
                    type_ = type_
                        .subst_loose(0, &args[..flags.len()])
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    specialized = true;
                }
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            else {
                break;
            };
            let is_instance =
                *binder_info != BinderInfo::Default && self.ac_is_class(binder_type, &registry)?;
            flags.push(is_instance);
            type_ = body.clone();
        }
        if !specialized {
            state.instances.insert(key, flags.clone());
        }
        Ok(flags)
    }

    /// `isClass?` (`src/Lean/Meta/InferType.lean`): under its binders, the type is an
    /// application of a class, possibly through reducible definitions.
    fn ac_is_class(
        &mut self,
        type_: &Expr,
        registry: &crate::instances::InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut body = type_;
        while let ExprNode::ForallE { body: next, .. } | ExprNode::MData { expr: next, .. } =
            body.node()
        {
            body = next;
        }
        let (head, _) = app_spine(body);
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(false);
        };
        if registry.is_class(name) {
            return Ok(true);
        }
        if body.has_loose_bvars() || !matches!(self.txn.env.find(name), Some(ConstantInfo::Defn(_)))
        {
            return Ok(false);
        }
        let reduced =
            self.whnf_with_transparency(body, UnificationTransparency::Abbreviations, false)?;
        let (head, _) = app_spine(&reduced);
        Ok(matches!(head.node(), ExprNode::Const { name, .. } if registry.is_class(name)))
    }

    /// `ACLt.main.reduce` in `.reduceSimpleOnly` mode (`ACLt.lean:51-61`): `DiscrTree.reduce`
    /// (`src/Lean/Meta/DiscrTree/Main.lean:204-210`) at reducible transparency without iota or
    /// projection reduction. A term with loose bound variables is left as it is.
    fn ac_reduce(&mut self, e: &Expr, state: &AcState) -> Result<Expr, NatDefinitionElabError> {
        if e.has_loose_bvars() {
            return Ok(e.clone());
        }
        let mut e = e.clone();
        for _ in 0..MAX_REDUCTIONS {
            self.tick()?;
            e = self.ac_whnf_core(&e)?;
            if let Some(next) = self.ac_unfold_reducible(&e, &state.table)? {
                e = next;
                continue;
            }
            if let Some(next) = eta_expanded_strict(&e) {
                e = next;
                continue;
            }
            return Ok(e);
        }
        Err(failure(SourceInferenceError::ResourceLimit))
    }

    /// `whnfCore` under the reduction configuration `acLt` sets (beta, `let` and `have` zeta,
    /// let-variable unfolding, assigned metavariables; no iota, no projections): at the head
    /// only.
    fn ac_whnf_core(&mut self, e: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut e = e.clone();
        for _ in 0..MAX_REDUCTIONS {
            self.tick()?;
            let (head, args) = app_spine(&e);
            let next = match head.node() {
                ExprNode::MData { expr, .. } => Some(expr.clone()),
                ExprNode::LetE { value, body, .. } => Some(
                    body.subst_loose(0, std::slice::from_ref(value))
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                ),
                ExprNode::FVar { id } => {
                    self.txn.lctx.find(id).and_then(|local| local.value.clone())
                }
                ExprNode::MVar { id } if self.txn.mvars.is_assigned(id) => {
                    Some(self.instantiate(&head)?)
                }
                ExprNode::Lam { .. } if !args.is_empty() => {
                    let reduced =
                        beta(&head, &args).ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    e = reduced;
                    continue;
                }
                _ => None,
            };
            let Some(head) = next else {
                return Ok(e);
            };
            e = args.into_iter().fold(head, Expr::app);
        }
        Err(failure(SourceInferenceError::ResourceLimit))
    }

    /// `unfoldDefinition?` at reducible transparency (`src/Lean/Meta/WHNF.lean:871-950`): a
    /// reducible definition at the head, instantiated at its universe arguments and
    /// beta-reduced with the application's arguments. Structure projections, matchers and
    /// definitions with smart unfolding are not unfolded here, as the simplifier's key path
    /// does not unfold them (`simp_key_unfolds`).
    fn ac_unfold_reducible(
        &mut self,
        e: &Expr,
        table: &crate::reducibility::ReducibilityTable,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, args) = app_spine(e);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if !simp_key_unfolds(&self.txn.env, table, name)
            || matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with("match_"))
            || self.txn.env.contains(&Name::str(name.clone(), "_sunfold"))
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len() {
            return Ok(None);
        }
        let value =
            self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
        Ok(beta(&value, &args))
    }

    /// `isPerm` (`SimpTheorems.lean:292-304`): whether a rule's two sides are one term up to its
    /// pattern variables. Two variables meet by unification (`isDefEq`), which can always
    /// identify two distinct ones of one type, so this is a union of variables, checked against
    /// their declared types.
    pub(in crate::source) fn simp_is_perm(&self, lhs: &Expr, rhs: &Expr) -> bool {
        let mut parents: HashMap<MVarId, MVarId> = HashMap::new();
        let find = |parents: &HashMap<MVarId, MVarId>, id: &MVarId| {
            let mut id = id.clone();
            while let Some(parent) = parents.get(&id) {
                id = parent.clone();
            }
            id
        };
        let mut pending = vec![(lhs.clone(), rhs.clone())];
        let mut visited = HashSet::new();
        while let Some((s, t)) = pending.pop() {
            if !visited.insert((s.allocation_identity(), t.allocation_identity())) {
                continue;
            }
            match (s.node(), t.node()) {
                (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
                    pending.push((a1.clone(), a2.clone()));
                    pending.push((f1.clone(), f2.clone()));
                }
                (ExprNode::MData { expr, .. }, _) => pending.push((expr.clone(), t.clone())),
                (_, ExprNode::MData { expr, .. }) => pending.push((s.clone(), expr.clone())),
                (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) => {
                    let (x, y) = (find(&parents, x), find(&parents, y));
                    if x == y {
                        continue;
                    }
                    let types = (
                        self.txn.mvars.get_decl(&x).map(|decl| &decl.type_),
                        self.txn.mvars.get_decl(&y).map(|decl| &decl.type_),
                    );
                    let (Some(x_type), Some(y_type)) = types else {
                        return false;
                    };
                    if !perm_types_agree(x_type, y_type, &parents, &find) {
                        return false;
                    }
                    parents.insert(x, y);
                }
                (
                    ExprNode::ForallE {
                        binder_type: d1,
                        body: b1,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: d2,
                        body: b2,
                        ..
                    },
                )
                | (
                    ExprNode::Lam {
                        binder_type: d1,
                        body: b1,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: d2,
                        body: b2,
                        ..
                    },
                ) => {
                    pending.push((b1.clone(), b2.clone()));
                    pending.push((d1.clone(), d2.clone()));
                }
                (
                    ExprNode::LetE {
                        type_: t1,
                        value: v1,
                        body: b1,
                        ..
                    },
                    ExprNode::LetE {
                        type_: t2,
                        value: v2,
                        body: b2,
                        ..
                    },
                ) => {
                    pending.push((b1.clone(), b2.clone()));
                    pending.push((v1.clone(), v2.clone()));
                    pending.push((t1.clone(), t2.clone()));
                }
                (
                    ExprNode::Proj {
                        idx: i, expr: x, ..
                    },
                    ExprNode::Proj {
                        idx: j, expr: y, ..
                    },
                ) => {
                    if i != j {
                        return false;
                    }
                    pending.push((x.clone(), y.clone()));
                }
                // `s == t`: structural equality.
                _ => {
                    if s != t {
                        return false;
                    }
                }
            }
        }
        true
    }
}

/// `ltPair` (`ACLt.lean:76-82`).
fn ac_lt_pair(a1: &Expr, a2: &Expr, b1: &Expr, b2: &Expr, steps: &mut Vec<Step>) {
    steps.push(Step::Lt(
        a1.clone(),
        b1.clone(),
        Then::Return(true),
        Then::Next,
    ));
    steps.push(Step::Lt(
        b1.clone(),
        a1.clone(),
        Then::Return(false),
        Then::Next,
    ));
    steps.push(Step::Lt(
        a2.clone(),
        b2.clone(),
        Then::Return(true),
        Then::Return(false),
    ));
}

/// Whether two pattern variables' types agree once the variables already identified are one.
fn perm_types_agree(
    left: &Expr,
    right: &Expr,
    parents: &HashMap<MVarId, MVarId>,
    find: &impl Fn(&HashMap<MVarId, MVarId>, &MVarId) -> MVarId,
) -> bool {
    let mut pending = vec![(left, right)];
    let mut visited = HashSet::new();
    while let Some((s, t)) = pending.pop() {
        if !visited.insert((s.allocation_identity(), t.allocation_identity())) {
            continue;
        }
        match (s.node(), t.node()) {
            (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) => {
                if find(parents, x) != find(parents, y) {
                    return false;
                }
            }
            (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
                pending.push((f1, f2));
                pending.push((a1, a2));
            }
            _ => {
                if s != t {
                    return false;
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests;
