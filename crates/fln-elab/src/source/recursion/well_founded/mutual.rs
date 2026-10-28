//! Mutual well-founded recursion over one shared fixpoint, as the pin builds it
//! (Lean/Elab/PreDefinition/WF/Main.lean `wfRecursion`, Mutual.lean,
//! PackMutual.lean, Meta/ArgsPacker.lean, WF/Fix.lean).
//!
//! A recursive component of a safe mutual block, in the pin's SCC order
//! (Lean/Util/SCC.lean over `foldConsts`-ordered call edges,
//! Lean/Elab/PreDefinition/Main.lean `partitionPreDefs`), becomes:
//!
//! * `<first>._mutual : fixed → (x : D₀ ⊕' D₁ ⊕' …) → C x`, a
//!   `WellFounded.Nat.fix` over the right-nested `PSum` of each member's
//!   `PSigma`-packed varying arguments (`Mutual.packType`, `Unary.packType`);
//! * each member `fun params => <first>._mutual fixed (PSum.inl ⟨varying⟩)`
//!   etc. (`Mutual.pack`, `preDefsFromUnaryNonRec`), marked `@[irreducible]`.
//!
//! Each member body is elaborated against the shared continuation at its own
//! injected argument; a call to any member packs that member's varying
//! arguments and injects them. Each member's `decreasing_by` (or the default
//! tactic) proves the goals of the calls in its own body
//! (`groupGoalsByFunction`, WF/Fix.lean).
//!
//! Supported: Nat-valued measures with the canonical relation (so the fixpoint
//! is `WellFounded.Nat.fix`), fixed parameters forming one common unreordered
//! prefix (`fixedArePrefix`), including the common section closure, and identical
//! written universe parameters. Every other recursive component is a typed refusal, never a
//! partial or unsafe fallback.
use super::*;
use std::sync::Arc;

/// A member's termination hint, as the group's body pass observed it.
#[derive(Clone)]
pub(in crate::source) enum MemberHint {
    /// Neither `termination_by` nor `decreasing_by`.
    None,
    /// `decreasing_by` alone: the pin guesses the measure (GuessLex).
    DecreasingOnly,
    /// `termination_by structural`.
    Structural,
    /// `termination_by e`: the measured member, or why it could not be measured.
    /// A failure matters only if the member turns out to be recursive.
    Measured(Result<Measured, NatDefinitionElabError>),
}

#[derive(Clone)]
pub(in crate::source) struct Measured {
    /// The parameters the measure and the packing range over: the header's,
    /// the equations', and the body's written leading lambdas.
    pub arity: usize,
    /// `fun params => e`, closed over the written parameters. The group's
    /// body-derived section closure is applied after dependency partitioning.
    pub measure: Expr,
    pub section_captures: Vec<FVarId>,
    /// `T` is `Nat` at default transparency.
    pub nat: bool,
    /// ... and its active `WellFoundedRelation` is `Nat.lt_wfRel` (`isNatLtWF`).
    pub natural: bool,
}

/// The shared construction of one recursive component, closed over its fixed
/// parameters (`fun fixed => …`), so every member's context and the final
/// assembly instantiate the same terms at their own fixed locals.
pub(in crate::source) struct Plan {
    /// `<first>._mutual`.
    pub name: Name,
    /// Members in SCC order: the `PSum` positions.
    pub names: Vec<Name>,
    pub level_params: Vec<Name>,
    pub fixed: usize,
    pub arities: Vec<usize>,
    /// Each member's closed header type.
    pub types: Vec<Expr>,
    domain: Expr,
    codomain: Expr,
    measure: Expr,
    domains: Vec<Expr>,
}

/// The member of a planned group being elaborated in a context, and, once its
/// body succeeds, its fixpoint alternative `fun fixed => fun x a => body`.
#[derive(Clone)]
pub(in crate::source) struct MutualMember {
    plan: Arc<Plan>,
    index: usize,
    captures: Vec<LocalDecl>,
    piece: Option<Expr>,
}

impl MutualMember {
    pub(in crate::source) fn new(plan: Arc<Plan>, index: usize, captures: Vec<LocalDecl>) -> Self {
        Self {
            plan,
            index,
            captures,
            piece: None,
        }
    }

    pub(in crate::source) fn piece(&self) -> Option<&Expr> {
        self.piece.as_ref()
    }
}

/// Every member's private recursive reference in one member's body.
#[derive(Clone)]
pub(super) struct Targets {
    entries: Vec<Target>,
}

#[derive(Clone)]
struct Target {
    name: Name,
    marker: FVarId,
    reference: Typed,
    arity: usize,
    fixed: usize,
    domain: Expr,
}

impl Targets {
    pub(super) fn marks(&self, id: &FVarId) -> bool {
        self.entries.iter().any(|entry| &entry.marker == id)
    }

    pub(super) fn reference(&self, name: &Name) -> Option<&Typed> {
        self.entries
            .iter()
            .find(|entry| &entry.name == name)
            .map(|entry| &entry.reference)
    }

    pub(super) fn markers(&self) -> Vec<FVarId> {
        self.entries
            .iter()
            .map(|entry| entry.marker.clone())
            .collect()
    }

    pub(super) fn find(&self, id: &FVarId) -> Option<usize> {
        self.entries.iter().position(|entry| &entry.marker == id)
    }

    pub(super) fn arity(&self, target: usize) -> usize {
        self.entries[target].arity
    }

    pub(super) fn varying(&self, target: usize) -> Vec<usize> {
        (self.entries[target].fixed..self.entries[target].arity).collect()
    }

    pub(super) fn domain(&self, target: usize) -> Expr {
        self.entries[target].domain.clone()
    }

    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }
}

fn unsupported(shape: &'static str) -> NatDefinitionElabError {
    error(RecursionError::MutualWellFoundedUnsupported(shape))
}

fn scope() -> NatDefinitionElabError {
    failure(SourceInferenceError::Scope)
}

/// `Lean.SCC.scc` (Lean/Util/SCC.lean): Tarjan's algorithm over `vertices` in
/// order, each vertex's successors in the given order. Components come out in
/// completion order (dependencies first), each in DFS discovery order.
pub(in crate::source) fn strongly_connected(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    #[derive(Clone, Copy, Default)]
    struct Data {
        index: Option<usize>,
        lowlink: Option<usize>,
        on_stack: bool,
    }
    struct State<'a> {
        successors: &'a [Vec<usize>],
        data: Vec<Data>,
        stack: Vec<usize>,
        next: usize,
        components: Vec<Vec<usize>>,
    }
    fn lower(data: &mut Data, value: Option<usize>) {
        data.lowlink = match (data.lowlink, value) {
            (link, None) => link,
            (None, link) => link,
            (Some(left), Some(right)) => Some(left.min(right)),
        };
    }
    fn visit(state: &mut State<'_>, vertex: usize) {
        state.stack.push(vertex);
        state.data[vertex] = Data {
            index: Some(state.next),
            lowlink: Some(state.next),
            on_stack: true,
        };
        state.next += 1;
        for &successor in &state.successors[vertex] {
            if state.data[successor].index.is_none() {
                visit(state, successor);
                let link = state.data[successor].lowlink;
                lower(&mut state.data[vertex], link);
            } else if state.data[successor].on_stack {
                let index = state.data[successor].index;
                lower(&mut state.data[vertex], index);
            }
        }
        if state.data[vertex].lowlink == state.data[vertex].index {
            let mut component = Vec::new();
            while let Some(top) = state.stack.pop() {
                state.data[top].on_stack = false;
                component.push(top);
                if top == vertex {
                    break;
                }
            }
            component.reverse();
            state.components.push(component);
        }
    }
    let mut state = State {
        successors,
        data: vec![Data::default(); successors.len()],
        stack: Vec::new(),
        next: 0,
        components: Vec::new(),
    };
    for vertex in 0..successors.len() {
        if state.data[vertex].index.is_none() {
            visit(&mut state, vertex);
        }
    }
    state.components
}

/// `FixedParams.Info` (Lean/Elab/PreDefinition/FixedParams.lean): for each
/// function and parameter, `None` once known varying, else the observed edge
/// from each caller's parameter.
struct FixedInfo {
    graph: Vec<Vec<Option<Vec<Option<usize>>>>>,
    reverse_dependencies: Vec<Vec<Vec<usize>>>,
}

impl FixedInfo {
    fn new(reverse_dependencies: Vec<Vec<Vec<usize>>>) -> Self {
        let functions = reverse_dependencies.len();
        let mut graph: Vec<Vec<Option<Vec<Option<usize>>>>> = reverse_dependencies
            .iter()
            .map(|parameters| vec![Some(vec![None; functions]); parameters.len()])
            .collect();
        // `addSelfCalls`.
        for (function, parameters) in graph.iter_mut().enumerate() {
            for (parameter, callers) in parameters.iter_mut().enumerate() {
                if let Some(callers) = callers {
                    callers[function] = Some(parameter);
                }
            }
        }
        Self {
            graph,
            reverse_dependencies,
        }
    }

    fn may_be_fixed(&self, function: usize, parameter: usize) -> bool {
        self.graph[function][parameter].is_some()
    }

    fn caller_parameter(&self, callee: usize, argument: usize, caller: usize) -> Option<usize> {
        self.graph[callee][argument]
            .as_ref()
            .and_then(|callers| callers[caller])
    }

    fn set_varying(&mut self, function: usize, parameter: usize) {
        if !self.may_be_fixed(function, parameter) {
            return;
        }
        self.graph[function][parameter] = None;
        for other in 0..self.graph.len() {
            for other_parameter in 0..self.graph[other].len() {
                if self.graph[other][other_parameter]
                    .as_ref()
                    .is_some_and(|callers| callers[function] == Some(parameter))
                {
                    self.set_varying(other, other_parameter);
                }
            }
        }
        for dependent in self.reverse_dependencies[function][parameter].clone() {
            self.set_varying(function, dependent);
        }
    }

    fn set_caller_parameter(
        &mut self,
        callee: usize,
        argument: usize,
        caller: usize,
        parameter: usize,
    ) {
        if !self.may_be_fixed(callee, argument) {
            return;
        }
        if !self.may_be_fixed(caller, parameter) {
            self.set_varying(callee, argument);
            return;
        }
        if let Some(previous) = self.caller_parameter(callee, argument, caller) {
            if previous != parameter {
                self.set_varying(callee, argument);
            }
            return;
        }
        if let Some(callers) = self.graph[callee][argument].as_mut() {
            callers[caller] = Some(parameter);
        }
        if let Some(caller_edges) = self.graph[caller][parameter].clone() {
            for (other, other_parameter) in caller_edges.into_iter().enumerate() {
                if let Some(other_parameter) = other_parameter {
                    self.set_caller_parameter(callee, argument, other, other_parameter);
                }
            }
        }
        for other in 0..self.graph.len() {
            for other_argument in 0..self.graph[other].len() {
                if self.graph[other][other_argument]
                    .as_ref()
                    .is_some_and(|callers| callers[callee] == Some(argument))
                {
                    self.set_caller_parameter(other, other_argument, caller, parameter);
                }
            }
        }
    }
}

fn strip_metadata(mut expr: &Expr) -> &Expr {
    while let ExprNode::MData { expr: inner, .. } = expr.node() {
        expr = inner;
    }
    expr
}

impl Context {
    /// The group's body pass: record this member's hint. A measure is elaborated
    /// in a discarded probe, at the actual parameters the well-founded engine
    /// would bind; a recoverable failure is kept until the member's component
    /// is known, since the pin ignores the hints of a nonrecursive definition.
    pub(in crate::source) fn record_mutual_member_hint(
        &mut self,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: Option<&TerminationHint<'_>>,
        header_parameters: usize,
    ) -> Result<(), NatDefinitionElabError> {
        let observed = match hint {
            None | Some(TerminationHint::Automatic) => MemberHint::None,
            Some(TerminationHint::Structural(_)) => MemberHint::Structural,
            Some(TerminationHint::WellFounded { hint, .. }) if hint.measure.is_none() => {
                MemberHint::DecreasingOnly
            }
            Some(TerminationHint::WellFounded { hint, allowed }) => {
                let mut probe = self.clone();
                let measured = probe.measure_mutual_member(
                    parameters,
                    syntax,
                    expected,
                    hint,
                    header_parameters,
                    *allowed,
                );
                self.txn.budget.heartbeats_consumed = probe.txn.budget.heartbeats_consumed;
                match measured {
                    Err(problem) if !tactics::backtrack::recoverable(&problem) => {
                        return Err(problem);
                    }
                    measured => MemberHint::Measured(measured),
                }
            }
        };
        if let Some(state) = self.partial.as_mut() {
            state.member_hint = Some(observed);
        }
        Ok(())
    }

    fn measure_mutual_member(
        &mut self,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: &Hint<'_>,
        header_parameters: usize,
        allowed: bool,
    ) -> Result<Measured, NatDefinitionElabError> {
        if !allowed {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "well-founded recursion in a safe def declaration",
            });
        }
        let mut parameters = parameters.to_vec();
        self.open_recursive_lambdas(syntax, expected, &mut parameters)?;
        let measure = self.well_founded_measure(hint, &parameters, header_parameters)?;
        let value = self.instantiate(&measure.value)?;
        let type_ = self.instantiate(&measure.type_)?;
        let nat_type = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let nat = self.well_founded_default_conversion(&type_, &nat_type)?;
        let natural = nat
            && self
                .select_well_founded_relation(
                    Typed {
                        value: value.clone(),
                        type_: nat_type,
                    },
                    &parameters,
                )?
                .natural;
        let mut value = self.instantiate(&value)?;
        for parameter in parameters.iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&parameter.type_)?;
            value = Expr::lam(
                parameter.user_name.clone(),
                domain,
                value.abstract_fvar(&parameter.id, 0).map_err(|_| scope())?,
                parameter.binder_info,
            );
        }
        self.require_resolved_terms(std::slice::from_ref(&value))?;
        let captures = self.section_parameters(std::slice::from_ref(&value), false)?;
        let closed = self.close_mutual_fixed(&value, &captures, true)?;
        if closed.has_fvar() || closed.has_level_mvar() {
            return Err(unsupported("a closed termination measure"));
        }
        Ok(Measured {
            arity: parameters.len(),
            measure: value,
            section_captures: captures.into_iter().map(|capture| capture.id).collect(),
            nat,
            natural,
        })
    }

    /// `partitionPreDefs`' successors: the group members `foldConsts` meets in
    /// `value`, in reverse order of first occurrence (Lean/Util/FoldConsts.lean
    /// visits a binder's type before its body and a function before its argument).
    pub(in crate::source) fn mutual_call_order(
        &mut self,
        value: &Expr,
        names: &[Name],
    ) -> Result<Vec<usize>, NatDefinitionElabError> {
        let mut visited = HashSet::new();
        let mut constants = HashSet::new();
        let mut order = Vec::new();
        let mut pending = vec![value];
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !visited.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::ForallE {
                    binder_type, body, ..
                }
                | ExprNode::Lam {
                    binder_type, body, ..
                } => {
                    pending.push(body);
                    pending.push(binder_type);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    pending.push(body);
                    pending.push(value);
                    pending.push(type_);
                }
                ExprNode::App { f, a } => {
                    pending.push(a);
                    pending.push(f);
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
                ExprNode::Const { name, .. } => {
                    if constants.insert(name.clone())
                        && let Some(index) = names.iter().position(|member| member == name)
                    {
                        order.push(index);
                    }
                }
                _ => {}
            }
        }
        order.reverse();
        Ok(order)
    }

    /// `getFixedParamPerms` on the group's closed bodies, `values[i]` binding
    /// `arities[i]` parameters. `Some(k)` when the fixed parameters are the
    /// first `k` of every member, unreordered (`fixedArePrefix`); `None` when
    /// they are not. An argument is a fixed parameter here only when it is that
    /// parameter itself; the pin also accepts reducibly defeq arguments.
    pub(in crate::source) fn mutual_fixed_prefix(
        &mut self,
        values: &[Expr],
        arities: &[usize],
        names: &[Name],
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        self.mutual_fixed_prefix_core(values, arities, names, false)
    }

    /// Structural product motives can generalize unchanged trailing arguments as well as
    /// changing ones. Preserve only the common leading fixed prefix, without imposing the
    /// well-founded packer's stronger `fixedArePrefix` restriction on every argument.
    pub(in crate::source) fn mutual_structural_fixed_prefix(
        &mut self,
        values: &[Expr],
        arities: &[usize],
        names: &[Name],
    ) -> Result<usize, NatDefinitionElabError> {
        self.mutual_fixed_prefix_core(values, arities, names, true)?
            .ok_or_else(scope)
    }

    fn mutual_fixed_prefix_core(
        &mut self,
        values: &[Expr],
        arities: &[usize],
        names: &[Name],
        generalize_trailing: bool,
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        let mut reverse_dependencies = Vec::new();
        let mut bodies = Vec::new();
        for (value, &arity) in values.iter().zip(arities) {
            let mut binder_types = Vec::new();
            let mut body = value;
            for _ in 0..arity {
                self.tick()?;
                let ExprNode::Lam {
                    binder_type,
                    body: next,
                    ..
                } = body.node()
                else {
                    return Err(unsupported(
                        "a member whose value binds each of its recursive parameters",
                    ));
                };
                binder_types.push(binder_type.clone());
                body = next;
            }
            // The pin's arity is the value's whole leading lambda telescope.
            if matches!(body.node(), ExprNode::Lam { .. }) {
                return Err(unsupported(
                    "a member whose elaborated value binds more parameters than its source",
                ));
            }
            let mut dependencies = Vec::new();
            for earlier in 0..arity {
                let mut dependents = Vec::new();
                for (later, binder_type) in binder_types.iter().enumerate().skip(earlier + 1) {
                    self.tick()?;
                    let index = u32::try_from(later - 1 - earlier).map_err(|_| scope())?;
                    if binder_type.has_loose_bvar(index) {
                        dependents.push(later);
                    }
                }
                dependencies.push(dependents);
            }
            reverse_dependencies.push(dependencies);
            bodies.push(body.clone());
        }
        let mut info = FixedInfo::new(reverse_dependencies);
        for (caller, body) in bodies.iter().enumerate() {
            // Meta.transform's order: an application before its arguments,
            // a binder's type before its body.
            let mut pending = vec![(body, 0usize)];
            while let Some((expr, depth)) = pending.pop() {
                self.tick()?;
                match expr.node() {
                    ExprNode::App { .. } => {
                        let mut head = expr;
                        let mut arguments = Vec::new();
                        while let ExprNode::App { f, a } = head.node() {
                            arguments.push(a);
                            head = f;
                        }
                        arguments.reverse();
                        let callee = match head.node() {
                            ExprNode::Const { name, .. } => {
                                names.iter().position(|member| member == name)
                            }
                            _ => None,
                        };
                        if let Some(callee) = callee {
                            self.observe_mutual_call(
                                &mut info,
                                (caller, callee),
                                &arguments,
                                depth,
                                arities,
                            )?;
                        } else if !matches!(head.node(), ExprNode::Const { .. }) {
                            arguments.insert(0, head);
                        }
                        for argument in arguments.into_iter().rev() {
                            pending.push((argument, depth));
                        }
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        pending.push((body, depth + 1));
                        pending.push((binder_type, depth));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        pending.push((body, depth + 1));
                        pending.push((value, depth));
                        pending.push((type_, depth));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        pending.push((expr, depth));
                    }
                    _ => {}
                }
            }
        }
        if generalize_trailing {
            let mut prefix = arities.iter().copied().min().ok_or_else(scope)?;
            for parameters in &info.graph {
                let leading = parameters
                    .iter()
                    .enumerate()
                    .take_while(|(position, callers)| {
                        callers
                            .as_ref()
                            .is_some_and(|callers| callers[0] == Some(*position))
                    })
                    .count();
                prefix = prefix.min(leading);
            }
            return Ok(Some(prefix));
        }
        // `getFixedParamPerms`, then `fixedArePrefix`.
        let mut first = Vec::new();
        let mut fixed = 0usize;
        for (parameter, callers) in info.graph[0].iter().enumerate() {
            match callers {
                Some(callers) if callers[0] == Some(parameter) => {
                    first.push(Some(fixed));
                    fixed += 1;
                }
                Some(_) => return Err(scope()),
                None => first.push(None),
            }
        }
        for parameters in &info.graph {
            if parameters.len() < fixed {
                return Ok(None);
            }
            for (parameter, callers) in parameters.iter().enumerate() {
                self.tick()?;
                let position = match callers {
                    Some(callers) => Some(
                        callers[0]
                            .and_then(|index| first.get(index).copied().flatten())
                            .ok_or_else(scope)?,
                    ),
                    None => None,
                };
                let expected = (parameter < fixed).then_some(parameter);
                if position != expected {
                    return Ok(None);
                }
            }
        }
        Ok(Some(fixed))
    }

    fn observe_mutual_call(
        &mut self,
        info: &mut FixedInfo,
        (caller, callee): (usize, usize),
        arguments: &[&Expr],
        depth: usize,
        arities: &[usize],
    ) -> Result<(), NatDefinitionElabError> {
        let caller_arity = arities[caller];
        let is_parameter = |argument: &Expr, parameter: usize| {
            matches!(strip_metadata(argument).node(), ExprNode::BVar { idx }
                if usize::try_from(*idx).ok() == Some(depth + caller_arity - 1 - parameter))
        };
        for argument_index in 0..arities[callee] {
            self.tick()?;
            if !info.may_be_fixed(callee, argument_index) {
                continue;
            }
            let Some(argument) = arguments.get(argument_index) else {
                info.set_varying(callee, argument_index);
                continue;
            };
            if let Some(parameter) = info.caller_parameter(callee, argument_index, caller) {
                if !is_parameter(argument, parameter) {
                    info.set_varying(callee, argument_index);
                }
                continue;
            }
            let mut any = false;
            for parameter in 0..caller_arity {
                if info.may_be_fixed(caller, parameter) && is_parameter(argument, parameter) {
                    info.set_caller_parameter(callee, argument_index, caller, parameter);
                    any = true;
                }
            }
            if !any {
                info.set_varying(callee, argument_index);
            }
        }
        Ok(())
    }

    /// Open the first `count` binders of a closed type as locals.
    fn open_mutual_fixed(
        &mut self,
        type_: &Expr,
        count: usize,
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let mut type_ = type_.clone();
        let mut locals = Vec::new();
        for _ in 0..count {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                binder_type.clone(),
                *binder_info,
            );
            locals.push(self.txn.lctx.find(&id).ok_or_else(scope)?.clone());
            let next = self.substitute(body, &Expr::fvar(id))?;
            type_ = next;
        }
        Ok(locals)
    }

    /// `fun fixed => body`, from a term over the fixed locals.
    pub(in crate::source) fn close_mutual_fixed(
        &mut self,
        body: &Expr,
        fixed: &[LocalDecl],
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut body = self.instantiate(body)?;
        for local in fixed.iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            let abstracted = body.abstract_fvar(&local.id, 0).map_err(|_| scope())?;
            body = if lambda {
                Expr::lam(
                    local.user_name.clone(),
                    domain,
                    abstracted,
                    local.binder_info,
                )
            } else {
                Expr::forall_e(
                    local.user_name.clone(),
                    domain,
                    abstracted,
                    local.binder_info,
                )
            };
        }
        Ok(body)
    }

    /// A closed `fun fixed => body` at these fixed arguments.
    fn open_mutual_closed(
        &mut self,
        closed: &Expr,
        fixed: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut body = closed.clone();
        for argument in fixed {
            let ExprNode::Lam { body: next, .. } = body.node() else {
                return Err(scope());
            };
            let next = self.substitute(next, argument)?;
            body = next;
        }
        Ok(body)
    }

    fn mutual_apply(
        &mut self,
        name: &[&str],
        arguments: impl IntoIterator<Item = Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut function = self.constant(&Name::from_components(name.iter().copied()))?;
        for value in arguments {
            self.tick()?;
            let type_ = self
                .known_type(&value)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            function = self.match_apply(function, Typed { value, type_ })?;
        }
        Ok(function)
    }

    fn psum_parts(&mut self, domain: &Expr) -> Result<(Expr, Expr), NatDefinitionElabError> {
        let domain = self.whnf(domain)?;
        let (head, arguments) = operators::spine(&domain);
        if !matches!(head.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components(["PSum"]))
            || arguments.len() != 2
        {
            return Err(failure(SourceInferenceError::ExpectedType));
        }
        Ok((arguments[0].clone(), arguments[1].clone()))
    }

    /// `Mutual.pack`: `PSum.inl` at the member's own position, `PSum.inr`
    /// around every later one; the last member has no `inl`.
    pub(super) fn inject_mutual_argument(
        &mut self,
        domain: &Expr,
        index: usize,
        count: usize,
        value: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut layers = Vec::new();
        let mut type_ = domain.clone();
        let mut injected = None;
        for position in 0..count.saturating_sub(1) {
            self.tick()?;
            let (left, right) = self.psum_parts(&type_)?;
            if position == index {
                injected = Some(
                    self.mutual_apply(&["PSum", "inl"], [left, right, value.clone()])?
                        .value,
                );
                break;
            }
            layers.push((left, right.clone()));
            type_ = right;
        }
        let mut injected = match injected {
            Some(injected) => injected,
            None if index + 1 == count => {
                let actual = self
                    .known_type(&value)?
                    .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                self.constrain_type(&actual, &type_)?;
                value
            }
            None => return Err(scope()),
        };
        for (left, right) in layers.into_iter().rev() {
            self.tick()?;
            injected = self
                .mutual_apply(&["PSum", "inr"], [left, right, injected])?
                .value;
        }
        Ok(injected)
    }

    /// `PSum.casesOn (motive := motive) major leaves₀ (fun _x => …)` over the
    /// right-nested sum, as `Mutual.mkCodomain` and `WF.Fix`'s `processSumCasesOn`
    /// build it. With `thread`, each nested sum's minor also takes and passes on
    /// the continuation, the motive's leading argument.
    fn mutual_cases(
        &mut self,
        domain: &Expr,
        major: &Expr,
        motive: &Expr,
        leaves: &[Expr],
        thread: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let (left, right) = self.psum_parts(domain)?;
        let ExprNode::Lam {
            body: motive_body, ..
        } = motive.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let (first, rest) = leaves.split_first().ok_or_else(scope)?;
        let minor = if let [last] = rest {
            last.clone()
        } else {
            let saved = self.txn.lctx.clone();
            let result = (|| {
                let user = Name::from_components(["_x"]);
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    user.clone(),
                    right.clone(),
                    BinderInfo::Default,
                );
                let inner = Expr::fvar(id.clone());
                let injected = self
                    .mutual_apply(
                        &["PSum", "inr"],
                        [left.clone(), right.clone(), inner.clone()],
                    )?
                    .value;
                let at_inner = self.substitute(motive_body, &injected)?;
                let inner_motive = Expr::lam(
                    user.clone(),
                    right.clone(),
                    at_inner.abstract_fvar(&id, 0).map_err(|_| scope())?,
                    BinderInfo::Default,
                );
                let mut nested = self.mutual_cases(&right, &inner, &inner_motive, rest, thread)?;
                if thread {
                    let ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        binder_info,
                        ..
                    } = at_inner.node()
                    else {
                        return Err(failure(SourceInferenceError::ExpectedFunction));
                    };
                    let continuation = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        continuation.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    );
                    nested = Expr::app(nested, Expr::fvar(continuation.clone()));
                    nested = Expr::lam(
                        binder_name.clone(),
                        binder_type.clone(),
                        nested
                            .abstract_fvar(&continuation, 0)
                            .map_err(|_| scope())?,
                        *binder_info,
                    );
                }
                let nested = self.instantiate(&nested)?;
                Ok(Expr::lam(
                    user,
                    right.clone(),
                    nested.abstract_fvar(&id, 0).map_err(|_| scope())?,
                    BinderInfo::Default,
                ))
            })();
            self.txn.lctx = saved;
            result?
        };
        Ok(self
            .mutual_apply(
                &["PSum", "casesOn"],
                [
                    left,
                    right,
                    motive.clone(),
                    major.clone(),
                    first.clone(),
                    minor,
                ],
            )?
            .value)
    }

    /// `WellFounded.Nat.fix D C measure`, the pin's `isNatLtWF` specialization.
    fn mutual_fix(
        &mut self,
        domain: Expr,
        codomain: Expr,
        measure: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let name = Name::from_components(["WellFounded", "Nat", "fix"]);
        if !matches!(
            self.txn.env.find(&name),
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe
        ) {
            return Err(failure(SourceInferenceError::UnknownConstant(name)));
        }
        self.mutual_apply(&["WellFounded", "Nat", "fix"], [domain, codomain, measure])
    }

    /// Build the shared domain, codomain and measure of a component, closed over
    /// its fixed parameters (member 0's binders; every member's must agree).
    pub(in crate::source) fn mutual_well_founded_plan(
        &mut self,
        names: Vec<Name>,
        types: Vec<Expr>,
        arities: Vec<usize>,
        measures: &[Expr],
        fixed: usize,
        level_params: Vec<Name>,
    ) -> Result<Plan, NatDefinitionElabError> {
        self.level_params = level_params.clone();
        self.explicit_levels = level_params.len();
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let fixed_locals = self.open_mutual_fixed(&types[0], fixed)?;
            let mut domains = Vec::new();
            let mut codomains = Vec::new();
            let mut packed_measures = Vec::new();
            let mut sort: Option<Level> = None;
            for (index, type_) in types.iter().enumerate() {
                let before = self.txn.lctx.clone();
                let mut type_ = type_.clone();
                for local in &fixed_locals {
                    self.tick()?;
                    if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                        type_ = self.whnf(&type_)?;
                    }
                    let ExprNode::ForallE {
                        binder_type, body, ..
                    } = type_.node()
                    else {
                        return Err(failure(SourceInferenceError::ExpectedFunction));
                    };
                    if self.instantiate(binder_type)? != self.instantiate(&local.type_)? {
                        return Err(unsupported("fixed parameters of one type in every member"));
                    }
                    let next = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                    type_ = next;
                }
                let mut varying = Vec::new();
                for _ in fixed..arities[index] {
                    self.tick()?;
                    if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                        type_ = self.whnf(&type_)?;
                    }
                    let ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } = type_.node()
                    else {
                        return Err(failure(SourceInferenceError::ExpectedFunction));
                    };
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    );
                    varying.push(self.txn.lctx.find(&id).ok_or_else(scope)?.clone());
                    let next = self.substitute(body, &Expr::fvar(id))?;
                    type_ = next;
                }
                if varying.is_empty() {
                    return Err(error(RecursionError::WellFoundedArgumentRequired));
                }
                let result_sort = self
                    .known_type(&type_)?
                    .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                let result_sort = self.whnf(&result_sort)?;
                let ExprNode::Sort { level } = result_sort.node() else {
                    return Err(failure(SourceInferenceError::ExpectedType));
                };
                let level = level.normalize();
                match &sort {
                    Some(previous) if previous != &level => {
                        return Err(unsupported("member results in one universe"));
                    }
                    Some(_) => {}
                    None => sort = Some(level),
                }
                let domain = self.well_founded_domain(&varying)?;
                codomains.push(self.well_founded_motive(&varying, &domain, &type_)?);
                let mut measure = measures[index].clone();
                for local in fixed_locals.iter().chain(&varying) {
                    let ExprNode::Lam { body, .. } = measure.node() else {
                        return Err(scope());
                    };
                    let next = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                    measure = next;
                }
                let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
                packed_measures.push(
                    self.uncurry_well_founded_value(
                        &varying,
                        Typed {
                            value: measure,
                            type_: nat,
                        },
                    )?
                    .value,
                );
                domains.push(domain);
                self.txn.lctx = before;
            }
            let mut domain = domains.last().cloned().ok_or_else(scope)?;
            for part in domains.iter().rev().skip(1) {
                self.tick()?;
                domain = self.mutual_apply(&["PSum"], [part.clone(), domain])?.value;
            }
            let sort = sort.ok_or_else(scope)?;
            let codomain = self.mutual_function_of_sum(&domain, Expr::sort(sort), &codomains)?;
            let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
            let measure = self.mutual_function_of_sum(&domain, nat, &packed_measures)?;
            let mut closed_domains = Vec::new();
            for part in &domains {
                closed_domains.push(self.close_mutual_fixed(part, &fixed_locals, true)?);
            }
            let plan = Plan {
                name: Name::str(names[0].clone(), "_mutual"),
                names: names.clone(),
                level_params: level_params.clone(),
                fixed,
                arities: arities.clone(),
                types: types.clone(),
                domain: self.close_mutual_fixed(&domain, &fixed_locals, true)?,
                codomain: self.close_mutual_fixed(&codomain, &fixed_locals, true)?,
                measure: self.close_mutual_fixed(&measure, &fixed_locals, true)?,
                domains: closed_domains,
            };
            for term in [&plan.domain, &plan.codomain, &plan.measure]
                .into_iter()
                .chain(&plan.domains)
            {
                self.require_resolved_terms(std::slice::from_ref(term))?;
                if term.has_fvar() || term.has_level_mvar() || term.has_loose_bvars() {
                    return Err(scope());
                }
            }
            Ok(plan)
        })();
        self.txn.lctx = saved;
        result
    }

    /// `fun x => PSum.casesOn x leaf₀ (fun _x => PSum.casesOn _x leaf₁ …)` with
    /// the constant motive `fun x => result`.
    fn mutual_function_of_sum(
        &mut self,
        domain: &Expr,
        result: Expr,
        leaves: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let outcome = (|| {
            let user = Name::from_components(["x"]);
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                user.clone(),
                domain.clone(),
                BinderInfo::Default,
            );
            let major = Expr::fvar(id.clone());
            let motive = Expr::lam(user.clone(), domain.clone(), result, BinderInfo::Default);
            let body = if let [only] = leaves {
                Expr::app(only.clone(), major)
            } else {
                self.mutual_cases(domain, &major, &motive, leaves, false)?
            };
            let body = self.instantiate(&body)?;
            Ok(Expr::lam(
                user,
                domain.clone(),
                body.abstract_fvar(&id, 0).map_err(|_| scope())?,
                BinderInfo::Default,
            ))
        })();
        self.txn.lctx = saved;
        outcome
    }

    /// One member's body against the group's shared fixpoint. The result is the
    /// member's wrapper body `<first>._mutual fixed (inject ⟨varying⟩)`; the
    /// fixpoint alternative is kept on the context for the group's assembly.
    pub(in crate::source) fn mutual_well_founded_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: Option<&TerminationHint<'_>>,
        header_parameters: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        let member = self.mutual_member.clone().ok_or_else(scope)?;
        let plan = member.plan.clone();
        let index = member.index;
        if plan.names.get(index) != Some(name) || self.well_founded.is_some() {
            return Err(scope());
        }
        let Some(TerminationHint::WellFounded {
            hint,
            allowed: true,
        }) = hint
        else {
            return Err(scope());
        };
        let mut parameters = parameters.to_vec();
        let (body, expected, lambdas) =
            self.open_recursive_lambdas(syntax, expected, &mut parameters)?;
        let header_parameters = header_parameters
            .checked_add(member.captures.len())
            .ok_or_else(scope)?;
        parameters.splice(0..0, member.captures.iter().cloned());
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        if parameters.len() != plan.arities[index] || parameters.len() <= plan.fixed {
            return Err(unsupported(
                "a member binding the same parameters in its body pass and its fixpoint",
            ));
        }
        let fixed_values: Vec<_> = parameters[..plan.fixed]
            .iter()
            .map(|parameter| Expr::fvar(parameter.id.clone()))
            .collect();
        let varying_parameters = parameters[plan.fixed..].to_vec();
        let varying_values: Vec<_> = varying_parameters
            .iter()
            .map(|parameter| Expr::fvar(parameter.id.clone()))
            .collect();
        let domain = self.open_mutual_closed(&plan.domain, &fixed_values)?;
        let codomain = self.open_mutual_closed(&plan.codomain, &fixed_values)?;
        let measure = self.open_mutual_closed(&plan.measure, &fixed_values)?;
        let mut domains = Vec::new();
        for part in &plan.domains {
            domains.push(self.open_mutual_closed(part, &fixed_values)?);
        }
        let packed = self
            .pack_well_founded_arguments(&domains[index], &varying_values)?
            .value;
        let current = self.inject_mutual_argument(&domain, index, plan.names.len(), packed)?;
        let fix = self.mutual_fix(domain, codomain, measure)?;
        let saved = self.txn.lctx.clone();
        let fix_type = self.whnf(&fix.type_)?;
        let ExprNode::ForallE {
            binder_type: functional_type,
            ..
        } = fix_type.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let functional_type = self.whnf(functional_type)?;
        let ExprNode::ForallE { body: at, .. } = functional_type.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let at_major = self.substitute(at, &current)?;
        let at_major = self.whnf(&at_major)?;
        let ExprNode::ForallE {
            binder_type: continuation_type,
            ..
        } = at_major.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let continuation_name = self.fresh_name()?;
        let continuation_id = FVarId(continuation_name.clone());
        self.txn.lctx.add_param(
            continuation_id.clone(),
            continuation_name,
            continuation_type.clone(),
            BinderInfo::Default,
        );
        let continuation = self
            .txn
            .lctx
            .find(&continuation_id)
            .ok_or_else(scope)?
            .clone();
        let mut entries = Vec::new();
        for (target, member_name) in plan.names.iter().enumerate() {
            self.tick()?;
            let marker = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                marker.clone(),
                Name::anonymous(),
                plan.types[target].clone(),
                BinderInfo::Default,
            );
            let mut reference = Typed {
                value: Expr::fvar(marker.clone()),
                type_: plan.types[target].clone(),
            };
            for capture in &member.captures {
                reference = self.course_apply(reference, Expr::fvar(capture.id.clone()))?;
            }
            entries.push(Target {
                name: member_name.clone(),
                marker,
                reference,
                arity: plan.arities[target],
                fixed: plan.fixed,
                domain: domains[target].clone(),
            });
        }
        let own = entries[index].clone();
        self.well_founded = Some(State {
            name: name.clone(),
            reference: own.reference,
            marker: own.marker,
            parameters: parameters.clone(),
            varying: (plan.fixed..parameters.len()).collect(),
            fixed: parameters[..plan.fixed]
                .iter()
                .cloned()
                .enumerate()
                .collect(),
            measure_captures: HashSet::new(),
            natural_measure: true,
            continuation: continuation.clone(),
            proof_inaccessible: parameters[header_parameters..]
                .iter()
                .map(|parameter| parameter.id.clone())
                .collect(),
            proof_hidden: HashSet::new(),
            branch_scopes: Vec::new(),
            calls: HashMap::new(),
            goals: Vec::new(),
            proving: false,
            mutual: Some(Targets { entries }),
        });
        let result = (|| {
            let term = self.term(body, Some(expected.clone()))?;
            self.resolve_instances_with_defaults()?;
            self.resume_postponed_eliminators(true)?;
            self.flush(true)?;
            self.complete_local_functions()?;
            let value = self.instantiate(&term.value)?;
            let state = self.well_founded.as_ref().ok_or_else(scope)?;
            let markers = state.markers();
            let reads = self.elimination_reads(&value)?;
            if markers.iter().any(|marker| reads.contains(marker)) {
                return Err(error(RecursionError::PartialApplication));
            }
            let live = self.txn.mvars.collect_mvars(&value);
            let obligations: Vec<_> = self
                .well_founded
                .as_ref()
                .ok_or_else(scope)?
                .goals
                .iter()
                .filter(|obligation| live.contains(&obligation.transport))
                .cloned()
                .collect();
            if !obligations.is_empty() {
                self.well_founded.as_mut().ok_or_else(scope)?.proving = true;
                let goals = self.prepare_decreasing_goals(&obligations)?;
                let automatic;
                let proof = match hint.decreasing {
                    Some(proof) => proof,
                    None => {
                        automatic = automatic_decreasing_proof();
                        &automatic
                    }
                };
                let prepared = self.lower_pattern_matrices(proof)?;
                self.prove_decreasing_goals(&prepared, goals, hint.decreasing.is_some())?;
                self.assign_decreasing_transports(obligations)?;
            }
            let mut value = self.instantiate(&value)?;
            self.require_resolved_terms(std::slice::from_ref(&value))?;
            value = Expr::lam(
                continuation.user_name.clone(),
                self.instantiate(&continuation.type_)?,
                value
                    .abstract_fvar(&continuation.id, 0)
                    .map_err(|_| scope())?,
                BinderInfo::Default,
            );
            let type_ = self
                .known_type(&value)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let mut alternative =
                self.uncurry_well_founded_value(&varying_parameters, Typed { value, type_ })?;
            // Peers outside this component are the group's header locals until
            // the group closes them into their constants.
            self.close_partial_group_references(&mut alternative)?;
            let piece =
                self.close_mutual_fixed(&alternative.value, &parameters[..plan.fixed], true)?;
            self.require_resolved_terms(std::slice::from_ref(&piece))?;
            if piece.has_fvar() || piece.has_loose_bvars() || piece.has_level_mvar() {
                return Err(scope());
            }
            Ok(piece)
        })();
        self.well_founded = None;
        self.txn.lctx = saved;
        let piece = result?;
        self.mutual_member.as_mut().ok_or_else(scope)?.piece = Some(piece);
        let levels = plan
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let mut wrapper = Expr::const_(plan.name.clone(), levels);
        for argument in fixed_values {
            wrapper = Expr::app(wrapper, argument);
        }
        wrapper = Expr::app(wrapper, current);
        self.close_recursive_lambdas(
            &lambdas,
            Typed {
                value: wrapper,
                type_: expected,
            },
        )
    }

    /// `<first>._mutual := fun fixed => WellFounded.Nat.fix D C measure
    /// (fun x a => PSum.casesOn (motive := fun x => FT x → C x) x alt₀ … a)`.
    pub(in crate::source) fn assemble_mutual_well_founded(
        &mut self,
        plan: &Plan,
        pieces: &[Expr],
    ) -> Result<DefinitionVal, NatDefinitionElabError> {
        self.level_params = plan.level_params.clone();
        self.explicit_levels = plan.level_params.len();
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let fixed = self.open_mutual_fixed(&plan.types[0], plan.fixed)?;
            let fixed_values: Vec<_> = fixed
                .iter()
                .map(|local| Expr::fvar(local.id.clone()))
                .collect();
            let domain = self.open_mutual_closed(&plan.domain, &fixed_values)?;
            let codomain = self.open_mutual_closed(&plan.codomain, &fixed_values)?;
            let measure = self.open_mutual_closed(&plan.measure, &fixed_values)?;
            let mut alternatives = Vec::new();
            for piece in pieces {
                alternatives.push(self.open_mutual_closed(piece, &fixed_values)?);
            }
            let fix = self.mutual_fix(domain.clone(), codomain, measure)?;
            let fix_type = self.whnf(&fix.type_)?;
            let ExprNode::ForallE {
                binder_type: functional_type,
                ..
            } = fix_type.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            let functional_type = self.whnf(functional_type)?;
            let ExprNode::ForallE {
                binder_name,
                body: at,
                ..
            } = functional_type.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            let motive = Expr::lam(
                binder_name.clone(),
                domain.clone(),
                at.clone(),
                BinderInfo::Default,
            );
            let major = FVarId(self.fresh_name()?);
            let major_name = Name::from_components(["x"]);
            self.txn.lctx.add_param(
                major.clone(),
                major_name.clone(),
                domain.clone(),
                BinderInfo::Default,
            );
            let at_major = self.substitute(at, &Expr::fvar(major.clone()))?;
            let ExprNode::ForallE {
                binder_type: continuation_type,
                ..
            } = at_major.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            let continuation = FVarId(self.fresh_name()?);
            let continuation_name = Name::from_components(["a"]);
            self.txn.lctx.add_param(
                continuation.clone(),
                continuation_name.clone(),
                continuation_type.clone(),
                BinderInfo::Default,
            );
            let cases = self.mutual_cases(
                &domain,
                &Expr::fvar(major.clone()),
                &motive,
                &alternatives,
                true,
            )?;
            let body = Expr::app(cases, Expr::fvar(continuation.clone()));
            let body = self.instantiate(&body)?;
            let functional = Expr::lam(
                major_name.clone(),
                domain.clone(),
                Expr::lam(
                    continuation_name,
                    continuation_type.clone(),
                    body.abstract_fvar(&continuation, 0).map_err(|_| scope())?,
                    BinderInfo::Default,
                )
                .abstract_fvar(&major, 0)
                .map_err(|_| scope())?,
                BinderInfo::Default,
            );
            self.txn.lctx.truncate(self.txn.lctx.len() - 2);
            let functional_actual = self
                .known_type(&functional)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let applied = self.match_apply(
                fix,
                Typed {
                    value: functional,
                    type_: functional_actual,
                },
            )?;
            let value = self.close_mutual_fixed(&applied.value, &fixed, true)?;
            let type_ = self.close_mutual_fixed(&applied.type_, &fixed, false)?;
            self.require_resolved_terms(&[value.clone(), type_.clone()])?;
            if value.has_fvar() || type_.has_fvar() || value.has_level_mvar() {
                return Err(scope());
            }
            let term = Typed {
                value: value.clone(),
                type_: type_.clone(),
            };
            if self.check_definition_codegen(&term)? {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "computable ordinary mutual definition",
                });
            }
            Ok(DefinitionVal {
                base: ConstantVal {
                    name: plan.name.clone(),
                    level_params: plan.level_params.clone(),
                    type_,
                },
                value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![plan.name.clone()],
            })
        })();
        self.txn.lctx = saved;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn components_follow_the_pins_tarjan_order() {
        // a → c, c → b, b → a: one component, discovered a, c, b.
        assert_eq!(
            strongly_connected(&[vec![2], vec![0], vec![1]]),
            vec![vec![0, 2, 1]]
        );
        // first → last; middle alone; completion order puts dependencies first.
        assert_eq!(
            strongly_connected(&[vec![2], vec![], vec![]]),
            vec![vec![2], vec![0], vec![1]]
        );
        // a calls c then b (successors in reverse first occurrence: b, c).
        assert_eq!(
            strongly_connected(&[vec![1, 2], vec![0], vec![0]]),
            vec![vec![0, 1, 2]]
        );
    }

    #[test]
    fn fixed_parameter_analysis_reorders_like_the_pin() {
        // f (x n) calls g x n; g (n x) calls f x n: x fixed but reordered.
        let mut info = FixedInfo::new(vec![vec![vec![], vec![]], vec![vec![], vec![]]]);
        // f calls g with arguments (x, n) = (f.0, f.1) at g's positions (0, 1)
        info.set_caller_parameter(1, 1, 0, 0);
        info.set_varying(1, 0);
        info.set_caller_parameter(0, 0, 1, 1);
        info.set_varying(0, 1);
        assert!(info.may_be_fixed(0, 0));
        assert!(info.may_be_fixed(1, 1));
        assert!(!info.may_be_fixed(0, 1));
        assert!(!info.may_be_fixed(1, 0));
    }
}
