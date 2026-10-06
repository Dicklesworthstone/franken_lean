//! The pin's expression-tree elaborator for operator notation
//! (`Lean.Elab.Extra`, namespace `Op`, vendored at
//! `vendor/lean4-src/src/Lean/Elab/Extra.lean:80-566`).
//!
//! `Init/Notation.lean:300-393` and `Init/Core.lean:880` expand arithmetic to
//! `binop%`, exponentiation to `rightact%`, prefix minus to `unop%`, and the
//! relations to `binrel%`/`binrel_no_prop%`. Those elaborators collect every
//! directly nested operator node into one tree, elaborate its leaves with no
//! expected type, compute the tree's "maximal" leaf type, and unify unknown
//! leaf types with it (or insert coercions to it) before building any
//! application. Without that step a numeral such as the `0` in `0 + i` stays
//! an unknown `?α`, and `HAdd ?α Nat ?γ` blocks until default instances run.
//!
//! What is implemented, mapped to the pin's functions:
//! - `toTree.go`: [`Context::operator_tree`] (parentheses are transparent; a
//!   `rightact%` right operand and every non-operator term is a leaf);
//! - `analyze` (with `isUnknown`, the new-depth `isDefEq` and `hasCoe`);
//! - `applyCoe` (with `hasHomogeneousInstance` and
//!   `hasHeterogeneousDefaultInstances`), `toExprCore`, `toExpr`;
//! - `elabBinRelCore` for `binrel%` and `binrel_no_prop%`, including
//!   `toBoolIfNecessary` and the `Prop`-to-`Bool` maximal type.
//!
//! What is refused with a type rather than approximated: inserting a
//! coercion at a leaf ([`SourceInferenceError::OperatorCoercion`]). The pin's
//! `mkCoe` returns the coercion after `expandCoe` has unfolded every
//! `@[coe_decl]` head; the native coercion search here returns the unexpanded
//! `CoeT.coe` application, which is a different term.
//!
//! A notation whose pin function is absent from the environment (the bounded
//! source seed has no `LT`/`LE`, and the raw Nat fixture has no classes at all)
//! does not reach this module: the pin itself would refuse it as an unknown
//! constant, and the caller keeps its pre-existing seed bridge for it.
use super::instances::{nonmatch, registry_error};
use super::*;

/// Nested `toExpr` calls happen only when a binary node has no homogeneous
/// instance at the maximal type. Each nests one Rust frame.
const MAX_OPERATOR_NESTING: usize = 256;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum OperatorKind {
    /// `binop% f a b`: both operands take part in the protocol.
    Regular,
    /// `rightact% f a b`: only `a` takes part; `b` is an ordinary leaf.
    RightAction,
}

/// The pin's notation for one surface operator kind.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum PinNotation {
    Binary(OperatorKind, &'static str),
    Unary(&'static str),
    /// `binrel% f a b`, or `binrel_no_prop% f a b` when `no_prop` holds.
    Relation {
        function: &'static str,
        no_prop: bool,
    },
}

impl PinNotation {
    pub(super) fn function(self) -> Name {
        let text = match self {
            Self::Binary(_, function) | Self::Unary(function) => function,
            Self::Relation { function, .. } => function,
        };
        Name::from_components(text.split('.'))
    }
}

/// The `macro_rules` rows of `Init/Notation.lean:303-313,383-388` and
/// `Init/Core.lean:880`, for the operator kinds this parser produces.
/// `<<<`, `>>>`, `∧`, `∨` and `↔` are plain `infix` notations in the pin
/// (ordinary applications), not expression-tree operators.
pub(super) fn pin_notation(kind: &Name) -> Option<PinNotation> {
    const ROWS: &[(&str, PinNotation)] = &[
        (
            "term_|||_",
            PinNotation::Binary(OperatorKind::Regular, "HOr.hOr"),
        ),
        (
            "term_^^^_",
            PinNotation::Binary(OperatorKind::Regular, "HXor.hXor"),
        ),
        (
            "term_&&&_",
            PinNotation::Binary(OperatorKind::Regular, "HAnd.hAnd"),
        ),
        (
            "term_+_",
            PinNotation::Binary(OperatorKind::Regular, "HAdd.hAdd"),
        ),
        (
            "term_-_",
            PinNotation::Binary(OperatorKind::Regular, "HSub.hSub"),
        ),
        (
            "term_*_",
            PinNotation::Binary(OperatorKind::Regular, "HMul.hMul"),
        ),
        (
            "term_/_",
            PinNotation::Binary(OperatorKind::Regular, "HDiv.hDiv"),
        ),
        (
            "term_%_",
            PinNotation::Binary(OperatorKind::Regular, "HMod.hMod"),
        ),
        (
            "term_^_",
            PinNotation::Binary(OperatorKind::RightAction, "HPow.hPow"),
        ),
        (
            "term_++_",
            PinNotation::Binary(OperatorKind::Regular, "HAppend.hAppend"),
        ),
        ("term-_", PinNotation::Unary("Neg.neg")),
        (
            "term_<=_",
            PinNotation::Relation {
                function: "LE.le",
                no_prop: false,
            },
        ),
        (
            "term_<_",
            PinNotation::Relation {
                function: "LT.lt",
                no_prop: false,
            },
        ),
        (
            "term_=_",
            PinNotation::Relation {
                function: "Eq",
                no_prop: false,
            },
        ),
        (
            "term_==_",
            PinNotation::Relation {
                function: "BEq.beq",
                no_prop: true,
            },
        ),
    ];
    ROWS.iter()
        .find(|(syntax_kind, _)| kind == &Name::str(Name::anonymous(), *syntax_kind))
        .map(|(_, notation)| *notation)
}

#[derive(Clone)]
enum OpNode {
    Leaf(usize),
    Binary {
        kind: OperatorKind,
        function: Name,
        lhs: usize,
        rhs: usize,
    },
    Unary {
        function: Name,
        arg: usize,
    },
}

/// One collected expression tree (`Op.Tree` without its info-tree payload).
pub(super) struct OperatorTree<'a> {
    nodes: Vec<OpNode>,
    root: usize,
    /// Leaf syntax in elaboration order (left to right).
    pub(super) leaves: Vec<&'a Syntax>,
    /// `Some(no_prop)` when the root is a `binrel%`/`binrel_no_prop%` node.
    relation: Option<bool>,
}

struct Analysis {
    max: Option<Expr>,
    uncomparable: bool,
    unknown: bool,
}

/// `Expr.cleanupAnnotations`: metadata and `optParam`/`autoParam`/
/// `outParam`/`semiOutParam` wrappers do not change a leaf's type.
fn cleanup_annotations(mut e: Expr) -> Expr {
    loop {
        if let ExprNode::MData { expr, .. } = e.node() {
            e = expr.clone();
            continue;
        }
        let (head, args) = spine(&e);
        if let ExprNode::Const { name, .. } = head.node() {
            let wrapper = |text: &str| name == &Name::from_components([text]);
            if (wrapper("optParam") || wrapper("autoParam")) && args.len() == 2 {
                e = args[0].clone();
                continue;
            }
            if (wrapper("outParam") || wrapper("semiOutParam")) && args.len() == 1 {
                e = args[0].clone();
                continue;
            }
        }
        return e;
    }
}

pub(super) fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut head = e.clone();
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f.clone();
    }
    args.reverse();
    (head, args)
}

/// `Op.isUnknown`.
fn is_unknown(e: &Expr) -> bool {
    let mut e = e.clone();
    loop {
        e = match e.node() {
            ExprNode::MVar { .. } => return true,
            ExprNode::App { f, .. } => f.clone(),
            ExprNode::LetE { body, .. } => body.clone(),
            ExprNode::MData { expr, .. } => expr.clone(),
            _ => return false,
        };
    }
}

fn head_constant(e: &Expr) -> Option<Name> {
    match spine(e).0.node() {
        ExprNode::Const { name, .. } => Some(name.clone()),
        _ => None,
    }
}

/// The pin answers these probes with `try … catch _ => false` (or
/// `isDefEqGuarded`), which does not catch runtime exhaustion. A resource stop
/// or an internal fault is therefore never turned into a `false` here.
pub(super) fn probe_says_no(error: &NatDefinitionElabError) -> bool {
    if nonmatch(error) {
        return true;
    }
    let NatDefinitionElabError::Inference(reason) = error else {
        return false;
    };
    let complete = |outcome: &Outcome<Verdict>| matches!(outcome, Outcome::Complete(_));
    match reason {
        SourceInferenceError::ResourceLimit
        | SourceInferenceError::Scope
        | SourceInferenceError::InstanceRegistry(_)
        | SourceInferenceError::ObservationComplete
        | SourceInferenceError::ConversionRefused(_) => false,
        SourceInferenceError::TypeObligation(outcome) => complete(outcome),
        SourceInferenceError::Unification(error) => match error.as_ref() {
            UnificationError::Cancelled
            | UnificationError::StepLimit { .. }
            | UnificationError::NodeLimit { .. }
            | UnificationError::AssignmentLimit { .. }
            | UnificationError::HeartbeatLimit
            | UnificationError::Reducibility(_) => false,
            UnificationError::ConversionCheck { outcome }
            | UnificationError::AssignmentCheck { outcome, .. }
            | UnificationError::ConstraintCheck { outcome, .. } => complete(outcome),
            _ => true,
        },
        _ => true,
    }
}

impl Context {
    /// Whether the pin's function for this notation resolves here, and, for a
    /// class method such as `HAdd.hAdd`, whether its class is registered.
    /// In the pin both always hold once the constant resolves; this engine can
    /// hold declarations whose class metadata was never activated, and those
    /// keep the pre-existing seed bridge rather than a half-working search.
    pub(super) fn pin_notation_available(
        &self,
        notation: PinNotation,
    ) -> Result<bool, NatDefinitionElabError> {
        let function = notation.function();
        if !self.txn.env.contains(&function) {
            return Ok(false);
        }
        let class = function.parent();
        if class.is_anonymous() {
            return Ok(true);
        }
        Ok(self.instance_registry()?.is_class(&class))
    }

    /// `toTree.go` for a root `binop%`/`unop%`/`rightact%` term, or both
    /// operand trees of a root `binrel%` term (`elabBinRelCore`).
    pub(super) fn operator_tree<'a>(
        &mut self,
        syntax: &'a Syntax,
        notation: PinNotation,
    ) -> Result<OperatorTree<'a>, NatDefinitionElabError> {
        let mut tree = OperatorTree {
            nodes: Vec::new(),
            root: 0,
            leaves: Vec::new(),
            relation: None,
        };
        tree.root = if let PinNotation::Relation { no_prop, .. } = notation {
            let kind = syntax
                .kind()
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let parts = expect_node(syntax, &kind, 3, "binary relation")?;
            let lhs = self.collect_operator_tree(&mut tree, &parts[0])?;
            let rhs = self.collect_operator_tree(&mut tree, &parts[2])?;
            tree.relation = Some(no_prop);
            tree.nodes.push(OpNode::Binary {
                kind: OperatorKind::Regular,
                function: notation.function(),
                lhs,
                rhs,
            });
            tree.nodes.len() - 1
        } else {
            self.collect_operator_tree(&mut tree, syntax)?
        };
        Ok(tree)
    }

    /// The non-relation operator nodes reachable from `syntax`, built
    /// iteratively so that long operator chains cannot exhaust the stack.
    fn collect_operator_tree<'a>(
        &mut self,
        tree: &mut OperatorTree<'a>,
        syntax: &'a Syntax,
    ) -> Result<usize, NatDefinitionElabError> {
        enum Step<'a> {
            Enter(&'a Syntax),
            Leaf(&'a Syntax),
            Binary(OperatorKind, Name),
            Unary(Name),
        }
        let mut steps = vec![Step::Enter(syntax)];
        let mut built: Vec<usize> = Vec::new();
        while let Some(step) = steps.pop() {
            self.tick()?;
            match step {
                Step::Enter(mut term) => {
                    while let Some(inner) = parenthesized_inner(term)? {
                        self.tick()?;
                        term = inner;
                    }
                    let notation = match term.kind().and_then(pin_notation) {
                        Some(notation) if self.pin_notation_available(notation)? => Some(notation),
                        _ => None,
                    };
                    let kind = term.kind().cloned();
                    match (notation, kind) {
                        (Some(PinNotation::Binary(operator, function)), Some(kind)) => {
                            let parts = expect_node(term, &kind, 3, "binary operator")?;
                            let function = Name::from_components(function.split('.'));
                            steps.push(Step::Binary(operator, function));
                            steps.push(if operator == OperatorKind::RightAction {
                                Step::Leaf(&parts[2])
                            } else {
                                Step::Enter(&parts[2])
                            });
                            steps.push(Step::Enter(&parts[0]));
                        }
                        (Some(PinNotation::Unary(function)), Some(kind)) => {
                            let parts = expect_node(term, &kind, 2, "unary operator")?;
                            expect_atom(&parts[0], "-", "negation prefix")?;
                            steps.push(Step::Unary(Name::from_components(function.split('.'))));
                            steps.push(Step::Enter(&parts[1]));
                        }
                        // `binrel%` is an elaborator, not a tree node: a nested
                        // relation is a leaf, as is every other term.
                        _ => steps.push(Step::Leaf(term)),
                    }
                }
                Step::Leaf(term) => {
                    tree.leaves.push(term);
                    tree.nodes.push(OpNode::Leaf(tree.leaves.len() - 1));
                    built.push(tree.nodes.len() - 1);
                }
                Step::Binary(kind, function) => {
                    let rhs = built
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let lhs = built
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    tree.nodes.push(OpNode::Binary {
                        kind,
                        function,
                        lhs,
                        rhs,
                    });
                    built.push(tree.nodes.len() - 1);
                }
                Step::Unary(function) => {
                    let arg = built
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    tree.nodes.push(OpNode::Unary { function, arg });
                    built.push(tree.nodes.len() - 1);
                }
            }
        }
        match built.as_slice() {
            [root] => Ok(*root),
            _ => Err(failure(SourceInferenceError::Scope)),
        }
    }

    /// Finish a collected tree once its leaves have been elaborated with no
    /// expected type (`processLeaf`), in leaf order.
    pub(super) fn finish_operator_tree(
        &mut self,
        tree: OperatorTree<'_>,
        leaves: Vec<Typed>,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if leaves.len() != tree.leaves.len() {
            return Err(failure(SourceInferenceError::Scope));
        }
        // `processLeaf` is `elabTerm s none`. An identifier or field access is
        // an application with no explicit arguments there, so its trailing
        // implicit and instance arguments are consumed (`processImplicitArg`).
        let mut prepared = Vec::with_capacity(leaves.len());
        for (syntax, leaf) in tree.leaves.iter().zip(leaves) {
            let application = matches!(syntax, Syntax::Ident { .. })
                || syntax.kind() == Some(&parser_kind(&["Term", "proj"]));
            prepared.push(if application {
                self.insert_implicits(leaf, ImplicitInsertion::ApplicationEnd)?
            } else {
                leaf
            });
        }
        let leaves = prepared;
        // The trailing `synthesizeSyntheticMVars (postpone := .yes)` of
        // `toTree`: ordinary synthesis only, never default instances.
        self.resolve_instances(false)?;
        let mut state = TreeState {
            nodes: tree.nodes,
            values: leaves.into_iter().map(Some).collect(),
            depth: 0,
        };
        match tree.relation {
            Some(no_prop) => self.relation_tree(&mut state, tree.root, no_prop, expected),
            None => self.operator_to_expr(&mut state, tree.root, expected),
        }
    }

    /// `elabBinRelCore` after both operand trees are built.
    fn relation_tree(
        &mut self,
        state: &mut TreeState,
        root: usize,
        no_prop: bool,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let OpNode::Binary {
            function, lhs, rhs, ..
        } = state.nodes[root].clone()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        // The relation itself does not use the expected type for its operands.
        let analysis = self.analyze_tree(state, root, None)?;
        let result = match analysis.max {
            Some(max) if !analysis.uncomparable => {
                let mut max = max;
                if no_prop && self.is_prop_type(&max)? {
                    max = Expr::const_(Name::from_components(["Bool"]), Vec::new());
                }
                self.apply_operator_coercions(state, root, &max, true)?;
                self.operator_core(state, root)?
            }
            _ => {
                // Default elaboration strategy plus `toBoolIfNecessary`.
                let left = self.operator_core(state, lhs)?;
                let right = self.operator_core(state, rhs)?;
                let left = self.bool_if_necessary(left, no_prop)?;
                let right = self.bool_if_necessary(right, no_prop)?;
                let left_type = self.instantiate(&left.type_)?;
                let right = self.finish_term(right, Some(&left_type))?;
                // `ensureHasType lhsType rhs` throws a type mismatch at once
                // when no coercion applies; a closed mismatch is not left for
                // the declaration's kernel check.
                let right_type = self.instantiate(&right.type_)?;
                let closed = |e: &Expr| !e.has_expr_mvar() && !e.has_level_mvar();
                if closed(&left_type)
                    && closed(&right_type)
                    && !self.defeq_guarded(&right_type, &left_type)?
                {
                    let mut budget = UnificationBudget::new(self.kernel);
                    budget.transparency = UnificationTransparency::SafeDefinitions;
                    if let Err(problem) = self.txn.unify(&right_type, &left_type, budget) {
                        return Err(failure(SourceInferenceError::Unification(Box::new(
                            problem,
                        ))));
                    }
                }
                return self.operator_application(&function, [left, right], expected);
            }
        };
        // `binrel%` returns its result without `ensureHasType`; the enclosing
        // elaboration checks it against the expected type.
        self.finish_term(result, expected)
    }

    /// `toExpr`: analyze, coerce leaves to the maximal type, build, check.
    fn operator_to_expr(
        &mut self,
        state: &mut TreeState,
        root: usize,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let analysis = self.analyze_tree(state, root, expected)?;
        let max = match analysis.max {
            Some(max) if !analysis.uncomparable => max,
            _ => {
                let result = self.operator_core(state, root)?;
                return self.finish_term(result, expected);
            }
        };
        self.apply_operator_coercions(state, root, &max, false)?;
        let result = self.operator_core(state, root)?;
        if !analysis.unknown {
            // Record the maximal type; a failure is not an error here.
            self.defeq_guarded(&result.type_, &max)?;
        }
        self.finish_term(result, expected)
    }

    /// `Op.analyze`.
    fn analyze_tree(
        &mut self,
        state: &TreeState,
        root: usize,
        expected: Option<&Expr>,
    ) -> Result<Analysis, NatDefinitionElabError> {
        let mut analysis = Analysis {
            max: None,
            uncomparable: false,
            unknown: false,
        };
        if let Some(expected) = expected {
            let expected = cleanup_annotations(self.instantiate(expected)?);
            if !is_unknown(&expected) {
                analysis.max = Some(expected);
            }
        }
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            self.tick()?;
            if analysis.uncomparable {
                break;
            }
            match &state.nodes[node] {
                OpNode::Binary {
                    kind: OperatorKind::RightAction,
                    lhs,
                    ..
                } => pending.push(*lhs),
                OpNode::Binary { lhs, rhs, .. } => {
                    pending.push(*rhs);
                    pending.push(*lhs);
                }
                OpNode::Unary { arg, .. } => pending.push(*arg),
                OpNode::Leaf(slot) => {
                    let value = state.values[*slot]
                        .as_ref()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let type_ = cleanup_annotations(self.instantiate(&value.type_)?);
                    if is_unknown(&type_) {
                        analysis.unknown = true;
                        continue;
                    }
                    let Some(max) = analysis.max.clone() else {
                        analysis.max = Some(type_);
                        continue;
                    };
                    if self.defeq_without_assignment(&max, &type_)? {
                        continue;
                    }
                    if self.has_coercion(&type_, &max)? {
                        continue;
                    }
                    if self.has_coercion(&max, &type_)? {
                        analysis.max = Some(type_);
                    } else {
                        analysis.uncomparable = true;
                    }
                }
            }
        }
        Ok(analysis)
    }

    /// `Op.applyCoe`. Leaves are rewritten in place, and a binary node with no
    /// homogeneous instance at the maximal type becomes a leaf holding its
    /// independently elaborated value, exactly as the pin's `.term` result.
    fn apply_operator_coercions(
        &mut self,
        state: &mut TreeState,
        root: usize,
        max: &Expr,
        is_pred: bool,
    ) -> Result<(), NatDefinitionElabError> {
        struct Visit {
            node: usize,
            function: Option<Name>,
            lhs: bool,
            is_pred: bool,
        }
        let mut pending = vec![Visit {
            node: root,
            function: None,
            lhs: false,
            is_pred,
        }];
        while let Some(visit) = pending.pop() {
            self.tick()?;
            match state.nodes[visit.node].clone() {
                OpNode::Binary {
                    kind: OperatorKind::RightAction,
                    lhs,
                    ..
                } => pending.push(Visit {
                    node: lhs,
                    function: None,
                    lhs: false,
                    is_pred: false,
                }),
                OpNode::Binary {
                    function, lhs, rhs, ..
                } => {
                    if visit.is_pred || self.has_homogeneous_instance(&function, max)? {
                        pending.push(Visit {
                            node: rhs,
                            function: Some(function.clone()),
                            lhs: false,
                            is_pred: false,
                        });
                        pending.push(Visit {
                            node: lhs,
                            function: Some(function),
                            lhs: true,
                            is_pred: false,
                        });
                    } else {
                        state.depth += 1;
                        if state.depth > MAX_OPERATOR_NESTING {
                            return Err(failure(SourceInferenceError::ResourceLimit));
                        }
                        let left = self.operator_to_expr(state, lhs, None)?;
                        let right = self.operator_to_expr(state, rhs, None)?;
                        state.depth -= 1;
                        let value = self.operator_application(&function, [left, right], None)?;
                        state.values.push(Some(value));
                        state.nodes[visit.node] = OpNode::Leaf(state.values.len() - 1);
                    }
                }
                OpNode::Unary { arg, .. } => pending.push(Visit {
                    node: arg,
                    function: None,
                    lhs: false,
                    is_pred: false,
                }),
                OpNode::Leaf(slot) => {
                    let value = state.values[slot]
                        .clone()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let type_ = cleanup_annotations(self.instantiate(&value.type_)?);
                    if is_unknown(&type_)
                        && let Some(function) = &visit.function
                        && self.has_heterogeneous_default_instances(function, max, visit.lhs)?
                    {
                        continue;
                    }
                    if self.defeq_guarded(max, &type_)? {
                        continue;
                    }
                    state.values[slot] = Some(self.operator_coercion(value, max)?);
                }
            }
        }
        Ok(())
    }

    /// `Op.toExprCore`: build the applications bottom-up, left to right.
    fn operator_core(
        &mut self,
        state: &mut TreeState,
        root: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut pending = vec![(root, false)];
        let mut built: Vec<Typed> = Vec::new();
        while let Some((node, ready)) = pending.pop() {
            self.tick()?;
            match (state.nodes[node].clone(), ready) {
                (OpNode::Leaf(slot), _) => built.push(
                    state.values[slot]
                        .take()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?,
                ),
                (OpNode::Binary { lhs, rhs, .. }, false) => {
                    pending.push((node, true));
                    pending.push((rhs, false));
                    pending.push((lhs, false));
                }
                (OpNode::Unary { arg, .. }, false) => {
                    pending.push((node, true));
                    pending.push((arg, false));
                }
                (OpNode::Binary { function, .. }, true) => {
                    let right = built
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let left = built
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    built.push(self.operator_application(&function, [left, right], None)?);
                }
                (OpNode::Unary { function, .. }, true) => {
                    let arg = built
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    built.push(self.operator_application(&function, [arg], None)?);
                }
            }
        }
        match <[Typed; 1]>::try_from(built) {
            Ok([value]) => Ok(value),
            Err(_) => Err(failure(SourceInferenceError::Scope)),
        }
    }

    /// `elabAppArgs f #[] args (expectedType? := …) (explicit := false)`:
    /// implicit and instance arguments become metavariables, each explicit
    /// argument is checked against its domain (with coercion), and the
    /// application's instance arguments are synthesized when possible.
    fn operator_application<const N: usize>(
        &mut self,
        function: &Name,
        arguments: [Typed; N],
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut function = self.constant(function)?;
        for argument in arguments {
            function = self.insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = function.type_.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            let domain = binder_type.clone();
            let body = body.clone();
            let argument = self.finish_term(argument, Some(&domain))?;
            self.constrain_type(&argument.type_, &domain)?;
            function.type_ = self.substitute(&body, &argument.value)?;
            function.value = Expr::app(function.value, argument.value);
        }
        self.finish_term(function, expected)
    }

    /// `isDefEqGuarded`: assignments are kept only when the check succeeds,
    /// and a failed or postponed check is `false`, never an error.
    pub(super) fn defeq_guarded(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = trial.coercion_eq(left, right);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(true) => {
                *self = trial;
                Ok(true)
            }
            Ok(false) => Ok(false),
            Err(error) if probe_says_no(&error) => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// `withNewMCtxDepth <| withConfig (isDefEqStuckEx := true) <|
    /// isDefEqGuarded`: no metavariable of the current context may be
    /// assigned, so a check that would need an assignment answers `false`.
    fn defeq_without_assignment(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        if left == right {
            return Ok(true);
        }
        let mut trial = self.clone();
        let assigned = (
            trial.txn.mvars.assignments().len(),
            trial.txn.universes.assignments().len(),
        );
        let result = trial.coercion_eq(&left, &right);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(true) => Ok(assigned
                == (
                    trial.txn.mvars.assignments().len(),
                    trial.txn.universes.assignments().len(),
                )),
            Ok(false) => Ok(false),
            Err(error) if probe_says_no(&error) => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// `Op.hasCoe`: `false` unless the environment has `CoeT`, otherwise
    /// whether a coercion from a local of type `from` to `to` resolves.
    fn has_coercion(&mut self, from: &Expr, to: &Expr) -> Result<bool, NatDefinitionElabError> {
        if !self.has_coercion_class("CoeT")? {
            return Ok(false);
        }
        let mut trial = self.clone();
        trial.equations.clear();
        let result = (|| {
            let id = FVarId(trial.fresh_name()?);
            trial.txn.lctx.add_param(
                id.clone(),
                Name::from_components(["x"]),
                from.clone(),
                BinderInfo::Default,
            );
            trial.coerce_value(
                &Typed {
                    value: Expr::fvar(id),
                    type_: from.clone(),
                },
                to,
            )
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(found) => Ok(found.is_some()),
            Err(error) if probe_says_no(&error) => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// `mkCoe maxType e` at a leaf. Without any coercion the pin reports a
    /// type mismatch; this is the ordinary typing constraint, which also
    /// postpones a check that is not yet decidable.
    fn operator_coercion(
        &mut self,
        value: Typed,
        max: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        if self.has_coercion(&value.type_, max)? {
            return Err(failure(SourceInferenceError::OperatorCoercion));
        }
        self.constrain_type(&value.type_, max)?;
        Ok(value)
    }

    /// `Op.hasHomogeneousInstance`: `Cls max max max` for `f = Cls.op`.
    fn has_homogeneous_instance(
        &mut self,
        function: &Name,
        max: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let class = function.parent();
        if class.is_anonymous() || !self.txn.env.contains(&class) {
            return Ok(false);
        }
        let mut trial = self.clone();
        // A probe, like the pin's `mkAppM` + `trySynthInstance`, neither solves
        // nor replays the caller's suspended equations.
        trial.equations.clear();
        let result = (|| {
            // `mkAppM` infers the universe instance from the arguments.
            let mut target = trial.constant(&class)?;
            for _ in 0..3 {
                let signature = trial.whnf(&target.type_)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = signature.node()
                else {
                    return Ok(None);
                };
                let Some(actual) = trial.known_type(max)? else {
                    return Ok(None);
                };
                if !trial.coercion_eq(&actual, binder_type)? {
                    return Ok(None);
                }
                target.type_ = trial.substitute(body, max)?;
                target.value = Expr::app(target.value, max.clone());
            }
            let target = trial.instantiate(&target.value)?;
            trial.coercion_instance(target)
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(found) => Ok(found.is_some()),
            Err(error) if probe_says_no(&error) => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// `Op.hasHeterogeneousDefaultInstances`.
    fn has_heterogeneous_default_instances(
        &mut self,
        function: &Name,
        max: &Expr,
        lhs: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        let max = self.instantiate(max)?;
        let Some(type_name) = head_constant(&max) else {
            return Ok(false);
        };
        let class = function.parent();
        let defaults = crate::instances::defaults::read(&self.txn.env).map_err(registry_error)?;
        let defaults: Vec<_> = defaults
            .into_iter()
            .filter(|row| row.class == class)
            .collect();
        if defaults.len() <= 1 {
            return Ok(false);
        }
        for row in defaults {
            self.tick()?;
            let Some(info) = self.txn.env.find(&row.candidate.declaration) else {
                continue;
            };
            let mut body = info.constant_val().type_.clone();
            while let ExprNode::ForallE { body: inner, .. } = body.node() {
                body = inner.clone();
            }
            let (_, args) = spine(&body);
            if let [lhs_type, rhs_type, _result] = args.as_slice() {
                let side = if lhs { rhs_type } else { lhs_type };
                if head_constant(side).as_ref() == Some(&type_name) {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// Whether `type_` is `Prop` (`isDefEq type (mkSort 0)` at a new depth).
    fn is_prop_type(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let prop = Expr::sort(Level::zero());
        self.defeq_without_assignment(type_, &prop)
    }

    /// `elabBinRelCore.toBoolIfNecessary`.
    fn bool_if_necessary(
        &mut self,
        term: Typed,
        no_prop: bool,
    ) -> Result<Typed, NatDefinitionElabError> {
        if !no_prop || !self.is_prop_type(&term.type_)? {
            return Ok(term);
        }
        let boolean = Expr::const_(Name::from_components(["Bool"]), Vec::new());
        self.finish_term(term, Some(&boolean))
    }
}

/// Mutable view of one tree while `applyCoe`/`toExprCore` consume it.
struct TreeState {
    nodes: Vec<OpNode>,
    values: Vec<Option<Typed>>,
    depth: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kind(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    #[test]
    fn the_pin_expands_each_parsed_operator_kind_to_its_notation() {
        for (syntax_kind, function) in [
            ("term_+_", "HAdd.hAdd"),
            ("term_-_", "HSub.hSub"),
            ("term_*_", "HMul.hMul"),
            ("term_/_", "HDiv.hDiv"),
            ("term_%_", "HMod.hMod"),
            ("term_++_", "HAppend.hAppend"),
            ("term_&&&_", "HAnd.hAnd"),
            ("term_|||_", "HOr.hOr"),
            ("term_^^^_", "HXor.hXor"),
        ] {
            assert_eq!(
                pin_notation(&kind(syntax_kind)),
                Some(PinNotation::Binary(OperatorKind::Regular, function))
            );
        }
        assert_eq!(
            pin_notation(&kind("term_^_")),
            Some(PinNotation::Binary(OperatorKind::RightAction, "HPow.hPow"))
        );
        assert_eq!(
            pin_notation(&kind("term-_")),
            Some(PinNotation::Unary("Neg.neg"))
        );
        assert_eq!(
            pin_notation(&kind("term_==_")),
            Some(PinNotation::Relation {
                function: "BEq.beq",
                no_prop: true
            })
        );
        for (syntax_kind, function) in [
            ("term_<_", "LT.lt"),
            ("term_<=_", "LE.le"),
            ("term_=_", "Eq"),
        ] {
            assert_eq!(
                pin_notation(&kind(syntax_kind)),
                Some(PinNotation::Relation {
                    function,
                    no_prop: false
                })
            );
        }
        // Plain `infix` notations in the pin are ordinary applications.
        for syntax_kind in ["term_<<<_", "term_>>>_", "term_∧_", "term_∨_", "term_↔_"] {
            assert_eq!(pin_notation(&kind(syntax_kind)), None, "{syntax_kind}");
        }
    }

    #[test]
    fn unknown_types_are_metavariable_headed_after_cleanup() {
        let mvar = Expr::mvar(MVarId(Name::from_components(["m"])));
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        assert!(is_unknown(&mvar));
        assert!(is_unknown(&Expr::app(mvar.clone(), nat.clone())));
        assert!(!is_unknown(&nat));
        let list = Expr::const_(Name::from_components(["List"]), Vec::new());
        assert!(!is_unknown(&Expr::app(list, mvar.clone())));
        let out = Expr::const_(Name::from_components(["outParam"]), Vec::new());
        assert_eq!(cleanup_annotations(Expr::app(out, nat.clone())), nat);
        assert!(is_unknown(&cleanup_annotations(Expr::mdata(
            KVMap::new(),
            mvar
        ))));
    }
}
