//! Immutable constant environment for the independent checker.
//!
//! This is intentionally not an adapter over `fln-env`. It preserves the
//! common declaration header needed by checker-owned typing and the optional
//! definition body needed by delta reduction while using a separate immutable
//! map, separate validation, and separate resource taxonomy. Construction is
//! failure-atomic: only a completely validated environment is published.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr, WireName, expression_owned_units,
    level_owned_units,
};

/// The three reducibility-hint shapes carried by a Lean definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u32),
}

impl ReducibilityHint {
    /// Height used by KR-309. Abbreviations are selected eagerly; opaque hints
    /// remain ordinary safe definitions with the minimum height.
    pub const fn delta_height(self) -> u32 {
        match self {
            ReducibilityHint::Opaque => 0,
            ReducibilityHint::Abbrev => u32::MAX,
            ReducibilityHint::Regular(height) => height,
        }
    }
}

/// The declaration family carried by one constant header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantKind {
    Axiom,
    Theorem,
    Opaque,
    Definition,
    Inductive,
    Constructor,
    Recursor,
    Quotient,
}

/// Unsafe quarantine is common declaration metadata, independent of whether a
/// constant has a definition body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantSafety {
    Safe,
    Unsafe,
}

/// Definition safety is schema, not an admission decision. Delta reduction may
/// unfold only `Safe` bodies belonging to a safe constant; retaining all three
/// forms prevents the environment boundary from erasing that distinction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// Optional definition-specific payload stored behind the common header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionBody {
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
    mutual: Vec<WireName>,
}

impl DefinitionBody {
    pub fn new(
        value: WireExpr,
        hint: ReducibilityHint,
        safety: DefinitionSafety,
        mutual: Vec<WireName>,
    ) -> DefinitionBody {
        DefinitionBody {
            value,
            hint,
            safety,
            mutual,
        }
    }

    pub fn value(&self) -> &WireExpr {
        &self.value
    }

    pub const fn hint(&self) -> ReducibilityHint {
        self.hint
    }

    pub const fn safety(&self) -> DefinitionSafety {
        self.safety
    }

    pub fn mutual(&self) -> &[WireName] {
        &self.mutual
    }
}

/// One constant declaration. Typing and reduction share this header; only a
/// definition may carry a body, and header-only declarations never receive a
/// fabricated value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantDeclaration {
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    kind: ConstantKind,
    safety: ConstantSafety,
    definition: Option<DefinitionBody>,
}

impl ConstantDeclaration {
    pub fn header(
        level_parameters: Vec<WireName>,
        type_: WireExpr,
        kind: ConstantKind,
        safety: ConstantSafety,
    ) -> ConstantDeclaration {
        ConstantDeclaration {
            level_parameters,
            type_,
            kind,
            safety,
            definition: None,
        }
    }

    pub fn definition(
        level_parameters: Vec<WireName>,
        type_: WireExpr,
        safety: ConstantSafety,
        definition: DefinitionBody,
    ) -> ConstantDeclaration {
        ConstantDeclaration {
            level_parameters,
            type_,
            kind: ConstantKind::Definition,
            safety,
            definition: Some(definition),
        }
    }

    pub fn level_parameters(&self) -> &[WireName] {
        &self.level_parameters
    }

    pub fn type_(&self) -> &WireExpr {
        &self.type_
    }

    pub const fn kind(&self) -> ConstantKind {
        self.kind
    }

    pub const fn safety(&self) -> ConstantSafety {
        self.safety
    }

    pub fn definition_body(&self) -> Option<&DefinitionBody> {
        self.definition.as_ref()
    }

    /// Return the body only when every schema dimension permits delta
    /// reduction. This keeps callers from forgetting the common unsafe flag.
    pub fn delta_body(&self) -> Option<&DefinitionBody> {
        if self.kind == ConstantKind::Definition
            && self.safety == ConstantSafety::Safe
            && matches!(
                self.definition.as_ref().map(DefinitionBody::safety),
                Some(DefinitionSafety::Safe)
            )
        {
            self.definition.as_ref()
        } else {
            None
        }
    }

    pub fn is_delta_unfoldable(&self) -> bool {
        self.delta_body().is_some()
    }
}

/// One input row. The name becomes the immutable map key on successful build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantEntry {
    name: WireName,
    declaration: ConstantDeclaration,
}

impl ConstantEntry {
    pub fn new(name: WireName, declaration: ConstantDeclaration) -> ConstantEntry {
        ConstantEntry { name, declaration }
    }

    pub fn name(&self) -> &WireName {
        &self.name
    }

    pub fn declaration(&self) -> &ConstantDeclaration {
        &self.declaration
    }

    fn into_parts(self) -> (WireName, ConstantDeclaration) {
        (self.name, self.declaration)
    }
}

#[derive(Clone)]
struct ConstantNode {
    name: WireName,
    declaration: Arc<ConstantDeclaration>,
    left: Option<Arc<ConstantNode>>,
    right: Option<Arc<ConstantNode>>,
    height: u32,
    len: usize,
}

fn node_height(node: &Option<Arc<ConstantNode>>) -> u32 {
    node.as_ref().map_or(0, |node| node.height)
}

fn node_len(node: &Option<Arc<ConstantNode>>) -> usize {
    node.as_ref().map_or(0, |node| node.len)
}

fn constant_node(
    name: WireName,
    declaration: Arc<ConstantDeclaration>,
    left: Option<Arc<ConstantNode>>,
    right: Option<Arc<ConstantNode>>,
) -> Arc<ConstantNode> {
    Arc::new(ConstantNode {
        name,
        declaration,
        height: node_height(&left)
            .max(node_height(&right))
            .saturating_add(1),
        len: node_len(&left)
            .saturating_add(node_len(&right))
            .saturating_add(1),
        left,
        right,
    })
}

fn rotate_constant_left(root: Arc<ConstantNode>) -> Arc<ConstantNode> {
    let Some(right) = root.right.as_ref() else {
        return root;
    };
    let new_left = constant_node(
        root.name.clone(),
        Arc::clone(&root.declaration),
        root.left.clone(),
        right.left.clone(),
    );
    constant_node(
        right.name.clone(),
        Arc::clone(&right.declaration),
        Some(new_left),
        right.right.clone(),
    )
}

fn rotate_constant_right(root: Arc<ConstantNode>) -> Arc<ConstantNode> {
    let Some(left) = root.left.as_ref() else {
        return root;
    };
    let new_right = constant_node(
        root.name.clone(),
        Arc::clone(&root.declaration),
        left.right.clone(),
        root.right.clone(),
    );
    constant_node(
        left.name.clone(),
        Arc::clone(&left.declaration),
        left.left.clone(),
        Some(new_right),
    )
}

fn balance_constant_node(root: Arc<ConstantNode>) -> Arc<ConstantNode> {
    let balance = i64::from(node_height(&root.left)) - i64::from(node_height(&root.right));
    if balance > 1 {
        let Some(left) = root.left.as_ref() else {
            return root;
        };
        let root = if node_height(&left.right) > node_height(&left.left) {
            constant_node(
                root.name.clone(),
                Arc::clone(&root.declaration),
                Some(rotate_constant_left(Arc::clone(left))),
                root.right.clone(),
            )
        } else {
            root
        };
        rotate_constant_right(root)
    } else if balance < -1 {
        let Some(right) = root.right.as_ref() else {
            return root;
        };
        let root = if node_height(&right.left) > node_height(&right.right) {
            constant_node(
                root.name.clone(),
                Arc::clone(&root.declaration),
                root.left.clone(),
                Some(rotate_constant_right(Arc::clone(right))),
            )
        } else {
            root
        };
        rotate_constant_left(root)
    } else {
        root
    }
}

fn insert_constant(
    root: &Option<Arc<ConstantNode>>,
    name: WireName,
    declaration: Arc<ConstantDeclaration>,
) -> Result<Option<Arc<ConstantNode>>, WireName> {
    let Some(current) = root else {
        return Ok(Some(constant_node(name, declaration, None, None)));
    };
    match name.cmp(&current.name) {
        std::cmp::Ordering::Less => {
            let left = insert_constant(&current.left, name, declaration)?;
            Ok(Some(balance_constant_node(constant_node(
                current.name.clone(),
                Arc::clone(&current.declaration),
                left,
                current.right.clone(),
            ))))
        }
        std::cmp::Ordering::Greater => {
            let right = insert_constant(&current.right, name, declaration)?;
            Ok(Some(balance_constant_node(constant_node(
                current.name.clone(),
                Arc::clone(&current.declaration),
                current.left.clone(),
                right,
            ))))
        }
        std::cmp::Ordering::Equal => Err(name),
    }
}

/// Canonically ordered traversal over an immutable checker environment.
pub struct ConstantIter<'a> {
    front: Vec<&'a ConstantNode>,
    back: Vec<&'a ConstantNode>,
    remaining: usize,
}

impl<'a> ConstantIter<'a> {
    fn new(root: &'a Option<Arc<ConstantNode>>) -> ConstantIter<'a> {
        let mut iter = ConstantIter {
            front: Vec::new(),
            back: Vec::new(),
            remaining: node_len(root),
        };
        iter.push_left(root.as_deref());
        iter.push_right(root.as_deref());
        iter
    }

    fn push_left(&mut self, mut node: Option<&'a ConstantNode>) {
        while let Some(current) = node {
            self.front.push(current);
            node = current.left.as_deref();
        }
    }

    fn push_right(&mut self, mut node: Option<&'a ConstantNode>) {
        while let Some(current) = node {
            self.back.push(current);
            node = current.right.as_deref();
        }
    }
}

impl<'a> Iterator for ConstantIter<'a> {
    type Item = (&'a WireName, &'a ConstantDeclaration);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let node = self.front.pop()?;
        self.push_left(node.right.as_deref());
        self.remaining -= 1;
        Some((&node.name, node.declaration.as_ref()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl DoubleEndedIterator for ConstantIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let node = self.back.pop()?;
        self.push_right(node.left.as_deref());
        self.remaining -= 1;
        Some((&node.name, node.declaration.as_ref()))
    }
}

impl ExactSizeIterator for ConstantIter<'_> {}

/// Persistent, deterministic name resolution for checker-owned constants.
///
/// Each successful extension path-copies only one balanced-tree search path;
/// prior snapshots and every untouched declaration remain shared by `Arc`.
#[derive(Clone, Default)]
pub struct ConstantEnvironment {
    constants: Option<Arc<ConstantNode>>,
}

impl fmt::Debug for ConstantEnvironment {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.constants()).finish()
    }
}

impl PartialEq for ConstantEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.constants().eq(other.constants())
    }
}

impl Eq for ConstantEnvironment {}

impl ConstantEnvironment {
    pub fn empty() -> ConstantEnvironment {
        ConstantEnvironment::default()
    }

    pub fn len(&self) -> usize {
        node_len(&self.constants)
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_none()
    }

    pub fn find(&self, name: &WireName) -> Option<&ConstantDeclaration> {
        let mut current = self.constants.as_deref();
        while let Some(node) = current {
            match name.cmp(&node.name) {
                std::cmp::Ordering::Less => current = node.left.as_deref(),
                std::cmp::Ordering::Greater => current = node.right.as_deref(),
                std::cmp::Ordering::Equal => return Some(node.declaration.as_ref()),
            }
        }
        None
    }

    pub fn constants(&self) -> ConstantIter<'_> {
        ConstantIter::new(&self.constants)
    }

    pub fn build(entries: Vec<ConstantEntry>, budget: EnvironmentBudget) -> EnvironmentOutcome {
        Self::build_with(entries, budget, || false)
    }

    pub fn build_with(
        entries: Vec<ConstantEntry>,
        budget: EnvironmentBudget,
        mut cancelled: impl FnMut() -> bool,
    ) -> EnvironmentOutcome {
        build_environment(entries, budget, &mut cancelled)
    }

    /// Validate and retain one new constant without rebuilding the base map.
    ///
    /// Progress and limits cover the candidate only. The immutable base has
    /// already passed this constructor's validation and is structurally shared
    /// on success; refusal, cancellation, exhaustion, and faults leave it intact.
    pub fn extend(&self, entry: ConstantEntry, budget: EnvironmentBudget) -> EnvironmentOutcome {
        self.extend_with(entry, budget, || false)
    }

    pub fn extend_with(
        &self,
        entry: ConstantEntry,
        budget: EnvironmentBudget,
        mut cancelled: impl FnMut() -> bool,
    ) -> EnvironmentOutcome {
        extend_environment(self, entry, budget, &mut cancelled)
    }
}

/// Aggregate limits for one environment build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvironmentBudget {
    pub max_steps: u64,
    pub max_constants: u64,
    pub max_level_parameters: u64,
    pub max_mutual_members: u64,
    pub max_arena_nodes: u64,
    pub max_owned_units: u64,
}

impl EnvironmentBudget {
    pub const fn new(
        max_steps: u64,
        max_constants: u64,
        max_level_parameters: u64,
        max_mutual_members: u64,
        max_arena_nodes: u64,
        max_owned_units: u64,
    ) -> EnvironmentBudget {
        EnvironmentBudget {
            max_steps,
            max_constants,
            max_level_parameters,
            max_mutual_members,
            max_arena_nodes,
            max_owned_units,
        }
    }

    pub const fn unlimited() -> EnvironmentBudget {
        EnvironmentBudget::new(u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX)
    }
}

/// Exact completed work. Stops report this without promoting a partial map.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EnvironmentProgress {
    pub steps: u64,
    pub constants: u64,
    pub level_parameters: u64,
    pub mutual_members: u64,
    pub arena_nodes: u64,
    pub owned_units: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentLimit {
    Steps,
    Constants,
    LevelParameters,
    MutualMembers,
    ArenaNodes,
    OwnedUnits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentField {
    Name,
    LevelParameter,
    MutualMember,
    TypeLevel,
    TypeExpression,
    ValueLevel,
    ValueExpression,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvironmentPosition {
    pub constant: usize,
    pub field: EnvironmentField,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentStop {
    Resource {
        limit: EnvironmentLimit,
        allowed: u64,
        observed: u64,
        at: EnvironmentPosition,
        progress: EnvironmentProgress,
    },
    Cancelled {
        at: EnvironmentPosition,
        polls: u64,
        progress: EnvironmentProgress,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentRefusal {
    DuplicateConstant {
        name: WireName,
    },
    DuplicateLevelParameter {
        constant: usize,
        first: usize,
        second: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentTerm {
    Type,
    Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentFault {
    MissingExpression {
        constant: usize,
        term: EnvironmentTerm,
        index: usize,
    },
    NonBackwardExpressionReference {
        constant: usize,
        term: EnvironmentTerm,
        parent: usize,
        child: usize,
    },
    MissingLevel {
        constant: usize,
        term: EnvironmentTerm,
        index: usize,
    },
    NonBackwardLevelReference {
        constant: usize,
        term: EnvironmentTerm,
        parent: usize,
        child: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentOutcome {
    Complete {
        environment: ConstantEnvironment,
        progress: EnvironmentProgress,
    },
    Refused {
        refusal: EnvironmentRefusal,
        progress: EnvironmentProgress,
    },
    Inconclusive(EnvironmentStop),
    InternalFault {
        fault: EnvironmentFault,
        progress: EnvironmentProgress,
    },
}

enum Halt {
    Stop(EnvironmentStop),
    Fault(EnvironmentFault),
}

struct Control<'a> {
    budget: EnvironmentBudget,
    progress: EnvironmentProgress,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl<'a> Control<'a> {
    fn new(budget: EnvironmentBudget, cancelled: &'a mut dyn FnMut() -> bool) -> Control<'a> {
        Control {
            budget,
            progress: EnvironmentProgress::default(),
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(EnvironmentStop::Cancelled {
                at,
                polls: self.polls,
                progress: self.progress,
            });
        }
        Ok(())
    }

    fn admit(
        &mut self,
        limit: EnvironmentLimit,
        allowed: u64,
        completed: u64,
        at: EnvironmentPosition,
    ) -> Result<u64, EnvironmentStop> {
        let observed = completed.saturating_add(1);
        if observed > allowed {
            return Err(EnvironmentStop::Resource {
                limit,
                allowed,
                observed,
                at,
                progress: self.progress,
            });
        }
        Ok(observed)
    }

    fn step(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.poll(at)?;
        self.progress.steps = self.admit(
            EnvironmentLimit::Steps,
            self.budget.max_steps,
            self.progress.steps,
            at,
        )?;
        Ok(())
    }

    fn constant(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.constants = self.admit(
            EnvironmentLimit::Constants,
            self.budget.max_constants,
            self.progress.constants,
            at,
        )?;
        Ok(())
    }

    fn level_parameter(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.level_parameters = self.admit(
            EnvironmentLimit::LevelParameters,
            self.budget.max_level_parameters,
            self.progress.level_parameters,
            at,
        )?;
        Ok(())
    }

    fn mutual_member(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.mutual_members = self.admit(
            EnvironmentLimit::MutualMembers,
            self.budget.max_mutual_members,
            self.progress.mutual_members,
            at,
        )?;
        Ok(())
    }

    fn arena_node(&mut self, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        self.progress.arena_nodes = self.admit(
            EnvironmentLimit::ArenaNodes,
            self.budget.max_arena_nodes,
            self.progress.arena_nodes,
            at,
        )?;
        Ok(())
    }

    fn owned_units(&mut self, units: u64, at: EnvironmentPosition) -> Result<(), EnvironmentStop> {
        let observed = self.progress.owned_units.saturating_add(units);
        if observed > self.budget.max_owned_units {
            return Err(EnvironmentStop::Resource {
                limit: EnvironmentLimit::OwnedUnits,
                allowed: self.budget.max_owned_units,
                observed,
                at,
                progress: self.progress,
            });
        }
        self.progress.owned_units = observed;
        Ok(())
    }
}

fn name_owned_units(name: &WireName) -> u64 {
    name.parts().iter().fold(0u64, |units, part| {
        let payload = match part {
            NamePart::Numeric { .. } => 0,
            NamePart::Text(text) => u64::try_from(text.len()).unwrap_or(u64::MAX),
        };
        units.saturating_add(1).saturating_add(payload)
    })
}

fn expression_children(node: &ExprNode) -> impl Iterator<Item = ExprId> {
    let children = match node {
        ExprNode::Apply { function, argument } => [Some(*function), Some(*argument), None],
        ExprNode::Lambda {
            binder_type, body, ..
        }
        | ExprNode::Forall {
            binder_type, body, ..
        } => [Some(*binder_type), Some(*body), None],
        ExprNode::Let {
            type_, value, body, ..
        } => [Some(*type_), Some(*value), Some(*body)],
        ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
            [Some(*expression), None, None]
        }
        ExprNode::Bound { .. }
        | ExprNode::Free { .. }
        | ExprNode::Meta { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Constant { .. }
        | ExprNode::NatLiteral { .. }
        | ExprNode::StringLiteral(_) => [None, None, None],
    };
    children.into_iter().flatten()
}

fn level_children(node: &LevelNode) -> impl Iterator<Item = LevelId> {
    let children = match node {
        LevelNode::Succ(child) => [Some(*child), None],
        LevelNode::Max(left, right) | LevelNode::IMax(left, right) => [Some(*left), Some(*right)],
        LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => [None, None],
    };
    children.into_iter().flatten()
}

fn field(term: EnvironmentTerm, levels: bool) -> EnvironmentField {
    match (term, levels) {
        (EnvironmentTerm::Type, true) => EnvironmentField::TypeLevel,
        (EnvironmentTerm::Type, false) => EnvironmentField::TypeExpression,
        (EnvironmentTerm::Value, true) => EnvironmentField::ValueLevel,
        (EnvironmentTerm::Value, false) => EnvironmentField::ValueExpression,
    }
}

fn missing_level(constant: usize, term: EnvironmentTerm, index: usize) -> Halt {
    Halt::Fault(EnvironmentFault::MissingLevel {
        constant,
        term,
        index,
    })
}

fn validate_level_child(
    levels: &[LevelNode],
    constant: usize,
    term: EnvironmentTerm,
    parent: usize,
    child: LevelId,
) -> Result<(), Halt> {
    if child.index() >= parent {
        return Err(Halt::Fault(EnvironmentFault::NonBackwardLevelReference {
            constant,
            term,
            parent,
            child: child.index(),
        }));
    }
    if levels.get(child.index()).is_none() {
        return Err(missing_level(constant, term, child.index()));
    }
    Ok(())
}

fn validate_expression_child(
    nodes: &[ExprNode],
    constant: usize,
    term: EnvironmentTerm,
    parent: usize,
    child: ExprId,
) -> Result<(), Halt> {
    if child.index() >= parent {
        return Err(Halt::Fault(
            EnvironmentFault::NonBackwardExpressionReference {
                constant,
                term,
                parent,
                child: child.index(),
            },
        ));
    }
    if nodes.get(child.index()).is_none() {
        return Err(Halt::Fault(EnvironmentFault::MissingExpression {
            constant,
            term,
            index: child.index(),
        }));
    }
    Ok(())
}

fn validate_term(
    control: &mut Control<'_>,
    constant: usize,
    term_kind: EnvironmentTerm,
    term: &WireExpr,
) -> Result<(), Halt> {
    if term.node(term.root()).is_none() {
        return Err(Halt::Fault(EnvironmentFault::MissingExpression {
            constant,
            term: term_kind,
            index: term.root().index(),
        }));
    }

    for (index, node) in term.levels().iter().enumerate() {
        let at = EnvironmentPosition {
            constant,
            field: field(term_kind, true),
            index,
        };
        control.step(at).map_err(Halt::Stop)?;
        control.arena_node(at).map_err(Halt::Stop)?;
        control
            .owned_units(level_owned_units(node), at)
            .map_err(Halt::Stop)?;
        for child in level_children(node) {
            validate_level_child(term.levels(), constant, term_kind, index, child)?;
        }
    }

    for (index, node) in term.nodes().iter().enumerate() {
        let at = EnvironmentPosition {
            constant,
            field: field(term_kind, false),
            index,
        };
        control.step(at).map_err(Halt::Stop)?;
        control.arena_node(at).map_err(Halt::Stop)?;
        control
            .owned_units(expression_owned_units(node), at)
            .map_err(Halt::Stop)?;
        for child in expression_children(node) {
            validate_expression_child(term.nodes(), constant, term_kind, index, child)?;
        }
        match node {
            ExprNode::Sort { level } => {
                if term.level(*level).is_none() {
                    return Err(missing_level(constant, term_kind, level.index()));
                }
            }
            ExprNode::Constant { levels, .. } => {
                for level in levels {
                    if term.level(*level).is_none() {
                        return Err(missing_level(constant, term_kind, level.index()));
                    }
                }
            }
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Apply { .. }
            | ExprNode::Lambda { .. }
            | ExprNode::Forall { .. }
            | ExprNode::Let { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_)
            | ExprNode::Metadata { .. }
            | ExprNode::Projection { .. } => {}
        }
    }
    Ok(())
}

enum ValidationFailure {
    Refusal(EnvironmentRefusal),
    Halt(Halt),
}

fn validate_constant(
    control: &mut Control<'_>,
    constant_index: usize,
    declaration: &ConstantDeclaration,
) -> Result<(), ValidationFailure> {
    let mut parameters = BTreeMap::new();
    for (parameter_index, parameter) in declaration.level_parameters.iter().enumerate() {
        let at = EnvironmentPosition {
            constant: constant_index,
            field: EnvironmentField::LevelParameter,
            index: parameter_index,
        };
        control
            .step(at)
            .map_err(|stop| ValidationFailure::Halt(Halt::Stop(stop)))?;
        control
            .level_parameter(at)
            .map_err(|stop| ValidationFailure::Halt(Halt::Stop(stop)))?;
        control
            .owned_units(name_owned_units(parameter), at)
            .map_err(|stop| ValidationFailure::Halt(Halt::Stop(stop)))?;
        if let Some(first) = parameters.insert(parameter, parameter_index) {
            return Err(ValidationFailure::Refusal(
                EnvironmentRefusal::DuplicateLevelParameter {
                    constant: constant_index,
                    first,
                    second: parameter_index,
                },
            ));
        }
    }

    validate_term(
        control,
        constant_index,
        EnvironmentTerm::Type,
        &declaration.type_,
    )
    .map_err(ValidationFailure::Halt)?;

    if let Some(definition) = declaration.definition.as_ref() {
        for (member_index, member) in definition.mutual.iter().enumerate() {
            let at = EnvironmentPosition {
                constant: constant_index,
                field: EnvironmentField::MutualMember,
                index: member_index,
            };
            control
                .step(at)
                .map_err(|stop| ValidationFailure::Halt(Halt::Stop(stop)))?;
            control
                .mutual_member(at)
                .map_err(|stop| ValidationFailure::Halt(Halt::Stop(stop)))?;
            control
                .owned_units(name_owned_units(member), at)
                .map_err(|stop| ValidationFailure::Halt(Halt::Stop(stop)))?;
        }

        validate_term(
            control,
            constant_index,
            EnvironmentTerm::Value,
            &definition.value,
        )
        .map_err(ValidationFailure::Halt)?;
    }
    Ok(())
}

fn validation_outcome(
    failure: ValidationFailure,
    progress: EnvironmentProgress,
) -> EnvironmentOutcome {
    match failure {
        ValidationFailure::Refusal(refusal) => EnvironmentOutcome::Refused { refusal, progress },
        ValidationFailure::Halt(Halt::Stop(stop)) => EnvironmentOutcome::Inconclusive(stop),
        ValidationFailure::Halt(Halt::Fault(fault)) => {
            EnvironmentOutcome::InternalFault { fault, progress }
        }
    }
}

fn extend_environment(
    environment: &ConstantEnvironment,
    entry: ConstantEntry,
    budget: EnvironmentBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> EnvironmentOutcome {
    let mut control = Control::new(budget, cancelled);
    let at = EnvironmentPosition {
        constant: 0,
        field: EnvironmentField::Name,
        index: 0,
    };
    if let Err(stop) = control.step(at) {
        return EnvironmentOutcome::Inconclusive(stop);
    }
    if let Err(stop) = control.constant(at) {
        return EnvironmentOutcome::Inconclusive(stop);
    }
    let (name, declaration) = entry.into_parts();
    if let Err(stop) = control.owned_units(name_owned_units(&name), at) {
        return EnvironmentOutcome::Inconclusive(stop);
    }
    if environment.find(&name).is_some() {
        return EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateConstant { name },
            progress: control.progress,
        };
    }
    if let Err(failure) = validate_constant(&mut control, 0, &declaration) {
        return validation_outcome(failure, control.progress);
    }
    let constants = match insert_constant(&environment.constants, name, Arc::new(declaration)) {
        Ok(constants) => constants,
        Err(name) => {
            return EnvironmentOutcome::Refused {
                refusal: EnvironmentRefusal::DuplicateConstant { name },
                progress: control.progress,
            };
        }
    };
    EnvironmentOutcome::Complete {
        environment: ConstantEnvironment { constants },
        progress: control.progress,
    }
}

fn build_environment(
    entries: Vec<ConstantEntry>,
    budget: EnvironmentBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> EnvironmentOutcome {
    let mut control = Control::new(budget, cancelled);
    let mut constants = BTreeMap::new();
    let mut duplicates = BTreeSet::new();

    for (input, entry) in entries.into_iter().enumerate() {
        let at = EnvironmentPosition {
            constant: input,
            field: EnvironmentField::Name,
            index: 0,
        };
        if let Err(stop) = control.step(at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        if let Err(stop) = control.constant(at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        let (name, declaration) = entry.into_parts();
        if let Err(stop) = control.owned_units(name_owned_units(&name), at) {
            return EnvironmentOutcome::Inconclusive(stop);
        }
        match constants.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(declaration);
            }
            Entry::Occupied(entry) => {
                duplicates.insert(entry.key().clone());
            }
        }
    }

    if let Some(name) = duplicates.into_iter().next() {
        return EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateConstant { name },
            progress: control.progress,
        };
    }

    for (constant_index, declaration) in constants.values().enumerate() {
        if let Err(failure) = validate_constant(&mut control, constant_index, declaration) {
            return validation_outcome(failure, control.progress);
        }
    }

    let mut persistent = None;
    for (name, declaration) in constants {
        persistent = match insert_constant(&persistent, name, Arc::new(declaration)) {
            Ok(constants) => constants,
            Err(name) => {
                return EnvironmentOutcome::Refused {
                    refusal: EnvironmentRefusal::DuplicateConstant { name },
                    progress: control.progress,
                };
            }
        };
    }

    EnvironmentOutcome::Complete {
        environment: ConstantEnvironment {
            constants: persistent,
        },
        progress: control.progress,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf() -> WireExpr {
        let root = ExprId::from_index(0).expect("zero is a valid expression index");
        WireExpr::from_parts(
            vec![ExprNode::NatLiteral { limbs_le: vec![0] }],
            Vec::new(),
            root,
        )
    }

    fn entry(value: WireExpr) -> ConstantEntry {
        ConstantEntry::new(
            WireName::default(),
            ConstantDeclaration::definition(
                Vec::new(),
                leaf(),
                ConstantSafety::Safe,
                DefinitionBody::new(
                    value,
                    ReducibilityHint::Regular(0),
                    DefinitionSafety::Safe,
                    Vec::new(),
                ),
            ),
        )
    }

    fn named_entry(name: &str) -> ConstantEntry {
        let name = WireName::from_parts(vec![NamePart::Text(name.to_owned())]);
        ConstantEntry::new(
            name,
            ConstantDeclaration::header(
                Vec::new(),
                leaf(),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
        )
    }

    fn declaration_arc(
        environment: &ConstantEnvironment,
        name: &WireName,
    ) -> Option<Arc<ConstantDeclaration>> {
        let mut current = environment.constants.as_deref();
        while let Some(node) = current {
            match name.cmp(&node.name) {
                std::cmp::Ordering::Less => current = node.left.as_deref(),
                std::cmp::Ordering::Greater => current = node.right.as_deref(),
                std::cmp::Ordering::Equal => return Some(Arc::clone(&node.declaration)),
            }
        }
        None
    }

    fn assert_balanced(node: &Option<Arc<ConstantNode>>) -> (u32, usize) {
        let Some(node) = node else {
            return (0, 0);
        };
        let (left_height, left_len) = assert_balanced(&node.left);
        let (right_height, right_len) = assert_balanced(&node.right);
        assert!(left_height.abs_diff(right_height) <= 1);
        let height = left_height.max(right_height).saturating_add(1);
        let len = left_len.saturating_add(right_len).saturating_add(1);
        assert_eq!(node.height, height);
        assert_eq!(node.len, len);
        (height, len)
    }

    #[test]
    fn reverse_order_extensions_remain_balanced_and_canonically_iterable() {
        let mut environment = ConstantEnvironment::empty();
        for index in (0..127).rev() {
            let outcome = environment.extend(
                named_entry(&format!("constant_{index:03}")),
                EnvironmentBudget::unlimited(),
            );
            assert!(
                matches!(&outcome, EnvironmentOutcome::Complete { .. }),
                "each unique valid extension must complete"
            );
            let EnvironmentOutcome::Complete {
                environment: successor,
                ..
            } = outcome
            else {
                return;
            };
            environment = successor;
        }

        assert_eq!(assert_balanced(&environment.constants), (7, 127));
        let names = environment
            .constants()
            .map(|(name, _)| name.parts().last().cloned())
            .collect::<Vec<_>>();
        let mut sorted = names.clone();
        sorted.sort();
        assert_eq!(names, sorted);
        assert_eq!(environment.constants().rev().count(), 127);
    }

    #[test]
    fn extension_structurally_shares_every_retained_declaration() {
        let outcome = ConstantEnvironment::build(
            vec![
                named_entry("alpha"),
                named_entry("middle"),
                named_entry("zeta"),
            ],
            EnvironmentBudget::unlimited(),
        );
        assert!(
            matches!(&outcome, EnvironmentOutcome::Complete { .. }),
            "the valid base fixture must build"
        );
        let EnvironmentOutcome::Complete {
            environment: base, ..
        } = outcome
        else {
            return;
        };
        let retained = ["alpha", "middle", "zeta"].map(|name| {
            let name = WireName::from_parts(vec![NamePart::Text(name.to_owned())]);
            (name.clone(), declaration_arc(&base, &name))
        });
        let outcome = base.extend(named_entry("omega"), EnvironmentBudget::unlimited());
        assert!(
            matches!(&outcome, EnvironmentOutcome::Complete { .. }),
            "the valid extension fixture must build"
        );
        let EnvironmentOutcome::Complete {
            environment: extended,
            ..
        } = outcome
        else {
            return;
        };

        for (name, before) in retained {
            assert!(before.is_some(), "the base must retain every fixture row");
            let Some(before) = before else {
                return;
            };
            let after = declaration_arc(&extended, &name);
            assert!(after.is_some(), "the extension must retain every base row");
            let Some(after) = after else {
                return;
            };
            assert!(Arc::ptr_eq(&before, &after));
        }
        assert_eq!(base.len(), 3);
        assert_eq!(extended.len(), 4);
    }

    #[test]
    fn private_type_and_value_corruption_are_distinct_faults_and_recovery_is_exact() {
        let root = ExprId::from_index(0).expect("zero is a valid expression index");
        let broken = WireExpr::from_parts(
            vec![ExprNode::Apply {
                function: root,
                argument: root,
            }],
            Vec::new(),
            root,
        );
        let broken_type = ConstantEntry::new(
            WireName::default(),
            ConstantDeclaration::header(
                Vec::new(),
                broken.clone(),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
        );
        assert!(matches!(
            ConstantEnvironment::build(vec![broken_type], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::InternalFault {
                fault: EnvironmentFault::NonBackwardExpressionReference {
                    constant: 0,
                    term: EnvironmentTerm::Type,
                    parent: 0,
                    child: 0,
                },
                ..
            }
        ));
        assert!(matches!(
            ConstantEnvironment::build(vec![entry(broken)], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::InternalFault {
                fault: EnvironmentFault::NonBackwardExpressionReference {
                    constant: 0,
                    term: EnvironmentTerm::Value,
                    parent: 0,
                    child: 0,
                },
                ..
            }
        ));
        assert!(matches!(
            ConstantEnvironment::build(vec![entry(leaf())], EnvironmentBudget::unlimited()),
            EnvironmentOutcome::Complete { .. }
        ));
    }
}
