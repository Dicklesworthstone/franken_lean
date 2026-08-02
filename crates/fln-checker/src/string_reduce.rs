//! Checker-owned KR-314 String-literal expansion.
//!
//! The pinned kernel expands a String literal into
//! `String.ofList (List.cons.{0} Char (Char.ofNat c) ... (List.nil.{0} Char))`.
//! This implementation derives that term independently over the checker's flat
//! wire arena. Unicode scalar values, not UTF-8 bytes, are the list elements.
//! Traversal and construction are iterative, bounded, cancellation-aware, and
//! failure-atomic: no partially built arena is ever returned.

use crate::wire::{
    ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr, WireName, expression_owned_units,
    level_owned_units,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StringExpansionBudget {
    pub max_steps: u64,
    pub max_code_points: u64,
    pub max_arena_nodes: u64,
    pub max_owned_units: u64,
}

impl StringExpansionBudget {
    pub const fn new(
        max_steps: u64,
        max_code_points: u64,
        max_arena_nodes: u64,
        max_owned_units: u64,
    ) -> StringExpansionBudget {
        StringExpansionBudget {
            max_steps,
            max_code_points,
            max_arena_nodes,
            max_owned_units,
        }
    }

    pub const fn unlimited() -> StringExpansionBudget {
        StringExpansionBudget::new(u64::MAX, u64::MAX, u64::MAX, u64::MAX)
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StringExpansionProgress {
    pub steps: u64,
    pub code_points: u64,
    pub generated_arenas: u64,
    pub arena_nodes: u64,
    pub owned_units: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringExpansionLimit {
    Steps,
    CodePoints,
    ArenaNodes,
    OwnedUnits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringExpansionStop {
    Resource {
        limit: StringExpansionLimit,
        allowed: u64,
        observed: u64,
        at_byte: usize,
        progress: StringExpansionProgress,
    },
    Cancelled {
        at_byte: usize,
        polls: u64,
        progress: StringExpansionProgress,
    },
}

impl StringExpansionStop {
    pub const fn progress(self) -> StringExpansionProgress {
        match self {
            StringExpansionStop::Resource { progress, .. }
            | StringExpansionStop::Cancelled { progress, .. } => progress,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringExpansionAllocation {
    ExpressionArena,
    LevelArena,
    NaturalLimb,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringExpansionFault {
    SizeOverflow,
    ArenaIndexOverflow {
        nodes: usize,
    },
    Allocation {
        region: StringExpansionAllocation,
        requested: usize,
    },
    Accounting {
        expected_nodes: u64,
        actual_nodes: u64,
        expected_owned_units: u64,
        actual_owned_units: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringExpansionResult {
    pub term: WireExpr,
    pub progress: StringExpansionProgress,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringExpansionOutcome {
    Expanded(StringExpansionResult),
    Inconclusive(StringExpansionStop),
    InternalFault {
        fault: StringExpansionFault,
        progress: StringExpansionProgress,
    },
}

enum Halt {
    Stop(StringExpansionStop),
    Fault {
        fault: StringExpansionFault,
        progress: StringExpansionProgress,
    },
}

struct Control {
    budget: StringExpansionBudget,
    progress: StringExpansionProgress,
    polls: u64,
}

impl Control {
    const fn new(budget: StringExpansionBudget) -> Control {
        Control {
            budget,
            progress: StringExpansionProgress {
                steps: 0,
                code_points: 0,
                generated_arenas: 0,
                arena_nodes: 0,
                owned_units: 0,
            },
            polls: 0,
        }
    }

    const fn fault(&self, fault: StringExpansionFault) -> Halt {
        Halt::Fault {
            fault,
            progress: self.progress,
        }
    }

    fn poll(&mut self, at_byte: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(Halt::Stop(StringExpansionStop::Cancelled {
                at_byte,
                polls: self.polls,
                progress: self.progress,
            }));
        }
        Ok(())
    }

    fn step(&mut self, at_byte: usize, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.poll(at_byte, cancelled)?;
        let observed = self.progress.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                at_byte,
                progress: self.progress,
            }));
        }
        self.progress.steps = observed;
        Ok(())
    }

    fn code_point(
        &mut self,
        at_byte: usize,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<(), Halt> {
        self.step(at_byte, cancelled)?;
        let observed = self.progress.code_points.saturating_add(1);
        if observed > self.budget.max_code_points {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::CodePoints,
                allowed: self.budget.max_code_points,
                observed,
                at_byte,
                progress: self.progress,
            }));
        }
        self.progress.code_points = observed;
        Ok(())
    }

    fn preflight(
        &self,
        emitted_steps: u64,
        arena_nodes: u64,
        owned_units: u64,
        at_byte: usize,
    ) -> Result<(), Halt> {
        let observed_steps = self
            .progress
            .steps
            .checked_add(emitted_steps)
            .ok_or_else(|| self.fault(StringExpansionFault::SizeOverflow))?;
        if observed_steps > self.budget.max_steps {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::Steps,
                allowed: self.budget.max_steps,
                observed: observed_steps,
                at_byte,
                progress: self.progress,
            }));
        }
        if arena_nodes > self.budget.max_arena_nodes {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::ArenaNodes,
                allowed: self.budget.max_arena_nodes,
                observed: arena_nodes,
                at_byte,
                progress: self.progress,
            }));
        }
        if owned_units > self.budget.max_owned_units {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::OwnedUnits,
                allowed: self.budget.max_owned_units,
                observed: owned_units,
                at_byte,
                progress: self.progress,
            }));
        }
        Ok(())
    }

    fn emit_level(
        &mut self,
        node: LevelNode,
        at_byte: usize,
        levels: &mut Vec<LevelNode>,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<LevelId, Halt> {
        self.step(at_byte, cancelled)?;
        let observed_nodes = self.progress.arena_nodes.saturating_add(1);
        if observed_nodes > self.budget.max_arena_nodes {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::ArenaNodes,
                allowed: self.budget.max_arena_nodes,
                observed: observed_nodes,
                at_byte,
                progress: self.progress,
            }));
        }
        let units = level_owned_units(&node);
        let observed_units = self.progress.owned_units.saturating_add(units);
        if observed_units > self.budget.max_owned_units {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::OwnedUnits,
                allowed: self.budget.max_owned_units,
                observed: observed_units,
                at_byte,
                progress: self.progress,
            }));
        }
        let id = LevelId::from_index(levels.len()).ok_or_else(|| {
            self.fault(StringExpansionFault::ArenaIndexOverflow {
                nodes: levels.len(),
            })
        })?;
        levels.push(node);
        self.progress.arena_nodes = observed_nodes;
        self.progress.owned_units = observed_units;
        Ok(id)
    }

    fn emit_expression(
        &mut self,
        node: ExprNode,
        at_byte: usize,
        nodes: &mut Vec<ExprNode>,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<ExprId, Halt> {
        self.step(at_byte, cancelled)?;
        let observed_nodes = self.progress.arena_nodes.saturating_add(1);
        if observed_nodes > self.budget.max_arena_nodes {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::ArenaNodes,
                allowed: self.budget.max_arena_nodes,
                observed: observed_nodes,
                at_byte,
                progress: self.progress,
            }));
        }
        let units = expression_owned_units(&node);
        let observed_units = self.progress.owned_units.saturating_add(units);
        if observed_units > self.budget.max_owned_units {
            return Err(Halt::Stop(StringExpansionStop::Resource {
                limit: StringExpansionLimit::OwnedUnits,
                allowed: self.budget.max_owned_units,
                observed: observed_units,
                at_byte,
                progress: self.progress,
            }));
        }
        let id = ExprId::from_index(nodes.len()).ok_or_else(|| {
            self.fault(StringExpansionFault::ArenaIndexOverflow { nodes: nodes.len() })
        })?;
        nodes.push(node);
        self.progress.arena_nodes = observed_nodes;
        self.progress.owned_units = observed_units;
        Ok(id)
    }
}

fn top_level_name(name: &str) -> WireName {
    WireName::from_parts(vec![NamePart::Text(name.to_owned())])
}

fn two_part_name(namespace: &str, leaf: &str) -> WireName {
    WireName::from_parts(vec![
        NamePart::Text(namespace.to_owned()),
        NamePart::Text(leaf.to_owned()),
    ])
}

fn natural_limbs(value: u64, progress: StringExpansionProgress) -> Result<Vec<u64>, Halt> {
    if value == 0 {
        return Ok(Vec::new());
    }
    let mut limbs = Vec::new();
    limbs.try_reserve_exact(1).map_err(|_| Halt::Fault {
        fault: StringExpansionFault::Allocation {
            region: StringExpansionAllocation::NaturalLimb,
            requested: 1,
        },
        progress,
    })?;
    limbs.push(value);
    Ok(limbs)
}

fn checked_size(
    code_points: u64,
    nonzero_code_points: u64,
    progress: StringExpansionProgress,
) -> Result<(u64, u64), Halt> {
    let nodes = code_points
        .checked_mul(4)
        .and_then(|value| value.checked_add(9))
        .ok_or(Halt::Fault {
            fault: StringExpansionFault::SizeOverflow,
            progress,
        })?;
    let owned_units = code_points
        .checked_mul(4)
        .and_then(|value| value.checked_add(nonzero_code_points))
        .and_then(|value| value.checked_add(60))
        .ok_or(Halt::Fault {
            fault: StringExpansionFault::SizeOverflow,
            progress,
        })?;
    Ok((nodes, owned_units))
}

fn expand(
    value: &str,
    budget: StringExpansionBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<StringExpansionResult, Halt> {
    let mut control = Control::new(budget);
    let mut nonzero_code_points = 0_u64;
    for (at_byte, character) in value.char_indices() {
        control.code_point(at_byte, cancelled)?;
        if character != '\0' {
            nonzero_code_points = nonzero_code_points.saturating_add(1);
        }
    }

    let (expected_nodes, expected_owned_units) = checked_size(
        control.progress.code_points,
        nonzero_code_points,
        control.progress,
    )?;
    let emitted_steps = expected_nodes;
    control.preflight(
        emitted_steps,
        expected_nodes,
        expected_owned_units,
        value.len(),
    )?;

    let expression_nodes = expected_nodes
        .checked_sub(1)
        .and_then(|nodes| usize::try_from(nodes).ok())
        .ok_or_else(|| control.fault(StringExpansionFault::SizeOverflow))?;
    let mut nodes = Vec::new();
    nodes.try_reserve_exact(expression_nodes).map_err(|_| {
        control.fault(StringExpansionFault::Allocation {
            region: StringExpansionAllocation::ExpressionArena,
            requested: expression_nodes,
        })
    })?;
    let mut levels = Vec::new();
    levels.try_reserve_exact(1).map_err(|_| {
        control.fault(StringExpansionFault::Allocation {
            region: StringExpansionAllocation::LevelArena,
            requested: 1,
        })
    })?;

    let zero = control.emit_level(LevelNode::Zero, 0, &mut levels, cancelled)?;
    let char_constant = control.emit_expression(
        ExprNode::Constant {
            name: top_level_name("Char"),
            levels: Vec::new(),
        },
        0,
        &mut nodes,
        cancelled,
    )?;
    let list_cons = control.emit_expression(
        ExprNode::Constant {
            name: two_part_name("List", "cons"),
            levels: vec![zero],
        },
        0,
        &mut nodes,
        cancelled,
    )?;
    let list_cons_char = control.emit_expression(
        ExprNode::Apply {
            function: list_cons,
            argument: char_constant,
        },
        0,
        &mut nodes,
        cancelled,
    )?;
    let list_nil = control.emit_expression(
        ExprNode::Constant {
            name: two_part_name("List", "nil"),
            levels: vec![zero],
        },
        value.len(),
        &mut nodes,
        cancelled,
    )?;
    let mut spine = control.emit_expression(
        ExprNode::Apply {
            function: list_nil,
            argument: char_constant,
        },
        value.len(),
        &mut nodes,
        cancelled,
    )?;
    let char_of_nat = control.emit_expression(
        ExprNode::Constant {
            name: two_part_name("Char", "ofNat"),
            levels: Vec::new(),
        },
        0,
        &mut nodes,
        cancelled,
    )?;

    for (at_byte, character) in value.char_indices().rev() {
        let code = u64::from(u32::from(character));
        let literal = control.emit_expression(
            ExprNode::NatLiteral {
                limbs_le: natural_limbs(code, control.progress)?,
            },
            at_byte,
            &mut nodes,
            cancelled,
        )?;
        let character = control.emit_expression(
            ExprNode::Apply {
                function: char_of_nat,
                argument: literal,
            },
            at_byte,
            &mut nodes,
            cancelled,
        )?;
        let cons = control.emit_expression(
            ExprNode::Apply {
                function: list_cons_char,
                argument: character,
            },
            at_byte,
            &mut nodes,
            cancelled,
        )?;
        spine = control.emit_expression(
            ExprNode::Apply {
                function: cons,
                argument: spine,
            },
            at_byte,
            &mut nodes,
            cancelled,
        )?;
    }

    let string_of_list = control.emit_expression(
        ExprNode::Constant {
            name: two_part_name("String", "ofList"),
            levels: Vec::new(),
        },
        value.len(),
        &mut nodes,
        cancelled,
    )?;
    let root = control.emit_expression(
        ExprNode::Apply {
            function: string_of_list,
            argument: spine,
        },
        value.len(),
        &mut nodes,
        cancelled,
    )?;
    let actual_nodes = u64::try_from(nodes.len())
        .unwrap_or(u64::MAX)
        .saturating_add(u64::try_from(levels.len()).unwrap_or(u64::MAX));
    if actual_nodes != expected_nodes || control.progress.owned_units != expected_owned_units {
        return Err(control.fault(StringExpansionFault::Accounting {
            expected_nodes,
            actual_nodes,
            expected_owned_units,
            actual_owned_units: control.progress.owned_units,
        }));
    }
    control.progress.generated_arenas = 1;
    Ok(StringExpansionResult {
        term: WireExpr::from_parts(nodes, levels, root),
        progress: control.progress,
    })
}

pub fn expand_string_literal(value: &str, budget: StringExpansionBudget) -> StringExpansionOutcome {
    expand_string_literal_with(value, budget, || false)
}

pub fn expand_string_literal_with(
    value: &str,
    budget: StringExpansionBudget,
    mut cancelled: impl FnMut() -> bool,
) -> StringExpansionOutcome {
    match expand(value, budget, &mut cancelled) {
        Ok(result) => StringExpansionOutcome::Expanded(result),
        Err(Halt::Stop(stop)) => StringExpansionOutcome::Inconclusive(stop),
        Err(Halt::Fault { fault, progress }) => {
            StringExpansionOutcome::InternalFault { fault, progress }
        }
    }
}
