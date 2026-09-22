//! Source level syntax and declaration-level quantification. Universe parameters
//! are rigid names, never unification metavariables or term-level locals.
use super::*;
use fln_core::level::LevelView;
use std::collections::{BTreeSet, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LevelSyntaxError {
    Malformed,
    Unknown(Name),
    Duplicate(Name),
    Unused(Name),
    OffsetTooLarge,
    TooManyArguments { expected: usize, actual: usize },
    LocalUniverseArguments,
}
impl std::fmt::Display for LevelSyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => write!(f, "malformed universe level syntax"),
            Self::Unknown(n) => write!(f, "unknown universe level `{}`", n.to_display_string()),
            Self::Duplicate(n) => write!(
                f,
                "duplicate universe parameter `{}`",
                n.to_display_string()
            ),
            Self::Unused(n) => write!(
                f,
                "unused explicit universe parameter `{}`",
                n.to_display_string()
            ),
            Self::OffsetTooLarge => {
                write!(f, "universe offset exceeds the supported maximum of 32")
            }
            Self::TooManyArguments { expected, actual } => write!(
                f,
                "constant has {expected} universe parameters but received {actual}"
            ),
            Self::LocalUniverseArguments => {
                write!(f, "universe arguments require a global constant")
            }
        }
    }
}
impl std::error::Error for LevelSyntaxError {}
fn error(error: LevelSyntaxError) -> NatDefinitionElabError {
    failure(SourceInferenceError::LevelSyntax(error))
}

/// The pinned `declId` suffix is optional `[.{, sepBy1 ident, }]`.
/// Called by both elaboration and post-admission instance registration.
pub(super) fn explicit_parameters(syntax: &Syntax) -> Result<Vec<Name>, NatDefinitionElabError> {
    let parts = expect_null_args(syntax, "explicit universe parameters")?;
    if parts.is_empty() {
        return Ok(vec![]);
    }
    let [open, names, close] = parts else {
        return Err(error(LevelSyntaxError::Malformed));
    };
    expect_atom(open, ".{", "universe parameter opener")?;
    expect_atom(close, "}", "universe parameter closer")?;
    let names = expect_null_args(names, "universe parameter list")?;
    if names.is_empty() || names.len() % 2 == 0 {
        return Err(error(LevelSyntaxError::Malformed));
    }
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for (index, name) in names.iter().enumerate() {
        if index % 2 == 1 {
            expect_atom(name, ",", "universe parameter separator")?;
            continue;
        }
        let Syntax::Ident { val, .. } = name else {
            return Err(error(LevelSyntaxError::Malformed));
        };
        if val.is_anonymous() || !val.parent().is_anonymous() {
            return Err(error(LevelSyntaxError::Malformed));
        }
        if !seen.insert(val.clone()) {
            return Err(error(LevelSyntaxError::Duplicate(val.clone())));
        }
        result.push(val.clone());
    }
    Ok(result)
}

impl Context {
    pub(super) fn declare_levels(&mut self, syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
        let names = explicit_parameters(syntax)?;
        for _ in &names {
            self.tick()?;
        }
        self.explicit_levels = names.len();
        self.level_params = names;
        for name in self.source_scope.universes.clone() {
            self.tick()?;
            if self.level_params.contains(&name) {
                return Err(error(LevelSyntaxError::Duplicate(name)));
            }
            self.level_params.push(name);
        }
        for name in self.source_scope.variables.levels().to_vec() {
            self.tick()?;
            if !self.level_params.contains(&name) {
                self.level_params.push(name);
            }
        }
        Ok(())
    }

    fn level_offset(&mut self, syntax: &Syntax) -> Result<u32, NatDefinitionElabError> {
        self.tick()?;
        let value = elaborate_atom(syntax, &[], false, None)?;
        let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = value.node()
        else {
            return Err(error(LevelSyntaxError::Malformed));
        };
        n.to_u64()
            .filter(|n| *n <= 32)
            .map(|n| n as u32)
            .ok_or_else(|| error(LevelSyntaxError::OffsetTooLarge))
    }

    pub(super) fn source_level(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Level, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Syntax),
            Offset(u32),
            Maximum(bool, usize),
        }
        let mut tasks = vec![Task::Visit(syntax)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(syntax) => {
                    if let Syntax::Ident { val, .. } = syntax {
                        if !self.level_params.contains(val) {
                            if !self.infer_level_params
                                || val.is_anonymous()
                                || !val.parent().is_anonymous()
                            {
                                return Err(error(LevelSyntaxError::Unknown(val.clone())));
                            }
                            self.level_params.push(val.clone());
                        }
                        values.push(Level::param(val.clone()));
                        continue;
                    }
                    let Syntax::Node { kind, args, .. } = syntax else {
                        return Err(error(LevelSyntaxError::Malformed));
                    };
                    if kind == &Name::from_components(["num"]) {
                        let offset = self.level_offset(syntax)?;
                        values.push(Level::zero());
                        tasks.push(Task::Offset(offset));
                    } else if kind == &parser_kind(&["Level", "hole"]) {
                        let [hole] = args.as_slice() else {
                            return Err(error(LevelSyntaxError::Malformed));
                        };
                        expect_atom(hole, "_", "universe hole")?;
                        values.push(self.level()?);
                    } else if kind == &parser_kind(&["Level", "paren"]) {
                        let [open, inner, close] = args.as_slice() else {
                            return Err(error(LevelSyntaxError::Malformed));
                        };
                        expect_atom(open, "(", "universe parentheses")?;
                        expect_atom(close, ")", "universe parentheses")?;
                        tasks.push(Task::Visit(inner));
                    } else if kind == &parser_kind(&["Level", "addLit"]) {
                        let [base, plus, offset] = args.as_slice() else {
                            return Err(error(LevelSyntaxError::Malformed));
                        };
                        expect_atom(plus, "+", "universe offset")?;
                        let offset = self.level_offset(offset)?;
                        tasks.push(Task::Offset(offset));
                        tasks.push(Task::Visit(base));
                    } else if kind == &parser_kind(&["Level", "max"])
                        || kind == &parser_kind(&["Level", "imax"])
                    {
                        let [keyword, arguments] = args.as_slice() else {
                            return Err(error(LevelSyntaxError::Malformed));
                        };
                        let imax = kind == &parser_kind(&["Level", "imax"]);
                        expect_atom(
                            keyword,
                            if imax { "imax" } else { "max" },
                            "universe maximum",
                        )?;
                        let arguments = expect_null_args(arguments, "maximum arguments")?;
                        if arguments.is_empty() {
                            return Err(error(LevelSyntaxError::Malformed));
                        }
                        tasks.push(Task::Maximum(imax, arguments.len()));
                        for arg in arguments.iter().rev() {
                            tasks.push(Task::Visit(arg));
                        }
                    } else {
                        return Err(error(LevelSyntaxError::Malformed));
                    }
                }
                Task::Offset(offset) => {
                    let mut level = values
                        .pop()
                        .ok_or_else(|| error(LevelSyntaxError::Malformed))?;
                    for _ in 0..offset {
                        self.tick()?;
                        level = level
                            .succ()
                            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
                    }
                    values.push(level);
                }
                Task::Maximum(imax, count) => {
                    let mut level = values
                        .pop()
                        .ok_or_else(|| error(LevelSyntaxError::Malformed))?;
                    for _ in 1..count {
                        self.tick()?;
                        let left = values
                            .pop()
                            .ok_or_else(|| error(LevelSyntaxError::Malformed))?;
                        level = if imax {
                            Level::imax(left, level)
                        } else {
                            Level::max(left, level)
                        }
                        .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
                    }
                    values.push(level);
                }
            }
        }
        if values.len() != 1 {
            return Err(error(LevelSyntaxError::Malformed));
        }
        Ok(values.pop().expect("one universe result"))
    }

    pub(super) fn source_sort(
        &mut self,
        parts: &[Syntax],
        type_: bool,
    ) -> Result<Level, NatDefinitionElabError> {
        let [keyword, optional] = parts else {
            return Err(error(LevelSyntaxError::Malformed));
        };
        expect_atom(
            keyword,
            if type_ { "Type" } else { "Sort" },
            "universe keyword",
        )?;
        let level = match expect_null_args(optional, "optional universe level")? {
            [] => Level::zero(),
            [syntax] => self.source_level(syntax)?,
            _ => return Err(error(LevelSyntaxError::Malformed)),
        };
        if type_ {
            level
                .succ()
                .map_err(|_| failure(SourceInferenceError::ResourceLimit))
        } else {
            Ok(level)
        }
    }

    pub(super) fn explicit_universes(
        &mut self,
        args: &[Syntax],
    ) -> Result<Typed, NatDefinitionElabError> {
        let [head, open, levels, close] = args else {
            return Err(error(LevelSyntaxError::Malformed));
        };
        expect_atom(open, ".{", "explicit universe opener")?;
        expect_atom(close, "}", "explicit universe closer")?;
        let Syntax::Ident { val: name, .. } = head else {
            return Err(error(LevelSyntaxError::LocalUniverseArguments));
        };
        // Do not bypass local shadowing to reach a global with the same spelling.
        if self
            .txn
            .lctx
            .decls()
            .iter()
            .any(|local| &local.user_name == name)
            || self.recursion.as_ref().is_some_and(|r| &r.name == name)
        {
            return Err(error(LevelSyntaxError::LocalUniverseArguments));
        }
        let name = &self
            .resolve_source_name(name)?
            .unwrap_or_else(|| name.clone());
        let levels = expect_null_args(levels, "explicit universe list")?;
        if levels.is_empty() || levels.len() % 2 == 0 {
            return Err(error(LevelSyntaxError::Malformed));
        }
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        let base = info.constant_val();
        let count = levels.len().div_ceil(2);
        if count > base.level_params.len() {
            return Err(error(LevelSyntaxError::TooManyArguments {
                expected: base.level_params.len(),
                actual: count,
            }));
        }
        let mut actual = Vec::new();
        for (index, level) in levels.iter().enumerate() {
            if index % 2 == 1 {
                expect_atom(level, ",", "universe separator")?;
            } else {
                actual.push(self.source_level(level)?);
            }
        }
        while actual.len() < base.level_params.len() {
            actual.push(self.level()?);
        }
        Ok(Typed {
            type_: self.instantiate_params(&base.type_, &base.level_params, &actual)?,
            value: Expr::const_(name.clone(), actual),
        })
    }

    /// Match the pinned ordering: used scope levels, explicit declaration levels,
    /// then automatically introduced levels in lexicographic order. An explicit
    /// but unused parameter is an error, not a vacuous new polymorphic constant.
    pub(super) fn declaration_levels(
        &mut self,
        terms: &[Expr],
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        let mut used = BTreeSet::new();
        let mut pending: Vec<_> = terms.iter().collect();
        let mut seen = HashSet::new();
        let mut level_seen = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            let mut levels = Vec::new();
            match expr.node() {
                ExprNode::Sort { level } => levels.push(level),
                ExprNode::Const { levels: args, .. } => levels.extend(args),
                ExprNode::App { f, a } => pending.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => pending.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => pending.extend([type_, value, body]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
                _ => {}
            }
            while let Some(level) = levels.pop() {
                self.tick()?;
                if !level_seen.insert(std::ptr::from_ref(level)) {
                    continue;
                }
                match level.view() {
                    LevelView::Param(name) => {
                        used.insert(name.clone());
                    }
                    LevelView::Succ(inner) => levels.push(inner),
                    LevelView::Max(a, b) | LevelView::IMax(a, b) => levels.extend([a, b]),
                    _ => {}
                }
            }
        }
        let mut result = Vec::new();
        // The pin orders used scope levels before declaration-local levels;
        // unused scope levels do not force vacuous parameters.
        for name in self.source_scope.universes.clone() {
            self.tick()?;
            if used.remove(&name) {
                result.push(name);
            }
        }
        for name in &self.level_params[..self.explicit_levels] {
            if !used.remove(name) {
                return Err(error(LevelSyntaxError::Unused(name.clone())));
            }
            result.push(name.clone());
        }
        result.extend(used);
        Ok(result)
    }
}
