//! Native `recOn` and `casesOn` candidates (fln-derived-declaration-frontier-cj7s).
//!
//! The inputs are the kernel-level family and recursor declarations, so the
//! generators also work on decoded Reference artifacts without source parsing.
//! They neither insert constants nor install elaborator attributes. A caller
//! must send every candidate through its ordinary kernel/checker admission and
//! may enable source generation only after the required corpus identity check.
//!
//! Algorithms: the pin's `Lean/Meta/Constructions/RecOn.lean::mkRecOn` and
//! `library/constructions/cases_on.cpp::mk_cases_on`. In particular, a mutual
//! `casesOn` keeps only its own motive/minors, replaces the other motives with
//! `PUnit`, and discards induction hypotheses rather than constructor fields.

use crate::lctx::LocalDecl;
use crate::records::{Builder, RecordBudget, RecordError, app, fv};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{
    ConstantVal, DefinitionSafety, DefinitionVal, InductiveVal, RecursorVal, ReducibilityHints,
};
use std::collections::HashSet;

mod course_of_values;
pub use course_of_values::{below_declaration, brec_on_declarations};

/// A candidate could not be constructed; this is not a kernel verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuxiliaryError {
    InvalidRecursorName,
    InvalidTelescope,
    InconsistentFamily,
    ResourceLimit,
}

impl std::fmt::Display for AuxiliaryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidRecursorName => "auxiliary generation requires a named .rec recursor",
            Self::InvalidTelescope => "auxiliary recursor telescope is malformed or unresolved",
            Self::InconsistentFamily => {
                "auxiliary recursor metadata disagrees with its inductive family"
            }
            Self::ResourceLimit => "auxiliary recursor generation work limit reached",
        })
    }
}

impl std::error::Error for AuxiliaryError {}

impl From<RecordError> for AuxiliaryError {
    fn from(error: RecordError) -> Self {
        match error {
            RecordError::ResourceLimit => Self::ResourceLimit,
            _ => Self::InvalidTelescope,
        }
    }
}

struct Build {
    work: Builder,
    remaining_binders: usize,
    next: u64,
}

impl Build {
    fn new(budget: RecordBudget, recursor: &RecursorVal) -> Result<Self, AuxiliaryError> {
        let mut work = Builder {
            remaining: budget.max_nodes,
        };
        // This also refuses free/metavariables and charges the actual input DAG
        // before opening any telescope. All walks are iterative.
        work.scan(&recursor.base.type_, &HashSet::new(), &Name::anonymous())?;
        if recursor.base.level_params.len() > budget.max_binders {
            return Err(AuxiliaryError::ResourceLimit);
        }
        Ok(Self {
            work,
            remaining_binders: budget.max_binders,
            next: 0,
        })
    }

    fn local(
        &mut self,
        user_name: Name,
        type_: Expr,
        binder_info: BinderInfo,
    ) -> Result<LocalDecl, AuxiliaryError> {
        self.work.tick()?;
        self.remaining_binders = self
            .remaining_binders
            .checked_sub(1)
            .ok_or(AuxiliaryError::ResourceLimit)?;
        let index = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or(AuxiliaryError::ResourceLimit)?;
        Ok(LocalDecl {
            id: FVarId(Name::num(Name::from_components(["_fln_auxiliary"]), index)),
            user_name,
            type_,
            value: None,
            binder_info,
            index: index as usize,
        })
    }

    fn telescope(&mut self, type_: &Expr) -> Result<(Vec<LocalDecl>, Expr), AuxiliaryError> {
        let mut current = type_.clone();
        let mut locals = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = current.node()
        {
            let local = self.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
            current = body
                .subst_loose(0, &[fv(&local)])
                .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            locals.push(local);
        }
        Ok((locals, current))
    }

    fn close(
        &mut self,
        locals: &[LocalDecl],
        body: Expr,
        lambda: bool,
    ) -> Result<Expr, AuxiliaryError> {
        self.work
            .close(locals, body, lambda, false)
            .map_err(Into::into)
    }

    /// The pin's mk_pi_unit/mk_fun_unit: preserve each dependent domain and
    /// binder name, replace the result, and use ordinary binder annotations.
    fn unit_telescope(
        &mut self,
        type_: &Expr,
        unit: &Expr,
        lambda: bool,
    ) -> Result<Expr, AuxiliaryError> {
        let mut current = type_;
        let mut binders = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = current.node()
        {
            self.work.tick()?;
            if binders.len() >= self.remaining_binders {
                return Err(AuxiliaryError::ResourceLimit);
            }
            binders.push((binder_name.clone(), binder_type.clone()));
            current = body;
        }
        let mut result = unit.clone();
        for (name, domain) in binders.into_iter().rev() {
            self.work.tick()?;
            result = if lambda {
                Expr::lam(name, domain, result, BinderInfo::Default)
            } else {
                Expr::forall_e(name, domain, result, BinderInfo::Default)
            };
        }
        Ok(result)
    }

    fn finish(
        &mut self,
        recursor: &RecursorVal,
        name: Name,
        params: &[LocalDecl],
        result: Expr,
        value: Expr,
    ) -> Result<DefinitionVal, AuxiliaryError> {
        let type_ = self.close(params, result, false)?;
        let value = self.close(params, value, true)?;
        // A forged telescope whose reordered binders depend on a removed minor
        // must fail here rather than leak an unbound local into a candidate.
        self.work
            .scan(&type_, &HashSet::new(), &Name::anonymous())?;
        self.work
            .scan(&value, &HashSet::new(), &Name::anonymous())?;
        Ok(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: recursor.base.level_params.clone(),
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            // An admitted recursor's safety covers its family and telescope.
            // Untrusted metadata remains a candidate and must be checked.
            safety: if recursor.is_unsafe {
                DefinitionSafety::Unsafe
            } else {
                DefinitionSafety::Safe
            },
            all: vec![name],
        })
    }
}

fn family_name(recursor: &RecursorVal) -> Result<Name, AuxiliaryError> {
    if !matches!(recursor.base.name.leaf_view(), LeafView::Str("rec"))
        || recursor.base.name.parent().is_anonymous()
    {
        return Err(AuxiliaryError::InvalidRecursorName);
    }
    Ok(recursor.base.name.parent())
}

fn argument_count(recursor: &RecursorVal) -> Result<usize, AuxiliaryError> {
    [
        recursor.num_params,
        recursor.num_motives,
        recursor.num_minors,
        recursor.num_indices,
        1,
    ]
    .into_iter()
    .try_fold(0usize, |sum, n| sum.checked_add(n as usize))
    .ok_or(AuxiliaryError::ResourceLimit)
}

/// Reorder a recursor's arguments to parameters, motives, indices, major
/// premise, minor premises. Every binder's name and annotation is preserved.
pub fn rec_on_declaration(
    recursor: &RecursorVal,
    budget: RecordBudget,
) -> Result<DefinitionVal, AuxiliaryError> {
    let family = family_name(recursor)?;
    let expected = argument_count(recursor)?;
    if expected > budget.max_binders {
        return Err(AuxiliaryError::ResourceLimit);
    }
    let mut build = Build::new(budget, recursor)?;
    let (locals, result) = build.telescope(&recursor.base.type_)?;
    if locals.len() != expected || recursor.num_motives == 0 {
        return Err(AuxiliaryError::InvalidTelescope);
    }
    let prefix = recursor.num_params as usize + recursor.num_motives as usize;
    let suffix = prefix + recursor.num_minors as usize;
    let params: Vec<_> = locals[..prefix]
        .iter()
        .chain(&locals[suffix..])
        .chain(&locals[prefix..suffix])
        .cloned()
        .collect();
    let value = app(
        Expr::const_(
            recursor.base.name.clone(),
            recursor
                .base
                .level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect(),
        ),
        locals.iter().map(fv),
    );
    build.finish(recursor, Name::str(family, "recOn"), &params, result, value)
}

/// Construct case analysis from an inductive recursor. `families` supplies
/// every type named by `recursor.all`; its slice order is immaterial, while the
/// recursor's own family and constructor orders remain observable.
pub fn cases_on_declaration(
    inductive: &InductiveVal,
    recursor: &RecursorVal,
    families: &[InductiveVal],
    budget: RecordBudget,
) -> Result<DefinitionVal, AuxiliaryError> {
    let family = family_name(recursor)?;
    if families.len() > budget.max_binders {
        return Err(AuxiliaryError::ResourceLimit);
    }
    if family != inductive.base.name
        || recursor.num_params != inductive.num_params
        || recursor.num_indices != inductive.num_indices
        || recursor.is_unsafe != inductive.is_unsafe
        || recursor.all.iter().filter(|n| **n == family).count() != 1
        || recursor.all.len() > recursor.num_motives as usize
    {
        return Err(AuxiliaryError::InconsistentFamily);
    }
    let expected = argument_count(recursor)?;
    if expected > budget.max_binders {
        return Err(AuxiliaryError::ResourceLimit);
    }
    let mut build = Build::new(budget, recursor)?;
    let mut minor_is_main = Vec::new();
    for name in &recursor.all {
        build.work.tick()?;
        let mut matches = families.iter().filter(|ind| &ind.base.name == name);
        let member = matches.next().ok_or(AuxiliaryError::InconsistentFamily)?;
        if matches.next().is_some()
            || member.num_params != inductive.num_params
            || member.is_unsafe != recursor.is_unsafe
            || minor_is_main
                .len()
                .checked_add(member.ctors.len())
                .is_none_or(|count| count > recursor.num_minors as usize)
        {
            return Err(AuxiliaryError::InconsistentFamily);
        }
        minor_is_main.extend(std::iter::repeat_n(name == &family, member.ctors.len()));
    }
    // Nested-recursion auxiliaries may add motives/minors beyond `all`.
    // They are unused by this family's case analysis, just like sibling types.
    minor_is_main.resize(recursor.num_minors as usize, false);
    let (locals, result) = build.telescope(&recursor.base.type_)?;
    if locals.len() != expected {
        return Err(AuxiliaryError::InvalidTelescope);
    }
    let level_count = recursor.base.level_params.len();
    let elimination = if level_count == inductive.base.level_params.len() {
        Level::zero()
    } else if level_count == inductive.base.level_params.len() + 1 {
        Level::param(recursor.base.level_params[0].clone())
    } else {
        return Err(AuxiliaryError::InconsistentFamily);
    };
    let unit = Expr::const_(Name::from_components(["PUnit"]), vec![elimination.clone()]);
    let star = Expr::const_(Name::from_components(["PUnit", "unit"]), vec![elimination]);
    let num_params = recursor.num_params as usize;
    let num_motives = recursor.num_motives as usize;
    let minor_start = num_params + num_motives;
    let suffix = minor_start + recursor.num_minors as usize;
    let motives = &locals[num_params..minor_start];
    let main = recursor
        .all
        .iter()
        .position(|n| n == &family)
        .ok_or(AuxiliaryError::InconsistentFamily)?;
    let main_id = &motives[main].id;
    let mut params = locals[..num_params].to_vec();
    let mut arguments: Vec<_> = params.iter().map(fv).collect();
    for (index, motive) in motives.iter().enumerate() {
        if index == main {
            params.push(motive.clone());
            arguments.push(fv(motive));
        } else {
            arguments.push(build.unit_telescope(&motive.type_, &unit, true)?);
        }
    }
    params.extend_from_slice(&locals[suffix..]);
    for (minor, is_main) in locals[minor_start..suffix].iter().zip(minor_is_main) {
        let (fields, result) = build.telescope(&minor.type_)?;
        let mut non_recursive = Vec::new();
        let mut minor_params = Vec::new();
        for field in fields {
            let mut target = &field.type_;
            while let ExprNode::ForallE { body, .. } = target.node() {
                build.work.tick()?;
                target = body;
            }
            while let ExprNode::App { f, .. } = target.node() {
                build.work.tick()?;
                target = f;
            }
            let motive = match target.node() {
                ExprNode::FVar { id } if motives.iter().any(|m| &m.id == id) => Some(id),
                _ => None,
            };
            if let Some(id) = motive {
                if id == main_id {
                    minor_params.push(field);
                } else {
                    let type_ = build.unit_telescope(&field.type_, &unit, false)?;
                    minor_params.push(build.local(field.user_name, type_, field.binder_info)?);
                }
            } else {
                if is_main {
                    non_recursive.push(field.clone());
                }
                minor_params.push(field);
            }
        }
        let body = if is_main {
            let type_ = build.close(&non_recursive, result, false)?;
            let new_minor = build.local(minor.user_name.clone(), type_, minor.binder_info)?;
            let body = app(fv(&new_minor), non_recursive.iter().map(fv));
            params.push(new_minor);
            body
        } else {
            star.clone()
        };
        arguments.push(build.close(&minor_params, body, true)?);
    }
    arguments.extend(locals[suffix..].iter().map(fv));
    let value = app(
        Expr::const_(
            recursor.base.name.clone(),
            recursor
                .base
                .level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect(),
        ),
        arguments,
    );
    build.finish(
        recursor,
        Name::str(family, "casesOn"),
        &params,
        result,
        value,
    )
}
