//! Equation theorems `f.eq_<n>`, `f.eq_def` and `f.eq_unfold`, generated on demand.
//!
//! The pin reserves these names for every safe definition and builds the theorems when a name
//! is first resolved (vendored `Lean/Meta/Eqns.lean`: `declFromEqLikeName`, the reserved-name
//! action, `getEqnsFor?` and `getUnfoldEqnFor?`; `Lean/Elab/PreDefinition/EqUnfold.lean`:
//! `getConstUnfoldEqnFor?`). The engine generates them before the command that names them (see
//! `fln`'s source command stream), so the elaborator only ever reads them from the environment.
//!
//! Generated here, with the pin's statements, for a definition whose value applies no recursor:
//! - `f.eq_1 : ∀ xs, f xs = rhs`, where `rhs` is the value's body with its head `let`s
//!   substituted (`Lean.Elab.Eqns.mkEqns` with no `match` to split: `expandRHS?` then
//!   `saveEqn`, Elab/PreDefinition/Eqns.lean:155-222, 293-310, 351-394);
//! - `f.eq_def : ∀ xs, f xs = body` with each nondependent `let` made a `have`
//!   (`mkSimpleEqThm`, Meta/Eqns.lean:183-203);
//! - `f.eq_unfold : f = fun xs => body` (`getConstUnfoldEqnFor?`).
//!
//! Each is proved by `Eq.refl`, which the kernel checks by unfolding `f`; nothing is trusted.
//!
//! Not generated, and refused typed where a name asks for them: a recursive definition
//! (structural, well-founded) and a definition whose value applies a recursor. This engine
//! compiles a `match` to recursor applications, and the pin's statements for those split the
//! definition's matcher (`splitMatch?`) and print `match` in `eq_def`; neither exists here.
use super::*;
use fln_env::constants::{ConstantInfo, ConstantVal, DefinitionVal, TheoremVal};
mod capture;
pub mod journal;
mod matched;

/// Which equation-like name was asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Suffix {
    /// `eq_<n>`: one of the equations `getEqnsFor?` generates together.
    Equation,
    /// `eq_def`, the unfolding theorem.
    Def,
    /// `eq_unfold`, the constant's unfolding theorem.
    Unfold,
}

/// Why this engine does not generate a definition's equation theorems.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unsupported {
    /// The definition is recursive: its unfolding theorem splits the compiled recursion.
    Recursive,
    /// The value applies a recursor, a compiled `match`; the pin's statements split its
    /// matcher, which this engine does not declare.
    CompiledMatch,
    /// The value applies a matcher or another auxiliary eliminator of an imported declaration.
    Auxiliary(Name),
    /// The value keeps a lifted local function inline; the pin's statement names the helper.
    LocalFunction(Name),
    /// Nothing generated the equations before this reference was elaborated.
    NotRequested,
    /// The definition is by pattern matching and its `match` was not recorded.
    UnrecordedMatch,
    /// The statement would contain a `match`, which the pin prints through its matcher.
    MatchInStatement,
    /// The equation's proof was not found here.
    Unproved,
    /// The definition is by well-founded recursion: the pin's unfolding theorem rewrites with
    /// `WellFounded.fix_eq` (vendored Lean/Elab/PreDefinition/WF/Unfold.lean:32-48, 211).
    WellFounded,
}

/// A name the pin generates on demand that this engine did not.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NotGenerated {
    pub name: Name,
    pub declaration: Name,
    pub reason: Unsupported,
}

impl std::fmt::Display for NotGenerated {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let reason = match &self.reason {
            Unsupported::Recursive => "it is recursive".to_string(),
            Unsupported::CompiledMatch => {
                "its value is a `match` this engine compiles to recursor applications, and \
                 the pin's equations split its matcher"
                    .to_string()
            }
            Unsupported::Auxiliary(name) => {
                format!(
                    "its value applies the auxiliary `{}`",
                    name.to_display_string()
                )
            }
            Unsupported::LocalFunction(name) => format!(
                "its value keeps the local function `{}` inline",
                name.to_display_string()
            ),
            Unsupported::NotRequested => {
                "no equation theorems were generated for this reference".to_string()
            }
            Unsupported::UnrecordedMatch => {
                "its `match` is not one whose alternatives this engine records".to_string()
            }
            Unsupported::MatchInStatement => {
                "the statement contains a `match`, which the pin states with its matcher"
                    .to_string()
            }
            Unsupported::Unproved => "its proof was not found here".to_string(),
            Unsupported::WellFounded => {
                "it is defined by well-founded recursion, whose equations the pin proves \
                 from `WellFounded.fix_eq`"
                    .to_string()
            }
        };
        write!(
            f,
            "the equation theorem `{}` of `{}` is not generated here: {reason}",
            self.name.to_display_string(),
            self.declaration.to_display_string()
        )
    }
}

/// `String.isNat`: ASCII digits, an `_` only between two digits.
fn is_nat(text: &str) -> bool {
    let mut last_was_digit = false;
    for character in text.chars() {
        if character == '_' {
            if !last_was_digit {
                return false;
            }
            last_was_digit = false;
        } else if character.is_ascii_digit() {
            last_was_digit = true;
        } else {
            return false;
        }
    }
    last_was_digit
}

fn safe_definition<'e>(env: &'e Environment, name: &Name) -> Option<&'e DefinitionVal> {
    match env.find(name) {
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
            Some(definition)
        }
        _ => None,
    }
}

/// The pin's matchers and splitters are `f.match_<n>` and `f.match_<n>.splitter`.
fn is_matcher_name(name: &Name) -> bool {
    match name.leaf_view() {
        LeafView::Str(leaf) => leaf
            .strip_prefix("match_")
            .is_some_and(|index| !index.is_empty() && index.bytes().all(|b| b.is_ascii_digit())),
        _ => false,
    }
}

/// `declFromEqLikeName`: the definition and suffix an equation-like name belongs to. A
/// matcher's own equations (`f.match_1.eq_1`) belong to `Lean.Meta.Match.MatchEqs`.
pub fn target(env: &Environment, name: &Name) -> Option<(Name, Suffix)> {
    let LeafView::Str(leaf) = name.leaf_view() else {
        return None;
    };
    let suffix = match leaf {
        "eq_def" => Suffix::Def,
        "eq_unfold" => Suffix::Unfold,
        _ if leaf.strip_prefix("eq_").is_some_and(is_nat) => Suffix::Equation,
        _ => return None,
    };
    let declaration = name.parent();
    (safe_definition(env, &declaration).is_some() && !is_matcher_name(&declaration))
        .then_some((declaration, suffix))
}

fn equation_name(declaration: &Name, index: usize) -> Name {
    Name::str(declaration.clone(), format!("eq_{index}"))
}

/// Whether the definition's equations (`eq_1`, …) have been generated.
pub fn equations_generated(env: &Environment, declaration: &Name) -> bool {
    env.contains(&equation_name(declaration, 1))
}

/// The generated equations `eq_1`, `eq_2`, … in order (`alreadyGenerated?`).
pub fn generated_equations(env: &Environment, declaration: &Name) -> Vec<Name> {
    (1..)
        .map(|index| equation_name(declaration, index))
        .take_while(|name| env.contains(name))
        .collect()
}

/// A constant the value applies that makes it unsupported here.
fn unsupported_reason(env: &Environment, declaration: &Name, value: &Expr) -> Option<Unsupported> {
    if super::scope::structurally_recursive(env, declaration) {
        return Some(Unsupported::Recursive);
    }
    let mut pending = vec![value];
    let mut seen = std::collections::HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                let text = name.to_display_string();
                if text.starts_with("_fln") {
                    return Some(Unsupported::CompiledMatch);
                }
                if name == declaration {
                    return Some(Unsupported::Recursive);
                }
                if text.starts_with("WellFounded.") {
                    return Some(Unsupported::Recursive);
                }
                if matches!(env.find(name), Some(ConstantInfo::Rec(_))) {
                    return Some(Unsupported::CompiledMatch);
                }
                let auxiliary = is_matcher_name(name)
                    || matches!(
                        name.leaf_view(),
                        LeafView::Str(
                            "casesOn"
                                | "recOn"
                                | "brecOn"
                                | "binductionOn"
                                | "below"
                                | "ibelow"
                                | "_unary"
                                | "_binary"
                                | "_mutual"
                                | "splitter"
                        )
                    );
                if auxiliary {
                    return Some(Unsupported::Auxiliary(name.clone()));
                }
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                ..
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } => {
                if binder_name.to_display_string().starts_with("_fln") {
                    return Some(Unsupported::CompiledMatch);
                }
                pending.extend([binder_type, body]);
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                ..
            } => {
                if decl_name.to_display_string().starts_with("_fln") {
                    return Some(Unsupported::CompiledMatch);
                }
                // A `let rec`/`where` helper is lifted to `declaration.helper` and also kept
                // inline in the owner, whose pin value names the helper instead.
                let helper = declaration.append_core(decl_name);
                if !decl_name.is_anonymous() && env.contains(&helper) {
                    return Some(Unsupported::LocalFunction(helper));
                }
                pending.extend([type_, value, body]);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    None
}

/// Whether `expr` keeps a compiled `match` or recursion: a recursor, an auxiliary eliminator
/// or one of this engine's internal names.
pub(super) fn compiled_match(env: &Environment, expr: &Expr) -> bool {
    let mut pending = vec![expr];
    let mut seen = std::collections::HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        let internal = |name: &Name| name.to_display_string().starts_with("_fln");
        match expr.node() {
            ExprNode::Const { name, .. } => {
                if internal(name)
                    || matches!(env.find(name), Some(ConstantInfo::Rec(_)))
                    || is_matcher_name(name)
                    || matches!(
                        name.leaf_view(),
                        LeafView::Str("casesOn" | "recOn" | "brecOn" | "binductionOn")
                    )
                {
                    return true;
                }
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                ..
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } => {
                if internal(binder_name) {
                    return true;
                }
                pending.extend([binder_type, body]);
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                ..
            } => {
                if internal(decl_name) {
                    return true;
                }
                pending.extend([type_, value, body]);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

fn mentions_well_founded(expr: &Expr) -> bool {
    let mut pending = vec![expr];
    let mut seen = std::collections::HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                if name.to_display_string().starts_with("WellFounded.") {
                    return true;
                }
            }
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
    }
    false
}

/// Why `declaration`'s equation theorems would not be generated here, if they would not.
pub fn refusal(env: &Environment, declaration: &Name) -> Option<Unsupported> {
    let definition = safe_definition(env, declaration)?;
    unsupported_reason(env, declaration, &definition.value)
}

/// `Expr.cleanupAnnotations`: metadata and `optParam`/`autoParam`/`outParam`/`semiOutParam`.
fn cleanup_annotations(mut expr: Expr) -> Expr {
    loop {
        if let ExprNode::MData { expr: inner, .. } = expr.node() {
            expr = inner.clone();
            continue;
        }
        let (head, args) = spine_args(&expr);
        let annotation = match head.node() {
            ExprNode::Const { name, .. } => name.to_display_string(),
            _ => return expr,
        };
        let next = match (annotation.as_str(), args.as_slice()) {
            ("optParam" | "autoParam", [inner, _]) => inner.clone(),
            ("outParam" | "semiOutParam", [inner]) => inner.clone(),
            _ => return expr,
        };
        expr = next;
    }
}

fn spine_args(expr: &Expr) -> (&Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    (head, args)
}

fn app_n(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

/// The head `let`s and metadata of an equation's right-hand side, substituted (`expand`).
fn expand_head(mut rhs: Expr) -> Result<Expr, NatDefinitionElabError> {
    loop {
        rhs = match rhs.node() {
            ExprNode::LetE { value, body, .. } => body
                .subst_loose(0, std::slice::from_ref(value))
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            ExprNode::MData { expr, .. } => expr.clone(),
            _ => return Ok(rhs),
        };
    }
}

/// A definition's value opened as locals: `lambdaTelescope (cleanupAnnotations := true)`.
struct Telescope {
    locals: Vec<FVarId>,
    body: Expr,
    result: Expr,
    result_level: Level,
    lhs: Expr,
}

impl Context {
    fn equation_telescope(
        &mut self,
        definition: &DefinitionVal,
    ) -> Result<Telescope, NatDefinitionElabError> {
        let levels: Vec<Level> = definition
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let mut value = definition.value.clone();
        let mut type_ = definition.base.type_.clone();
        let mut locals = Vec::new();
        while let ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = value.node()
        {
            self.tick()?;
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                cleanup_annotations(binder_type.clone()),
                *binder_info,
            );
            let local = Expr::fvar(id.clone());
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE { body: codomain, .. } = type_.node() else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            type_ = self.substitute(codomain, &local)?;
            value = self.substitute(body, &local)?;
            locals.push(id);
        }
        let Some(sort) = self.known_type(&type_)? else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let sort = self.whnf(&sort)?;
        let ExprNode::Sort { level } = sort.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let lhs = app_n(
            Expr::const_(definition.base.name.clone(), levels.clone()),
            locals.iter().cloned().map(Expr::fvar),
        );
        Ok(Telescope {
            locals,
            body: value,
            result: type_,
            result_level: level.clone(),
            lhs,
        })
    }

    /// `mkForallFVars`/`mkLambdaFVars` over `locals`, with their names and binder kinds.
    fn close_locals(
        &mut self,
        locals: &[FVarId],
        mut body: Expr,
        forall: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        for id in locals.iter().rev() {
            self.tick()?;
            let local = self
                .txn
                .lctx
                .find(id)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let abstracted = body
                .abstract_fvar(id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            body = if forall {
                Expr::forall_e(local.user_name, local.type_, abstracted, local.binder_info)
            } else {
                Expr::lam(local.user_name, local.type_, abstracted, local.binder_info)
            };
        }
        Ok(body)
    }

    /// `letToHave`: a `let` whose body type-checks with its variable opaque becomes a `have`
    /// (vendored `Lean/Meta/LetToHave.lean`). The pin decides it by tracking whether checking
    /// the body unfolds the variable; here the kernel checks the body with the variable a
    /// plain local, against the type this elaborator reconstructs. When either answer is
    /// missing the `let` stays dependent.
    fn let_to_have(
        &mut self,
        expr: &Expr,
        level_params: &[Name],
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        if !contains_dependent_let(expr) {
            return Ok(expr.clone());
        }
        Ok(match expr.node() {
            ExprNode::App { f, a } => Expr::app(
                self.let_to_have(f, level_params)?,
                self.let_to_have(a, level_params)?,
            ),
            ExprNode::MData { data, expr } => {
                Expr::mdata(data.clone(), self.let_to_have(expr, level_params)?)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(
                struct_name.clone(),
                *idx,
                self.let_to_have(expr, level_params)?,
            ),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let lambda = matches!(expr.node(), ExprNode::Lam { .. });
                let binder_type = self.let_to_have(binder_type, level_params)?;
                let id = FVarId(self.fresh_name()?);
                let saved = self.txn.lctx.len();
                self.txn.lctx.add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                let opened = self.substitute(body, &Expr::fvar(id.clone()))?;
                let body = self.let_to_have(&opened, level_params);
                self.txn.lctx.truncate(saved);
                let body = body?
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                if lambda {
                    Expr::lam(binder_name.clone(), binder_type, body, *binder_info)
                } else {
                    Expr::forall_e(binder_name.clone(), binder_type, body, *binder_info)
                }
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let type_ = self.let_to_have(type_, level_params)?;
                let value = self.let_to_have(value, level_params)?;
                let id = FVarId(self.fresh_name()?);
                let saved = self.txn.lctx.len();
                let opened = self.substitute(body, &Expr::fvar(id.clone()))?;
                let non_dep = *non_dep || {
                    self.txn.lctx.add_param(
                        id.clone(),
                        decl_name.clone(),
                        type_.clone(),
                        BinderInfo::Default,
                    );
                    let nondependent = self.body_checks_opaque(&opened, level_params);
                    self.txn.lctx.truncate(saved);
                    nondependent?
                };
                if non_dep {
                    self.txn.lctx.add_param(
                        id.clone(),
                        decl_name.clone(),
                        type_.clone(),
                        BinderInfo::Default,
                    );
                } else {
                    self.txn.lctx.add_let(
                        id.clone(),
                        decl_name.clone(),
                        type_.clone(),
                        value.clone(),
                    );
                }
                let body = self.let_to_have(&opened, level_params);
                self.txn.lctx.truncate(saved);
                let body = body?
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                Expr::let_e(decl_name.clone(), type_, value, body, non_dep)
            }
            _ => expr.clone(),
        })
    }

    /// Whether `body` type-checks in the current local context, every local opaque but the
    /// dependent `let`s: the kernel checks it closed over that context.
    fn body_checks_opaque(
        &mut self,
        body: &Expr,
        level_params: &[Name],
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(body)? else {
            return Ok(false);
        };
        let locals = self.txn.lctx.decls().to_vec();
        let mut value = body.clone();
        let mut expected = type_;
        for local in locals.iter().rev() {
            self.tick()?;
            let close = |expr: &Expr| {
                expr.abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))
            };
            match &local.value {
                Some(definition) => {
                    value = Expr::let_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        definition.clone(),
                        close(&value)?,
                        false,
                    );
                    expected = Expr::let_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        definition.clone(),
                        close(&expected)?,
                        false,
                    );
                }
                None => {
                    value = Expr::lam(
                        local.user_name.clone(),
                        local.type_.clone(),
                        close(&value)?,
                        local.binder_info,
                    );
                    expected = Expr::forall_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        close(&expected)?,
                        local.binder_info,
                    );
                }
            }
        }
        if value.has_fvar() || expected.has_fvar() || value.has_expr_mvar() {
            return Ok(false);
        }
        let opaque = std::collections::BTreeSet::new();
        Ok(matches!(
            fln_kernel::check_type_with_unfolding(
                &self.txn.env,
                level_params,
                &value,
                &expected,
                self.kernel,
                fln_kernel::DefEqUnfolding {
                    opaque_definitions: &opaque,
                    unfold_theorems: false,
                },
            ),
            Outcome::Complete(Verdict::Accepted { .. })
        ))
    }

    fn theorem(
        &self,
        name: Name,
        definition: &DefinitionVal,
        type_: Expr,
        value: Expr,
    ) -> Declaration {
        Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: definition.base.level_params.clone(),
                type_,
            },
            value,
            all: vec![name],
        })
    }

    /// `f.eq_1` of a definition with no `match` to split (`mkEqns declName #[]`).
    fn simple_equation(
        &mut self,
        definition: &DefinitionVal,
    ) -> Result<Declaration, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let telescope = self.equation_telescope(definition)?;
            let rhs = expand_head(telescope.body.clone())?;
            let statement = self.equality(&telescope, rhs);
            let type_ = self.close_locals(&telescope.locals, statement, true)?;
            let proof = self.reflexivity(&telescope);
            let value = self.close_locals(&telescope.locals, proof, false)?;
            Ok(self.theorem(
                equation_name(&definition.base.name, 1),
                definition,
                type_,
                value,
            ))
        })();
        self.txn.lctx = saved;
        result
    }

    /// `f.eq_def` of a nonrecursive definition (`mkSimpleEqThm`).
    fn simple_unfold(
        &mut self,
        definition: &DefinitionVal,
    ) -> Result<Declaration, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let telescope = self.equation_telescope(definition)?;
            let statement = self.equality(&telescope, telescope.body.clone());
            let type_ = self.close_locals(&telescope.locals, statement, true)?;
            let type_ = self.let_to_have(&type_, &definition.base.level_params)?;
            let proof = self.reflexivity(&telescope);
            let value = self.close_locals(&telescope.locals, proof, false)?;
            Ok(self.theorem(
                Name::str(definition.base.name.clone(), "eq_def"),
                definition,
                type_,
                value,
            ))
        })();
        self.txn.lctx = saved;
        result
    }

    /// `f.eq_unfold : f = fun xs => rhs`, from the unfolding theorem's statement
    /// (`getConstUnfoldEqnFor?`), proved by `Eq.refl f`.
    fn const_unfold(
        &mut self,
        definition: &DefinitionVal,
        unfold: &Expr,
    ) -> Result<Declaration, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut statement = unfold.clone();
            let mut locals = Vec::new();
            while let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = statement.node()
            {
                self.tick()?;
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    binder_name.clone(),
                    binder_type.clone(),
                    *binder_info,
                );
                statement = self.substitute(body, &Expr::fvar(id.clone()))?;
                locals.push(id);
            }
            let (head, args) = spine_args(&statement);
            let (ExprNode::Const { name, .. }, [_, _, rhs]) = (head.node(), args.as_slice()) else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if name != &Name::from_components(["Eq"]) {
                return Err(failure(SourceInferenceError::Scope));
            }
            let function = self.close_locals(&locals, rhs.clone(), false)?;
            let levels: Vec<Level> = definition
                .base
                .level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect();
            let constant = Expr::const_(definition.base.name.clone(), levels);
            let Some(sort) = self.known_type(&definition.base.type_)? else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            let sort = self.whnf(&sort)?;
            let ExprNode::Sort { level } = sort.node() else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            let eq = Expr::const_(Name::from_components(["Eq"]), vec![level.clone()]);
            let type_ = app_n(
                eq,
                [definition.base.type_.clone(), constant.clone(), function],
            );
            let refl = Expr::const_(Name::from_components(["Eq", "refl"]), vec![level.clone()]);
            let value = app_n(refl, [definition.base.type_.clone(), constant]);
            Ok(self.theorem(
                Name::str(definition.base.name.clone(), "eq_unfold"),
                definition,
                type_,
                value,
            ))
        })();
        self.txn.lctx = saved;
        result
    }

    fn equality(&self, telescope: &Telescope, rhs: Expr) -> Expr {
        let eq = Expr::const_(
            Name::from_components(["Eq"]),
            vec![telescope.result_level.clone()],
        );
        app_n(eq, [telescope.result.clone(), telescope.lhs.clone(), rhs])
    }

    fn reflexivity(&self, telescope: &Telescope) -> Expr {
        let refl = Expr::const_(
            Name::from_components(["Eq", "refl"]),
            vec![telescope.result_level.clone()],
        );
        app_n(refl, [telescope.result.clone(), telescope.lhs.clone()])
    }

    /// `shouldGenerateEqnThms`: a definition whose type is not a proposition.
    fn proposition_typed(
        &mut self,
        definition: &DefinitionVal,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(sort) = self.known_type(&definition.base.type_)? else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let sort = self.whnf(&sort)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level == &Level::zero()))
    }
}

fn contains_dependent_let(expr: &Expr) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::LetE { non_dep: false, .. } => return true,
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

impl Context {
    /// A reference to an equation-like name that is not declared: the pin's "Unknown
    /// identifier" once its family was generated (`f.eq_4` of a definition with three
    /// equations) or when none is (a proposition), otherwise this engine's refusal.
    pub(super) fn missing_equation_theorem(
        &mut self,
        name: &Name,
    ) -> Result<NatDefinitionElabError, NatDefinitionElabError> {
        let unknown = failure(SourceInferenceError::UnknownConstant(name.clone()));
        let Some((declaration, suffix)) = target(&self.txn.env, name) else {
            return Ok(unknown);
        };
        if suffix == Suffix::Equation && equations_generated(&self.txn.env, &declaration) {
            return Ok(unknown);
        }
        let Some(definition) = safe_definition(&self.txn.env, &declaration).cloned() else {
            return Ok(unknown);
        };
        if self.proposition_typed(&definition)? {
            return Ok(unknown);
        }
        // The reason realizing it here gives, when it fails; otherwise nothing generated it.
        match realize(&self.txn.env, &Request::Name(name.clone()), self.kernel) {
            Err(
                refusal @ NatDefinitionElabError::Inference(SourceInferenceError::EquationTheorem(
                    _,
                )),
            ) => Ok(refusal),
            Err(other) => Err(other),
            Ok(_) => Ok(failure(SourceInferenceError::EquationTheorem(Box::new(
                NotGenerated {
                    name: name.clone(),
                    declaration,
                    reason: Unsupported::NotRequested,
                },
            )))),
        }
    }

    /// The equation theorems `rw [f]` rewrites with, when `syntax` names a global definition
    /// that has them (`withRWRulesSeq`'s `processId`, vendored Lean/Elab/Tactic/Rewrite.lean:
    /// 86-103): a local is never one, and `@f` is read as `f`.
    pub(super) fn rewrite_rule_equations(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<(Name, Vec<Name>)>, NatDefinitionElabError> {
        let ident = match syntax {
            Syntax::Ident { .. } => syntax,
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(&["Term", "explicit"]) && args.len() == 2 =>
            {
                &args[1]
            }
            _ => return Ok(None),
        };
        let Syntax::Ident { val, .. } = ident else {
            return Ok(None);
        };
        if self.txn.lctx.find_by_user_name(val).is_some() {
            return Ok(None);
        }
        let Ok(Some(resolved)) = self.resolve_source_candidates(val)? else {
            return Ok(None);
        };
        if self.txn.lctx.find_by_user_name(&resolved).is_some()
            || self.defining.as_ref() == Some(&resolved)
            || self.recursion.as_ref().is_some_and(|r| r.name == resolved)
        {
            return Ok(None);
        }
        let Some(definition) = safe_definition(&self.txn.env, &resolved).cloned() else {
            return Ok(None);
        };
        if is_matcher_name(&resolved) || self.proposition_typed(&definition)? {
            return Ok(None);
        }
        let equations = generated_equations(&self.txn.env, &resolved);
        if equations.is_empty() {
            return Err(self.missing_equation_theorem(&equation_name(&resolved, 1))?);
        }
        Ok(Some((resolved, equations)))
    }
}

/// What a source reference to an equation-like name needs before it resolves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Request {
    /// `f.eq_<n>`, `f.eq_def` or `f.eq_unfold`, by its full name.
    Name(Name),
    /// All of `f`'s equations, as `rw [f]` asks (`getEqnsFor?`).
    Equations(Name),
}

fn equation_like_leaf(name: &Name) -> bool {
    matches!(name.leaf_view(), LeafView::Str(leaf)
        if leaf == "eq_def"
            || leaf == "eq_unfold"
            || leaf.strip_prefix("eq_").is_some_and(is_nat))
}

/// The equation theorems `syntax` refers to that are not generated yet, in source order: each
/// identifier that resolves in `scope` to an equation-like name of a definition, and each
/// `rw [f]`/`rewrite [f]` rule naming a definition. The pin generates them when it resolves
/// the name (its reserved-name action); a reference later elaborated as a local still asks
/// here, so this may ask for more than the pin generates, never less.
pub fn requests(
    syntaxes: &[&Syntax],
    env: &Environment,
    scope: &SourceScope,
    kernel: Budget,
) -> Result<Vec<Request>, NatDefinitionElabError> {
    let mut context = Context::scoped(env, kernel, scope);
    let declaration_id = parser_kind(&["Command", "declId"]);
    let rewrite_rule = parser_kind(&["Tactic", "rwRule"]);
    let explicit = parser_kind(&["Term", "explicit"]);
    let mut found: Vec<Request> = Vec::new();
    let mut pending: Vec<&Syntax> = syntaxes.iter().rev().copied().collect();
    while let Some(syntax) = pending.pop() {
        context.tick()?;
        match syntax {
            Syntax::Ident { val, .. } if equation_like_leaf(val) => {
                if let Ok(Some(resolved)) = context.resolve_source_candidates(val)?
                    && !env.contains(&resolved)
                    && target(env, &resolved).is_some()
                {
                    found.push(Request::Name(resolved));
                }
            }
            Syntax::Node { kind, .. } if kind == &declaration_id => {}
            Syntax::Node { kind, args, .. } => {
                if kind == &rewrite_rule
                    && let [_, term] = args.as_slice()
                {
                    let ident = match term {
                        Syntax::Node { kind, args, .. } if kind == &explicit && args.len() == 2 => {
                            &args[1]
                        }
                        _ => term,
                    };
                    if let Syntax::Ident { val, .. } = ident
                        && let Ok(Some(resolved)) = context.resolve_source_candidates(val)?
                        && safe_definition(env, &resolved).is_some()
                        && !is_matcher_name(&resolved)
                        && !equations_generated(env, &resolved)
                    {
                        found.push(Request::Equations(resolved));
                    }
                }
                pending.extend(args.iter().rev());
            }
            _ => {}
        }
    }
    let mut unique = Vec::new();
    for request in found {
        if !unique.contains(&request) {
            unique.push(request);
        }
    }
    Ok(unique)
}

/// The declarations to admit, in order, so that what `request` asks for exists: the pin's
/// realization of the reserved name. Nothing for a name already generated, a definition whose
/// type is a proposition (the pin generates no equations for it) or a name no definition
/// reserves; a refusal for a definition this engine does not generate equations for.
pub fn realize(
    env: &Environment,
    request: &Request,
    kernel: Budget,
) -> Result<Vec<Declaration>, NatDefinitionElabError> {
    let (declaration, suffix, name) = match request {
        Request::Name(name) => match target(env, name) {
            Some((declaration, suffix)) => (declaration, suffix, name.clone()),
            None => return Ok(Vec::new()),
        },
        Request::Equations(declaration) => (
            declaration.clone(),
            Suffix::Equation,
            equation_name(declaration, 1),
        ),
    };
    let Some(definition) = safe_definition(env, &declaration).cloned() else {
        return Ok(Vec::new());
    };
    if is_matcher_name(&declaration) {
        return Ok(Vec::new());
    }
    let unfold_name = Name::str(declaration.clone(), "eq_def");
    let const_unfold_name = Name::str(declaration.clone(), "eq_unfold");
    let done = match suffix {
        Suffix::Equation => equations_generated(env, &declaration),
        Suffix::Def => env.contains(&unfold_name),
        Suffix::Unfold => env.contains(&const_unfold_name),
    };
    if done {
        return Ok(Vec::new());
    }
    let mut context = Context::new(env, kernel);
    if context.proposition_typed(&definition)? {
        return Ok(Vec::new());
    }
    if let Some(mut reason) = unsupported_reason(env, &declaration, &definition.value) {
        // A definition by pattern matching, non-recursive or structural: its equations from
        // its recorded `match`.
        let well_founded = mentions_well_founded(&definition.value);
        if matches!(reason, Unsupported::CompiledMatch | Unsupported::Recursive) && well_founded {
            reason = Unsupported::WellFounded;
        }
        if matches!(reason, Unsupported::CompiledMatch | Unsupported::Recursive) {
            match journal::find(env, &declaration)? {
                Some(record) if suffix == Suffix::Equation => {
                    return context.matched_equations(&definition, &record);
                }
                Some(_) => reason = Unsupported::MatchInStatement,
                None if reason == Unsupported::CompiledMatch => {
                    reason = Unsupported::UnrecordedMatch;
                }
                None => {}
            }
        }
        return Err(failure(SourceInferenceError::EquationTheorem(Box::new(
            NotGenerated {
                name,
                declaration,
                reason,
            },
        ))));
    }
    Ok(match suffix {
        Suffix::Equation => vec![context.simple_equation(&definition)?],
        Suffix::Def => vec![context.simple_unfold(&definition)?],
        Suffix::Unfold => {
            let mut declarations = Vec::new();
            let unfold = match env.find(&unfold_name) {
                Some(info) => info.constant_val().type_.clone(),
                None => {
                    let declaration = context.simple_unfold(&definition)?;
                    let Declaration::Thm(theorem) = &declaration else {
                        unreachable!("an unfolding theorem")
                    };
                    let type_ = theorem.base.type_.clone();
                    declarations.push(declaration);
                    type_
                }
            };
            declarations.push(context.const_unfold(&definition, &unfold)?);
            declarations
        }
    })
}

/// Whether `rw [f]` asks for `f`'s equations: a safe definition whose type is not a
/// proposition (`getEqnsFor?`'s `shouldGenerateEqnThms`).
pub fn has_equations(
    env: &Environment,
    declaration: &Name,
    kernel: Budget,
) -> Result<bool, NatDefinitionElabError> {
    let Some(definition) = safe_definition(env, declaration).cloned() else {
        return Ok(false);
    };
    if is_matcher_name(declaration) {
        return Ok(false);
    }
    let mut context = Context::new(env, kernel);
    Ok(!context.proposition_typed(&definition)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equation_like_suffixes_follow_the_pins_reserved_names() {
        for (text, expected) in [
            ("eq_1", true),
            ("eq_12", true),
            ("eq_1_0", true),
            ("eq_def", true),
            ("eq_unfold", true),
            ("eq_", false),
            ("eq_x", false),
            ("eq", false),
            ("eq_1_", false),
        ] {
            let suffix = match text {
                "eq_def" | "eq_unfold" => true,
                _ => text.strip_prefix("eq_").is_some_and(is_nat),
            };
            assert_eq!(suffix, expected, "{text}");
        }
        assert!(is_matcher_name(&Name::from_components(["f", "match_1"])));
        assert!(!is_matcher_name(&Name::from_components(["f", "match_"])));
        assert!(!is_matcher_name(&Name::from_components(["f", "matcher"])));
    }
}
