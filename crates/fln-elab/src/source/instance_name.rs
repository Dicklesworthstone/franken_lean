//! Generated names for anonymous instances: the pin's `Lean.Elab.Command.NameGen`
//! (`Lean/Elab/DeclNameGen.lean`), `mkInstanceName` = `mkBaseNameWithSuffix' "inst"`.
//!
//! The instance's binders and type are elaborated first; the type is then "winnowed"
//! (`winnowExpr`: proofs, implicit non-type arguments and universes dropped), rendered by
//! `mkBaseNameCore` (each constant's last component, capitalized; `Forall`, `Prop`,
//! `Type`, `Sort`; a repeated subexpression only once), with each top-level binder whose
//! rendering is nonempty appended as `Of…` (`mkBaseNameAux`). The current namespace's
//! constant prefixes count as already seen (`visitNamespace`). `mkUnusedBaseName` then
//! appends `_1`, `_2`, … while the name is taken.
//!
//! One part of the pin's rule is not reproduced: when no constant in the type belongs to
//! the current module or project, the pin appends the main module as a suffix
//! (`instInhabitedNat_main`). The elaborator does not know the module's name, so such an
//! instance gets the unsuffixed base name (made unused as above) instead.
use super::*;
use std::collections::HashSet;

/// `winnowExpr`'s output, kept as the structure the renderer needs rather than as `Expr`.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Winnowed {
    Const(Name),
    App(Box<Winnowed>, Box<Winnowed>),
    Forall(Box<Winnowed>, Box<Winnowed>),
    Prop,
    Type,
    Sort,
    /// The pin's `.bvar 0`: anything not mentioned.
    Hidden,
}

/// `str.capitalize`: the first character upper-cased.
fn capitalize(text: &str) -> String {
    let mut chars = text.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

#[derive(Default)]
struct Render {
    seen: HashSet<Winnowed>,
}

impl Render {
    /// `mkBaseNameCore.visit`.
    fn core(&mut self, e: &Winnowed, omit_top_forall: bool) -> String {
        if self.seen.contains(e) {
            return String::new();
        }
        let rendered = match e {
            Winnowed::Const(name) => match name.leaf_view() {
                LeafView::Str(text) => capitalize(text),
                _ => String::new(),
            },
            Winnowed::App(f, x) => {
                let mut s = self.core(f, false);
                s.push_str(&self.core(x, false));
                s
            }
            Winnowed::Forall(ty, body) => {
                let sty = self.core(ty, false);
                if omit_top_forall && sty.is_empty() {
                    self.core(body, true)
                } else {
                    let rest = self.core(body, false);
                    format!("Forall{sty}{rest}")
                }
            }
            Winnowed::Prop => "Prop".to_owned(),
            Winnowed::Type => "Type".to_owned(),
            Winnowed::Sort => "Sort".to_owned(),
            Winnowed::Hidden => String::new(),
        };
        self.seen.insert(e.clone());
        rendered
    }

    /// `mkBaseNameAux`: the body first, then each top-level binder as `Of…`.
    fn aux(&mut self, binders: &[Winnowed], body: &Winnowed) -> String {
        let base = self.core(body, false);
        let mut foralls = Vec::new();
        for binder in binders.iter().rev() {
            let rendered = self.core(binder, true);
            if !rendered.is_empty() {
                foralls.push(format!("Of{rendered}"));
            }
        }
        foralls.reverse();
        base + &foralls.concat()
    }
}

impl Context {
    /// The pin's generated name for an anonymous instance whose parameters are
    /// `parameters` (already in the local context) and whose type is `expected`, in the
    /// current namespace and not yet taken in the environment.
    pub(super) fn generated_instance_name(
        &mut self,
        parameters: &[LocalDecl],
        expected: &Expr,
    ) -> Result<Name, NatDefinitionElabError> {
        let expected = self.instantiate(expected)?;
        let mut types = Vec::with_capacity(parameters.len());
        for parameter in parameters {
            types.push(self.instantiate(&parameter.type_)?);
        }
        // A binder whose local the rest of the type mentions is not named (`hasLooseBVars`).
        let mut binders = Vec::with_capacity(parameters.len());
        for (index, parameter) in parameters.iter().enumerate() {
            let id = &parameter.id;
            let mentioned = types[index + 1..]
                .iter()
                .chain(std::iter::once(&expected))
                .any(|later| {
                    later
                        .abstract_fvar(id, 0)
                        .map_or(true, |closed| &closed != later)
                });
            binders.push(if mentioned {
                Winnowed::Hidden
            } else {
                self.winnow(&types[index])?
            });
        }
        let body = self.winnow(&expected)?;
        let mut render = Render::default();
        // `visitNamespace`: the namespace's constant prefixes are already "said".
        let mut namespace = self.source_scope.namespace.clone();
        while !namespace.is_anonymous() {
            if self.txn.env.contains(&namespace) {
                render.seen.insert(Winnowed::Const(namespace.clone()));
            }
            namespace = namespace.parent();
        }
        let base = format!("inst{}", render.aux(&binders, &body));
        // `mkUnusedBaseName`: the pin's Macro.hasDecl adapter checks both the
        // public name and the current module's private name (Elab/Util.lean).
        // Anonymous and derived instances bypass enter_declaration, so this
        // path must also apply the file's private-by-default visibility.
        let namespace = self.source_scope.namespace.clone();
        let candidate = |suffix: Option<usize>| {
            let text = match suffix {
                None => base.clone(),
                Some(n) => format!("{base}_{n}"),
            };
            Name::str(namespace.clone(), text)
        };
        let mut user_name = candidate(None);
        let mut name = self.source_scope.visible_name(&user_name);
        let mut next = 1;
        while self.txn.env.contains(&user_name)
            || self
                .txn
                .env
                .contains(&self.source_scope.private_name(&user_name))
        {
            self.tick()?;
            user_name = candidate(Some(next));
            name = self.source_scope.visible_name(&user_name);
            next += 1;
        }
        Ok(name)
    }

    /// Whether `e`'s type is a proposition (`isProof`). Unknown types are not proofs.
    fn is_proof(&mut self, e: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(e)? else {
            return Ok(false);
        };
        let Some(sort) = self.known_type(&type_)? else {
            return Ok(false);
        };
        let sort = self.whnf(&sort)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.is_zero()))
    }

    /// Whether `e` is a type former (`isTypeFormer`): its type is `∀ …, Sort u`.
    fn is_type_former(&mut self, e: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(mut type_) = self.known_type(e)? else {
            return Ok(false);
        };
        loop {
            self.tick()?;
            type_ = self.whnf(&type_)?;
            match type_.node() {
                ExprNode::Sort { .. } => return Ok(true),
                ExprNode::ForallE { body, .. } => type_ = body.clone(),
                _ => return Ok(false),
            }
        }
    }

    /// `winnowExpr`, over a type whose locals are in the current context. Bound
    /// variables are opened only as far as their binder needs: a body under a binder is
    /// rendered with the bound variable hidden, which renders exactly as the pin's local.
    fn winnow(&mut self, e: &Expr) -> Result<Winnowed, NatDefinitionElabError> {
        self.tick()?;
        if !e.has_loose_bvars() && self.is_proof(e)? {
            return Ok(Winnowed::Hidden);
        }
        Ok(match e.node() {
            ExprNode::App { .. } => {
                let (head, args) = operators::spine(e);
                let mut result = self.winnow(&head)?;
                // Binder information of the head's type, argument by argument.
                let mut head_type = if head.has_loose_bvars() {
                    None
                } else {
                    self.known_type(&head)?
                };
                for arg in &args {
                    let mut explicit = true;
                    if let Some(type_) = head_type.take() {
                        let type_ = self.whnf(&type_)?;
                        if let ExprNode::ForallE {
                            body, binder_info, ..
                        } = type_.node()
                        {
                            explicit = *binder_info == BinderInfo::Default;
                            head_type = Some(self.substitute(body, arg)?);
                        }
                    }
                    let closed = !arg.has_loose_bvars();
                    let mentioned = explicit
                        || (closed
                            && !matches!(arg.node(), ExprNode::Sort { .. })
                            && self.is_type_former(arg)?);
                    if mentioned && !(closed && self.is_proof(arg)?) {
                        result = Winnowed::App(Box::new(result), Box::new(self.winnow(arg)?));
                    }
                }
                result
            }
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let domain = if body.has_loose_bvar(0) {
                    Winnowed::Hidden
                } else {
                    self.winnow(binder_type)?
                };
                Winnowed::Forall(Box::new(domain), Box::new(self.winnow(body)?))
            }
            ExprNode::Lam { body, .. } => self.winnow(body)?,
            ExprNode::LetE { value, body, .. } => {
                let body = self.substitute(body, value)?;
                self.winnow(&body)?
            }
            ExprNode::Sort { level } => {
                if level.is_zero() {
                    Winnowed::Prop
                } else if *level == Level::one() {
                    Winnowed::Type
                } else {
                    Winnowed::Sort
                }
            }
            ExprNode::Const { name, .. } => Winnowed::Const(name.clone()),
            ExprNode::MData { expr, .. } => self.winnow(expr)?,
            _ => Winnowed::Hidden,
        })
    }
}
