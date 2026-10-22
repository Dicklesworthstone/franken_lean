//! `#print` (vendored `Lean/Elab/Print.lean`): the header, value and inductive forms, and
//! `#print axioms` (vendored `Lean/Util/CollectAxioms.lean`).
//!
//! Only constants this source declared get a header. An imported constant may carry tags this
//! door does not decode from its `.olean` (`defeq`, `backward_defeq` and `meta` mark thousands
//! of `Init` constants), and a header without them would be text the pin does not print. A
//! structure, a recursor and anything the term printer refuses are refused here too.
use super::*;
use fln_elab::reducibility::{Reducibility, ReducibilityTable};

/// Whether `value` shows how this engine compiles a `match` or a recursive definition, which
/// the pin's value does not: its matchers, `brecOn` and `WellFounded.fix` print as `match`
/// and recursion where this door would print recursors and elaboration's own binders. Those
/// binders are named `_fln_…` or by a number; a recursor is one too in a definition's value
/// (`recursors`), while a theorem's proof may reach it as the pin's would, by `induction`.
fn compiled_artifact(env: &Environment, value: &Expr, recursors: bool) -> bool {
    let internal = internal_name;
    let mut pending = vec![value];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name, .. } => {
                if internal(name)
                    || (recursors && matches!(env.find(name), Some(ConstantInfo::Rec(_))))
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

impl<'a> Printer<'a> {
    /// `#print c` (`signature_only` false) or `#print sig c` (true) for a constant this
    /// source declared (`printIdCore`, vendored `Lean/Elab/Print.lean:198-217`).
    pub fn print_constant(&mut self, name: &Name, signature_only: bool) -> Printed {
        let Some(info) = self.env.find(name) else {
            return Err(Unsupported("a name that is not a constant"));
        };
        let doc = match info {
            ConstantInfo::Axiom(v) => {
                self.print_header(name, "axiom", unsafe_word(v.is_unsafe), true)?
            }
            ConstantInfo::Defn(v) => {
                let safety = match v.safety {
                    DefinitionSafety::Safe => "",
                    DefinitionSafety::Unsafe => "unsafe ",
                    DefinitionSafety::Partial => "partial ",
                };
                self.print_def_like(name, "def", safety, &v.value, signature_only)?
            }
            ConstantInfo::Thm(v) => {
                // Generated equation theorems carry `defeq`/`backward_defeq` at the pin
                // (`inferDefEqAttr`), which this door does not record.
                if generated_equation(name) {
                    return Err(Unsupported("a generated equation theorem's attributes"));
                }
                self.print_def_like(name, "theorem", "", &v.value, signature_only)?
            }
            ConstantInfo::Opaque(v) => {
                self.print_header(name, "opaque", unsafe_word(v.is_unsafe), true)?
            }
            ConstantInfo::Quot(_) => self.print_header(name, "Quotient primitive", "", true)?,
            ConstantInfo::Ctor(v) => {
                self.print_header(name, "constructor", unsafe_word(v.is_unsafe), true)?
            }
            ConstantInfo::Rec(_) => return Err(Unsupported("a recursor's rules")),
            // `printIdCore` prints an inductive in full under `#print sig` too.
            ConstantInfo::Induct(v) => self.print_inductive(name, v)?,
        };
        Ok(doc.pretty(WIDTH))
    }

    /// `printDefLike` (vendored `Lean/Elab/Print.lean:77-83`): the header, then ` :=`, a line
    /// and the value.
    fn print_def_like(
        &mut self,
        name: &Name,
        kind: &str,
        safety: &str,
        value: &Expr,
        signature_only: bool,
    ) -> Doc {
        let header = self.print_header(name, kind, safety, true)?;
        if signature_only {
            return Ok(header);
        }
        if compiled_artifact(self.env, value, kind == "def") {
            return Err(Unsupported("a compiled `match` or recursion"));
        }
        // The pin's `letToHaveValue` cleans a safe definition's value unless its type is a
        // proposition; a theorem's it leaves alone.
        let lets = match kind {
            "def" if safety.is_empty() => match self.proposition(name) {
                Some(false) => LetMode::ToHave,
                Some(true) => LetMode::AsIs,
                None => LetMode::Refuse,
            },
            "def" => LetMode::Refuse,
            _ => LetMode::AsIs,
        };
        let outer = std::mem::replace(&mut self.lets, lets);
        let value = self.doc(value, 0);
        self.lets = outer;
        Ok(header
            .then(Format::text(" :="))
            .then(Format::Line)
            .then(value?))
    }

    /// Whether `name`'s type is a proposition: its result is an application of a constant
    /// whose own type ends in `Prop` (`Some(true)`) or in a nonzero sort (`Some(false)`); a
    /// sort is never one. `None` when that cannot be read off the types.
    fn proposition(&self, name: &Name) -> Option<bool> {
        fn result(mut expr: &Expr) -> &Expr {
            while let ExprNode::ForallE { body, .. } = expr.node() {
                expr = body;
            }
            expr
        }
        let type_ = result(&self.env.find(name)?.constant_val().type_);
        let (head, _) = spine(type_);
        match head.node() {
            ExprNode::Sort { .. } => Some(false),
            ExprNode::Const { name, .. } => {
                match result(&self.env.find(name)?.constant_val().type_).node() {
                    ExprNode::Sort { level } if level.is_zero() => Some(true),
                    ExprNode::Sort { level } if level.is_never_zero() => Some(false),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `printInduct` (vendored `Lean/Elab/Print.lean:88-96`): the header, the number of
    /// parameters, and each constructor by its whole name with its type.
    fn print_inductive(&mut self, name: &Name, value: &InductiveVal) -> Doc {
        if self.structure_like(value) {
            return Err(Unsupported("a structure"));
        }
        let mut doc = self
            .print_header(name, "inductive", unsafe_word(value.is_unsafe), true)?
            .then(Format::Line)
            .then(Format::text(format!(
                "number of parameters: {}",
                value.num_params
            )))
            .then(Format::Line)
            .then(Format::text("constructors:"));
        for ctor in &value.ctors {
            let Some(info) = self.env.find(ctor) else {
                return Err(Unsupported("a constructor that is not a constant"));
            };
            // `ctor ++ " : "`: a `Name` as `MessageData.ofName` shows it, in full.
            if ctor.to_display_string().starts_with("_private") {
                return Err(Unsupported("a private constructor's name"));
            }
            let type_ = self.doc(&info.constant_val().type_, 0)?;
            doc = doc
                .then(Format::Line)
                .then(Format::text(format!("{} : ", escaped_name(ctor))))
                .then(type_);
        }
        Ok(doc)
    }

    /// Whether `value` may be a structure, which `#print` prints with its fields
    /// (`printStructure`). This door keeps no record of which inductives the `structure`
    /// command made, so one constructor and no indices with either no fields or a projection
    /// function for its first field is treated as one.
    pub(super) fn structure_like(&self, value: &InductiveVal) -> bool {
        let [ctor] = value.ctors.as_slice() else {
            return false;
        };
        if value.num_indices != 0 {
            return false;
        }
        let Some(info) = self.env.find(ctor) else {
            return true;
        };
        let mut type_ = &info.constant_val().type_;
        for _ in 0..value.num_params {
            match type_.node() {
                ExprNode::ForallE { body, .. } => type_ = body,
                _ => return true,
            }
        }
        let ExprNode::ForallE { binder_name, .. } = type_.node() else {
            return true;
        };
        let projection = value.base.name.append_core(binder_name);
        self.env.find(&projection).is_some()
    }

    /// `mkHeader` (vendored `Lean/Elab/Print.lean:26-68`) for a constant this source declared:
    /// its reducibility attribute, `unsafe` or `partial`, `private`, `protected`, then
    /// `kind name.{u, …} : type`. The `expose`, `defeq`, `backward_defeq` and `meta` markers
    /// never arise: this door admits no source declaration that carries them.
    fn print_header(&mut self, name: &Name, kind: &str, safety: &str, signature: bool) -> Doc {
        let mut attributes = Vec::new();
        let mut status = ReducibilityTable::effective(self.env)
            .map_err(|_| Unsupported("an unreadable reducibility journal"))?
            .get(name);
        // `abbrev` is `@[reducible]` at the pin (`mkDefViewOfAbbrev`); here its status is
        // carried by the definition's `abbrev` hint rather than the journal.
        if status.is_none()
            && matches!(self.env.find(name), Some(ConstantInfo::Defn(v))
                if v.hints == ReducibilityHints::Abbrev)
        {
            status = Some(Reducibility::Reducible);
        }
        match status {
            Some(Reducibility::Reducible) => attributes.push("reducible"),
            Some(Reducibility::Irreducible) => attributes.push("irreducible"),
            Some(Reducibility::ImplicitReducible) => attributes.push("implicit_reducible"),
            Some(Reducibility::Semireducible) | None => {}
        }
        if self.env.find(name).is_some_and(rfl_bodied) {
            attributes.push("defeq");
        }
        let mut head = String::new();
        if !attributes.is_empty() {
            head.push_str(&format!("@[{}] ", attributes.join(", ")));
        }
        head.push_str(safety);
        // `privateToUserName?`: a private name prints its source spelling after `private`.
        let shown = self
            .scope
            .map_or_else(|| name.clone(), |scope| scope.user_name(name));
        if &shown != name {
            head.push_str("private ");
        } else if name.to_display_string().starts_with("_private") {
            return Err(Unsupported("a private name of another module"));
        }
        let protected = fln_elab::protected_names::ProtectedNames::read(self.env)
            .map_err(|_| Unsupported("an unreadable protected-names journal"))?;
        if protected.contains(name) {
            head.push_str("protected ");
        }
        head.push_str(kind);
        if !signature {
            return Ok(Format::text(head));
        }
        let Some(info) = self.env.find(name) else {
            return Err(Unsupported("a name that is not a constant"));
        };
        head.push(' ');
        head.push_str(&escaped_name(&shown));
        let parameters = &info.constant_val().level_params;
        if !parameters.is_empty() {
            head.push_str(".{");
            head.push_str(
                &parameters
                    .iter()
                    .map(escaped_name)
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            head.push('}');
        }
        head.push_str(" : ");
        let type_ = self.doc(&info.constant_val().type_, 0)?;
        Ok(Format::text(head).then(type_))
    }

    /// `#print axioms c` (vendored `Lean/Elab/Print.lean:239-244`): the axioms `c` reaches
    /// through types, values and constructors, sorted by `Name.lt`.
    pub fn print_axioms(&self, name: &Name) -> Printed {
        let axioms = collect_axioms(self.env, name, 4_000_000).ok_or(Unsupported(
            "an axiom closure larger than this door's budget",
        ))?;
        let shown = self.display_name(name);
        Ok(if axioms.is_empty() {
            format!("'{shown}' does not depend on any axioms")
        } else {
            let names = axioms
                .iter()
                .map(|axiom| self.display_name(axiom))
                .collect::<Vec<_>>();
            format!("'{shown}' depends on axioms: [{}]", names.join(", "))
        })
    }
}

/// Whether a definition or theorem's value is `rfl` under its binders. The pin tags a
/// declaration whose body is the syntax `:= rfl` with `@[defeq]` (`elabMutualDef`, vendored
/// `Lean/Elab/MutualDef.lean:1531`); the syntax is gone here, and `@rfl _ _` is what it
/// elaborates to. A body written `:= (rfl)` or `:= @rfl _ _` elaborates the same and is not
/// tagged by the pin, so it is mis-shown as `@[defeq]`.
fn rfl_bodied(info: &ConstantInfo) -> bool {
    let mut value = match info {
        ConstantInfo::Defn(v) => &v.value,
        ConstantInfo::Thm(v) => &v.value,
        _ => return false,
    };
    while let ExprNode::Lam { body, .. } = value.node() {
        value = body;
    }
    let ExprNode::App { f, .. } = value.node() else {
        return false;
    };
    let ExprNode::App { f, .. } = f.node() else {
        return false;
    };
    matches!(f.node(), ExprNode::Const { name, .. } if name.to_display_string() == "rfl")
}

fn unsafe_word(is_unsafe: bool) -> &'static str {
    if is_unsafe { "unsafe " } else { "" }
}

/// The names the pin's equation generators give the theorems `inferDefEqAttr` tags:
/// `f.eq_1`, `f.eq_def`, `f.eq_unfold`.
fn generated_equation(name: &Name) -> bool {
    match name.leaf_view() {
        LeafView::Str(leaf) => {
            leaf == "eq_def"
                || leaf == "eq_unfold"
                || leaf
                    .strip_prefix("eq_")
                    .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
        }
        _ => false,
    }
}

/// `CollectAxioms.collect` (vendored `Lean/Util/CollectAxioms.lean:39-74`): every constant
/// reached through a type, a value (definitions, theorems, opaques) or an inductive's
/// constructors, keeping the axioms. `None` when more than `budget` term nodes would be
/// visited. Sorted by the pin's `Name.lt`.
fn collect_axioms(env: &Environment, root: &Name, budget: usize) -> Option<Vec<Name>> {
    let mut seen_constants = std::collections::BTreeSet::new();
    let mut seen_terms = std::collections::HashSet::new();
    let mut pending_constants = vec![root.clone()];
    let mut axioms = Vec::new();
    let mut visits = 0_usize;
    while let Some(constant) = pending_constants.pop() {
        if !seen_constants.insert(constant.clone()) {
            continue;
        }
        let Some(info) = env.find(&constant) else {
            continue;
        };
        let mut terms: Vec<&Expr> = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Axiom(_) => axioms.push(constant.clone()),
            ConstantInfo::Defn(v) => terms.push(&v.value),
            ConstantInfo::Thm(v) => terms.push(&v.value),
            ConstantInfo::Opaque(v) => terms.push(&v.value),
            ConstantInfo::Quot(_) => terms.clear(),
            ConstantInfo::Induct(v) => pending_constants.extend(v.ctors.iter().cloned()),
            ConstantInfo::Ctor(_) | ConstantInfo::Rec(_) => {}
        }
        let mut stack: Vec<Expr> = terms.into_iter().cloned().collect();
        while let Some(term) = stack.pop() {
            visits += 1;
            if visits > budget {
                return None;
            }
            if !seen_terms.insert(term.clone()) {
                continue;
            }
            match term.node() {
                ExprNode::Const { name, .. } => pending_constants.push(name.clone()),
                ExprNode::App { f, a } => {
                    stack.push(f.clone());
                    stack.push(a.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push(binder_type.clone());
                    stack.push(body.clone());
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push(type_.clone());
                    stack.push(value.clone());
                    stack.push(body.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    stack.push(expr.clone());
                }
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Lit { .. } => {}
            }
        }
    }
    axioms.sort_by(name_cmp);
    Some(axioms)
}

/// The pin's `Name.cmp` (vendored `Lean/Data/Name.lean:67-80`): the anonymous name least, a
/// numeric last component before a string one whatever their prefixes, and otherwise the
/// prefixes first, then the components (strings by code point).
fn name_cmp(left: &Name, right: &Name) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (left.leaf_view(), right.leaf_view()) {
        (LeafView::Anonymous, LeafView::Anonymous) => Ordering::Equal,
        (LeafView::Anonymous, _) => Ordering::Less,
        (_, LeafView::Anonymous) => Ordering::Greater,
        (LeafView::Num(a), LeafView::Num(b)) => {
            name_cmp(&left.parent(), &right.parent()).then_with(|| a.cmp(&b))
        }
        (LeafView::Num(_), LeafView::Str(_)) => Ordering::Less,
        (LeafView::Str(_), LeafView::Num(_)) => Ordering::Greater,
        (LeafView::Str(a), LeafView::Str(b)) => {
            name_cmp(&left.parent(), &right.parent()).then_with(|| a.cmp(b))
        }
    }
}
