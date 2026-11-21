//! `#print` (vendored `Lean/Elab/Print.lean`): the header, value and inductive forms, and
//! `#print axioms` (vendored `Lean/Util/CollectAxioms.lean`).
//!
//! Only constants this source declared get a header. An imported constant may carry tags this
//! door does not decode from its `.olean` (`defeq`, `backward_defeq` and `meta` mark thousands
//! of `Init` constants), and a header without them would be text the pin does not print. A
//! structure, a recursor and anything the term printer refuses are refused here too.
use super::*;
use fln_elab::instances::InstanceRegistry;
use fln_elab::records::RecordBudget;
use fln_elab::records::defaults::RecordDefaults;
use fln_elab::records::imported::ImportedStructures;
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
            return self.print_structure(name, value);
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

    /// `printStructure` (vendored `Lean/Elab/Print.lean:125-196`): header with signature,
    /// parameter count, parents, flattened fields with origin projections, constructor
    /// signature, and relaxed-C3 field notation resolution order. Fails closed (`Unsupported`)
    /// when structure metadata is absent or a field carries a default/autoParam this printer
    /// does not yet format.
    fn print_structure(&mut self, name: &Name, value: &InductiveVal) -> Doc {
        let structures = ImportedStructures::read(self.env)
            .map_err(|_| Unsupported("an unreadable structure journal"))?;
        let Some(entry) = structures.get(name) else {
            return Err(Unsupported("a structure"));
        };
        let [ctor] = value.ctors.as_slice() else {
            return Err(Unsupported("a structure"));
        };
        let Some(ConstantInfo::Ctor(ctor_info)) = self.env.find(ctor) else {
            return Err(Unsupported("a structure without its constructor"));
        };
        let instances = InstanceRegistry::read(self.env)
            .map_err(|_| Unsupported("an unreadable instance registry"))?;
        let defaults = RecordDefaults::read(self.env)
            .map_err(|_| Unsupported("an unreadable record defaults journal"))?;
        let flat_ctor_name = Name::str(ctor.clone(), "_flat_ctor");
        if let Some(ConstantInfo::Defn(flat_ctor)) = self.env.find(&flat_ctor_name) {
            let mut cursor = &flat_ctor.base.type_;
            for index in 0..u64::from(value.num_params) + 1024 {
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = cursor.node()
                else {
                    break;
                };
                if index >= u64::from(value.num_params)
                    && annotation(binder_type, "autoParam").is_some()
                {
                    return Err(Unsupported("a structure with an autoParam field"));
                }
                cursor = body;
            }
        }
        let kind = if instances.is_class(name) {
            "class"
        } else {
            "structure"
        };
        let header = self.print_header(name, kind, unsafe_word(value.is_unsafe), false)?;
        let sig = self.signature(name, &value.base.type_)?;
        let mut doc = header
            .then(Format::text(" "))
            .then(Format::text(sig))
            .then(Format::Line)
            .then(Format::text(format!(
                "number of parameters: {}",
                value.num_params
            )));

        let num_params = usize::try_from(value.num_params)
            .map_err(|_| Unsupported("a structure with too many parameters"))?;
        let levels: Vec<Level> = value
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let depth = self.names.len();
        let mut cursor = &value.base.type_;
        for _ in 0..num_params {
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = cursor.node()
            else {
                self.unbind_to(depth);
                return Err(Unsupported("a structure with an unexpected telescope"));
            };
            let shown = self.parameter_name(binder_name);
            self.bind(shown, binder_type);
            cursor = body;
        }
        let mut self_type = Expr::const_(name.clone(), levels.clone());
        let mut param_exprs = Vec::with_capacity(num_params);
        for index in 0..num_params {
            // `self` will be bound at BVar(0), so parameter `index` sits at `num_params - index`.
            let bvar = Expr::bvar((num_params - index) as u32)
                .map_err(|_| Unsupported("a structure with too many parameters"))?;
            let ty_bvar = Expr::bvar((num_params - 1 - index) as u32)
                .map_err(|_| Unsupported("a structure with too many parameters"))?;
            self_type = Expr::app(self_type, ty_bvar);
            param_exprs.push(bvar);
        }
        self.bind("self".to_owned(), &self_type);
        let self_expr = Expr::bvar(0).map_err(|_| Unsupported("bound variable out of range"))?;

        let body_result = (|| -> Result<Format, Unsupported> {
            let mut body_doc = Format::Nil;
            if !entry.parents.is_empty() {
                let mut parents_doc = Format::Nil;
                let mut proj_args = param_exprs.clone();
                proj_args.push(self_expr.clone());
                for parent in &entry.parents {
                    let ptype = self.application_type(&parent.projection, &levels, &proj_args)?;
                    let ptype_doc = self.doc(&ptype, 0)?;
                    parents_doc = parents_doc.then(
                        Format::Line
                            .then(Format::text(format!(
                                "{} : ",
                                self.full_name(&parent.projection)
                            )))
                            .then(ptype_doc)
                            .nest(2),
                    );
                }
                body_doc = body_doc
                    .then(Format::Line)
                    .then(Format::text("parents:"))
                    .then(parents_doc);
            }

            let mut flattened = Vec::new();
            let mut seen_fields = std::collections::HashSet::new();
            self.collect_structure_print_fields(
                &structures,
                name,
                name,
                &levels,
                &param_exprs,
                &self_expr,
                &defaults,
                &mut seen_fields,
                &mut flattened,
                0,
            )?;
            if flattened.is_empty() {
                body_doc = body_doc
                    .then(Format::Line)
                    .then(Format::text("fields: (none)"));
            } else {
                let mut fields_doc = Format::Nil;
                for (origin_proj, ftype) in flattened {
                    let modifier = if is_private(&origin_proj) {
                        if self.pp.private_names {
                            return Err(Unsupported("a private field under `pp.privateNames`"));
                        }
                        "private "
                    } else {
                        ""
                    };
                    let ftype_doc = self.doc(&ftype, 0)?;
                    fields_doc = fields_doc.then(
                        Format::Line
                            .then(Format::text(format!(
                                "{modifier}{} : ",
                                self.full_name(&origin_proj)
                            )))
                            .then(ftype_doc.nest(2))
                            .nest(2),
                    );
                }
                body_doc = body_doc
                    .then(Format::Line)
                    .then(Format::text("fields:"))
                    .then(fields_doc);
            }
            Ok(body_doc)
        })();
        self.unbind_to(depth);
        doc = doc.then(body_result?);

        let ctor_modifier = if is_private(ctor) {
            if self.pp.private_names {
                return Err(Unsupported("a private constructor under `pp.privateNames`"));
            }
            "private "
        } else {
            ""
        };
        let ctor_sig = self.signature(ctor, &ctor_info.base.type_)?;
        doc = doc
            .then(Format::Line)
            .then(Format::text("constructor:"))
            .then(
                Format::Line
                    .then(Format::text(format!("{ctor_modifier}{ctor_sig}")))
                    .nest(2),
            );

        let res_order = structures
            .resolution_order(name, RecordBudget::default())
            .map_err(|_| Unsupported("an unreadable structure resolution order"))?;
        if res_order.len() > 1 {
            let order_text = res_order
                .iter()
                .map(|item| self.full_name(item))
                .collect::<Vec<_>>()
                .join(", ");
            doc = doc
                .then(Format::Line)
                .then(Format::text("field notation resolution order:"))
                .then(Format::Line.then(Format::text(order_text)).nest(2));
        }
        Ok(doc)
    }

    #[allow(clippy::too_many_arguments)]
    fn collect_structure_print_fields(
        &self,
        structures: &ImportedStructures,
        root: &Name,
        current: &Name,
        levels: &[Level],
        args: &[Expr],
        receiver: &Expr,
        defaults: &RecordDefaults,
        seen: &mut std::collections::HashSet<Name>,
        out: &mut Vec<(Name, Expr)>,
        depth: usize,
    ) -> Result<(), Unsupported> {
        if depth > 64 {
            return Err(Unsupported("deeply nested structure parents"));
        }
        let Some(entry) = structures.get(current) else {
            return Err(Unsupported("a parent without structure metadata"));
        };
        let mut proj_args = args.to_vec();
        proj_args.push(receiver.clone());
        for (index, field) in entry.fields.iter().enumerate() {
            if let Some(sub_parent) = &field.subobject {
                let sub_type = self.application_type(&field.projection, levels, &proj_args)?;
                let (head, sub_args) = spine(&sub_type);
                let ExprNode::Const {
                    name: head_name,
                    levels: sub_levels,
                } = head.node()
                else {
                    return Err(Unsupported("a non-constant subobject parent type"));
                };
                if head_name != sub_parent {
                    return Err(Unsupported("a mismatched subobject parent type"));
                }
                let sub_receiver = proj_args.iter().cloned().fold(
                    Expr::const_(field.projection.clone(), levels.to_vec()),
                    Expr::app,
                );
                self.collect_structure_print_fields(
                    structures,
                    root,
                    sub_parent,
                    sub_levels,
                    &sub_args,
                    &sub_receiver,
                    defaults,
                    seen,
                    out,
                    depth + 1,
                )?;
                continue;
            }
            if !seen.insert(field.name.clone()) {
                continue;
            }
            let has_default = self
                .env
                .find(&Name::str(root.append_core(&field.name), "_default"))
                .is_some()
                || self
                    .env
                    .find(&Name::str(
                        root.append_core(&field.name),
                        "_inherited_default",
                    ))
                    .is_some()
                || u32::try_from(index)
                    .ok()
                    .and_then(|idx| defaults.helper(current, idx))
                    .is_some();
            if has_default {
                return Err(Unsupported("a structure with field defaults"));
            }
            let ftype = self.application_type(&field.projection, levels, &proj_args)?;
            let origin = structure_field_origin(structures, root, &field.name, 0)
                .ok_or(Unsupported("a structure field without a known origin"))?;
            out.push((origin, ftype));
        }
        Ok(())
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
            // Under `pp.privateNames` the header names the private name's internal form.
            if self.pp.private_names {
                return Err(Unsupported("a private name under `pp.privateNames`"));
            }
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
            // `MessageData.ofConstName`: `delabConst` of the constant at its own universe
            // parameters, so `pp.universes` shows them.
            let names = axioms
                .iter()
                .map(|axiom| {
                    let levels: Vec<Level> = self
                        .env
                        .find(axiom)
                        .map(|info| {
                            info.constant_val()
                                .level_params
                                .iter()
                                .cloned()
                                .map(Level::param)
                                .collect()
                        })
                        .unwrap_or_default();
                    self.constant_head(axiom, &levels)
                })
                .collect::<Result<Vec<_>, _>>()?;
            format!("'{shown}' depends on axioms: [{}]", names.join(", "))
        })
    }
}

/// `getFieldOrigin` (vendored `Lean/Elab/Print.lean:115-122`): the originating structure's
/// projection name for `field`, following the first parent that provides `field`.
fn structure_field_origin(
    structures: &ImportedStructures,
    struct_name: &Name,
    field: &Name,
    depth: usize,
) -> Option<Name> {
    if depth > 64 {
        return None;
    }
    let entry = structures.get(struct_name)?;
    for parent in &entry.parents {
        if structure_has_field(structures, &parent.name, field, depth + 1) {
            return structure_field_origin(structures, &parent.name, field, depth + 1);
        }
    }
    entry
        .fields
        .iter()
        .find(|item| &item.name == field)
        .map(|item| item.projection.clone())
}

fn structure_has_field(
    structures: &ImportedStructures,
    struct_name: &Name,
    field: &Name,
    depth: usize,
) -> bool {
    if depth > 64 {
        return false;
    }
    let Some(entry) = structures.get(struct_name) else {
        return false;
    };
    if entry
        .fields
        .iter()
        .any(|item| item.subobject.is_none() && &item.name == field)
    {
        return true;
    }
    entry
        .parents
        .iter()
        .any(|parent| structure_has_field(structures, &parent.name, field, depth + 1))
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
