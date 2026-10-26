//! Structure instances, as the pin's `delabStructureInstance` prints them (vendored
//! `PrettyPrinter/Delaborator/Builtins.lean:594-689`). A structure's constructor applied to every
//! parameter and field is `{ x := a, … }`, or `⟨a, …⟩` of its explicit fields for a structure
//! tagged `@[pp_using_anonymous_constructor]`. A field that is a parent's subobject, and is that
//! parent's constructor applied, is flattened in place (`pp.structureInstances.flatten`).
//!
//! The pin omits a field equal to its default value (`pp.structureInstances.defaults` is off):
//! the printed structure's default for the field, instantiated with the parameters and the
//! fields before it, is compared with the field by a reducible definitional check. Here a field
//! syntactically equal to it is omitted and a literal that differs from a literal default is
//! kept; any other comparison is refused, as is a default this structure only inherits through
//! a parent this door does not resolve. So is a constructor that an `@[app_unexpander]` or a
//! notation of this file prints, and a local type without fields: the pin prints `structure E`
//! as `{ }` and `inductive E | mk` as `E.mk`, which this door cannot tell apart.
use super::*;
use fln_elab::records::imported::ImportedStructures;
use fln_elab::records::inheritance::RecordParents;
use fln_env::constants::ConstructorVal;

/// What the printer reads about structures, read when one is first printed.
pub(super) struct StructureTables {
    imported: ImportedStructures,
    local: RecordParents,
}

impl<'a> Printer<'a> {
    /// `delabStructureInstance` for `ctor` at `levels` applied to `args`, its parameters and
    /// fields.
    pub(super) fn structure_instance(
        &mut self,
        ctor: &ConstructorVal,
        levels: &[Level],
        args: &[Expr],
    ) -> Doc {
        let tags = self
            .tags
            .as_ref()
            .ok_or(Unsupported("an unreadable delaborator tag journal"))?;
        // `(appUnexpanderAttribute.getValues env s.name).isEmpty`.
        if self.unexpander_in_force(&ctor.base.name) || self.notation_prints(&ctor.base.name) {
            return Err(Unsupported("a constructor an unexpander prints"));
        }
        if tags.anonymous_constructor(&ctor.induct) {
            let infos = self.binder_infos(&ctor.base.name);
            let mut doc = Format::text("⟨");
            let mut first = true;
            for (index, arg) in args.iter().enumerate().skip(ctor.num_params as usize) {
                if infos.get(index) != Some(&BinderInfo::Default) {
                    continue;
                }
                if !first {
                    doc = doc.then(Format::text(",")).then(Format::Line);
                }
                doc = doc.then(self.with_trailing(false, |printer| printer.doc(arg, 0))?);
                first = false;
            }
            let doc = node(doc.then(Format::text("⟩")));
            // `withTypeAscription (cond := (← withType <| getPPOption getPPStructureInstanceType))`.
            if self.pp.structure_instance_types {
                let type_ = self.application_type(&ctor.base.name, levels, args)?;
                return self.ascribed(doc, &type_);
            }
            return Ok(doc);
        }
        self.structure_tables()?;
        let imported = self
            .structures
            .as_ref()
            .is_some_and(|tables| tables.imported.get(&ctor.induct).is_some());
        if ctor.num_fields == 0 && !imported {
            return Err(Unsupported(
                "a type without fields, which may not be a structure",
            ));
        }
        let mut fields = Vec::new();
        let root = Root {
            name: &ctor.induct,
            levels,
            params: args.get(..ctor.num_params as usize).unwrap_or(&[]),
        };
        let mut values = Vec::new();
        self.structure_fields(&root, ctor, args, &mut values, &mut fields)?;
        // `optional (" : " termParser)`: under `pp.structureInstanceTypes`, the instance's type.
        let type_ = if self.pp.structure_instance_types {
            let type_ = self.application_type(&ctor.base.name, levels, args)?;
            Some(self.with_trailing(false, |printer| printer.doc(&type_, 0))?)
        } else {
            None
        };
        if fields.is_empty() {
            return match type_ {
                None => Ok(Format::text("{ }")),
                Some(_) => Err(Unsupported(
                    "a structure instance without fields, with its type",
                )),
            };
        }
        // `"{ " … sepByIndent structInstField ", " … " }"`: each token's trailing space is a line.
        let mut doc = Format::text("{").then(Format::Line);
        for (index, (name, value)) in fields.into_iter().enumerate() {
            if index > 0 {
                doc = doc.then(Format::text(",")).then(Format::Line);
            }
            doc = doc.then(node(
                Format::text(format!("{} :=", escaped_name(&name)))
                    .then(Format::Line)
                    .then(value),
            ));
        }
        if let Some(type_) = type_ {
            doc = doc.then(Format::text(" :")).then(Format::Line).then(type_);
        }
        Ok(node(doc.then(Format::text(" }"))))
    }

    /// `collectStructFields`: `ctor`'s fields in order, a parent's subobject flattened when it is
    /// that parent's constructor applied. `root` is the printed structure, whose defaults govern
    /// every field shown; `values` are the fields collected so far, by name, which a default
    /// may read.
    fn structure_fields(
        &mut self,
        root: &Root<'_>,
        ctor: &ConstructorVal,
        args: &[Expr],
        values: &mut Vec<(Name, Expr)>,
        out: &mut Vec<(Name, Format)>,
    ) -> Result<(), Unsupported> {
        let names = field_names(self.env, ctor)?;
        let subobjects = self.subobjects(&ctor.induct, names.len())?;
        for (index, name) in names.iter().enumerate() {
            let value = args
                .get(ctor.num_params as usize + index)
                .ok_or(Unsupported("a structure instance missing a field"))?;
            values.push((name.clone(), value.clone()));
            let (head, parent_args) = spine(value);
            if let Some(parent) = &subobjects[index]
                && let ExprNode::Const {
                    name: parent_name, ..
                } = head.node()
                && let Some(ConstantInfo::Ctor(parent_ctor)) = self.env.find(parent_name)
                && parent_ctor.induct == *parent
                && parent_args.len() == (parent_ctor.num_params + parent_ctor.num_fields) as usize
            {
                let parent_ctor = parent_ctor.clone();
                self.structure_fields(root, &parent_ctor, &parent_args, values, out)?;
                continue;
            }
            // `getEffectiveDefaultFnForField?`: the printed structure's `_default` or
            // `_inherited_default` helper for the field.
            let helper = ["_default", "_inherited_default"]
                .into_iter()
                .map(|suffix| Name::str(root.name.append_core(name), suffix))
                .find(|helper| self.env.find(helper).is_some());
            match helper {
                Some(helper) => {
                    if self.default_matches(&helper, root, values, value)? {
                        continue;
                    }
                }
                // A default the field's own structure declares, which the printed one inherits
                // under a name this door does not resolve.
                None if ["_default", "_inherited_default"]
                    .into_iter()
                    .any(|suffix| {
                        self.env
                            .find(&Name::str(ctor.induct.append_core(name), suffix))
                            .is_some()
                    }) =>
                {
                    return Err(Unsupported(
                        "a structure field with an inherited default value",
                    ));
                }
                None => {}
            }
            // A `,` or `}` follows a field's value, which ends no term.
            let printed = self.with_trailing(false, |printer| printer.doc(value, 0))?;
            out.push((name.clone(), printed));
        }
        Ok(())
    }

    /// Whether a field `value` equals its default from `helper`: `instantiateStructDefaultValueFn?`
    /// (vendored `Lean/Meta/Structure.lean:196-222`) with the root's levels and parameters, each
    /// further `fun` reading the collected field of its binder's name (none: not omitted), an
    /// `id _ a` read as `a`; then the pin's reducible `isDefEq`, decided here only for a value
    /// syntactically equal to the default or two different literals.
    fn default_matches(
        &mut self,
        helper: &Name,
        root: &Root<'_>,
        values: &[(Name, Expr)],
        value: &Expr,
    ) -> Result<bool, Unsupported> {
        let Some(ConstantInfo::Defn(definition)) = self.env.find(helper) else {
            return Err(Unsupported(
                "a structure field default that is not a definition",
            ));
        };
        if definition.base.level_params.len() != root.levels.len() {
            return Err(Unsupported(
                "a structure field default at other universe levels",
            ));
        }
        let mut default = fln_elab::universe::parameters::instantiate(
            || Ok(()),
            || Unsupported("a structure field default at other universe levels"),
            &definition.value,
            &definition.base.level_params,
            root.levels,
        )?;
        let instantiate = |body: &Expr, argument: &Expr| {
            body.subst_loose(0, std::slice::from_ref(argument))
                .map_err(|_| Unsupported("an unreadable structure field default"))
        };
        for param in root.params {
            self.tick()?;
            let ExprNode::Lam { body, .. } = default.node() else {
                return Ok(false);
            };
            default = instantiate(body, param)?;
        }
        while let ExprNode::Lam {
            binder_name, body, ..
        } = default.node()
        {
            self.tick()?;
            let Some((_, field)) = values.iter().rev().find(|(name, _)| name == binder_name) else {
                return Ok(false);
            };
            default = instantiate(body, field)?;
        }
        let (head, args) = spine(&default);
        if let ExprNode::Const { name, .. } = head.node()
            && *name == Name::from_components(["id"])
            && args.len() == 2
        {
            default = args[1].clone();
        }
        if default == *value {
            return Ok(true);
        }
        match (literal(&default), literal(value)) {
            (Some(left), Some(right)) if left.0 == right.0 && left.1 != right.1 => Ok(false),
            _ => Err(Unsupported(
                "a structure field that may be definitionally equal to its default",
            )),
        }
    }

    fn structure_tables(&mut self) -> Result<(), Unsupported> {
        if self.structures.is_none() {
            let imported = ImportedStructures::read(self.env)
                .map_err(|_| Unsupported("an unreadable imported structure journal"))?;
            let local = RecordParents::read(self.env)
                .map_err(|_| Unsupported("an unreadable structure parent journal"))?;
            self.structures = Some(StructureTables { imported, local });
        }
        Ok(())
    }

    /// For each of `record`'s `count` fields, the parent it is a subobject of, if any: from the
    /// imported structure metadata, or for a local structure from its recorded parents.
    fn subobjects(
        &mut self,
        record: &Name,
        count: usize,
    ) -> Result<Vec<Option<Name>>, Unsupported> {
        self.structure_tables()?;
        let tables = self
            .structures
            .as_ref()
            .ok_or(Unsupported("an unreadable structure journal"))?;
        if let Some(entry) = tables.imported.get(record) {
            if entry.fields.len() != count {
                return Err(Unsupported(
                    "a structure whose fields disagree with its metadata",
                ));
            }
            return Ok(entry
                .fields
                .iter()
                .map(|field| field.subobject.clone())
                .collect());
        }
        let mut subobjects = vec![None; count];
        for parent in tables.local.parents(record) {
            let slot = subobjects
                .get_mut(parent.field as usize)
                .ok_or(Unsupported(
                    "a structure whose parents disagree with its fields",
                ))?;
            *slot = Some(parent.parent.clone());
        }
        Ok(subobjects)
    }

    /// `stripParentProjections` (vendored `PrettyPrinter/Delaborator/Builtins.lean:260-270`): a
    /// field-notation object printed `x.toP` by a projection to a parent's subobject is `x`, so
    /// `B.toA (D.toB self)` prints `self.toA`. `parentProj? false` (`FieldNotation.lean:145-153`)
    /// takes only a subobject field's projection applied to its parameters and the structure.
    /// A projection a notation may print instead is refused: the pin strips only `x.toP`.
    pub(super) fn without_parent_projections(
        &mut self,
        object: &Expr,
        explicit: bool,
    ) -> Result<Expr, Unsupported> {
        let mut object = object.clone();
        loop {
            self.tick()?;
            let (head, args) = spine(&object);
            let ExprNode::Const { name, .. } = head.node() else {
                return Ok(object);
            };
            let Some(params) = self.parent_projection(name, args.len())? else {
                return Ok(object);
            };
            // In explicit mode a projection of a structure with parameters stays: they are its
            // implicit arguments (`withoutParentProjections (explicit := true)`).
            if explicit && params > 0 {
                return Ok(object);
            }
            let infos = self.binder_infos(name);
            let Some((receiver, _)) = self.field_receiver(name, &infos, &args) else {
                return Ok(object);
            };
            if receiver != params {
                return Ok(object);
            }
            if self.notation_prints(name) || (self.imported_tags && self.unexpander_in_force(name))
            {
                return Err(Unsupported("a parent projection a notation may print"));
            }
            object = args[params].clone();
        }
    }

    /// The parameter count of `name`'s structure when `name` projects a parent's subobject field
    /// and `arity` arguments are its parameters and the structure.
    fn parent_projection(
        &mut self,
        name: &Name,
        arity: usize,
    ) -> Result<Option<usize>, Unsupported> {
        let LeafView::Str(field) = name.leaf_view() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(record)) = self.env.find(&name.parent()) else {
            return Ok(None);
        };
        let ([ctor], 0) = (record.ctors.as_slice(), record.num_indices) else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.env.find(ctor) else {
            return Ok(None);
        };
        if arity != ctor.num_params as usize + 1 {
            return Ok(None);
        }
        let ctor = ctor.clone();
        let names = field_names(self.env, &ctor)?;
        let Some(index) = names
            .iter()
            .position(|candidate| candidate.leaf_view() == LeafView::Str(field))
        else {
            return Ok(None);
        };
        let subobjects = self.subobjects(&ctor.induct, names.len())?;
        Ok(subobjects[index]
            .is_some()
            .then_some(ctor.num_params as usize))
    }

    /// Whether a notation of this file prints applications of `constant`: it declares an
    /// unexpander for it, which withholds the structure instance whether or not it applies.
    pub(super) fn notation_prints(&self, constant: &Name) -> bool {
        self.notations.is_some_and(|notations| {
            notations
                .unexpanders
                .iter()
                .any(|unexpander| unexpander.head == *constant)
        })
    }
}

/// A constructor's field names: its binder names after the parameters.
fn field_names(env: &Environment, ctor: &ConstructorVal) -> Result<Vec<Name>, Unsupported> {
    let Some(info) = env.find(&ctor.base.name) else {
        return Err(Unsupported("a constructor that is not a constant"));
    };
    let mut type_ = &info.constant_val().type_;
    let mut names = Vec::new();
    for index in 0..(ctor.num_params + ctor.num_fields) {
        let ExprNode::ForallE {
            binder_name, body, ..
        } = type_.node()
        else {
            return Err(Unsupported("a constructor type shorter than its fields"));
        };
        if index >= ctor.num_params {
            names.push(binder_name.clone());
        }
        type_ = body;
    }
    Ok(names)
}

/// The structure a structure instance prints: its name, universe levels and parameters.
pub(super) struct Root<'r> {
    name: &'r Name,
    levels: &'r [Level],
    params: &'r [Expr],
}

/// A literal's kind and value, for a literal written as the elaborator writes it: a raw
/// natural number or string, a numeral `OfNat.ofNat Nat n _`, or `Bool.true`/`Bool.false`.
/// Two literals of one kind that differ are never definitionally equal.
fn literal(e: &Expr) -> Option<(u8, Expr)> {
    match e.node() {
        ExprNode::Lit {
            literal: Literal::Nat(_),
        } => return Some((0, e.clone())),
        ExprNode::Lit {
            literal: Literal::Str(_),
        } => return Some((1, e.clone())),
        _ => {}
    }
    let (head, args) = spine(e);
    let ExprNode::Const { name, .. } = head.node() else {
        return None;
    };
    let text = name.to_display_string();
    match (text.as_str(), args.as_slice()) {
        ("OfNat.ofNat", [type_, raw, _])
            if matches!(type_.node(), ExprNode::Const { name, .. } if name.to_display_string() == "Nat")
                && matches!(
                    raw.node(),
                    ExprNode::Lit {
                        literal: Literal::Nat(_)
                    }
                ) =>
        {
            Some((0, raw.clone()))
        }
        ("Bool.true" | "Bool.false", []) => Some((2, e.clone())),
        _ => None,
    }
}
