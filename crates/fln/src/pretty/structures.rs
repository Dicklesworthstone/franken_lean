//! Structure instances, as the pin's `delabStructureInstance` prints them (vendored
//! `PrettyPrinter/Delaborator/Builtins.lean:594-689`). A structure's constructor applied to every
//! parameter and field is `{ x := a, … }`, or `⟨a, …⟩` of its explicit fields for a structure
//! tagged `@[pp_using_anonymous_constructor]`. A field that is a parent's subobject, and is that
//! parent's constructor applied, is flattened in place (`pp.structureInstances.flatten`).
//!
//! The pin omits a field equal to its default value (`pp.structureInstances.defaults` is off).
//! That takes instantiating the default and a reducible definitional check, so a structure
//! with a default is refused here. So is a constructor that an `@[app_unexpander]` or a
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
    /// `delabStructureInstance` for `ctor` applied to `args`, its parameters and fields.
    pub(super) fn structure_instance(&mut self, ctor: &ConstructorVal, args: &[Expr]) -> Doc {
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
            return Ok(node(doc.then(Format::text("⟩"))));
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
        self.structure_fields(&ctor.induct, ctor, args, &mut fields)?;
        if fields.is_empty() {
            return Ok(Format::text("{ }"));
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
        Ok(node(doc.then(Format::text(" }"))))
    }

    /// `collectStructFields`: `ctor`'s fields in order, a parent's subobject flattened when it is
    /// that parent's constructor applied. `root` is the printed structure, whose defaults govern
    /// every field shown.
    fn structure_fields(
        &mut self,
        root: &Name,
        ctor: &ConstructorVal,
        args: &[Expr],
        out: &mut Vec<(Name, Format)>,
    ) -> Result<(), Unsupported> {
        let names = field_names(self.env, ctor)?;
        let subobjects = self.subobjects(&ctor.induct, names.len())?;
        for (index, name) in names.iter().enumerate() {
            let value = args
                .get(ctor.num_params as usize + index)
                .ok_or(Unsupported("a structure instance missing a field"))?;
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
                self.structure_fields(root, &parent_ctor, &parent_args, out)?;
                continue;
            }
            // `getEffectiveDefaultFnForField?`: a `_default` or an `_inherited_default` helper of
            // the printed structure's field, or of the structure this field belongs to.
            let defaulted = [root, &ctor.induct].into_iter().any(|record| {
                ["_default", "_inherited_default"]
                    .into_iter()
                    .any(|suffix| {
                        self.env
                            .find(&Name::str(record.append_core(name), suffix))
                            .is_some()
                    })
            });
            if defaulted {
                return Err(Unsupported("a structure field with a default value"));
            }
            // A `,` or `}` follows a field's value, which ends no term.
            let printed = self.with_trailing(false, |printer| printer.doc(value, 0))?;
            out.push((name.clone(), printed));
        }
        Ok(())
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

    /// Whether a notation of this file prints applications of `constant`: it declares an
    /// unexpander for it, which withholds the structure instance whether or not it applies.
    fn notation_prints(&self, constant: &Name) -> bool {
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
