//! Declaration binder tactics become ordinary, checked Lean.Syntax data.
//! Semantics: Lean/Elab/Binders.lean quoteAutoTactic / declareTacticSyntax.
//! No tactic runs while its binder is declared. The existing autoParam
//! application path decodes the quotation and checks the resulting proof.
use super::*;
use fln_core::name::identifier::{NameRenderError, to_identifier_string};
use fln_syntax::tree::Preresolved;

fn invalid() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax {
        expected: "an autoParam tactic without missing syntax or antiquotations",
    }
}

fn constant(parts: &[&str]) -> Expr {
    Expr::const_(Name::from_components(parts.iter().copied()), Vec::new())
}

fn apps(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn natural(value: u64) -> Expr {
    Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
}

impl Context {
    pub(super) fn declare_auto_tactic(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Name, NatDefinitionElabError> {
        if !self.allow_auxiliary_declarations && self.declaration_header_probe.is_none() {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "an entry point preserving autoParam auxiliary declarations",
            });
        }
        // The declaration header has its own withDeclName scope at the pin.
        // Restore the caller's generator before body elaboration, including
        // its separate asynchronous theorem-child generator.
        let temporary_names = self.aux_names.is_none();
        if temporary_names {
            let owner = self
                .diagnostic_declaration
                .clone()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            self.aux_names = Some(tactics::AuxNames::new(owner, false));
        }
        let name = self.aux_decl_name(&Name::from_components(["_auto"]));
        if temporary_names {
            self.aux_names = None;
        }
        let name = name?;
        let value = self.quote_auto_tactic(syntax)?;
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: constant(&["Lean", "Syntax"]),
            },
            value,
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        });
        // These are checked private transaction predecessors, not publication
        // receipts. The facade admits this ordered effect through both seats
        // before publishing its owner. Context rollback retains neither effect.
        // A header visibility probe discards its entire Context on completion;
        // the real declaration pass recreates and returns these predecessors.
        let base = self.txn.env.clone();
        self.txn.env = self.admit_auxiliary_into_env(&base, declaration.clone())?;
        if !self.private_auxiliary_declarations {
            self.auxiliary_visibility
                .header_quotations
                .insert(name.clone());
            // Header types survive the switch to a hidden body's world.
            // Carry their checked quotation predecessor with them; never
            // turn a private body declaration into a public predecessor.
            if let Some(environment) = self
                .private_proof_body
                .as_ref()
                .map(|(environment, _)| environment.clone())
            {
                let checked = self.admit_auxiliary_into_env(&environment, declaration.clone())?;
                if let Some((environment, _)) = &mut self.private_proof_body {
                    *environment = checked;
                }
            }
            if let Some(environment) = self
                .private_decl_world
                .as_ref()
                .map(|(environment, _)| environment.clone())
            {
                let checked = self.admit_auxiliary_into_env(&environment, declaration.clone())?;
                if let Some((environment, _)) = &mut self.private_decl_world {
                    *environment = checked;
                }
            }
        }
        self.auxiliary_declarations.push(declaration);
        Ok(name)
    }

    fn auto_string(&mut self, value: &str) -> Result<Expr, NatDefinitionElabError> {
        for _ in value.as_bytes() {
            self.tick()?;
        }
        Ok(Expr::lit(Literal::Str(value.to_owned())))
    }

    fn auto_name(&mut self, name: &Name) -> Result<Expr, NatDefinitionElabError> {
        let mut parts = Vec::new();
        let mut cursor = name.clone();
        while !cursor.is_anonymous() {
            self.tick()?;
            if cursor.component_overflowed() {
                return Err(invalid());
            }
            parts.push(cursor.clone());
            cursor = cursor.parent();
        }
        let mut value = constant(&["Lean", "Name", "anonymous"]);
        for part in parts.into_iter().rev() {
            self.tick()?;
            value = match part.leaf_view() {
                LeafView::Str(text) => apps(
                    constant(&["Lean", "Name", "str"]),
                    [value, self.auto_string(text)?],
                ),
                LeafView::Num(number) => {
                    apps(constant(&["Lean", "Name", "num"]), [value, natural(number)])
                }
                LeafView::Anonymous => unreachable!("collected name components"),
            };
        }
        Ok(value)
    }

    fn auto_list(
        &mut self,
        type_: Expr,
        values: Vec<Expr>,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        let mut list = Expr::app(
            Expr::const_(Name::from_components(["List", "nil"]), vec![Level::zero()]),
            type_.clone(),
        );
        let cons = Expr::const_(Name::from_components(["List", "cons"]), vec![Level::zero()]);
        for value in values.into_iter().rev() {
            self.tick()?;
            list = apps(cons.clone(), [type_.clone(), value, list]);
        }
        Ok(list)
    }

    fn auto_preresolved(
        &mut self,
        entries: &[Preresolved],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut values = Vec::new();
        for entry in entries {
            self.tick()?;
            values.push(match entry {
                Preresolved::Namespace { ns } => Expr::app(
                    constant(&["Lean", "Syntax", "Preresolved", "namespace"]),
                    self.auto_name(ns)?,
                ),
                Preresolved::Decl { name, fields } => {
                    let name = self.auto_name(name)?;
                    let mut names = Vec::new();
                    for field in fields {
                        names.push(self.auto_string(field)?);
                    }
                    let names = self.auto_list(constant(&["String"]), names)?;
                    apps(
                        constant(&["Lean", "Syntax", "Preresolved", "decl"]),
                        [name, names],
                    )
                }
            });
        }
        self.auto_list(constant(&["Lean", "Syntax", "Preresolved"]), values)
    }

    fn auto_raw_identifier(&mut self, name: &Name) -> Result<Expr, NatDefinitionElabError> {
        let remaining = if self.txn.budget.max_heartbeats == 0 {
            usize::MAX
        } else {
            usize::try_from(
                self.txn
                    .budget
                    .max_heartbeats
                    .saturating_sub(self.txn.budget.heartbeats_consumed),
            )
            .unwrap_or(usize::MAX)
        };
        // quoteAutoTactic uses Name.toString, not the old source span.
        // This shared renderer retains escaped components and numeric scopes.
        let raw = to_identifier_string(name, remaining).map_err(|error| match error {
            NameRenderError::OverflowedComponent => invalid(),
            NameRenderError::ByteBudgetExceeded { .. } => {
                failure(SourceInferenceError::ResourceLimit)
            }
        })?;
        for _ in raw.as_bytes() {
            self.tick()?;
        }
        let length =
            u64::try_from(raw.len()).map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        let position = |index| Expr::app(constant(&["String", "Pos", "Raw", "mk"]), natural(index));
        Ok(apps(
            constant(&["Substring", "Raw", "mk"]),
            [Expr::lit(Literal::Str(raw)), position(0), position(length)],
        ))
    }

    fn quote_auto_tactic(&mut self, syntax: &Syntax) -> Result<Expr, NatDefinitionElabError> {
        enum Work<'a> {
            Visit(&'a Syntax),
            Finish(&'a Name, usize),
        }
        let mut work = vec![Work::Visit(syntax)];
        let mut built = Vec::new();
        while let Some(next) = work.pop() {
            self.tick()?;
            match next {
                Work::Visit(Syntax::Missing) => return Err(invalid()),
                Work::Visit(Syntax::Atom { val, .. }) => built.push(apps(
                    constant(&["Lean", "Syntax", "atom"]),
                    [
                        constant(&["Lean", "SourceInfo", "none"]),
                        self.auto_string(val)?,
                    ],
                )),
                Work::Visit(Syntax::Ident {
                    val, preresolved, ..
                }) => {
                    let raw = self.auto_raw_identifier(val)?;
                    let name = self.auto_name(val)?;
                    let preresolved = self.auto_preresolved(preresolved)?;
                    built.push(apps(
                        constant(&["Lean", "Syntax", "ident"]),
                        [
                            constant(&["Lean", "SourceInfo", "none"]),
                            raw,
                            name,
                            preresolved,
                        ],
                    ));
                }
                Work::Visit(Syntax::Node { kind, args, .. }) => {
                    if matches!(kind.leaf_view(), LeafView::Str("antiquot")) {
                        return Err(invalid());
                    }
                    if kind == &Name::from_components(["null"]) {
                        for argument in args {
                            self.tick()?;
                            if argument.kind().is_some_and(|kind| {
                                matches!(
                                    kind.leaf_view(),
                                    LeafView::Str("antiquot_scope" | "antiquot_suffix_splice")
                                )
                            }) {
                                return Err(invalid());
                            }
                        }
                    }
                    work.push(Work::Finish(kind, built.len()));
                    work.extend(args.iter().rev().map(Work::Visit));
                }
                Work::Finish(kind, start) => {
                    let children = built.split_off(start);
                    let children = self.auto_list(constant(&["Lean", "Syntax"]), children)?;
                    let array = apps(
                        Expr::const_(Name::from_components(["Array", "mk"]), vec![Level::zero()]),
                        [constant(&["Lean", "Syntax"]), children],
                    );
                    let kind = self.auto_name(kind)?;
                    built.push(apps(
                        constant(&["Lean", "Syntax", "node"]),
                        [constant(&["Lean", "SourceInfo", "none"]), kind, array],
                    ));
                }
            }
        }
        if built.len() != 1 {
            return Err(invalid());
        }
        built.pop().ok_or_else(invalid)
    }
}
