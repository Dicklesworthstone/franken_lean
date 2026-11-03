//! Closed parser-description data from the same checked source-import receipt.
//! No parser function or upstream elaborator is executed to obtain a grammar.

use super::{MacroRegistrationError, MacroRegistrationModule, MacroRegistryLimits};
use crate::Environment;
use fln_core::expr::{Expr, ExprNode, Literal};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_olean::source_extensions::parsers::{self, ParserEntryKind};
use fln_parse::extensions::{
    Descr, IdentBehavior, ImportedSyntaxEntry, ImportedSyntaxModule, SyntaxDecl,
};
use std::collections::BTreeMap;
use std::sync::Arc;

pub(super) type Modules = Arc<[(Name, Arc<ImportedSyntaxModule>)]>;
type Owners = BTreeMap<Name, (Name, ConstantInfo)>;

pub(super) fn prepare(
    inputs: &[MacroRegistrationModule<'_>],
    admitted: &Environment,
    limits: MacroRegistryLimits,
) -> Result<(Modules, Owners), MacroRegistrationError> {
    let mut decoder = parsers::Decoder::new(limits.metadata);
    let mut work = limits.metadata.max_objects;
    let mut bytes = limits.metadata.max_bytes;
    let mut modules = Vec::new();
    let mut owners = Owners::new();
    modules
        .try_reserve_exact(inputs.len())
        .map_err(|_| MacroRegistrationError::Limit("parser modules allocation"))?;
    for input in inputs {
        let module = &input.checked.name;
        let before = decoder.remaining_limits();
        let decoded =
            decoder
                .decode(input.extensions)
                .map_err(|error| MacroRegistrationError::Decode {
                    module: module.clone(),
                    error,
                })?;
        work = work
            .checked_sub(before.max_objects - decoder.remaining_limits().max_objects)
            .ok_or(MacroRegistrationError::Limit(
                "parser journal and description work",
            ))?;
        bytes = bytes
            .checked_sub(before.max_bytes - decoder.remaining_limits().max_bytes)
            .ok_or(MacroRegistrationError::Limit(
                "parser journal and description bytes",
            ))?;
        let declarations: BTreeMap<_, _> = input
            .checked
            .decoded
            .constants
            .iter()
            .map(|info| (info.name(), info))
            .collect();
        let mut entries = Vec::new();
        entries
            .try_reserve_exact(decoded.entries.len())
            .map_err(|_| MacroRegistrationError::Limit("parser entries allocation"))?;
        for row in decoded.entries {
            let scope = row.scope;
            let entry = match row.kind {
                ParserEntryKind::Token(token) => ImportedSyntaxEntry::Token { scope, token },
                ParserEntryKind::Kind(kind) => ImportedSyntaxEntry::Kind { scope, kind },
                ParserEntryKind::Category {
                    category,
                    declaration,
                    behavior,
                } => {
                    bind(module, &declaration, &declarations, admitted, &mut owners)?;
                    ImportedSyntaxEntry::Category {
                        scope,
                        category,
                        declaration,
                        behavior: match behavior {
                            parsers::LeadingIdentBehavior::Default => IdentBehavior::Default,
                            parsers::LeadingIdentBehavior::Symbol => IdentBehavior::Symbol,
                            parsers::LeadingIdentBehavior::Both => IdentBehavior::Both,
                        },
                    }
                }
                ParserEntryKind::Parser {
                    category,
                    declaration,
                    priority,
                } => {
                    let owner = bind(module, &declaration, &declarations, admitted, &mut owners)?;
                    let mut reader = Reader {
                        module,
                        declaration: &declaration,
                        work: &mut work,
                        bytes: &mut bytes,
                    };
                    let type_ = &owner.constant_val().type_;
                    let leading = match type_.node() {
                        ExprNode::Const { name, levels } if levels.is_empty() && *name == named(parsers::PARSER_DESCR_TYPE) => true,
                        ExprNode::Const { name, levels } if levels.is_empty() && *name == named(parsers::TRAILING_PARSER_DESCR_TYPE) => false,
                        _ => return Err(reader.refuse("imported parser is not closed ParserDescr data; executable Parser functions are unsupported")),
                    };
                    let ConstantInfo::Defn(definition) = owner else {
                        return Err(reader
                            .refuse("parser description has no transparent checked definition"));
                    };
                    if !definition.base.level_params.is_empty() {
                        return Err(reader.refuse("polymorphic parser description"));
                    }
                    let descr = reader.descr(&definition.value, 0)?;
                    ImportedSyntaxEntry::Parser(Arc::new(SyntaxDecl {
                        module: module.clone(),
                        decl: declaration,
                        category: Some(category),
                        leading,
                        priority,
                        scope,
                        descr,
                    }))
                }
            };
            entries.push(entry);
        }
        modules.push((module.clone(), Arc::new(ImportedSyntaxModule { entries })));
    }
    Ok((Arc::from(modules), owners))
}

fn bind<'a>(
    module: &Name,
    declaration: &Name,
    declarations: &BTreeMap<&Name, &'a ConstantInfo>,
    admitted: &Environment,
    owners: &mut Owners,
) -> Result<&'a ConstantInfo, MacroRegistrationError> {
    let refuse = |reason| MacroRegistrationError::Owner {
        module: module.clone(),
        declaration: declaration.clone(),
        reason,
    };
    let owner = declarations
        .get(declaration)
        .copied()
        .ok_or_else(|| refuse("parser registration is not owned by this checked module"))?;
    if admitted.find(declaration) != Some(owner) {
        return Err(refuse(
            "admitted parser declaration differs from its checked owner",
        ));
    }
    if owners
        .get(declaration)
        .is_some_and(|(previous, _)| previous != module)
    {
        return Err(refuse(
            "parser registration has multiple checked module owners",
        ));
    }
    owners.insert(declaration.clone(), (module.clone(), owner.clone()));
    Ok(owner)
}

fn named(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

struct Reader<'a> {
    module: &'a Name,
    declaration: &'a Name,
    work: &'a mut u64,
    bytes: &'a mut usize,
}

impl Reader<'_> {
    fn refuse(&self, reason: &'static str) -> MacroRegistrationError {
        MacroRegistrationError::Owner {
            module: self.module.clone(),
            declaration: self.declaration.clone(),
            reason,
        }
    }

    fn tick(&mut self, depth: usize) -> Result<(), MacroRegistrationError> {
        if depth > 64 {
            return Err(MacroRegistrationError::Limit("parser description depth"));
        }
        *self.work = self
            .work
            .checked_sub(1)
            .ok_or(MacroRegistrationError::Limit("parser description work"))?;
        Ok(())
    }

    fn application<'a>(
        &mut self,
        value: &'a Expr,
        depth: usize,
    ) -> Result<(Name, Vec<&'a Expr>), MacroRegistrationError> {
        self.tick(depth)?;
        let mut head = value;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick(depth)?;
            // The extracted vocabulary has at most eight arguments. A longer
            // spine is not a constructor or literal in this data-only subset.
            if arguments.len() == 8 {
                return Err(self.refuse("over-applied parser data constructor"));
            }
            arguments.push(a);
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(self.refuse("parser data requires a constructor or extracted literal form"));
        };
        arguments.reverse();
        Ok((name.clone(), arguments))
    }

    fn string(&mut self, value: &Expr, depth: usize) -> Result<String, MacroRegistrationError> {
        self.tick(depth)?;
        let ExprNode::Lit {
            literal: Literal::Str(value),
        } = value.node()
        else {
            return Err(self.refuse("parser data requires a literal String"));
        };
        *self.bytes = self
            .bytes
            .checked_sub(value.len())
            .ok_or(MacroRegistrationError::Limit("parser description bytes"))?;
        Ok(value.clone())
    }

    fn natural(&mut self, value: &Expr, depth: usize) -> Result<u32, MacroRegistrationError> {
        u32::try_from(self.natural_u64(value, depth)?)
            .map_err(|_| self.refuse("parser natural is outside u32"))
    }

    fn natural_u64(&mut self, value: &Expr, depth: usize) -> Result<u64, MacroRegistrationError> {
        self.tick(depth)?;
        if let ExprNode::Lit {
            literal: Literal::Nat(value),
        } = value.node()
        {
            return value
                .to_u64()
                .ok_or_else(|| self.refuse("parser natural is outside u64"));
        }
        let (head, args) = self.application(value, depth)?;
        if head != named(parsers::PARSER_NAT_LITERAL_PROJECTION)
            || args.len() != 3
            || !matches!(args[0].node(), ExprNode::Const { name, levels } if *name == named("Nat") && levels.is_empty())
        {
            return Err(self.refuse("unsupported parser Nat literal"));
        }
        let (instance, indices) = self.application(args[2], depth + 1)?;
        if instance != named(parsers::PARSER_NAT_LITERAL_INSTANCE)
            || indices.len() != 1
            || indices[0] != args[1]
        {
            return Err(self.refuse("parser Nat literal has a different instance"));
        }
        // A literal projection's index must itself be a raw natural literal;
        // this never recursively evaluates a caller-supplied OfNat instance.
        if !matches!(
            args[1].node(),
            ExprNode::Lit {
                literal: Literal::Nat(_)
            }
        ) {
            return Err(self.refuse("parser Nat literal has a nonliteral index"));
        }
        self.natural_u64(args[1], depth + 1)
    }

    fn boolean(&mut self, value: &Expr, depth: usize) -> Result<bool, MacroRegistrationError> {
        let (head, args) = self.application(value, depth)?;
        if !args.is_empty() {
            return Err(self.refuse("over-applied parser Bool"));
        }
        let Some(index) = parsers::PARSER_BOOL_CONSTRUCTOR_FIELDS
            .iter()
            .position(|(name, fields)| fields.is_empty() && head == named(name))
        else {
            return Err(self.refuse("unknown parser Bool constructor"));
        };
        Ok(index == 1)
    }

    fn name(&mut self, value: &Expr, depth: usize) -> Result<Name, MacroRegistrationError> {
        let (head, args) = self.application(value, depth)?;
        let Some((form, arity)) = parsers::PARSER_NAME_LITERAL_FORMS
            .iter()
            .find(|(name, _)| head == named(name))
        else {
            return Err(self.refuse("unsupported parser Name literal"));
        };
        if args.len() != *arity {
            return Err(self.refuse("parser Name literal arity"));
        }
        match *form {
            "Lean.Name.anonymous" => Ok(Name::anonymous()),
            "Lean.Name.str" | "Lean.Name.mkStr" => {
                let prefix = self.name(args[0], depth + 1)?;
                Ok(Name::str(prefix, self.string(args[1], depth + 1)?))
            }
            "Lean.Name.num" | "Lean.Name.mkNum" => {
                let prefix = self.name(args[0], depth + 1)?;
                Ok(Name::num(prefix, self.natural_u64(args[1], depth + 1)?))
            }
            _ => {
                let mut result = Name::anonymous();
                for arg in args {
                    result = Name::str(result, self.string(arg, depth + 1)?);
                }
                Ok(result)
            }
        }
    }

    fn descr(&mut self, value: &Expr, depth: usize) -> Result<Descr, MacroRegistrationError> {
        let (head, args) = self.application(value, depth)?;
        let Some((constructor, arity)) = parsers::PARSER_DESCR_CONSTRUCTORS
            .iter()
            .find(|(name, _)| head == named(name))
        else {
            return Err(self.refuse("unsupported nonliteral parser description"));
        };
        if args.len() != *arity {
            return Err(self.refuse("parser description constructor arity"));
        }
        let next = depth + 1;
        Ok(match *constructor {
            "Lean.ParserDescr.const" => Descr::Const(self.name(args[0], next)?),
            "Lean.ParserDescr.unary" => Descr::Unary(
                self.name(args[0], next)?,
                Box::new(self.descr(args[1], next)?),
            ),
            "Lean.ParserDescr.binary" => Descr::Binary(
                self.name(args[0], next)?,
                Box::new(self.descr(args[1], next)?),
                Box::new(self.descr(args[2], next)?),
            ),
            "Lean.ParserDescr.node" => Descr::Node {
                kind: self.name(args[0], next)?,
                prec: self.natural(args[1], next)?,
                body: Box::new(self.descr(args[2], next)?),
            },
            "Lean.ParserDescr.trailingNode" => Descr::TrailingNode {
                kind: self.name(args[0], next)?,
                prec: self.natural(args[1], next)?,
                lhs_prec: self.natural(args[2], next)?,
                body: Box::new(self.descr(args[3], next)?),
            },
            "Lean.ParserDescr.symbol" => Descr::Symbol(self.string(args[0], next)?),
            "Lean.ParserDescr.nonReservedSymbol" => {
                Descr::NonReservedSymbol(self.string(args[0], next)?, self.boolean(args[1], next)?)
            }
            "Lean.ParserDescr.cat" => {
                Descr::Cat(self.name(args[0], next)?, self.natural(args[1], next)?)
            }
            "Lean.ParserDescr.parser" => Descr::Parser(self.name(args[0], next)?),
            "Lean.ParserDescr.nodeWithAntiquot" => Descr::NodeWithAntiquot(
                self.string(args[0], next)?,
                self.name(args[1], next)?,
                Box::new(self.descr(args[2], next)?),
            ),
            "Lean.ParserDescr.sepBy" | "Lean.ParserDescr.sepBy1" => Descr::SepBy {
                item: Box::new(self.descr(args[0], next)?),
                separator: self.string(args[1], next)?,
                parser: Box::new(self.descr(args[2], next)?),
                trailing: self.boolean(args[3], next)?,
                at_least_one: *constructor == "Lean.ParserDescr.sepBy1",
            },
            "Lean.ParserDescr.unicodeSymbol" => Descr::UnicodeSymbol(
                self.string(args[0], next)?,
                self.string(args[1], next)?,
                self.boolean(args[2], next)?,
            ),
            _ => return Err(self.refuse("unimplemented extracted parser description constructor")),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::NatLit;
    use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};

    fn call(head: &str, arguments: &[Expr]) -> Expr {
        arguments
            .iter()
            .fold(Expr::const_(named(head), vec![]), |f, a| {
                Expr::app(f, a.clone())
            })
    }

    fn string(value: &str) -> Expr {
        Expr::lit(Literal::Str(value.to_owned()))
    }
    fn natural(value: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(value)))
    }
    fn name(value: &str) -> Expr {
        call("Lean.Name.mkStr1", &[string(value)])
    }

    fn read(
        value: &Expr,
        work: &mut u64,
        bytes: &mut usize,
    ) -> Result<Descr, MacroRegistrationError> {
        Reader {
            module: &named("Provider"),
            declaration: &named("custom"),
            work,
            bytes,
        }
        .descr(value, 0)
    }

    #[test]
    fn closed_literals_reconstruct_a_parser_and_surplus_fields_are_refused() {
        let index = natural(1022);
        let precedence = call(
            parsers::PARSER_NAT_LITERAL_PROJECTION,
            &[
                Expr::const_(named("Nat"), vec![]),
                index.clone(),
                call(parsers::PARSER_NAT_LITERAL_INSTANCE, &[index]),
            ],
        );
        let body = call("Lean.ParserDescr.symbol", &[string("owned%[")]);
        let data = call("Lean.ParserDescr.node", &[name("custom"), precedence, body]);
        let expected = Descr::Node {
            kind: named("custom"),
            prec: 1022,
            body: Box::new(Descr::Symbol("owned%[".to_owned())),
        };
        assert_eq!(read(&data, &mut 1000, &mut 1000).unwrap(), expected);
        let surplus = Expr::app(data, string("discarded"));
        assert!(matches!(
            read(&surplus, &mut 1000, &mut 1000),
            Err(MacroRegistrationError::Owner {
                reason: "parser description constructor arity",
                ..
            })
        ));
        let unknown = call("Provider.computeParser", &[]);
        assert!(matches!(
            read(&unknown, &mut 1000, &mut 1000),
            Err(MacroRegistrationError::Owner { .. })
        ));
    }

    #[test]
    fn description_work_bytes_depth_and_nat_instances_stop_before_publication() {
        let symbol = call("Lean.ParserDescr.symbol", &[string("x")]);
        assert!(read(&symbol, &mut 0, &mut 1000).unwrap_err().is_resource());
        assert!(read(&symbol, &mut 1000, &mut 0).unwrap_err().is_resource());
        let mut deep = symbol;
        for _ in 0..70 {
            deep = call("Lean.ParserDescr.unary", &[name("atomic"), deep]);
        }
        assert!(
            read(&deep, &mut 10000, &mut 10000)
                .unwrap_err()
                .is_resource()
        );
        let bad_nat = call(
            parsers::PARSER_NAT_LITERAL_PROJECTION,
            &[
                Expr::const_(named("Nat"), vec![]),
                natural(4),
                call(parsers::PARSER_NAT_LITERAL_INSTANCE, &[natural(5)]),
            ],
        );
        let data = call("Lean.ParserDescr.cat", &[name("term"), bad_nat]);
        assert!(matches!(
            read(&data, &mut 1000, &mut 1000),
            Err(MacroRegistrationError::Owner {
                reason: "parser Nat literal has a different instance",
                ..
            })
        ));
    }

    #[test]
    fn parser_owner_binding_requires_the_exact_module_and_admitted_declaration() {
        // Caller-input binding test only: these synthetic declarations are not
        // council admission evidence. The installed CLI test supplies that path.
        let module = named("Provider");
        let declaration = named("custom");
        let owner = ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: declaration.clone(),
                level_params: vec![],
                type_: Expr::const_(named(parsers::PARSER_DESCR_TYPE), vec![]),
            },
            value: call("Lean.ParserDescr.symbol", &[string("x")]),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![declaration.clone()],
        });
        let declarations = BTreeMap::from([(&declaration, &owner)]);
        let environment = Environment::new().add_decl(owner.clone()).unwrap();
        let mut owners = Owners::new();
        assert_eq!(
            bind(
                &module,
                &declaration,
                &declarations,
                &environment,
                &mut owners
            )
            .unwrap(),
            &owner
        );
        assert!(
            bind(
                &module,
                &declaration,
                &BTreeMap::new(),
                &environment,
                &mut owners
            )
            .is_err()
        );
        let mut changed = owner.clone();
        let ConstantInfo::Defn(definition) = &mut changed else {
            unreachable!()
        };
        definition.value = call("Lean.ParserDescr.symbol", &[string("y")]);
        let different = Environment::new().add_decl(changed).unwrap();
        assert!(
            bind(
                &module,
                &declaration,
                &declarations,
                &different,
                &mut owners
            )
            .is_err()
        );
        assert!(
            bind(
                &named("Sibling"),
                &declaration,
                &declarations,
                &environment,
                &mut owners
            )
            .is_err()
        );
        assert_eq!(owners[&declaration], (module, owner));
    }

    #[test]
    fn projected_parser_journals_follow_import_order_and_cannot_cross_engine_worlds() {
        use super::super::RegisteredMacros;
        // Synthetic registry inputs test projection and binding, not admission.
        // Token-only journals deliberately have no declaration owner: module
        // presence must still be checked independently of the owner map.
        let a = named("A");
        let b = named("B");
        let c = named("C");
        let registry = RegisteredMacros {
            candidates: Arc::new(BTreeMap::new()),
            global: Arc::new(BTreeMap::new()),
            scoped: Arc::new(BTreeMap::new()),
            active_scopes: Default::default(),
            modules: Arc::new(BTreeMap::from([
                (a.clone(), vec![]),
                (b.clone(), vec![a.clone()]),
                (c.clone(), vec![]),
            ])),
            owners: Arc::new(BTreeMap::new()),
            parsers: Arc::from([a.clone(), b.clone(), c.clone()].map(|module| {
                (
                    module.clone(),
                    Arc::new(ImportedSyntaxModule {
                        entries: vec![ImportedSyntaxEntry::Token {
                            scope: None,
                            token: module.to_display_string(),
                        }],
                    }),
                )
            })),
        };
        let projected = registry
            .project_imports(&[c.clone(), a.clone(), b.clone()])
            .unwrap();
        assert_eq!(
            projected
                .parsers
                .iter()
                .map(|(module, _)| module)
                .collect::<Vec<_>>(),
            [&c, &a, &b]
        );
        let sibling = registry.project_imports(std::slice::from_ref(&c)).unwrap();
        assert_eq!(sibling.parsers.len(), 1);
        assert!(registry.project_imports(&[b.clone(), a.clone()]).is_err());
        assert!(registry.project_imports(std::slice::from_ref(&b)).is_err());
        let mut engine = crate::Engine::from_environment(Environment::new());
        assert!(sibling.validate_source_engine(&engine).is_err());
        engine.imported_modules = Arc::new([c].into_iter().collect());
        sibling.validate_source_engine(&engine).unwrap();
        assert!(projected.validate_source_engine(&engine).is_err());
    }
}
