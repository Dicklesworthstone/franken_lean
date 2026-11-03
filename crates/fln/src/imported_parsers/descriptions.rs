//! Reconstruct the pin's closed ParserDescr algebra without running a parser.
use super::*;
use data::{Reader, Value};
use fln_parse::extensions::Descr;

struct DescriptionReader<'a, 'b> {
    data: &'a mut Reader<'b>,
    admitted: &'b Environment,
    module: &'a Name,
    owner: &'a Name,
    nodes: &'a mut usize,
    max_depth: usize,
    references: BTreeSet<Name>,
}

pub(super) fn read<'a>(
    data: &mut Reader<'a>,
    body: &Expr,
    admitted: &'a Environment,
    module: &Name,
    owner: &Name,
    nodes: &mut usize,
    max_depth: usize,
) -> Result<Descr, ParserRegistrationError> {
    data.validate_family(
        &name(parsers::PARSER_DESCR_TYPE),
        parsers::PARSER_DESCR_CONSTRUCTOR_FIELDS,
    )
    .map_err(|error| data_error(module, owner, error))?;
    DescriptionReader {
        data,
        admitted,
        module,
        owner,
        nodes,
        max_depth: max_depth.min(64),
        references: BTreeSet::from([owner.clone()]),
    }
    .value(Value::closed(body.clone()), 0)
}

impl DescriptionReader<'_, '_> {
    fn unsupported(&self, reason: &'static str) -> ParserRegistrationError {
        ParserRegistrationError::Description {
            module: self.module.clone(),
            declaration: self.owner.clone(),
            reason,
        }
    }

    fn value(&mut self, value: Value, depth: usize) -> Result<Descr, ParserRegistrationError> {
        if depth >= self.max_depth {
            return Err(ParserRegistrationError::Limit("parser description depth"));
        }
        *self.nodes = self
            .nodes
            .checked_sub(1)
            .ok_or(ParserRegistrationError::Limit(
                "expanded parser description nodes",
            ))?;
        let (constructor, args) = self
            .data
            .constructor(value)
            .map_err(|error| data_error(self.module, self.owner, error))?;
        let Some((label, arity)) = parsers::PARSER_DESCR_CONSTRUCTORS
            .iter()
            .find(|(label, _)| constructor == name(label))
        else {
            return Err(self.unsupported("value is not a ParserDescr constructor"));
        };
        if args.len() != *arity {
            return Err(self.unsupported("ParserDescr constructor has the wrong arity"));
        }
        let mut fields = args.into_iter();
        // Generated field signatures and constructor membership have already
        // been checked. This match attaches native semantics to the named
        // variants, so a changed constructor order cannot change their meaning.
        let mut field = || {
            fields
                .next()
                .expect("validated ParserDescr constructor arity")
        };
        Ok(
            match label.rsplit('.').next().expect("qualified constructor") {
                "const" => Descr::Const(self.name(field())?),
                "unary" => Descr::Unary(
                    self.name(field())?,
                    Box::new(self.value(field(), depth + 1)?),
                ),
                "binary" => Descr::Binary(
                    self.name(field())?,
                    Box::new(self.value(field(), depth + 1)?),
                    Box::new(self.value(field(), depth + 1)?),
                ),
                "node" => Descr::Node {
                    kind: self.name(field())?,
                    prec: self.nat(field())?,
                    body: Box::new(self.value(field(), depth + 1)?),
                },
                "trailingNode" => Descr::TrailingNode {
                    kind: self.name(field())?,
                    prec: self.nat(field())?,
                    lhs_prec: self.nat(field())?,
                    body: Box::new(self.value(field(), depth + 1)?),
                },
                "symbol" => Descr::Symbol(self.string(field())?),
                "nonReservedSymbol" => {
                    Descr::NonReservedSymbol(self.string(field())?, self.boolean(field())?)
                }
                "cat" => Descr::Cat(self.name(field())?, self.nat(field())?),
                "parser" => {
                    let reference = self.name(field())?;
                    if !self.references.insert(reference.clone()) {
                        return Err(self.unsupported("cyclic parser description reference"));
                    }
                    let owner = self.admitted.find(&reference).ok_or_else(|| {
                        owner_error(
                            self.module,
                            &reference,
                            "referenced parser has no admitted owner",
                        )
                    })?;
                    let (leading, _) = description_body(self.module, &reference, owner)?;
                    if !leading {
                        return Err(
                            self.unsupported("nested trailing parser description reference")
                        );
                    }
                    // Resolve through the data reader, which checks the permitted
                    // closure and retains the exact helper/owner bindings. Never
                    // take a same-named census description as artifact authority.
                    let result = self.value(
                        Value::closed(Expr::const_(reference.clone(), vec![])),
                        depth + 1,
                    )?;
                    self.references.remove(&reference);
                    result
                }
                "nodeWithAntiquot" => Descr::NodeWithAntiquot(
                    self.string(field())?,
                    self.name(field())?,
                    Box::new(self.value(field(), depth + 1)?),
                ),
                "sepBy" | "sepBy1" => Descr::SepBy {
                    item: Box::new(self.value(field(), depth + 1)?),
                    separator: self.string(field())?,
                    parser: Box::new(self.value(field(), depth + 1)?),
                    trailing: self.boolean(field())?,
                    at_least_one: label.ends_with(".sepBy1"),
                },
                "unicodeSymbol" => Descr::UnicodeSymbol(
                    self.string(field())?,
                    self.string(field())?,
                    self.boolean(field())?,
                ),
                _ => {
                    return Err(self.unsupported(
                        "generated ParserDescr variant has no native reconstruction",
                    ));
                }
            },
        )
    }

    fn name(&mut self, value: Value) -> Result<Name, ParserRegistrationError> {
        self.data
            .name(value)
            .map_err(|error| data_error(self.module, self.owner, error))
    }

    fn nat(&mut self, value: Value) -> Result<u32, ParserRegistrationError> {
        self.data
            .nat_u32(value)
            .map_err(|error| data_error(self.module, self.owner, error))
    }

    fn string(&mut self, value: Value) -> Result<String, ParserRegistrationError> {
        self.data
            .string(value)
            .map_err(|error| data_error(self.module, self.owner, error))
    }

    fn boolean(&mut self, value: Value) -> Result<bool, ParserRegistrationError> {
        self.data
            .boolean(value)
            .map_err(|error| data_error(self.module, self.owner, error))
    }
}
