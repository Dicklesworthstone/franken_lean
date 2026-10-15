//! Literal configuration at the pinned optConfig surface, not ignored terms.
use super::*;

#[derive(Clone, Copy)]
pub(super) struct Config {
    pub max_steps: usize,
    pub symm: bool,
    pub exfalso: bool,
    pub intro: bool,
    pub constructor: bool,
}

fn unsupported() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax {
        expected: "supported literal proof-search or rule configuration",
    }
}

impl Config {
    pub const fn search_default() -> Self {
        Self {
            max_steps: 6,
            symm: true,
            exfalso: true,
            intro: true,
            constructor: true,
        }
    }

    pub fn read(context: &mut Context, syntax: &Syntax) -> Result<Self, NatDefinitionElabError> {
        Self::read_for(context, syntax, false)
    }

    pub fn read_search(
        context: &mut Context,
        syntax: &Syntax,
    ) -> Result<Self, NatDefinitionElabError> {
        Self::read_for(context, syntax, true)
    }

    fn read_for(
        context: &mut Context,
        syntax: &Syntax,
        search: bool,
    ) -> Result<Self, NatDefinitionElabError> {
        let mut config = Self::search_default();
        if !search {
            config.max_steps = 50;
        }
        let [rows] = expect_node(
            syntax,
            &parser_kind(&["Tactic", "optConfig"]),
            1,
            "rule configuration",
        )?
        else {
            return Err(unsupported());
        };
        for row in expect_null_args(rows, "rule configuration items")? {
            context.tick()?;
            let [item] = expect_node(
                row,
                &parser_kind(&["Tactic", "configItem"]),
                1,
                "rule configuration item",
            )?
            else {
                return Err(unsupported());
            };
            let Syntax::Node { kind, args, .. } = item else {
                return Err(unsupported());
            };
            let (name, flag, value) = if kind == &parser_kind(&["Tactic", "posConfigItem"])
                || kind == &parser_kind(&["Tactic", "negConfigItem"])
            {
                let [sign, Syntax::Ident { val, .. }] = args.as_slice() else {
                    return Err(unsupported());
                };
                let positive = kind == &parser_kind(&["Tactic", "posConfigItem"]);
                expect_atom(sign, if positive { "+" } else { "-" }, "rule option sign")?;
                (val, Some(positive), None)
            } else if kind == &parser_kind(&["Tactic", "valConfigItem"]) {
                let [open, Syntax::Ident { val, .. }, assign, value, close] = args.as_slice()
                else {
                    return Err(unsupported());
                };
                expect_atom(open, "(", "rule option opening")?;
                expect_atom(assign, ":=", "rule option assignment")?;
                expect_atom(close, ")", "rule option closing")?;
                (val, None, Some(value))
            } else {
                return Err(unsupported());
            };
            if name == &Name::from_components(["maxDepth"]) {
                if flag.is_some() {
                    return Err(unsupported());
                }
                let value = unparen(context, value.ok_or_else(unsupported)?)?;
                let [Syntax::Atom { val, .. }] = expect_node(
                    value,
                    &Name::from_components(["num"]),
                    1,
                    "literal rule iteration bound",
                )?
                else {
                    return Err(unsupported());
                };
                for _ in val.bytes() {
                    context.tick()?;
                }
                let Literal::Nat(n) = decode_natural(val)? else {
                    return Err(unsupported());
                };
                config.max_steps = match n.limbs_le() {
                    [] => 0,
                    [n] => usize::try_from(*n)
                        .map_err(|_| failure(SourceInferenceError::ResourceLimit))?,
                    _ => return Err(failure(SourceInferenceError::ResourceLimit)),
                };
            } else if name == &Name::from_components(["symm"])
                || name == &Name::from_components(["exfalso"])
                || (search
                    && (name == &Name::from_components(["intro"])
                        || name == &Name::from_components(["constructor"])))
            {
                // The pin's ConfigEval.evalBoolStx recognizes these syntax
                // literals directly, without looking up a same-named local.
                let enabled = match flag {
                    Some(flag) => flag,
                    None => match unparen(context, value.ok_or_else(unsupported)?)? {
                        Syntax::Ident { val, .. }
                            if val == &Name::from_components(["true"])
                                || val == &Name::from_components(["Bool", "true"]) =>
                        {
                            true
                        }
                        Syntax::Ident { val, .. }
                            if val == &Name::from_components(["false"])
                                || val == &Name::from_components(["Bool", "false"]) =>
                        {
                            false
                        }
                        _ => return Err(unsupported()),
                    },
                };
                if name == &Name::from_components(["symm"]) {
                    config.symm = enabled;
                } else if name == &Name::from_components(["exfalso"]) {
                    config.exfalso = enabled;
                } else if name == &Name::from_components(["intro"]) {
                    config.intro = enabled;
                } else {
                    config.constructor = enabled;
                }
            } else {
                return Err(unsupported());
            }
        }
        Ok(config)
    }
}

fn unparen<'a>(
    context: &mut Context,
    mut syntax: &'a Syntax,
) -> Result<&'a Syntax, NatDefinitionElabError> {
    while let Some(inner) = parenthesized_inner(syntax)? {
        context.tick()?;
        syntax = inner;
    }
    Ok(syntax)
}
