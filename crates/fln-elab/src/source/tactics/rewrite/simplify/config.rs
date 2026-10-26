//! The configuration slot of `simp`, `simp_all`, `simpa` and `dsimp` (`optConfig`), read as the
//! pin's `declare_config_elab` elaborators read it: item by item, left to right, over
//! `Lean.Meta.Simp.Config`, or `Lean.Meta.DSimp.Config` for `dsimp` (vendored
//! `src/Init/MetaTypes.lean:118-383`). `+f` and `-f` set a Boolean field, `(f := v)` sets it to a
//! Boolean literal, and `(config := { … })` resets every field to its default and then sets the
//! instance's fields.
//!
//! A field set to its declared default changes nothing and is accepted. `arith`, `decide` and
//! `failIfUnchanged` are honoured. Every other field set away from its default, a field the
//! structure does not declare, a value other than a Boolean literal, and any other configuration
//! term (`Lean.Meta.Simp.neutralConfig`, `{ c with … }`) remain this slot's typed refusal.
use super::*;

const EXPECTED: &str = "default simplification configuration";

/// The configuration fields this engine honours; every other field holds its default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::source) struct SimpConfig {
    /// `arith`: the linear normalization of `arith.rs`.
    pub(super) arith: bool,
    /// `decide`: closed decidable propositions become `True` or `False` (`decide.rs`).
    pub(super) decide: bool,
    /// `failIfUnchanged`: a call that changes nothing fails, rather than leaving its goal.
    pub(super) fail_if_unchanged: bool,
}

impl Default for SimpConfig {
    fn default() -> Self {
        Self {
            arith: false,
            decide: false,
            fail_if_unchanged: true,
        }
    }
}

/// `Simp.Config`'s Boolean fields with their declared defaults (`Init/MetaTypes.lean:231-381`).
/// `maxSteps`, `maxDischargeDepth`, `etaStruct` and `maxSuggestions` are not Boolean.
const SIMP_FIELDS: &[(&str, bool)] = &[
    ("contextual", false),
    ("memoize", true),
    ("singlePass", false),
    ("zeta", true),
    ("beta", true),
    ("eta", true),
    ("iota", true),
    ("proj", true),
    ("decide", false),
    ("arith", false),
    ("autoUnfold", false),
    ("dsimp", true),
    ("failIfUnchanged", true),
    ("ground", false),
    ("unfoldPartialApp", false),
    ("zetaDelta", false),
    ("index", true),
    ("implicitDefEqProofs", true),
    ("zetaUnused", true),
    ("catchRuntime", true),
    ("zetaHave", true),
    ("letToHave", true),
    ("congrConsts", true),
    ("bitVecOfNat", true),
    ("warnExponents", true),
    ("suggestions", false),
    ("locals", false),
    ("instances", false),
];

/// `DSimp.Config`'s Boolean fields with their declared defaults (`Init/MetaTypes.lean:125-200`).
/// It has no `arith`.
const DSIMP_FIELDS: &[(&str, bool)] = &[
    ("zeta", true),
    ("beta", true),
    ("eta", true),
    ("iota", true),
    ("proj", true),
    ("decide", false),
    ("autoUnfold", false),
    ("failIfUnchanged", true),
    ("unfoldPartialApp", false),
    ("zetaDelta", false),
    ("index", true),
    ("zetaUnused", true),
    ("zetaHave", true),
    ("locals", false),
    ("instances", false),
];

fn unsupported() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax { expected: EXPECTED }
}

impl Context {
    /// The configuration `config`, a tactic's `optConfig` slot (or the empty node of a tactic
    /// written without one), selects; `dsimp` reads `DSimp.Config`.
    pub(super) fn simp_config(
        &mut self,
        config: &Syntax,
        dsimp: bool,
    ) -> Result<SimpConfig, NatDefinitionElabError> {
        let items = match config {
            Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Tactic", "optConfig"]) => {
                let [items] = args.as_slice() else {
                    return Err(unsupported());
                };
                expect_null_args(items, EXPECTED)?
            }
            _ => {
                expect_empty_null(config, EXPECTED)?;
                return Ok(SimpConfig::default());
            }
        };
        let fields = if dsimp { DSIMP_FIELDS } else { SIMP_FIELDS };
        let mut config = SimpConfig::default();
        for item in items {
            self.tick()?;
            let [item] = expect_node(item, &parser_kind(&["Tactic", "configItem"]), 1, EXPECTED)?
            else {
                return Err(unsupported());
            };
            let Syntax::Node { kind, args, .. } = item else {
                return Err(unsupported());
            };
            if kind == &parser_kind(&["Tactic", "posConfigItem"])
                || kind == &parser_kind(&["Tactic", "negConfigItem"])
            {
                let [
                    Syntax::Atom { val: sign, .. },
                    Syntax::Ident { val: field, .. },
                ] = args.as_slice()
                else {
                    return Err(unsupported());
                };
                let value = match sign.as_str() {
                    "+" => true,
                    "-" => false,
                    _ => return Err(unsupported()),
                };
                set_field(&mut config, fields, field, value)?;
            } else if kind == &parser_kind(&["Tactic", "valConfigItem"]) {
                let [
                    Syntax::Atom { val: open, .. },
                    Syntax::Ident { val: field, .. },
                    Syntax::Atom { val: assign, .. },
                    value,
                    Syntax::Atom { val: close, .. },
                ] = args.as_slice()
                else {
                    return Err(unsupported());
                };
                if open != "(" || assign != ":=" || close != ")" {
                    return Err(unsupported());
                }
                if field == &Name::from_components(["config"]) {
                    config = SimpConfig::default();
                    for (field, value) in structure_fields(value).ok_or_else(unsupported)? {
                        self.tick()?;
                        set_field(&mut config, fields, &field, value)?;
                    }
                } else {
                    let value = bool_literal(value).ok_or_else(unsupported)?;
                    set_field(&mut config, fields, field, value)?;
                }
            } else {
                return Err(unsupported());
            }
        }
        Ok(config)
    }
}

/// Set `field` of a configuration declaring `fields` to `value`: an honoured field takes it, any
/// other field must keep its default.
fn set_field(
    config: &mut SimpConfig,
    fields: &[(&str, bool)],
    field: &Name,
    value: bool,
) -> Result<(), NatDefinitionElabError> {
    let Some(&(field, default)) = fields
        .iter()
        .find(|(declared, _)| field == &Name::from_components([*declared]))
    else {
        return Err(unsupported());
    };
    match field {
        "arith" => config.arith = value,
        "decide" => config.decide = value,
        "failIfUnchanged" => config.fail_if_unchanged = value,
        _ if value == default => {}
        _ => return Err(unsupported()),
    }
    Ok(())
}

/// `true` or `false`, as a configuration value.
fn bool_literal(value: &Syntax) -> Option<bool> {
    let Syntax::Ident { val, .. } = value else {
        return None;
    };
    if val == &Name::from_components(["true"]) || val == &Name::from_components(["Bool", "true"]) {
        Some(true)
    } else if val == &Name::from_components(["false"])
        || val == &Name::from_components(["Bool", "false"])
    {
        Some(false)
    } else {
        None
    }
}

/// The fields of a structure instance `{ f := v, … }` whose every value is a Boolean literal:
/// no source, no `..`, no type ascription, no binders. Anything else is `None`.
fn structure_fields(value: &Syntax) -> Option<Vec<(Name, bool)>> {
    let null = |syntax: &Syntax| -> Option<Vec<Syntax>> {
        match syntax {
            Syntax::Node { kind, args, .. } if kind == &Name::str(Name::anonymous(), "null") => {
                Some(args.clone())
            }
            _ => None,
        }
    };
    let node = |syntax: &Syntax, path: &[&str], arity: usize| -> Option<Vec<Syntax>> {
        match syntax {
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(path) && args.len() == arity =>
            {
                Some(args.clone())
            }
            _ => None,
        }
    };
    let atom =
        |syntax: &Syntax, text: &str| matches!(syntax, Syntax::Atom { val, .. } if val == text);
    let parts = node(value, &["Term", "structInst"], 6)?;
    if !atom(&parts[0], "{")
        || !null(&parts[1])?.is_empty()
        || !null(&parts[4])?.is_empty()
        || !atom(&parts[5], "}")
    {
        return None;
    }
    let ellipsis = node(&parts[3], &["Term", "optEllipsis"], 1)?;
    if !null(&ellipsis[0])?.is_empty() {
        return None;
    }
    let fields = node(&parts[2], &["Term", "structInstFields"], 1)?;
    let mut result = Vec::new();
    for field in null(&fields[0])? {
        // Fields are separated by `,` or by a line break, an empty node.
        if atom(&field, ",") || null(&field).is_some_and(|args| args.is_empty()) {
            continue;
        }
        let field = node(&field, &["Term", "structInstField"], 2)?;
        let lval = node(&field[0], &["Term", "structInstLVal"], 2)?;
        let Syntax::Ident { val: name, .. } = &lval[0] else {
            return None;
        };
        if !null(&lval[1])?.is_empty() {
            return None;
        }
        let [binders, ascription, definition]: [Syntax; 3] = null(&field[1])?.try_into().ok()?;
        if !null(&binders)?.is_empty() || !null(&ascription)?.is_empty() {
            return None;
        }
        let definition = node(&definition, &["Term", "structInstFieldDef"], 3)?;
        if !atom(&definition[0], ":=") || !null(&definition[1])?.is_empty() {
            return None;
        }
        result.push((name.clone(), bool_literal(&definition[2])?));
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every field the reader admits is declared by the pinned structure with that default; the
    /// honoured fields are among them; `DSimp.Config` declares no field `Simp.Config` lacks.
    #[test]
    fn field_tables_match_the_pinned_structures() {
        let declared = |table: &[(&str, bool)], field: &str| {
            table
                .iter()
                .find(|(name, _)| *name == field)
                .map(|(_, default)| *default)
        };
        assert_eq!(declared(SIMP_FIELDS, "arith"), Some(false));
        assert_eq!(declared(DSIMP_FIELDS, "arith"), None);
        for (field, default) in DSIMP_FIELDS {
            assert_eq!(declared(SIMP_FIELDS, field), Some(*default), "{field}");
        }
        for field in ["decide", "failIfUnchanged"] {
            assert!(declared(SIMP_FIELDS, field).is_some());
            assert!(declared(DSIMP_FIELDS, field).is_some());
        }
        let default = SimpConfig::default();
        assert_eq!(declared(SIMP_FIELDS, "arith"), Some(default.arith));
        assert_eq!(declared(SIMP_FIELDS, "decide"), Some(default.decide));
        assert_eq!(
            declared(SIMP_FIELDS, "failIfUnchanged"),
            Some(default.fail_if_unchanged)
        );
    }

    #[test]
    fn a_default_value_is_accepted_and_any_other_value_of_an_unhonoured_field_is_refused() {
        let mut config = SimpConfig::default();
        let field = |name: &str| Name::from_components([name]);
        set_field(&mut config, SIMP_FIELDS, &field("zeta"), true).unwrap();
        set_field(
            &mut config,
            SIMP_FIELDS,
            &field("implicitDefEqProofs"),
            true,
        )
        .unwrap();
        assert_eq!(config, SimpConfig::default());
        assert!(set_field(&mut config, SIMP_FIELDS, &field("zeta"), false).is_err());
        assert!(set_field(&mut config, SIMP_FIELDS, &field("unknownField"), false).is_err());
        assert!(set_field(&mut config, DSIMP_FIELDS, &field("arith"), true).is_err());
        set_field(&mut config, SIMP_FIELDS, &field("decide"), true).unwrap();
        set_field(&mut config, SIMP_FIELDS, &field("failIfUnchanged"), false).unwrap();
        assert!(config.decide && !config.fail_if_unchanged && !config.arith);
    }
}
