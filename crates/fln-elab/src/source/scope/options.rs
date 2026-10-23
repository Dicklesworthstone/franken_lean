//! `set_option`'s one table (bead `fln-set-option-t69b`). An option is admitted only where this
//! engine then behaves as the pin does with it set: the option is honored, or it is left at the
//! pin's default, or it switches off something this engine never does. Every other option or
//! value is refused by name, never ignored. Each row cites the pin's declaration in the vendored
//! sources (`vendor/lean4-src/src`), and a test reads those declarations to keep the types and
//! defaults here from drifting.
use fln_core::name::Name;
use fln_core::options::DataValue;

/// What admitting an option does here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    /// Recorded in the scope's options, where its reader finds it.
    Honored,
    /// Nothing here changes, which is what the pin's own change amounts to for this engine.
    NoChange,
}

/// Why `set_option` was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptionRefusal {
    /// No row: the option may exist at the pin, but this engine cannot say what it would do.
    Unknown { name: Name },
    /// The value is not of the option's type (the pin refuses this too).
    WrongType { name: Name, expected: &'static str },
    /// The value would make the pin behave differently, and this engine does not.
    Unsupported {
        name: Name,
        value: DataValue,
        reason: &'static str,
    },
}

impl std::fmt::Display for OptionRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown { name } => write!(
                f,
                "set_option `{}`: no option row, so it is refused rather than ignored",
                name.to_display_string()
            ),
            Self::WrongType { name, expected } => write!(
                f,
                "set_option `{}`: the value is not a {expected}",
                name.to_display_string()
            ),
            Self::Unsupported {
                name,
                value,
                reason,
            } => write!(
                f,
                "set_option `{}` {}: {reason}",
                name.to_display_string(),
                show(value)
            ),
        }
    }
}

fn show(value: &DataValue) -> String {
    match value {
        DataValue::OfBool(value) => value.to_string(),
        DataValue::OfNat(value) => value.to_string(),
        DataValue::OfString(value) => format!("{value:?}"),
        other => format!("{other:?}"),
    }
}

/// An option's type and the pin's `defValue`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinDefault {
    Bool(bool),
    Nat(u64),
}

/// How a row decides a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Policy {
    /// Read by this engine from the scope's options: every value of the type is admitted.
    Honored,
    /// Read by this engine, but only at or above `floor`, or `0` when `zero` is set: a ceiling
    /// below the floor would stop the pin where this engine does not stop.
    HonoredAtLeast { floor: u64, zero: bool },
    /// Read by this engine, at its default or `false` only: switching it on would make the pin
    /// print output this engine does not produce.
    HonoredOff,
    /// Controls output this engine never produces (a linter or a warning). Switching it off,
    /// or leaving it at the default, changes nothing here; switching on what is off by
    /// default would make the pin print what this engine does not.
    Silent,
    /// No value changes anything this engine does; the row says why.
    Inert(&'static str),
    /// A limit this engine does not reach at the pin's default: raising it changes nothing,
    /// lowering it would stop the pin where this engine does not stop.
    AtLeastDefault,
    /// Changes what the pin prints or does in a way this engine does not implement: only the
    /// default is admitted.
    DefaultOnly,
}

/// One option: its name, its type and default, where the pin declares it, and the policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Row {
    pub name: &'static str,
    pub default: PinDefault,
    /// `path:line` of its `register_builtin_option`, under `vendor/lean4-src/src`.
    pub declared_at: &'static str,
    pub policy: Policy,
}

const fn row(
    name: &'static str,
    default: PinDefault,
    declared_at: &'static str,
    policy: Policy,
) -> Row {
    Row {
        name,
        default,
        declared_at,
        policy,
    }
}

use PinDefault::{Bool, Nat};
use Policy::*;

/// The table, in one place. `maxRecDepth`'s default is `defaultMaxRecDepth`, 512
/// (`Init/Prelude.lean`).
pub const ROWS: &[Row] = &[
    // Simp may re-synthesize occurrence-assigned theorem dictionaries.
    row(
        "tactic.skipAssignedInstances",
        Bool(true),
        "Lean/Meta/Tactic/Util.lean:176",
        Honored,
    ),
    // Read by the elaborator's monad-lift coercion (`coercions/monad.rs`).
    row("autoLift", Bool(true), "Lean/Meta/Coe.lean:72", Honored),
    // Read by Golem at command entry for `#eval`. Elaboration does not count the pin's
    // heartbeats, so a ceiling below the default is refused rather than half honored.
    row(
        "maxHeartbeats",
        Nat(200_000),
        "Lean/CoreM.lean:30",
        HonoredAtLeast {
            floor: 200_000,
            zero: true,
        },
    ),
    row(
        "synthInstance.maxHeartbeats",
        Nat(20_000),
        "Lean/Meta/SynthInstance.lean:19",
        AtLeastDefault,
    ),
    // Both instance search strategies count every consumed dictionary,
    // including repeated table answers (SynthInstance.addAnswer/resume).
    row(
        "synthInstance.maxSize",
        Nat(128),
        "Lean/Meta/SynthInstance.lean:24",
        Honored,
    ),
    row(
        "maxRecDepth",
        Nat(512),
        "Lean/Util/RecDepth.lean:15",
        AtLeastDefault,
    ),
    // Read by a definition header (`auto_bound_name` in source.rs).
    row(
        "autoImplicit",
        Bool(true),
        "Lean/Elab/AutoBound.lean:17",
        Honored,
    ),
    row(
        "relaxedAutoImplicit",
        Bool(true),
        "Lean/Elab/AutoBound.lean:22",
        Inert(
            "this engine auto-binds only strict names (one character and a suffix) either way; \
             `false` is exactly that, and under `true` it binds a subset of the pin's names",
        ),
    ),
    row(
        "Elab.async",
        Bool(false),
        "Lean/CoreM.lean:35",
        Inert("it schedules elaboration; this engine's results do not depend on scheduling"),
    ),
    row(
        "diagnostics.threshold",
        Nat(20),
        "Lean/CoreM.lean:25",
        Inert("it filters `diagnostics` output, which is refused unless off"),
    ),
    row(
        "guard_msgs.diff",
        Bool(true),
        "Lean/Elab/GuardMsgs.lean:25",
        Inert("it formats `#guard_msgs` failures, and `#guard_msgs` is not implemented"),
    ),
    // `linter.all` is the default of every linter option left unset (`getLinterAll`), so the
    // unused-variables linter reads it; switching it on would switch on linters this engine
    // does not have.
    row(
        "linter.all",
        Bool(false),
        "Lean/Linter/Init.lean:99",
        HonoredOff,
    ),
    row(
        "linter.unusedVariables",
        Bool(true),
        "Lean/Linter/UnusedVariables.lean:84",
        Honored,
    ),
    row(
        "linter.unusedSimpArgs",
        Bool(true),
        "Lean/Elab/Tactic/Simp.lean:675",
        Silent,
    ),
    row(
        "linter.missingDocs",
        Bool(false),
        "Lean/Linter/MissingDocs.lean:20",
        Silent,
    ),
    row(
        "linter.deprecated",
        Bool(true),
        "Lean/Linter/Deprecated.lean:19",
        Honored,
    ),
    row(
        "linter.defProp",
        Bool(true),
        "Lean/Linter/DefProp.lean:26",
        Honored,
    ),
    row(
        "linter.constructorNameAsVariable",
        Bool(true),
        "Lean/Linter/ConstructorAsVariable.lean:25",
        Silent,
    ),
    // The remaining builtin linters the pin's tests/elab files set (2026-10-12): each only
    // warns, so `false` or the default changes nothing here.
    row(
        "linter.loopingSimpArgs",
        Bool(false),
        "Lean/Meta/Tactic/Simp/LoopProtection.lean:17",
        Silent,
    ),
    row(
        "linter.deprecated.options",
        Bool(true),
        "Lean/Elab/SetOption.lean:15",
        Silent,
    ),
    row(
        "linter.unusedSectionVars",
        Bool(true),
        "Lean/Elab/MutualDef.lean:497",
        Silent,
    ),
    row(
        "linter.omit",
        Bool(false),
        "Lean/Linter/Omit.lean:17",
        Silent,
    ),
    row(
        "linter.redundantVisibility",
        Bool(false),
        "Lean/Elab/DeclModifiers.lean:17",
        Silent,
    ),
    row(
        "linter.tacticCheckInstances",
        Bool(false),
        "Lean/Linter/TacticTypeCheck.lean:24",
        Silent,
    ),
    row(
        "linter.indexVariables",
        Bool(false),
        "Lean/Linter/List.lean:31",
        Silent,
    ),
    row(
        "linter.deprecated.arg",
        Bool(true),
        "Lean/Elab/DeprecatedArg.lean:18",
        Silent,
    ),
    row(
        "linter.tactic.docsOnAlt",
        Bool(true),
        "Lean/Linter/DocsOnAlt.lean:21",
        Silent,
    ),
    row(
        "linter.suspiciousUnexpanderPatterns",
        Bool(true),
        "Lean/Linter/Builtin.lean:16",
        Silent,
    ),
    row(
        "linter.unusedVariables.funArgs",
        Bool(true),
        "Lean/Linter/UnusedVariables.lean:89",
        Honored,
    ),
    row(
        "linter.unusedVariables.patternVars",
        Bool(true),
        "Lean/Linter/UnusedVariables.lean:94",
        Honored,
    ),
    row(
        "linter.deprecated.syntax",
        Bool(true),
        "Lean/Elab/DeprecatedSyntax.lean:17",
        Silent,
    ),
    row(
        "linter.tactic.unusedName",
        Bool(true),
        "Lean/Elab/Tactic/Lets.lean:25",
        Silent,
    ),
    row(
        "linter.extra.unusedDecidableInType",
        Bool(false),
        "Lean/Linter/Extra/UnusedDecidableInType.lean:120",
        Silent,
    ),
    row(
        "linter.deprecatedCoercions",
        Bool(true),
        "Lean/Linter/Coe.lean:23",
        Silent,
    ),
    row(
        "linter.listVariables",
        Bool(false),
        "Lean/Linter/List.lean:40",
        Silent,
    ),
    row(
        "linter.checkUnivs",
        Bool(true),
        "Lean/Linter/CheckUnivs.lean:29",
        Silent,
    ),
    // Read by the source executor: a declaration that uses `sorry` warns while it is true.
    row("warn.sorry", Bool(true), "Lean/AddDecl.lean:69", Honored),
    // Read by the source executor: a class-typed `def` without a reducibility attribute warns
    // while it is true.
    row(
        "warn.classDefReducibility",
        Bool(true),
        "Lean/Elab/MutualDef.lean:1180",
        Honored,
    ),
    row(
        "mvcgen.warning",
        Bool(true),
        "Lean/Elab/Tactic/Do/VCGen/Basic.lean:23",
        Silent,
    ),
    row(
        "grind.warning",
        Bool(false),
        "Lean/Meta/Tactic/Grind/Types.lean:77",
        Silent,
    ),
    row(
        "structureDiamondWarning",
        Bool(false),
        "Lean/Elab/Structure.lean:21",
        Silent,
    ),
    row("diagnostics", Bool(false), "Lean/CoreM.lean:18", Silent),
    row(
        "backward.do.legacy",
        Bool(false),
        "Lean/Elab/Do/Switch.lean:17",
        DefaultOnly,
    ),
    row(
        "doc.verso",
        Bool(false),
        "Lean/DocString/Extension.lean:71",
        DefaultOnly,
    ),
    row(
        "hygiene",
        Bool(true),
        "Lean/Elab/Quotation/Util.lean:16",
        DefaultOnly,
    ),
    row(
        "pp.all",
        Bool(false),
        "Lean/PrettyPrinter/Delaborator/Options.lean:19",
        DefaultOnly,
    ),
    row(
        "pp.universes",
        Bool(false),
        "Lean/PrettyPrinter/Delaborator/Options.lean:56",
        DefaultOnly,
    ),
    row(
        "pp.mvars",
        Bool(true),
        "Lean/PrettyPrinter/Delaborator/Options.lean:109",
        Inert(
            "it names metavariables in output, and this engine prints none: the printer \
             refuses them, and the one message that shows one spells it `?_`, the pin's \
             spelling with this option off",
        ),
    ),
    row(
        "pp.explicit",
        Bool(false),
        "Lean/PrettyPrinter/Delaborator/Options.lean:163",
        DefaultOnly,
    ),
    row(
        "pp.proofs",
        Bool(false),
        "Lean/PrettyPrinter/Delaborator/Options.lean:179",
        DefaultOnly,
    ),
];

/// The row for `name`, if this engine has one.
pub fn row_for(name: &Name) -> Option<&'static Row> {
    let spelled = name.to_display_string();
    ROWS.iter().find(|row| row.name == spelled)
}

/// Decide `set_option name value`.
pub fn admit(name: &Name, value: &DataValue) -> Result<Effect, OptionRefusal> {
    let row = row_for(name).ok_or_else(|| OptionRefusal::Unknown { name: name.clone() })?;
    let unsupported = |reason| OptionRefusal::Unsupported {
        name: name.clone(),
        value: value.clone(),
        reason,
    };
    let at_default = match (row.default, value) {
        (Bool(default), DataValue::OfBool(value)) => default == *value,
        (Nat(default), DataValue::OfNat(value)) => default == *value,
        (Bool(_), _) => {
            return Err(OptionRefusal::WrongType {
                name: name.clone(),
                expected: "Bool",
            });
        }
        (Nat(_), _) => {
            return Err(OptionRefusal::WrongType {
                name: name.clone(),
                expected: "Nat",
            });
        }
    };
    match row.policy {
        Honored => Ok(Effect::Honored),
        HonoredAtLeast { floor, zero } => match value {
            DataValue::OfNat(value) if *value >= floor || (zero && *value == 0) => {
                Ok(Effect::Honored)
            }
            _ => Err(unsupported(
                "a ceiling below the pin's default would stop the pin where this engine does not",
            )),
        },
        Inert(_) => Ok(Effect::NoChange),
        HonoredOff if at_default || *value == DataValue::OfBool(false) => Ok(Effect::Honored),
        HonoredOff => Err(unsupported(
            "it would make the pin print output this engine does not produce",
        )),
        Silent if at_default || *value == DataValue::OfBool(false) => Ok(Effect::NoChange),
        Silent => Err(unsupported(
            "it would make the pin print output this engine does not produce",
        )),
        AtLeastDefault => match (row.default, value) {
            (Nat(default), DataValue::OfNat(value)) if *value >= default => Ok(Effect::NoChange),
            _ => Err(unsupported(
                "a limit below the pin's default would stop the pin where this engine does not",
            )),
        },
        DefaultOnly if at_default => Ok(Effect::NoChange),
        DefaultOnly => Err(unsupported(
            "only the pin's default is admitted: this engine does not implement the change",
        )),
    }
}

impl crate::source::Context {
    /// The pinned term and tactic `set_option` nodes have the same six fields
    /// (`Parser/Command.lean`). Values are syntax data, never elaborated terms:
    /// resolving an identifier or synthesizing OfNat here would change them.
    pub(in crate::source) fn enter_source_options<'a>(
        &mut self,
        args: &'a [fln_syntax::tree::Syntax],
    ) -> Result<
        (&'a fln_syntax::tree::Syntax, fln_core::options::KVMap),
        crate::NatDefinitionElabError,
    > {
        use crate::source::{SourceInferenceError, failure};
        use crate::{NatDefinitionElabError, expect_atom, expect_empty_null};
        use fln_core::expr::Literal;
        use fln_syntax::tree::Syntax;

        let malformed = || NatDefinitionElabError::UnexpectedSyntax {
            expected: "set_option name value in body",
        };
        let [
            keyword,
            Syntax::Ident { val: name, .. },
            trailing,
            value,
            separator,
            body,
        ] = args
        else {
            return Err(malformed());
        };
        expect_atom(keyword, "set_option", "scoped option keyword")?;
        expect_empty_null(trailing, "complete option name")?;
        expect_atom(separator, "in", "scoped option separator")?;
        let value = match value {
            Syntax::Atom { val, .. } if val == "true" || val == "false" => {
                DataValue::OfBool(val == "true")
            }
            Syntax::Node { kind, args, .. } if kind == &Name::from_components(["num"]) => {
                let [Syntax::Atom { val, .. }] = args.as_slice() else {
                    return Err(malformed());
                };
                let Literal::Nat(value) = crate::decode_natural(val)? else {
                    unreachable!("natural decoder");
                };
                DataValue::OfNat(value.to_u64().ok_or_else(malformed)?)
            }
            Syntax::Node { kind, args, .. } if kind == &Name::from_components(["str"]) => {
                let [Syntax::Atom { val, .. }] = args.as_slice() else {
                    return Err(malformed());
                };
                let Literal::Str(value) = crate::decode_string(val)? else {
                    unreachable!("string decoder");
                };
                DataValue::OfString(value)
            }
            _ => return Err(malformed()),
        };
        let effect =
            admit(name, &value).map_err(|error| failure(SourceInferenceError::Option(error)))?;
        let saved = self.txn.options.clone();
        if effect == Effect::Honored {
            self.txn.options.insert(name.clone(), value);
        }
        Ok((body, saved))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::NatDefinitionElabError;
    use crate::source::{Context, SourceInferenceError, parser_kind};
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_env::environment::Environment;
    use fln_kernel::verdict::Budget;
    use fln_syntax::tree::Syntax;

    fn n(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }

    #[test]
    fn failed_option_scopes_restore_the_map_without_refunding_exhausted_work() {
        for (body, kind, exhausted) in [
            (
                "set_option autoLift false in set_option autoLift true in missing",
                "set_option",
                false,
            ),
            (
                "by first | set_option autoLift false in repeat skip | skip",
                "byTactic",
                true,
            ),
        ] {
            let source = format!("theorem t : Prop := {body}");
            let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
            let mut pending = vec![parsed.syntax()];
            let syntax = loop {
                let syntax = pending.pop().expect("scoped term");
                if syntax.kind() == Some(&parser_kind(&["Term", kind])) {
                    break syntax;
                }
                if let Syntax::Node { args, .. } = syntax {
                    pending.extend(args.iter().rev());
                }
            };
            let mut context =
                Context::new(&Environment::new(), Budget::for_stack_bytes(128 * 1024));
            context
                .txn
                .options
                .insert(n("autoLift"), DataValue::OfBool(true));
            context
                .txn
                .options
                .insert(n("maxHeartbeats"), DataValue::OfNat(400_000));
            context.txn.budget.max_heartbeats = 400;
            let options = context.txn.options.clone();
            let result = context.term(syntax, Some(Expr::sort(Level::zero())));
            assert_eq!(context.txn.options, options, "{body}");
            if exhausted {
                assert!(
                    matches!(
                        result,
                        Err(NatDefinitionElabError::Inference(
                            SourceInferenceError::ResourceLimit
                        ))
                    ),
                    "{body}: {:?}",
                    result.as_ref().err()
                );
                assert!(context.txn.budget.heartbeats_consumed > 400);
            } else {
                assert!(
                    matches!(
                        result,
                        Err(NatDefinitionElabError::Inference(
                            SourceInferenceError::UnknownConstant(_)
                        ))
                    ),
                    "{body}: {:?}",
                    result.as_ref().err()
                );
                assert!(context.txn.budget.heartbeats_consumed > 0);
            }
        }
    }

    #[test]
    fn each_policy_admits_and_refuses_as_stated() {
        let admitted = |name: &str, value: DataValue| admit(&n(name), &value);
        assert_eq!(
            admitted("autoLift", DataValue::OfBool(false)),
            Ok(Effect::Honored)
        );
        assert_eq!(
            admitted("maxHeartbeats", DataValue::OfNat(400_000)),
            Ok(Effect::Honored)
        );
        assert_eq!(
            admitted("maxHeartbeats", DataValue::OfNat(0)),
            Ok(Effect::Honored)
        );
        assert!(matches!(
            admitted("maxHeartbeats", DataValue::OfNat(1_000)),
            Err(OptionRefusal::Unsupported { .. })
        ));
        // The unused-variables linter reads its options, and `linter.all` while it is off.
        for (name, value) in [
            ("linter.unusedVariables", false),
            ("linter.unusedVariables", true),
            ("linter.unusedVariables.funArgs", false),
            ("linter.all", false),
        ] {
            assert_eq!(
                admitted(name, DataValue::OfBool(value)),
                Ok(Effect::Honored),
                "{name} {value}"
            );
        }
        assert!(matches!(
            admitted("linter.all", DataValue::OfBool(true)),
            Err(OptionRefusal::Unsupported { .. })
        ));
        // Off by default: switching it on would print what this engine does not.
        assert!(matches!(
            admitted("linter.missingDocs", DataValue::OfBool(true)),
            Err(OptionRefusal::Unsupported { .. })
        ));
        // The same holds for every builtin linter row: a default-off one may only stay off,
        // a default-on one may be switched off or left on.
        for (name, value, admits) in [
            ("linter.omit", false, true),
            ("linter.omit", true, false),
            ("linter.unusedSectionVars", false, true),
            ("linter.unusedSectionVars", true, true),
        ] {
            assert_eq!(
                admitted(name, DataValue::OfBool(value)).is_ok(),
                admits,
                "{name} {value}"
            );
        }
        assert!(matches!(
            admitted("diagnostics", DataValue::OfBool(true)),
            Err(OptionRefusal::Unsupported { .. })
        ));
        assert_eq!(
            admitted("pp.all", DataValue::OfBool(false)),
            Ok(Effect::NoChange)
        );
        assert!(matches!(
            admitted("pp.all", DataValue::OfBool(true)),
            Err(OptionRefusal::Unsupported { .. })
        ));
        // No metavariable name is ever printed here, so either spelling is the pin's.
        assert_eq!(
            admitted("pp.mvars", DataValue::OfBool(false)),
            Ok(Effect::NoChange)
        );
        assert_eq!(
            admitted("maxRecDepth", DataValue::OfNat(10_000)),
            Ok(Effect::NoChange)
        );
        assert!(matches!(
            admitted("maxRecDepth", DataValue::OfNat(100)),
            Err(OptionRefusal::Unsupported { .. })
        ));
        assert_eq!(
            admitted("autoImplicit", DataValue::OfBool(false)),
            Ok(Effect::Honored)
        );
        assert!(matches!(
            admitted("trace.Meta.synthInstance", DataValue::OfBool(true)),
            Err(OptionRefusal::Unknown { .. })
        ));
        assert!(matches!(
            admitted("maxHeartbeats", DataValue::OfBool(true)),
            Err(OptionRefusal::WrongType {
                expected: "Nat",
                ..
            })
        ));
        assert!(matches!(
            admitted("autoLift", DataValue::OfNat(1)),
            Err(OptionRefusal::WrongType {
                expected: "Bool",
                ..
            })
        ));
        assert!(matches!(
            admitted("autoLift", DataValue::OfString("true".into())),
            Err(OptionRefusal::WrongType { .. })
        ));
    }

    /// Each row is bound to the pin's own declaration: the cited line in the vendored sources
    /// opens `register_builtin_option <name> : <type> := {`, and its `defValue` is the row's.
    /// A row whose declaration moves, or whose default the pin changes, fails here.
    #[test]
    fn every_row_is_the_pins_declaration() {
        let sources = fln_core::checked_workspace_root!().join("vendor/lean4-src/src");
        for row in ROWS {
            let (path, line) = row.declared_at.rsplit_once(':').expect("path:line");
            let line: usize = line.parse().expect("a line number");
            let text = std::fs::read_to_string(sources.join(path))
                .unwrap_or_else(|error| panic!("{}: {error}", row.declared_at));
            let declaration: Vec<_> = text.lines().skip(line - 1).take(12).collect();
            let (expected_type, expected_value) = match row.default {
                Bool(value) => ("Bool", value.to_string()),
                Nat(value) => ("Nat", value.to_string()),
            };
            assert_eq!(
                declaration.first().map(|first| first.trim_end()),
                Some(
                    format!(
                        "register_builtin_option {} : {expected_type} := {{",
                        row.name
                    )
                    .as_str()
                ),
                "{}",
                row.declared_at
            );
            let value = declaration
                .iter()
                .find_map(|line| line.trim().strip_prefix("defValue"))
                .and_then(|rest| rest.trim().strip_prefix(":="))
                .map(|value| value.trim().trim_end_matches(',').to_owned())
                .unwrap_or_else(|| panic!("{}: no defValue", row.declared_at));
            // `maxRecDepth`'s default is a named constant; read it where the pin defines it.
            let value = if value == "defaultMaxRecDepth" {
                let prelude = std::fs::read_to_string(sources.join("Init/Prelude.lean")).unwrap();
                let at = prelude
                    .find("def defaultMaxRecDepth")
                    .expect("Init.Prelude defines defaultMaxRecDepth");
                prelude[at..]
                    .split(":=")
                    .nth(1)
                    .and_then(|rest| rest.split_whitespace().next())
                    .expect("its value")
                    .to_owned()
            } else {
                value
            };
            assert_eq!(value, expected_value, "{}", row.declared_at);
        }
    }

    #[test]
    fn names_are_unique_and_honored_rows_are_the_ones_this_engine_reads() {
        let mut names: Vec<_> = ROWS.iter().map(|row| row.name).collect();
        names.sort_unstable();
        let before = names.len();
        names.dedup();
        assert_eq!(names.len(), before, "a name has two rows");
        let honored: Vec<_> = ROWS
            .iter()
            .filter(|row| matches!(row.policy, Honored | HonoredAtLeast { .. } | HonoredOff))
            .map(|row| row.name)
            .collect();
        // `tactic.skipAssignedInstances`: matching/instance_args.rs;
        // source_simp_instance_matching exercises both values.
        // `autoImplicit`: `auto_bound_name` (source.rs); `source_auto_bound_implicits` sets it false.
        // `linter.*`: the unused-variables, deprecated-syntax and defProp warnings (`fln`,
        // `unused_variables.rs` and `linters.rs`); `unused_variables_lint` sets each one.
        // `warn.sorry`: the source executor's "declaration uses `sorry`" warning (`fln`,
        // `execute_source_command_stream`); `sorry_is_admitted_with_the_pins_warnings` sets it false.
        // `warn.classDefReducibility`: the class-typed `def` warning (`fln`, `linters.rs`);
        // `class_def_reducibility` sets it false.
        assert_eq!(
            honored,
            [
                "tactic.skipAssignedInstances",
                "autoLift",
                "maxHeartbeats",
                "synthInstance.maxSize",
                "autoImplicit",
                "linter.all",
                "linter.unusedVariables",
                "linter.deprecated",
                "linter.defProp",
                "linter.unusedVariables.funArgs",
                "linter.unusedVariables.patternVars",
                "warn.sorry",
                "warn.classDefReducibility"
            ]
        );
    }
}
