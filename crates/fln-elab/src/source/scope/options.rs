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
    row(
        "maxRecDepth",
        Nat(512),
        "Lean/Util/RecDepth.lean:15",
        AtLeastDefault,
    ),
    // This engine has no auto-bound implicits: `false` makes the pin do what it does, and
    // `true` is the pin's default.
    row(
        "autoImplicit",
        Bool(true),
        "Lean/Elab/AutoBound.lean:17",
        Inert("this engine never auto-binds an unknown identifier"),
    ),
    row(
        "relaxedAutoImplicit",
        Bool(true),
        "Lean/Elab/AutoBound.lean:22",
        Inert("it refines auto-bound implicits, which this engine never makes"),
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
    row(
        "linter.all",
        Bool(false),
        "Lean/Linter/Init.lean:99",
        Silent,
    ),
    row(
        "linter.unusedVariables",
        Bool(true),
        "Lean/Linter/UnusedVariables.lean:84",
        Silent,
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
        Silent,
    ),
    row(
        "linter.constructorNameAsVariable",
        Bool(true),
        "Lean/Linter/ConstructorAsVariable.lean:25",
        Silent,
    ),
    row("warn.sorry", Bool(true), "Lean/AddDecl.lean:69", Silent),
    row(
        "warn.classDefReducibility",
        Bool(true),
        "Lean/Elab/MutualDef.lean:1180",
        Silent,
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
        DefaultOnly,
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

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Name {
        Name::from_components(s.split('.'))
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
        assert_eq!(
            admitted("linter.unusedVariables", DataValue::OfBool(false)),
            Ok(Effect::NoChange)
        );
        assert_eq!(
            admitted("linter.unusedVariables", DataValue::OfBool(true)),
            Ok(Effect::NoChange)
        );
        // Off by default: switching it on would print what this engine does not.
        assert!(matches!(
            admitted("linter.missingDocs", DataValue::OfBool(true)),
            Err(OptionRefusal::Unsupported { .. })
        ));
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
            Ok(Effect::NoChange)
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
            .filter(|row| matches!(row.policy, Honored | HonoredAtLeast { .. }))
            .map(|row| row.name)
            .collect();
        assert_eq!(honored, ["autoLift", "maxHeartbeats"]);
    }
}
