//! Source information needed by `split` after constructor matching has been lowered.
//!
//! The recursor fixes its minor order, independently of the written alternatives. This
//! transparent annotation retains only that lost order and the pattern's binder names.
//! It grants no proof authority: consumers validate the entire layout against the admitted
//! recursor before constructing ordinary, kernel-checked elimination terms.
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use fln_env::constants::RecursorVal;
use std::collections::HashSet;

pub(in crate::source) fn key() -> Name {
    Name::from_components(["FrankenLean", "splitMatch", "v1"])
}

fn constructor_key(index: usize) -> Name {
    Name::num(Name::str(key(), "constructor"), index as u64)
}

fn fields_key(index: usize) -> Name {
    Name::num(Name::str(key(), "fields"), index as u64)
}

pub(in crate::source) fn encode<'a>(
    alternatives: impl ExactSizeIterator<Item = (&'a Name, &'a [Option<Name>])>,
) -> KVMap {
    let mut data = KVMap::new();
    data.insert(key(), DataValue::OfNat(alternatives.len() as u64));
    for (index, (constructor, fields)) in alternatives.enumerate() {
        data.insert(
            constructor_key(index),
            DataValue::OfName(constructor.clone()),
        );
        data.insert(fields_key(index), DataValue::OfNat(fields.len() as u64));
        for (field, name) in fields.iter().enumerate() {
            data.insert(
                Name::num(fields_key(index), field as u64),
                DataValue::OfName(name.clone().unwrap_or_else(Name::anonymous)),
            );
        }
    }
    data
}

/// One alternative in source order. An anonymous field uses the constructor binder's name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::source) struct Alternative {
    pub(in crate::source) constructor: Name,
    pub(in crate::source) fields: Vec<Name>,
}

/// Bound association-list lookups by the admitted recursor's exact annotation schema.
/// Candidate discovery must apply this before looking for the marker, too.
pub(in crate::source) fn matches_schema_size(data: &KVMap, recursor: &RecursorVal) -> bool {
    let count = recursor.rules.len();
    if count == 0 || count > 256 {
        return false;
    }
    let Some(fields) = recursor.rules.iter().try_fold(0usize, |total, rule| {
        (rule.nfields <= 256).then_some(total + rule.nfields as usize)
    }) else {
        return false;
    };
    data.len() == 1 + 2 * count + fields
}

/// Refuse incomplete, duplicated, foreign or oversized layouts, including forged annotations
/// read from a module. Metadata never supplies constructor arities or extra alternatives.
pub(in crate::source) fn decode(data: &KVMap, recursor: &RecursorVal) -> Option<Vec<Alternative>> {
    if !matches_schema_size(data, recursor) {
        return None;
    }
    let DataValue::OfNat(count) = data.find(&key())? else {
        return None;
    };
    let count = usize::try_from(*count).ok()?;
    if count == 0 || count > 256 || count != recursor.rules.len() {
        return None;
    }
    let mut keys = HashSet::new();
    if data.entries().iter().any(|(name, _)| !keys.insert(name)) {
        return None;
    }
    let mut seen = HashSet::new();
    let mut alternatives = Vec::new();
    for index in 0..count {
        let DataValue::OfName(constructor) = data.find(&constructor_key(index))? else {
            return None;
        };
        if !seen.insert(constructor.clone()) {
            return None;
        }
        let rule = recursor
            .rules
            .iter()
            .find(|rule| &rule.ctor == constructor)?;
        let DataValue::OfNat(fields) = data.find(&fields_key(index))? else {
            return None;
        };
        if *fields > 256 || *fields != u64::from(rule.nfields) {
            return None;
        }
        let mut names = Vec::new();
        for field in 0..*fields {
            let DataValue::OfName(name) = data.find(&Name::num(fields_key(index), field))? else {
                return None;
            };
            names.push(name.clone());
        }
        alternatives.push(Alternative {
            constructor: constructor.clone(),
            fields: names,
        });
    }
    Some(alternatives)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::{Expr, ExprNode, FVarId};
    use fln_core::level::Level;
    use fln_env::constants::{ConstantVal, RecursorRule};

    fn name(label: &str) -> Name {
        Name::from_components(["Choice", label])
    }

    fn recursor() -> RecursorVal {
        RecursorVal {
            base: ConstantVal {
                name: name("rec"),
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            all: vec![Name::from_components(["Choice"])],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule {
                    ctor: name("empty"),
                    nfields: 0,
                    rhs: Expr::sort(Level::zero()),
                },
                RecursorRule {
                    ctor: name("value"),
                    nfields: 1,
                    rhs: Expr::sort(Level::zero()),
                },
            ],
            k: false,
            is_unsafe: false,
        }
    }

    fn annotation() -> KVMap {
        let alternatives = [
            (
                name("value"),
                vec![Some(Name::from_components(["payload"]))],
            ),
            (name("empty"), vec![]),
        ];
        encode(
            alternatives
                .iter()
                .map(|(name, fields)| (name, fields.as_slice())),
        )
    }

    #[test]
    fn source_order_and_names_survive_binder_substitution() {
        let data = annotation();
        let local = FVarId(Name::from_components(["input"]));
        let marked = Expr::mdata(data.clone(), Expr::fvar(local.clone()));
        let closed = marked.abstract_fvar(&local, 0).unwrap();
        let opened = closed
            .subst_loose(0, &[Expr::const_(name("empty"), vec![])])
            .unwrap();
        let ExprNode::MData { data: reopened, .. } = opened.node() else {
            panic!("match layout was lost during substitution");
        };
        let layout = decode(reopened, &recursor()).unwrap();
        assert_eq!(layout[0].constructor, name("value"));
        assert_eq!(layout[0].fields, [Name::from_components(["payload"])]);
        assert_eq!(layout[1].constructor, name("empty"));
        assert!(layout[1].fields.is_empty());
    }

    #[test]
    fn malformed_layouts_cannot_change_recursor_coverage_or_field_arity() {
        let recursor = recursor();
        assert!(decode(&KVMap::new(), &recursor).is_none());
        for (key, value) in [
            (constructor_key(1), DataValue::OfName(name("value"))),
            (constructor_key(0), DataValue::OfName(name("foreign"))),
            (fields_key(0), DataValue::OfNat(0)),
            (fields_key(1), DataValue::OfNat(1)),
            (key(), DataValue::OfNat(u64::MAX)),
        ] {
            let mut data = annotation();
            data.insert(key, value);
            assert!(decode(&data, &recursor).is_none());
        }
        let mut extra = annotation();
        extra.insert(
            Name::from_components(["unrelated"]),
            DataValue::OfBool(true),
        );
        assert!(decode(&extra, &recursor).is_none());
        let mut entries = annotation().entries().to_vec();
        entries[1] = entries[0].clone();
        assert!(decode(&KVMap::from_entries(entries), &recursor).is_none());
    }
}
