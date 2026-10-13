//! Exact monomorphic constant aliases into the existing completed-value memo.
//!
//! Materialization may put the same constant in different generated arenas.
//! These names are an index, not another value cache: an alias is published only
//! after its cursor has a retained, completed natural value. Name/entry ceilings
//! bound this optional index; no query context or universe argument is omitted.
use super::super::{Control, Cursor, Halt, NamePart, WireName};
use std::collections::HashMap;

const MAX_ALIASES: usize = 4_096;
const MAX_NAME_UNITS: usize = 65_536;

#[derive(Default)]
pub(super) struct Names {
    entries: HashMap<WireName, Cursor>,
    units: usize,
}

/// Price exact structural hashing and equality before either is performed.
/// WireName clones shared immutable storage, not the name's text. Oversized
/// names simply use the ordinary cursor cache; they do not acquire a new limit.
fn priced_name(
    name: &WireName,
    cursor: Cursor,
    control: &mut Control<'_>,
) -> Result<Option<usize>, Halt> {
    control.step(cursor.root.index())?;
    let mut units = 0_usize;
    for part in name.parts() {
        control.step(cursor.root.index())?;
        units = units.saturating_add(1).saturating_add(match part {
            NamePart::Text(text) => text.len(),
            NamePart::Numeric { .. } => 0,
        });
        if units > MAX_NAME_UNITS {
            return Ok(None);
        }
    }
    for _ in 0..units {
        control.step(cursor.root.index())?;
    }
    Ok(Some(units))
}

impl Names {
    pub(super) fn recall(
        &self,
        name: &WireName,
        cursor: Cursor,
        control: &mut Control<'_>,
    ) -> Result<Option<Cursor>, Halt> {
        if priced_name(name, cursor, control)?.is_none() {
            return Ok(None);
        }
        Ok(self.entries.get(name).copied())
    }

    pub(super) fn remember(
        &mut self,
        name: &WireName,
        cursor: Cursor,
        control: &mut Control<'_>,
    ) -> Result<(), Halt> {
        let Some(units) = priced_name(name, cursor, control)? else {
            return Ok(());
        };
        if self.entries.len() >= MAX_ALIASES
            || units > MAX_NAME_UNITS.saturating_sub(self.units)
            || self.entries.contains_key(name)
        {
            return Ok(());
        }
        if self.entries.try_reserve(1).is_err() {
            return Ok(());
        }
        self.entries.insert(name.clone(), cursor);
        self.units += units;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::{ArenaSource, ExprId, NatReductionBudget, NatValue};
    use super::super::{MAX_ENTRIES, NaturalMemo};
    use super::*;
    use std::sync::Arc;

    fn cursor(n: usize) -> Cursor {
        Cursor {
            source: ArenaSource::Candidate,
            root: ExprId::from_index(n).unwrap(),
        }
    }
    fn name(text: &str) -> WireName {
        WireName::from_parts(vec![NamePart::Text(text.into())])
    }
    fn complete<T>(result: Result<T, Halt>) -> T {
        result.unwrap_or_else(|_| panic!("unexpected memo stop"))
    }

    #[test]
    fn aliases_reuse_exact_names_and_the_same_immutable_value() {
        let mut memo = NaturalMemo::default();
        let mut never = || false;
        let mut control = Control::new(NatReductionBudget::unlimited(), &mut never);
        let first = name("A.B");
        let structured =
            WireName::from_parts(vec![NamePart::Text("A".into()), NamePart::Text("B".into())]);
        let value = Arc::new(NatValue::from_u64(7));
        complete(memo.remember_operand(cursor(0), Some(&first), &value, &mut control));
        let repeated = Cursor {
            source: ArenaSource::Generated(2),
            root: cursor(99).root,
        };
        let recalled = complete(memo.recall_operand(repeated, Some(&first), &mut control)).unwrap();
        assert!(Arc::ptr_eq(&recalled, &value));
        assert!(complete(memo.recall_operand(repeated, Some(&structured), &mut control)).is_none());
        assert!(complete(memo.recall_operand(repeated, None, &mut control)).is_none());
        assert_eq!(memo.entries.len(), 1);
    }

    #[test]
    fn name_retention_is_bounded_and_never_replaces_an_alias() {
        let mut names = Names::default();
        let mut never = || false;
        let mut control = Control::new(NatReductionBudget::unlimited(), &mut never);
        let exact = name(&"x".repeat(MAX_NAME_UNITS - 1));
        complete(names.remember(&exact, cursor(0), &mut control));
        assert_eq!(names.units, MAX_NAME_UNITS);
        complete(names.remember(&name("another"), cursor(1), &mut control));
        complete(names.remember(&exact, cursor(2), &mut control));
        assert_eq!(names.entries.len(), 1);
        assert!(complete(names.recall(&exact, cursor(7), &mut control)) == Some(cursor(0)));
        assert!(
            complete(names.recall(&name(&"x".repeat(MAX_NAME_UNITS)), cursor(7), &mut control))
                .is_none()
        );
        let mut names = Names::default();
        for n in 0..=MAX_ALIASES {
            complete(names.remember(&name(&n.to_string()), cursor(n), &mut control));
        }
        assert_eq!(names.entries.len(), MAX_ALIASES);
    }

    #[test]
    fn a_full_value_cache_cannot_create_a_dangling_name_alias() {
        let mut memo = NaturalMemo::default();
        let mut never = || false;
        let mut control = Control::new(NatReductionBudget::unlimited(), &mut never);
        let value = Arc::new(NatValue::one());
        for n in 0..MAX_ENTRIES {
            complete(memo.remember(cursor(n), &value, &mut control));
        }
        let absent = name("full");
        complete(memo.remember_operand(cursor(MAX_ENTRIES), Some(&absent), &value, &mut control));
        assert!(memo.names.entries.is_empty());
        assert!(
            complete(memo.recall_operand(cursor(MAX_ENTRIES), Some(&absent), &mut control))
                .is_none()
        );
    }

    #[test]
    fn every_name_publication_checkpoint_is_cancellable() {
        let text = name("wide_name");
        let mut polls = 0;
        complete(Names::default().remember(
            &text,
            cursor(0),
            &mut Control::new(NatReductionBudget::unlimited(), &mut || {
                polls += 1;
                false
            }),
        ));
        for stop in 1..=polls {
            let mut names = Names::default();
            let mut current = 0;
            let mut cancelled = || {
                current += 1;
                current == stop
            };
            let mut control = Control::new(NatReductionBudget::unlimited(), &mut cancelled);
            assert!(matches!(
                names.remember(&text, cursor(0), &mut control),
                Err(Halt::Stop(_))
            ));
            assert!(names.entries.is_empty());
            assert_eq!(names.units, 0);
        }
    }
}
