//! KR-955 on checker-owned arenas. Admission of the primitive quartet is
//! separate; these shape tests never grant declaration-publication authority.
use super::*;
use crate::environment::{ConstantSafety, QuotientKind};

pub(super) struct QuotientFrame {
    pub head: Cursor,
    pub arguments: VecDeque<Cursor>,
    pub major: usize,
    pub delta_mode: DeltaMode,
    pub unfolded_bindings: BTreeSet<usize>,
    pub force_string_delta: bool,
}

fn primitive_name(name: &WireName, suffix: Option<&str>) -> bool {
    match (name.parts(), suffix) {
        ([NamePart::Text(root)], None) => root == "Quot",
        ([NamePart::Text(root), NamePart::Text(leaf)], Some(suffix)) => {
            root == "Quot" && leaf == suffix
        }
        _ => false,
    }
}

impl Reducer<'_, '_> {
    pub(super) fn quotient_major(
        &mut self,
        current: &Cursor,
        arguments: usize,
    ) -> Result<Option<usize>, Halt> {
        let ExprNode::Constant { name, levels } = self.node(current)? else {
            return Ok(None);
        };
        let Some(entry) = self.context.source.constants().find(name) else {
            return Ok(None);
        };
        let (major, arity) = match entry.quotient_kind() {
            Some(QuotientKind::Lift) if primitive_name(name, Some("lift")) => (5, 2),
            Some(QuotientKind::Induction) if primitive_name(name, Some("ind")) => (4, 1),
            _ => return Ok(None),
        };
        if arguments <= major || levels.len() != arity {
            return Ok(None);
        }
        // Require the registered quartet, not just the spelling of a constant.
        for (suffix, kind, arity) in [
            (None, QuotientKind::Type, 1),
            (Some("mk"), QuotientKind::Constructor, 1),
            (Some("lift"), QuotientKind::Lift, 2),
            (Some("ind"), QuotientKind::Induction, 1),
        ] {
            self.control.step(current.root.index(), self.cancelled)?;
            let mut parts = vec![NamePart::Text("Quot".to_owned())];
            if let Some(suffix) = suffix {
                parts.push(NamePart::Text(suffix.to_owned()));
            }
            let name = WireName::from_parts(parts);
            let Some(entry) = self.context.source.constants().find(&name) else {
                return Ok(None);
            };
            if entry.quotient_kind() != Some(kind)
                || entry.level_parameters().len() != arity
                || entry.safety() != ConstantSafety::Safe
            {
                return Ok(None);
            }
        }
        Ok(Some(major))
    }

    pub(super) fn quotient_representative(
        &mut self,
        eliminator: &Cursor,
        major: &Cursor,
    ) -> Result<Option<Cursor>, Halt> {
        let (head, arguments) = self.peel_application(major)?;
        if arguments.len() != 3 {
            return Ok(None);
        }
        let ExprNode::Constant { name, levels } = self.node(&head)? else {
            return Ok(None);
        };
        if !primitive_name(name, Some("mk")) || levels.len() != 1 {
            return Ok(None);
        }
        let ExprNode::Constant {
            levels: elimination_levels,
            ..
        } = self.node(eliminator)?
        else {
            return Ok(None);
        };
        let Some(source_level) = elimination_levels.first() else {
            return Ok(None);
        };
        if !level_roots_equal(
            eliminator.arena.levels(),
            *source_level,
            head.arena.levels(),
            levels[0],
        )
        .map_err(|error| {
            Halt::Fault(WhnfFault::Universe {
                at: head.root.index(),
                error,
            })
        })? {
            return Ok(None);
        }
        Ok(Some(arguments[2].clone()))
    }
}
