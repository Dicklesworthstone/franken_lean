//! Structured native observations for the read-only RPC procedures.
//! References retain these provisional presentations, not admission credentials.
use super::{Answer, Query};
use std::ops::Range;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hypothesis {
    pub name: String,
    pub fvar_id: String,
    pub type_: String,
    pub value: Option<String>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Goal {
    pub mvar_id: String,
    pub user_name: Option<String>,
    pub hypotheses: Vec<Hypothesis>,
    pub target: String,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermGoal {
    pub hypotheses: Vec<Hypothesis>,
    pub target: String,
    pub range: Range<usize>,
}

/// Charge all strings and row overhead before cloning or serializing a result.
/// Many empty rows must not evade the retained-memory or output limits.
pub(in crate::dispatch) fn payload_bytes(answer: &Answer) -> Result<usize, &'static str> {
    use std::collections::BTreeSet;
    fn add(total: &mut usize, bytes: usize) -> Result<(), &'static str> {
        *total = total
            .checked_add(bytes)
            .filter(|n| *n <= 64 * 1024)
            .ok_or("interactive observation exceeds its payload budget")?;
        Ok(())
    }
    fn context(total: &mut usize, hyps: &[Hypothesis], target: &str) -> Result<(), &'static str> {
        if hyps.len() > 4096 {
            return Err("interactive observation has too many hypotheses");
        }
        add(total, target.len())?;
        let mut seen = BTreeSet::new();
        for hyp in hyps {
            if hyp.fvar_id.is_empty() || !seen.insert(&hyp.fvar_id) {
                return Err("interactive observation has invalid local identities");
            }
            add(total, 64)?;
            for text in [&hyp.name, &hyp.fvar_id, &hyp.type_] {
                add(total, text.len())?;
            }
            if let Some(value) = &hyp.value {
                add(total, value.len())?;
            }
        }
        Ok(())
    }
    let mut total = 64;
    match answer {
        Answer::InteractiveGoals { goals } => {
            if goals.len() > 256 {
                return Err("interactive observation has too many goals");
            }
            let mut seen = BTreeSet::new();
            for goal in goals {
                if goal.mvar_id.is_empty() || !seen.insert(&goal.mvar_id) {
                    return Err("interactive observation has invalid goal identities");
                }
                add(&mut total, 64)?;
                add(&mut total, goal.mvar_id.len())?;
                if let Some(name) = &goal.user_name {
                    add(&mut total, name.len())?;
                }
                context(&mut total, &goal.hypotheses, &goal.target)?;
            }
        }
        Answer::InteractiveTermGoal(goal) => context(&mut total, &goal.hypotheses, &goal.target)?,
        _ => return Err("interactive provider returned another answer kind"),
    }
    Ok(total)
}

pub(in crate::dispatch) fn validate(
    answer: &Answer,
    query: Query<'_>,
) -> Result<usize, &'static str> {
    let bytes = payload_bytes(answer)?;
    if let Answer::InteractiveTermGoal(goal) = answer {
        if goal.range.start >= goal.range.end || !goal.range.contains(&query.offset) {
            return Err("interactive term range does not contain the requested position");
        }
        for offset in [goal.range.start, goal.range.end] {
            let position = super::position(query.text, offset)?;
            if super::super::json::byte_offset(query.text, position)? != offset {
                return Err("interactive term range has no exact LSP coordinate mapping");
            }
        }
    }
    Ok(bytes)
}
