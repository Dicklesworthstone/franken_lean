//! Render structured RPC observations directly from the native inspection.
//! Never parse pretty-printed goal strings to recover identities or contexts.
use super::render::Renderer;
use fln::source_check::inspect::ObservedGoal;
use fln_server::dispatch::semantic::{Answer, Goal, Hypothesis, QueryKind, TermGoal};
use std::ops::Range;

fn charge(total: &mut usize, bytes: usize) -> Result<(), String> {
    *total = total
        .checked_add(bytes)
        .filter(|n| *n <= 64 * 1024)
        .ok_or("native interactive observation exceeded its byte limit")?;
    Ok(())
}

pub(super) fn observe(
    goals: Vec<ObservedGoal>,
    range: Range<usize>,
    kind: QueryKind,
) -> Result<Answer, String> {
    let term = kind == QueryKind::InteractiveTermGoal;
    if goals.len() > 256 || (term && goals.len() != 1) {
        return Err("native interactive inspection returned an invalid goal count".to_owned());
    }
    let mut total = 64;
    let mut displayed = Vec::new();
    for goal in goals {
        charge(&mut total, 64)?;
        if goal.locals.len() > 4096 {
            return Err("native interactive goal has too many hypotheses".to_owned());
        }
        let mut renderer = Renderer::new();
        let mut names = Vec::new();
        for local in goal.locals.decls() {
            names.push(renderer.local(&local.id, &local.user_name)?);
        }
        let mut hypotheses = Vec::new();
        for (local, name) in goal.locals.decls().iter().zip(names) {
            let fvar_id = local.id.0.to_display_string();
            let type_ = renderer.expr(&local.type_)?;
            let value = local
                .value
                .as_ref()
                .map(|expr| renderer.expr(expr))
                .transpose()?;
            charge(&mut total, 64)?;
            for text in [&name, &fvar_id, &type_] {
                charge(&mut total, text.len())?;
            }
            if let Some(value) = &value {
                charge(&mut total, value.len())?;
            }
            hypotheses.push(Hypothesis {
                name,
                fvar_id,
                type_,
                value,
            });
        }
        let target = renderer.expr(&goal.target)?;
        charge(&mut total, target.len())?;
        if term {
            return Ok(Answer::InteractiveTermGoal(TermGoal {
                hypotheses,
                target,
                range,
            }));
        }
        let mvar_id = goal
            .id
            .as_ref()
            .ok_or("native tactic observation has no obligation identity")?
            .0
            .to_display_string();
        let user_name = goal.user_name.as_ref().map(fln::Name::to_display_string);
        charge(&mut total, mvar_id.len())?;
        if let Some(name) = &user_name {
            charge(&mut total, name.len())?;
        }
        displayed.push(Goal {
            mvar_id,
            user_name,
            hypotheses,
            target,
        });
    }
    Ok(Answer::InteractiveGoals { goals: displayed })
}
