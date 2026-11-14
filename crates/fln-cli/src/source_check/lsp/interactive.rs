//! Render structured RPC observations directly from the native inspection.
//! Never parse pretty-printed goal strings to recover identities or contexts.
use super::render::Renderer;
use fln::source_check::inspect::{ExpressionInspector, ObservedGoal};
use fln_server::dispatch::semantic::{
    Answer, Code, ExpressionInfo, Goal, Hypothesis, QueryKind, SubexpressionInfo, TermGoal,
};
use std::collections::HashMap;
use std::ops::Range;

fn charge(total: &mut usize, bytes: usize) -> Result<(), String> {
    *total = total
        .checked_add(bytes)
        .filter(|n| *n <= 64 * 1024)
        .ok_or("native interactive observation exceeded its byte limit")?;
    Ok(())
}

struct Presenter {
    renderer: Renderer,
    inspector: ExpressionInspector,
    infos: HashMap<fln::Expr, ExpressionInfo>,
}

impl Presenter {
    fn info(
        &mut self,
        expression: &fln::Expr,
        total: &mut usize,
    ) -> Result<ExpressionInfo, String> {
        let info = match self.infos.get(expression) {
            Some(info) => info.clone(),
            None => {
                let type_ = self
                    .inspector
                    .type_of(expression)
                    .map_err(|error| error.to_string())?
                    .as_ref()
                    .map(|type_| self.renderer.expr(type_))
                    .transpose()?;
                let info = ExpressionInfo { type_ };
                self.infos.insert(expression.clone(), info.clone());
                info
            }
        };
        charge(total, 32)?;
        if let Some(type_) = &info.type_ {
            charge(total, type_.len())?;
        }
        Ok(info)
    }

    fn code(&mut self, expression: &fln::Expr, total: &mut usize) -> Result<Code, String> {
        let rendered = self.renderer.annotated(expression)?;
        charge(total, 96)?;
        charge(total, rendered.text.len())?;
        let info = Some(self.info(expression, total)?);
        let mut subexpressions = Vec::with_capacity(rendered.expressions.len());
        for span in rendered.expressions {
            charge(total, 32)?;
            subexpressions.push(SubexpressionInfo {
                range: span.range,
                position: span.position,
                info: self.info(&span.expression, total)?,
            });
        }
        Ok(Code {
            text: rendered.text,
            info,
            subexpressions,
        })
    }
}

pub(super) fn observe(
    goals: Vec<ObservedGoal>,
    range: Range<usize>,
    kind: QueryKind,
    kernel: fln::Budget,
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
        let mut presenter = Presenter {
            renderer,
            inspector: goal
                .expression_inspector(kernel, 100_000)
                .map_err(|error| error.to_string())?,
            infos: HashMap::new(),
        };
        let mut hypotheses = Vec::new();
        for (local, name) in goal.locals.decls().iter().zip(names) {
            let fvar_id = local.id.0.to_display_string();
            let type_ = presenter.code(&local.type_, &mut total)?;
            let value = local
                .value
                .as_ref()
                .map(|expr| presenter.code(expr, &mut total))
                .transpose()?;
            charge(&mut total, 64)?;
            for text in [&name, &fvar_id] {
                charge(&mut total, text.len())?;
            }
            hypotheses.push(Hypothesis {
                name,
                fvar_id,
                type_,
                value,
            });
        }
        let target = presenter.code(&goal.target, &mut total)?;
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
