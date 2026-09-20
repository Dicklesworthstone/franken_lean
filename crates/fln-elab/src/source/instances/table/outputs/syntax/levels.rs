//! Universe variants are private cache data. Parameters stay rigid; unknown
//! universes are renamed only when independent of the active cycle path.
//! Saved assignments are read, never copied into the live elaboration state.
use super::*;
use fln_core::level::LevelView;
use std::collections::HashSet;

#[derive(Default)]
pub(super) struct LevelTemplates {
    holes: HashMap<LMVarId, Level>,
    done: HashMap<Level, Level>,
    anchored: HashSet<LMVarId>,
    allow_variants: bool,
}

impl LevelTemplates {
    pub fn units(&self) -> usize {
        self.done.len() + self.anchored.len()
    }

    /// Cycle detection compares saved keys, not their interpretation under the
    /// latest assignment store. Keep those keys exact and do not alpha-rename a
    /// query universe that occurs in them. This conservative miss preserves the
    /// distinction between a repeated goal and a fresh universe variant.
    pub fn anchor(
        &mut self,
        context: &mut Context,
        ancestors: &[Frame],
    ) -> Result<bool, NatDefinitionElabError> {
        let mut expressions = Vec::new();
        let mut levels = Vec::new();
        let mut seen_expr = HashSet::new();
        let mut seen_level = HashSet::new();
        for ancestor in ancestors {
            context.tick()?;
            expressions.push(ancestor.key.clone());
        }
        while let Some(expr) = expressions.pop() {
            context.tick()?;
            if seen_expr.len() + expressions.len() + levels.len() >= MAX_KEY_UNITS {
                return Ok(false);
            }
            if !expr.has_level_mvar() || !seen_expr.insert(expr.clone()) {
                continue;
            }
            match expr.node() {
                ExprNode::Sort { level } => levels.push(level.clone()),
                ExprNode::Const { levels: args, .. } => {
                    let occupied = seen_expr.len() + expressions.len() + levels.len();
                    if args.len() > MAX_KEY_UNITS.saturating_sub(occupied) {
                        return Ok(false);
                    }
                    levels.extend(args.iter().cloned());
                }
                ExprNode::App { f, a } => expressions.extend([a.clone(), f.clone()]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    expressions.extend([body.clone(), binder_type.clone()]);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    expressions.extend([body.clone(), value.clone(), type_.clone()]);
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    expressions.push(expr.clone())
                }
                _ => {}
            }
        }
        while let Some(level) = levels.pop() {
            context.tick()?;
            if seen_level.len() + levels.len() >= MAX_KEY_UNITS {
                return Ok(false);
            }
            if !level.has_mvar() || !seen_level.insert(level.clone()) {
                continue;
            }
            match level.view() {
                LevelView::MVar(id) => {
                    self.anchored.insert(id.clone());
                }
                LevelView::Succ(inner) => levels.push(inner.clone()),
                LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                    levels.extend([right.clone(), left.clone()]);
                }
                LevelView::Zero | LevelView::Param(_) => {}
            }
        }
        self.allow_variants = true;
        Ok(true)
    }

    pub fn rewrite(
        &mut self,
        context: &mut Context,
        frame: &Frame,
        root: &Level,
    ) -> Result<Option<Level>, NatDefinitionElabError> {
        // Cycle-key comparison does not alpha-rename universes. Only answer
        // keys explicitly prepared with an anchored path enable variants.
        if !self.allow_variants && root.has_mvar() {
            context.tick()?;
            return Ok(None);
        }
        let mut pending = vec![(root.clone(), false)];
        let mut active = HashSet::new();
        while let Some((level, finish)) = pending.pop() {
            context.tick()?;
            if self.done.contains_key(&level) {
                continue;
            }
            if self.units() + self.holes.len() + pending.len() >= MAX_KEY_UNITS {
                return Ok(None);
            }
            if !level.has_mvar() {
                self.done.insert(level.clone(), level);
                continue;
            }
            if !finish {
                pending.push((level.clone(), true));
                match level.view() {
                    LevelView::MVar(id) => {
                        if let Some(value) = frame.base.txn.universes.get_assignment(id) {
                            if !active.insert(id.clone()) {
                                return Ok(None);
                            }
                            pending.push((value.clone(), false));
                        } else if self.anchored.contains(id) {
                            return Ok(None);
                        }
                    }
                    LevelView::Succ(inner) => pending.push((inner.clone(), false)),
                    LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                        pending.push((right.clone(), false));
                        pending.push((left.clone(), false));
                    }
                    LevelView::Zero | LevelView::Param(_) => {}
                }
                continue;
            }
            let child = |level: &Level| {
                self.done
                    .get(level)
                    .expect("planned universe child")
                    .clone()
            };
            let value = match level.view() {
                LevelView::MVar(id) => {
                    if let Some(value) = frame.base.txn.universes.get_assignment(id) {
                        active.remove(id);
                        Some(child(value))
                    } else {
                        let next = Level::mvar(LMVarId(Name::num(
                            Name::anonymous(),
                            self.holes.len() as u64,
                        )));
                        Some(self.holes.entry(id.clone()).or_insert(next).clone())
                    }
                }
                LevelView::Succ(inner) => child(inner).succ().ok(),
                LevelView::Max(left, right) => Level::max(child(left), child(right)).ok(),
                LevelView::IMax(left, right) => Level::imax(child(left), child(right)).ok(),
                LevelView::Zero | LevelView::Param(_) => Some(level.clone()),
            };
            let Some(value) = value else {
                return Ok(None);
            };
            self.done.insert(level, value);
        }
        Ok(self.done.get(root).cloned())
    }
}
