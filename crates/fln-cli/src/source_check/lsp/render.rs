//! Bounded, stack-safe presentation of actual elaborator expressions.
//! This is display syntax, never reparsed into a proof or used for admission.
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal};
use fln_core::level::{Level, LevelView};
use fln_core::name::{LeafView, Name};
use std::collections::{HashMap, HashSet};

const MAX_BYTES: usize = 64 * 1024;
const MAX_WORK: usize = 100_000;
const LIMIT: &str = "semantic expression presentation exceeded its budget";
type Result<T> = std::result::Result<T, String>;

pub(super) struct ExpressionSpan {
    pub range: std::ops::Range<usize>,
    pub position: u64,
    pub expression: Expr,
}

pub(super) struct Rendered {
    pub text: String,
    pub expressions: Vec<ExpressionSpan>,
}

fn child_position(position: Option<u64>, child: u64) -> Option<u64> {
    position?.checked_mul(4)?.checked_add(child)
}

pub(super) struct Renderer {
    locals: HashMap<FVarId, String>,
    names: HashSet<String>,
    work: usize,
    bytes: usize,
}
impl Renderer {
    pub(super) fn new() -> Self {
        Self {
            locals: HashMap::new(),
            names: HashSet::new(),
            work: MAX_WORK,
            bytes: MAX_BYTES,
        }
    }
    fn tick(&mut self) -> Result<()> {
        self.work = self.work.checked_sub(1).ok_or(LIMIT)?;
        Ok(())
    }
    fn text(&mut self, out: &mut String, text: &str) -> Result<()> {
        self.bytes = self.bytes.checked_sub(text.len()).ok_or(LIMIT)?;
        out.push_str(text);
        Ok(())
    }
    fn name(&mut self, name: &Name) -> Result<String> {
        let mut cursor = name.clone();
        let mut parts = Vec::new();
        let mut bytes = 0usize;
        while !cursor.is_anonymous() {
            self.tick()?;
            let part = match cursor.leaf_view() {
                LeafView::Str(s) => {
                    if s.len() > MAX_BYTES {
                        return Err(LIMIT.to_owned());
                    }
                    s.to_owned()
                }
                LeafView::Num(n) => n.to_string(),
                LeafView::Anonymous => break,
            };
            bytes = bytes
                .checked_add(part.len() + 1)
                .filter(|n| *n <= MAX_BYTES)
                .ok_or(LIMIT)?;
            parts.push(part);
            cursor = cursor.parent();
        }
        parts.reverse();
        Ok(if parts.is_empty() {
            "_".to_owned()
        } else {
            parts.join(".")
        })
    }
    fn fresh(&mut self, name: &Name) -> Result<String> {
        let base = self.name(name)?;
        let mut name = base.clone();
        let mut serial = 1usize;
        while self.names.contains(&name) {
            self.tick()?;
            name = format!("{base}✝{serial}");
            serial += 1;
        }
        self.names.insert(name.clone());
        Ok(name)
    }
    pub(super) fn local(&mut self, id: &FVarId, name: &Name) -> Result<String> {
        if let Some(name) = self.locals.get(id) {
            return Ok(name.clone());
        }
        let name = self.fresh(name)?;
        self.locals.insert(id.clone(), name.clone());
        Ok(name)
    }
    pub(super) fn expr(&mut self, expr: &Expr) -> Result<String> {
        Ok(self.render(expr, false)?.text)
    }
    /// Record native expression leaves while printing them. No identifier is
    /// recovered by reparsing display text. Very deep positions that exceed the
    /// bounded position representation remain plain text, never wrapped IDs.
    pub(super) fn annotated(&mut self, expr: &Expr) -> Result<Rendered> {
        self.render(expr, true)
    }
    fn render(&mut self, expr: &Expr, annotated: bool) -> Result<Rendered> {
        enum Work<'a> {
            Expr(&'a Expr, Option<u64>),
            Text(String),
            Level(&'a Level),
            Bind(String),
            Unbind,
            EndTag {
                start: usize,
                expression: &'a Expr,
                position: u64,
            },
        }
        let mut work = vec![Work::Expr(expr, annotated.then_some(1))];
        let mut binders = Vec::new();
        let mut out = String::new();
        let mut expressions = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Text(text) => self.text(&mut out, &text)?,
                Work::Bind(name) => binders.push(name),
                Work::Unbind => {
                    binders.pop();
                }
                Work::EndTag {
                    start,
                    expression,
                    position,
                } => {
                    if expressions.len() >= 4096 {
                        return Err(LIMIT.to_owned());
                    }
                    expressions.push(ExpressionSpan {
                        range: start..out.len(),
                        position,
                        expression: expression.clone(),
                    });
                }
                Work::Level(level) => match level.view() {
                    LevelView::Zero => self.text(&mut out, "0")?,
                    LevelView::Param(n) => {
                        let n = self.name(n)?;
                        self.text(&mut out, &n)?;
                    }
                    LevelView::MVar(id) => {
                        let n = self.name(&id.0)?;
                        self.text(&mut out, &format!("?{n}"))?;
                    }
                    LevelView::Succ(child) => {
                        self.text(&mut out, "(")?;
                        work.extend([Work::Text(" + 1)".to_owned()), Work::Level(child)]);
                    }
                    LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                        self.text(
                            &mut out,
                            if matches!(level.view(), LevelView::Max(..)) {
                                "(max "
                            } else {
                                "(imax "
                            },
                        )?;
                        work.extend([
                            Work::Text(")".to_owned()),
                            Work::Level(b),
                            Work::Text(" ".to_owned()),
                            Work::Level(a),
                        ]);
                    }
                },
                Work::Expr(expr, position) => {
                    if let Some(position) = position.filter(|position| *position != 1)
                        && matches!(
                            expr.node(),
                            ExprNode::Const { .. }
                                | ExprNode::FVar { .. }
                                | ExprNode::Sort { .. }
                                | ExprNode::Lit { .. }
                        )
                    {
                        work.push(Work::EndTag {
                            start: out.len(),
                            expression: expr,
                            position,
                        });
                    }
                    match expr.node() {
                        ExprNode::BVar { idx } => {
                            let name = binders
                                .len()
                                .checked_sub(*idx as usize + 1)
                                .and_then(|i| binders.get(i))
                                .cloned()
                                .ok_or("unbound variable in semantic expression")?;
                            self.text(&mut out, &name)?;
                        }
                        ExprNode::FVar { id } => {
                            let name = self
                                .locals
                                .get(id)
                                .cloned()
                                .ok_or("missing local in semantic expression")?;
                            self.text(&mut out, &name)?;
                        }
                        ExprNode::MVar { id } => {
                            let n = self.name(&id.0)?;
                            self.text(&mut out, &format!("?{n}"))?;
                        }
                        ExprNode::Sort { level } => {
                            if level.is_zero() {
                                self.text(&mut out, "Prop")?;
                            } else if let LevelView::Succ(child) = level.view() {
                                if child.is_zero() {
                                    self.text(&mut out, "Type")?;
                                } else {
                                    self.text(&mut out, "Type ")?;
                                    work.push(Work::Level(child));
                                }
                            } else {
                                self.text(&mut out, "Sort ")?;
                                work.push(Work::Level(level));
                            }
                        }
                        ExprNode::Const { name, levels } => {
                            let name = self.name(name)?;
                            if self.names.contains(&name) {
                                self.text(&mut out, "_root_.")?;
                            }
                            self.text(&mut out, &name)?;
                            if !levels.is_empty() {
                                self.text(&mut out, ".{")?;
                                work.push(Work::Text("}".to_owned()));
                                for (i, level) in levels.iter().enumerate().rev() {
                                    work.push(Work::Level(level));
                                    if i > 0 {
                                        work.push(Work::Text(", ".to_owned()));
                                    }
                                }
                            }
                        }
                        ExprNode::App { f, a } => {
                            self.text(&mut out, "(")?;
                            work.extend([
                                Work::Text(")".to_owned()),
                                Work::Expr(a, child_position(position, 1)),
                                Work::Text(" ".to_owned()),
                                Work::Expr(f, child_position(position, 0)),
                            ]);
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        }
                        | ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let name = self.fresh(binder_name)?;
                            let (left, right) = match binder_info {
                                BinderInfo::Default => ("(", ")"),
                                BinderInfo::Implicit => ("{", "}"),
                                BinderInfo::StrictImplicit => ("⦃", "⦄"),
                                BinderInfo::InstImplicit => ("[", "]"),
                            };
                            let (head, sep) = if matches!(expr.node(), ExprNode::Lam { .. }) {
                                ("fun", " => ")
                            } else {
                                ("∀", ", ")
                            };
                            self.text(&mut out, &format!("({head} {left}{name} : "))?;
                            work.extend([
                                Work::Text(")".to_owned()),
                                Work::Unbind,
                                Work::Expr(body, child_position(position, 1)),
                                Work::Bind(name),
                                Work::Text(format!("{right}{sep}")),
                                Work::Expr(binder_type, child_position(position, 0)),
                            ]);
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            ..
                        } => {
                            let name = self.fresh(decl_name)?;
                            self.text(&mut out, &format!("(let {name} : "))?;
                            work.extend([
                                Work::Text(")".to_owned()),
                                Work::Unbind,
                                Work::Expr(body, child_position(position, 2)),
                                Work::Bind(name),
                                Work::Text("; ".to_owned()),
                                Work::Expr(value, child_position(position, 1)),
                                Work::Text(" := ".to_owned()),
                                Work::Expr(type_, child_position(position, 0)),
                            ]);
                        }
                        ExprNode::MData { expr, .. } => work.push(Work::Expr(expr, position)),
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            let name = self.name(struct_name)?;
                            self.text(&mut out, "(")?;
                            work.extend([
                                Work::Text(format!(").{name}.{idx}")),
                                Work::Expr(expr, child_position(position, 0)),
                            ]);
                        }
                        ExprNode::Lit {
                            literal: Literal::Nat(n),
                        } => {
                            if let Some(n) = n.to_u64() {
                                self.text(&mut out, &n.to_string())?;
                            } else {
                                self.text(&mut out, "0x")?;
                                for limb in n.limbs_le().iter().rev() {
                                    self.tick()?;
                                    self.text(&mut out, &format!("{limb:016x}"))?;
                                }
                            }
                        }
                        ExprNode::Lit {
                            literal: Literal::Str(s),
                        } => {
                            if s.len() > self.bytes / 6 {
                                return Err(LIMIT.to_owned());
                            }
                            self.text(&mut out, &format!("{s:?}"))?;
                        }
                    }
                }
            }
        }
        Ok(Rendered {
            text: out,
            expressions,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn expression_annotations_follow_native_children_and_unicode_byte_ranges() {
        let beta = FVarId(Name::from_components(["beta"]));
        let mut renderer = Renderer::new();
        renderer
            .local(&beta, &Name::from_components(["β"]))
            .unwrap();
        let f = Expr::const_(Name::from_components(["f"]), vec![]);
        let a = Expr::const_(Name::from_components(["a"]), vec![]);
        let expression = Expr::app(Expr::app(f.clone(), a.clone()), Expr::fvar(beta.clone()));
        let rendered = renderer.annotated(&expression).unwrap();
        assert_eq!(rendered.text, "((f a) β)");
        let spans: Vec<_> = rendered
            .expressions
            .iter()
            .map(|span| {
                (
                    span.range.clone(),
                    span.position,
                    rendered.text[span.range.clone()].to_owned(),
                    span.expression.clone(),
                )
            })
            .collect();
        assert_eq!(
            spans,
            vec![
                (2..3, 16, "f".to_owned(), f),
                (4..5, 17, "a".to_owned(), a),
                (7..9, 5, "β".to_owned(), Expr::fvar(beta)),
            ]
        );
    }

    #[test]
    fn expression_positions_never_wrap_or_alias_on_deep_terms() {
        let leaf = Expr::const_(Name::from_components(["a"]), vec![]);
        let mut expression = leaf.clone();
        for _ in 0..40 {
            expression = Expr::app(expression, leaf.clone());
        }
        let rendered = Renderer::new().annotated(&expression).unwrap();
        assert_eq!(rendered.text, Renderer::new().expr(&expression).unwrap());
        let mut positions = HashSet::new();
        for span in &rendered.expressions {
            assert!(positions.insert(span.position));
            assert!(span.position >= 4);
            let mut root = span.position;
            while root >= 4 {
                root /= 4;
            }
            assert_eq!(root, 1);
        }
        assert!(rendered.expressions.len() < 41);
    }
    #[test]
    fn dependent_binders_cannot_capture_outer_locals() {
        let name = Name::from_components(["x"]);
        let id = FVarId(name.clone());
        let mut r = Renderer::new();
        r.local(&id, &name).unwrap();
        let e = Expr::lam(
            name,
            Expr::sort(Level::zero()),
            Expr::app(Expr::bvar(0).unwrap(), Expr::fvar(id)),
            BinderInfo::Default,
        );
        assert_eq!(r.expr(&e).unwrap(), "(fun (x✝1 : Prop) => (x✝1 x))");
    }
    #[test]
    fn shared_expansion_is_bounded_and_missing_locals_refuse() {
        let mut e = Expr::const_(Name::from_components(["P"]), vec![]);
        for _ in 0..30 {
            e = Expr::app(e.clone(), e);
        }
        assert!(Renderer::new().expr(&e).is_err());
        assert!(Renderer::new().expr(&Expr::bvar(0).unwrap()).is_err());
        assert!(
            Renderer::new()
                .expr(&Expr::fvar(FVarId(Name::anonymous())))
                .is_err()
        );
    }
}
