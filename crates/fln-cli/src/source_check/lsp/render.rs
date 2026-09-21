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
        enum Work<'a> {
            Expr(&'a Expr),
            Text(String),
            Level(&'a Level),
            Bind(String),
            Unbind,
        }
        let mut work = vec![Work::Expr(expr)];
        let mut binders = Vec::new();
        let mut out = String::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Text(text) => self.text(&mut out, &text)?,
                Work::Bind(name) => binders.push(name),
                Work::Unbind => {
                    binders.pop();
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
                Work::Expr(expr) => match expr.node() {
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
                            Work::Expr(a),
                            Work::Text(" ".to_owned()),
                            Work::Expr(f),
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
                            Work::Expr(body),
                            Work::Bind(name),
                            Work::Text(format!("{right}{sep}")),
                            Work::Expr(binder_type),
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
                            Work::Expr(body),
                            Work::Bind(name),
                            Work::Text("; ".to_owned()),
                            Work::Expr(value),
                            Work::Text(" := ".to_owned()),
                            Work::Expr(type_),
                        ]);
                    }
                    ExprNode::MData { expr, .. } => work.push(Work::Expr(expr)),
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        let name = self.name(struct_name)?;
                        self.text(&mut out, "(")?;
                        work.extend([Work::Text(format!(").{name}.{idx}")), Work::Expr(expr)]);
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
                },
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
