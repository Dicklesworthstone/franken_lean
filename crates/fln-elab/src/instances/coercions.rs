//! Checked candidates for Lean's staged coercion hierarchy (Init.Coe).
//! No declaration or registration here has admission authority. Callers must
//! admit the whole library before publishing its class and instance journal.
use crate::lctx::LocalDecl;
use crate::records::{RecordBudget, RecordError, RecordSpec, record_declarations};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_kernel::Declaration;

pub struct CoercionSeed {
    pub declarations: Vec<Declaration>,
    pub classes: Vec<Name>,
    /// Register in this order, at priority 1000. Newer entries take precedence.
    pub instances: Vec<Name>,
}
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn constant(s: &str, levels: &[Level]) -> Expr {
    Expr::const_(n(s), levels.to_vec())
}
fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
fn local(name: &str, type_: Expr, style: BinderInfo) -> LocalDecl {
    LocalDecl {
        id: FVarId(n(&format!("_fln_coercion.{name}"))),
        user_name: n(name),
        type_,
        value: None,
        binder_info: style,
        index: 0,
    }
}
fn close(locals: &[LocalDecl], mut term: Expr, lambda: bool) -> Result<Expr, RecordError> {
    for local in locals.iter().rev() {
        term = term
            .abstract_fvar(&local.id, 0)
            .map_err(|_| RecordError::InvalidTelescope)?;
        term = if lambda {
            Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                term,
                local.binder_info,
            )
        } else {
            Expr::forall_e(
                local.user_name.clone(),
                local.type_.clone(),
                term,
                local.binder_info,
            )
        };
    }
    Ok(term)
}
fn arrow(domain: Expr, range: Expr) -> Result<Expr, RecordError> {
    close(&[local("x", domain, BinderInfo::Default)], range, false)
}
fn max(a: Level, b: Level) -> Result<Level, RecordError> {
    Level::max(a, b).map_err(|_| RecordError::ResourceLimit)
}
fn succ(a: &Level) -> Result<Level, RecordError> {
    a.clone().succ().map_err(|_| RecordError::ResourceLimit)
}
fn mark(mode: &str, sort: Expr, level: Level) -> Expr {
    Expr::app(constant(mode, &[level]), sort)
}
fn class(name: &str) -> Result<Vec<Declaration>, RecordError> {
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let a_type = Expr::sort(u.clone());
    let a_type = if matches!(name, "Coe" | "CoeTail") {
        mark("semiOutParam", a_type, succ(&u)?)
    } else {
        a_type
    };
    let a = local("A", a_type, BinderInfo::Default);
    let x = local("x", fv(&a), BinderInfo::Default);
    let mut params = vec![a.clone()];
    if matches!(name, "CoeDep" | "CoeT") {
        params.push(x.clone());
    }
    let mut b_type = if name == "CoeFun" {
        arrow(fv(&a), Expr::sort(v.clone()))?
    } else {
        Expr::sort(v.clone())
    };
    if matches!(name, "CoeOut" | "CoeHead" | "CoeSort" | "CoeFun") {
        let level = if name == "CoeFun" {
            max(u.clone(), succ(&v)?)?
        } else {
            succ(&v)?
        };
        let mode = if matches!(name, "CoeFun" | "CoeSort") {
            "outParam"
        } else {
            "semiOutParam"
        };
        b_type = mark(mode, b_type, level);
    }
    let b = local("B", b_type, BinderInfo::Default);
    params.push(b.clone());
    let field_type = match name {
        "CoeDep" | "CoeT" => fv(&b),
        "CoeFun" => close(std::slice::from_ref(&x), Expr::app(fv(&b), fv(&x)), false)?,
        _ => arrow(fv(&a), fv(&b))?,
    };
    record_declarations(
        &RecordSpec {
            name: n(name),
            level_params: vec![n("u"), n("v")],
            parameters: params,
            fields: vec![local("coe", field_type, BinderInfo::Default)],
            result_level: max(Level::one(), max(u, v)?)?,
            is_class: true,
        },
        RecordBudget::default(),
    )
}
struct Build {
    seed: CoercionSeed,
}
impl Build {
    fn definition(
        &mut self,
        name: &str,
        levels: &[&str],
        params: &[LocalDecl],
        type_: Expr,
        value: Expr,
    ) -> Result<(), RecordError> {
        let name = n(&format!("_fln_coe.{name}"));
        self.seed
            .declarations
            .push(Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: levels.iter().map(|s| n(s)).collect(),
                    type_: close(params, type_, false)?,
                },
                value: close(params, value, true)?,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![name.clone()],
            }));
        self.seed.instances.push(name);
        Ok(())
    }
    fn closure(
        &mut self,
        target: &str,
        base: &str,
        left: &str,
        right: &str,
        right_first: bool,
    ) -> Result<(), RecordError> {
        let u = Level::param(n("u"));
        let v = Level::param(n("v"));
        let w = Level::param(n("w"));
        let a = local("A", Expr::sort(u.clone()), BinderInfo::Implicit);
        let b = local("B", Expr::sort(v.clone()), BinderInfo::Implicit);
        let c = local("C", Expr::sort(w.clone()), BinderInfo::Implicit);
        let ab = [fv(&a), fv(&b)];
        let bc = [fv(&b), fv(&c)];
        let ac = [fv(&a), fv(&c)];
        let uv = [u.clone(), v.clone()];
        let vw = [v.clone(), w.clone()];
        let uw = [u.clone(), w.clone()];
        let l = local(
            "left",
            app(constant(left, &uv), ab.clone()),
            BinderInfo::InstImplicit,
        );
        let r = local(
            "right",
            app(constant(right, &vw), bc.clone()),
            BinderInfo::InstImplicit,
        );
        let x = local("x", fv(&a), BinderInfo::Default);
        let lvalue = app(
            constant(&format!("{left}.coe"), &uv),
            [fv(&a), fv(&b), fv(&l), fv(&x)],
        );
        let value = app(
            constant(&format!("{right}.coe"), &vw),
            [fv(&b), fv(&c), fv(&r), lvalue],
        );
        let value = close(std::slice::from_ref(&x), value, true)?;
        let params = if right_first {
            vec![a.clone(), b.clone(), c, r, l]
        } else {
            vec![a.clone(), b.clone(), c, l, r]
        };
        self.definition(
            &format!("{target}_trans"),
            &["u", "v", "w"],
            &params,
            app(constant(target, &uw), ac.clone()),
            app(
                constant(&format!("{target}.mk"), &uw),
                ac.into_iter().chain([value]),
            ),
        )?;
        let d = local(
            "dict",
            app(constant(base, &uv), ab.clone()),
            BinderInfo::InstImplicit,
        );
        let value = app(
            constant(&format!("{base}.coe"), &uv),
            [fv(&a), fv(&b), fv(&d)],
        );
        self.definition(
            &format!("{target}_base"),
            &["u", "v"],
            &[a.clone(), b, d],
            app(constant(target, &uv), ab.clone()),
            app(
                constant(&format!("{target}.mk"), &uv),
                ab.into_iter().chain([value]),
            ),
        )?;
        let uu = [u.clone(), u];
        let aa = [fv(&a), fv(&a)];
        let value = close(std::slice::from_ref(&x), fv(&x), true)?;
        self.definition(
            &format!("{target}_refl"),
            &["u"],
            &[a],
            app(constant(target, &uu), aa.clone()),
            app(
                constant(&format!("{target}.mk"), &uu),
                aa.into_iter().chain([value]),
            ),
        )
    }
    fn out_bridges(&mut self) -> Result<(), RecordError> {
        let u = Level::param(n("u"));
        let v = Level::param(n("v"));
        let levels = [u.clone(), v.clone()];
        let a = local("A", Expr::sort(u), BinderInfo::Implicit);
        let b = local("B", Expr::sort(v), BinderInfo::Implicit);
        let x = local("x", fv(&a), BinderInfo::Default);
        let target = [fv(&a), fv(&b)];
        for class in ["CoeFun", "CoeSort"] {
            let output = if class == "CoeFun" {
                close(std::slice::from_ref(&x), fv(&b), true)?
            } else {
                fv(&b)
            };
            let args = [fv(&a), output];
            let d = local(
                "dict",
                app(constant(class, &levels), args.clone()),
                BinderInfo::InstImplicit,
            );
            let value = app(
                constant(&format!("{class}.coe"), &levels),
                args.into_iter().chain([fv(&d)]),
            );
            self.definition(
                &format!("{class}_out"),
                &["u", "v"],
                &[a.clone(), b.clone(), d],
                app(constant("CoeOut", &levels), target.clone()),
                app(
                    constant("CoeOut.mk", &levels),
                    target.clone().into_iter().chain([value]),
                ),
            )?;
        }
        Ok(())
    }

    fn terminal(&mut self) -> Result<(), RecordError> {
        let u = Level::param(n("u"));
        let v = Level::param(n("v"));
        let uv = [u.clone(), v.clone()];
        let a = local("A", Expr::sort(u.clone()), BinderInfo::Implicit);
        let x = local("x", fv(&a), BinderInfo::Implicit);
        let b = local("B", Expr::sort(v), BinderInfo::Implicit);
        let axb = [fv(&a), fv(&x), fv(&b)];
        for base in ["CoeHTCT", "CoeDep"] {
            let args = if base == "CoeDep" {
                axb.to_vec()
            } else {
                vec![fv(&a), fv(&b)]
            };
            let d = local(
                "dict",
                app(constant(base, &uv), args.clone()),
                BinderInfo::InstImplicit,
            );
            let mut value = app(
                constant(&format!("{base}.coe"), &uv),
                args.into_iter().chain([fv(&d)]),
            );
            if base == "CoeHTCT" {
                value = Expr::app(value, fv(&x));
            }
            self.definition(
                &format!("CoeT_{base}"),
                &["u", "v"],
                &[a.clone(), x.clone(), b.clone(), d],
                app(constant("CoeT", &uv), axb.clone()),
                app(
                    constant("CoeT.mk", &uv),
                    axb.clone().into_iter().chain([value]),
                ),
            )?;
        }
        let uu = [u.clone(), u];
        let axa = [fv(&a), fv(&x), fv(&a)];
        self.definition(
            "CoeT_refl",
            &["u"],
            &[a, x.clone()],
            app(constant("CoeT", &uu), axa.clone()),
            app(constant("CoeT.mk", &uu), axa.into_iter().chain([fv(&x)])),
        )
    }
}

/// Build the staged path `CoeHead? CoeOut* Coe* CoeTail?`, with `CoeDep`
/// tried as a value-dependent alternative. These are ordinary checked instance
/// definitions; native instance search supplies all composition and rollback.
pub fn declarations() -> Result<CoercionSeed, RecordError> {
    let names = [
        "Coe", "CoeTC", "CoeOut", "CoeOTC", "CoeHead", "CoeHTC", "CoeTail", "CoeHTCT", "CoeDep",
        "CoeT", "CoeFun", "CoeSort",
    ];
    let mut build = Build {
        seed: CoercionSeed {
            declarations: Vec::new(),
            classes: names.iter().map(|s| n(s)).collect(),
            instances: Vec::new(),
        },
    };
    for name in names {
        build.seed.declarations.extend(class(name)?);
    }
    build.closure("CoeTC", "Coe", "CoeTC", "Coe", true)?;
    build.closure("CoeOTC", "CoeTC", "CoeOut", "CoeOTC", false)?;
    build.closure("CoeHTC", "CoeOTC", "CoeHead", "CoeOTC", false)?;
    build.closure("CoeHTCT", "CoeHTC", "CoeHTC", "CoeTail", true)?;
    build.terminal()?;
    build.out_bridges()?;
    Ok(build.seed)
}
