//! Native candidates for numeric notation. All dictionaries and adapters are
//! ordinary definitions: callers admit them before registering any instances.
use crate::lctx::LocalDecl;
use crate::records::{Builder, RecordBudget, RecordError, RecordSpec, record_declarations};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_kernel::Declaration;

pub struct NumericSeed {
    pub declarations: Vec<Declaration>,
    pub classes: Vec<Name>,
    pub instances: Vec<Name>,
    pub defaults: Vec<(Name, u32)>,
}

/// Symbol, homogeneous class, method, heterogeneous class, method, Nat primitive.
const OPERATIONS: &[(&str, &str, &str, &str, &str, &str)] = &[
    ("+", "Add", "add", "HAdd", "hAdd", "add"),
    ("-", "Sub", "sub", "HSub", "hSub", "sub"),
    ("*", "Mul", "mul", "HMul", "hMul", "mul"),
    ("/", "Div", "div", "HDiv", "hDiv", "div"),
    ("%", "Mod", "mod", "HMod", "hMod", "mod"),
    ("^", "Pow", "pow", "HPow", "hPow", "pow"),
    ("++", "Append", "append", "HAppend", "hAppend", ""),
    ("&&&", "AndOp", "and", "HAnd", "hAnd", "land"),
    ("|||", "OrOp", "or", "HOr", "hOr", "lor"),
    ("^^^", "XorOp", "xor", "HXor", "hXor", "xor"),
    (
        "<<<",
        "ShiftLeft",
        "shiftLeft",
        "HShiftLeft",
        "hShiftLeft",
        "shiftLeft",
    ),
    (
        ">>>",
        "ShiftRight",
        "shiftRight",
        "HShiftRight",
        "hShiftRight",
        "shiftRight",
    ),
];

/// Exact root notation classes; unrelated user names have no special meaning.
pub fn notation(symbol: &str) -> Option<(&'static str, &'static str)> {
    if symbol == "==" {
        return Some(("BEq", "beq"));
    }
    OPERATIONS
        .iter()
        .find(|row| row.0 == symbol)
        .map(|row| (row.3, row.4))
}
fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn c(s: &str, levels: &[Level]) -> Expr {
    Expr::const_(n(s), levels.to_vec())
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn local(name: &str, type_: Expr, style: BinderInfo) -> LocalDecl {
    LocalDecl {
        id: FVarId(n(&format!("_fln_numeric_local.{name}"))),
        user_name: n(name),
        type_,
        value: None,
        binder_info: style,
        index: 0,
    }
}
fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
fn succ(level: &Level) -> Result<Level, RecordError> {
    level.clone().succ().map_err(|_| RecordError::ResourceLimit)
}
fn max(a: Level, b: Level) -> Result<Level, RecordError> {
    Level::max(a, b).map_err(|_| RecordError::ResourceLimit)
}
fn close(locals: &[LocalDecl], term: Expr, lambda: bool) -> Result<Expr, RecordError> {
    Builder {
        remaining: RecordBudget::default().max_nodes,
    }
    .close(locals, term, lambda, false)
}
fn binary(a: Expr, b: Expr, result: Expr) -> Result<Expr, RecordError> {
    close(
        &[
            local("x", a, BinderInfo::Default),
            local("y", b, BinderInfo::Default),
        ],
        result,
        false,
    )
}
impl NumericSeed {
    fn class(
        &mut self,
        name: &str,
        levels: &[&str],
        params: Vec<LocalDecl>,
        method: &str,
        domain: Expr,
        result: Level,
    ) -> Result<(), RecordError> {
        self.declarations.extend(record_declarations(
            &RecordSpec {
                name: n(name),
                level_params: levels.iter().map(|s| n(s)).collect(),
                parameters: params,
                fields: vec![local(method, domain, BinderInfo::Default)],
                result_level: result,
                is_class: true,
            },
            RecordBudget::default(),
        )?);
        self.classes.push(n(name));
        Ok(())
    }
    fn instance(
        &mut self,
        name: &str,
        levels: &[&str],
        params: &[LocalDecl],
        type_: Expr,
        value: Expr,
        default: Option<u32>,
    ) -> Result<(), RecordError> {
        let name = n(&format!("_fln_numeric.{name}"));
        self.declarations.push(Declaration::Defn(DefinitionVal {
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
        self.instances.push(name.clone());
        if let Some(priority) = default {
            self.defaults.push((name, priority));
        }
        Ok(())
    }
}

pub fn declarations() -> Result<NumericSeed, RecordError> {
    let mut seed = NumericSeed {
        declarations: vec![],
        classes: vec![],
        instances: vec![],
        defaults: vec![],
    };
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let w = Level::param(n("w"));
    let a = local("A", Expr::sort(succ(&u)?), BinderInfo::Default);
    let b = local("B", Expr::sort(succ(&v)?), BinderInfo::Default);
    let number = local("n", c("Nat", &[]), BinderInfo::Default);
    seed.class(
        "OfNat",
        &["u"],
        vec![a.clone(), number.clone()],
        "ofNat",
        fv(&a),
        succ(&u)?,
    )?;
    let nat_args = [c("Nat", &[]), fv(&number)];
    seed.instance(
        "ofNat",
        &[],
        &[number],
        app(c("OfNat", &[Level::zero()]), nat_args.clone()),
        app(
            c("OfNat.mk", &[Level::zero()]),
            nat_args
                .into_iter()
                .chain([fv(&local("n", c("Nat", &[]), BinderInfo::Default))]),
        ),
        Some(100),
    )?;
    for &(_, homogeneous, method, hetero, hmethod, primitive) in OPERATIONS {
        let is_pow = homogeneous == "Pow";
        let params = if is_pow {
            vec![a.clone(), b.clone()]
        } else {
            vec![a.clone()]
        };
        let levels = if is_pow { vec!["u", "v"] } else { vec!["u"] };
        let right = if is_pow { fv(&b) } else { fv(&a) };
        let result = if is_pow {
            max(succ(&u)?, succ(&v)?)?
        } else {
            succ(&u)?
        };
        seed.class(
            homogeneous,
            &levels,
            params.clone(),
            method,
            binary(fv(&a), right.clone(), fv(&a))?,
            result,
        )?;
        let out = local(
            "C",
            Expr::app(c("outParam", &[succ(&succ(&w)?)?]), Expr::sort(succ(&w)?)),
            BinderInfo::Default,
        );
        seed.class(
            hetero,
            &["u", "v", "w"],
            vec![a.clone(), b.clone(), out.clone()],
            hmethod,
            binary(fv(&a), fv(&b), fv(&out))?,
            max(max(succ(&u)?, succ(&v)?)?, succ(&w)?)?,
        )?;
        let hlevels = if is_pow {
            vec![u.clone(), v.clone(), u.clone()]
        } else {
            vec![u.clone(); 3]
        };
        let plevels = if is_pow {
            vec![u.clone(), v.clone()]
        } else {
            vec![u.clone()]
        };
        let pargs: Vec<_> = params.iter().map(fv).collect();
        let dict = local(
            "dict",
            app(c(homogeneous, &plevels), pargs.clone()),
            BinderInfo::InstImplicit,
        );
        let mut implicit = params;
        for param in &mut implicit {
            param.binder_info = BinderInfo::Implicit;
        }
        implicit.push(dict.clone());
        let args = [fv(&a), right, fv(&a)];
        let implementation = app(
            c(&format!("{homogeneous}.{method}"), &plevels),
            pargs.into_iter().chain([fv(&dict)]),
        );
        seed.instance(
            &format!("adapt{hetero}"),
            &levels,
            &implicit,
            app(c(hetero, &hlevels), args.clone()),
            app(
                c(&format!("{hetero}.mk"), &hlevels),
                args.into_iter().chain([implementation]),
            ),
            Some(1000),
        )?;
        let scalar = if homogeneous == "Append" {
            "String"
        } else {
            "Nat"
        };
        let scalar_args = if is_pow {
            vec![c(scalar, &[]); 2]
        } else {
            vec![c(scalar, &[])]
        };
        let zeros = vec![Level::zero(); levels.len()];
        let value = c(
            &format!(
                "{scalar}.{}",
                if primitive.is_empty() {
                    "append"
                } else {
                    primitive
                }
            ),
            &[],
        );
        seed.instance(
            &format!("scalar{homogeneous}"),
            &[],
            &[],
            app(c(homogeneous, &zeros), scalar_args.clone()),
            app(
                c(&format!("{homogeneous}.mk"), &zeros),
                scalar_args.into_iter().chain([value]),
            ),
            None,
        )?;
    }
    seed.class(
        "BEq",
        &["u"],
        vec![a.clone()],
        "beq",
        binary(fv(&a), fv(&a), c("Bool", &[]))?,
        succ(&u)?,
    )?;
    for (scalar, primitive) in [("Nat", "Nat.beq"), ("String", "String.decEq")] {
        let args = [c(scalar, &[])];
        seed.instance(
            &format!("beq{scalar}"),
            &[],
            &[],
            app(c("BEq", &[Level::zero()]), args.clone()),
            app(
                c("BEq.mk", &[Level::zero()]),
                args.into_iter().chain([c(primitive, &[])]),
            ),
            None,
        )?;
    }
    Ok(seed)
}
