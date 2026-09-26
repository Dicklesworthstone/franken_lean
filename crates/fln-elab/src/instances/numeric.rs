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
    pub priorities: Vec<(Name, u32)>,
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
pub(crate) fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
pub(crate) fn c(s: &str, levels: &[Level]) -> Expr {
    Expr::const_(n(s), levels.to_vec())
}
pub(crate) fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
pub(crate) fn local(name: &str, type_: Expr, style: BinderInfo) -> LocalDecl {
    LocalDecl {
        id: FVarId(n(&format!("_fln_numeric_local.{name}"))),
        user_name: n(name),
        type_,
        value: None,
        binder_info: style,
        index: 0,
    }
}
pub(crate) fn fv(local: &LocalDecl) -> Expr {
    Expr::fvar(local.id.clone())
}
pub(crate) fn succ(level: &Level) -> Result<Level, RecordError> {
    level.clone().succ().map_err(|_| RecordError::ResourceLimit)
}
fn max(a: Level, b: Level) -> Result<Level, RecordError> {
    Level::max(a, b).map_err(|_| RecordError::ResourceLimit)
}
pub(crate) fn close(locals: &[LocalDecl], term: Expr, lambda: bool) -> Result<Expr, RecordError> {
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
    pub(crate) fn class(
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
        self.named_instance(
            &format!("_fln_numeric.{name}"),
            levels,
            params,
            type_,
            value,
            default,
        )
    }

    pub(crate) fn named_instance(
        &mut self,
        name: &str,
        levels: &[&str],
        params: &[LocalDecl],
        type_: Expr,
        value: Expr,
        default: Option<u32>,
    ) -> Result<(), RecordError> {
        let name = n(name);
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
        priorities: vec![],
        defaults: vec![],
    };
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let w = Level::param(n("w"));
    let a = local("α", Expr::sort(succ(&u)?), BinderInfo::Default);
    let b = local("β", Expr::sort(succ(&v)?), BinderInfo::Default);
    let number = local("n", c("Nat", &[]), BinderInfo::Default);
    seed.class(
        "OfNat",
        &["u"],
        vec![a.clone(), number.clone()],
        "ofNat",
        fv(&a),
        succ(&u)?,
    )?;
    // The numeral index is an explicit argument of the Reference projection
    // (`OfNat.ofNat 37`), unlike the inferred carrier and instance dictionary.
    // The general record builder hides record parameters, so retain this
    // projection's declared binder contract when constructing the fixed seed.
    let mut alpha = a.clone();
    alpha.binder_info = BinderInfo::Implicit;
    let dictionary = local(
        "self",
        app(c("OfNat", std::slice::from_ref(&u)), [fv(&a), fv(&number)]),
        BinderInfo::InstImplicit,
    );
    let projection_parameters = [alpha, number.clone(), dictionary.clone()];
    let projection_name = n("OfNat.ofNat");
    *seed
        .declarations
        .last_mut()
        .ok_or(RecordError::InvalidTelescope)? = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: projection_name.clone(),
            level_params: vec![n("u")],
            type_: close(&projection_parameters, fv(&a), false)?,
        },
        value: close(
            &projection_parameters,
            Expr::proj(n("OfNat"), 0, fv(&dictionary)),
            true,
        )?,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![projection_name],
    });
    let nat_args = [c("Nat", &[]), fv(&number)];
    seed.named_instance(
        "instOfNatNat",
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
            "γ",
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
        let adapter_name = match hetero {
            "HAdd" | "HSub" | "HMul" | "HDiv" | "HMod" | "HPow" => {
                format!("inst{hetero}")
            }
            _ => format!("inst{hetero}Of{homogeneous}"),
        };
        seed.named_instance(
            &adapter_name,
            &levels,
            &implicit,
            app(c(hetero, &hlevels), args.clone()),
            app(
                c(&format!("{hetero}.mk"), &hlevels),
                args.into_iter().chain([implementation]),
            ),
            Some(1000),
        )?;
        if is_pow {
            seed.class(
                "NatPow",
                &["u"],
                vec![a.clone()],
                "pow",
                binary(fv(&a), c("Nat", &[]), fv(&a))?,
                succ(&u)?,
            )?;
            let dict = local(
                "dict",
                Expr::app(c("NatPow", std::slice::from_ref(&u)), fv(&a)),
                BinderInfo::InstImplicit,
            );
            let mut alpha = a.clone();
            alpha.binder_info = BinderInfo::Implicit;
            seed.named_instance(
                "instPowNat",
                &["u"],
                &[alpha, dict.clone()],
                app(
                    c("Pow", &[u.clone(), Level::zero()]),
                    [fv(&a), c("Nat", &[])],
                ),
                app(
                    c("Pow.mk", &[u.clone(), Level::zero()]),
                    [
                        fv(&a),
                        c("Nat", &[]),
                        app(
                            c("NatPow.pow", std::slice::from_ref(&u)),
                            [fv(&a), fv(&dict)],
                        ),
                    ],
                ),
                Some(1000),
            )?;
            seed.named_instance(
                "instNatPowNat",
                &[],
                &[],
                Expr::app(c("NatPow", &[Level::zero()]), c("Nat", &[])),
                app(
                    c("NatPow.mk", &[Level::zero()]),
                    [c("Nat", &[]), c("Nat.pow", &[])],
                ),
                None,
            )?;
            continue;
        }
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
        let instance_name = match homogeneous {
            "Add" | "Sub" | "Mul" => format!("inst{homogeneous}Nat"),
            "Div" | "Mod" => format!("Nat.inst{homogeneous}"),
            "Append" => "instAppendString".to_owned(),
            _ => format!("Nat.inst{homogeneous}"),
        };
        seed.named_instance(
            &instance_name,
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
    let eq_dict = local(
        "inst",
        Expr::app(c("DecidableEq", &[succ(&u)?]), fv(&a)),
        BinderInfo::InstImplicit,
    );
    let x = local("x", fv(&a), BinderInfo::Default);
    let y = local("y", fv(&a), BinderInfo::Default);
    let proposition = app(c("Eq", &[succ(&u)?]), [fv(&a), fv(&x), fv(&y)]);
    let equality = close(
        &[x.clone(), y.clone()],
        app(
            c("decide", &[]),
            [proposition, app(fv(&eq_dict), [fv(&x), fv(&y)])],
        ),
        true,
    )?;
    let mut alpha = a;
    alpha.binder_info = BinderInfo::Implicit;
    seed.named_instance(
        "instBEqOfDecidableEq",
        &["u"],
        &[alpha.clone(), eq_dict],
        Expr::app(c("BEq", std::slice::from_ref(&u)), fv(&alpha)),
        app(c("BEq.mk", &[u]), [fv(&alpha), equality]),
        None,
    )?;
    seed.priorities.push((n("instBEqOfDecidableEq"), 500));
    // The opaque String seed has a Boolean extern, not the Reference's full
    // String equality proof interface. Keep this dictionary explicitly native.
    seed.instance(
        "beqString",
        &[],
        &[],
        Expr::app(c("BEq", &[Level::zero()]), c("String", &[])),
        app(
            c("BEq.mk", &[Level::zero()]),
            [c("String", &[]), c("String.decEq", &[])],
        ),
        None,
    )?;
    Ok(seed)
}
