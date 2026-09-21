//! Independent named-local fixtures, shared by checker and two-seat tests.
//! This does not use either checker's inductive/recursor reconstruction code.
#![forbid(unsafe_code)]
#![allow(dead_code)]
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;

pub fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(n: &Name, levels: &[Name]) -> Expr {
    Expr::const_(
        n.clone(),
        levels.iter().cloned().map(Level::param).collect(),
    )
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
#[derive(Clone)]
struct B {
    id: FVarId,
    user_name: Name,
    ty: Expr,
}
impl B {
    fn new(label: &str, ty: Expr) -> Self {
        Self {
            id: FVarId(name(label)),
            user_name: name(label),
            ty,
        }
    }
    fn named(mut self, user_name: Name) -> Self {
        self.user_name = user_name;
        self
    }
    fn e(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}
fn close(bs: &[B], mut body: Expr, lambda: bool) -> Expr {
    for b in bs.iter().rev() {
        body = body.abstract_fvar(&b.id, 0).unwrap();
        body = if lambda {
            Expr::lam(b.user_name.clone(), b.ty.clone(), body, BinderInfo::Default)
        } else {
            Expr::forall_e(b.user_name.clone(), b.ty.clone(), body, BinderInfo::Default)
        };
    }
    body
}
#[derive(Clone)]
struct Child {
    field: B,
    arguments: Vec<B>,
    family: usize,
    indices: Vec<Expr>,
}
#[derive(Clone)]
struct C {
    name: Name,
    family: usize,
    fields: Vec<B>,
    indices: Vec<Expr>,
    children: Vec<Child>,
}
#[derive(Clone)]
pub struct Type {
    pub name: Name,
    pub ty: Expr,
    pub indices: usize,
    pub ctors: Vec<Name>,
}
#[derive(Clone)]
pub struct Ctor {
    pub name: Name,
    pub ty: Expr,
    pub family: usize,
    pub index: usize,
    pub fields: usize,
}
#[derive(Clone)]
pub struct Rule {
    pub ctor: Name,
    pub fields: usize,
    pub rhs: Expr,
}
#[derive(Clone)]
pub struct Rec {
    pub name: Name,
    pub ty: Expr,
    pub indices: usize,
    pub rules: Vec<Rule>,
}
#[derive(Clone)]
pub struct Fixture {
    pub names: Vec<Name>,
    pub levels: Vec<Name>,
    pub rec_levels: Vec<Name>,
    pub parameters: usize,
    pub types: Vec<Type>,
    pub ctors: Vec<Ctor>,
    pub recs: Vec<Rec>,
    pub recursive: bool,
    pub reflexive: bool,
}
#[derive(Clone, Copy, Default, Debug)]
pub enum Mutation {
    #[default]
    None,
    MultipleChildren,
    WrongCallFamily,
    SwapMotives,
    SwapMinors,
    MissingInductionHypothesis,
    MissingArgumentLambda,
    WrongChildIndex,
    NegativeCrossFamily,
    NonuniformParameter,
    FalseRecursive,
    FalseReflexive,
    WrongResultFamily,
}

pub fn fixture(
    generic: bool,
    indexed: bool,
    higher: bool,
    families: usize,
    mutation: Mutation,
) -> Fixture {
    assert!(families >= 2 && (!indexed || (families == 2 && generic)) && (!higher || generic));
    let names: Vec<_> = (0..families).map(|i| name(&format!("Mutual{i}"))).collect();
    let levels = if generic { vec![name("u")] } else { vec![] };
    let result = if generic {
        Level::succ(Level::param(name("u"))).unwrap()
    } else {
        Level::one()
    };
    let motive_level = if generic { name("u_1") } else { name("u") };
    let mut rec_levels = vec![motive_level.clone()];
    rec_levels.extend_from_slice(&levels);
    let a = B::new("A", Expr::sort(result.clone()));
    let x = B::new("type_argument", a.e());
    let b = B::new(
        "B",
        close(std::slice::from_ref(&x), Expr::sort(result.clone()), false),
    );
    let parameters = if generic {
        vec![a.clone(), b.clone()]
    } else {
        vec![]
    };
    let family_type = |i: usize, indices: Vec<Expr>| {
        app(
            constant(&names[i], &levels),
            parameters.iter().map(B::e).chain(indices),
        )
    };
    let mut indices = Vec::new();
    let mut majors = Vec::new();
    let mut motives = Vec::new();
    for i in 0..families {
        let mut is = Vec::new();
        if indexed {
            let x = B::new(&format!("index{i}"), a.e());
            is.push(x.clone());
            if i == 1 {
                is.push(B::new("dependent_index", app(b.e(), [x.e()])));
            }
        }
        let major = B::new(
            &format!("major{i}"),
            family_type(i, is.iter().map(B::e).collect()),
        )
        .named(name("t"));
        let mut args = is.clone();
        args.push(major.clone());
        motives.push(
            B::new(
                &format!("motive{i}"),
                close(&args, Expr::sort(Level::param(motive_level.clone())), false),
            )
            .named(name(&format!("motive_{}", i + 1))),
        );
        majors.push(major);
        indices.push(is);
    }
    let mut cs = Vec::new();
    // A genuine base case prevents a suite of only empty mutually recursive
    // types from hiding a bad computation rule behind the absence of values.
    let leaf_x = B::new("leaf_value", a.e());
    let leaf_b = B::new("leaf_evidence", app(b.e(), [leaf_x.e()]));
    cs.push(C {
        name: name("Mutual0.leaf"),
        family: 0,
        fields: if generic {
            vec![leaf_x.clone(), leaf_b]
        } else {
            vec![]
        },
        indices: if indexed { vec![leaf_x.e()] } else { vec![] },
        children: vec![],
    });
    for family in 0..families {
        let target = (family + 1) % families;
        let mut fields = Vec::new();
        let x = B::new(&format!("value{family}"), a.e());
        let witness = B::new(&format!("witness{family}"), app(b.e(), [x.e()]));
        if indexed {
            fields.push(x.clone());
        }
        let mut child_indices = if indexed { vec![x.e()] } else { vec![] };
        let mut arguments = Vec::new();
        if higher {
            let domain = if matches!(mutation, Mutation::NegativeCrossFamily) && family == 0 {
                family_type(family, if indexed { vec![x.e()] } else { vec![] })
            } else if indexed {
                app(b.e(), [x.e()])
            } else {
                a.e()
            };
            let y = B::new(&format!("argument{family}"), domain);
            arguments.push(y.clone());
            if indexed && target == 1 {
                child_indices.push(y.e());
            }
            if !indexed && !matches!(mutation, Mutation::NegativeCrossFamily) {
                arguments.push(B::new(
                    &format!("dependent_argument{family}"),
                    app(b.e(), [y.e()]),
                ));
            }
        } else if indexed && target == 1 {
            fields.push(witness.clone());
            child_indices.push(witness.e());
        }
        if indexed && family == 1 {
            fields.push(witness.clone());
        }
        let mut child_type = family_type(target, child_indices.clone());
        if matches!(mutation, Mutation::NonuniformParameter) && family == 0 && generic {
            let fake_b = close(std::slice::from_ref(&x), a.e(), true);
            child_type = app(
                constant(&names[target], &levels),
                [a.e(), fake_b].into_iter().chain(child_indices.clone()),
            );
        }
        let field = B::new(
            &format!("children{family}"),
            close(&arguments, child_type, false),
        );
        fields.push(field.clone());
        let mut result_indices = if indexed { vec![x.e()] } else { vec![] };
        if indexed && family == 1 {
            result_indices.push(witness.e());
        }
        let mut children = vec![Child {
            field,
            arguments: arguments.clone(),
            family: target,
            indices: child_indices,
        }];
        if matches!(mutation, Mutation::MultipleChildren) {
            // Interleave a nonrecursive field before a second, self-recursive
            // child. Both IH offsets and the destination family's index spine
            // differ from the first child's; neither is a shared-position case.
            if generic {
                fields.push(B::new(&format!("interleaved{family}"), a.e()));
            }
            let field = B::new(
                &format!("sibling{family}"),
                close(
                    &arguments,
                    family_type(family, result_indices.clone()),
                    false,
                ),
            );
            fields.push(field.clone());
            children.push(Child {
                field,
                arguments,
                family,
                indices: result_indices.clone(),
            });
        }
        cs.push(C {
            name: name(&format!("Mutual{family}.node")),
            family,
            fields,
            indices: result_indices,
            children,
        });
    }
    let mut minors = Vec::new();
    for (index, c) in cs.iter().enumerate() {
        let mut bs = c.fields.clone();
        for (r, child) in c.children.iter().enumerate() {
            let value = app(child.field.e(), child.arguments.iter().map(B::e));
            let conclusion = app(
                motives[child.family].e(),
                child.indices.iter().cloned().chain([value]),
            );
            bs.push(
                B::new(
                    &format!("ih{index}_{r}"),
                    close(&child.arguments, conclusion, false),
                )
                .named(name(&format!(
                    "{}_ih",
                    child.field.user_name.to_display_string()
                ))),
            );
        }
        let constructed = app(
            constant(&c.name, &levels),
            parameters.iter().map(B::e).chain(c.fields.iter().map(B::e)),
        );
        let conclusion = app(
            motives[c.family].e(),
            c.indices.iter().cloned().chain([constructed]),
        );
        minors.push(
            B::new(&format!("minor{index}"), close(&bs, conclusion, false))
                .named(name(if index == 0 { "leaf" } else { "node" })),
        );
    }
    let prefix: Vec<_> = parameters
        .iter()
        .chain(&motives)
        .chain(&minors)
        .cloned()
        .collect();
    let mut types = Vec::new();
    let mut ctors = Vec::new();
    let mut recs = Vec::new();
    for family in 0..families {
        let mut bs = parameters.clone();
        bs.extend_from_slice(&indices[family]);
        types.push(Type {
            name: names[family].clone(),
            ty: close(&bs, Expr::sort(result.clone()), false),
            indices: indices[family].len(),
            ctors: cs
                .iter()
                .filter(|c| c.family == family)
                .map(|c| c.name.clone())
                .collect(),
        });
        let mut bs = prefix.clone();
        bs.extend_from_slice(&indices[family]);
        bs.push(majors[family].clone());
        let ty = close(
            &bs,
            app(
                motives[family].e(),
                indices[family].iter().map(B::e).chain([majors[family].e()]),
            ),
            false,
        );
        let mut rules = Vec::new();
        for (cidx, (index, c)) in cs
            .iter()
            .enumerate()
            .filter(|(_, c)| c.family == family)
            .enumerate()
        {
            let mut bs = parameters.clone();
            bs.extend_from_slice(&c.fields);
            let result_family = if matches!(mutation, Mutation::WrongResultFamily) && family == 0 {
                1
            } else {
                family
            };
            ctors.push(Ctor {
                name: c.name.clone(),
                ty: close(&bs, family_type(result_family, c.indices.clone()), false),
                family,
                index: cidx,
                fields: c.fields.len(),
            });
            let mut rhs = app(minors[index].e(), c.fields.iter().map(B::e));
            for child in &c.children {
                let target = if matches!(mutation, Mutation::WrongCallFamily) {
                    family
                } else {
                    child.family
                };
                let mut args: Vec<_> = parameters.iter().map(B::e).collect();
                let mut ms: Vec<_> = motives.iter().map(B::e).collect();
                if matches!(mutation, Mutation::SwapMotives) {
                    ms.swap(0, 1);
                }
                args.extend(ms);
                let mut ns: Vec<_> = minors.iter().map(B::e).collect();
                if matches!(mutation, Mutation::SwapMinors) {
                    ns.swap(0, 1);
                }
                args.extend(ns);
                args.extend(child.indices.iter().cloned());
                if matches!(mutation, Mutation::WrongChildIndex) && !child.indices.is_empty() {
                    args.pop();
                    args.push(a.e());
                }
                args.push(app(child.field.e(), child.arguments.iter().map(B::e)));
                let call = app(
                    constant(&name(&format!("Mutual{target}.rec")), &rec_levels),
                    args,
                );
                let call = if matches!(mutation, Mutation::MissingArgumentLambda) {
                    call
                } else {
                    close(&child.arguments, call, true)
                };
                if !matches!(mutation, Mutation::MissingInductionHypothesis) {
                    rhs = Expr::app(rhs, call);
                }
            }
            let mut bs = prefix.clone();
            bs.extend_from_slice(&c.fields);
            rules.push(Rule {
                ctor: c.name.clone(),
                fields: c.fields.len(),
                rhs: close(&bs, rhs, true),
            });
        }
        recs.push(Rec {
            name: name(&format!("Mutual{family}.rec")),
            ty,
            indices: indices[family].len(),
            rules,
        });
    }
    Fixture {
        names,
        levels,
        rec_levels,
        parameters: parameters.len(),
        types,
        ctors,
        recs,
        recursive: !matches!(mutation, Mutation::FalseRecursive),
        reflexive: higher && !matches!(mutation, Mutation::FalseReflexive),
    }
}
