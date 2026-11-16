//! Closed subterms (`external_bound_span == 0`) shared across sibling or nested
//! binder bodies keep their canonical `TermReference` origin across generated
//! telescope arenas instead of re-inferring `2^depth` times.
//!
//! In `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective`
//! (`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`), shared
//! DAG subterms inside nested `clear_value` / `Classical.choose` / `Cone.mk`
//! lambdas were copied into fresh `ArenaSource::Generated(g)` arenas on each
//! binder opening, causing `InferenceEngine` to visit 219,949 lambda binders and
//! 12,189,808 application nodes before exhausting 100M steps. Propagating
//! closed-node origins (`scope.external == 0`) through `materialize_telescope_subterm`
//! preserves O(1) `inferred_types` hits across all enclosing telescopes while
//! keeping open bound subterms (`scope.external > 0`) strictly separated.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::infer::InferenceDeferred;
use fln_checker::wire as tag;
use fln_core::expr::ExprNode as CoreExprNode;
use fln_hash::canon::CanonWriter;

fn decoded_dag(expression: &Expr) -> WireExpr {
    fn children(node: &CoreExprNode) -> [Option<&Expr>; 3] {
        match node {
            CoreExprNode::App { f, a } => [Some(f), Some(a), None],
            CoreExprNode::Lam {
                binder_type, body, ..
            }
            | CoreExprNode::ForallE {
                binder_type, body, ..
            } => [Some(binder_type), Some(body), None],
            CoreExprNode::LetE {
                type_, value, body, ..
            } => [Some(type_), Some(value), Some(body)],
            CoreExprNode::MData { expr, .. } | CoreExprNode::Proj { expr, .. } => {
                [Some(expr), None, None]
            }
            _ => [None, None, None],
        }
    }
    let identity = |term: &Expr| std::ptr::from_ref(term.node()).addr();
    let mut index = std::collections::HashMap::<usize, u32>::new();
    let mut order = Vec::<&Expr>::new();
    let mut pending = vec![(expression, false)];
    while let Some((term, done)) = pending.pop() {
        let id = identity(term);
        if index.contains_key(&id) {
            continue;
        }
        if done {
            index.insert(id, u32::try_from(order.len()).expect("small dag"));
            order.push(term);
            continue;
        }
        pending.push((term, true));
        for child in children(term.node()).into_iter().rev().flatten() {
            if !index.contains_key(&identity(child)) {
                pending.push((child, false));
            }
        }
    }
    let reference = |term: &Expr| index[&identity(term)];
    let mut w = CanonWriter::new();
    w.schema(tag::SCHEMA_EXPR_DAG);
    w.u64(order.len() as u64);
    for term in order {
        match term.node() {
            CoreExprNode::BVar { idx } => {
                w.u8(tag::EXPR_BVAR);
                w.u32(*idx);
            }
            CoreExprNode::Const { name, levels } => {
                w.u8(tag::EXPR_CONST);
                name.write_body(&mut w);
                w.u64(levels.len() as u64);
                for level in levels {
                    level.write_body(&mut w);
                }
            }
            CoreExprNode::App { f, a } => {
                w.u8(tag::EXPR_APP);
                w.u32(reference(f));
                w.u32(reference(a));
            }
            CoreExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(tag::EXPR_LAM);
                binder_name.write_body(&mut w);
                w.u32(reference(binder_type));
                w.u32(reference(body));
                w.u8(binder_info.to_u64() as u8);
            }
            other => panic!("unexpected node in test dag: {other:?}"),
        }
    }
    match tag::decode_expr_dag(&w.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("DAG wire expression must decode: {other:?}"),
    }
}

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}

fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}

fn lam(name: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name(name), domain, body, BinderInfo::Default)
}

fn bv(index: u32) -> Expr {
    Expr::bvar(index).expect("small bound index")
}

fn ty() -> Expr {
    Expr::sort(Level::one())
}

fn typed_axiom(label: &str, decl_ty: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            vec![],
            decoded(&decl_ty),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}

fn environment() -> ConstantEnvironment {
    let t = c("T");
    let u = c("U");
    let t_to_t = arrow(t.clone(), t.clone());
    environment_of(vec![
        typed_axiom("T", ty()),
        typed_axiom("U", ty()),
        typed_axiom("c0", t.clone()),
        typed_axiom("u0", u.clone()),
        typed_axiom("idT", t_to_t.clone()),
        typed_axiom("comb", arrow(t.clone(), t_to_t)),
        typed_axiom(
            "pairTU",
            arrow(arrow(t, c("T")), arrow(arrow(u, c("T")), c("T"))),
        ),
    ])
}

/// `D_0 = fun z : T => leaf`;
/// `D_{i+1} = fun z : T => comb (D_i c0) ((fun w : T => comb (D_i w) w) z)`.
///
/// Every `D_i` is closed (`external_bound_span == 0`) and pointer-shared twice
/// inside `D_{i+1}`: once in `D_{i+1}`'s body arena and once inside the inner
/// `fun w` arena. Without closed-subterm origin propagation, `D_0` is inferred
/// `2^DEPTH` (`1,048,576`) times (>10M steps); with it, each `D_i` is inferred
/// once (<10,000 steps).
const DEPTH: usize = 20;
const STEP_BUDGET: u64 = 50_000;

fn nested_shared_lambdas(leaf: Expr) -> Expr {
    let t = c("T");
    let comb = c("comb");
    let c0 = c("c0");
    let bv0 = bv(0);
    let mut d = lam("z", t.clone(), leaf);
    for _ in 0..DEPTH {
        let inner = lam(
            "w",
            t.clone(),
            app(comb.clone(), [app(d.clone(), [bv0.clone()]), bv0.clone()]),
        );
        d = lam(
            "z",
            t.clone(),
            app(
                comb.clone(),
                [app(d, [c0.clone()]), app(inner, [bv0.clone()])],
            ),
        );
    }
    d
}

fn budget() -> AdmissionBudget {
    AdmissionBudget::new(
        InferenceBudget::new(
            STEP_BUDGET,
            u64::MAX,
            TermBudget::unlimited(),
            TermBudget::unlimited(),
        ),
        WhnfBudget::unlimited(),
        InferenceBudget::unlimited().defeq,
    )
}

#[test]
fn closed_subterms_shared_across_nested_lambdas_infer_once() {
    let env = environment();
    let t = c("T");
    let body = decoded_dag(&nested_shared_lambdas(c("c0")));
    assert!(body.nodes().len() < 200, "got {} nodes", body.nodes().len());
    let candidate = definition("shared_lambdas", decoded(&arrow(t, c("T"))), body);
    let verdict = admit(&env, &candidate, budget());
    assert!(matches!(verdict, Verdict::Admitted(_)), "{verdict:?}");
}

#[test]
fn ill_typed_leaf_below_shared_nested_lambdas_is_still_rejected() {
    let env = environment();
    let t = c("T");
    let body = decoded_dag(&nested_shared_lambdas(c("u0")));
    let candidate = definition("bad_shared_leaf", decoded(&arrow(t, c("T"))), body);
    let verdict = admit(&env, &candidate, budget());
    assert!(
        matches!(
            &verdict,
            Verdict::Deferred(AdmissionDeferred::BodyTypeInference { requirement, .. })
                if matches!(
                    requirement.as_ref(),
                    InferenceDeferred::ApplicationConversion { argument: 0, .. }
                )
        ),
        "{verdict:?}"
    );
}

#[test]
fn open_subterm_shared_under_distinct_binder_domains_is_not_conflated() {
    let env = environment();
    // Share the OPEN application `idT #0` (`external == 1`) across BOTH
    // `fun (a : T) => idT #0` (well-typed) and `fun (b : U) => idT #0`
    // (ill-typed because `#0 : U`, not `T`). `SCHEMA_EXPR_DAG` preserves the
    // shared `idT #0` node in `WireExpr`.
    let open_call = app(c("idT"), [bv(0)]);
    let body = app(
        c("pairTU"),
        [
            lam("a", c("T"), open_call.clone()),
            lam("b", c("U"), open_call),
        ],
    );
    let raw_body = decoded_dag(&body);
    assert!(
        raw_body.nodes().len() <= 10,
        "SCHEMA_EXPR_DAG must share `idT #0` across both lambdas (got {} nodes)",
        raw_body.nodes().len()
    );
    let candidate = definition("open_dag_sharing", decoded(&c("T")), raw_body);
    let verdict = admit(&env, &candidate, budget());
    assert!(
        matches!(
            &verdict,
            Verdict::Deferred(AdmissionDeferred::BodyTypeInference { requirement, .. })
                if matches!(
                    requirement.as_ref(),
                    InferenceDeferred::ApplicationConversion { argument: 0, .. }
                )
        ),
        "an open subterm shared across binders of different types must not reuse the first binder's typing: {verdict:?}"
    );
}
