//! Term-store identity (bead `fln-49c`, plan §7.1b).
//!
//! The **alpha-canonical digest** is an auxiliary identity that strips exactly the
//! freedom in bound-variable *names* and nothing else, so kernel-side defeq and whnf
//! caches let alpha-varied duplicates share reduction work without disturbing the
//! metaprogram-visible plane, where binder names are observable and must round-trip
//! exactly.
//!
//! # The boundary, which is the whole specification
//!
//! Alpha-free — a rename here must NOT change the digest:
//! * `Lam.binder_name`
//! * `ForallE.binder_name`
//! * `LetE.decl_name`
//!
//! NOT alpha-free — a change here MUST change the digest:
//! * `Const.name` and its level arguments
//! * `Proj.struct_name` and its index
//! * every key and value in `MData.data`
//! * `binder_info`, `non_dep`, literals, sorts, and every de Bruijn index
//!
//! Getting that boundary wrong is a silent identity bug in either direction: strip
//! too much and distinct terms collide in a cache that then returns the wrong
//! reduction; strip too little and alpha-equivalent terms never share, which is
//! merely slow but also means the digest is not doing the job it exists for. The
//! tests assert both directions, because a one-sided test — "alpha-equal terms agree"
//! — is satisfied by a digest that returns a constant.
//!
//! # Why this is not `Expr::to_canonical_bytes`
//!
//! An alpha-canonical digest is by definition a *different* function from the
//! registered `fln.canon.expr` encoding: that encoding keeps binder names, because
//! the visible plane needs them. So this cannot reuse it wholesale. What it does
//! reuse is that encoding for every **leaf**, where no binder can occur — so the
//! bytes under a `Const`, `Sort`, `Lit`, `BVar`, `FVar` or `MVar` are exactly the
//! frozen registered ones rather than a second hand-rolled encoding that could drift.
//! Interior nodes contribute their own non-alpha-free payload plus their children's
//! digests.
//!
//! The fold is bottom-up over distinct nodes and memoised on node identity, so a
//! shared subterm is digested once. That is not an optimisation: a term DAG can
//! denote a tree astronomically larger than itself, and a digest that expanded it
//! would be the same DAG-bomb exposure the expanded-weight budget exists to refuse.

use std::collections::HashMap;

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::outcome::{BoundedText, Inconclusive, InconclusiveCause, Outcome, ResourceUsage};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, DomainHasher};

/// Domain-separation tag. Versioned: a change to what the digest strips or keeps is a
/// new tag, never a redefinition of this one, because caches keyed on it would
/// otherwise silently mix two identity notions.
const ALPHA_DIGEST_TAG: &[u8] = b"fln.term.alpha-canonical/1";

/// Node-kind tags. Explicit and exhaustive: a new `ExprNode` variant fails to compile
/// here rather than defaulting into another kind's encoding.
const KIND_LEAF: u8 = 0;
const KIND_APP: u8 = 1;
const KIND_LAM: u8 = 2;
const KIND_FORALL: u8 = 3;
const KIND_LET: u8 = 4;
const KIND_MDATA: u8 = 5;
const KIND_PROJ: u8 = 6;

const fn binder_info_tag(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn node_key(expr: &Expr) -> *const ExprNode {
    std::ptr::from_ref(expr.node())
}

/// Children of a node, in canonical order.
fn children<'a>(node: &'a ExprNode, out: &mut Vec<&'a Expr>) {
    match node {
        ExprNode::BVar { .. }
        | ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit { .. } => {}
        ExprNode::App { f, a } => {
            out.push(f);
            out.push(a);
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            out.push(binder_type);
            out.push(body);
        }
        ExprNode::LetE {
            type_, value, body, ..
        } => {
            out.push(type_);
            out.push(value);
            out.push(body);
        }
        ExprNode::MData { expr, .. } => out.push(expr),
        ExprNode::Proj { expr, .. } => out.push(expr),
    }
}

/// The alpha-canonical digest of `root`.
///
/// Total: the traversal is iterative, so depth is bounded by the heap rather than the
/// stack, and every node shape is handled explicitly.
pub fn alpha_canonical_digest(root: &Expr) -> Digest {
    // Post-order over distinct nodes, iteratively.
    enum Step<'a> {
        Enter(&'a Expr),
        Exit(&'a Expr),
    }
    let mut order: Vec<&Expr> = Vec::new();
    let mut seen: HashMap<*const ExprNode, ()> = HashMap::new();
    let mut stack = vec![Step::Enter(root)];
    let mut kids: Vec<&Expr> = Vec::new();
    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr) => {
                if seen.insert(node_key(expr), ()).is_some() {
                    continue;
                }
                stack.push(Step::Exit(expr));
                kids.clear();
                children(expr.node(), &mut kids);
                for child in kids.iter().rev() {
                    stack.push(Step::Enter(child));
                }
            }
            Step::Exit(expr) => order.push(expr),
        }
    }

    let mut digests: HashMap<*const ExprNode, Digest> = HashMap::with_capacity(order.len());
    for expr in &order {
        let mut hasher = DomainHasher::new(Domain::DeclContent);
        hasher.update(ALPHA_DIGEST_TAG);
        hasher.update(&[0]);
        let node = expr.node();
        let mut payload = CanonWriter::new();
        let kind = match node {
            // Leaves carry no binder, so their frozen registered encoding is exactly
            // right and there is no second encoder to drift from it.
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => {
                payload.bytes(&expr.to_canonical_bytes());
                KIND_LEAF
            }
            ExprNode::App { .. } => KIND_APP,
            // The binder NAME is deliberately absent; binder_info is not, because a
            // change of implicitness is a different term, not a renaming.
            ExprNode::Lam { binder_info, .. } => {
                payload.u8(binder_info_tag(*binder_info));
                KIND_LAM
            }
            ExprNode::ForallE { binder_info, .. } => {
                payload.u8(binder_info_tag(*binder_info));
                KIND_FORALL
            }
            // `decl_name` is a bound name and is stripped; `non_dep` is not.
            ExprNode::LetE { non_dep, .. } => {
                payload.bool(*non_dep);
                KIND_LET
            }
            // Metadata is metaprogram-visible: every key and value stays.
            ExprNode::MData { data, .. } => {
                data.write_body(&mut payload);
                KIND_MDATA
            }
            ExprNode::Proj {
                struct_name, idx, ..
            } => {
                struct_name.write_body(&mut payload);
                payload.u64(*idx);
                KIND_PROJ
            }
        };
        let payload = payload.into_bytes();
        hasher.update(&[kind]);
        hasher.update(&(payload.len() as u64).to_le_bytes());
        hasher.update(&payload);

        kids.clear();
        children(node, &mut kids);
        hasher.update(&(kids.len() as u64).to_le_bytes());
        for child in &kids {
            let child_digest = digests
                .get(&node_key(child))
                .copied()
                // Post-order guarantees this is populated.
                .unwrap_or(Digest([0; 32]));
            hasher.update(&child_digest.0);
        }
        digests.insert(node_key(expr), hasher.finalize());
    }

    digests
        .get(&node_key(root))
        .copied()
        .unwrap_or(Digest([0; 32]))
}

/// What a caller allows one term to cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WeightBudget {
    /// Maximum size of the tree the DAG denotes.
    pub max_expanded_weight: u64,
    /// Maximum number of distinct nodes visited. Bounds the traversal itself, so a
    /// term that is merely enormous (rather than merely deep) also stops.
    pub max_distinct_nodes: u64,
}

impl WeightBudget {
    pub const fn new(max_expanded_weight: u64, max_distinct_nodes: u64) -> Self {
        Self {
            max_expanded_weight,
            max_distinct_nodes,
        }
    }
}

/// Exact cost facts for one term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WeightReport {
    /// Size of the tree the DAG denotes.
    pub expanded_weight: u128,
    /// Distinct nodes actually stored.
    pub distinct_nodes: u64,
    /// Child edges traversed.
    pub edges: u64,
    /// Longest root-to-leaf path in the **denoted tree**, counting nodes. A leaf is 1.
    ///
    /// This is the fact `franken_lean-j8h` names and that this report previously did not
    /// carry, which is why [`crate::environment::DeclarationUsage`] documented maximum
    /// logical depth as absent rather than approximating it.
    ///
    /// It is the longest path, **not** the sum of paths and not the stored height: a
    /// shared diamond denotes a tree deeper than its node count suggests in one
    /// direction and shallower in the other, so depth folds with `max` where
    /// `expanded_weight` folds with `+`. Sharing changes the weight and leaves the depth
    /// alone, which is exactly the property that makes it worth reporting separately.
    ///
    /// Bounded by `distinct_nodes`: a path in a DAG cannot revisit a node, so this
    /// cannot exceed the number of distinct nodes and cannot wrap.
    pub max_logical_depth: u64,
}

impl WeightReport {
    /// How much smaller the stored DAG is than the tree it denotes. `1` means no
    /// sharing at all; larger means the term is shared.
    pub fn sharing_factor(&self) -> u128 {
        let distinct = u128::from(self.distinct_nodes).max(1);
        self.expanded_weight / distinct
    }
}

/// A budget stop, in the structural-budget axis `franken_lean-vui8` added.
///
/// The unit matters and is not decoration: `ExpandedWeight` says the DENOTED tree
/// was too large, `ProducedNodes` says the STORED graph was. A caller that cannot
/// tell them apart cannot react — shrinking the input helps the second and may not
/// help the first at all. Neither is a statement that the term is malformed, which is
/// the distinction the taxonomy now lets this seam make rather than collapse.
fn exhausted(unit: StructuralUnit, allowed: u64, observed: u64) -> Inconclusive {
    Inconclusive {
        cause: InconclusiveCause::ResourceExhausted {
            usage: ResourceUsage {
                reason: ResourceReason::StructuralBudget { unit },
                allowed,
                // A stop must report spending past its allowance or it is not a stop;
                // `is_genuine_exhaustion` depends on it.
                observed: observed.max(allowed.saturating_add(1)),
            },
        },
        diagnostic: None,
        // Where the traversal had got to. Diagnostic only: `allowed`/`observed` size
        // a retry, this says which measurement bound so a caller can tell a denoted
        // -size stop from a stored-graph one at a glance.
        progress: Some(Box::new(BoundedText::new(unit.as_str()))),
    }
}

/// Measure what `root` expands to, refusing before the budget is exceeded.
///
/// **Charges for what the term DENOTES, not what it looks like.** A term's wire size
/// and its stored node count are both blind to sharing: `f x x` over a chain of
/// shared nodes is small on disk, small in memory, and astronomical expanded, because
/// each level that references the level below it twice doubles the tree it denotes.
/// A size check that counts bytes or distinct nodes waves that through, and the work
/// it triggers later dies far from the input that caused it — usually as an
/// allocation abort rather than a diagnosis. This is the same shape as the fln-olean
/// defect fixed in `c26b8ed`: a length that escapes the budget before the storage it
/// implies is charged.
///
/// Returns [`Outcome::Complete`] with exact facts, or [`Outcome::Inconclusive`] when a
/// budget binds. It never rejects — a term over budget is not a term judged
/// ill-formed — and the outcome's own `cache_admission` refuses to memoize it.
pub fn expanded_weight(root: &Expr, budget: &WeightBudget) -> Outcome<WeightReport> {
    // Phase 1: collect distinct nodes in post-order, iteratively. An explicit stack is
    // what makes a deep term a measurement rather than a stack overflow.
    let mut order: Vec<*const ExprNode> = Vec::new();
    let mut seen: HashMap<*const ExprNode, ()> = HashMap::new();
    let mut nodes: Vec<&Expr> = Vec::new();
    let mut edges: u64 = 0;

    enum Step<'a> {
        Enter(&'a Expr),
        Exit(&'a Expr),
    }
    let mut stack = vec![Step::Enter(root)];
    let mut kids: Vec<&Expr> = Vec::new();
    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr) => {
                let key = node_key(expr);
                if seen.insert(key, ()).is_some() {
                    continue;
                }
                if u64::try_from(seen.len()).unwrap_or(u64::MAX) > budget.max_distinct_nodes {
                    return Outcome::Inconclusive(exhausted(
                        StructuralUnit::ProducedNodes,
                        budget.max_distinct_nodes,
                        u64::try_from(seen.len()).unwrap_or(u64::MAX),
                    ));
                }
                stack.push(Step::Exit(expr));
                kids.clear();
                children(expr.node(), &mut kids);
                for child in kids.iter().rev() {
                    stack.push(Step::Enter(child));
                }
            }
            Step::Exit(expr) => {
                order.push(node_key(expr));
                nodes.push(expr);
            }
        }
    }

    // Phase 2: fold weights in post-order, so every child is already resolved.
    // Checked u128 throughout: a bomb must stop AT THE BUDGET, never wrap into a
    // small number that then passes.
    let allowed = u128::from(budget.max_expanded_weight);
    let mut weights: HashMap<*const ExprNode, u128> = HashMap::with_capacity(order.len());
    // Depth folds beside the weight, over the same post-order, so it costs one `u64` per
    // distinct node and no second traversal. `max` where the weight uses `+`: a node's
    // depth is one more than its DEEPEST child, not the sum of its children.
    let mut depths: HashMap<*const ExprNode, u64> = HashMap::with_capacity(order.len());
    for expr in &nodes {
        kids.clear();
        children(expr.node(), &mut kids);
        let mut weight: u128 = 1;
        let mut deepest_child: u64 = 0;
        for child in &kids {
            edges = edges.saturating_add(1);
            deepest_child = deepest_child.max(depths.get(&node_key(child)).copied().unwrap_or(1));
            let child_weight = weights.get(&node_key(child)).copied().unwrap_or(1);
            match weight.checked_add(child_weight) {
                Some(next) => weight = next,
                None => {
                    return Outcome::Inconclusive(exhausted(
                        StructuralUnit::ExpandedWeight,
                        budget.max_expanded_weight,
                        u64::MAX,
                    ));
                }
            }
        }
        if weight > allowed {
            return Outcome::Inconclusive(exhausted(
                StructuralUnit::ExpandedWeight,
                budget.max_expanded_weight,
                u64::try_from(weight).unwrap_or(u64::MAX),
            ));
        }
        weights.insert(node_key(expr), weight);
        // Saturating rather than checked, and that is not a shortcut: a path in a DAG
        // cannot revisit a node, so depth is bounded by `distinct_nodes`, which is itself
        // already refused above `budget.max_distinct_nodes`. The saturation is
        // unreachable; it is here so the arithmetic is total on its face.
        depths.insert(node_key(expr), deepest_child.saturating_add(1));
    }

    Outcome::Complete(WeightReport {
        expanded_weight: weights.get(&node_key(root)).copied().unwrap_or(1),
        distinct_nodes: u64::try_from(order.len()).unwrap_or(u64::MAX),
        edges,
        max_logical_depth: depths.get(&node_key(root)).copied().unwrap_or(1),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::{DataValue, KVMap};
    use fln_core::outcome::CacheAdmission;

    fn n(value: &str) -> Name {
        Name::str(Name::anonymous(), value)
    }

    fn c(value: &str) -> Expr {
        Expr::const_(n(value), vec![])
    }

    fn ty() -> Expr {
        Expr::sort(Level::zero())
    }

    fn kv(key: &str, value: &str) -> KVMap {
        let mut map = KVMap::new();
        map.insert(n(key), DataValue::OfString(value.to_owned()));
        map
    }

    /// DIRECTION ONE: renaming any of the three alpha-free fields must not move the
    /// digest. On its own this proves nothing — a digest returning a constant passes
    /// it — which is why it is paired with the test below.
    #[test]
    fn alpha_renaming_the_three_bound_names_does_not_move_the_digest() {
        // Lam.binder_name
        let lam_x = Expr::lam(n("x"), ty(), Expr::app(c("f"), c("a")), BinderInfo::Default);
        let lam_y = Expr::lam(n("y"), ty(), Expr::app(c("f"), c("a")), BinderInfo::Default);
        assert_eq!(
            alpha_canonical_digest(&lam_x),
            alpha_canonical_digest(&lam_y),
            "Lam.binder_name is alpha-free"
        );

        // ForallE.binder_name
        let all_x = Expr::forall_e(n("x"), ty(), c("b"), BinderInfo::Implicit);
        let all_z = Expr::forall_e(n("z"), ty(), c("b"), BinderInfo::Implicit);
        assert_eq!(
            alpha_canonical_digest(&all_x),
            alpha_canonical_digest(&all_z),
            "ForallE.binder_name is alpha-free"
        );

        // LetE.decl_name
        let let_a = Expr::let_e(n("a"), ty(), c("v"), c("b"), false);
        let let_b = Expr::let_e(n("b2"), ty(), c("v"), c("b"), false);
        assert_eq!(
            alpha_canonical_digest(&let_a),
            alpha_canonical_digest(&let_b),
            "LetE.decl_name is alpha-free"
        );

        // Nested, so the stripping is not merely a top-level special case.
        let nested_p = Expr::lam(
            n("p"),
            ty(),
            Expr::forall_e(
                n("q"),
                ty(),
                Expr::let_e(n("r"), ty(), c("v"), c("b"), true),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let nested_u = Expr::lam(
            n("u"),
            ty(),
            Expr::forall_e(
                n("v2"),
                ty(),
                Expr::let_e(n("w"), ty(), c("v"), c("b"), true),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        assert_eq!(
            alpha_canonical_digest(&nested_p),
            alpha_canonical_digest(&nested_u),
            "nested bound names are alpha-free at every depth"
        );
    }

    /// DIRECTION TWO: everything that is NOT alpha-free must move the digest. This is
    /// the half that kills a digest ignoring its input, and each row names the field
    /// it protects so a regression says which distinction was lost.
    #[test]
    fn perturbing_any_non_alpha_free_field_moves_the_digest() {
        let base_lam = Expr::lam(n("x"), ty(), Expr::app(c("f"), c("a")), BinderInfo::Default);
        let cases: Vec<(&str, Expr)> = vec![
            // Const.name — the classic collision if it were stripped with binder names.
            (
                "Const.name",
                Expr::lam(n("x"), ty(), Expr::app(c("g"), c("a")), BinderInfo::Default),
            ),
            // Const level arguments.
            (
                "Const.levels",
                Expr::lam(
                    n("x"),
                    ty(),
                    Expr::app(Expr::const_(n("f"), vec![Level::param(n("u"))]), c("a")),
                    BinderInfo::Default,
                ),
            ),
            // binder_info: a change of implicitness is a different term, not a rename.
            (
                "binder_info",
                Expr::lam(
                    n("x"),
                    ty(),
                    Expr::app(c("f"), c("a")),
                    BinderInfo::Implicit,
                ),
            ),
            // Argument order, i.e. the child positions.
            (
                "App child order",
                Expr::lam(n("x"), ty(), Expr::app(c("a"), c("f")), BinderInfo::Default),
            ),
            // The binder TYPE is an ordinary subterm.
            (
                "binder_type",
                Expr::lam(
                    n("x"),
                    Expr::sort(Level::zero().succ().expect("one successor is not too deep")),
                    Expr::app(c("f"), c("a")),
                    BinderInfo::Default,
                ),
            ),
        ];

        let base = alpha_canonical_digest(&base_lam);
        for (field, variant) in &cases {
            assert_ne!(
                base,
                alpha_canonical_digest(variant),
                "{field} must not be stripped by the alpha digest"
            );
        }

        // Proj.struct_name and Proj.idx.
        let proj = Expr::proj(n("S"), 0, c("v"));
        assert_ne!(
            alpha_canonical_digest(&proj),
            alpha_canonical_digest(&Expr::proj(n("T"), 0, c("v"))),
            "Proj.struct_name must not be stripped"
        );
        assert_ne!(
            alpha_canonical_digest(&proj),
            alpha_canonical_digest(&Expr::proj(n("S"), 1, c("v"))),
            "Proj.idx must not be stripped"
        );

        // MData keys and values are metaprogram-visible.
        let mdata = Expr::mdata(kv("k", "v"), c("b"));
        assert_ne!(
            alpha_canonical_digest(&mdata),
            alpha_canonical_digest(&Expr::mdata(kv("k2", "v"), c("b"))),
            "an MData key must not be stripped"
        );
        assert_ne!(
            alpha_canonical_digest(&mdata),
            alpha_canonical_digest(&Expr::mdata(kv("k", "v2"), c("b"))),
            "an MData value must not be stripped"
        );
        assert_ne!(
            alpha_canonical_digest(&mdata),
            alpha_canonical_digest(&c("b")),
            "an MData wrapper is not transparent"
        );

        // LetE.non_dep.
        assert_ne!(
            alpha_canonical_digest(&Expr::let_e(n("a"), ty(), c("v"), c("b"), false)),
            alpha_canonical_digest(&Expr::let_e(n("a"), ty(), c("v"), c("b"), true)),
            "LetE.non_dep must not be stripped"
        );

        // And the anti-constant guard, stated outright rather than inferred: the
        // digests produced across this test are not all one value.
        let mut distinct = std::collections::BTreeSet::new();
        distinct.insert(base);
        for (_, variant) in &cases {
            distinct.insert(alpha_canonical_digest(variant));
        }
        assert_eq!(
            distinct.len(),
            cases.len() + 1,
            "every perturbation must produce its own digest"
        );
    }

    /// Determinism and sharing-independence: the digest is a function of the term's
    /// structure, not of how the DAG happens to be shared or how many times it is
    /// computed.
    #[test]
    fn the_digest_is_deterministic_and_independent_of_sharing() {
        let shared_child = Expr::app(c("f"), c("a"));
        let shared = Expr::app(shared_child.clone(), shared_child);
        // The same value built without sharing the subterm.
        let unshared = Expr::app(Expr::app(c("f"), c("a")), Expr::app(c("f"), c("a")));
        assert_eq!(
            alpha_canonical_digest(&shared),
            alpha_canonical_digest(&unshared),
            "sharing is a representation choice, not an identity"
        );
        assert_eq!(
            alpha_canonical_digest(&shared),
            alpha_canonical_digest(&shared),
            "repeated computation must agree"
        );
    }

    const GENEROUS: WeightBudget = WeightBudget::new(u64::MAX, u64::MAX);

    fn weight_of(expr: &Expr) -> WeightReport {
        match expanded_weight(expr, &GENEROUS) {
            Outcome::Complete(report) => report,
            other => panic!("expected a complete measurement, got {other:?}"),
        }
    }

    /// On a tree, expanded weight is just the node count — the case where a naive
    /// size check happens to be right, pinned so the model is anchored somewhere
    /// obvious.
    #[test]
    fn expanded_weight_of_an_unshared_term_is_its_node_count() {
        assert_eq!(weight_of(&c("a")).expanded_weight, 1);
        let report = weight_of(&Expr::app(c("f"), c("a")));
        assert_eq!(report.expanded_weight, 3, "f, a, and the application");
        assert_eq!(report.distinct_nodes, 3);
        assert_eq!(report.edges, 2);
        assert_eq!(
            report.sharing_factor(),
            1,
            "an unshared term shares nothing"
        );
    }

    /// **Maximum logical depth**, the fact `franken_lean-j8h` names and that this report
    /// did not carry until now.
    ///
    /// Depth folds with `max` where weight folds with `+`, and the diamond below is what
    /// separates them: a node with two children of depth 2 is depth 3, never depth 5. A
    /// `+` in that fold passes every weight assertion in this file and fails only here.
    #[test]
    fn maximum_logical_depth_is_the_longest_path_not_the_sum() {
        assert_eq!(weight_of(&c("a")).max_logical_depth, 1, "a leaf is depth 1");
        assert_eq!(
            weight_of(&Expr::app(c("f"), c("a"))).max_logical_depth,
            2,
            "an application over two leaves is depth 2"
        );

        // A diamond: one shared child of depth 2, reached by both edges of an app.
        let shared = Expr::app(c("f"), c("a"));
        let diamond = Expr::app(shared.clone(), shared);
        let report = weight_of(&diamond);
        assert_eq!(
            report.max_logical_depth, 3,
            "1 + max(2, 2). Summing the children would say 5 and would be wrong"
        );
        assert_eq!(
            report.expanded_weight, 7,
            "the weight DOES sum, which is why the two folds cannot share an operator"
        );

        // Depth is a property of the denoted tree, so sharing must not move it. The
        // unshared twin denotes the same tree with more stored nodes.
        let twin = Expr::app(Expr::app(c("f"), c("a")), Expr::app(c("f"), c("a")));
        let twin_report = weight_of(&twin);
        assert_eq!(
            twin_report.max_logical_depth, report.max_logical_depth,
            "sharing changes distinct_nodes, never depth"
        );
        assert!(
            twin_report.distinct_nodes > report.distinct_nodes,
            "the fixture must actually differ in sharing or it proves nothing: {twin_report:?} vs \
             {report:?}"
        );
    }

    /// Depth tracks the input rather than being a constant that happens to agree, and it
    /// is measured on a term deep enough that a recursive fold would not survive it.
    #[test]
    fn maximum_logical_depth_grows_with_nesting_and_is_stack_safe() {
        let mut shallow = c("a");
        for _ in 0..4 {
            shallow = Expr::app(shallow, c("a"));
        }
        assert_eq!(
            weight_of(&shallow).max_logical_depth,
            5,
            "four nestings over a leaf"
        );

        let mut deep = c("a");
        for _ in 0..10_000 {
            deep = Expr::app(deep, c("a"));
        }
        let report = weight_of(&deep);
        assert_eq!(
            report.max_logical_depth, 10_001,
            "depth is exact at ten thousand nestings, not saturated or approximated"
        );
        assert!(
            report.max_logical_depth <= report.distinct_nodes,
            "a DAG path cannot revisit a node, so depth can never exceed distinct_nodes"
        );
    }

    /// Sharing is measured, not assumed: the same subterm used twice is stored once
    /// and counted twice.
    #[test]
    fn sharing_is_measured_exactly() {
        let shared = Expr::app(c("f"), c("a"));
        let report = weight_of(&Expr::app(shared.clone(), shared));
        assert_eq!(report.distinct_nodes, 4, "outer app, inner app, f, a");
        assert_eq!(report.expanded_weight, 7, "1 + 3 + 3");
    }

    /// THE ADVERSARIAL CASE. Each level references the level below it twice, so the
    /// stored DAG grows by one node while the tree it denotes doubles. This is the
    /// term a byte or node count waves through and a later traversal dies on — the
    /// same shape as the fln-olean length that escaped its budget in c26b8ed.
    #[test]
    fn a_dag_bomb_is_typed_inconclusive_rather_than_an_abort() {
        let mut bomb = c("leaf");
        for _ in 0..40 {
            bomb = Expr::app(bomb.clone(), bomb);
        }

        // Wire-small by every naive measure, astronomical by the one that counts.
        let report = weight_of(&bomb);
        assert_eq!(report.distinct_nodes, 41, "the stored DAG really is tiny");
        assert!(
            report.expanded_weight > 1_000_000_000_000,
            "the tree it denotes really is astronomical: {}",
            report.expanded_weight
        );
        assert!(report.sharing_factor() > 1_000_000_000);

        // Under a realistic budget it stops, as an FL-INV-07 inconclusive: not a
        // rejection of the term, and never cacheable.
        let outcome = expanded_weight(&bomb, &WeightBudget::new(100_000, u64::MAX));
        match &outcome {
            Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                InconclusiveCause::ResourceExhausted { usage } => {
                    assert_eq!(usage.allowed, 100_000);
                    assert!(
                        usage.is_genuine_exhaustion(),
                        "a stop must report spending past its allowance"
                    );
                    // The unit is the point: DENOTED size, not stored size, and not
                    // a claim that the term is malformed.
                    assert_eq!(
                        usage.reason,
                        ResourceReason::StructuralBudget {
                            unit: StructuralUnit::ExpandedWeight
                        }
                    );
                }
                other => panic!("expected resource exhaustion, got {other:?}"),
            },
            other => panic!("expected inconclusive, got {other:?}"),
        }
        assert!(
            matches!(outcome.cache_admission(), CacheAdmission::Refused { .. }),
            "an exhausted measurement must never be cacheable"
        );
    }

    /// The distinct-node budget bounds the traversal itself, and reports a DIFFERENT
    /// unit — a caller shrinking its input can act on that, and could not if both
    /// stops collapsed into one reason.
    #[test]
    fn the_distinct_node_budget_stops_under_its_own_unit() {
        let mut wide = c("leaf");
        for _ in 0..2_000u32 {
            wide = Expr::app(wide, Expr::const_(n("f"), vec![Level::param(n("u"))]));
        }
        let outcome = expanded_weight(&wide, &WeightBudget::new(u64::MAX, 100));
        match &outcome {
            Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                InconclusiveCause::ResourceExhausted { usage } => assert_eq!(
                    usage.reason,
                    ResourceReason::StructuralBudget {
                        unit: StructuralUnit::ProducedNodes
                    },
                    "a stored-graph stop must not be reported as a denoted-size stop"
                ),
                other => panic!("expected resource exhaustion, got {other:?}"),
            },
            other => panic!("expected inconclusive, got {other:?}"),
        }
        assert!(matches!(
            outcome.cache_admission(),
            CacheAdmission::Refused { .. }
        ));
    }

    /// Totality on the degenerate shape: deep terms are digested on the heap, not the
    /// call stack, so depth is a measurement rather than a crash.
    #[test]
    fn a_deeply_nested_term_is_digested_without_recursion() {
        let mut deep = c("leaf");
        for _ in 0..100_000 {
            deep = Expr::lam(n("x"), ty(), deep, BinderInfo::Default);
        }
        let digest = alpha_canonical_digest(&deep);
        // Renaming every binder in a 100k-deep term still cannot move it.
        let mut renamed = c("leaf");
        for _ in 0..100_000 {
            renamed = Expr::lam(n("y"), ty(), renamed, BinderInfo::Default);
        }
        assert_eq!(digest, alpha_canonical_digest(&renamed));
    }
}
