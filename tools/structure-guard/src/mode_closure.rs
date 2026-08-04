//! FLN-D18 mode-closure registration (bead `franken_lean-r2st`).
//!
//! This module DERIVES a product closure from governed structure and hands it to
//! [`fln_core::mode::scan_mode_closure`], which is the sole authority on D18. It
//! deliberately does not reimplement the traversal or the mode algebra, and it never
//! softens a refusal: every `FLN-D18-001..013` code and its witness are translated
//! verbatim into a [`Finding`].
//!
//! # The rule that decides the extractor
//!
//! [`ModeClosureNode`] carries `requirement` and `observed_provenance` as separate
//! fields *so the scanner can compare them*. `requirement` is the AUTHORITATIVE
//! classification this module derives from structure — manifests, declared features,
//! the reviewed workspace graph. `observed_provenance` is the UNTRUSTED marker an
//! artifact carries. Deriving `requirement` by reading a marker would make the check
//! compare a value with itself, which is a pass with no content.
//!
//! # Node identity
//!
//! Ids are the index of the crate in the sorted crate list, so the projection from
//! crate name to [`ModeClosureNodeId`] is injective by construction. Hashing a name
//! into the id space would be a projection keyed as an identity without an
//! injectivity check — a defect this repository has already produced three times.
//!
//! # Scope, stated because a silent scope is the defect one floor up
//!
//! The frontier inventory is derived from real declared Cargo features. The product
//! inventory is derived from crates that declare a mode-bound product root. This
//! module does NOT fabricate a closure when no product declares one: an empty product
//! inventory yields no scan and no finding, and [`ModeClosureFacts`] reports both
//! counts so the vacuity is visible rather than presented as an enforced pass.
//!
//! Today that product inventory is EMPTY — no crate declares a mode-bound product root —
//! so the live scan traverses nothing and every real run renders `scan_class":"vacuous"`.
//! That gap is owned rather than merely disclosed: the product half (the canonical
//! sidecar, two certified builds compared for byte-identity, the no-mock E2E that BUILDS
//! products, 1/8/32) is bead `fln-d18-product-half-rgsg`, which is OPEN. `franken_lean-r2st`
//! closed on its registration half only, so a reader following that citation must not read
//! it as the product half having been done. The two are bound by
//! `the_deferred_d18_product_half_stays_owned_while_the_scan_is_vacuous`, which refuses to
//! let the remainder be closed while this module still reports a vacuous scan.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use fln_core::mode::{
    FrontierFeature, FrontierSurface, Mode, ModeClosureEdge, ModeClosureEdgeKind, ModeClosureNode,
    ModeClosureNodeId, ModeClosureRefusal, ModeClosureRequest, ObservedModeProvenance,
    StructuralModeRequirement, scan_mode_closure,
};

use crate::checks::Finding;
use crate::graph::GraphFile;

/// What the derivation actually saw. Reported so that "D18 registered" can never be
/// read as "a frontier node was traversed".
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModeClosureFacts {
    /// Nodes whose SUBMITTED requirement is `FrontierOnly`, derived from real Cargo
    /// features. Counted after the product-root override rather than before it: a crate
    /// that declares both a frontier feature and a mode-bound product root is submitted
    /// as `ModeBound`, so counting it as a frontier surface would publish a number that
    /// does not describe the request the core actually received.
    pub frontier_surfaces: usize,
    /// Product roots that declare a mode binding. Zero means nothing was scanned.
    pub product_roots: usize,
    /// Consumer modes for which a closure was actually submitted to the scanner.
    pub closures_scanned: usize,
    /// Nodes actually submitted, summed across closures — the reachable subset, which
    /// is what the core validates. Distinct from `nodes`, which counts the whole
    /// workspace: a run where these are equal has either one all-reaching product or a
    /// derivation that has stopped selecting.
    pub closure_nodes: usize,
    pub nodes: usize,
    pub edges: usize,
}

impl ModeClosureFacts {
    /// True when no product closure existed to scan. A caller reporting D18 state must
    /// distinguish this from a scan that traversed a closure and found it clean.
    pub const fn is_vacuous(&self) -> bool {
        self.closures_scanned == 0
    }

    /// The scope word carried into the robot artifact beside the counts (bead
    /// `fln-q8qt`).
    ///
    /// It is derived from [`Self::is_vacuous`] rather than stored, so the word and the
    /// counts cannot disagree at the source. A consumer re-checks the same law against
    /// the emitted numbers, which is what makes a hand-edited artifact fail rather than
    /// read as an enforced pass.
    pub const fn scan_class(&self) -> &'static str {
        if self.is_vacuous() {
            "vacuous"
        } else {
            "traversed"
        }
    }
}

/// Registered feature names for each frontier surface.
///
/// The match is exhaustive on purpose: adding a [`FrontierFeature`] variant fails to
/// compile until its surface is registered here, so this cannot become a hand-list
/// that silently stops covering the frontier.
const fn frontier_feature_names(feature: FrontierFeature) -> &'static [&'static str] {
    match feature {
        FrontierFeature::OleanNext => &["olean-next"],
        FrontierFeature::EGraphPortfolio => &["e-graph-portfolio", "egraph-portfolio"],
        FrontierFeature::IronJit => &["iron", "iron-jit"],
        FrontierFeature::McpWriteTools => &["mcp-write-tools"],
        FrontierFeature::EpochBridge => &["epoch-bridge"],
    }
}

const FRONTIER_FEATURES: [FrontierFeature; 5] = [
    FrontierFeature::OleanNext,
    FrontierFeature::EGraphPortfolio,
    FrontierFeature::IronJit,
    FrontierFeature::McpWriteTools,
    FrontierFeature::EpochBridge,
];

/// Modes a product closure is derived for. Every mode is scanned; a mode is never
/// skipped because it "has no frontier code", which would be the runtime-branch
/// isolation the bead forbids.
const CONSUMER_MODES: [Mode; 3] = [Mode::Faithful, Mode::Sound, Mode::Frontier];

/// Declared feature names of one crate, read from its manifest.
fn declared_features(manifest: &str) -> Vec<String> {
    let mut features = Vec::new();
    let mut in_features = false;
    for line in manifest.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_features = trimmed == "[features]";
            continue;
        }
        if !in_features || trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if let Some((key, _)) = trimmed.split_once('=') {
            let key = key.trim().trim_matches('"');
            if !key.is_empty() {
                features.push(key.to_string());
            }
        }
    }
    features
}

/// Structural classification of one crate, derived from its manifest — never from a
/// mode marker.
fn derive_requirement(features: &[String]) -> StructuralModeRequirement {
    for feature in FRONTIER_FEATURES {
        for name in frontier_feature_names(feature) {
            if features.iter().any(|declared| declared == name) {
                return StructuralModeRequirement::FrontierOnly(FrontierSurface::Feature(feature));
            }
        }
    }
    StructuralModeRequirement::Neutral
}

/// Mode marker observed on the crate's artifact. This is the UNTRUSTED half: it is read
/// from a declared marker and is never inferred from the structural classification
/// above. Absence stays [`ObservedModeProvenance::Missing`] and is never upgraded to
/// `Neutral`, which is what makes stripped provenance a refusal rather than a default.
fn observed_provenance(manifest: &str) -> ObservedModeProvenance {
    let marker = manifest
        .lines()
        .find_map(|line| line.trim().strip_prefix("# fln-mode-provenance:"))
        .map(str::trim);
    match marker {
        None => ObservedModeProvenance::Missing,
        Some("neutral") => ObservedModeProvenance::Neutral,
        Some("faithful") => ObservedModeProvenance::ModeBound {
            tag: Mode::Faithful.tag(),
        },
        Some("sound") => ObservedModeProvenance::ModeBound {
            tag: Mode::Sound.tag(),
        },
        Some("frontier") => ObservedModeProvenance::ModeBound {
            tag: Mode::Frontier.tag(),
        },
        // An unrecognised marker keeps its raw tag so the core, not this extractor,
        // decides that it is unknown (FLN-D18-003).
        Some(other) => ObservedModeProvenance::ModeBound {
            tag: other.parse::<u8>().unwrap_or(u8::MAX),
        },
    }
}

/// Declared product root binding, if the crate declares one.
fn declared_product_root(manifest: &str) -> Option<Mode> {
    let declared = manifest
        .lines()
        .find_map(|line| line.trim().strip_prefix("# fln-product-root:"))
        .map(str::trim)?;
    match declared {
        "faithful" => Some(Mode::Faithful),
        "sound" => Some(Mode::Sound),
        "frontier" => Some(Mode::Frontier),
        _ => None,
    }
}

fn render_refusal(refusal: &ModeClosureRefusal, names: &BTreeMap<u128, String>) -> String {
    let name = |id: ModeClosureNodeId| -> String {
        names
            .get(&id.get())
            .cloned()
            .unwrap_or_else(|| format!("node#{}", id.get()))
    };
    match refusal {
        ModeClosureRefusal::FrontierLeak {
            consumer,
            node,
            surface,
            witness,
        } => format!(
            "frontier surface reaches a {consumer:?} product closure: node={} surface={surface:?} \
             witness_len={}",
            name(*node),
            witness.nodes().len()
        ),
        ModeClosureRefusal::MissingModeProvenance { node, .. } => format!(
            "node={} carries no mode provenance; absence is explicit and is never a default",
            name(*node)
        ),
        ModeClosureRefusal::UnknownModeProvenance { node, tag, .. } => {
            format!("node={} carries unknown mode tag {tag}", name(*node))
        }
        ModeClosureRefusal::ModeProvenanceMismatch {
            node,
            expected,
            observed,
            ..
        } => format!(
            "node={} observed provenance {observed:?} contradicts derived requirement {expected:?}",
            name(*node)
        ),
        ModeClosureRefusal::MixedMode {
            producer,
            consumer,
            node,
            ..
        } => format!(
            "node={} was produced in {producer:?} and consumed in {consumer:?}",
            name(*node)
        ),
        ModeClosureRefusal::DuplicateNode { node } => {
            format!("node={} appears twice in the derived closure", name(*node))
        }
        ModeClosureRefusal::DuplicateRoot { root } => {
            format!("product root={} appears twice", name(*root))
        }
        ModeClosureRefusal::MissingRoot { root } => {
            format!("product root={} is absent from the closure", name(*root))
        }
        ModeClosureRefusal::MissingEdgeEndpoint { edge, endpoint } => format!(
            "edge {:?} -> {:?} names endpoint {} that the closure omits",
            edge.from.get(),
            edge.to.get(),
            name(*endpoint)
        ),
        ModeClosureRefusal::DuplicateEdge { edge } => format!(
            "edge {} -> {} ({:?}) appears twice",
            name(edge.from),
            name(edge.to),
            edge.kind
        ),
        ModeClosureRefusal::EmptyRoots => {
            "the derived closure declares no product root".to_string()
        }
        ModeClosureRefusal::UnreachableNode { node } => format!(
            "node={} is in the closure but unreachable from any product root; a reachable \
             node omitted from the supplied closure is a refusal, not a partial pass",
            name(*node)
        ),
        ModeClosureRefusal::InvalidProductRoot {
            root,
            consumer,
            requirement,
        } => format!(
            "product root={} is {requirement:?}, which cannot root a {consumer:?} closure",
            name(*root)
        ),
    }
}

/// Derive the product closure from governed structure and submit it to the core D18
/// scanner. Returns the translated findings and the scope the derivation achieved.
///
/// `manifests` is the manifest text already read by `checks::run`, keyed by crate name.
/// This module performs no filesystem access of its own: a second read pass would add
/// work between the two governed-root snapshots and destabilise the concurrency
/// authority tests, which race a writer against the scan window.
pub fn audit_with_facts(
    graph: &GraphFile,
    manifests: &BTreeMap<String, String>,
) -> (Vec<Finding>, ModeClosureFacts) {
    let mut findings = Vec::new();
    let mut facts = ModeClosureFacts::default();

    // Sorted crate list: the index IS the node id, so the mapping is injective.
    let crate_names: Vec<&String> = graph.crates.keys().collect();

    let mut nodes: Vec<ModeClosureNode> = Vec::new();
    let mut names: BTreeMap<u128, String> = BTreeMap::new();
    let mut index_of: BTreeMap<&str, u128> = BTreeMap::new();
    let mut roots_by_mode: BTreeMap<u8, Vec<ModeClosureNodeId>> = BTreeMap::new();

    for (index, name) in crate_names.iter().enumerate() {
        let index = index as u128;
        let id = ModeClosureNodeId::new(index);
        names.insert(index, (*name).clone());
        index_of.insert(name.as_str(), index);

        let manifest = manifests.get(*name).map_or("", String::as_str);
        let features = declared_features(manifest);

        let mut requirement = derive_requirement(&features);
        if let Some(mode) = declared_product_root(manifest) {
            facts.product_roots += 1;
            requirement = StructuralModeRequirement::ModeBound(mode);
            roots_by_mode.entry(mode.tag()).or_default().push(id);
        }
        // Counted from the FINAL requirement, after the override above. Counting the
        // pre-override classification published a frontier surface for a node that was
        // submitted as `ModeBound`, i.e. a disclosed number describing a request the
        // core never received.
        if matches!(requirement, StructuralModeRequirement::FrontierOnly(_)) {
            facts.frontier_surfaces += 1;
        }

        nodes.push(ModeClosureNode {
            id,
            requirement,
            observed_provenance: observed_provenance(manifest),
        });
    }

    let edges: Vec<ModeClosureEdge> = graph
        .edges
        .iter()
        .filter_map(|(from, to)| {
            Some(ModeClosureEdge {
                from: ModeClosureNodeId::new(*index_of.get(from.as_str())?),
                to: ModeClosureNodeId::new(*index_of.get(to.as_str())?),
                kind: ModeClosureEdgeKind::Dependency,
            })
        })
        .collect();
    facts.nodes = nodes.len();
    facts.edges = edges.len();

    // No product declares a mode-bound root: there is no closure to scan. Do not
    // fabricate one, and do not report a clean pass — `facts.is_vacuous()` carries it.
    for mode in CONSUMER_MODES {
        let Some(roots) = roots_by_mode.get(&mode.tag()) else {
            continue;
        };
        // Only the nodes this product actually reaches belong to its closure. Submitting
        // the whole workspace instead refuses every unrelated crate with FLN-D18-012 —
        // which stayed invisible while no crate declared a product root, because a
        // vacuous scan never exercises the request it would have built (bead
        // franken_lean-r2st). Edges are filtered with the nodes: an edge leaving the
        // closure would name an endpoint the closure omits.
        facts.closures_scanned += 1;
        let reachable = reachable_from(roots, &edges);
        let closure_nodes: Vec<ModeClosureNode> = nodes
            .iter()
            .filter(|node| reachable.contains(&node.id))
            .copied()
            .collect();
        let closure_edges: Vec<ModeClosureEdge> = edges
            .iter()
            .filter(|edge| reachable.contains(&edge.from))
            .copied()
            .collect();
        facts.closure_nodes += closure_nodes.len();
        let request = ModeClosureRequest {
            consumer: mode,
            roots,
            nodes: &closure_nodes,
            edges: &closure_edges,
        };
        if let Err(refusal) = scan_mode_closure(request) {
            findings.push(Finding {
                // The core's stable code, unchanged. The gate translates, never renames.
                code: refusal.finding_code(),
                path: crate::GRAPH_FILE.to_string(),
                detail: format!(
                    "D18 {:?} closure refused: {}",
                    mode,
                    render_refusal(&refusal, &names)
                ),
            });
        }
    }

    (findings, facts)
}

/// The nodes one product root set actually reaches, over the supplied edges.
///
/// The core requires `ModeClosureRequest::nodes` to be **exactly** the reachable closure
/// of `roots`: `ValidatedModeClosure` is documented as proof that every supplied node is
/// reachable, and `scan_mode_closure` refuses any node it cannot reach with
/// `FLN-D18-012`. Selecting that subset is the caller's obligation under that contract,
/// not a second copy of the scanner: no mode algebra happens here, and every admission
/// decision still belongs to `fln_core::mode`.
fn reachable_from(
    roots: &[ModeClosureNodeId],
    edges: &[ModeClosureEdge],
) -> BTreeSet<ModeClosureNodeId> {
    let mut outgoing: BTreeMap<ModeClosureNodeId, Vec<ModeClosureNodeId>> = BTreeMap::new();
    for edge in edges {
        outgoing.entry(edge.from).or_default().push(edge.to);
    }
    let mut seen: BTreeSet<ModeClosureNodeId> = roots.iter().copied().collect();
    let mut queue: VecDeque<ModeClosureNodeId> = roots.iter().copied().collect();
    while let Some(node) = queue.pop_front() {
        for child in outgoing.get(&node).into_iter().flatten() {
            if seen.insert(*child) {
                queue.push_back(*child);
            }
        }
    }
    seen
}

/// Registration entry point, matching the other audit modules.
pub fn audit(graph: &GraphFile, manifests: &BTreeMap<String, String>) -> Vec<Finding> {
    audit_with_facts(graph, manifests).0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_frontier_feature_has_a_registered_surface_name() {
        for feature in FRONTIER_FEATURES {
            assert!(
                !frontier_feature_names(feature).is_empty(),
                "{feature:?} has no registered feature name, so a crate declaring it \
                 would be classified Neutral and its frontier surface would be invisible"
            );
        }
    }

    #[test]
    fn requirement_is_derived_from_features_not_from_a_marker() {
        // A crate whose manifest claims to be neutral but declares a frontier feature
        // must still classify as frontier: the marker is untrusted, the feature is not.
        let manifest = "# fln-mode-provenance: neutral\n[features]\niron = []\n";
        let features = declared_features(manifest);
        assert_eq!(
            derive_requirement(&features),
            StructuralModeRequirement::FrontierOnly(FrontierSurface::Feature(
                FrontierFeature::IronJit
            )),
            "the derived requirement must come from the declared feature, never from the \
             mode marker; otherwise the scanner compares a value with itself"
        );
        assert_eq!(
            observed_provenance(manifest),
            ObservedModeProvenance::Neutral
        );
    }

    const GRAPH: &str = "schema fln-workspace-graph/1\n\
                         crate app rank=2 kind=ordinary\n\
                         crate lib rank=1 kind=ordinary\n\
                         edge app -> lib\n";

    fn manifests(app: &str, lib: &str) -> BTreeMap<String, String> {
        BTreeMap::from([
            ("app".to_string(), app.to_string()),
            ("lib".to_string(), lib.to_string()),
        ])
    }

    fn codes(graph_text: &str, manifests: &BTreeMap<String, String>) -> Vec<&'static str> {
        let graph = crate::graph::parse(graph_text).expect("fixture graph parses");
        let (findings, _) = audit_with_facts(&graph, manifests);
        findings.into_iter().map(|finding| finding.code).collect()
    }

    /// Negative control. Without this the planted cases below could be passing for a
    /// reason unrelated to what they plant.
    #[test]
    fn a_clean_sound_product_closure_is_admitted() {
        let m = manifests(
            "# fln-product-root: sound\n# fln-mode-provenance: sound\n",
            "# fln-mode-provenance: neutral\n",
        );
        assert!(
            codes(GRAPH, &m).is_empty(),
            "clean closure must be admitted"
        );
        let graph = crate::graph::parse(GRAPH).expect("fixture graph parses");
        let (_, facts) = audit_with_facts(&graph, &m);
        assert_eq!(facts.product_roots, 1);
        assert_eq!(facts.closures_scanned, 1);
        assert!(!facts.is_vacuous(), "a scanned closure is not vacuous");
    }

    /// Regression guard for the defect this module shipped with (bead
    /// `franken_lean-r2st`): the derivation submitted the **whole workspace** as the
    /// closure while its own comment said it submitted only what the product reaches.
    /// The core refuses any node it cannot reach, so the first crate to declare a real
    /// product root would have been met with `FLN-D18-012` naming an unrelated crate.
    ///
    /// It stayed invisible because no crate declares a product root, so the live scan is
    /// vacuous and never builds the request it would have built. A vacuous check cannot
    /// be trusted to be a correct one — that is the whole reason this test exists rather
    /// than a note saying the derivation looks right.
    #[test]
    fn only_the_reachable_subset_is_submitted_not_the_whole_workspace() {
        const GRAPH3: &str = "schema fln-workspace-graph/1\n\
                              crate app rank=2 kind=ordinary\n\
                              crate lib rank=1 kind=ordinary\n\
                              crate unrelated rank=1 kind=ordinary\n\
                              edge app -> lib\n";
        let m = BTreeMap::from([
            (
                "app".to_string(),
                "# fln-product-root: sound\n# fln-mode-provenance: sound\n".to_string(),
            ),
            (
                "lib".to_string(),
                "# fln-mode-provenance: neutral\n".to_string(),
            ),
            (
                "unrelated".to_string(),
                "# fln-mode-provenance: neutral\n".to_string(),
            ),
        ]);
        let graph = crate::graph::parse(GRAPH3).expect("fixture graph parses");
        let (findings, facts) = audit_with_facts(&graph, &m);
        assert!(
            findings.is_empty(),
            "a crate the product does not reach must not refuse its closure: {findings:?}"
        );
        assert_eq!(facts.nodes, 3, "the workspace has three crates");
        assert_eq!(
            facts.closure_nodes, 2,
            "the Sound closure is app+lib; submitting `unrelated` as well is what \
             produced FLN-D18-012 on every unrelated crate"
        );
    }

    #[test]
    fn planted_frontier_contamination_of_a_sound_root_is_refused() {
        // `lib` declares a real frontier feature, carries provenance consistent with
        // that classification, and is reachable from a Sound product.
        let m = manifests(
            "# fln-product-root: sound\n# fln-mode-provenance: sound\n",
            "# fln-mode-provenance: frontier\n[features]\niron = []\n",
        );
        assert_eq!(
            codes(GRAPH, &m),
            vec!["FLN-D18-001"],
            "a frontier surface reachable from a Sound root must be refused, and the \
             core's stable code must survive translation unchanged"
        );
    }

    /// The same contamination with an INCONSISTENT marker is a different refusal, and
    /// the ordering belongs to the core rather than to this extractor: a frontier-only
    /// node claiming neutral provenance is a mismatch (004) before it can be reported
    /// as a leak (001). Pinned so that translating a refusal never silently reclassifies
    /// which one the core chose.
    #[test]
    fn frontier_node_claiming_neutral_provenance_is_a_mismatch_not_a_leak() {
        let m = manifests(
            "# fln-product-root: sound\n# fln-mode-provenance: sound\n",
            "# fln-mode-provenance: neutral\n[features]\niron = []\n",
        );
        assert_eq!(codes(GRAPH, &m), vec!["FLN-D18-004"]);
    }

    #[test]
    fn planted_stripped_provenance_refuses_rather_than_defaulting() {
        let m = manifests(
            "# fln-product-root: sound\n# fln-mode-provenance: sound\n",
            "[package]\nname = \"lib\"\n",
        );
        assert_eq!(
            codes(GRAPH, &m),
            vec!["FLN-D18-002"],
            "absent provenance must refuse; silently reading it as Neutral is the \
             default-on-absence defect the core exists to prevent"
        );
    }

    /// **This test's assertion was inverted deliberately** (bead `franken_lean-r2st`);
    /// recorded rather than quietly rewritten, because changing a test to match new
    /// behaviour is how a regression gets blessed.
    ///
    /// It previously asserted that a crate the product root cannot reach refuses the
    /// closure with `FLN-D18-012`. That was not a D18 property — it was the derivation
    /// submitting the **whole workspace** as the closure instead of the reachable subset
    /// its own comment described. Under it, the first crate to declare a real product
    /// root would have been refused on account of the 32 unrelated crates beside it, so
    /// the rule as written said no workspace may contain a crate outside the product.
    ///
    /// The omission check is not weakened, it moved to where it can still act: the core
    /// refuses any supplied node it cannot reach, and this derivation can no longer
    /// supply one. That is the point of deriving a closure rather than declaring it, and
    /// it is why `only_the_reachable_subset_is_submitted_not_the_whole_workspace` above
    /// pins the subset by count.
    #[test]
    fn a_crate_the_product_does_not_reach_is_outside_its_closure_not_a_refusal() {
        // `lib` is in the workspace and no edge reaches it from the product root.
        let disconnected = "schema fln-workspace-graph/1\n\
                            crate app rank=2 kind=ordinary\n\
                            crate lib rank=1 kind=ordinary\n";
        let m = manifests(
            "# fln-product-root: sound\n# fln-mode-provenance: sound\n",
            "# fln-mode-provenance: neutral\n",
        );
        assert!(
            codes(disconnected, &m).is_empty(),
            "a crate outside the product's reach is not part of that product, and a \
             workspace does not become inadmissible by containing one"
        );
        let graph = crate::graph::parse(disconnected).expect("fixture graph parses");
        let (_, facts) = audit_with_facts(&graph, &m);
        assert_eq!(
            facts.closure_nodes, 1,
            "only the root itself is reachable, so only it is submitted"
        );
    }

    /// The disclosed frontier count must describe the request the core received, not an
    /// intermediate classification the derivation then discarded. A crate declaring both
    /// a frontier feature and a mode-bound product root is submitted as `ModeBound`.
    #[test]
    fn a_frontier_feature_on_a_product_root_is_not_counted_as_a_frontier_surface() {
        let m = manifests(
            "# fln-product-root: frontier\n# fln-mode-provenance: frontier\n[features]\niron = []\n",
            "# fln-mode-provenance: neutral\n",
        );
        let graph = crate::graph::parse(GRAPH).expect("fixture graph parses");
        let (_, facts) = audit_with_facts(&graph, &m);
        assert_eq!(facts.product_roots, 1);
        assert_eq!(
            facts.frontier_surfaces, 0,
            "the root was submitted as ModeBound, so publishing it as a frontier surface \
             would disclose a count for a request the core never received"
        );
    }

    /// The scope word and the counts are one fact, not two. A consumer re-checks this
    /// law against the emitted numbers, so it must hold at the source in both directions.
    #[test]
    fn the_scan_class_agrees_with_the_closure_count_in_both_directions() {
        let vacuous = ModeClosureFacts {
            nodes: 33,
            edges: 28,
            ..ModeClosureFacts::default()
        };
        assert!(vacuous.is_vacuous());
        assert_eq!(vacuous.scan_class(), "vacuous");
        let traversed = ModeClosureFacts {
            closures_scanned: 1,
            closure_nodes: 2,
            ..vacuous.clone()
        };
        assert!(!traversed.is_vacuous());
        assert_eq!(traversed.scan_class(), "traversed");
    }

    #[test]
    fn absent_provenance_stays_missing_and_is_never_upgraded() {
        assert_eq!(
            observed_provenance("[package]\nname = \"x\"\n"),
            ObservedModeProvenance::Missing,
            "stripped provenance must stay explicit so the core can refuse it"
        );
    }
}
