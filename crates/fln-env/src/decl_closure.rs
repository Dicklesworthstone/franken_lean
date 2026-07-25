//! Declaration-level artifact-closure governance (bead
//! franken_lean-artifact-incomplete-private-refs-sgt): a serialized module can
//! reference constants its own artifact does not carry — the pin's serializer
//! drops private elaboration auxiliaries (`.match_1`, `._proof_N`) that non-safe
//! implementation helpers (`._unsafe_rec`, `._override`) still name. Such a
//! declaration's dependency closure is unprovable *from the artifact alone*: the
//! kernel would reject it (`UnknownConstant`) even though the Reference accepted
//! it at original elaboration time and never re-checks imports
//! (`lean_add_decl_without_checking`, environment.cpp:284). Neither `Accepted`
//! nor `Rejected` is honest, so admission classifies the declaration
//! **ArtifactIncomplete** — an FL-INV-07 inconclusive-family outcome that can
//! never be cached, never enter an environment, and never satisfy a G1
//! acceptance count.
//!
//! This module owns the typed vocabulary and the census partition:
//! * [`MissingConstantFinding`] — one affected declaration with its canonically
//!   ordered missing references (the declaration-level analogue of
//!   `effective_imports::MissingModuleFinding`);
//! * [`DeclClosureStatus`] — `Complete` | `ArtifactIncomplete` | `Inconclusive`
//!   | `InternalFault`, mirroring [`crate::effective_imports::ClosureStatus`];
//! * [`classify_closures`] — the order-independent, resource-bounded,
//!   cancellation-aware partition of a module's declarations into
//!   kernel-checkable candidates and artifact-incomplete findings, with a
//!   canonical witness digest over the findings.
//!
//! No hidden allowlist and no name-only exception: the partition is a function
//! of each declaration's declared dependencies and the resolver — never of a
//! declaration's spelling.

use std::collections::{BTreeMap, BTreeSet};

use fln_core::name::Name;
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, DomainHasher};

use crate::constants::DefinitionSafety;

/// Domain-separation tag for the artifact-incomplete witness digest (the same
/// `Domain::Fixture` + tag + NUL + length-prefixed-rows discipline as the
/// kernel-contract ownership projection).
///
/// **Version 2** replaced version 1's display projection of [`Name`] with the
/// canonical structural encoding. Version 1 hashed `to_display_string()`, which
/// joins components with `.` without escaping and renders numeric and string
/// components identically — so distinct names collided and the witness stopped
/// discriminating the finding set it exists to bind. The tag moves with the
/// encoding on purpose: a consumer that recomputes a witness must be able to tell
/// "different data" from "different rule", and an encoding that changed silently
/// under an unchanged version is indistinguishable from corruption.
const WITNESS_TAG: &[u8] = b"fln.artifact-incomplete-witness/2";

/// One declaration whose artifact cannot supply its dependency closure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingConstantFinding {
    /// The affected declaration.
    pub declaration: Name,
    /// Its safety class as decoded from the artifact (the six known rows are
    /// `Unsafe`/`Partial`; a `Safe` finding would be new evidence, not an error).
    pub safety: DefinitionSafety,
    /// The referenced constants absent from the artifact and the ambient
    /// environment — deduplicated, canonically ordered.
    pub missing: Vec<Name>,
}

/// Resource classes the census can exhaust (FL-INV-07: exhaustion is a value).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclClosureResource {
    /// Total dependency edges examined across the module.
    DependencyEdges,
    /// Artifact-incomplete findings recorded.
    Findings,
}

impl DeclClosureResource {
    pub fn label(self) -> &'static str {
        match self {
            DeclClosureResource::DependencyEdges => "dependency-edges",
            DeclClosureResource::Findings => "findings",
        }
    }
}

/// Why the census could not finish. Never rendered as, cached as, or promoted
/// to completeness *or* incompleteness (FL-INV-07).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclClosureInconclusive {
    /// Cancellation observed before the census finished.
    Cancelled { at_declaration: usize },
    /// A typed resource budget was exhausted.
    ResourceLimitExceeded {
        resource: DeclClosureResource,
        limit: usize,
        actual: usize,
        declaration: Option<Name>,
    },
}

/// Faults in the census *input* — evidence of an upstream invariant violation,
/// never a verdict about the artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclClosureFault {
    /// The same declaration name appeared twice in the census input: the
    /// one-name law was violated before the census ran.
    DuplicateDeclaration { declaration: Name },
}

/// The typed outcome of the declaration-closure census.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclClosureStatus {
    /// Every examined declaration's dependencies resolve: all are candidates
    /// for the ordinary kernel authority.
    Complete,
    /// At least one declaration's closure cannot be supplied by the artifact.
    /// The findings are canonically ordered and bound by a witness digest.
    /// This is an inconclusive-family outcome: not accepted, not rejected,
    /// not checked, not cacheable, and barred from the environment.
    ArtifactIncomplete {
        findings: Vec<MissingConstantFinding>,
        witness: Digest,
    },
    /// The census itself did not finish (cancellation / exhaustion).
    Inconclusive { reason: DeclClosureInconclusive },
    /// The census input violated an upstream invariant.
    InternalFault { fault: DeclClosureFault },
}

impl DeclClosureStatus {
    /// Stable evidence label for census rows and NDJSON artifacts.
    pub fn outcome_label(&self) -> &'static str {
        match self {
            DeclClosureStatus::Complete => "complete",
            DeclClosureStatus::ArtifactIncomplete { .. } => "inconclusive-artifact-incomplete",
            DeclClosureStatus::Inconclusive { .. } => "inconclusive",
            DeclClosureStatus::InternalFault { .. } => "internal-fault",
        }
    }

    /// Only a `Complete` census may feed the cache: incompleteness carries a
    /// witness, and inconclusive/fault outcomes are never publication-grade.
    pub fn is_cacheable(&self) -> bool {
        matches!(self, DeclClosureStatus::Complete)
    }

    /// An artifact-incomplete, inconclusive, or faulted declaration set can
    /// never enter an environment (the bead's core prohibition: today the six
    /// are silently `add_decl`ed; under this contract they are barred).
    pub fn may_enter_environment(&self) -> bool {
        matches!(self, DeclClosureStatus::Complete)
    }
}

/// Resource budgets for one census run. Budgets are explicit values so the
/// zero / one-under / exact / one-over boundary rows are testable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclClosureBudget {
    pub max_dependency_edges: usize,
    pub max_findings: usize,
}

impl DeclClosureBudget {
    /// Generous defaults for real modules (Prelude examines ~10^5 edges).
    pub const DEFAULT: DeclClosureBudget = DeclClosureBudget {
        max_dependency_edges: 16_777_216,
        max_findings: 65_536,
    };
}

/// One declaration presented to the census: its name, safety class, and the
/// full set of constants it references (type + value + structural edges), as
/// extracted by the caller from the decoded artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclClosureInput {
    pub name: Name,
    pub safety: DefinitionSafety,
    pub dependencies: Vec<Name>,
}

/// The canonical witness digest over a canonically ordered finding set:
/// `DomainHasher(Fixture)` over the tag, a NUL, then per finding the
/// length-prefixed declaration name, a one-byte safety class, and the
/// length-prefixed missing references (count-prefixed). The witness binds
/// EVERY fact a finding row asserts — declaration, safety class, and the
/// exact missing set — so no single-field tamper survives it. Deterministic
/// for a given finding set; input-order independence is the census's job.
/// Canonical, injective bytes for one [`Name`].
///
/// [`Name::write_body`] is the same structural encoding that
/// `Environment::decl_content_digest` and the provenance manifest already commit
/// to: it tags each component's kind and length, so an anonymous, string, or
/// numeric component can never imitate another, and a component containing the
/// display separator cannot forge a deeper path. Reusing it — rather than writing a
/// second name encoding here — is deliberate: a private encoding is exactly how the
/// two would drift apart again.
fn canonical_name_bytes(name: &Name) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    name.write_body(&mut writer);
    writer.into_bytes()
}

pub fn witness_digest(findings: &[MissingConstantFinding]) -> Digest {
    let mut hasher = DomainHasher::new(Domain::Fixture);
    hasher.update(WITNESS_TAG);
    hasher.update(&[0]);
    hasher.update(&(findings.len() as u64).to_le_bytes());
    for finding in findings {
        let declaration = canonical_name_bytes(&finding.declaration);
        hasher.update(&(declaration.len() as u64).to_le_bytes());
        hasher.update(&declaration);
        hasher.update(&[match finding.safety {
            DefinitionSafety::Safe => 0,
            DefinitionSafety::Unsafe => 1,
            DefinitionSafety::Partial => 2,
        }]);
        hasher.update(&(finding.missing.len() as u64).to_le_bytes());
        for name in &finding.missing {
            let encoded = canonical_name_bytes(name);
            hasher.update(&(encoded.len() as u64).to_le_bytes());
            hasher.update(&encoded);
        }
    }
    hasher.finalize()
}

/// Partition a module's declarations by artifact-closure completeness.
///
/// * `resolves(name)` answers whether a referenced constant is available —
///   present in the artifact's own constant index or in the ambient
///   environment. The census never invents availability.
/// * Findings and their missing lists are deduplicated and canonically
///   ordered; the status is a function of the input *set* (any permutation of
///   `inputs` or of a declaration's `dependencies` yields an identical status,
///   including the witness digest).
/// * `cancelled()` is polled per declaration; cancellation and budget
///   exhaustion yield typed `Inconclusive`, never a partial verdict.
pub fn classify_closures<R, C>(
    inputs: &[DeclClosureInput],
    resolves: R,
    budget: DeclClosureBudget,
    cancelled: C,
) -> DeclClosureStatus
where
    R: Fn(&Name) -> bool,
    C: Fn() -> bool,
{
    let mut seen: BTreeSet<Name> = BTreeSet::new();
    let mut findings: BTreeMap<Name, MissingConstantFinding> = BTreeMap::new();
    let mut edges_examined: usize = 0;

    for (index, input) in inputs.iter().enumerate() {
        if cancelled() {
            return DeclClosureStatus::Inconclusive {
                reason: DeclClosureInconclusive::Cancelled {
                    at_declaration: index,
                },
            };
        }
        if !seen.insert(input.name.clone()) {
            return DeclClosureStatus::InternalFault {
                fault: DeclClosureFault::DuplicateDeclaration {
                    declaration: input.name.clone(),
                },
            };
        }
        let mut missing: BTreeSet<Name> = BTreeSet::new();
        for dependency in &input.dependencies {
            edges_examined += 1;
            if edges_examined > budget.max_dependency_edges {
                return DeclClosureStatus::Inconclusive {
                    reason: DeclClosureInconclusive::ResourceLimitExceeded {
                        resource: DeclClosureResource::DependencyEdges,
                        limit: budget.max_dependency_edges,
                        actual: edges_examined,
                        declaration: Some(input.name.clone()),
                    },
                };
            }
            if !resolves(dependency) {
                missing.insert(dependency.clone());
            }
        }
        if !missing.is_empty() {
            if findings.len() + 1 > budget.max_findings {
                return DeclClosureStatus::Inconclusive {
                    reason: DeclClosureInconclusive::ResourceLimitExceeded {
                        resource: DeclClosureResource::Findings,
                        limit: budget.max_findings,
                        actual: findings.len() + 1,
                        declaration: Some(input.name.clone()),
                    },
                };
            }
            findings.insert(
                input.name.clone(),
                MissingConstantFinding {
                    declaration: input.name.clone(),
                    safety: input.safety,
                    missing: missing.into_iter().collect(),
                },
            );
        }
    }

    if findings.is_empty() {
        return DeclClosureStatus::Complete;
    }
    let findings: Vec<MissingConstantFinding> = findings.into_values().collect();
    let witness = witness_digest(&findings);
    DeclClosureStatus::ArtifactIncomplete { findings, witness }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(text: &str) -> Name {
        text.split('.').fold(Name::anonymous(), Name::str)
    }

    fn input(decl: &str, safety: DefinitionSafety, deps: &[&str]) -> DeclClosureInput {
        DeclClosureInput {
            name: name(decl),
            safety,
            dependencies: deps.iter().map(|d| name(d)).collect(),
        }
    }

    fn finding(declaration: Name, missing: Vec<Name>) -> MissingConstantFinding {
        MissingConstantFinding {
            declaration,
            safety: DefinitionSafety::Unsafe,
            missing,
        }
    }

    /// The witness has exactly one job: distinguish the finding set it binds. A
    /// `Name` is a structured path of anonymous, string, and numeric components, and
    /// flattening it to its display form collapses distinct structures onto one
    /// string — so the digest stopped being a discriminator.
    ///
    /// This is soundness-adjacent rather than cosmetic: a colliding witness lets a
    /// cached or replayed result be attributed to the wrong closure, silently, with
    /// no error anywhere. The pairs below are the three distinct ways the display
    /// projection loses information, and every one of them collided before this was
    /// fixed.
    #[test]
    fn the_witness_binds_name_structure_not_its_display_form() {
        let dotted_component = Name::str(Name::anonymous(), "a.b");
        let two_components = Name::str(Name::str(Name::anonymous(), "a"), "b");
        let numeric = Name::num(Name::anonymous(), 1);
        let numeric_lookalike = Name::str(Name::anonymous(), "1");

        // Each pair is genuinely two different names that render identically.
        for (left, right) in [
            (&dotted_component, &two_components),
            (&numeric, &numeric_lookalike),
        ] {
            assert_ne!(left, right, "the pair must be structurally distinct");
            assert_eq!(
                left.to_display_string(),
                right.to_display_string(),
                "the pair must be indistinguishable in display form, or it proves nothing"
            );
        }

        // (1) ambiguity in the declaration position
        assert_ne!(
            witness_digest(&[finding(dotted_component.clone(), vec![])]),
            witness_digest(&[finding(two_components.clone(), vec![])]),
            "two distinct declarations share a witness"
        );
        // (2) ambiguity inside the missing list
        let host = Name::str(Name::anonymous(), "D");
        assert_ne!(
            witness_digest(&[finding(host.clone(), vec![dotted_component])]),
            witness_digest(&[finding(host.clone(), vec![two_components])]),
            "two distinct missing-reference sets share a witness"
        );
        // (3) numeric vs string components — the case that occurs in real pin data,
        // where Lean's private mangling puts a genuine `Num` component inside names
        // like `_private.Init.Prelude.0.Lean.Name.hash._proof_1`.
        assert_ne!(
            witness_digest(&[finding(numeric.clone(), vec![])]),
            witness_digest(&[finding(numeric_lookalike, vec![])]),
            "a numeric component and its string lookalike share a witness"
        );

        // The separator itself must not be forgeable: a component containing the
        // component separator may not imitate a deeper path.
        let nested = Name::str(Name::str(Name::str(Name::anonymous(), "x"), "y"), "z");
        let flat = Name::str(Name::anonymous(), "x.y.z");
        assert_ne!(
            witness_digest(&[finding(nested, vec![])]),
            witness_digest(&[finding(flat, vec![])]),
            "a dotted component forged a deeper path"
        );

        // Discrimination must not have been bought with instability: the witness is
        // still a pure function of the finding set.
        let stable = finding(numeric, vec![Name::str(Name::anonymous(), "M")]);
        assert_eq!(
            witness_digest(std::slice::from_ref(&stable)),
            witness_digest(std::slice::from_ref(&stable)),
            "the witness must stay deterministic"
        );
    }

    fn resolver(present: &[&str]) -> impl Fn(&Name) -> bool {
        let set: BTreeSet<String> = present.iter().map(|s| s.to_string()).collect();
        move |n: &Name| set.contains(&n.to_display_string())
    }

    #[test]
    fn complete_control_definitions_stay_checkable() {
        let inputs = [
            input("A.f", DefinitionSafety::Safe, &["Nat", "Nat.succ"]),
            input("A.g", DefinitionSafety::Unsafe, &["A.f"]),
        ];
        let status = classify_closures(
            &inputs,
            resolver(&["Nat", "Nat.succ", "A.f"]),
            DeclClosureBudget::DEFAULT,
            || false,
        );
        assert_eq!(status, DeclClosureStatus::Complete);
        assert!(status.is_cacheable());
        assert!(status.may_enter_environment());
    }

    #[test]
    fn missing_private_auxiliary_yields_artifact_incomplete_not_reject() {
        let inputs = [input(
            "Lean.Name.hash._override",
            DefinitionSafety::Unsafe,
            &["Nat", "_private.Init.Prelude.0.Lean.Name.hash._proof_1"],
        )];
        let status = classify_closures(
            &inputs,
            resolver(&["Nat"]),
            DeclClosureBudget::DEFAULT,
            || false,
        );
        let DeclClosureStatus::ArtifactIncomplete { findings, witness } = &status else {
            panic!("expected ArtifactIncomplete, got {status:?}");
        };
        assert_eq!(findings.len(), 1);
        assert_eq!(
            findings[0].missing[0].to_display_string(),
            "_private.Init.Prelude.0.Lean.Name.hash._proof_1"
        );
        assert_eq!(status.outcome_label(), "inconclusive-artifact-incomplete");
        assert!(
            !status.is_cacheable(),
            "ArtifactIncomplete is never cacheable"
        );
        assert!(
            !status.may_enter_environment(),
            "ArtifactIncomplete never enters an environment"
        );
        assert_eq!(witness, &witness_digest(findings));
    }

    #[test]
    fn status_and_witness_are_input_order_independent() {
        let a = input(
            "M.x._unsafe_rec",
            DefinitionSafety::Partial,
            &["M.gone", "Nat"],
        );
        let b = input("M.y._override", DefinitionSafety::Unsafe, &["M.also_gone"]);
        let c = input("M.ok", DefinitionSafety::Safe, &["Nat"]);
        let orders: [[&DeclClosureInput; 3]; 4] =
            [[&a, &b, &c], [&c, &b, &a], [&b, &a, &c], [&c, &a, &b]];
        let mut statuses = Vec::new();
        for order in orders {
            let inputs: Vec<DeclClosureInput> = order.into_iter().cloned().collect();
            statuses.push(classify_closures(
                &inputs,
                resolver(&["Nat"]),
                DeclClosureBudget::DEFAULT,
                || false,
            ));
        }
        for status in &statuses[1..] {
            assert_eq!(status, &statuses[0], "a permutation changed the census");
        }
        // Dependency-order permutation too.
        let a_rev = input(
            "M.x._unsafe_rec",
            DefinitionSafety::Partial,
            &["Nat", "M.gone"],
        );
        let permuted = classify_closures(
            &[a_rev, b, c],
            resolver(&["Nat"]),
            DeclClosureBudget::DEFAULT,
            || false,
        );
        assert_eq!(permuted, statuses[0]);
    }

    #[test]
    fn findings_and_missing_lists_are_canonically_ordered_and_deduplicated() {
        let inputs = [
            input(
                "M.z",
                DefinitionSafety::Partial,
                &["M.gone_b", "M.gone_a", "M.gone_b", "M.gone_a"],
            ),
            input("M.a", DefinitionSafety::Unsafe, &["M.gone_c"]),
        ];
        let status =
            classify_closures(&inputs, resolver(&[]), DeclClosureBudget::DEFAULT, || false);
        let DeclClosureStatus::ArtifactIncomplete { findings, .. } = status else {
            panic!("expected ArtifactIncomplete");
        };
        assert_eq!(findings.len(), 2);
        // Findings ordered by declaration; missing lists deduped and ordered.
        assert_eq!(findings[0].declaration.to_display_string(), "M.a");
        assert_eq!(findings[1].declaration.to_display_string(), "M.z");
        let missing: Vec<String> = findings[1]
            .missing
            .iter()
            .map(|n| n.to_display_string())
            .collect();
        assert_eq!(
            missing,
            vec!["M.gone_a".to_string(), "M.gone_b".to_string()]
        );
    }

    #[test]
    fn count_conservation_partitions_every_declaration_exactly_once() {
        let inputs = [
            input("M.a", DefinitionSafety::Safe, &["Nat"]),
            input("M.b", DefinitionSafety::Unsafe, &["M.gone"]),
            input("M.c", DefinitionSafety::Partial, &["Nat"]),
            input("M.d", DefinitionSafety::Partial, &["M.gone", "M.gone2"]),
        ];
        let status = classify_closures(
            &inputs,
            resolver(&["Nat"]),
            DeclClosureBudget::DEFAULT,
            || false,
        );
        let DeclClosureStatus::ArtifactIncomplete { findings, .. } = status else {
            panic!("expected ArtifactIncomplete");
        };
        let incomplete: BTreeSet<String> = findings
            .iter()
            .map(|f| f.declaration.to_display_string())
            .collect();
        let complete: Vec<&DeclClosureInput> = inputs
            .iter()
            .filter(|i| !incomplete.contains(&i.name.to_display_string()))
            .collect();
        assert_eq!(incomplete.len() + complete.len(), inputs.len());
        assert_eq!(incomplete.len(), 2);
    }

    #[test]
    fn resource_boundaries_zero_one_under_exact_one_over() {
        let two_edges = [input("M.a", DefinitionSafety::Safe, &["Nat", "Bool"])];
        let run = |max_edges: usize| {
            classify_closures(
                &two_edges,
                resolver(&["Nat", "Bool"]),
                DeclClosureBudget {
                    max_dependency_edges: max_edges,
                    max_findings: 8,
                },
                || false,
            )
        };
        // zero: the first edge already exceeds.
        let DeclClosureStatus::Inconclusive {
            reason:
                DeclClosureInconclusive::ResourceLimitExceeded {
                    resource, limit, ..
                },
        } = run(0)
        else {
            panic!("zero budget must be inconclusive");
        };
        assert_eq!(resource, DeclClosureResource::DependencyEdges);
        assert_eq!(limit, 0);
        // one-under (limit 1 of 2 edges): inconclusive.
        assert!(matches!(run(1), DeclClosureStatus::Inconclusive { .. }));
        // exact (limit 2 of 2): completes.
        assert_eq!(run(2), DeclClosureStatus::Complete);
        // one-over (limit 3 of 2): completes.
        assert_eq!(run(3), DeclClosureStatus::Complete);
    }

    #[test]
    fn findings_budget_is_typed_exhaustion_not_truncation() {
        let inputs = [
            input("M.a", DefinitionSafety::Unsafe, &["M.gone_a"]),
            input("M.b", DefinitionSafety::Unsafe, &["M.gone_b"]),
        ];
        let status = classify_closures(
            &inputs,
            resolver(&[]),
            DeclClosureBudget {
                max_dependency_edges: 100,
                max_findings: 1,
            },
            || false,
        );
        let DeclClosureStatus::Inconclusive {
            reason: DeclClosureInconclusive::ResourceLimitExceeded { resource, .. },
        } = status
        else {
            panic!("a truncated finding set may never present as a verdict");
        };
        assert_eq!(resource, DeclClosureResource::Findings);
    }

    #[test]
    fn cancellation_is_typed_and_never_a_partial_verdict() {
        let inputs = [
            input("M.a", DefinitionSafety::Unsafe, &["M.gone"]),
            input("M.b", DefinitionSafety::Safe, &["Nat"]),
        ];
        let status = classify_closures(
            &inputs,
            resolver(&["Nat"]),
            DeclClosureBudget::DEFAULT,
            || true,
        );
        assert_eq!(
            status,
            DeclClosureStatus::Inconclusive {
                reason: DeclClosureInconclusive::Cancelled { at_declaration: 0 }
            }
        );
        assert!(!status.is_cacheable());
        assert!(!status.may_enter_environment());
    }

    #[test]
    fn duplicate_declaration_is_an_internal_fault() {
        let inputs = [
            input("M.a", DefinitionSafety::Safe, &[]),
            input("M.a", DefinitionSafety::Unsafe, &[]),
        ];
        let status =
            classify_closures(&inputs, resolver(&[]), DeclClosureBudget::DEFAULT, || false);
        assert_eq!(
            status,
            DeclClosureStatus::InternalFault {
                fault: DeclClosureFault::DuplicateDeclaration {
                    declaration: name("M.a")
                }
            }
        );
        assert!(!status.is_cacheable());
    }

    #[test]
    fn witness_digest_binds_the_exact_finding_set() {
        let base = vec![MissingConstantFinding {
            declaration: name("M.a"),
            safety: DefinitionSafety::Unsafe,
            missing: vec![name("M.gone")],
        }];
        let with_extra = vec![
            base[0].clone(),
            MissingConstantFinding {
                declaration: name("M.b"),
                safety: DefinitionSafety::Partial,
                missing: vec![name("M.gone")],
            },
        ];
        let omitted_ref = vec![MissingConstantFinding {
            declaration: name("M.a"),
            safety: DefinitionSafety::Unsafe,
            missing: vec![],
        }];
        let collapsed_safety = vec![MissingConstantFinding {
            declaration: name("M.a"),
            safety: DefinitionSafety::Partial,
            missing: vec![name("M.gone")],
        }];
        let w0 = witness_digest(&base);
        assert_eq!(w0, witness_digest(&base), "witness is deterministic");
        assert_ne!(
            w0,
            witness_digest(&collapsed_safety),
            "a collapsed safety class changes the witness"
        );
        assert_ne!(
            w0,
            witness_digest(&with_extra),
            "extra finding changes witness"
        );
        assert_ne!(
            w0,
            witness_digest(&omitted_ref),
            "omitted missing ref changes witness"
        );
    }
}
