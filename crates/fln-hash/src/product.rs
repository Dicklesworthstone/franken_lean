//! Canonical product sidecars for exact FLBC artifacts (plan §13.4, D18).
//!
//! A sidecar is a binding, not an attestation. Its only public constructor hashes the
//! actual bytes of all thirteen closure components and the exact product bytes under
//! dedicated domains; callers cannot provide precomputed roots. Decoding independently
//! recomputes the aggregate closure root and rejects missing, duplicated, reordered, or
//! unknown components. Schema v1 deliberately supports only the `Standard` profile:
//! carrying a `Certified` tag without a [`fln_core::mode::CertifiedEligibility`] proof
//! would turn a marker into authority.

use fln_core::mode::{
    ArtifactCoordinates, BuildProfileId, CgsePolicyId, ClaimRowId, ClosureComponent,
    CompatibilityRefusal, ContentRoot, DeterminismClass, EpochId, Mode, ObservedArtifactScope,
    ReproducibilityProfile, TargetId, artifact_compatibility,
};

use crate::canon::{CanonError, CanonReader, CanonWriter, Canonical, SCHEMA_FLBC_PRODUCT_SIDECAR};
use crate::domain::{Domain, DomainHasher, hash};

const COMPONENT_COUNT: usize = ClosureComponent::ALL.len();
const COMPONENT_HASH_TAG: &str = "fln.flbc-product-sidecar.component/1";
const CLOSURE_HASH_TAG: &str = "fln.flbc-product-sidecar.closure/1";

/// Non-root coordinates supplied by a producer of one standard-profile product.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StandardProductCoordinatesV1 {
    pub mode: Mode,
    pub epoch: EpochId,
    pub cgse_policy: CgsePolicyId,
    pub determinism: DeterminismClass,
    pub target: TargetId,
    pub build_profile: BuildProfileId,
}

/// Actual bytes contributing one typed closure component.
#[derive(Debug, Clone, Copy)]
pub struct ClosureMaterialV1<'a> {
    pub component: ClosureComponent,
    pub bytes: &'a [u8],
}

/// Why actual closure material could not form a complete sidecar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductSidecarBuildRefusal {
    MissingClosureComponent { component: ClosureComponent },
    DuplicateClosureComponent { component: ClosureComponent },
    ZeroRegistryIdentity { coordinate: &'static str },
}

impl std::fmt::Display for ProductSidecarBuildRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingClosureComponent { component } => {
                write!(f, "missing closure component {component:?}")
            }
            Self::DuplicateClosureComponent { component } => {
                write!(f, "duplicate closure component {component:?}")
            }
            Self::ZeroRegistryIdentity { coordinate } => {
                write!(f, "{coordinate} has the unregistered zero identity")
            }
        }
    }
}

/// A decoded sidecar that has already passed schema, closure-shape, and aggregate-root
/// validation. Exact product bytes and the consumer mode remain boundary inputs and are
/// checked by [`FlbcProductSidecarV1::verify_product`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlbcProductSidecarV1 {
    coordinates: StandardProductCoordinatesV1,
    component_roots: [ContentRoot; COMPONENT_COUNT],
    closure_root: ContentRoot,
    product_root: ContentRoot,
}

/// Failure to bind a validated sidecar to a consumer or to actual product material.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProductSidecarRefusal {
    ProductRootMismatch,
    ClosureComponentMismatch { component: ClosureComponent },
    CoordinateMismatch { coordinate: &'static str },
    Mode(CompatibilityRefusal),
}

impl std::fmt::Display for ProductSidecarRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ProductRootMismatch => f.write_str("FLBC product root mismatch"),
            Self::ClosureComponentMismatch { component } => {
                write!(
                    f,
                    "closure component {component:?} does not match current material"
                )
            }
            Self::CoordinateMismatch { coordinate } => {
                write!(
                    f,
                    "product coordinate {coordinate} does not match the consumer"
                )
            }
            Self::Mode(refusal) => write!(f, "product mode is incompatible: {refusal:?}"),
        }
    }
}

impl FlbcProductSidecarV1 {
    /// Build a standard-profile sidecar from actual material and exact product bytes.
    pub fn build_standard(
        coordinates: StandardProductCoordinatesV1,
        material: &[ClosureMaterialV1<'_>],
        flbc_product: &[u8],
    ) -> Result<Self, ProductSidecarBuildRefusal> {
        validate_coordinate_ids(coordinates)?;
        let mut observed = [None; COMPONENT_COUNT];
        for entry in material {
            let slot = &mut observed[component_index(entry.component)];
            if slot
                .replace(component_root(entry.component, entry.bytes))
                .is_some()
            {
                return Err(ProductSidecarBuildRefusal::DuplicateClosureComponent {
                    component: entry.component,
                });
            }
        }
        let component_roots = roots_from_observed(&observed)?;
        Ok(Self {
            coordinates,
            closure_root: aggregate_closure_root(&component_roots),
            product_root: flbc_product_root(flbc_product),
            component_roots,
        })
    }

    pub const fn mode(&self) -> Mode {
        self.coordinates.mode
    }

    pub const fn reproducibility(&self) -> ReproducibilityProfile {
        ReproducibilityProfile::Standard
    }

    pub const fn closure_root(&self) -> ContentRoot {
        self.closure_root
    }

    pub const fn product_root(&self) -> ContentRoot {
        self.product_root
    }

    pub const fn component_root(&self, component: ClosureComponent) -> ContentRoot {
        self.component_roots[component_index(component)]
    }

    pub const fn coordinates(&self) -> ArtifactCoordinates {
        ArtifactCoordinates {
            epoch: self.coordinates.epoch,
            cgse_policy: self.coordinates.cgse_policy,
            determinism: self.coordinates.determinism,
            reproducibility: ReproducibilityProfile::Standard,
            target: self.coordinates.target,
            build_profile: self.coordinates.build_profile,
            closure_root: self.closure_root,
            product_root: self.product_root,
            claim_row: None::<ClaimRowId>,
        }
    }

    pub const fn standard_coordinates(&self) -> StandardProductCoordinatesV1 {
        self.coordinates
    }

    /// Require every non-root coordinate to match independently derived consumer
    /// coordinates. Component material binds their descriptive bytes separately.
    pub fn verify_coordinates(
        &self,
        expected: StandardProductCoordinatesV1,
    ) -> Result<(), ProductSidecarRefusal> {
        for (coordinate, matches) in [
            ("mode", self.coordinates.mode == expected.mode),
            ("epoch", self.coordinates.epoch == expected.epoch),
            (
                "CGSE policy",
                self.coordinates.cgse_policy == expected.cgse_policy,
            ),
            (
                "determinism",
                self.coordinates.determinism == expected.determinism,
            ),
            ("target", self.coordinates.target == expected.target),
            (
                "build profile",
                self.coordinates.build_profile == expected.build_profile,
            ),
        ] {
            if !matches {
                return Err(ProductSidecarRefusal::CoordinateMismatch { coordinate });
            }
        }
        Ok(())
    }

    /// Recompute the exact product root and enforce the core mixed-mode/frontier law.
    pub fn verify_product(
        &self,
        flbc_product: &[u8],
        consumer_mode: Mode,
    ) -> Result<(), ProductSidecarRefusal> {
        if flbc_product_root(flbc_product) != self.product_root {
            return Err(ProductSidecarRefusal::ProductRootMismatch);
        }
        artifact_compatibility(
            consumer_mode,
            ObservedArtifactScope::ModeBound {
                tag: self.coordinates.mode.tag(),
                semantic_root: self.product_root,
            },
            self.product_root,
            &[],
        )
        .map_err(ProductSidecarRefusal::Mode)?;
        Ok(())
    }

    /// Re-hash current material for one component. Consumers can rebind every input
    /// available in their own closure without trusting the sidecar's root field.
    pub fn verify_component_material(
        &self,
        component: ClosureComponent,
        material: &[u8],
    ) -> Result<(), ProductSidecarRefusal> {
        if component_root(component, material) != self.component_root(component) {
            return Err(ProductSidecarRefusal::ClosureComponentMismatch { component });
        }
        Ok(())
    }
}

impl Canonical for FlbcProductSidecarV1 {
    const SCHEMA: crate::canon::SchemaId = SCHEMA_FLBC_PRODUCT_SIDECAR;

    fn write_body(&self, writer: &mut CanonWriter) {
        writer.u8(self.coordinates.mode.tag());
        write_u128(writer, self.coordinates.epoch.get());
        write_u128(writer, self.coordinates.cgse_policy.get());
        writer.u8(self.coordinates.determinism.tag());
        writer.u8(ReproducibilityProfile::Standard.tag());
        write_u128(writer, self.coordinates.target.get());
        write_u128(writer, self.coordinates.build_profile.get());
        writer.u64(COMPONENT_COUNT as u64);
        for component in ClosureComponent::ALL {
            writer.u8(component_tag(component));
            write_root(writer, self.component_root(component));
        }
        write_root(writer, self.closure_root);
        write_root(writer, self.product_root);
    }

    fn read_body(reader: &mut CanonReader<'_>) -> Result<Self, CanonError> {
        let mode = Mode::from_tag(Some(reader.u8()?))
            .map_err(|_| reader.reject("unknown FLBC sidecar mode"))?;
        let epoch = EpochId::new(read_u128(reader)?);
        let cgse_policy = CgsePolicyId::new(read_u128(reader)?);
        let determinism = DeterminismClass::from_tag(Some(reader.u8()?))
            .map_err(|_| reader.reject("unknown FLBC sidecar determinism class"))?;
        let profile = ReproducibilityProfile::from_tag(Some(reader.u8()?))
            .map_err(|_| reader.reject("unknown FLBC sidecar reproducibility profile"))?;
        if profile != ReproducibilityProfile::Standard {
            return Err(reader.reject("FLBC sidecar v1 cannot carry an unproven certified claim"));
        }
        let target = TargetId::new(read_u128(reader)?);
        let build_profile = BuildProfileId::new(read_u128(reader)?);
        let coordinates = StandardProductCoordinatesV1 {
            mode,
            epoch,
            cgse_policy,
            determinism,
            target,
            build_profile,
        };
        validate_coordinate_ids(coordinates)
            .map_err(|_| reader.reject("FLBC sidecar contains an unregistered zero identity"))?;

        let count = reader.u64()?;
        if count != COMPONENT_COUNT as u64 {
            return Err(reader.reject("FLBC sidecar must contain all 13 closure components"));
        }
        let mut component_roots = [ContentRoot::new([0; 32]); COMPONENT_COUNT];
        for expected in ClosureComponent::ALL {
            let observed = reader.u8()?;
            if observed != component_tag(expected) {
                return Err(reader.reject(
                    "FLBC sidecar closure components are missing, duplicated, or out of order",
                ));
            }
            component_roots[component_index(expected)] = read_root(reader)?;
        }
        let closure_root = read_root(reader)?;
        if aggregate_closure_root(&component_roots) != closure_root {
            return Err(reader.reject("FLBC sidecar aggregate closure root mismatch"));
        }
        let product_root = read_root(reader)?;
        Ok(Self {
            coordinates,
            component_roots,
            closure_root,
            product_root,
        })
    }
}

/// Root of exact FLBC bytes under the permanent artifact-product domain.
pub fn flbc_product_root(flbc_product: &[u8]) -> ContentRoot {
    ContentRoot::new(hash(Domain::ArtifactProduct, flbc_product).0)
}

fn validate_coordinate_ids(
    coordinates: StandardProductCoordinatesV1,
) -> Result<(), ProductSidecarBuildRefusal> {
    for (coordinate, value) in [
        ("epoch", coordinates.epoch.get()),
        ("CGSE policy", coordinates.cgse_policy.get()),
        ("target", coordinates.target.get()),
        ("build profile", coordinates.build_profile.get()),
    ] {
        if value == 0 {
            return Err(ProductSidecarBuildRefusal::ZeroRegistryIdentity { coordinate });
        }
    }
    Ok(())
}

fn roots_from_observed(
    observed: &[Option<ContentRoot>; COMPONENT_COUNT],
) -> Result<[ContentRoot; COMPONENT_COUNT], ProductSidecarBuildRefusal> {
    let mut roots = [ContentRoot::new([0; 32]); COMPONENT_COUNT];
    for component in ClosureComponent::ALL {
        roots[component_index(component)] = observed[component_index(component)]
            .ok_or(ProductSidecarBuildRefusal::MissingClosureComponent { component })?;
    }
    Ok(roots)
}

const fn component_index(component: ClosureComponent) -> usize {
    component as usize
}

const fn component_tag(component: ClosureComponent) -> u8 {
    component as u8
}

fn component_root(component: ClosureComponent, material: &[u8]) -> ContentRoot {
    let mut hasher = DomainHasher::new(Domain::ArtifactClosureComponent);
    hasher
        .update(&(COMPONENT_HASH_TAG.len() as u64).to_le_bytes())
        .update(COMPONENT_HASH_TAG.as_bytes())
        .update(&[component_tag(component)])
        .update(&(material.len() as u64).to_le_bytes())
        .update(material);
    ContentRoot::new(hasher.finalize().0)
}

fn aggregate_closure_root(component_roots: &[ContentRoot; COMPONENT_COUNT]) -> ContentRoot {
    let mut writer = CanonWriter::new();
    writer.str(CLOSURE_HASH_TAG);
    writer.u64(COMPONENT_COUNT as u64);
    for component in ClosureComponent::ALL {
        writer.u8(component_tag(component));
        write_root(&mut writer, component_roots[component_index(component)]);
    }
    ContentRoot::new(hash(Domain::ArtifactClosure, &writer.into_bytes()).0)
}

fn write_root(writer: &mut CanonWriter, root: ContentRoot) {
    writer.bytes(&root.bytes());
}

fn read_root(reader: &mut CanonReader<'_>) -> Result<ContentRoot, CanonError> {
    let bytes: [u8; 32] = reader
        .bytes()?
        .try_into()
        .map_err(|_| reader.reject("FLBC sidecar root must be 32 bytes"))?;
    Ok(ContentRoot::new(bytes))
}

fn write_u128(writer: &mut CanonWriter, value: u128) {
    writer.bytes(&value.to_le_bytes());
}

fn read_u128(reader: &mut CanonReader<'_>) -> Result<u128, CanonError> {
    let bytes: [u8; 16] = reader
        .bytes()?
        .try_into()
        .map_err(|_| reader.reject("FLBC sidecar registry identity must be 16 bytes"))?;
    Ok(u128::from_le_bytes(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn coordinates(mode: Mode) -> StandardProductCoordinatesV1 {
        StandardProductCoordinatesV1 {
            mode,
            epoch: EpochId::new(4_032_000),
            cgse_policy: CgsePolicyId::new(1),
            determinism: DeterminismClass::D1Canonicalized,
            target: TargetId::new(1),
            build_profile: BuildProfileId::new(1),
        }
    }

    fn material(mode: Mode) -> Vec<(ClosureComponent, Vec<u8>)> {
        ClosureComponent::ALL
            .into_iter()
            .map(|component| {
                let bytes = if component == ClosureComponent::Mode {
                    vec![mode.tag()]
                } else {
                    format!("material-{component:?}").into_bytes()
                };
                (component, bytes)
            })
            .collect()
    }

    fn build(mode: Mode, product: &[u8]) -> FlbcProductSidecarV1 {
        let bytes = material(mode);
        let entries: Vec<_> = bytes
            .iter()
            .map(|(component, bytes)| ClosureMaterialV1 {
                component: *component,
                bytes,
            })
            .collect();
        FlbcProductSidecarV1::build_standard(coordinates(mode), &entries, product)
            .expect("complete fixture closure")
    }

    #[test]
    fn canonical_round_trip_retains_all_coordinates_and_roots() {
        let sidecar = build(Mode::Sound, b"exact flbc");
        let bytes = sidecar.to_canonical_bytes();
        let decoded = FlbcProductSidecarV1::from_canonical_bytes(&bytes).expect("sidecar");
        assert_eq!(decoded, sidecar);
        assert_eq!(decoded.reproducibility(), ReproducibilityProfile::Standard);
        assert_eq!(decoded.coordinates().claim_row, None);
        decoded
            .verify_product(b"exact flbc", Mode::Sound)
            .expect("exact product and mode");
    }

    #[test]
    fn missing_and_duplicate_material_are_refused_before_any_manifest_exists() {
        let bytes = material(Mode::Sound);
        let mut entries: Vec<_> = bytes
            .iter()
            .map(|(component, bytes)| ClosureMaterialV1 {
                component: *component,
                bytes,
            })
            .collect();
        entries.pop();
        assert_eq!(
            FlbcProductSidecarV1::build_standard(coordinates(Mode::Sound), &entries, b"x"),
            Err(ProductSidecarBuildRefusal::MissingClosureComponent {
                component: ClosureComponent::ReplayInputs,
            })
        );
        entries.push(entries[0]);
        assert_eq!(
            FlbcProductSidecarV1::build_standard(coordinates(Mode::Sound), &entries, b"x"),
            Err(ProductSidecarBuildRefusal::DuplicateClosureComponent {
                component: ClosureComponent::Sources,
            })
        );
    }

    #[test]
    fn codec_refuses_a_manifest_whose_component_count_omits_one_root() {
        let sidecar = build(Mode::Sound, b"x");
        let mut bytes = sidecar.to_canonical_bytes();
        let mut reader = CanonReader::new(&bytes);
        reader.expect_schema(SCHEMA_FLBC_PRODUCT_SIDECAR).unwrap();
        reader.u8().unwrap();
        read_u128(&mut reader).unwrap();
        read_u128(&mut reader).unwrap();
        reader.u8().unwrap();
        reader.u8().unwrap();
        read_u128(&mut reader).unwrap();
        read_u128(&mut reader).unwrap();
        let count_at = reader.offset();
        bytes[count_at..count_at + 8].copy_from_slice(&12_u64.to_le_bytes());
        let error = FlbcProductSidecarV1::from_canonical_bytes(&bytes)
            .expect_err("an omitted component cannot decode");
        assert!(error.what.contains("all 13 closure components"));
        FlbcProductSidecarV1::from_canonical_bytes(&sidecar.to_canonical_bytes())
            .expect("unmodified recovery control");
    }

    #[test]
    fn codec_refuses_a_certified_marker_without_an_eligibility_proof() {
        let sidecar = build(Mode::Sound, b"x");
        let mut bytes = sidecar.to_canonical_bytes();
        let mut reader = CanonReader::new(&bytes);
        reader.expect_schema(SCHEMA_FLBC_PRODUCT_SIDECAR).unwrap();
        reader.u8().unwrap();
        read_u128(&mut reader).unwrap();
        read_u128(&mut reader).unwrap();
        reader.u8().unwrap();
        let profile_at = reader.offset();
        bytes[profile_at] = ReproducibilityProfile::Certified.tag();
        let error = FlbcProductSidecarV1::from_canonical_bytes(&bytes)
            .expect_err("a marker cannot manufacture certified authority");
        assert!(error.what.contains("unproven certified claim"));
        FlbcProductSidecarV1::from_canonical_bytes(&sidecar.to_canonical_bytes())
            .expect("unmodified recovery control");
    }

    #[test]
    fn frontier_contamination_and_product_substitution_are_refused() {
        let frontier = build(Mode::Frontier, b"frontier product");
        assert!(matches!(
            frontier.verify_product(b"frontier product", Mode::Sound),
            Err(ProductSidecarRefusal::Mode(
                CompatibilityRefusal::FrontierLeak { .. }
            ))
        ));
        let sound = build(Mode::Sound, b"sound product");
        assert_eq!(
            sound.verify_product(b"substituted product", Mode::Sound),
            Err(ProductSidecarRefusal::ProductRootMismatch)
        );
        sound
            .verify_product(b"sound product", Mode::Sound)
            .expect("unmodified recovery control");
    }

    #[test]
    fn component_roots_bind_the_component_tag_as_well_as_its_bytes() {
        let bytes = b"same material";
        assert_ne!(
            component_root(ClosureComponent::Sources, bytes),
            component_root(ClosureComponent::Toolchain, bytes)
        );
        let sidecar = build(Mode::Sound, b"x");
        assert_eq!(
            sidecar.verify_component_material(ClosureComponent::Sources, b"wrong"),
            Err(ProductSidecarRefusal::ClosureComponentMismatch {
                component: ClosureComponent::Sources,
            })
        );
    }

    #[test]
    fn consumer_coordinates_are_not_trusted_from_the_sidecar() {
        let sidecar = build(Mode::Sound, b"x");
        let mut expected = coordinates(Mode::Sound);
        expected.cgse_policy = CgsePolicyId::new(2);
        assert_eq!(
            sidecar.verify_coordinates(expected),
            Err(ProductSidecarRefusal::CoordinateMismatch {
                coordinate: "CGSE policy",
            })
        );
        sidecar
            .verify_coordinates(coordinates(Mode::Sound))
            .expect("unmodified recovery control");
    }
}
