//! Metamorphic laws over the implemented FrankenLean substrate.
//!
//! The parser and elaborator are not implemented yet, so this rig deliberately
//! exercises only relations with a real public surface today. Every permutation is
//! generated; no expected ordering is hand-enumerated.
//!
//! Relation strength (`fault sensitivity × independence ÷ cost`):
//! - canonical set permutation invariance: `5 × 4 ÷ 1 = 20`;
//! - ordered canonical row sensitivity: `5 × 5 ÷ 1 = 25`;
//! - independent declaration commutation: `5 × 4 ÷ 2 = 10`;
//! - extension journal order identity: `5 × 5 ÷ 2 = 12.5`;
//! - snapshot/rebuild observational equivalence and isolation: `5 × 5 ÷ 2 = 12.5`;
//! - repeated olean decode identity: `5 × 4 ÷ 2 = 10`;
//! - truncated/corrupt olean typed totality: `5 × 5 ÷ 3 = 8.3`.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::{LogicalRoot, LogicalRootBuilder};
use fln_olean::decl::{DeclDecoder, DeclError};
use fln_olean::format;
use fln_olean::region::{OleanView, RegionError, WalkBudget};

const PROPERTY_SEEDS: [u64; 4] = [
    0x6d65_7461_6d6f_7270,
    0x6869_635f_6c61_7731,
    0x7472_6962_756e_616c,
    0x6672_616e_6b65_6e21,
];
const ROW_COUNT: usize = 5;
const OLEAN_CORRUPTION_CHILD: &str = "FLN_METAMORPHIC_OLEAN_CORRUPTION_CHILD";
const OLEAN_FIXTURES: [&str; 3] = [
    "Init.olean",
    "Init.BinderNameHint.olean",
    "Init.SizeOfLemmas.olean",
];

#[derive(Debug, Clone)]
struct Seeded {
    state: u64,
}

impl Seeded {
    fn new(seed: u64) -> Self {
        assert_ne!(seed, 0, "xorshift seed must be nonzero");
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        let mut value = self.state;
        value ^= value << 13;
        value ^= value >> 7;
        value ^= value << 17;
        self.state = value;
        value
    }
}

fn generated_permutations(len: usize) -> Vec<Vec<usize>> {
    fn heap(size: usize, values: &mut [usize], out: &mut Vec<Vec<usize>>) {
        if size == 1 {
            out.push(values.to_vec());
            return;
        }
        heap(size - 1, values, out);
        for index in 0..size - 1 {
            if size.is_multiple_of(2) {
                values.swap(index, size - 1);
            } else {
                values.swap(0, size - 1);
            }
            heap(size - 1, values, out);
        }
    }

    assert!(len > 0, "permutation domain must be nonempty");
    let mut values: Vec<usize> = (0..len).collect();
    let mut out = Vec::new();
    heap(len, &mut values, &mut out);
    let unique: BTreeSet<Vec<usize>> = out.iter().cloned().collect();
    assert_eq!(
        unique.len(),
        out.len(),
        "permutation generator emitted duplicates"
    );
    assert_eq!(
        out.len(),
        (1..=len).product(),
        "permutation generator did not cover the factorial state space"
    );
    out
}

fn name(value: impl AsRef<str>) -> Name {
    Name::str(Name::anonymous(), value.as_ref())
}

fn seeded_names(seed: u64, prefix: &str) -> Vec<Name> {
    let mut rng = Seeded::new(seed);
    (0..ROW_COUNT)
        .map(|index| name(format!("{prefix}_{index}_{:016x}", rng.next())))
        .collect()
}

fn seeded_digests(seed: u64, domain: Domain) -> Vec<Digest> {
    let mut rng = Seeded::new(seed);
    (0..ROW_COUNT)
        .map(|index| {
            let mut bytes = Vec::with_capacity(16);
            bytes.extend_from_slice(&rng.next().to_le_bytes());
            bytes.extend_from_slice(&(index as u64).to_le_bytes());
            hash(domain, &bytes)
        })
        .collect()
}

fn build_set_root(names: &[Name], digests: &[Digest], order: &[usize]) -> LogicalRoot {
    let mut builder = LogicalRootBuilder::new();
    for &index in order {
        builder.add_decl(&names[index], digests[index]);
        builder.add_extension_delta(&names[index], digests[(index + 1) % digests.len()]);
    }
    builder.finalize()
}

fn ordered_map(names: &[Name], values: &[u64], order: &[usize]) -> KVMap {
    let mut map = KVMap::new();
    for &index in order {
        map.insert(names[index].clone(), DataValue::OfNat(values[index]));
    }
    map
}

fn axiom(name: Name, unsafe_flag: bool) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name,
            level_params: Vec::new(),
            type_: Expr::sort(Level::zero()),
        },
        is_unsafe: unsafe_flag,
    })
}

fn seeded_declarations(seed: u64) -> Vec<ConstantInfo> {
    let mut rng = Seeded::new(seed);
    seeded_names(seed ^ 0x6465_636c_6172_6573, "Independent")
        .into_iter()
        .map(|decl_name| axiom(decl_name, rng.next() & 1 == 1))
        .collect()
}

fn build_declaration_environment(declarations: &[ConstantInfo], order: &[usize]) -> Environment {
    let mut environment = Environment::new();
    for &index in order {
        let inserted = environment.add_decl(declarations[index].clone());
        assert!(
            inserted.is_ok(),
            "generated declarations must be independent; order={order:?}, error={:?}",
            inserted.as_ref().err()
        );
        environment = inserted.expect("declaration insertion was checked above");
    }
    environment
}

fn extension_descriptor(seed: u64) -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: name(format!("Metamorphic.Extension.{seed:016x}")),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

fn seeded_payloads(seed: u64) -> Vec<Vec<u8>> {
    let mut rng = Seeded::new(seed);
    (0..ROW_COUNT)
        .map(|index| {
            let mut payload = Vec::with_capacity(17);
            payload.push(index as u8);
            payload.extend_from_slice(&rng.next().to_le_bytes());
            payload.extend_from_slice(&rng.next().to_le_bytes());
            payload
        })
        .collect()
}

fn build_extension_environment(
    descriptor: &ExtensionDescriptor,
    payloads: &[Vec<u8>],
    order: &[usize],
) -> Environment {
    let mut environment = Environment::new()
        .register_extension(descriptor.clone())
        .expect("fresh extension registers");
    for &index in order {
        environment = environment
            .push_extension_entry(&descriptor.name, payloads[index].clone())
            .expect("registered extension accepts an entry");
    }
    environment
}

fn extension_payloads(environment: &Environment, extension: &Name) -> Vec<Vec<u8>> {
    environment
        .extension(extension)
        .expect("registered extension remains visible")
        .entries()
        .map(|entry| entry.payload.as_ref().to_vec())
        .collect()
}

fn fixture_path(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3")
        .join(name)
}

fn fixture_bytes(name: &str) -> Vec<u8> {
    let bytes = std::fs::read(fixture_path(name));
    assert!(
        bytes.is_ok(),
        "failed to read pinned fixture {name}: {:?}",
        bytes.as_ref().err()
    );
    bytes.expect("fixture read was checked above")
}

#[derive(Debug)]
enum DecodeFailure {
    Region(RegionError),
    Declaration(DeclError),
}

impl std::fmt::Display for DecodeFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeFailure::Region(error) => write!(formatter, "region: {error}"),
            DecodeFailure::Declaration(error) => write!(formatter, "declaration: {error:?}"),
        }
    }
}

impl From<RegionError> for DecodeFailure {
    fn from(value: RegionError) -> Self {
        Self::Region(value)
    }
}

impl From<DeclError> for DecodeFailure {
    fn from(value: DeclError) -> Self {
        Self::Declaration(value)
    }
}

fn decode_transcript(bytes: &[u8]) -> Result<Vec<u8>, DecodeFailure> {
    let view = OleanView::parse(bytes)?;
    let shared = view.shared_audit()?;
    let walked = view.walk(WalkBudget::default())?;
    let module = view.module_data(WalkBudget::default())?;
    let declarations = DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants()?;

    let mut writer = CanonWriter::new();
    writer.str("fln.conformance.decoded-olean-observation");
    writer.u16(1);
    writer.u8(view.header.version);
    writer.u8(view.header.flags);
    writer.str(&view.header.lean_version);
    writer.str(&view.header.githash);
    writer.u64(view.header.base_addr);
    writer.u64(shared.objects);
    writer.u64(walked.objects);
    writer.u64(walked.ctors);
    writer.u64(walked.arrays);
    writer.u64(walked.scalar_arrays);
    writer.u64(walked.strings);
    writer.u64(walked.mpz);
    writer.u64(walked.thunks);
    writer.u64(walked.tasks);
    writer.u64(walked.refs);
    writer.u64(walked.scalar_refs);
    writer.bool(module.is_module);
    writer.u64(module.imports.len() as u64);
    for import in &module.imports {
        import.module.write_body(&mut writer);
        writer.bool(import.import_all);
        writer.bool(import.is_exported);
        writer.bool(import.is_meta);
    }
    writer.u64(module.const_names.len() as u64);
    for constant_name in &module.const_names {
        writer.str(constant_name);
    }
    writer.u64(module.constants);
    writer.u64(module.extra_const_names);
    writer.u64(module.extensions.len() as u64);
    for extension in &module.extensions {
        writer.str(&extension.name);
        writer.u64(extension.entries);
    }
    writer.u64(declarations.len() as u64);
    for declaration in &declarations {
        writer.str(declaration.kind_name());
        declaration.name().write_body(&mut writer);
        writer.bytes(&Environment::decl_content_digest(declaration).0);
    }
    Ok(writer.into_bytes())
}

fn generated_prefix_lengths(len: usize, seed: u64) -> BTreeSet<usize> {
    let mut lengths = BTreeSet::new();
    lengths.extend(0..=format::OLEAN_HEADER_SIZE.min(len.saturating_sub(1)));
    lengths.extend(len.saturating_sub(64)..len);
    let mut rng = Seeded::new(seed);
    for _ in 0..256 {
        lengths.insert((rng.next() as usize) % len);
    }
    lengths
}

fn exercise_corrupt_olean_inputs() {
    for (fixture_index, fixture_name) in OLEAN_FIXTURES.into_iter().enumerate() {
        let bytes = fixture_bytes(fixture_name);
        assert!(
            decode_transcript(&bytes).is_ok(),
            "clean pinned fixture must decode before mutation: {fixture_name}"
        );

        let cuts = generated_prefix_lengths(
            bytes.len(),
            PROPERTY_SEEDS[fixture_index % PROPERTY_SEEDS.len()],
        );
        for cut in cuts {
            let result = decode_transcript(&bytes[..cut]);
            assert!(
                result.is_err(),
                "accepted truncated pinned artifact: fixture={fixture_name}, cut={cut}, len={}",
                bytes.len()
            );
        }

        let magic = format::OLEAN_MAGIC;
        for permutation in generated_permutations(magic.len()) {
            if permutation == (0..magic.len()).collect::<Vec<_>>() {
                continue;
            }
            let mut corrupt = bytes.clone();
            for (target, source) in permutation.iter().copied().enumerate() {
                corrupt[target] = magic[source];
            }
            let result = decode_transcript(&corrupt);
            assert!(
                result.is_err(),
                "accepted corrupted magic prefix: fixture={fixture_name}, permutation={permutation:?}"
            );
        }

        let base = u64::from_le_bytes(
            bytes[80..88]
                .try_into()
                .expect("generated header has an eight-byte base"),
        );
        let bad_roots = [
            0,
            base.saturating_sub(8),
            base.saturating_add(bytes.len() as u64).saturating_add(8),
            base.saturating_add(format::OLEAN_HEADER_SIZE as u64)
                .saturating_add(1),
        ];
        for bad_root in bad_roots {
            let mut corrupt = bytes.clone();
            corrupt[format::OLEAN_HEADER_SIZE..format::OLEAN_HEADER_SIZE + 8]
                .copy_from_slice(&bad_root.to_le_bytes());
            let result = decode_transcript(&corrupt);
            assert!(
                result.is_err(),
                "accepted corrupted root prefix: fixture={fixture_name}, root={bad_root:#x}"
            );
        }
    }
}

/// Permutative/equivalence MR: set-valued declaration and extension rows have one
/// canonical identity regardless of insertion schedule.
#[test]
fn canonical_set_rows_are_insertion_order_independent() {
    let permutations = generated_permutations(ROW_COUNT);
    for seed in PROPERTY_SEEDS {
        let names = seeded_names(seed, "CanonicalSet");
        let digests = seeded_digests(seed ^ 0x7365_745f_6469_6765, Domain::DeclContent);
        let baseline = build_set_root(&names, &digests, &permutations[0]);
        for permutation in &permutations[1..] {
            assert_eq!(
                build_set_root(&names, &digests, permutation),
                baseline,
                "canonical set identity changed: seed={seed:#018x}, permutation={permutation:?}"
            );
        }

        // Negative control: an order-sensitive stream must vary over this same
        // generated corpus, otherwise the invariant test could pass vacuously.
        let ordered: BTreeSet<Vec<u8>> = permutations
            .iter()
            .map(|permutation| {
                let mut writer = CanonWriter::new();
                for &index in permutation {
                    names[index].write_body(&mut writer);
                    writer.bytes(&digests[index].0);
                }
                writer.into_bytes()
            })
            .collect();
        assert_eq!(
            ordered.len(),
            permutations.len(),
            "negative-control ordered encoder collapsed a permutation: seed={seed:#018x}"
        );
    }
}

/// Exclusive MR: upstream `KVMap` rows are an ordered association list, so every
/// non-identity permutation of unique rows must change both canonical bytes and the
/// options-bearing logical root.
#[test]
fn canonical_ordered_rows_are_order_sensitive() {
    let permutations = generated_permutations(ROW_COUNT);
    for seed in PROPERTY_SEEDS {
        let names = seeded_names(seed, "OrderedRow");
        let mut rng = Seeded::new(seed ^ 0x6f72_6465_7265_645f);
        let values: Vec<u64> = (0..ROW_COUNT).map(|_| rng.next()).collect();
        let baseline_map = ordered_map(&names, &values, &permutations[0]);
        let baseline_bytes = baseline_map.to_canonical_bytes();
        let mut baseline_builder = LogicalRootBuilder::new();
        baseline_builder.set_options(&baseline_map);
        let baseline_root = baseline_builder.finalize();

        for permutation in &permutations[1..] {
            let permuted = ordered_map(&names, &values, permutation);
            assert_ne!(
                permuted.to_canonical_bytes(),
                baseline_bytes,
                "ordered canonical rows lost order: seed={seed:#018x}, permutation={permutation:?}"
            );
            let mut builder = LogicalRootBuilder::new();
            builder.set_options(&permuted);
            assert_ne!(
                builder.finalize(),
                baseline_root,
                "options root lost ordered identity: seed={seed:#018x}, permutation={permutation:?}"
            );
        }
    }
}

/// Permutative/equivalence MR: declarations with no dependency edges commute at the
/// environment boundary, not only inside the lower-level root builder.
#[test]
fn independent_declaration_insertions_commute_at_logical_root() {
    let permutations = generated_permutations(ROW_COUNT);
    let options = KVMap::new();
    for seed in PROPERTY_SEEDS {
        let declarations = seeded_declarations(seed);
        let baseline = build_declaration_environment(&declarations, &permutations[0]);
        let baseline_root = baseline.logical_root(&options);
        for permutation in &permutations[1..] {
            let permuted = build_declaration_environment(&declarations, permutation);
            assert_eq!(
                permuted.logical_root(&options),
                baseline_root,
                "independent declaration order changed logical root: seed={seed:#018x}, permutation={permutation:?}"
            );
            assert_eq!(
                permuted, baseline,
                "independent declaration order changed the observable environment: seed={seed:#018x}, permutation={permutation:?}"
            );
        }
    }
}

/// Exclusive MR: extension contributions form an append-only ordered journal. A
/// permutation must be visible in iteration order, the extension content digest, and
/// the enclosing environment root.
#[test]
fn extension_entry_contributions_preserve_ordered_identity() {
    let permutations = generated_permutations(ROW_COUNT);
    let options = KVMap::new();
    for seed in PROPERTY_SEEDS {
        let descriptor = extension_descriptor(seed);
        let payloads = seeded_payloads(seed);
        let baseline = build_extension_environment(&descriptor, &payloads, &permutations[0]);
        let baseline_state = baseline
            .extension(&descriptor.name)
            .expect("baseline extension exists");
        let baseline_digest = baseline_state.content_digest();
        let baseline_root = baseline.logical_root(&options);

        for permutation in &permutations[1..] {
            let permuted =
                build_extension_environment(&descriptor, &payloads, permutation.as_slice());
            let observed = extension_payloads(&permuted, &descriptor.name);
            let expected: Vec<Vec<u8>> = permutation
                .iter()
                .map(|&index| payloads[index].clone())
                .collect();
            assert_eq!(
                observed, expected,
                "extension replay order drifted: seed={seed:#018x}, permutation={permutation:?}"
            );
            let state = permuted
                .extension(&descriptor.name)
                .expect("permuted extension exists");
            assert_ne!(
                state.content_digest(),
                baseline_digest,
                "extension content digest lost order: seed={seed:#018x}, permutation={permutation:?}"
            );
            assert_ne!(
                permuted.logical_root(&options),
                baseline_root,
                "environment root lost extension order: seed={seed:#018x}, permutation={permutation:?}"
            );
        }
    }
}

/// Composite equivalence + inclusive/exclusive MR: each O(1) snapshot is
/// observationally equal to a from-scratch rebuild of its prefix, stays a strict
/// subset of later descendants, and remains unchanged after those descendants exist.
#[test]
fn snapshots_match_rebuilt_prefixes_and_isolate_later_mutations() {
    let permutations = generated_permutations(ROW_COUNT);
    let options = KVMap::new();
    for seed in PROPERTY_SEEDS {
        let declarations = seeded_declarations(seed);
        let descriptor = extension_descriptor(seed ^ 0x736e_6170_7368_6f74);
        let payloads = seeded_payloads(seed ^ 0x7265_6275_696c_645f);
        for permutation in &permutations {
            let mut descendant = Environment::new()
                .register_extension(descriptor.clone())
                .expect("fresh extension registers");
            let mut snapshots = Vec::new();
            snapshots.push(descendant.clone());
            for &index in permutation {
                descendant = descendant
                    .add_decl(declarations[index].clone())
                    .expect("generated declarations are independent");
                descendant = descendant
                    .push_extension_entry(&descriptor.name, payloads[index].clone())
                    .expect("registered extension accepts an entry");
                snapshots.push(descendant.clone());
            }

            for (prefix_len, snapshot) in snapshots.iter().enumerate() {
                let mut rebuilt = Environment::new()
                    .register_extension(descriptor.clone())
                    .expect("fresh extension registers");
                for &index in &permutation[..prefix_len] {
                    rebuilt = rebuilt
                        .add_decl(declarations[index].clone())
                        .expect("generated declarations are independent");
                    rebuilt = rebuilt
                        .push_extension_entry(&descriptor.name, payloads[index].clone())
                        .expect("registered extension accepts an entry");
                }
                assert_eq!(
                    snapshot, &rebuilt,
                    "snapshot differs from rebuilt prefix: seed={seed:#018x}, permutation={permutation:?}, prefix={prefix_len}"
                );
                assert_eq!(
                    snapshot.logical_root(&options),
                    rebuilt.logical_root(&options),
                    "snapshot root differs from rebuilt prefix: seed={seed:#018x}, permutation={permutation:?}, prefix={prefix_len}"
                );
                assert_eq!(
                    extension_payloads(snapshot, &descriptor.name),
                    extension_payloads(&rebuilt, &descriptor.name),
                    "snapshot extension differs from rebuilt prefix: seed={seed:#018x}, permutation={permutation:?}, prefix={prefix_len}"
                );
                for &omitted in &permutation[prefix_len..] {
                    assert!(
                        !snapshot.contains(declarations[omitted].name()),
                        "later declaration leaked into snapshot: seed={seed:#018x}, permutation={permutation:?}, prefix={prefix_len}, omitted={omitted}"
                    );
                }
            }

            assert_ne!(
                snapshots[0].logical_root(&options),
                descendant.logical_root(&options),
                "negative control: later mutations did not change the descendant root"
            );
        }
    }
}

/// Idempotent/equivalence MR: two independent decoders must produce exactly the
/// same canonical observation bytes for every pinned artifact in the fixed corpus.
#[test]
fn repeated_pinned_olean_decode_is_bit_identical() {
    for fixture_name in OLEAN_FIXTURES {
        let bytes = fixture_bytes(fixture_name);
        let first = decode_transcript(&bytes);
        assert!(
            first.is_ok(),
            "first decode failed for {fixture_name}: {}",
            first
                .as_ref()
                .expect_err("failed decode must include a typed error")
        );
        let first = first.expect("first decode was checked above");
        let second = decode_transcript(&bytes);
        assert!(
            second.is_ok(),
            "second decode failed for {fixture_name}: {}",
            second
                .as_ref()
                .expect_err("failed decode must include a typed error")
        );
        let second = second.expect("second decode was checked above");
        assert_eq!(
            first, second,
            "repeated decode bytes diverged for pinned fixture {fixture_name}"
        );
        assert!(
            !first.is_empty(),
            "decode transcript must bind observations"
        );
    }
}

/// Exclusive/totality MR: generated proper prefixes and critical-prefix
/// corruptions must produce typed errors. The work runs in a child copy of this test
/// binary so a panic, abort, or fatal signal is observed as a failed status by the
/// parent instead of destroying the conformance harness.
#[test]
fn truncated_and_corrupted_olean_prefixes_are_typed_total() {
    if std::env::var_os(OLEAN_CORRUPTION_CHILD).is_some() {
        exercise_corrupt_olean_inputs();
        return;
    }

    let executable = std::env::current_exe().expect("current integration-test executable");
    let output = Command::new(executable)
        .arg("--exact")
        .arg("truncated_and_corrupted_olean_prefixes_are_typed_total")
        .arg("--nocapture")
        .env(OLEAN_CORRUPTION_CHILD, "1")
        .output()
        .expect("spawn isolated olean corruption child");
    assert!(
        output.status.success(),
        "olean corruption child panicked, aborted, or was signalled: status={}; stdout={}; stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
