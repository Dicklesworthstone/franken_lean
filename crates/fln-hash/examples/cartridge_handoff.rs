//! Filesystem driver for the W3 certificate-cartridge handoff.
//!
//! This is a transport exerciser, not an admission surface. `verify` checks canonical
//! structure, content identities, random access, nested certificate/cache codecs, and
//! completeness; it never returns a kernel verdict or publishes a declaration.

#![forbid(unsafe_code)]

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::canon::DecodeBudget;
use fln_hash::cartridge::{
    AttachmentRoleV1, CartridgeArchiveV1, CartridgeBuilderV1, CartridgeDecodeBudgetsV1,
    CartridgeExtensionV1, CartridgeIndexV1, CartridgeObjectKindV1, CartridgeStreamDecoderV1,
    CartridgeTransportStateV1, DefeqTransparencyV1, ObjectPortabilityV1, ObjectRequirementV1,
    WarmDefeqBindingV1, WarmDefeqCacheV1, WarmDefeqEntryV1, WarmDefeqQueryV1,
};
use fln_hash::certificate::{
    CertificateBindingV1, CertificateExtensionV1, CertificateJudgmentV1, ClaimedResultV1,
    ConsensusPolicyV1, DeclarationCertificateV1, DeclarationKindV1, FuelProfileV1, TermDagV1,
    TermNodeId, TermNodeV1,
};
use fln_hash::domain::{Digest, Domain, hash};

const OUTPUT_SCHEMA: &str = "fln.cartridge-handoff/1";
const MAX_FILE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_DECODE_NODES: u64 = 4 * 1024 * 1024;
const STREAM_CHUNK_BYTES: usize = 8191;

fn main() -> ExitCode {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    if arguments.is_empty() {
        usage();
        return ExitCode::from(2);
    }
    match dispatch(&arguments) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("cartridge_handoff: {error}");
            ExitCode::FAILURE
        }
    }
}

fn usage() {
    eprintln!(
        "usage:\n\
         cartridge_handoff make-certificate <output> <epoch-u128> <declaration> <dependency>\n\
         cartridge_handoff pack <output> <epoch-u128> <receipt> <certificate> <declaration> \
         <dependency> <fixture> <schema> <resource-contract> <witness>\n\
         cartridge_handoff inspect <archive>\n\
         cartridge_handoff verify <archive>\n\
         cartridge_handoff project <thin|partial|sealed|complete> <source> <output>\n\
         cartridge_handoff extract <archive> <fresh-directory>"
    );
}

fn dispatch(arguments: &[String]) -> Result<(), String> {
    match arguments {
        [command, output, epoch, declaration, dependency] if command == "make-certificate" => {
            make_certificate(
                Path::new(output),
                parse_epoch(epoch)?,
                Path::new(declaration),
                Path::new(dependency),
            )
        }
        [
            command,
            output,
            epoch,
            receipt,
            certificate,
            declaration,
            dependency,
            fixture,
            schema,
            resource_contract,
            witness,
        ] if command == "pack" => pack(
            Path::new(output),
            parse_epoch(epoch)?,
            PackInputs {
                receipt: Path::new(receipt),
                certificate: Path::new(certificate),
                declaration: Path::new(declaration),
                dependency: Path::new(dependency),
                fixture: Path::new(fixture),
                schema: Path::new(schema),
                resource_contract: Path::new(resource_contract),
                witness: Path::new(witness),
            },
        ),
        [command, archive] if command == "inspect" => inspect(Path::new(archive)),
        [command, archive] if command == "verify" => verify(Path::new(archive)),
        [command, state, source, output] if command == "project" => {
            project(state, Path::new(source), Path::new(output))
        }
        [command, archive, directory] if command == "extract" => {
            extract(Path::new(archive), Path::new(directory))
        }
        _ => {
            usage();
            Err("invalid arguments".to_string())
        }
    }
}

fn parse_epoch(value: &str) -> Result<EpochId, String> {
    value
        .parse::<u128>()
        .map(EpochId::new)
        .map_err(|error| format!("invalid epoch {value:?}: {error}"))
}

fn read_bounded(file: &Path) -> Result<Vec<u8>, String> {
    let link_metadata = fs::symlink_metadata(file)
        .map_err(|error| format!("inspect {}: {error}", file.display()))?;
    if link_metadata.file_type().is_symlink() || !link_metadata.is_file() {
        return Err(format!(
            "input is not one real regular file: {}",
            file.display()
        ));
    }
    if link_metadata.len() > MAX_FILE_BYTES {
        return Err(format!(
            "input exceeds the {MAX_FILE_BYTES}-byte handoff limit: {}",
            file.display()
        ));
    }
    fs::read(file).map_err(|error| format!("read {}: {error}", file.display()))
}

fn write_new(file: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut handle = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(file)
        .map_err(|error| format!("create {} without overwrite: {error}", file.display()))?;
    handle
        .write_all(bytes)
        .map_err(|error| format!("write {}: {error}", file.display()))?;
    handle
        .sync_all()
        .map_err(|error| format!("sync {}: {error}", file.display()))
}

fn content_root(domain: Domain, bytes: &[u8]) -> ContentRoot {
    ContentRoot::new(hash(domain, bytes).0)
}

fn joined_environment_root(declaration: &[u8], dependency: &[u8]) -> ContentRoot {
    let declaration = hash(Domain::DeclContent, declaration);
    let dependency = hash(Domain::DeclContent, dependency);
    let mut joined = [0u8; 64];
    joined[..32].copy_from_slice(&declaration.0);
    joined[32..].copy_from_slice(&dependency.0);
    content_root(Domain::LogicalRoot, &joined)
}

fn complete<T, E>(outcome: Outcome<Result<T, E>>, context: &str) -> Result<T, String>
where
    T: std::fmt::Debug,
    E: std::fmt::Debug,
{
    match outcome {
        Outcome::Complete(Ok(value)) => Ok(value),
        Outcome::Complete(Err(error)) => Err(format!("{context} refused: {error:?}")),
        Outcome::Inconclusive(stop) => Err(format!("{context} inconclusive: {stop:?}")),
        Outcome::InternalFault(fault) => Err(format!("{context} internal fault: {fault:?}")),
    }
}

fn make_certificate(
    output: &Path,
    epoch: EpochId,
    declaration_path: &Path,
    dependency_path: &Path,
) -> Result<(), String> {
    let declaration = read_bounded(declaration_path)?;
    let dependency = read_bounded(dependency_path)?;
    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(0),
            },
        ],
    };
    let certificate = DeclarationCertificateV1::new(
        CertificateBindingV1 {
            epoch,
            mode: Mode::Sound,
            reproducibility: ReproducibilityProfile::Certified,
            build_profile: BuildProfileId::new(1),
            consensus_policy: ConsensusPolicyV1::Paranoid,
            environment_root: joined_environment_root(&declaration, &dependency),
            dependency_roots: vec![content_root(Domain::DeclContent, &dependency)],
            declaration_root: content_root(Domain::DeclContent, &declaration),
            term_root: term_dag.content_root(),
            kernel_build_root: content_root(Domain::Receipt, b"fln-kernel-cartridge-handoff-v1"),
            checker_build_root: content_root(Domain::Receipt, b"fln-checker-cartridge-handoff-v1"),
            policy_root: content_root(Domain::Receipt, b"fln-cartridge-policy-v1"),
            engine_id: "fln-cartridge-handoff".to_string(),
            engine_version: 1,
            fuel: FuelProfileV1 {
                profile_id: 1,
                heartbeats: 1_000_000,
                recursion_depth: 100_000,
                reduction_steps: 1_000_000,
                expanded_weight: 4_000_000,
                allocation_bytes: MAX_FILE_BYTES,
            },
        },
        CertificateJudgmentV1::CheckDeclaration {
            name: Name::from_components(["CertificateWitness", "certificate_witness_add_zero"]),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(1)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        Vec::new(),
        vec![CertificateExtensionV1::advisory(
            1,
            hash(Domain::Receipt, &dependency).0.to_vec(),
        )],
    )
    .map_err(|error| format!("construct candidate certificate: {error:?}"))?;
    let bytes = certificate
        .to_canonical_bytes()
        .map_err(|error| format!("encode candidate certificate: {error:?}"))?;
    write_new(output, &bytes)?;
    println!(
        "{{\"authority\":false,\"bytes\":{},\"certificate_digest\":\"{}\",\
         \"schema\":\"{OUTPUT_SCHEMA}\"}}",
        bytes.len(),
        certificate
            .digest()
            .map_err(|error| format!("digest candidate certificate: {error:?}"))?
    );
    Ok(())
}

struct PackInputs<'a> {
    receipt: &'a Path,
    certificate: &'a Path,
    declaration: &'a Path,
    dependency: &'a Path,
    fixture: &'a Path,
    schema: &'a Path,
    resource_contract: &'a Path,
    witness: &'a Path,
}

fn pack(output: &Path, epoch: EpochId, inputs: PackInputs<'_>) -> Result<(), String> {
    let receipt_bytes = read_bounded(inputs.receipt)?;
    let certificate_bytes = read_bounded(inputs.certificate)?;
    let declaration_bytes = read_bounded(inputs.declaration)?;
    let dependency_bytes = read_bounded(inputs.dependency)?;
    let fixture_bytes = read_bounded(inputs.fixture)?;
    let schema_bytes = read_bounded(inputs.schema)?;
    let resource_contract_bytes = read_bounded(inputs.resource_contract)?;
    let witness_bytes = read_bounded(inputs.witness)?;
    let environment_root = joined_environment_root(&declaration_bytes, &dependency_bytes);

    let mut builder = CartridgeBuilderV1::new(epoch, environment_root)
        .with_chunk_size(16 * 1024)
        .map_err(|error| format!("set cartridge chunk size: {error:?}"))?;
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        receipt_bytes,
    );
    let certificate = builder.add_object(
        CartridgeObjectKindV1::Certificate,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        certificate_bytes.clone(),
    );
    builder.add_object(
        CartridgeObjectKindV1::Declaration,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        declaration_bytes.clone(),
    );
    let dependency = builder.add_object(
        CartridgeObjectKindV1::Dependency,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        dependency_bytes.clone(),
    );
    let fixture = builder.add_object(
        CartridgeObjectKindV1::Fixture,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::EpochBound,
        fixture_bytes,
    );
    let schema = builder.add_object(
        CartridgeObjectKindV1::Schema,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::Portable,
        schema_bytes,
    );
    let resource_contract = builder.add_object(
        CartridgeObjectKindV1::ResourceContract,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::Portable,
        resource_contract_bytes.clone(),
    );
    let witness = builder.add_object(
        CartridgeObjectKindV1::Witness,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::EpochBound,
        witness_bytes,
    );
    let warm_cache = WarmDefeqCacheV1::new(
        WarmDefeqBindingV1 {
            receipt_object: receipt,
            certificate_object: certificate,
            epoch,
            mode: Mode::Sound,
            environment_root,
            kernel_build_root: content_root(Domain::Receipt, b"fln-kernel-cartridge-handoff-v1"),
            checker_build_root: content_root(Domain::Receipt, b"fln-checker-cartridge-handoff-v1"),
            policy_root: content_root(Domain::Receipt, b"fln-cartridge-policy-v1"),
            fuel_profile_root: content_root(Domain::Receipt, &resource_contract_bytes),
        },
        vec![WarmDefeqEntryV1 {
            query: WarmDefeqQueryV1 {
                left_term_root: content_root(Domain::Receipt, &declaration_bytes),
                right_term_root: content_root(Domain::Receipt, &dependency_bytes),
                expected_type_root: Some(content_root(Domain::Receipt, &certificate_bytes)),
                transparency: DefeqTransparencyV1::Semireducible,
            },
            normal_form_root: content_root(Domain::Receipt, b"cartridge-handoff-normal-form"),
            left_trace: vec![
                content_root(Domain::Receipt, &declaration_bytes),
                content_root(Domain::Receipt, b"cartridge-handoff-normal-form"),
            ],
            right_trace: vec![
                content_root(Domain::Receipt, &dependency_bytes),
                content_root(Domain::Receipt, b"cartridge-handoff-normal-form"),
            ],
        }],
        vec![CartridgeExtensionV1::advisory(
            1,
            b"oq13-replay-hints-only".to_vec(),
        )],
    )
    .map_err(|error| format!("construct warm cache: {error:?}"))?;
    let warm_cache = builder.add_object(
        CartridgeObjectKindV1::WarmDefeqCache,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::EpochBound,
        warm_cache
            .to_canonical_bytes()
            .map_err(|error| format!("encode warm cache: {error:?}"))?,
    );

    builder.add_root_receipt(receipt);
    for (role, object) in [
        (AttachmentRoleV1::Certificate, certificate),
        (AttachmentRoleV1::Dependency, dependency),
        (AttachmentRoleV1::Fixture, fixture),
        (AttachmentRoleV1::Schema, schema),
        (AttachmentRoleV1::ResourceContract, resource_contract),
        (AttachmentRoleV1::Witness, witness),
        (AttachmentRoleV1::WarmDefeqCache, warm_cache),
    ] {
        builder.attach(receipt, role, object);
    }
    builder.add_extension(CartridgeExtensionV1::advisory(
        1,
        b"sealed-handoff-v1".to_vec(),
    ));
    let archive = builder
        .build()
        .map_err(|error| format!("build cartridge: {error:?}"))?;
    let bytes = archive
        .to_canonical_bytes()
        .map_err(|error| format!("encode cartridge: {error:?}"))?;
    write_new(output, &bytes)?;
    print_summary(
        &archive,
        Some(
            archive
                .archive_digest()
                .map_err(|error| format!("digest cartridge: {error:?}"))?,
        ),
    );
    Ok(())
}

fn decode_archive(bytes: &[u8]) -> Result<CartridgeArchiveV1, String> {
    let mut decoder = CartridgeStreamDecoderV1::new(MAX_FILE_BYTES);
    for chunk in bytes.chunks(STREAM_CHUNK_BYTES) {
        complete(decoder.push(chunk), "stream cartridge bytes")?;
    }
    complete(
        decoder.finish(CartridgeDecodeBudgetsV1 {
            archive: DecodeBudget::new(bytes.len() as u64, MAX_DECODE_NODES),
            manifest: DecodeBudget::new(bytes.len() as u64, MAX_DECODE_NODES),
        }),
        "decode cartridge",
    )
}

fn load_archive(file: &Path) -> Result<(Vec<u8>, CartridgeArchiveV1), String> {
    let bytes = read_bounded(file)?;
    let archive = decode_archive(&bytes)?;
    Ok((bytes, archive))
}

fn inspect(file: &Path) -> Result<(), String> {
    let (_, archive) = load_archive(file)?;
    print_summary(&archive, None);
    Ok(())
}

fn validate_complete(bytes: &[u8], archive: &CartridgeArchiveV1) -> Result<usize, String> {
    if archive.transport_state() != CartridgeTransportStateV1::Complete {
        return Err(format!(
            "transport is not complete: {:?}",
            archive.transport_state()
        ));
    }
    let index = complete(
        CartridgeIndexV1::from_canonical_bytes(
            bytes,
            CartridgeDecodeBudgetsV1 {
                archive: DecodeBudget::new(bytes.len() as u64, MAX_DECODE_NODES),
                manifest: DecodeBudget::new(bytes.len() as u64, MAX_DECODE_NODES),
            },
        ),
        "derive cartridge random-access index",
    )?;
    if index.manifest_root
        != archive
            .manifest_root()
            .map_err(|error| format!("derive manifest root: {error:?}"))?
        || index.chunks.len() != archive.frames.len()
    {
        return Err("derived index does not cover the archive".to_string());
    }
    for frame in &archive.frames {
        let indexed = index
            .read_chunk(bytes, frame.id)
            .map_err(|error| format!("read indexed frame: {error:?}"))?;
        if indexed != frame.bytes {
            return Err("random-access bytes differ from the canonical frame".to_string());
        }
    }

    for object in &archive.manifest.objects {
        let object_bytes = archive
            .assemble_object(object.id)
            .map_err(|error| format!("assemble {:?} object: {error:?}", object.kind))?
            .ok_or_else(|| format!("complete transport lacks {:?} bytes", object.kind))?;
        if object.kind == CartridgeObjectKindV1::Certificate {
            complete(
                DeclarationCertificateV1::from_canonical_bytes_budgeted(
                    &object_bytes,
                    DecodeBudget::new(object_bytes.len() as u64, MAX_DECODE_NODES),
                ),
                "decode nested declaration certificate",
            )?;
        }
    }
    let report = complete(
        archive
            .validate_present_warm_caches(DecodeBudget::new(bytes.len() as u64, MAX_DECODE_NODES)),
        "validate present warm caches",
    )?;
    if report.missing != 0 {
        return Err("complete cartridge reports a missing warm-cache attachment".to_string());
    }
    Ok(report.validated)
}

fn verify(file: &Path) -> Result<(), String> {
    let (bytes, archive) = load_archive(file)?;
    let warm_caches = validate_complete(&bytes, &archive)?;
    let archive_digest = archive
        .archive_digest()
        .map_err(|error| format!("derive archive digest: {error:?}"))?;
    let manifest_root = archive
        .manifest_root()
        .map_err(|error| format!("derive manifest root: {error:?}"))?;
    println!(
        "{{\"archive_digest\":\"{archive_digest}\",\"authority\":false,\
         \"frames\":{},\"manifest_root\":\"{}\",\"objects\":{},\
         \"schema\":\"{OUTPUT_SCHEMA}\",\"state\":\"complete\",\"warm_caches\":{warm_caches}}}",
        archive.frames.len(),
        hex_root(manifest_root),
        archive.manifest.objects.len(),
    );
    Ok(())
}

fn project(state: &str, source: &Path, output: &Path) -> Result<(), String> {
    let (_, archive) = load_archive(source)?;
    let required = archive.manifest.required_chunk_ids();
    let frames = match state {
        "thin" => Vec::new(),
        "sealed" => archive
            .frames
            .iter()
            .filter(|frame| required.contains(&frame.id))
            .cloned()
            .collect(),
        "partial" => {
            let mut frames = archive
                .frames
                .iter()
                .filter(|frame| required.contains(&frame.id))
                .cloned()
                .collect::<Vec<_>>();
            frames
                .pop()
                .ok_or_else(|| "no required frame is available to omit".to_string())?;
            frames
        }
        "complete" => archive.frames.clone(),
        _ => return Err(format!("unknown projection state {state:?}")),
    };
    let projected = CartridgeArchiveV1::new(archive.manifest, frames)
        .map_err(|error| format!("construct {state} projection: {error:?}"))?;
    let bytes = projected
        .to_canonical_bytes()
        .map_err(|error| format!("encode {state} projection: {error:?}"))?;
    write_new(output, &bytes)?;
    print_summary(&projected, None);
    Ok(())
}

fn extract(file: &Path, directory: &Path) -> Result<(), String> {
    let (bytes, archive) = load_archive(file)?;
    let warm_caches = validate_complete(&bytes, &archive)?;
    fs::create_dir(directory)
        .map_err(|error| format!("create fresh extraction {}: {error}", directory.display()))?;
    write_new(
        &directory.join("manifest.bin"),
        &archive
            .manifest
            .to_canonical_bytes()
            .map_err(|error| format!("encode extracted manifest: {error:?}"))?,
    )?;
    for (index, object) in archive.manifest.objects.iter().enumerate() {
        let object_bytes = archive
            .assemble_object(object.id)
            .map_err(|error| format!("assemble {:?} object: {error:?}", object.kind))?
            .ok_or_else(|| format!("complete transport lacks {:?} bytes", object.kind))?;
        let name = format!(
            "{index:02}-{}-{}.bin",
            kind_name(object.kind),
            object.id.digest()
        );
        write_new(&directory.join(name), &object_bytes)?;
    }
    println!(
        "{{\"files\":{},\"objects\":{},\"schema\":\"{OUTPUT_SCHEMA}\",\
         \"state\":\"extracted\",\"warm_caches\":{warm_caches}}}",
        archive.manifest.objects.len() + 1,
        archive.manifest.objects.len(),
    );
    Ok(())
}

fn print_summary(archive: &CartridgeArchiveV1, digest: Option<Digest>) {
    let state = archive.transport_state();
    let (state_name, missing_required, missing_optional) = match &state {
        CartridgeTransportStateV1::Thin => ("thin", archive.manifest.required_chunk_ids().len(), 0),
        CartridgeTransportStateV1::Partial { missing_required } => {
            ("partial", missing_required.len(), 0)
        }
        CartridgeTransportStateV1::Sealed { missing_optional } => {
            ("sealed", 0, missing_optional.len())
        }
        CartridgeTransportStateV1::Complete => ("complete", 0, 0),
    };
    let root = archive
        .manifest_root()
        .expect("validated archive has a canonical manifest");
    if let Some(digest) = digest {
        println!(
            "{{\"archive_digest\":\"{digest}\",\"authority\":false,\"frames\":{},\
             \"manifest_root\":\"{}\",\"missing_optional\":{missing_optional},\
             \"missing_required\":{missing_required},\"objects\":{},\
             \"schema\":\"{OUTPUT_SCHEMA}\",\"state\":\"{state_name}\"}}",
            archive.frames.len(),
            hex_root(root),
            archive.manifest.objects.len(),
        );
    } else {
        println!(
            "{{\"authority\":false,\"frames\":{},\"manifest_root\":\"{}\",\
             \"missing_optional\":{missing_optional},\"missing_required\":{missing_required},\
             \"objects\":{},\"schema\":\"{OUTPUT_SCHEMA}\",\"state\":\"{state_name}\"}}",
            archive.frames.len(),
            hex_root(root),
            archive.manifest.objects.len(),
        );
    }
}

fn kind_name(kind: CartridgeObjectKindV1) -> &'static str {
    match kind {
        CartridgeObjectKindV1::Declaration => "declaration",
        CartridgeObjectKindV1::Dependency => "dependency",
        CartridgeObjectKindV1::Receipt => "receipt",
        CartridgeObjectKindV1::Certificate => "certificate",
        CartridgeObjectKindV1::Fixture => "fixture",
        CartridgeObjectKindV1::Schema => "schema",
        CartridgeObjectKindV1::ResourceContract => "resource-contract",
        CartridgeObjectKindV1::Witness => "witness",
        CartridgeObjectKindV1::WarmDefeqCache => "warm-defeq-cache",
    }
}

fn hex_root(root: Digest) -> String {
    root.to_hex()
}
