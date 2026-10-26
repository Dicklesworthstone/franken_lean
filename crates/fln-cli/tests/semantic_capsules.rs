//! Real process boundaries for sealed declaration checking. Every fixture is
//! serialized untrusted input; the producer and verifier each run both checkers.
#![forbid(unsafe_code)]

use fln::{
    BinderInfo, ConstantInfo, ConstantVal, Expr, Level, Name, OleanModuleImport,
    OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader, TheoremVal,
};
use fln_hash::cartridge::{
    CartridgeArchiveV1, CartridgeBuilderV1, CartridgeObjectIdV1, CartridgeObjectKindV1,
    ObjectPortabilityV1, ObjectRequirementV1,
};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        let root = std::env::var_os("CARGO_TARGET_TMPDIR")
            .map(PathBuf::from)
            .unwrap_or_else(std::env::temp_dir)
            .join(format!(
                "fln-cli-semantic-capsules-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
        std::fs::create_dir_all(root.join("modules")).unwrap();
        std::fs::create_dir(root.join("isolated")).unwrap();
        Self(root)
    }

    fn write(&self, relative: &str, bytes: impl AsRef<[u8]>) {
        std::fs::write(self.0.join(relative), bytes).unwrap();
    }

    fn capsule(&self) -> PathBuf {
        self.0.join("proofs.flnpack")
    }

    fn seal(&self, extra: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["seal-capsule", "--json"])
            .args(extra)
            .arg("--output")
            .arg(self.capsule())
            .arg(self.0.join("modules"))
            .output()
            .unwrap()
    }

    fn verify(&self, extra: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["verify-capsule", "--json"])
            .args(extra)
            .arg(self.capsule())
            .current_dir(self.0.join("isolated"))
            .env("LEAN_PATH", self.0.join("isolated"))
            .output()
            .unwrap()
    }
}

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

/// A universe-polymorphic theorem with dependent local types; the forged
/// variant replaces its hypothesis proof by a value of the unrelated type A.
fn generic_theorem(name: &str, forged: bool) -> ConstantInfo {
    let binders = [
        (
            n("A"),
            Expr::sort(Level::param(n("u"))),
            BinderInfo::Implicit,
        ),
        (
            n("P"),
            Expr::forall_e(n("x"), b(0), Expr::sort(Level::zero()), BinderInfo::Default),
            BinderInfo::Default,
        ),
        (n("a"), b(1), BinderInfo::Default),
        (n("h"), Expr::app(b(1), b(0)), BinderInfo::Default),
    ];
    let mut type_ = Expr::app(b(2), b(1));
    let mut value = b(u32::from(forged));
    for (name, domain, style) in binders.into_iter().rev() {
        type_ = Expr::forall_e(name.clone(), domain.clone(), type_, style);
        value = Expr::lam(name, domain, value, style);
    }
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![n("u")],
            type_,
        },
        value,
        all: vec![n(name)],
    })
}

fn encoded(
    constants: &[ConstantInfo],
    imports: &[&str],
    module_system: bool,
    region: u64,
) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| OleanModuleImport {
            module: n(name),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    fln::encode_olean_module(
        OleanModuleWriteInput {
            is_module: module_system,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: region * fln::OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
}

fn fixture() -> Project {
    let project = Project::new();
    project.write(
        "modules/Base.olean",
        encoded(&[generic_theorem("Base.keep", false)], &[], false, 2),
    );
    let ConstantInfo::Thm(mut child) = generic_theorem("Main.keep", false) else {
        unreachable!()
    };
    child.value = Expr::const_(n("Base.keep"), vec![Level::param(n("u"))]);
    project.write(
        "modules/Main.olean",
        encoded(&[ConstantInfo::Thm(child)], &["Base"], false, 2),
    );
    project
}

fn success(output: Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let text = String::from_utf8(output.stdout).unwrap();
    assert_eq!(text.lines().count(), 1, "{text}");
    assert!(text.contains("\"outcome\":\"complete\""), "{text}");
    text
}

fn failure(output: Output, code: i32) -> String {
    assert_eq!(output.status.code(), Some(code), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let text = String::from_utf8(output.stderr).unwrap();
    assert_eq!(text.lines().count(), 1, "{text}");
    assert!(text.contains("\"outcome\":\"error\""), "{text}");
    text
}

fn field<'a>(json: &'a str, name: &str) -> &'a str {
    let marker = format!("\"{name}\":\"");
    json.split_once(&marker)
        .unwrap_or_else(|| panic!("missing {name}: {json}"))
        .1
        .split_once('"')
        .unwrap()
        .0
}

#[test]
fn seals_and_rechecks_a_generic_module_graph_in_a_fresh_process() {
    let project = fixture();
    let sealed = success(project.seal(&[]));
    assert!(sealed.contains("\"status\":\"sealed\""), "{sealed}");
    assert!(sealed.contains("\"modules_verified\":2"), "{sealed}");
    assert!(sealed.contains("\"declarations_verified\":2"), "{sealed}");
    // Verification must use the sealed bytes even when the original files
    // have changed. The new process runs in an empty import search directory.
    project.write("modules/Base.olean", b"the original input is now corrupt");
    let verified = success(project.verify(&["--require-semantic"]));
    assert!(
        verified.contains("\"status\":\"declarations_verified\""),
        "{verified}"
    );
    assert!(
        verified.contains("\"verification_method\":\"full_recomputation\""),
        "{verified}"
    );
    assert!(
        verified.contains("\"declarations_verified\":2"),
        "{verified}"
    );
    for name in [
        "manifest_root",
        "archive_digest",
        "base_logical_root",
        "result_logical_root",
    ] {
        assert_eq!(field(&sealed, name), field(&verified, name), "{name}");
    }
}

#[test]
fn complete_module_system_companions_are_inside_the_capsule() {
    let project = Project::new();
    project.write("modules/Main.olean", encoded(&[], &[], true, 2));
    project.write("modules/Main.olean.server", encoded(&[], &[], true, 4));
    project.write(
        "modules/Main.olean.private",
        encoded(&[generic_theorem("Main.privateKeep", false)], &[], true, 6),
    );
    let sealed = success(project.seal(&[]));
    assert!(sealed.contains("\"declarations_verified\":1"), "{sealed}");
    project.write("modules/Main.olean.private", b"corrupt after sealing");
    let verified = success(project.verify(&["--require-semantic"]));
    assert!(
        verified.contains("\"declarations_verified\":1"),
        "{verified}"
    );
}

#[test]
fn missing_imports_and_companions_do_not_replace_an_existing_capsule() {
    for companion in [false, true] {
        let project = Project::new();
        project.write("proofs.flnpack", b"previous complete output");
        project.write(
            "modules/Main.olean",
            encoded(
                &[],
                if companion { &[] } else { &["Missing"] },
                companion,
                2,
            ),
        );
        if companion {
            project.write("modules/Main.olean.server", encoded(&[], &[], true, 4));
        }
        let rejected = failure(project.seal(&[]), 1);
        assert!(
            !rejected.contains("\"class\":\"internal_fault\""),
            "{rejected}"
        );
        assert_eq!(
            std::fs::read(project.capsule()).unwrap(),
            b"previous complete output"
        );
    }
}

#[test]
fn an_invalid_proof_and_resource_exhaustion_publish_no_output() {
    let project = Project::new();
    project.write(
        "modules/Main.olean",
        encoded(&[generic_theorem("Main.keep", true)], &[], false, 2),
    );
    let rejected = failure(project.seal(&[]), 1);
    assert!(
        rejected.contains("\"class\":\"kernel-rejection\""),
        "{rejected}"
    );
    assert!(rejected.contains("\"authority\":true"), "{rejected}");
    assert!(!project.capsule().exists());
    let bounded = fixture();
    let exhausted = failure(bounded.seal(&["--max-bytes", "0"]), 3);
    assert!(exhausted.contains("\"class\":\"resource\""), "{exhausted}");
    assert!(!bounded.capsule().exists());
    success(bounded.seal(&[]));
    failure(bounded.verify(&["--max-bytes", "0"]), 3);
}

fn archive(path: &Path) -> CartridgeArchiveV1 {
    CartridgeArchiveV1::from_canonical_bytes(&std::fs::read(path).unwrap())
        .into_complete()
        .unwrap()
        .unwrap()
}

/// Reseal every changed object, chunk, root receipt, and attachment. This
/// models an attacker controlling the container, not a mere damaged checksum.
fn repack(
    archive: &CartridgeArchiveV1,
    mut change: impl FnMut(CartridgeObjectKindV1, Vec<u8>) -> Vec<u8>,
) -> Vec<u8> {
    let mut builder =
        CartridgeBuilderV1::new(archive.manifest.epoch, archive.manifest.environment_root);
    let mut replacements = BTreeMap::<CartridgeObjectIdV1, CartridgeObjectIdV1>::new();
    for receipt in [false, true] {
        for object in &archive.manifest.objects {
            if (object.kind == CartridgeObjectKindV1::Receipt) != receipt {
                continue;
            }
            let mut bytes = archive
                .assemble_object(object.id, 64 * 1024 * 1024)
                .into_complete()
                .unwrap()
                .unwrap()
                .unwrap();
            if receipt {
                for (old, new) in &replacements {
                    if old != new {
                        let matches: Vec<_> = bytes
                            .windows(32)
                            .enumerate()
                            .filter_map(|(index, bytes)| (bytes == old.digest().0).then_some(index))
                            .collect();
                        assert_eq!(
                            matches.len(),
                            1,
                            "profile binds each module object exactly once"
                        );
                        bytes[matches[0]..matches[0] + 32].copy_from_slice(&new.digest().0);
                    }
                }
            }
            let bytes = change(object.kind, bytes);
            let new = builder.add_object(
                object.kind,
                object.requirement,
                object.portability.clone(),
                bytes,
            );
            replacements.insert(object.id, new);
            if archive.manifest.root_receipts.contains(&object.id) {
                builder.add_root_receipt(new);
            }
        }
    }
    for attachment in &archive.manifest.attachments {
        builder.attach(
            replacements[&attachment.receipt],
            attachment.role,
            replacements[&attachment.object],
        );
    }
    for extension in &archive.manifest.extensions {
        builder.add_extension(extension.clone());
    }
    builder.build().unwrap().to_canonical_bytes().unwrap()
}

#[test]
fn a_resealed_false_proof_reaches_the_checker_and_is_rejected() {
    let project = fixture();
    success(project.seal(&[]));
    let original = std::fs::read(project.0.join("modules/Base.olean")).unwrap();
    let forged = encoded(&[generic_theorem("Base.keep", true)], &[], false, 2);
    let mut changed = 0;
    let forged_capsule = repack(&archive(&project.capsule()), |_, bytes| {
        if bytes == original {
            changed += 1;
            forged.clone()
        } else {
            bytes
        }
    });
    assert_eq!(changed, 1);
    project.write("proofs.flnpack", forged_capsule);
    let rejected = failure(project.verify(&[]), 1);
    assert!(
        rejected.contains("\"class\":\"kernel-rejection\""),
        "{rejected}"
    );
    assert!(rejected.contains("\"authority\":true"), "{rejected}");
    assert!(!rejected.contains("integrity_only"), "{rejected}");
}

#[test]
fn an_unknown_semantic_profile_version_cannot_downgrade_to_integrity() {
    let project = fixture();
    success(project.seal(&[]));
    let mut prefix = fln_hash::canon::CanonWriter::new();
    prefix.schema(fln::capsule::SCHEMA_OLEAN_CAPSULE);
    let prefix = prefix.into_bytes();
    let mut changed = 0;
    let bytes = repack(&archive(&project.capsule()), |kind, mut bytes| {
        if kind == CartridgeObjectKindV1::Receipt && bytes.starts_with(&prefix) {
            changed += 1;
            let version = prefix.len() - 2;
            bytes[version..version + 2].copy_from_slice(&u16::MAX.to_le_bytes());
        }
        bytes
    });
    assert_eq!(changed, 1);
    project.write("proofs.flnpack", bytes);
    let output = project.verify(&[]);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("version"), "{stderr}");
    assert!(!stderr.contains("integrity_verified"), "{stderr}");
}

#[test]
fn legacy_integrity_remains_explicit_and_semantic_requirement_refuses_it() {
    let project = Project::new();
    let mut builder =
        CartridgeBuilderV1::new(fln::capsule::PINNED_EPOCH, fln::ContentRoot::new([1; 32]));
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"legacy receipt".to_vec(),
    );
    builder.add_root_receipt(receipt);
    project.write(
        "proofs.flnpack",
        builder.build().unwrap().to_canonical_bytes().unwrap(),
    );
    let integrity = success(project.verify(&[]));
    assert!(
        integrity.contains("\"verification_method\":\"integrity_only\""),
        "{integrity}"
    );
    assert!(
        integrity.contains("\"declarations_verified\":0"),
        "{integrity}"
    );
    let refused = failure(project.verify(&["--require-semantic"]), 1);
    assert!(
        refused.contains("semantic verification was required"),
        "{refused}"
    );
}
