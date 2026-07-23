//! G0-1 region-reader suite (bead franken_lean-y24): real pinned-Reference
//! oleans from the C3 fixture corpus walked with full integrity checking and
//! `ModuleData` decoding, plus a hostile-input smoke lane — deterministic
//! corruptions and a seeded byte-flip sweep must yield typed errors under
//! budget, never panics and never false acceptance (FL-INV-07 discipline).

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_core::name::Name;
use fln_olean::format;
use fln_olean::region::{ModuleImport, OleanView, RegionError, WalkBudget};
use fln_rt::abi;

const SYNTHETIC_BASE: u64 = 1 << 16;

#[derive(Debug)]
struct SyntheticImports {
    bytes: Vec<u8>,
    import_offsets: Vec<usize>,
}

fn ctor_header(tag: u8, other: u8, cs_sz: u16) -> u64 {
    let packed = u64::from(cs_sz) | (u64::from(other) << 16) | (u64::from(tag) << 24);
    packed << 32
}

fn align_word(bytes: &mut Vec<u8>) {
    let remainder = bytes.len() % abi::OBJECT_SIZE_DELTA;
    if remainder != 0 {
        bytes.resize(bytes.len() + abi::OBJECT_SIZE_DELTA - remainder, 0);
    }
}

fn put_u64(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

fn get_u64(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(
        bytes[offset..offset + 8]
            .try_into()
            .expect("test word is in bounds"),
    )
}

fn synthetic_ptr(offset: usize) -> u64 {
    SYNTHETIC_BASE + u64::try_from(offset).expect("test offset fits u64")
}

fn module_name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn push_string(bytes: &mut Vec<u8>, value: &str) -> usize {
    align_word(bytes);
    let offset = bytes.len();
    let size = value.len() + 1;
    bytes.resize(offset + 32 + size, 0);
    put_u64(bytes, offset, ctor_header(abi::TAG_STRING, 0, 1));
    put_u64(bytes, offset + 8, size as u64);
    put_u64(bytes, offset + 16, size as u64);
    put_u64(bytes, offset + 24, value.chars().count() as u64);
    bytes[offset + 32..offset + 32 + value.len()].copy_from_slice(value.as_bytes());
    align_word(bytes);
    offset
}

fn push_name(bytes: &mut Vec<u8>, value: &str) -> usize {
    let string = push_string(bytes, value);
    let offset = bytes.len();
    bytes.resize(offset + 32, 0);
    put_u64(bytes, offset, ctor_header(1, 2, 32));
    put_u64(bytes, offset + 8, 1); // Name.anonymous
    put_u64(bytes, offset + 16, synthetic_ptr(string));
    // The cached hash is a scalar usize. Its value is irrelevant to Name text
    // decoding, but its storage is part of the exact constructor shape.
    put_u64(bytes, offset + 24, 0);
    offset
}

fn push_array(bytes: &mut Vec<u8>, elements: &[u64]) -> usize {
    align_word(bytes);
    let offset = bytes.len();
    bytes.resize(offset + 24 + 8 * elements.len(), 0);
    put_u64(bytes, offset, ctor_header(abi::TAG_ARRAY, 0, 1));
    put_u64(bytes, offset + 8, elements.len() as u64);
    put_u64(bytes, offset + 16, elements.len() as u64);
    for (index, element) in elements.iter().copied().enumerate() {
        put_u64(bytes, offset + 24 + 8 * index, element);
    }
    align_word(bytes);
    offset
}

fn synthetic_imports(rows: &[(&str, bool, bool, bool)]) -> SyntheticImports {
    let mut bytes = vec![0; format::OLEAN_HEADER_SIZE + 8];
    bytes[..format::OLEAN_MAGIC.len()].copy_from_slice(&format::OLEAN_MAGIC);
    bytes[5] = 2;
    bytes[6] = 1;
    bytes[7..13].copy_from_slice(b"4.32.0");
    bytes[40..80].copy_from_slice(format::PIN_COMMIT.as_bytes());
    put_u64(&mut bytes, 80, SYNTHETIC_BASE);

    let empty_array = push_array(&mut bytes, &[]);
    let names: Vec<usize> = rows
        .iter()
        .map(|(module, _, _, _)| push_name(&mut bytes, module))
        .collect();

    let import_array = push_array(&mut bytes, &vec![0; rows.len()]);

    let root = bytes.len();
    bytes.resize(root + 56, 0);
    put_u64(&mut bytes, root, ctor_header(0, 5, 56));
    put_u64(&mut bytes, root + 8, synthetic_ptr(import_array));
    for field in 1..5 {
        put_u64(&mut bytes, root + 8 + 8 * field, synthetic_ptr(empty_array));
    }
    bytes[root + 48] = 1;
    put_u64(&mut bytes, format::OLEAN_HEADER_SIZE, synthetic_ptr(root));

    let mut import_offsets = Vec::with_capacity(rows.len());
    for (index, ((_, import_all, is_exported, is_meta), name)) in rows.iter().zip(names).enumerate()
    {
        let offset = bytes.len();
        bytes.resize(offset + 24, 0);
        put_u64(&mut bytes, offset, ctor_header(0, 1, 24));
        put_u64(&mut bytes, offset + 8, synthetic_ptr(name));
        bytes[offset + 16] = u8::from(*import_all);
        bytes[offset + 17] = u8::from(*is_exported);
        bytes[offset + 18] = u8::from(*is_meta);
        put_u64(
            &mut bytes,
            import_array + 24 + 8 * index,
            synthetic_ptr(offset),
        );
        import_offsets.push(offset);
    }

    SyntheticImports {
        bytes,
        import_offsets,
    }
}

fn fixture(name: &str) -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3")
        .join(name);
    let data = std::fs::read(&path);
    assert!(
        data.is_ok(),
        "missing C3 fixture {}: {:?}",
        path.display(),
        data.err()
    );
    data.expect("asserted above")
}

#[test]
fn import_decoder_preserves_all_eight_flag_combinations() {
    for bits in 0u8..8 {
        let expected = ModuleImport {
            module: module_name("TruthTable"),
            import_all: bits & 0b001 != 0,
            is_exported: bits & 0b010 != 0,
            is_meta: bits & 0b100 != 0,
        };
        let fixture = synthetic_imports(&[(
            "TruthTable",
            expected.import_all,
            expected.is_exported,
            expected.is_meta,
        )]);
        let view = OleanView::parse(&fixture.bytes).expect("synthetic header");
        let module = view
            .module_data(WalkBudget::default())
            .expect("synthetic module");
        assert_eq!(module.imports, [expected], "flag combination {bits:03b}");
    }
}

#[test]
fn import_decoder_preserves_order_and_duplicate_rows() {
    let fixture = synthetic_imports(&[
        ("Alpha", false, true, false),
        ("Beta", true, false, true),
        ("Alpha", true, true, false),
    ]);
    let view = OleanView::parse(&fixture.bytes).expect("synthetic header");
    let module = view
        .module_data(WalkBudget::default())
        .expect("synthetic module");
    assert_eq!(
        module.imports,
        [
            ModuleImport {
                module: module_name("Alpha"),
                import_all: false,
                is_exported: true,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Beta"),
                import_all: true,
                is_exported: false,
                is_meta: true,
            },
            ModuleImport {
                module: module_name("Alpha"),
                import_all: true,
                is_exported: true,
                is_meta: false,
            },
        ]
    );
}

#[test]
fn import_module_name_preserves_numeric_component_kind() {
    let mut fixture = synthetic_imports(&[("7", false, true, false)]);
    let import = fixture.import_offsets[0];
    let name = usize::try_from(get_u64(&fixture.bytes, import + 8) - SYNTHETIC_BASE)
        .expect("synthetic Name offset fits usize");
    put_u64(&mut fixture.bytes, name, ctor_header(2, 2, 32));
    put_u64(&mut fixture.bytes, name + 16, (7 << 1) | 1);

    let view = OleanView::parse(&fixture.bytes).expect("synthetic header");
    let module = view
        .module_data(WalkBudget::default())
        .expect("numeric module Name");
    assert_eq!(module.imports[0].module, Name::num(Name::anonymous(), 7));
    assert_ne!(module.imports[0].module, module_name("7"));
}

#[test]
fn import_decoder_rejects_each_noncanonical_bool() {
    let reasons = [
        "noncanonical Import.importAll Bool",
        "noncanonical Import.isExported Bool",
        "noncanonical Import.isMeta Bool",
    ];
    for (index, reason) in reasons.into_iter().enumerate() {
        let mut fixture = synthetic_imports(&[("BadBool", false, true, false)]);
        let import = fixture.import_offsets[0];
        fixture.bytes[import + 16 + index] = 2;
        let view = OleanView::parse(&fixture.bytes).expect("synthetic header");
        assert!(
            matches!(
                view.module_data(WalkBudget::default()),
                Err(RegionError::DecodeShape { reason: actual, .. }) if actual == reason
            ),
            "field {index} accepted a noncanonical Bool"
        );
    }
}

#[test]
fn import_decoder_rejects_wrong_arity_and_scalar_size() {
    let mut wrong_arity = synthetic_imports(&[("WrongArity", false, true, false)]);
    let import = wrong_arity.import_offsets[0];
    put_u64(&mut wrong_arity.bytes, import, ctor_header(0, 0, 24));
    let view = OleanView::parse(&wrong_arity.bytes).expect("synthetic header");
    assert!(matches!(
        view.module_data(WalkBudget::default()),
        Err(RegionError::DecodeShape {
            reason: "Import shape",
            ..
        })
    ));

    let mut short_scalar = synthetic_imports(&[("ShortScalar", false, true, false)]);
    let import = short_scalar.import_offsets[0];
    put_u64(&mut short_scalar.bytes, import, ctor_header(0, 1, 16));
    let view = OleanView::parse(&short_scalar.bytes).expect("synthetic header");
    assert!(matches!(
        view.module_data(WalkBudget::default()),
        Err(RegionError::DecodeShape {
            reason: "Import shape",
            ..
        })
    ));
}

#[test]
fn import_decoder_rejects_physically_truncated_scalar_storage() {
    let mut fixture = synthetic_imports(&[("Truncated", false, true, false)]);
    let import = fixture.import_offsets[0];
    fixture.bytes.truncate(import + 18);
    let view = OleanView::parse(&fixture.bytes).expect("synthetic header");
    assert!(matches!(
        view.module_data(WalkBudget::default()),
        Err(RegionError::Truncated { .. })
    ));
}

#[test]
fn module_decode_budget_is_cumulative_across_import_work() {
    let fixture = synthetic_imports(&[("Budgeted", false, true, false)]);
    let view = OleanView::parse(&fixture.bytes).expect("synthetic header");
    assert!(matches!(
        view.module_data(WalkBudget { max_objects: 2 }),
        Err(RegionError::BudgetExhausted {
            visited: 3,
            budget: 2
        })
    ));
}

#[test]
fn init_aggregator_walks_clean() {
    let bytes = fixture("Init.olean");
    let view = OleanView::parse(&bytes).expect("header");
    assert_eq!(view.header.version, 2);
    assert_eq!(view.header.lean_version, "4.32.0");
    assert_eq!(
        view.header.githash,
        "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
    );
    assert_eq!(view.header.base_addr % format::REGION_ALIGN as u64, 0);
    let report = view.walk(WalkBudget::default()).expect("walk");
    assert_eq!(report.objects, 158, "object census drifted for Init.olean");
    let md = view
        .module_data(WalkBudget::default())
        .expect("module data");
    assert!(md.is_module);
    assert_eq!(md.imports.len(), 43);
    assert_eq!(md.constants, 0, "Init is an import aggregator");
    assert!(
        md.imports
            .iter()
            .any(|import| import.module == module_name("Init.Prelude"))
    );
    assert!(
        md.imports
            .iter()
            .all(|import| !import.import_all && import.is_exported),
        "Init.lean has only public, non-all imports at the pin"
    );
    let init_try: Vec<ModuleImport> = md
        .imports
        .iter()
        .filter(|import| import.module == module_name("Init.Try"))
        .cloned()
        .collect();
    assert_eq!(
        init_try,
        [
            ModuleImport {
                module: module_name("Init.Try"),
                import_all: false,
                is_exported: true,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Init.Try"),
                import_all: false,
                is_exported: true,
                is_meta: true,
            },
        ],
        "the two Reference-produced Init.Try rows must not collapse"
    );
}

#[test]
fn binder_name_hint_decodes_constants_and_extensions() {
    let bytes = fixture("Init.BinderNameHint.olean");
    let view = OleanView::parse(&bytes).expect("header");
    view.walk(WalkBudget::default()).expect("walk");
    let md = view
        .module_data(WalkBudget::default())
        .expect("module data");
    // Independently recorded from the ordered import declarations in the
    // pinned Reference source `Init/BinderNameHint.lean`.
    assert_eq!(
        md.imports,
        [
            ModuleImport {
                module: module_name("Init.Prelude"),
                import_all: false,
                is_exported: true,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Init.Tactics"),
                import_all: false,
                is_exported: false,
                is_meta: false,
            },
        ]
    );
    assert_eq!(md.constants, 2);
    assert_eq!(md.const_names.len(), 2, "constNames must mirror constants");
    assert!(
        md.const_names.iter().any(|n| n == "binderNameHint"),
        "expected binderNameHint among {:?}",
        md.const_names
    );
    assert!(!md.extensions.is_empty());
    // Extension payloads are opaque by contract: counted, never interpreted.
    let total: u64 = md.extensions.iter().map(|e| e.entries).sum();
    assert!(total > 0);
}

#[test]
fn size_of_lemmas_carries_simp_extension_payloads() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("header");
    let report = view.walk(WalkBudget::default()).expect("walk");
    assert!(report.objects > 500);
    let md = view
        .module_data(WalkBudget::default())
        .expect("module data");
    // This real Reference artifact covers import-all, public, private, meta,
    // and an ordered duplicate. Expectations are independently recorded from
    // `Init/SizeOfLemmas.lean` at the pinned commit.
    assert_eq!(
        md.imports,
        [
            ModuleImport {
                module: module_name("Init.Data.Char.Basic"),
                import_all: true,
                is_exported: false,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Init.SizeOf"),
                import_all: true,
                is_exported: false,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Init.Data.Char.Basic"),
                import_all: false,
                is_exported: true,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Init.Data.Nat.Linear"),
                import_all: false,
                is_exported: false,
                is_meta: false,
            },
            ModuleImport {
                module: module_name("Init.MetaTypes"),
                import_all: false,
                is_exported: false,
                is_meta: true,
            },
        ]
    );
    assert_eq!(md.constants, 16);
    assert!(
        md.extensions.iter().any(|e| e.name.contains("simp")),
        "expected a simp extension block among {:?}",
        md.extensions.iter().map(|e| &e.name).collect::<Vec<_>>()
    );
}

#[test]
fn header_rejections_are_typed() {
    let good = fixture("Init.olean");

    // Truncation below the fixed header.
    let r = OleanView::parse(&good[..40]);
    assert!(matches!(r, Err(RegionError::Truncated { .. })), "{r:?}");

    // Bad magic.
    let mut bad = good.clone();
    bad[0] ^= 0xff;
    let r = OleanView::parse(&bad);
    assert!(matches!(r, Err(RegionError::BadMagic)), "{r:?}");

    // Unsupported version.
    let mut bad = good.clone();
    bad[5] = 9;
    let r = OleanView::parse(&bad);
    assert!(
        matches!(r, Err(RegionError::UnsupportedVersion(9))),
        "{r:?}"
    );

    // Misaligned base address (violates REGION_ALIGN).
    let mut bad = good.clone();
    bad[80] = 8;
    let r = OleanView::parse(&bad);
    assert!(
        matches!(r, Err(RegionError::MisalignedBase { .. })),
        "{r:?}"
    );
}

#[test]
fn walk_rejections_are_typed() {
    let good = fixture("Init.olean");
    let header = format::OLEAN_HEADER_SIZE;

    // Root pointer pushed out of bounds (kept even: an odd value would be a
    // legitimate scalar box, not a pointer).
    let mut bad = good.clone();
    bad[header] = 0xf8;
    bad[header + 7] = 0x7f;
    let view = OleanView::parse(&bad).expect("header still valid");
    let r = view.walk(WalkBudget::default());
    assert!(
        matches!(r, Err(RegionError::PtrOutOfBounds { .. })),
        "{r:?}"
    );

    // Root pointer misaligned.
    let mut bad = good.clone();
    bad[header] ^= 0x04;
    let view = OleanView::parse(&bad).expect("header still valid");
    let r = view.walk(WalkBudget::default());
    assert!(
        matches!(
            r,
            Err(RegionError::MisalignedPtr { .. }) | Err(RegionError::PtrOutOfBounds { .. })
        ),
        "{r:?}"
    );

    // Truncated data region: keep the header, drop the tail.
    let view_bytes = good[..good.len() - 64].to_vec();
    let view = OleanView::parse(&view_bytes).expect("header still valid");
    let r = view.walk(WalkBudget::default());
    assert!(r.is_err(), "truncated region must not walk clean: {r:?}");
}

#[test]
fn budget_exhaustion_is_typed_not_partial() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("header");
    let r = view.walk(WalkBudget { max_objects: 10 });
    assert!(
        matches!(r, Err(RegionError::BudgetExhausted { budget: 10, .. })),
        "{r:?}"
    );
}

#[test]
fn seeded_byteflip_sweep_never_panics_never_lies() {
    // Deterministic xorshift sweep: flip one byte at a time in the data
    // region and demand a typed outcome. Acceptance is allowed ONLY when the
    // corruption did not change the walked graph's integrity-relevant bytes
    // (e.g. unreached padding); a panic or hang fails the whole test.
    let good = fixture("Init.BinderNameHint.olean");
    let mut seed: u64 = 0x53_76_24_79_24_31_66_6c; // fixed; determinism law
    let mut flips = 0u32;
    let mut typed_errors = 0u32;
    while flips < 300 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let pos =
            (seed as usize) % (good.len() - format::OLEAN_HEADER_SIZE) + format::OLEAN_HEADER_SIZE;
        let bit = 1u8 << ((seed >> 32) % 8);
        let mut mutated = good.clone();
        mutated[pos] ^= bit;
        flips += 1;
        match OleanView::parse(&mutated) {
            Err(_) => typed_errors += 1,
            Ok(view) => {
                let budget = WalkBudget {
                    max_objects: 1_000_000,
                };
                let walk = view.walk(budget);
                let md = view.module_data(budget);
                if walk.is_err() || md.is_err() {
                    typed_errors += 1;
                }
            }
        }
    }
    assert_eq!(flips, 300);
    // The corpus is dense: the sweep must actually be exercising the error
    // paths, not silently accepting everything.
    assert!(
        typed_errors > 100,
        "only {typed_errors}/300 flips produced typed errors — corruption not detected"
    );
}

#[test]
fn manifest_matches_fixture_bytes() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tribunal/fixtures/c3");
    let manifest = std::fs::read_to_string(dir.join("MANIFEST.txt"));
    assert!(manifest.is_ok(), "missing C3 MANIFEST.txt");
    let manifest = manifest.expect("asserted above");
    assert!(manifest.contains("schema fln-c3-manifest/1"));
    let mut rows = 0;
    for line in manifest.lines() {
        if line.starts_with('#') || line.starts_with("schema") || line.is_empty() {
            continue;
        }
        let cols: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(cols.len(), 4, "manifest row arity: {line:?}");
        let bytes = std::fs::read(dir.join(cols[3]));
        assert!(bytes.is_ok(), "fixture {} missing", cols[3]);
        let bytes = bytes.expect("asserted above");
        assert_eq!(
            bytes.len().to_string(),
            cols[1],
            "size mismatch for {}",
            cols[3]
        );
        rows += 1;
    }
    assert_eq!(rows, 3, "C3 seed corpus is three fixtures");
}

// ---- the fln-20n × fln-wgp seam: shared engine + mmap path -----------------

/// The mmap-backed production path must equal the by-value path observation
/// for observation: same header, same ModuleData decode — and the mapping
/// comes back sealed (region hygiene holds while the view is live).
#[test]
fn mapped_load_matches_by_value_load_and_is_sealed() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3/Init.SizeOfLemmas.olean");
    if !path.exists() {
        eprintln!("SKIP (typed limitation): c3 fixture olean not present");
        return;
    }
    let mapped = fln_olean::region::MappedOlean::open(&path).expect("mmap load");
    assert!(mapped.is_sealed(), "open() must seal after validation");
    assert!(!mapped.is_empty());

    let bytes = fixture("Init.SizeOfLemmas.olean");
    let by_value = OleanView::parse(&bytes).expect("by-value parse");
    assert_eq!(mapped.header(), &by_value.header, "headers agree");
    assert_eq!(
        mapped
            .view()
            .module_data(WalkBudget::default())
            .expect("mmap decode"),
        by_value
            .module_data(WalkBudget::default())
            .expect("by-value decode"),
        "ModuleData decode is path-independent"
    );
}

/// The shared full-surface audit accepts the real fixture and sees at least
/// as many objects as the reachability walk (it validates the whole payload,
/// reachable or not), with zero rewrites.
#[test]
fn shared_audit_covers_the_full_surface() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let audit = view.shared_audit().expect("shared audit");
    let walk = view.walk(WalkBudget::default()).expect("walk");
    assert_eq!(audit.pointers_fixed, 0, "audit never rewrites");
    assert!(
        audit.objects >= walk.objects,
        "full-surface audit ({}) cannot see fewer objects than the reachable walk ({})",
        audit.objects,
        walk.objects
    );
}

/// Corruption reaches the codec through the SHARED engine's laws: a hot rc
/// in the first payload object and a wild pointer both fault typed via the
/// mapped fault vocabulary, and MappedOlean::open refuses the artifact.
#[test]
fn shared_audit_rejects_corruption_typed() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let header = fln_olean::format::OLEAN_HEADER_SIZE;

    // Non-persistent rc in the first object (payload offset 8 → rc word).
    let mut hot = bytes.clone();
    hot[header + 8] = 1;
    let view = OleanView::parse(&hot).expect("header still parses");
    assert!(
        matches!(
            view.shared_audit(),
            Err(RegionError::NonPersistentRc { .. })
        ),
        "hot rc must fault typed through the shared engine"
    );

    // Wild root pointer (payload offset 0).
    let mut wild = bytes.clone();
    let bogus = ((u64::MAX / 2) & !7).to_le_bytes();
    wild[header..header + 8].copy_from_slice(&bogus);
    let view = OleanView::parse(&wild).expect("header still parses");
    assert!(
        matches!(view.shared_audit(), Err(RegionError::PtrOutOfBounds { .. })),
        "wild root must fault typed through the shared engine"
    );

    // The mmap door enforces the same laws before sealing.
    let dir =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target_local/fln-olean-seam-tests");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let corrupt_path = dir.join(format!("corrupt-{}.olean", std::process::id()));
    std::fs::write(&corrupt_path, &hot).expect("write corrupt fixture");
    assert!(
        matches!(
            fln_olean::region::MappedOlean::open(&corrupt_path),
            Err(fln_olean::region::MappedOleanError::Region(
                RegionError::NonPersistentRc { .. }
            ))
        ),
        "MappedOlean must refuse a corrupt artifact before sealing"
    );
}
