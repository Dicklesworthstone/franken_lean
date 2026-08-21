//! Module-system companion-chain decode (bead `franken_lean-timy`): the
//! `.olean.private` part is the authoritative constant array, and decoding the
//! chain must recover the `_private` equation-compiler auxiliary family that the
//! exported `.olean` part omits.
//!
//! WHY THIS SUITE EXISTS. `franken_lean-timy` reported 24 corpus
//! `UnknownConstant` rejections whose missing dependencies were all `_private`
//! equation-compiler auxiliaries (`match_N`, `_proof_N`, `.loop`). The named
//! localisation was intra-module decode coverage: `Init.Data.List.ToArrayImpl`
//! decoded FIVE declarations and
//! `_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1` was not among
//! them. That is exactly what reading the exported part alone produces. The
//! repair is to read the companion chain, whose private part carries a superset
//! of the exported constant array. Before this file, `fln-olean` had no test
//! over a real module-system chain at all, so a decoder that silently returned
//! the exported array again would reintroduce the whole bead unnoticed.
//!
//! EVERY NUMBER BELOW IS MEASURED against the pinned Reference stdlib
//! (leanprover/lean4 v4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35),
//! not assumed. The exported-part counts are asserted alongside the chain counts
//! so a change that made the exported part already complete would fail here
//! rather than turn these assertions vacuous.
//!
//! SCOPE. This suite pins `fln-olean`'s chain-decode capability: given the three
//! parts, the private region decodes to the superset. Which array a downstream
//! consumer chooses to admit is that consumer's surface and is not judged here.

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

/// The pinned Reference stdlib. `FLN_REFERENCE_LIB` overrides; the
/// elan-installed pin is the default. No checked-in fixture carries the
/// `.olean.server`/`.olean.private` companion parts, so an absent toolchain is a
/// loud skip rather than a silent pass.
fn reference_lib() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(dir);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

macro_rules! lib_or_skip {
    ($what:expr) => {
        match reference_lib() {
            Some(lib) => lib,
            None => {
                eprintln!(
                    "SKIP {}: pinned Reference stdlib absent (set FLN_REFERENCE_LIB \
                     or install leanprover--lean4---v4.32.0)",
                    $what
                );
                return;
            }
        }
    };
}

/// The three parts of one module-system module, read whole.
struct ChainBytes {
    exported: Vec<u8>,
    server: Vec<u8>,
    private: Vec<u8>,
}

fn chain_bytes(lib: &PathBuf, relative: &str) -> ChainBytes {
    let exported_path = lib.join(format!("{relative}.olean"));
    let server_path = lib.join(format!("{relative}.olean.server"));
    let private_path = lib.join(format!("{relative}.olean.private"));
    let read = |path: &PathBuf| -> Vec<u8> {
        std::fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
    };
    ChainBytes {
        exported: read(&exported_path),
        server: read(&server_path),
        private: read(&private_path),
    }
}

/// `constNames` of the exported part alone, and of the full chain's private
/// part, as display strings.
fn exported_and_private_names(chain: &ChainBytes) -> (Vec<String>, Vec<String>) {
    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported = exported_view
        .module_data(WalkBudget::default())
        .expect("exported ModuleData decodes");
    assert!(
        exported.is_module,
        "fixture must be a module-system module, else the chain law does not apply"
    );

    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");
    let private = private_view
        .module_data(WalkBudget::default())
        .expect("private ModuleData decodes");

    (exported.const_names, private.const_names)
}

/// The exact constant `franken_lean-timy` names as never decoded.
const TIMY_WITNESS: &str = "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1";

#[test]
fn timy_witness_module_recovers_its_private_match_auxiliary() {
    let lib = lib_or_skip!("timy_witness_module_recovers_its_private_match_auxiliary");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");
    let (exported, private) = exported_and_private_names(&chain);

    // The precondition that made the bead real. Without this assertion the one
    // below proves nothing: if the exported part already carried the auxiliary,
    // finding it in the chain would be no evidence about chain decode at all.
    assert_eq!(
        exported.len(),
        5,
        "measured at the pin: the exported part of Init.Data.List.ToArrayImpl \
         carries five constants; got {exported:?}"
    );
    assert!(
        !exported.contains(&TIMY_WITNESS.to_owned()),
        "the exported part must NOT carry {TIMY_WITNESS}; if it does, this suite \
         no longer witnesses the bead and its assertions are vacuous"
    );

    // The repaired behaviour.
    assert_eq!(
        private.len(),
        6,
        "measured at the pin: the private part carries the five exported \
         constants plus one equation-compiler auxiliary; got {private:?}"
    );
    assert!(
        private.contains(&TIMY_WITNESS.to_owned()),
        "the private part must carry {TIMY_WITNESS} — this is the exact \
         constant franken_lean-timy reported as never decoded; got {private:?}"
    );
    for name in &exported {
        assert!(
            private.contains(name),
            "the private constant array must be a superset of the exported one; \
             {name} is missing"
        );
    }
}

#[test]
fn the_recovered_auxiliary_decodes_to_a_real_constant_info() {
    let lib = lib_or_skip!("the_recovered_auxiliary_decodes_to_a_real_constant_info");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");

    // Naming a constant is not decoding it. The bead's complaint was that the
    // kernel was handed no ConstantInfo for the auxiliary, so this walks the
    // whole declaration decoder — including the Name/Level/Expr identity
    // cross-checks it enables by default — over the chain.
    let constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("the private part's constants decode through the chain");

    assert_eq!(
        constants.len(),
        6,
        "the private part decodes six full ConstantInfos at the pin"
    );
    let witness = constants
        .iter()
        .find(|info| info.name().to_display_string() == TIMY_WITNESS);
    assert!(
        witness.is_some(),
        "{TIMY_WITNESS} must decode to a ConstantInfo, not merely appear in \
         constNames; decoded {:?}",
        constants
            .iter()
            .map(|info| info.name().to_display_string())
            .collect::<Vec<_>>()
    );
}

#[test]
fn private_part_is_a_superset_across_the_modules_the_bead_names() {
    let lib = lib_or_skip!("private_part_is_a_superset_across_the_modules_the_bead_names");

    // (module, exported constants, private constants) — all measured at the pin.
    // franken_lean-timy named these modules as sources of missing auxiliaries.
    let expected = [
        ("Init/Data/List/ToArrayImpl", 5_usize, 6_usize),
        ("Init/Prelude", 2204, 2314),
        ("Init/Data/Array/BasicAux", 8, 37),
        ("Init/Control/MonadAttach", 29, 30),
    ];

    for (relative, exported_count, private_count) in expected {
        let chain = chain_bytes(&lib, relative);
        let (exported, private) = exported_and_private_names(&chain);

        assert_eq!(
            exported.len(),
            exported_count,
            "{relative}: exported constant count changed at the pin"
        );
        assert_eq!(
            private.len(),
            private_count,
            "{relative}: private constant count changed at the pin"
        );
        assert!(
            private_count > exported_count,
            "{relative}: this module must actually gain constants from its \
             private part, else it witnesses nothing"
        );
        for name in &exported {
            assert!(
                private.contains(name),
                "{relative}: private array must be a superset of the exported \
                 array; {name} is missing"
            );
        }
        let recovered = private
            .iter()
            .filter(|name| !exported.contains(name))
            .count();
        assert_eq!(
            recovered,
            private_count - exported_count,
            "{relative}: the private part must add constants rather than \
             replace exported ones"
        );
    }
}

#[test]
fn recovered_family_covers_match_and_proof_and_loop_auxiliaries() {
    let lib = lib_or_skip!("recovered_family_covers_match_and_proof_and_loop_auxiliaries");
    let chain = chain_bytes(&lib, "Init/Data/Array/BasicAux");
    let (exported, private) = exported_and_private_names(&chain);

    // franken_lean-timy named match_N, _proof_N and the `.loop`/`.go` recursion
    // auxiliaries as the missing family. These three are measured members of
    // this module's private delta.
    let family = [
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
    ];
    for member in family {
        assert!(
            !exported.contains(&member.to_owned()),
            "{member} must be absent from the exported part, else it witnesses \
             nothing about chain decode"
        );
        assert!(
            private.contains(&member.to_owned()),
            "{member} must be recovered from the private part; got {private:?}"
        );
    }
}

/// The auxiliary families `franken_lean-timy` names, as predicates over a
/// display-form constant name.
///
/// Each mirrors a `\.<pattern>$`-anchored form: the leading dot is required, so
/// a bare top-level `match_1` is not counted. `.loop` and `.go` are component
/// tests rather than suffix tests because the recursion auxiliary is a segment,
/// not a terminal.
mod family {
    fn components(name: &str) -> Vec<&str> {
        name.split('.').collect()
    }

    /// A nonempty run of ASCII digits — the `\d+` of the measured patterns.
    fn digits(rest: &str) -> bool {
        !rest.is_empty() && rest.bytes().all(|byte| byte.is_ascii_digit())
    }

    /// `\d+(_\d+)*` — only `match_N` admits the underscore-joined form.
    fn digit_groups(rest: &str) -> bool {
        !rest.is_empty() && rest.split('_').all(digits)
    }

    fn last_component_suffix<'a>(name: &'a str, prefix: &str) -> Option<&'a str> {
        let parts = components(name);
        if parts.len() < 2 {
            return None;
        }
        parts.last().and_then(|last| last.strip_prefix(prefix))
    }

    /// `.match_1`, `.match_1_1`, …
    pub fn match_n(name: &str) -> bool {
        last_component_suffix(name, "match_").is_some_and(digit_groups)
    }

    /// `._proof_1`, …
    pub fn proof_n(name: &str) -> bool {
        last_component_suffix(name, "_proof_").is_some_and(digits)
    }

    /// `.eq_1`, … — equation lemmas.
    pub fn eq_n(name: &str) -> bool {
        last_component_suffix(name, "eq_").is_some_and(digits)
    }

    /// `.eq_def`.
    pub fn eq_def(name: &str) -> bool {
        let parts = components(name);
        parts.len() >= 2 && parts.last() == Some(&"eq_def")
    }

    /// A `loop` component anywhere but the head.
    pub fn loop_(name: &str) -> bool {
        components(name)
            .iter()
            .skip(1)
            .any(|component| *component == "loop")
    }
}

/// Enumerate every module under `Init` that has a complete companion chain.
fn init_chain_modules(lib: &PathBuf) -> Vec<String> {
    let mut out = Vec::new();
    let root = lib.join("Init");
    let mut pending = vec![root];
    while let Some(directory) = pending.pop() {
        let entries = std::fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()));
        for entry in entries {
            let entry = entry.expect("directory entry");
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
                continue;
            }
            if path.extension() != Some(std::ffi::OsStr::new("olean")) {
                continue;
            }
            let server = PathBuf::from(format!("{}.server", path.display()));
            let private = PathBuf::from(format!("{}.private", path.display()));
            if !(server.is_file() && private.is_file()) {
                continue;
            }
            let relative = path
                .strip_prefix(lib)
                .expect("module path is under the stdlib root")
                .with_extension("");
            out.push(relative.to_string_lossy().into_owned());
        }
    }
    out.sort();
    out
}

#[test]
fn every_named_auxiliary_family_decodes_across_the_whole_init_corpus() {
    let lib = lib_or_skip!("every_named_auxiliary_family_decodes_across_the_whole_init_corpus");

    // An aggregate count cannot witness a per-family gap: one family could be
    // wholly absent while the total still looked healthy. franken_lean-timy
    // names match_N, _proof_N, eq_N/eq_def and the `.loop` recursion auxiliary
    // as one population, so each is bound to its own measured floor here.
    //
    // Counts are per-module-distinct names summed over every Init module with a
    // complete chain, measured at the pin.
    let modules = init_chain_modules(&lib);
    assert_eq!(
        modules.len(),
        600,
        "every Init module at the pin carries a complete companion chain"
    );

    let mut match_n = 0_usize;
    let mut proof_n = 0_usize;
    let mut eq_n = 0_usize;
    let mut eq_def = 0_usize;
    let mut loop_ = 0_usize;
    let mut exported_total = 0_usize;
    let mut private_total = 0_usize;

    for relative in &modules {
        let chain = chain_bytes(&lib, relative);
        let (exported, private) = exported_and_private_names(&chain);
        exported_total += exported.len();
        private_total += private.len();
        for name in &private {
            if family::match_n(name) {
                match_n += 1;
            }
            if family::proof_n(name) {
                proof_n += 1;
            }
            if family::eq_n(name) {
                eq_n += 1;
            }
            if family::eq_def(name) {
                eq_def += 1;
            }
            if family::loop_(name) {
                loop_ += 1;
            }
        }
    }

    assert_eq!(exported_total, 51_506, "exported corpus total moved");
    assert_eq!(private_total, 65_404, "private corpus total moved");
    assert_eq!(match_n, 2_592, "match_N decode coverage moved");
    assert_eq!(proof_n, 3_480, "_proof_N decode coverage moved");
    assert_eq!(eq_n, 3_449, "eq_N decode coverage moved");
    assert_eq!(eq_def, 507, "eq_def decode coverage moved");
    assert_eq!(loop_, 686, "`.loop` decode coverage moved");
}

#[test]
fn every_named_private_auxiliary_family_reaches_the_constant_info_decoder() {
    let lib =
        lib_or_skip!("every_named_private_auxiliary_family_reaches_the_constant_info_decoder");

    // The corpus census above proves that the private `constNames` arrays name
    // each family. That is necessary but insufficient: a future decoder could
    // retain the names while failing to construct the corresponding
    // ConstantInfo. Find one *private-only* representative per family, then
    // pass each through DeclDecoder with its real companion address spaces.
    let families: [(&str, fn(&str) -> bool); 4] = [
        ("match_N", family::match_n),
        ("_proof_N", family::proof_n),
        ("eq_N", family::eq_n),
        (".loop", family::loop_),
    ];
    let mut representatives: [Option<(String, String)>; 4] = [None, None, None, None];

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let (exported, private) = exported_and_private_names(&chain);
        for (slot, (_, belongs_to_family)) in representatives.iter_mut().zip(families) {
            if slot.is_some() {
                continue;
            }
            if let Some(name) = private
                .iter()
                .find(|name| !exported.contains(*name) && belongs_to_family(name))
            {
                *slot = Some((relative.clone(), name.clone()));
            }
        }
        if representatives.iter().all(Option::is_some) {
            break;
        }
    }

    for ((family, _), representative) in families.into_iter().zip(representatives) {
        let (relative, name) = representative.unwrap_or_else(|| {
            panic!(
                "the pinned Init private companions contain no private-only {family} representative"
            )
        });
        let chain = chain_bytes(&lib, &relative);
        let private_view =
            OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
                .unwrap_or_else(|error| {
                    panic!("{family} {name}: parse private {relative}: {error}")
                });
        let constants = DeclDecoder::new(&private_view, WalkBudget::default())
            .decode_module_constants()
            .unwrap_or_else(|error| panic!("{family} {name}: decode private {relative}: {error}"));

        assert!(
            constants
                .iter()
                .any(|info| info.name().to_display_string() == name),
            "{family} {name} in {relative} remained only a constName instead of decoding to ConstantInfo"
        );
    }
}

#[test]
fn a_companion_part_read_without_its_dependencies_is_a_typed_refusal() {
    let lib = lib_or_skip!("a_companion_part_read_without_its_dependencies_is_a_typed_refusal");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    // The private region's stored pointers retain the exported region's
    // compacted addresses. Read standalone, those are out-of-region pointers and
    // must become a typed RegionError — never a panic, and never a
    // silently-partial constant array that would look like a decode result.
    let view = OleanView::parse(&chain.private).expect("the private part has a valid header");
    let error = view
        .module_data(WalkBudget::default())
        .expect_err("a standalone private part must refuse its external pointers");
    let rendered = format!("{error}");
    assert!(
        rendered.contains("out of bounds"),
        "expected an out-of-region pointer refusal, got: {rendered}"
    );
}
