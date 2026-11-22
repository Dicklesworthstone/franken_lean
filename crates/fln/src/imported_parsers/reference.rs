//! Exact pinned artifact representations exercise native descriptor reduction.
//! This is a decoded-data compatibility test, not a kernel admission claim:
//! the temporary Environment below contains decoded, unchecked declarations,
//! never becomes an Engine, and never supplies a production import receipt.
//! No Reference executable or imported IR runs in this test.
use super::*;
use crate::{OleanDecodeLimits, decode_olean_module_artifacts};
use fln_core::options::KVMap;
use fln_olean::region::{OleanView, WalkBudget};
use fln_parse::closure_registry::ClosureSyntaxRegistry;
use fln_parse::extensions::Descr;
use fln_parse::reference_tokens::reference_census;
use std::path::{Path, PathBuf};

fn module_constants(lib: &Path, module: &str) -> Vec<ConstantInfo> {
    let path = lib.join(format!("{}.olean", module.replace('.', "/")));
    let public = std::fs::read(&path).unwrap_or_else(|error| panic!("{path:?}: {error}"));
    let server =
        std::fs::read(path.with_extension("olean.server")).expect("pinned module server companion");
    let private = std::fs::read(path.with_extension("olean.private"))
        .expect("pinned module private companion");
    let decoded = decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        OleanDecodeLimits::new(public.len() + server.len() + private.len()),
    )
    .unwrap_or_else(|error| panic!("{module}: {error}"));
    assert_eq!(decoded.header.githash, fln_olean::format::PIN_COMMIT);
    assert!(decoded.companion_parts_loaded);
    if module == "Init.Prelude" {
        // Prelude defines parser-description data without registering parsers.
        // Preparing its complete journal must preserve the existing imported
        // macro CLI path whose artifact closure contains only this Prelude.
        let view = OleanView::parse_with_dependencies(&private, &[&public, &server]).unwrap();
        let blocks = view
            .extension_payloads(WalkBudget::default(), 32 << 20)
            .unwrap();
        let journal = parsers::decode(&blocks, DecodeLimits::default()).unwrap();
        assert!(
            journal.is_empty(),
            "Init.Prelude parser journal: {journal:?}"
        );
        eprintln!("actual Init.Prelude parser journal is empty");
    }
    decoded.constants
}

#[test]
fn installed_conv_descriptions_reconstruct_actual_constructor_values_without_execution() {
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required for descriptor reconstruction"
        );
        eprintln!("SKIP: actual descriptor representation requires FLN_REFERENCE_LIB");
        return;
    };
    // Prelude supplies the real datatype interfaces, literal Name helpers and
    // Nat numeral projection. Conv supplies these four simple descriptions.
    // This deliberately does not load or claim to admit the Init closure.
    let mut environment = Environment::new();
    for module in ["Init.Prelude", "Init.Conv"] {
        for declaration in module_constants(&lib, module) {
            environment = environment.add_decl(declaration).unwrap();
        }
    }
    let allowed: BTreeSet<_> = environment
        .constants()
        .map(|(name, _)| name.clone())
        .collect();
    let mut reader = data::Reader::new(
        &environment,
        &allowed,
        data::DataLimits {
            max_steps: 100_000,
            max_depth: 64,
            max_bytes: 16_384,
        },
    );
    let mut nodes = 64;
    let module = name("Init.Conv");
    for symbol in ["skip", "cbv", "lhs", "rhs"] {
        let declaration = Name::str(name("Lean.Parser.Tactic.Conv"), symbol);
        let owner = environment.find(&declaration).unwrap();
        let (leading, value) = description_body(&module, &declaration, owner)
            .unwrap_or_else(|error| panic!("{error}"));
        assert!(leading);
        let descr = descriptions::read(
            &mut reader,
            value,
            &environment,
            &module,
            &declaration,
            &mut nodes,
            64,
        )
        .unwrap_or_else(|error| panic!("{error}"));
        // src/Init/Conv.lean declares these atom-like entries in category conv
        // with behavior Both: maximum precedence and a nonreserved first atom.
        assert_eq!(
            descr,
            Descr::Node {
                kind: declaration,
                prec: 1024,
                body: Box::new(Descr::NonReservedSymbol(symbol.into(), false)),
            }
        );
    }
    assert!(reader.used().contains(&name("Lean.ParserDescr.node")));
    assert!(
        reader.used().contains(&name("Lean.ParserDescr.sepBy1")),
        "all generated constructor interfaces are validated, even unused variants"
    );
    assert!(reader.used().contains(&name("Lean.Name.str")));
    eprintln!("actual Init.Conv ParserDescr values reconstructed: skip, cbv, lhs, rhs");
}

struct PinnedClosure {
    loaded: Vec<(CheckedOleanModule, Vec<OpaqueExtensionBlock>)>,
    environment: Environment,
    order: Vec<Name>,
}

fn load_pinned_closure(lib: &Path, roots: &[&str]) -> PinnedClosure {
    fn visit(
        lib: &Path,
        module: &Name,
        visited: &mut BTreeSet<Name>,
        out: &mut Vec<(CheckedOleanModule, Vec<OpaqueExtensionBlock>)>,
    ) {
        if !visited.insert(module.clone()) {
            return;
        }
        let rel = module.to_display_string().replace('.', "/");
        let path = lib.join(format!("{rel}.olean"));
        let public = std::fs::read(&path).unwrap_or_else(|error| panic!("{path:?}: {error}"));
        let server_path = path.with_extension("olean.server");
        let private_path = path.with_extension("olean.private");
        let (decoded, blocks) = if server_path.exists() && private_path.exists() {
            let server = std::fs::read(&server_path)
                .unwrap_or_else(|error| panic!("{server_path:?}: {error}"));
            let private = std::fs::read(&private_path)
                .unwrap_or_else(|error| panic!("{private_path:?}: {error}"));
            let decoded = decode_olean_module_artifacts(
                &public,
                &server,
                &private,
                OleanDecodeLimits::new(public.len() + server.len() + private.len()),
            )
            .unwrap_or_else(|error| panic!("{}: {error}", module.to_display_string()));
            let view = OleanView::parse_with_dependencies(&private, &[&public, &server])
                .unwrap_or_else(|error| panic!("{}: {error}", module.to_display_string()));
            let blocks = view
                .extension_payloads(WalkBudget::default(), 64 << 20)
                .unwrap_or_else(|error| panic!("{}: {error}", module.to_display_string()));
            (decoded, blocks)
        } else {
            let decoded =
                crate::decode_olean_artifact(&public, OleanDecodeLimits::new(public.len()))
                    .unwrap_or_else(|error| panic!("{}: {error}", module.to_display_string()));
            let view = OleanView::parse(&public)
                .unwrap_or_else(|error| panic!("{}: {error}", module.to_display_string()));
            let blocks = view
                .extension_payloads(WalkBudget::default(), 64 << 20)
                .unwrap_or_else(|error| panic!("{}: {error}", module.to_display_string()));
            (decoded, blocks)
        };
        assert_eq!(decoded.header.githash, fln_olean::format::PIN_COMMIT);
        let imports: Vec<Name> = decoded
            .module
            .imports
            .iter()
            .map(|imp| imp.module.clone())
            .collect();
        for dep in imports {
            visit(lib, &dep, visited, out);
        }
        let root = Environment::new().logical_root(&KVMap::new());
        out.push((
            CheckedOleanModule {
                name: module.clone(),
                decoded,
                base_logical_root: root,
                result_logical_root: root,
                declarations: Vec::new(),
            },
            blocks,
        ));
    }

    let mut visited = BTreeSet::new();
    let mut loaded = Vec::new();
    for root in roots {
        visit(lib, &name(root), &mut visited, &mut loaded);
    }
    let mut environment = Environment::new();
    let mut order = Vec::with_capacity(loaded.len());
    for (checked, _) in &loaded {
        order.push(checked.name.clone());
        for constant in &checked.decoded.constants {
            environment = environment
                .add_decl(constant.clone())
                .unwrap_or_else(|error| {
                    panic!("{}: {error:?}", constant.name().to_display_string())
                });
        }
    }
    PinnedClosure {
        loaded,
        environment,
        order,
    }
}

fn build_closure_registry_from_pin(lib: &Path, roots: &[&str]) -> ClosureSyntaxRegistry {
    let PinnedClosure {
        loaded,
        environment,
        order,
    } = load_pinned_closure(lib, roots);
    let inputs: Vec<ParserRegistrationModule<'_>> = loaded
        .iter()
        .map(|(checked, extensions)| ParserRegistrationModule {
            checked,
            extensions,
        })
        .collect();
    let limits = ParserRegistryLimits {
        max_steps: 1 << 25,
        max_bytes: 64 << 20,
        max_description_nodes: 1 << 20,
        ..ParserRegistryLimits::default()
    };
    let prepared = RegisteredParsers::prepare(&inputs, &environment, limits)
        .unwrap_or_else(|error| panic!("RegisteredParsers::prepare({roots:?}): {error}"));
    let mut engine = Engine::from_environment(environment);
    engine.imported_modules = Arc::new(order.iter().cloned().collect());
    prepared
        .closure_syntax_registry(&order, &engine)
        .unwrap_or_else(|error| panic!("closure_syntax_registry({roots:?}): {error}"))
}

#[test]
fn prelude_and_list_basic_olean_closures_build_exact_per_closure_syntax_registries() {
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required for per-closure registry verification"
        );
        eprintln!("SKIP: per-closure .olean registry test requires FLN_REFERENCE_LIB");
        return;
    };

    let prelude = build_closure_registry_from_pin(&lib, &["Init.Prelude"]);
    let list_basic = build_closure_registry_from_pin(&lib, &["Init.Data.List.Basic"]);
    let term = name("term");
    let plus_name = Name::str(Name::anonymous(), "term_+_");
    let list_lit_name = Name::str(Name::anonymous(), "term[_]");

    // Anonymous-constructor bracket `⟨` comes from the extracted builtin set in both closures.
    assert!(
        prelude.has_token("⟨") && prelude.has_token("⟩"),
        "Init.Prelude closure must carry builtin `⟨`/`⟩`"
    );
    assert!(
        list_basic.has_token("⟨") && list_basic.has_token("⟩"),
        "Init.Data.List.Basic closure must carry builtin `⟨`/`⟩`"
    );

    // `prelude import Init.Prelude` lacks the `+` term operator and list-literal syntax.
    assert!(
        !prelude.has_global_parser(&term, &plus_name)
            && !prelude.has_global_symbol_in_category(&term, "+"),
        "Init.Prelude closure must lack the `+` term operator"
    );
    assert!(
        !prelude.has_global_parser(&term, &list_lit_name),
        "Init.Prelude closure must lack list-literal syntax"
    );
    let expected_prelude_tokens = reference_census()
        .tokens_for(true, &[name("Init.Prelude")])
        .expect("Init.Prelude in census");
    assert_eq!(
        prelude.global_tokens(),
        &expected_prelude_tokens,
        "Init.Prelude decoded token set must equal the oracle's builtin token table"
    );

    // `import Init.Data.List.Basic` decodes both `+` (with precedence) and `[a, b]` directly
    // from the 15-module pinned `.olean` closure, matching the oracle's exact 351-token set.
    let plus = list_basic
        .find_parser(&term, &plus_name)
        .expect("Init.Data.List.Basic closure must decode `«term_+_»`");
    assert!(
        !plus.leading && plus.precedence == Some(65) && plus.lhs_precedence == Some(65),
        "unexpected `«term_+_»` precedence metadata: {plus:?}"
    );
    assert!(
        list_basic.has_global_symbol_in_category(&term, "+"),
        "Init.Data.List.Basic closure must expose `+` as a term operator"
    );
    let list_lit = list_basic
        .find_parser(&term, &list_lit_name)
        .expect("Init.Data.List.Basic closure must decode list-literal syntax `«term[_]»`");
    assert!(
        list_lit.leading && list_lit.precedence == Some(1024) && list_lit.scope.is_none(),
        "unexpected `«term[_]»` registration metadata: {list_lit:?}"
    );
    assert!(
        list_basic.imported_parser_count() >= 400,
        "expected full 15-module Init.Data.List.Basic parser closure, got {}",
        list_basic.imported_parser_count()
    );
    let expected_list_tokens = reference_census()
        .tokens_for(true, &[name("Init.Data.List.Basic")])
        .expect("Init.Data.List.Basic in census");
    assert_eq!(
        list_basic.global_tokens(),
        &expected_list_tokens,
        "Init.Data.List.Basic decoded token set must equal the oracle's 351-token closure"
    );
    assert_ne!(
        prelude.digest(),
        list_basic.digest(),
        "distinct closures must produce distinct canonical registry digests"
    );
    eprintln!(
        "actual pinned .olean closures decoded cleanly: Init.Prelude (tokens={}, imported_parsers={}, digest={}) vs Init.Data.List.Basic (tokens={}, imported_parsers={}, digest={})",
        prelude.global_tokens().len(),
        prelude.imported_parser_count(),
        prelude.digest().to_hex(),
        list_basic.global_tokens().len(),
        list_basic.imported_parser_count(),
        list_basic.digest().to_hex(),
    );
}

#[test]
fn olean_closure_syntax_registry_decoding_is_deterministic_across_threads() {
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required for multi-thread registry determinism"
        );
        eprintln!("SKIP: multi-thread .olean registry determinism test requires FLN_REFERENCE_LIB");
        return;
    };

    let single = build_closure_registry_from_pin(&lib, &["Init.Data.List.Basic"]);
    let single_digest = single.digest();

    let worker_results: Vec<ClosureSyntaxRegistry> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..8)
            .map(|_| {
                scope.spawn(|| build_closure_registry_from_pin(&lib, &["Init.Data.List.Basic"]))
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("registry decoder thread panicked"))
            .collect()
    });

    for (idx, worker) in worker_results.iter().enumerate() {
        assert_eq!(
            worker.digest(),
            single_digest,
            "thread {idx} digest diverged from single-threaded run"
        );
        assert_eq!(
            worker, &single,
            "thread {idx} registry diverged structurally from single-threaded run"
        );
    }
    eprintln!(
        "1-thread vs 8-thread deterministic .olean registry digest verified: {}",
        single_digest.to_hex()
    );
}
