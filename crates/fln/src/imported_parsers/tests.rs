//! Codec/registry ownership-boundary fixtures, not admission or parity evidence.
//!
//! Datatype rows are generated candidates, module envelopes pass the actual
//! codec, and ownership/import markers are synthetic. The public source/macro
//! integration tests separately exercise genuine artifact admission. These
//! cells isolate reference resolution and stale projected-environment binding.
use super::test_wire as wire;
use super::*;
use crate::{OleanDecodeLimits, decode_olean_artifact};
use fln_core::expr::{BinderInfo, Literal, NatLit};
use fln_core::level::Level;
use fln_core::options::KVMap;
use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints};
use fln_kernel::Declaration;
use fln_olean::format;
use fln_olean::region::ModuleImport;
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};
use fln_parse::extensions::Descr;
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::compact;
use std::sync::OnceLock;

// Keep the former macro-local reader's file as tests of the authoritative
// parser registry; production has one reconstruction and ownership path.
#[path = "../imported_macros/registrations/parsers.rs"]
mod macro_bindings;

fn c(symbol: &str) -> Expr {
    Expr::const_(name(symbol), vec![])
}

fn app(symbol: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(c(symbol), Expr::app)
}

fn text(value: &str) -> Expr {
    Expr::lit(Literal::Str(value.into()))
}

fn number(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn literal_name(symbol: &str) -> Expr {
    symbol
        .split('.')
        .fold(c("Lean.Name.anonymous"), |prefix, part| {
            app("Lean.Name.str", [prefix, text(part)])
        })
}

fn definition(symbol: &str, type_: &str, value: Expr) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(symbol),
            level_params: vec![],
            type_: c(type_),
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(symbol)],
    })
}

fn flatten(declaration: Declaration) -> Vec<ConstantInfo> {
    match declaration {
        Declaration::Axiom(value) => vec![ConstantInfo::Axiom(value)],
        Declaration::Defn(value) => vec![ConstantInfo::Defn(value)],
        Declaration::Inductive(block) => block
            .types
            .into_iter()
            .map(ConstantInfo::Induct)
            .chain(block.ctors.into_iter().map(ConstantInfo::Ctor))
            .chain(block.recursors.into_iter().map(ConstantInfo::Rec))
            .collect(),
        _ => panic!("fixed data fixture contains only families and safe definitions"),
    }
}

fn base() -> &'static Environment {
    static BASE: OnceLock<Environment> = OnceLock::new();
    BASE.get_or_init(|| {
        [
            fln_elab::seed::nat_inductive_seed_declaration(),
            fln_elab::seed::string_seed_declaration(),
            fln_elab::seed::bool_seed_declaration(),
        ]
        .into_iter()
        .chain(fixture_declarations())
        .flat_map(flatten)
        .fold(Environment::new(), |environment, constant| {
            environment.add_decl(constant).unwrap()
        })
    })
}

fn checked(symbol: &str, constants: &[ConstantInfo], imports: &[&str]) -> CheckedOleanModule {
    let imports: Vec<_> = imports
        .iter()
        .map(|module| ModuleImport {
            module: name(module),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let bytes = encode_module(
        ModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: format::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: format::PIN_COMMIT,
            base_addr: (format::REGION_ALIGN * 2) as u64,
        },
        WriteBudget::default(),
    )
    .unwrap()
    .bytes;
    let decoded = decode_olean_artifact(&bytes, OleanDecodeLimits::new(bytes.len())).unwrap();
    let root = base().logical_root(&KVMap::new());
    CheckedOleanModule {
        name: name(symbol),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: vec![],
    }
}

fn environment(modules: &[&CheckedOleanModule]) -> Environment {
    modules
        .iter()
        .flat_map(|module| &module.decoded.constants)
        .fold(base().clone(), |environment, constant| {
            environment.add_decl(constant.clone()).unwrap()
        })
}

fn projected_engine(environment: Environment, modules: &[Name]) -> Engine {
    // Deliberately synthetic ownership markers for the projection boundary.
    let mut engine = Engine::from_environment(environment);
    engine.imported_modules = Arc::new(modules.iter().cloned().collect());
    engine
}

fn journal(declaration: &str, kind: &str) -> Vec<OpaqueExtensionBlock> {
    let rows = [
        Obj::mk_ctor(wire::PARSER_ENTRY_KIND, vec![inject_name(&name(kind))], &[]),
        Obj::mk_ctor(
            wire::PARSER_ENTRY_PARSER,
            vec![
                inject_name(&name("term")),
                inject_name(&name(declaration)),
                Obj::mk_nat(1000),
            ],
            &[],
        ),
    ];
    vec![OpaqueExtensionBlock {
        name: parsers::extension_name(),
        entries: rows
            .into_iter()
            .map(|row| compact(&Obj::mk_ctor(wire::SCOPE_GLOBAL, vec![row], &[]), 0).unwrap())
            .collect(),
    }]
}

fn node(kind: &str, body: Expr) -> Expr {
    app(
        "Lean.ParserDescr.node",
        [literal_name(kind), number(1022), body],
    )
}

fn reference(target: &str) -> Expr {
    app("Lean.ParserDescr.parser", [literal_name(target)])
}

#[test]
fn named_parser_descriptions_inline_the_checked_dependency_value() {
    let dependency = checked(
        "Dependency",
        &[definition(
            "Dependency.tail",
            "Lean.ParserDescr",
            app("Lean.ParserDescr.symbol", [text("@")]),
        )],
        &[],
    );
    let consumer = checked(
        "Consumer",
        &[definition(
            "Consumer.rule",
            "Lean.ParserDescr",
            node("Consumer.syntax", reference("Dependency.tail")),
        )],
        &["Dependency"],
    );
    let rows = journal("Consumer.rule", "Consumer.syntax");
    let admitted = environment(&[&dependency, &consumer]);
    let registry = RegisteredParsers::prepare(
        &[
            ParserRegistrationModule {
                checked: &dependency,
                extensions: &[],
            },
            ParserRegistrationModule {
                checked: &consumer,
                extensions: &rows,
            },
        ],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap();
    let imports = [name("Dependency"), name("Consumer")];
    let syntax = registry
        .project_imports(&imports, &projected_engine(admitted, &imports))
        .unwrap();
    let declarations: Vec<_> = syntax
        .entries
        .iter()
        .filter_map(|entry| match entry {
            ImportedSyntaxEntry::Parser(declaration) => Some(declaration),
            _ => None,
        })
        .collect();
    assert_eq!(declarations.len(), 1);
    assert!(declarations[0].leading);
    assert_eq!(
        declarations[0].descr,
        Descr::Node {
            kind: name("Consumer.syntax"),
            prec: 1022,
            body: Box::new(Descr::Symbol("@".into())),
        }
    );
}

#[test]
fn parser_references_refuse_cycles_and_visible_but_unimported_siblings() {
    let cycle = checked(
        "Loop",
        &[
            definition("Loop.a", "Lean.ParserDescr", reference("Loop.b")),
            definition("Loop.b", "Lean.ParserDescr", reference("Loop.a")),
        ],
        &[],
    );
    let rows = journal("Loop.a", "Loop.syntax");
    let admitted = environment(&[&cycle]);
    assert!(matches!(
        RegisteredParsers::prepare(
            &[ParserRegistrationModule {
                checked: &cycle,
                extensions: &rows
            },],
            &admitted,
            ParserRegistryLimits::default()
        ),
        Err(ParserRegistrationError::Description {
            reason: "cyclic parser description reference",
            ..
        })
    ));

    let foreign = checked(
        "Foreign",
        &[definition(
            "Foreign.tail",
            "Lean.ParserDescr",
            app("Lean.ParserDescr.symbol", [text("foreign")]),
        )],
        &[],
    );
    let consumer = checked(
        "Consumer",
        &[definition(
            "Consumer.rule",
            "Lean.ParserDescr",
            node("Consumer.syntax", reference("Foreign.tail")),
        )],
        &[],
    );
    let rows = journal("Consumer.rule", "Consumer.syntax");
    let admitted = environment(&[&foreign, &consumer]);
    assert!(matches!(RegisteredParsers::prepare(&[
        ParserRegistrationModule { checked: &foreign, extensions: &[] },
        ParserRegistrationModule { checked: &consumer, extensions: &rows },
    ], &admitted, ParserRegistryLimits::default()),
        Err(ParserRegistrationError::Owner { declaration, reason, .. })
        if declaration == name("Foreign.tail")
            && reason == "description dependency is outside its checked import closure"));
}

#[test]
fn nested_data_owner_cannot_borrow_a_sibling_from_the_consumers_wider_world() {
    let right = checked(
        "Right",
        &[definition(
            "Right.value",
            "Lean.ParserDescr",
            app("Lean.ParserDescr.symbol", [text("right")]),
        )],
        &[],
    );
    let left = checked(
        "Left",
        &[definition(
            "Left.value",
            "Lean.ParserDescr",
            c("Right.value"),
        )],
        &[],
    );
    let consumer = checked(
        "Consumer",
        &[definition(
            "Consumer.rule",
            "Lean.ParserDescr",
            node("Consumer.syntax", c("Left.value")),
        )],
        &["Left", "Right"],
    );
    let rows = journal("Consumer.rule", "Consumer.syntax");
    let admitted = environment(&[&right, &left, &consumer]);
    let error = RegisteredParsers::prepare(
        &[
            ParserRegistrationModule {
                checked: &right,
                extensions: &[],
            },
            ParserRegistrationModule {
                checked: &left,
                extensions: &[],
            },
            ParserRegistrationModule {
                checked: &consumer,
                extensions: &rows,
            },
        ],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap_err();
    assert!(
        matches!(error, ParserRegistrationError::Owner { declaration, reason, .. }
        if declaration == name("Right.value") && reason == "description dependency is outside its checked import closure")
    );
}

#[test]
fn imported_data_function_retains_the_callers_legitimate_argument_world() {
    let right = checked(
        "Right",
        &[definition(
            "Right.value",
            "Lean.ParserDescr",
            app("Lean.ParserDescr.symbol", [text("right")]),
        )],
        &[],
    );
    let mut helper = definition(
        "Left.pass",
        "Lean.ParserDescr",
        Expr::lam(
            name("value"),
            c("Lean.ParserDescr"),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
    );
    if let ConstantInfo::Defn(helper) = &mut helper {
        helper.base.type_ = Expr::forall_e(
            name("value"),
            c("Lean.ParserDescr"),
            c("Lean.ParserDescr"),
            BinderInfo::Default,
        );
    }
    let left = checked("Left", &[helper], &[]);
    let consumer = checked(
        "Consumer",
        &[definition(
            "Consumer.rule",
            "Lean.ParserDescr",
            node("Consumer.syntax", app("Left.pass", [c("Right.value")])),
        )],
        &["Left", "Right"],
    );
    let rows = journal("Consumer.rule", "Consumer.syntax");
    let admitted = environment(&[&right, &left, &consumer]);
    let registry = RegisteredParsers::prepare(
        &[
            ParserRegistrationModule {
                checked: &right,
                extensions: &[],
            },
            ParserRegistrationModule {
                checked: &left,
                extensions: &[],
            },
            ParserRegistrationModule {
                checked: &consumer,
                extensions: &rows,
            },
        ],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap();
    let modules = [name("Right"), name("Left"), name("Consumer")];
    let product = registry
        .project_imports(&modules, &projected_engine(admitted, &modules))
        .unwrap();
    assert!(
        matches!(&product.entries[1], ImportedSyntaxEntry::Parser(parser)
        if matches!(&parser.descr, Descr::Node { body, .. } if **body == Descr::Symbol("right".into())))
    );
}

fn category_journal(declaration: &str) -> Vec<OpaqueExtensionBlock> {
    let mut pointers: Vec<_> = (0..wire::PARSER_CATEGORY_POINTERS)
        .map(|_| Obj::mk_nat(0))
        .collect();
    pointers[wire::PARSER_CATEGORY_CAT_NAME] = inject_name(&name("userCategory"));
    pointers[wire::PARSER_CATEGORY_DECL_NAME] = inject_name(&name(declaration));
    let mut scalars = vec![0; wire::PARSER_CATEGORY_SCALAR_BYTES];
    scalars[wire::PARSER_CATEGORY_BEHAVIOR_SCALAR] = wire::PARSER_IDENT_DEFAULT;
    let row = Obj::mk_ctor(wire::PARSER_ENTRY_CATEGORY, pointers, &scalars);
    let mut scope: Vec<_> = (0..wire::PARSER_SCOPE_GLOBAL_POINTERS)
        .map(|_| Obj::mk_nat(0))
        .collect();
    scope[wire::PARSER_SCOPE_GLOBAL_ENTRY] = row;
    vec![OpaqueExtensionBlock {
        name: parsers::extension_name(),
        entries: vec![compact(&Obj::mk_ctor(wire::SCOPE_GLOBAL, scope, &[]), 0).unwrap()],
    }]
}

#[test]
fn category_rows_require_the_checked_category_marker_type() {
    use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
    use fln_elab::records::RecordBudget;
    let family = inductive_declaration(
        &InductiveSpec {
            name: name("Lean.Parser.Category"),
            level_params: vec![],
            parameters: vec![],
            indices: vec![],
            constructors: vec![ConstructorSpec {
                name: name("mk"),
                fields: vec![],
                result_indices: vec![],
            }],
            result_level: Level::one(),
        },
        RecordBudget::default(),
    )
    .unwrap();
    let family = checked("CategoryBase", &flatten(family), &[]);
    let good = checked(
        "Good",
        &[definition(
            "Good.category",
            "Lean.Parser.Category",
            c("Lean.Parser.Category.mk"),
        )],
        &["CategoryBase"],
    );
    let rows = category_journal("Good.category");
    let admitted = environment(&[&family, &good]);
    let registry = RegisteredParsers::prepare(
        &[
            ParserRegistrationModule {
                checked: &family,
                extensions: &[],
            },
            ParserRegistrationModule {
                checked: &good,
                extensions: &rows,
            },
        ],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap();
    let modules = [name("CategoryBase"), name("Good")];
    let product = registry
        .project_imports(&modules, &projected_engine(admitted, &modules))
        .unwrap();
    assert!(
        matches!(&product.entries[0], ImportedSyntaxEntry::Category { declaration, .. } if *declaration == name("Good.category"))
    );
    let wrong = checked(
        "Wrong",
        &[definition("Wrong.category", "Nat", number(0))],
        &["CategoryBase"],
    );
    let rows = category_journal("Wrong.category");
    let admitted = environment(&[&family, &wrong]);
    assert!(matches!(
        RegisteredParsers::prepare(
            &[
                ParserRegistrationModule {
                    checked: &family,
                    extensions: &[]
                },
                ParserRegistrationModule {
                    checked: &wrong,
                    extensions: &rows
                },
            ],
            &admitted,
            ParserRegistryLimits::default()
        ),
        Err(ParserRegistrationError::Owner {
            reason: "category owner is not a safe monomorphic Lean.Parser.Category definition",
            ..
        })
    ));
}

#[test]
fn projection_binds_the_trailing_type_alias_and_literal_helpers() {
    let module = checked(
        "Trailing",
        &[
            definition(
                "Trailing.kind",
                "Lean.Name",
                literal_name("Trailing.syntax"),
            ),
            definition(
                "Trailing.rule",
                "Lean.TrailingParserDescr",
                app(
                    "Lean.ParserDescr.trailingNode",
                    [
                        c("Trailing.kind"),
                        number(65),
                        number(65),
                        app("Lean.ParserDescr.symbol", [text("~")]),
                    ],
                ),
            ),
        ],
        &[],
    );
    let rows = journal("Trailing.rule", "Trailing.syntax");
    let admitted = environment(&[&module]);
    let registry = RegisteredParsers::prepare(
        &[ParserRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap();
    let imports = [name("Trailing")];
    let syntax = registry
        .project_imports(&imports, &projected_engine(admitted.clone(), &imports))
        .unwrap();
    assert!(syntax.entries.iter().any(|entry| matches!(entry,
        ImportedSyntaxEntry::Parser(declaration) if !declaration.leading)));

    for changed in ["Lean.TrailingParserDescr", "Trailing.kind"] {
        let altered =
            admitted
                .constants()
                .fold(Environment::new(), |environment, (symbol, constant)| {
                    let mut constant = constant.clone();
                    if symbol == &name(changed) {
                        let ConstantInfo::Defn(definition) = &mut constant else {
                            panic!("the bound fixture dependency is a definition");
                        };
                        definition.value = if changed == "Trailing.kind" {
                            literal_name("Changed.syntax")
                        } else {
                            // Still a valid type alias, but a different admitted body.
                            Expr::let_e(
                                name("unused"),
                                c("Nat"),
                                number(0),
                                c("Lean.ParserDescr"),
                                true,
                            )
                        };
                    }
                    environment.add_decl(constant).unwrap()
                });
        assert!(
            matches!(registry.project_imports(&imports, &projected_engine(altered, &imports)),
            Err(ParserRegistrationError::Owner { declaration, reason, .. })
            if declaration == name(changed)
                && reason == "source engine differs from the checked parser dependency")
        );
    }
}
