//! Actual pinned structure metadata retains complete field and parent identities.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::pin::check_pinned_header;
use fln_olean::region::{OleanView, WalkBudget};
use std::collections::BTreeSet;
use std::path::PathBuf;

const BYTES: usize = 64 * 1024 * 1024;

#[test]
fn actual_prelude_structure_journal_decodes_exact_parent_interfaces() {
    use fln_core::expr::BinderInfo;
    use fln_olean::region::OpaqueExtensionBlock;
    use fln_olean::source_extensions::{
        self, DecodeLimits, StructureEntry, StructureField, StructureParent,
    };

    let library = PathBuf::from(
        std::env::var_os("FLN_REFERENCE_LIB")
            .expect("actual pinned artifacts are mandatory; set FLN_REFERENCE_LIB"),
    );
    let path = library.join("Init/Prelude.olean");
    let exported = std::fs::read(&path).expect("actual exported Prelude");
    let server = std::fs::read(path.with_extension("olean.server")).expect("actual server Prelude");
    let private =
        std::fs::read(path.with_extension("olean.private")).expect("actual private Prelude");
    assert!(exported.len() + server.len() + private.len() <= BYTES);
    for bytes in [&exported, &server, &private] {
        check_pinned_header(bytes).expect("exact pinned artifact header");
    }
    let views = [
        OleanView::parse(&exported).unwrap(),
        OleanView::parse_with_dependencies(&server, &[&exported]).unwrap(),
        OleanView::parse_with_dependencies(&private, &[&exported, &server]).unwrap(),
    ];
    let structural_name = Name::str(
        Name::str(
            Name::num(Name::from_components(["_private", "Lean", "Structure"]), 0),
            "Lean",
        ),
        "structureExt",
    );
    assert_eq!(
        source_extensions::structure_extension_name(),
        structural_name
    );
    let cases: [(&str, &[&str], &[&str]); 8] = [
        ("Functor", &["map", "mapConst"], &[]),
        ("Pure", &["pure"], &[]),
        ("Bind", &["bind"], &[]),
        ("Seq", &["seq"], &[]),
        ("SeqLeft", &["seqLeft"], &[]),
        ("SeqRight", &["seqRight"], &[]),
        (
            "Applicative",
            &["toFunctor", "toPure", "toSeq", "toSeqLeft", "toSeqRight"],
            &["Functor", "Pure", "Seq", "SeqLeft", "SeqRight"],
        ),
        (
            "Monad",
            &["toApplicative", "toBind"],
            &["Applicative", "Bind"],
        ),
    ];
    let mut first = None;
    for view in views {
        let blocks = view
            .extension_payloads(WalkBudget::default(), BYTES)
            .expect("actual bounded metadata capture");
        let selected: Vec<_> = blocks
            .iter()
            .filter(|block| block.name == structural_name)
            .collect();
        assert_eq!(selected.len(), 1);
        let block = selected[0];
        assert_eq!(
            block.entries.len(),
            101,
            "the full pinned Prelude structure journal"
        );
        let decoded =
            source_extensions::decode(std::slice::from_ref(block), DecodeLimits::default())
                .expect("all actual structure rows decode");
        assert_eq!(decoded.structures.len(), 101);
        assert!(decoded.uninterpreted.is_empty());
        assert_eq!(
            decoded
                .structures
                .iter()
                .map(|row| &row.name)
                .collect::<BTreeSet<_>>()
                .len(),
            101,
            "every original structure identity is retained",
        );
        for (root, fields, parents) in cases {
            let expected = StructureEntry {
                name: Name::from_components([root]),
                fields: fields
                    .iter()
                    .map(|label| {
                        let subobject = label
                            .strip_prefix("to")
                            .filter(|parent| parents.contains(parent))
                            .map(|parent| Name::from_components([parent]));
                        StructureField {
                            name: Name::from_components([*label]),
                            projection: Name::from_components([root, *label]),
                            binder_info: if subobject.is_some() {
                                BinderInfo::InstImplicit
                            } else {
                                BinderInfo::Default
                            },
                            subobject,
                            auto_param: None,
                        }
                    })
                    .collect(),
                parents: parents
                    .iter()
                    .map(|parent| StructureParent {
                        name: Name::from_components([*parent]),
                        subobject: true,
                        projection: Name::from_components([root, &format!("to{parent}")]),
                    })
                    .collect(),
            };
            assert_eq!(
                decoded
                    .structures
                    .iter()
                    .find(|row| row.name == expected.name),
                Some(&expected),
                "physical fields and extends order for {root}",
            );
        }
        if let Some(first) = &first {
            assert_eq!(
                &decoded.structures, first,
                "all three parts retain the same full journal"
            );
        } else {
            first = Some(decoded.structures.clone());
        }
        // Display equality cannot activate an extension with a string "0"
        // where the private-name contract requires a numeric component.
        let alias = OpaqueExtensionBlock {
            name: Name::from_components([
                "_private",
                "Lean",
                "Structure",
                "0",
                "Lean",
                "structureExt",
            ]),
            entries: block.entries.clone(),
        };
        assert_ne!(alias.name, structural_name);
        let refused_alias =
            source_extensions::decode(std::slice::from_ref(&alias), DecodeLimits::default())
                .unwrap();
        assert!(refused_alias.structures.is_empty());
        assert_eq!(refused_alias.uninterpreted, vec![alias.name]);
        let error = source_extensions::decode(
            std::slice::from_ref(block),
            DecodeLimits {
                max_entries: 100,
                ..DecodeLimits::default()
            },
        )
        .expect_err("the real101 rows cannot fit a100-entry decoder budget");
        assert!(error.is_resource(), "{error:?}");
    }
    assert_actual_prop_projection_interfaces(
        &exported,
        &server,
        &private,
        first
            .as_deref()
            .expect("the complete actual structure journal"),
    );
}

fn assert_actual_prop_projection_interfaces(
    exported: &[u8],
    server: &[u8],
    private: &[u8],
    structures: &[fln_olean::source_extensions::StructureEntry],
) {
    use fln_core::expr::{BinderInfo, Expr, ExprNode};
    use fln_core::level::Level;
    use fln_env::constants::ConstantInfo;
    use fln_olean::decl::{ChainLimits, decode_chain_constants_from_parts};

    let decoded =
        decode_chain_constants_from_parts(exported, server, private, ChainLimits::new(BYTES))
            .expect("actual proof-structure declarations decode within the original byte bound");
    let declaration = |label: &str| {
        let name = Name::from_components(label.split('.'));
        let mut matching = decoded.constants.iter().filter(|info| info.name() == &name);
        let info = matching
            .next()
            .unwrap_or_else(|| panic!("actual proof-structure declaration is required: {label}"));
        assert!(
            matching.next().is_none(),
            "unique actual declaration: {label}"
        );
        info
    };
    let and_name = Name::from_components(["And"]);
    let ConstantInfo::Induct(and) = declaration("And") else {
        panic!("the actual And interface is an inductive family");
    };
    assert_eq!(and.num_params, 2);
    assert_eq!(and.num_indices, 0);
    assert!(!and.is_unsafe);
    assert!(and.base.level_params.is_empty());
    assert_eq!(and.ctors, vec![Name::from_components(["And", "intro"])]);
    let ConstantInfo::Ctor(constructor) = declaration("And.intro") else {
        panic!("the actual And.intro interface is a constructor");
    };
    assert_eq!(constructor.induct, and_name);
    assert_eq!(constructor.num_params, 2);
    assert_eq!(constructor.num_fields, 2);
    assert!(!constructor.is_unsafe);
    assert!(constructor.base.level_params.is_empty());
    let metadata = structures
        .iter()
        .find(|row| row.name == and_name)
        .expect("the real101-row journal retains the proof-valued And structure");
    assert!(metadata.parents.is_empty());
    assert_eq!(metadata.fields.len(), 2);
    let proposition = Expr::sort(Level::zero());
    let receiver = Expr::app(
        Expr::app(
            Expr::const_(and_name.clone(), vec![]),
            Expr::bvar(1).unwrap(),
        ),
        Expr::bvar(0).unwrap(),
    );
    for (label, index, result_index) in [("left", 0_u64, 2_u32), ("right", 1, 1)] {
        let field = &metadata.fields[index as usize];
        let projection = Name::from_components(["And", label]);
        assert_eq!(field.name, Name::from_components([label]));
        assert_eq!(field.projection, projection);
        assert_eq!(field.binder_info, BinderInfo::Default);
        assert!(field.subobject.is_none());
        assert!(field.auto_param.is_none());
        let ConstantInfo::Thm(theorem) = declaration(&format!("And.{label}")) else {
            panic!("the actual proof-valued And.{label} projection is a theorem");
        };
        assert_eq!(theorem.base.name, projection);
        assert!(theorem.base.level_params.is_empty());
        let mut value = &theorem.value;
        let mut type_ = &theorem.base.type_;
        for expected_domain in [&proposition, &proposition, &receiver] {
            let ExprNode::Lam {
                binder_type, body, ..
            } = value.node()
            else {
                panic!("the actual proof projection has two parameters and a receiver");
            };
            assert_eq!(binder_type, expected_domain);
            value = body;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                panic!("the actual proof projection type retains the same three domains");
            };
            assert_eq!(binder_type, expected_domain);
            type_ = body;
        }
        assert!(
            matches!(
                value.node(),
                ExprNode::Proj { struct_name, idx, expr }
                    if struct_name == &and_name
                        && *idx == index
                        && matches!(expr.node(), ExprNode::BVar { idx: 0 })
            ),
            "the admitted theorem body projects the exact original physical field",
        );
        assert_eq!(type_, &Expr::bvar(result_index).unwrap());
    }
}
