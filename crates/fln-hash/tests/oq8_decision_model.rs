#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use fln_core::expr::{BinderInfo, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::certificate::{
    DeclarationKindV1, LEAN4EXPORT_FORMAT_VERSION, LEAN4EXPORT_REVISION, Lean4ExportRowV1,
    Oq8FieldV1, Oq8ProjectionV1, TermNodeId, TermNodeV1, lean4export_row_for_declaration,
    lean4export_row_for_term, oq8_projection,
};

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

#[test]
fn every_internal_field_has_an_explicit_nondropping_projection() {
    let mut seen = BTreeSet::new();
    for field in Oq8FieldV1::ALL {
        assert!(seen.insert(format!("{field:?}")));
        match field {
            Oq8FieldV1::TermDag | Oq8FieldV1::Judgment => assert_eq!(
                oq8_projection(field),
                Oq8ProjectionV1::Lean4ExportKernelLanguage
            ),
            Oq8FieldV1::Extensions => assert_eq!(
                oq8_projection(field),
                Oq8ProjectionV1::RefuseWithoutRegisteredMapping
            ),
            _ => assert_eq!(oq8_projection(field), Oq8ProjectionV1::CertificateSidecar),
        }
    }
    assert_eq!(seen.len(), Oq8FieldV1::ALL.len());
}

#[test]
fn lean4export_version_and_row_inventory_are_frozen() {
    assert_eq!(LEAN4EXPORT_FORMAT_VERSION, "3.1.0");
    assert_eq!(
        LEAN4EXPORT_REVISION,
        "4e7915201d3f9f04470d9eae002fa695f7cdc589"
    );

    let names = Lean4ExportRowV1::ALL
        .into_iter()
        .map(|row| format!("{row:?}"))
        .collect::<BTreeSet<_>>();
    assert_eq!(names.len(), Lean4ExportRowV1::ALL.len());
    assert!(names.contains("Meta"));
    assert!(names.contains("ExprMetadata"));
    assert!(names.contains("InductiveGroup"));
}

#[test]
fn every_internal_term_constructor_maps_to_one_export_row() {
    let nodes = [
        (TermNodeV1::BVar { index: 0 }, Lean4ExportRowV1::ExprBVar),
        (
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            Lean4ExportRowV1::ExprSort,
        ),
        (
            TermNodeV1::Const {
                name: name("Nat"),
                levels: Vec::new(),
            },
            Lean4ExportRowV1::ExprConst,
        ),
        (
            TermNodeV1::App {
                function: TermNodeId::new(0),
                argument: TermNodeId::new(0),
            },
            Lean4ExportRowV1::ExprApp,
        ),
        (
            TermNodeV1::Lam {
                binder_name: name("x"),
                binder_info: BinderInfo::Default,
                domain: TermNodeId::new(0),
                body: TermNodeId::new(0),
            },
            Lean4ExportRowV1::ExprLam,
        ),
        (
            TermNodeV1::Forall {
                binder_name: name("x"),
                binder_info: BinderInfo::Implicit,
                domain: TermNodeId::new(0),
                body: TermNodeId::new(0),
            },
            Lean4ExportRowV1::ExprForall,
        ),
        (
            TermNodeV1::Let {
                declaration_name: name("x"),
                type_node: TermNodeId::new(0),
                value_node: TermNodeId::new(0),
                body: TermNodeId::new(0),
            },
            Lean4ExportRowV1::ExprLet,
        ),
        (
            TermNodeV1::Proj {
                type_name: name("Prod"),
                index: 0,
                structure: TermNodeId::new(0),
            },
            Lean4ExportRowV1::ExprProj,
        ),
        (
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(1),
            },
            Lean4ExportRowV1::ExprNatValue,
        ),
        (
            TermNodeV1::StringLiteral {
                value: "x".to_owned(),
            },
            Lean4ExportRowV1::ExprStringValue,
        ),
    ];
    for (node, row) in nodes {
        assert_eq!(lean4export_row_for_term(&node), row);
    }
}

#[test]
fn every_declaration_class_maps_without_free_standing_ctor_or_recursor_rows() {
    let cells = [
        (DeclarationKindV1::Axiom, Lean4ExportRowV1::Axiom),
        (DeclarationKindV1::Definition, Lean4ExportRowV1::Definition),
        (DeclarationKindV1::Theorem, Lean4ExportRowV1::Theorem),
        (DeclarationKindV1::Opaque, Lean4ExportRowV1::Opaque),
        (DeclarationKindV1::Quotient, Lean4ExportRowV1::Quotient),
        (
            DeclarationKindV1::Inductive,
            Lean4ExportRowV1::InductiveGroup,
        ),
        (
            DeclarationKindV1::Constructor,
            Lean4ExportRowV1::InductiveGroup,
        ),
        (
            DeclarationKindV1::Recursor,
            Lean4ExportRowV1::InductiveGroup,
        ),
    ];
    for (kind, row) in cells {
        assert_eq!(lean4export_row_for_declaration(kind), row);
    }
}
