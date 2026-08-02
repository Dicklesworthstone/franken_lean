#![forbid(unsafe_code)]

use fln_checker::wire::{
    BinderStyle, DecodeBudget, DecodeLimit, DecodeOutcome, DecodeStop, ExprNode, LevelNode,
    MalformedKind, MetadataValue, NamePart, decode_expr, decode_expr_with, decode_level,
    decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_EXPR, SCHEMA_LEVEL, SCHEMA_NAME};

fn complete<T>(outcome: DecodeOutcome<T>) -> Result<T, String> {
    match outcome {
        DecodeOutcome::Complete(result) => result.map_err(|error| format!("{error:?}")),
        DecodeOutcome::Inconclusive(stop) => Err(format!("inconclusive: {stop:?}")),
    }
}

fn malformed<T>(outcome: DecodeOutcome<T>) -> Option<MalformedKind> {
    match outcome {
        DecodeOutcome::Complete(Err(error)) => Some(error.kind),
        DecodeOutcome::Complete(Ok(_)) | DecodeOutcome::Inconclusive(_) => None,
    }
}

fn named() -> Name {
    Name::str(
        Name::num(Name::str(Name::anonymous(), "Checker"), 7),
        "value",
    )
}

#[test]
fn checker_owned_decoder_covers_name_level_and_expression_variants() {
    let name = named();
    let decoded_name = complete(decode_name(
        &name.to_canonical_bytes(),
        DecodeBudget::unlimited(),
    ))
    .expect("name bytes");
    assert_eq!(
        decoded_name.parts(),
        &[
            NamePart::Text("Checker".to_owned()),
            NamePart::Numeric {
                value: 7,
                overflowed: false,
            },
            NamePart::Text("value".to_owned()),
        ]
    );

    let parameter = Level::param(name.clone());
    let level = Level::imax(
        Level::max(
            parameter.clone(),
            Level::mvar(fln_core::level::LMVarId(Name::str(Name::anonymous(), "u"))),
        )
        .expect("level depth"),
        parameter.succ().expect("level depth"),
    )
    .expect("level depth");
    let decoded_level = complete(decode_level(
        &level.to_canonical_bytes(),
        DecodeBudget::unlimited(),
    ))
    .expect("level bytes");
    assert!(matches!(
        decoded_level.node(decoded_level.root()),
        Some(LevelNode::IMax(_, _))
    ));
    assert_eq!(decoded_level.nodes().len(), 6);

    let type_ = Expr::sort(Level::one());
    let application = Expr::app(
        Expr::const_(name.clone(), vec![level]),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![3, 4]))),
    );
    let locals = Expr::app(
        Expr::app(
            Expr::bvar(5).expect("bounded index"),
            Expr::fvar(FVarId(Name::str(Name::anonymous(), "free"))),
        ),
        Expr::mvar(MVarId(Name::str(Name::anonymous(), "meta"))),
    );
    let body = Expr::app(application, locals);
    let default_lambda = Expr::lam(name.clone(), type_.clone(), body, BinderInfo::Default);
    let implicit_lambda = Expr::lam(
        name.clone(),
        type_.clone(),
        default_lambda,
        BinderInfo::Implicit,
    );
    let strict_lambda = Expr::lam(
        name.clone(),
        type_.clone(),
        implicit_lambda,
        BinderInfo::StrictImplicit,
    );
    let forall = Expr::forall_e(
        name.clone(),
        type_.clone(),
        strict_lambda,
        BinderInfo::InstImplicit,
    );
    let let_expr = Expr::let_e(
        name.clone(),
        type_,
        Expr::lit(Literal::Str("wire".to_owned())),
        forall,
        true,
    );
    let metadata = KVMap::from_entries(vec![
        (
            Name::str(Name::anonymous(), "text"),
            DataValue::OfString("metadata".to_owned()),
        ),
        (name.clone(), DataValue::OfBool(true)),
        (
            Name::str(Name::anonymous(), "name"),
            DataValue::OfName(name.clone()),
        ),
        (Name::str(Name::anonymous(), "nat"), DataValue::OfNat(42)),
        (Name::str(Name::anonymous(), "int"), DataValue::OfInt(-7)),
        (
            Name::str(Name::anonymous(), "syntax"),
            DataValue::OfSyntax(SyntaxHandle(9)),
        ),
    ]);
    let expression = Expr::proj(name, 2, Expr::mdata(metadata, let_expr));
    let decoded = complete(decode_expr(
        &expression.to_canonical_bytes(),
        DecodeBudget::unlimited(),
    ))
    .expect("expr bytes");

    assert!(matches!(
        decoded.node(decoded.root()),
        Some(ExprNode::Projection { index: 2, .. })
    ));
    assert!(
        decoded
            .nodes()
            .iter()
            .any(|node| matches!(node, ExprNode::Bound { index: 5 }))
    );
    assert!(
        decoded
            .nodes()
            .iter()
            .any(|node| matches!(node, ExprNode::Free { .. }))
    );
    assert!(
        decoded
            .nodes()
            .iter()
            .any(|node| matches!(node, ExprNode::Meta { .. }))
    );
    for style in [
        BinderStyle::Default,
        BinderStyle::Implicit,
        BinderStyle::StrictImplicit,
        BinderStyle::InstanceImplicit,
    ] {
        assert!(decoded.nodes().iter().any(|node| {
            matches!(
                node,
                ExprNode::Lambda {
                    style: found,
                    ..
                } | ExprNode::Forall {
                    style: found,
                    ..
                } if *found == style
            )
        }));
    }
    assert!(decoded.nodes().iter().any(|node| matches!(
        node,
        ExprNode::Metadata { entries, .. } if
            entries.iter().any(|(_, value)| matches!(value, MetadataValue::Text(text) if text == "metadata"))
            && entries.iter().any(|(_, value)| matches!(value, MetadataValue::Bool(true)))
            && entries.iter().any(|(_, value)| matches!(value, MetadataValue::Name(name) if !name.is_anonymous()))
            && entries.iter().any(|(_, value)| matches!(value, MetadataValue::Nat(42)))
            && entries.iter().any(|(_, value)| matches!(value, MetadataValue::Int(-7)))
            && entries.iter().any(|(_, value)| matches!(value, MetadataValue::Syntax(9)))
    )));
    assert!(
        decoded
            .nodes()
            .iter()
            .any(|node| matches!(node, ExprNode::NatLiteral { limbs_le } if limbs_le == &[3, 4]))
    );
}

#[test]
fn checker_owned_name_order_matches_the_primary_prefix_and_leaf_law() {
    let primary = [
        Name::anonymous(),
        Name::str(Name::anonymous(), "a"),
        Name::str(Name::anonymous(), "z"),
        Name::num(Name::str(Name::anonymous(), "z"), 1),
        Name::str(Name::str(Name::anonymous(), "a"), "x"),
        Name::num_overflowing(Name::str(Name::anonymous(), "a"), u64::MAX),
    ];
    let checker: Vec<_> = primary
        .iter()
        .map(|name| {
            complete(decode_name(
                &name.to_canonical_bytes(),
                DecodeBudget::unlimited(),
            ))
            .expect("primary-produced name")
        })
        .collect();

    for (left_index, left) in primary.iter().enumerate() {
        for (right_index, right) in primary.iter().enumerate() {
            assert_eq!(
                checker[left_index].cmp(&checker[right_index]),
                left.cmp(right),
                "name order drift at ({left_index}, {right_index})"
            );
        }
    }
}

#[test]
fn schema_tag_canonicality_and_trailing_bytes_are_refused_independently() {
    let mut name = Name::str(Name::anonymous(), "x").to_canonical_bytes();
    name[8] ^= 1;
    assert_eq!(
        malformed(decode_name(&name, DecodeBudget::unlimited())),
        Some(MalformedKind::SchemaName)
    );

    let mut level = Level::zero().to_canonical_bytes();
    let version_at = 8 + SCHEMA_LEVEL.name.len();
    level[version_at] = 2;
    assert_eq!(
        malformed(decode_level(&level, DecodeBudget::unlimited())),
        Some(MalformedKind::SchemaVersion)
    );

    let mut expression = Expr::sort(Level::zero()).to_canonical_bytes();
    expression.push(0);
    assert_eq!(
        malformed(decode_expr(&expression, DecodeBudget::unlimited())),
        Some(MalformedKind::TrailingBytes)
    );

    let mut unknown = CanonWriter::new();
    unknown.schema(SCHEMA_EXPR);
    unknown.u8(255);
    assert_eq!(
        malformed(decode_expr(
            &unknown.into_bytes(),
            DecodeBudget::unlimited()
        )),
        Some(MalformedKind::UnknownExprTag(255))
    );

    let mut unknown_name = CanonWriter::new();
    unknown_name.schema(SCHEMA_NAME);
    unknown_name.u64(1);
    unknown_name.u8(255);
    assert_eq!(
        malformed(decode_name(
            &unknown_name.into_bytes(),
            DecodeBudget::unlimited()
        )),
        Some(MalformedKind::UnknownNameTag(255))
    );

    let mut anonymous_component = CanonWriter::new();
    anonymous_component.schema(SCHEMA_NAME);
    anonymous_component.u64(1);
    anonymous_component.u8(0);
    assert_eq!(
        malformed(decode_name(
            &anonymous_component.into_bytes(),
            DecodeBudget::unlimited()
        )),
        Some(MalformedKind::AnonymousNameComponent)
    );

    let mut unknown_level = CanonWriter::new();
    unknown_level.schema(SCHEMA_LEVEL);
    unknown_level.u8(255);
    assert_eq!(
        malformed(decode_level(
            &unknown_level.into_bytes(),
            DecodeBudget::unlimited()
        )),
        Some(MalformedKind::UnknownLevelTag(255))
    );

    let mut binder = Expr::lam(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::bvar(0).expect("bounded index"),
        BinderInfo::Default,
    )
    .to_canonical_bytes();
    *binder.last_mut().expect("binder tag") = 255;
    assert_eq!(
        malformed(decode_expr(&binder, DecodeBudget::unlimited())),
        Some(MalformedKind::UnknownBinderTag(255))
    );

    let mut unknown_metadata = CanonWriter::new();
    unknown_metadata.schema(SCHEMA_EXPR);
    unknown_metadata.u8(11);
    unknown_metadata.u64(1);
    unknown_metadata.u64(0);
    unknown_metadata.u8(255);
    assert_eq!(
        malformed(decode_expr(
            &unknown_metadata.into_bytes(),
            DecodeBudget::unlimited()
        )),
        Some(MalformedKind::UnknownMetadataTag(255))
    );

    let mut bound = CanonWriter::new();
    bound.schema(SCHEMA_EXPR);
    bound.u8(0);
    bound.u32(1 << 20);
    assert_eq!(
        malformed(decode_expr(&bound.into_bytes(), DecodeBudget::unlimited())),
        Some(MalformedKind::BoundIndex)
    );
}

#[test]
fn invalid_utf8_bool_and_nat_forms_have_distinct_refusals() {
    let mut name = CanonWriter::new();
    name.schema(SCHEMA_NAME);
    name.u64(1);
    name.u8(1);
    name.bytes(&[0xff]);
    assert_eq!(
        malformed(decode_name(&name.into_bytes(), DecodeBudget::unlimited())),
        Some(MalformedKind::InvalidUtf8)
    );

    let mut metadata = CanonWriter::new();
    metadata.schema(SCHEMA_EXPR);
    metadata.u8(11);
    metadata.u64(1);
    metadata.u64(1);
    metadata.u8(1);
    metadata.str("k");
    metadata.u8(1);
    metadata.u8(2);
    metadata.u8(0);
    metadata.u32(0);
    assert_eq!(
        malformed(decode_expr(
            &metadata.into_bytes(),
            DecodeBudget::unlimited()
        )),
        Some(MalformedKind::NonCanonicalBool(2))
    );

    let mut nat = CanonWriter::new();
    nat.schema(SCHEMA_EXPR);
    nat.u8(9);
    nat.u64(2);
    nat.u64(4);
    nat.u64(0);
    assert_eq!(
        malformed(decode_expr(&nat.into_bytes(), DecodeBudget::unlimited())),
        Some(MalformedKind::NonCanonicalNat)
    );
}

#[test]
fn resource_and_cancellation_stops_are_nonanswers_and_recovery_is_clean() {
    let expression = Expr::app(Expr::sort(Level::zero()), Expr::sort(Level::one()));
    let bytes = expression.to_canonical_bytes();

    let input_limit = bytes.len() as u64 - 1;
    assert!(matches!(
        decode_expr(&bytes, DecodeBudget::new(input_limit, u64::MAX)),
        DecodeOutcome::Inconclusive(DecodeStop::Resource {
            limit: DecodeLimit::InputBytes,
            allowed,
            observed,
            ..
        }) if allowed == input_limit && observed == bytes.len() as u64
    ));

    assert!(matches!(
        decode_expr(&bytes, DecodeBudget::new(u64::MAX, 1)),
        DecodeOutcome::Inconclusive(DecodeStop::Resource {
            limit: DecodeLimit::ProducedUnits,
            allowed: 1,
            observed: 2,
            ..
        })
    ));

    let mut nat = CanonWriter::new();
    nat.schema(SCHEMA_EXPR);
    nat.u8(9);
    nat.u64(3);
    nat.u64(1);
    nat.u64(2);
    nat.u64(3);
    let nat_bytes = nat.into_bytes();
    assert!(matches!(
        decode_expr(&nat_bytes, DecodeBudget::new(u64::MAX, 3)),
        DecodeOutcome::Inconclusive(DecodeStop::Resource {
            limit: DecodeLimit::ProducedUnits,
            allowed: 3,
            observed: 4,
            ..
        })
    ));

    let mut polls = 0_u64;
    let cancelled = decode_expr_with(&bytes, DecodeBudget::unlimited(), || {
        polls += 1;
        polls == 4
    });
    assert!(matches!(
        cancelled,
        DecodeOutcome::Inconclusive(DecodeStop::Cancelled { .. })
    ));

    let recovered = complete(decode_expr(&bytes, DecodeBudget::unlimited()));
    assert!(recovered.is_ok());
    let recovered_nat = complete(decode_expr(&nat_bytes, DecodeBudget::unlimited()));
    assert!(recovered_nat.is_ok());
}

#[test]
fn deep_level_input_uses_heap_worklists_and_flat_destruction() {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_LEVEL);
    for _ in 0..DEPTH {
        writer.u8(1);
    }
    writer.u8(0);

    let decoded = complete(decode_level(
        &writer.into_bytes(),
        DecodeBudget::new(u64::MAX, DEPTH as u64 + 1),
    ))
    .expect("deep level");
    assert_eq!(decoded.nodes().len(), DEPTH + 1);
    assert!(matches!(
        decoded.node(decoded.root()),
        Some(LevelNode::Succ(_))
    ));
}

#[test]
fn production_decoder_uses_only_shared_schema_constants_from_the_primary_codec() {
    let source = include_str!("../src/wire.rs");
    for forbidden in [
        "CanonReader",
        "Canonical for",
        "from_canonical",
        "fln_core::expr",
        "fln_core::level",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker production decoder shares forbidden primary path `{forbidden}`"
        );
    }
    assert!(source.contains("SCHEMA_NAME"));
    assert!(source.contains("SCHEMA_LEVEL"));
    assert!(source.contains("SCHEMA_EXPR"));
}
