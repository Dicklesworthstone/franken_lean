#![forbid(unsafe_code)]

use fln_checker::universe::{NormalId, NormalNode, NormalizedLevel, levels_equal, normalize};
use fln_checker::wire::{DecodeBudget, DecodeOutcome, NamePart, WireLevel, WireName, decode_level};
use fln_core::level::{LMVarId, Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_LEVEL};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Shape {
    Zero,
    Succ(Box<Shape>),
    Max(Box<Shape>, Box<Shape>),
    IMax(Box<Shape>, Box<Shape>),
    Parameter(Vec<NamePart>),
    Meta(Vec<NamePart>),
}

fn primary_name(name: &Name) -> Vec<NamePart> {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    loop {
        let part = match cursor.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(value) => NamePart::Text(value.to_owned()),
            LeafView::Num(value) => NamePart::Numeric {
                value,
                overflowed: cursor.component_overflowed(),
            },
        };
        parts.push(part);
        cursor = cursor.parent();
    }
    parts.reverse();
    parts
}

fn primary_shape(level: &Level) -> Shape {
    match level.view() {
        LevelView::Zero => Shape::Zero,
        LevelView::Succ(child) => Shape::Succ(Box::new(primary_shape(child))),
        LevelView::Max(left, right) => Shape::Max(
            Box::new(primary_shape(left)),
            Box::new(primary_shape(right)),
        ),
        LevelView::IMax(left, right) => Shape::IMax(
            Box::new(primary_shape(left)),
            Box::new(primary_shape(right)),
        ),
        LevelView::Param(name) => Shape::Parameter(primary_name(name)),
        LevelView::MVar(id) => Shape::Meta(primary_name(&id.0)),
    }
}

fn checker_name(name: &WireName) -> Vec<NamePart> {
    name.parts().to_vec()
}

fn checker_shape(level: &NormalizedLevel, id: NormalId) -> Shape {
    match level.node(id).expect("normal arena id") {
        NormalNode::Zero => Shape::Zero,
        NormalNode::Succ(child) => Shape::Succ(Box::new(checker_shape(level, *child))),
        NormalNode::Max(left, right) => Shape::Max(
            Box::new(checker_shape(level, *left)),
            Box::new(checker_shape(level, *right)),
        ),
        NormalNode::IMax(left, right) => Shape::IMax(
            Box::new(checker_shape(level, *left)),
            Box::new(checker_shape(level, *right)),
        ),
        NormalNode::Parameter(name) => Shape::Parameter(checker_name(name)),
        NormalNode::Meta(name) => Shape::Meta(checker_name(name)),
    }
}

fn decoded(level: &Level) -> WireLevel {
    let result = match decode_level(&level.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(level)) => Ok(level),
        other => Err(format!("primary-produced level did not decode: {other:?}")),
    };
    result.expect("primary-produced level must decode")
}

fn p(value: &str) -> Level {
    Level::param(Name::str(Name::anonymous(), value))
}

fn generated_levels() -> Vec<Level> {
    let mut levels = vec![
        Level::zero(),
        Level::one(),
        p("u"),
        p("v"),
        Level::param(Name::num(Name::str(Name::anonymous(), "z"), 1)),
        Level::param(Name::str(Name::str(Name::anonymous(), "a"), "x")),
        Level::mvar(LMVarId(Name::str(Name::anonymous(), "m"))),
    ];
    for _ in 0..3 {
        let seed: Vec<Level> = levels.iter().take(14).cloned().collect();
        for level in &seed {
            levels.push(level.clone().succ().expect("generated depth"));
        }
        for left in seed.iter().take(8) {
            for right in seed.iter().take(8) {
                levels.push(Level::max(left.clone(), right.clone()).expect("generated depth"));
                levels.push(Level::imax(left.clone(), right.clone()).expect("generated depth"));
            }
        }
    }
    levels
}

#[test]
fn one_pass_normal_forms_match_the_primary_on_a_generated_constructor_corpus() {
    let levels = generated_levels();
    assert!(levels.len() > 300);
    for (index, level) in levels.iter().enumerate() {
        let ours = normalize(&decoded(level)).expect("checker normalization");
        assert_eq!(
            checker_shape(&ours, ours.root()),
            primary_shape(&level.normalize()),
            "one-pass form drift at generated level {index}: {level:?}"
        );
    }
}

#[test]
fn universe_equality_matches_the_primary_relation_pairwise() {
    let levels = generated_levels();
    let sample: Vec<&Level> = levels.iter().step_by(11).take(48).collect();
    for (left_index, left) in sample.iter().enumerate() {
        let left_wire = decoded(left);
        for (right_index, right) in sample.iter().enumerate() {
            let right_wire = decoded(right);
            assert_eq!(
                levels_equal(&left_wire, &right_wire).expect("checker equality"),
                left.is_equiv(right),
                "equality drift at sample pair ({left_index}, {right_index})"
            );
        }
    }
}

#[test]
fn imax_collapse_and_never_bottom_conversion_kill_distinct_mutants() {
    let u = p("u");
    let v = p("v");
    let zero = Level::zero();
    let one = Level::one();
    let successor_v = v.clone().succ().expect("shallow");

    for (left, right, expected) in [
        (
            Level::imax(u.clone(), zero.clone()).expect("shallow"),
            zero.clone(),
            "imax-u-zero",
        ),
        (
            Level::imax(one, u.clone()).expect("shallow"),
            u.clone(),
            "imax-one-u",
        ),
        (
            Level::imax(u.clone(), successor_v.clone()).expect("shallow"),
            Level::max(u.clone(), successor_v).expect("shallow"),
            "never-bottom-right-becomes-max",
        ),
    ] {
        assert!(
            levels_equal(&decoded(&left), &decoded(&right)).expect("checker equality"),
            "{expected}"
        );
    }

    let contingent = Level::imax(u.clone(), v.clone()).expect("shallow");
    let unconditional = Level::max(u, v).expect("shallow");
    assert!(
        !levels_equal(&decoded(&contingent), &decoded(&unconditional)).expect("checker equality"),
        "treating every imax as max is a spec divergence"
    );
}

#[test]
fn equality_preserves_the_pins_one_pass_incompleteness() {
    let u = p("u");
    let v = p("v");
    let x = Level::imax(v, u.succ().expect("shallow"))
        .expect("shallow")
        .succ()
        .expect("shallow");
    let twice = x.normalize().normalize();

    assert!(!x.is_equiv(&twice));
    assert!(
        !levels_equal(&decoded(&x), &decoded(&twice)).expect("checker equality"),
        "a fixpoint implementation would disagree with KR-501 here"
    );
    let once = x.normalize();
    assert!(once.is_equiv(&twice));
    assert!(levels_equal(&decoded(&once), &decoded(&twice)).expect("checker equality"));
}

#[test]
fn deep_successor_normalization_uses_heap_worklists_and_flat_destruction() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_LEVEL);
    for _ in 0..DEPTH {
        writer.u8(1);
    }
    writer.u8(0);

    let decoded = match decode_level(
        &writer.into_bytes(),
        DecodeBudget::new(u64::MAX, DEPTH as u64 + 1),
    ) {
        DecodeOutcome::Complete(Ok(level)) => level,
        DecodeOutcome::Complete(Err(error)) => {
            return Err(format!("deep level was malformed: {error:?}"));
        }
        DecodeOutcome::Inconclusive(stop) => {
            return Err(format!("deep level was inconclusive: {stop:?}"));
        }
    };
    let normalized =
        normalize(&decoded).map_err(|error| format!("deep normalization failed: {error:?}"))?;
    assert_eq!(normalized.nodes().len(), DEPTH + 1);
    assert!(matches!(
        normalized.node(normalized.root()),
        Some(NormalNode::Succ(_))
    ));
    Ok(())
}

#[test]
fn universe_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/universe.rs");
    for forbidden in ["fln_core::", "is_equiv", "normalize_fixpoint", "is_zero"] {
        assert!(
            !source.contains(forbidden),
            "checker universe source shares forbidden semantic path `{forbidden}`"
        );
    }
}
