#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use fln_checker::policy::{
    ContentDigest, HighRiskForm, POLICY_SCHEMA, PolicyV1, RiskProfile, SelectionReason,
    VerificationPolicy,
};

fn digest(first_word: u64) -> ContentDigest {
    let mut bytes = [0_u8; 32];
    bytes[..8].copy_from_slice(&first_word.to_le_bytes());
    ContentDigest::new(bytes)
}

#[test]
fn standard_selection_is_content_seeded_and_iteration_order_independent() {
    let policy = PolicyV1;
    let forward: BTreeMap<_, _> = (0..128_u64)
        .map(|value| {
            (
                value,
                policy.decide(
                    VerificationPolicy::Standard,
                    digest(value),
                    RiskProfile::none(),
                ),
            )
        })
        .collect();
    let reverse: BTreeMap<_, _> = (0..128_u64)
        .rev()
        .map(|value| {
            (
                value,
                policy.decide(
                    VerificationPolicy::Standard,
                    digest(value),
                    RiskProfile::none(),
                ),
            )
        })
        .collect();

    assert_eq!(forward, reverse);
    assert_eq!(
        forward
            .values()
            .filter(|decision| decision.selected)
            .count(),
        8
    );
    assert!(
        forward
            .values()
            .all(|decision| decision.schema == POLICY_SCHEMA && decision.attestable)
    );
}

#[test]
fn every_registered_high_risk_form_is_an_undilutable_floor() {
    let policy = PolicyV1;
    let outside_bucket = digest(PolicyV1::STANDARD_DENOMINATOR as u64 - 1);

    for form in HighRiskForm::ALL {
        let decision = policy.decide(
            VerificationPolicy::Standard,
            outside_bucket,
            RiskProfile::only(form),
        );
        assert!(decision.selected, "{form:?} fell below the high-risk floor");
        assert_eq!(decision.reason, SelectionReason::HighRiskFloor);
        assert!(decision.risks.contains(form));
    }

    let control = policy.decide(
        VerificationPolicy::Standard,
        outside_bucket,
        RiskProfile::none(),
    );
    assert!(!control.selected);
    assert_eq!(control.reason, SelectionReason::OutsideContentBucket);
}

#[test]
fn release_and_paranoid_are_total_while_compat_bench_cannot_attest() {
    let policy = PolicyV1;
    for content in [digest(0), digest(7), digest(15), digest(u64::MAX)] {
        for mode in [VerificationPolicy::Release, VerificationPolicy::Paranoid] {
            let decision = policy.decide(mode, content, RiskProfile::none());
            assert!(decision.selected);
            assert!(decision.attestable);
            assert_eq!(decision.reason, SelectionReason::FullPolicy);
        }

        let benchmark = policy.decide(
            VerificationPolicy::CompatBench,
            content,
            RiskProfile::none(),
        );
        assert!(!benchmark.attestable);
        assert_eq!(
            benchmark.selected,
            benchmark.bucket < PolicyV1::STANDARD_NUMERATOR
        );
    }
}

#[test]
fn combining_risks_is_set_like_and_does_not_change_content_identity() {
    let risks = RiskProfile::only(HighRiskForm::Recursor)
        .with(HighRiskForm::DeepUniverse)
        .with(HighRiskForm::Recursor);
    assert!(risks.contains(HighRiskForm::Recursor));
    assert!(risks.contains(HighRiskForm::DeepUniverse));
    assert_eq!(risks.bits().count_ones(), 2);

    let decision = PolicyV1.decide(VerificationPolicy::Standard, digest(15), risks);
    assert_eq!(decision.content.bytes(), digest(15).bytes());
    assert_eq!(decision.reason, SelectionReason::HighRiskFloor);
}
