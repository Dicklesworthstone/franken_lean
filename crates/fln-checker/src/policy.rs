//! Versioned selection policy for the independent checker.
//!
//! This module is intentionally present before the expensive checker engine. Once a
//! second implementation costs real CPU, an unbound "sample some declarations" knob
//! would quickly become runtime randomness or a cost-biased skip. Both silently erase
//! coverage. Version 1 therefore has no entropy source and no dynamic rate setter:
//! identical declaration content and risk facts produce the same recorded decision.

/// Frozen policy schema. A semantic change requires a new versioned policy type.
pub const POLICY_SCHEMA: &str = "fln.checker.policy/1";

/// The policies registered by plan section 8.3c.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerificationPolicy {
    /// Check a content-seeded sample plus every high-risk declaration.
    Standard,
    /// Check the complete release closure.
    Release,
    /// Check every declaration, with execution-substrate diversity permitted.
    Paranoid,
    /// Sample for performance observation only; never produces attestable evidence.
    CompatBench,
}

impl VerificationPolicy {
    /// Whether a decision under this policy may contribute to an attested receipt.
    pub const fn is_attestable(self) -> bool {
        !matches!(self, VerificationPolicy::CompatBench)
    }
}

/// Stable declaration-content identity supplied by the caller.
///
/// The policy consumes an already-domain-separated digest. It does not hash again,
/// consult a process seed, or depend on iteration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentDigest([u8; 32]);

impl ContentDigest {
    pub const fn new(bytes: [u8; 32]) -> ContentDigest {
        ContentDigest(bytes)
    }

    pub const fn bytes(self) -> [u8; 32] {
        self.0
    }

    fn bucket(self) -> u16 {
        let word = u64::from_le_bytes([
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5], self.0[6], self.0[7],
        ]);
        (word % u64::from(PolicyV1::STANDARD_DENOMINATOR)) as u16
    }
}

/// Forms that always cross the independent checker in the standard policy.
///
/// This is an exhaustive, versioned inventory rather than a free-form label. Adding
/// or removing a form changes the sampling semantics and therefore requires policy
/// version 2.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum HighRiskForm {
    Recursor = 0,
    NestedOrMutualInductive = 1,
    QuotientPrimitive = 2,
    LiteralArithmetic = 3,
    DeepUniverse = 4,
    NativeReduction = 5,
}

impl HighRiskForm {
    pub const ALL: [HighRiskForm; 6] = [
        HighRiskForm::Recursor,
        HighRiskForm::NestedOrMutualInductive,
        HighRiskForm::QuotientPrimitive,
        HighRiskForm::LiteralArithmetic,
        HighRiskForm::DeepUniverse,
        HighRiskForm::NativeReduction,
    ];

    const fn bit(self) -> u8 {
        1 << (self as u8)
    }
}

/// A declaration may carry more than one high-risk form.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RiskProfile {
    bits: u8,
}

impl RiskProfile {
    pub const fn none() -> RiskProfile {
        RiskProfile { bits: 0 }
    }

    pub const fn only(form: HighRiskForm) -> RiskProfile {
        RiskProfile { bits: form.bit() }
    }

    pub const fn with(self, form: HighRiskForm) -> RiskProfile {
        RiskProfile {
            bits: self.bits | form.bit(),
        }
    }

    pub const fn contains(self, form: HighRiskForm) -> bool {
        self.bits & form.bit() != 0
    }

    pub const fn is_empty(self) -> bool {
        self.bits == 0
    }

    pub const fn bits(self) -> u8 {
        self.bits
    }
}

/// Why a declaration was or was not selected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectionReason {
    FullPolicy,
    HighRiskFloor,
    ContentBucket,
    OutsideContentBucket,
}

/// The durable semantic decision. Host, time, scheduler, and process facts do not
/// appear here; those belong in a separately linked telemetry record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SelectionDecision {
    pub schema: &'static str,
    pub policy: VerificationPolicy,
    pub content: ContentDigest,
    pub risks: RiskProfile,
    pub bucket: u16,
    pub denominator: u16,
    pub selected: bool,
    pub attestable: bool,
    pub reason: SelectionReason,
}

/// Frozen standard-policy implementation.
#[derive(Debug, Clone, Copy, Default)]
pub struct PolicyV1;

impl PolicyV1 {
    /// One ordinary declaration in sixteen is selected. The high-risk floor is
    /// independent of this bucket and cannot be diluted by changing the rate.
    pub const STANDARD_NUMERATOR: u16 = 1;
    pub const STANDARD_DENOMINATOR: u16 = 16;

    pub fn decide(
        self,
        policy: VerificationPolicy,
        content: ContentDigest,
        risks: RiskProfile,
    ) -> SelectionDecision {
        let bucket = content.bucket();
        let in_bucket = bucket < Self::STANDARD_NUMERATOR;
        let (selected, reason) = match policy {
            VerificationPolicy::Release | VerificationPolicy::Paranoid => {
                (true, SelectionReason::FullPolicy)
            }
            VerificationPolicy::Standard | VerificationPolicy::CompatBench if !risks.is_empty() => {
                (true, SelectionReason::HighRiskFloor)
            }
            VerificationPolicy::Standard | VerificationPolicy::CompatBench if in_bucket => {
                (true, SelectionReason::ContentBucket)
            }
            VerificationPolicy::Standard | VerificationPolicy::CompatBench => {
                (false, SelectionReason::OutsideContentBucket)
            }
        };

        SelectionDecision {
            schema: POLICY_SCHEMA,
            policy,
            content,
            risks,
            bucket,
            denominator: Self::STANDARD_DENOMINATOR,
            selected,
            attestable: policy.is_attestable(),
            reason,
        }
    }
}
