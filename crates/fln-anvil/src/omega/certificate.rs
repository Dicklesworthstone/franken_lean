//! Linear replay and a bounded canonical codec. Neither routine runs variable
//! selection, inequality search or witness reconstruction, and neither grants
//! proof authority: the source tactic still constructs and checks a Lean proof.

use super::*;

/// A malformed/invalid certificate is distinct from an exhausted checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateError {
    UnsupportedVersion(u32),
    InputMismatch,
    InputIndex(u32),
    Parent { step: u32, parent: u32 },
    NonPositiveScale(u32),
    ZeroDivisor(u32),
    Conclusion,
    BranchShape,
    BranchVariable(u32),
    Encoding(&'static str),
    Inconclusive(OmegaInconclusive),
}

impl From<OmegaInconclusive> for CertificateError {
    fn from(value: OmegaInconclusive) -> Self {
        Self::Inconclusive(value)
    }
}

type Checked<T> = Result<T, CertificateError>;

fn row_count(count: usize, meter: &mut Meter<'_>) -> Checked<()> {
    meter.tick(1)?;
    let limit = meter.limits.max_rows.min(u32::MAX as usize);
    if count > limit {
        return Err(Meter::limit(OmegaResource::Rows, limit, count).into());
    }
    Ok(())
}

fn parent(rows: &[LinearConstraint], step: usize, id: u32) -> Checked<&LinearConstraint> {
    rows.get(id as usize).ok_or(CertificateError::Parent {
        step: step as u32,
        parent: id,
    })
}

pub(super) fn check(
    expected: &[LinearConstraint],
    certificate: &OmegaCertificate,
    meter: &mut Meter<'_>,
) -> Checked<Vec<LinearConstraint>> {
    if certificate.version != OMEGA_CERTIFICATE_VERSION {
        return Err(CertificateError::UnsupportedVersion(certificate.version));
    }
    let dimensions = meter.dimensions(expected)?;
    meter.dimensions(&certificate.inputs)?;
    if certificate.inputs.len() != expected.len() {
        return Err(CertificateError::InputMismatch);
    }
    for (actual, expected) in certificate.inputs.iter().zip(expected) {
        if actual.coeffs.len() != expected.coeffs.len() {
            return Err(CertificateError::InputMismatch);
        }
        for (a, b) in actual
            .coeffs
            .iter()
            .chain(std::iter::once(&actual.bound))
            .zip(
                expected
                    .coeffs
                    .iter()
                    .chain(std::iter::once(&expected.bound)),
            )
        {
            meter.tick(
                a.magnitude()
                    .limbs_le()
                    .len()
                    .max(b.magnitude().limbs_le().len()) as u64
                    + 1,
            )?;
            if a != b {
                return Err(CertificateError::InputMismatch);
            }
        }
    }
    row_count(certificate.steps.len(), meter)?;
    if certificate.steps.is_empty()
        || certificate.conclusion as usize != certificate.steps.len() - 1
    {
        return Err(CertificateError::Conclusion);
    }
    let mut rows: Vec<LinearConstraint> = Vec::new();
    meter.reserve(&mut rows, certificate.steps.len())?;
    for (index, step) in certificate.steps.iter().enumerate() {
        meter.tick(1)?;
        let row = match step {
            OmegaStep::Input { index } => {
                let input = expected
                    .get(*index as usize)
                    .ok_or(CertificateError::InputIndex(*index))?;
                meter.copy_row(input, dimensions)?
            }
            OmegaStep::Combine {
                left,
                right,
                left_scale,
                right_scale,
            } => {
                if left_scale.is_zero() || right_scale.is_zero() {
                    return Err(CertificateError::NonPositiveScale(index as u32));
                }
                meter.width(left_scale.limbs_le().len())?;
                meter.width(right_scale.limbs_le().len())?;
                let a = parent(&rows, index, *left)?;
                let b = parent(&rows, index, *right)?;
                let left_scale = BigInt::from_sign_magnitude(false, meter.copy_nat(left_scale)?);
                let right_scale = BigInt::from_sign_magnitude(false, meter.copy_nat(right_scale)?);
                let mut coefficients = Vec::new();
                meter.reserve(&mut coefficients, dimensions)?;
                // Replay the declared arithmetic; do not call Solver::combine,
                // its pivot cancellation or its factor-selection logic.
                for variable in 0..dimensions {
                    let first = meter.mul(&left_scale, &a.coeffs[variable])?;
                    let second = meter.mul(&right_scale, &b.coeffs[variable])?;
                    coefficients.push(meter.add(&first, &second)?);
                }
                let first = meter.mul(&left_scale, &a.bound)?;
                let second = meter.mul(&right_scale, &b.bound)?;
                LinearConstraint {
                    coeffs: coefficients,
                    bound: meter.add(&first, &second)?,
                }
            }
            OmegaStep::DivideGcd { source } => {
                let source = parent(&rows, index, *source)?;
                let mut gcd = BigNat::zero();
                for coefficient in &source.coeffs {
                    gcd = meter.gcd(&gcd, coefficient.magnitude())?;
                }
                if gcd.is_zero() {
                    return Err(CertificateError::ZeroDivisor(index as u32));
                }
                let gcd = BigInt::from_sign_magnitude(false, gcd);
                let mut coefficients = Vec::new();
                meter.reserve(&mut coefficients, dimensions)?;
                for coefficient in &source.coeffs {
                    coefficients.push(meter.div(coefficient, &gcd)?);
                }
                LinearConstraint {
                    coeffs: coefficients,
                    bound: meter.div(&source.bound, &gcd)?,
                }
            }
        };
        for coefficient in row.coeffs.iter().chain(std::iter::once(&row.bound)) {
            meter.storage(coefficient.magnitude().limbs_le().len().saturating_mul(8))?;
        }
        rows.push(row);
    }
    let last = &rows[certificate.conclusion as usize];
    meter.tick(dimensions as u64 + 1)?;
    if !last.bound.is_negative() || last.coeffs.iter().any(|coefficient| !coefficient.is_zero()) {
        return Err(CertificateError::Conclusion);
    }
    Ok(rows)
}

/// Check exact input binding, all arithmetic steps, and the final contradiction.
/// The resulting rows are useful for a proof replayer; this is not admission.
pub fn check_certificate(
    expected: &[LinearConstraint],
    certificate: &OmegaCertificate,
    limits: OmegaLimits,
) -> Checked<Vec<LinearConstraint>> {
    let mut never_cancel = || false;
    check(
        expected,
        certificate,
        &mut Meter {
            limits,
            used: 0,
            bytes: 0,
            cancelled: &mut never_cancel,
        },
    )
}

const MAGIC: &[u8; 8] = b"FLNOMEGA";

pub(super) struct Encoder<'a, 'b> {
    pub(super) output: Vec<u8>,
    pub(super) meter: &'a mut Meter<'b>,
}

impl Encoder<'_, '_> {
    pub(super) fn bytes(&mut self, bytes: &[u8]) -> Checked<()> {
        self.meter.reserve(&mut self.output, bytes.len())?;
        self.output.extend_from_slice(bytes);
        Ok(())
    }
    pub(super) fn u32(&mut self, n: u32) -> Checked<()> {
        self.bytes(&n.to_le_bytes())
    }
    pub(super) fn nat(&mut self, n: &BigNat) -> Checked<()> {
        let limbs = n.limbs_le();
        self.meter.width(limbs.len())?;
        let len = u32::try_from(limbs.len())
            .map_err(|_| CertificateError::Encoding("integer limb count"))?;
        self.u32(len)?;
        for limb in limbs {
            self.bytes(&limb.to_le_bytes())?;
        }
        Ok(())
    }
    pub(super) fn int(&mut self, n: &BigInt) -> Checked<()> {
        self.bytes(&[u8::from(n.is_negative())])?;
        self.nat(n.magnitude())
    }
    pub(super) fn row(&mut self, row: &LinearConstraint) -> Checked<()> {
        self.u32(
            u32::try_from(row.coeffs.len())
                .map_err(|_| CertificateError::Encoding("coefficient count"))?,
        )?;
        for coefficient in &row.coeffs {
            self.int(coefficient)?;
        }
        self.int(&row.bound)
    }
}

/// Encode the V1 tagged DAG with canonical signed-magnitude integers. Encoding
/// preserves data and does not claim that the encoded certificate is valid.
pub fn encode_certificate(certificate: &OmegaCertificate, limits: OmegaLimits) -> Checked<Vec<u8>> {
    let mut never_cancel = || false;
    let mut meter = Meter {
        limits,
        used: 0,
        bytes: 0,
        cancelled: &mut never_cancel,
    };
    encode(certificate, &mut meter)
}

pub(super) fn encode(certificate: &OmegaCertificate, meter: &mut Meter<'_>) -> Checked<Vec<u8>> {
    if certificate.version != OMEGA_CERTIFICATE_VERSION {
        return Err(CertificateError::UnsupportedVersion(certificate.version));
    }
    meter.dimensions(&certificate.inputs)?;
    row_count(certificate.steps.len(), meter)?;
    let mut encoder = Encoder {
        output: Vec::new(),
        meter,
    };
    encoder.bytes(MAGIC)?;
    encoder.u32(certificate.version)?;
    encoder.u32(certificate.inputs.len() as u32)?;
    for input in &certificate.inputs {
        encoder.row(input)?;
    }
    encoder.u32(certificate.steps.len() as u32)?;
    for step in &certificate.steps {
        match step {
            OmegaStep::Input { index } => {
                encoder.bytes(&[0])?;
                encoder.u32(*index)?;
            }
            OmegaStep::Combine {
                left,
                right,
                left_scale,
                right_scale,
            } => {
                encoder.bytes(&[1])?;
                encoder.u32(*left)?;
                encoder.u32(*right)?;
                encoder.nat(left_scale)?;
                encoder.nat(right_scale)?;
            }
            OmegaStep::DivideGcd { source } => {
                encoder.bytes(&[2])?;
                encoder.u32(*source)?;
            }
        }
    }
    encoder.u32(certificate.conclusion)?;
    Ok(encoder.output)
}

pub(super) struct Decoder<'a, 'b, 'c> {
    pub(super) input: &'a [u8],
    pub(super) position: usize,
    pub(super) meter: &'b mut Meter<'c>,
}

impl<'a> Decoder<'a, '_, '_> {
    pub(super) fn bytes(&mut self, count: usize) -> Checked<&'a [u8]> {
        let end = self
            .position
            .checked_add(count)
            .ok_or(CertificateError::Encoding("length overflow"))?;
        let bytes = self
            .input
            .get(self.position..end)
            .ok_or(CertificateError::Encoding("truncated"))?;
        // An untrusted length does not describe work until its entire span
        // exists. Reject missing bytes before charging or traversing them.
        self.meter.tick(count as u64 + 1)?;
        self.position = end;
        Ok(bytes)
    }
    pub(super) fn byte(&mut self) -> Checked<u8> {
        Ok(self.bytes(1)?[0])
    }
    pub(super) fn u32(&mut self) -> Checked<u32> {
        Ok(u32::from_le_bytes(
            self.bytes(4)?.try_into().expect("four bytes"),
        ))
    }
    pub(super) fn nat(&mut self) -> Checked<BigNat> {
        let count = self.u32()? as usize;
        self.meter.width(count)?;
        // Validate the byte span before allocating from an untrusted prefix.
        let raw = self.bytes(
            count
                .checked_mul(8)
                .ok_or(CertificateError::Encoding("limb length overflow"))?,
        )?;
        let mut limbs = Vec::new();
        self.meter.reserve(&mut limbs, count)?;
        for &limb in raw.as_chunks::<8>().0 {
            limbs.push(u64::from_le_bytes(limb));
        }
        if limbs.last() == Some(&0) {
            return Err(CertificateError::Encoding("noncanonical integer"));
        }
        Ok(BigNat::from_limbs_le(limbs))
    }
    pub(super) fn int(&mut self) -> Checked<BigInt> {
        let negative = match self.byte()? {
            0 => false,
            1 => true,
            _ => return Err(CertificateError::Encoding("integer sign")),
        };
        let magnitude = self.nat()?;
        if negative && magnitude.is_zero() {
            return Err(CertificateError::Encoding("negative zero"));
        }
        Ok(BigInt::from_sign_magnitude(negative, magnitude))
    }
    pub(super) fn row(&mut self) -> Checked<LinearConstraint> {
        let count = self.u32()? as usize;
        if count > self.meter.limits.max_variables {
            return Err(Meter::limit(
                OmegaResource::Variables,
                self.meter.limits.max_variables,
                count,
            )
            .into());
        }
        let mut coeffs = Vec::new();
        self.meter.reserve(&mut coeffs, count)?;
        for _ in 0..count {
            coeffs.push(self.int()?);
        }
        Ok(LinearConstraint {
            coeffs,
            bound: self.int()?,
        })
    }
}

/// Decode one complete canonical V1 certificate. Unknown versions/tags, invalid
/// integers, truncation and trailing bytes are errors. Arithmetic and exact input
/// binding are checked separately by the certificate checker.
pub fn decode_certificate(input: &[u8], limits: OmegaLimits) -> Checked<OmegaCertificate> {
    let mut never_cancel = || false;
    let mut meter = Meter {
        limits,
        used: 0,
        bytes: 0,
        cancelled: &mut never_cancel,
    };
    decode(input, &mut meter)
}

pub(super) fn decode(input: &[u8], meter: &mut Meter<'_>) -> Checked<OmegaCertificate> {
    decode_after_rows(input, meter, 0)
}

/// Branch decoding carries its earlier tree/leaf rows into this prefix check,
/// so an otherwise permitted leaf cannot allocate past the cumulative cap.
pub(super) fn decode_after_rows(
    input: &[u8],
    meter: &mut Meter<'_>,
    earlier_rows: usize,
) -> Checked<OmegaCertificate> {
    if input.len() > meter.limits.max_certificate_bytes {
        return Err(Meter::limit(
            OmegaResource::CertificateBytes,
            meter.limits.max_certificate_bytes,
            input.len(),
        )
        .into());
    }
    let mut decoder = Decoder {
        input,
        position: 0,
        meter,
    };
    if decoder.bytes(8)? != MAGIC {
        return Err(CertificateError::Encoding("magic"));
    }
    let version = decoder.u32()?;
    if version != OMEGA_CERTIFICATE_VERSION {
        return Err(CertificateError::UnsupportedVersion(version));
    }
    let count = decoder.u32()? as usize;
    row_count(count, decoder.meter)?;
    let mut inputs = Vec::new();
    decoder.meter.reserve(&mut inputs, count)?;
    for _ in 0..count {
        inputs.push(decoder.row()?);
    }
    let count = decoder.u32()? as usize;
    row_count(earlier_rows.saturating_add(count), decoder.meter)?;
    let mut steps = Vec::new();
    decoder.meter.reserve(&mut steps, count)?;
    for _ in 0..count {
        let step = match decoder.byte()? {
            0 => OmegaStep::Input {
                index: decoder.u32()?,
            },
            1 => OmegaStep::Combine {
                left: decoder.u32()?,
                right: decoder.u32()?,
                left_scale: decoder.nat()?,
                right_scale: decoder.nat()?,
            },
            2 => OmegaStep::DivideGcd {
                source: decoder.u32()?,
            },
            _ => return Err(CertificateError::Encoding("step tag")),
        };
        steps.push(step);
    }
    let conclusion = decoder.u32()?;
    if decoder.position != input.len() {
        return Err(CertificateError::Encoding("trailing bytes"));
    }
    Ok(OmegaCertificate {
        version,
        inputs,
        steps,
        conclusion,
    })
}
