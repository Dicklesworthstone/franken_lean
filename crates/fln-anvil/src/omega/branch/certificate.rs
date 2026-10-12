//! Independent scoped replay and canonical flat-tree encoding.
//! No rational arithmetic, pivot choice or branch search runs in this checker.

use super::super::certificate::{Decoder, Encoder};
use super::super::*;

type Checked<T> = std::result::Result<T, CertificateError>;

fn row_count(count: usize, meter: &mut Meter<'_>) -> Checked<()> {
    meter.tick(1)?;
    let limit = meter.limits.max_rows.min(u32::MAX as usize);
    if count > limit {
        return Err(Meter::limit(OmegaResource::Rows, limit, count).into());
    }
    Ok(())
}

fn same_inputs(
    actual: &[LinearConstraint],
    expected: &[LinearConstraint],
    meter: &mut Meter<'_>,
) -> Checked<()> {
    meter.dimensions(actual)?;
    meter.dimensions(expected)?;
    if actual.len() != expected.len() {
        return Err(CertificateError::InputMismatch);
    }
    for (a, b) in actual.iter().zip(expected) {
        if a.coeffs.len() != b.coeffs.len() {
            return Err(CertificateError::InputMismatch);
        }
        for (a, b) in a
            .coeffs
            .iter()
            .chain(std::iter::once(&a.bound))
            .zip(b.coeffs.iter().chain(std::iter::once(&b.bound)))
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
    Ok(())
}

fn shape(certificate: &OmegaBranchCertificate, meter: &mut Meter<'_>) -> Checked<usize> {
    if certificate.version != OMEGA_BRANCH_CERTIFICATE_VERSION {
        return Err(CertificateError::UnsupportedVersion(certificate.version));
    }
    let dimensions = meter.dimensions(&certificate.inputs)?;
    row_count(certificate.nodes.len(), meter)?;
    if certificate.nodes.is_empty()
        || certificate.conclusion as usize != certificate.nodes.len() - 1
    {
        return Err(CertificateError::BranchShape);
    }
    let mut incoming = Vec::new();
    meter.reserve(&mut incoming, certificate.nodes.len())?;
    incoming.resize(certificate.nodes.len(), false);
    let mut rows = certificate.nodes.len();
    for (index, node) in certificate.nodes.iter().enumerate() {
        meter.tick(1)?;
        match node {
            OmegaBranchNode::Leaf { certificate } => {
                rows = rows.saturating_add(certificate.steps.len());
                row_count(rows, meter)?;
            }
            OmegaBranchNode::Split {
                variable,
                cut,
                le,
                gt,
            } => {
                meter.integer(cut)?;
                if *variable as usize >= dimensions {
                    return Err(CertificateError::BranchVariable(*variable));
                }
                if le == gt || *le as usize >= index || *gt as usize >= index {
                    return Err(CertificateError::BranchShape);
                }
                for child in [*le, *gt] {
                    if incoming[child as usize] {
                        return Err(CertificateError::BranchShape);
                    }
                    incoming[child as usize] = true;
                }
            }
        }
    }
    // Strict postorder plus exactly one parent for every earlier node gives
    // one rooted tree. Shared leaves, context reuse, dead nodes and cycles are
    // all rejected before any leaf can amplify checker work.
    for (index, has_parent) in incoming.into_iter().enumerate() {
        meter.tick(1)?;
        if has_parent == (index == certificate.conclusion as usize) {
            return Err(CertificateError::BranchShape);
        }
    }
    Ok(dimensions)
}

enum Visit {
    Enter(u32),
    Greater {
        variable: u32,
        cut: BigInt,
        child: u32,
    },
    Leave,
}

/// Build the case assumptions independently of the searcher's row builder.
/// The vector includes every root variable, including zero trailing entries.
fn scoped_row(
    dimensions: usize,
    variable: u32,
    cut: &BigInt,
    greater: bool,
    meter: &mut Meter<'_>,
) -> Checked<LinearConstraint> {
    if variable as usize >= dimensions {
        return Err(CertificateError::BranchVariable(variable));
    }
    let mut coeffs = Vec::new();
    meter.reserve(&mut coeffs, dimensions)?;
    for index in 0..dimensions {
        meter.tick(1)?;
        coeffs.push(BigInt::from_i64(if index == variable as usize {
            if greater { -1 } else { 1 }
        } else {
            0
        }));
    }
    meter.storage(8)?;
    let bound = if greater {
        let negative_cut = meter.sub(&BigInt::zero(), cut)?;
        let bound = meter.sub(&negative_cut, &BigInt::from_i64(1))?;
        meter.storage(bound.magnitude().limbs_le().len().saturating_mul(8))?;
        bound
    } else {
        meter.copy_int(cut)?
    };
    Ok(LinearConstraint { coeffs, bound })
}

fn check(
    expected: &[LinearConstraint],
    certificate: &OmegaBranchCertificate,
    meter: &mut Meter<'_>,
) -> Checked<()> {
    same_inputs(&certificate.inputs, expected, meter)?;
    let dimensions = shape(certificate, meter)?;
    let mut inputs = Vec::new();
    meter.reserve(&mut inputs, expected.len())?;
    for input in expected {
        inputs.push(meter.copy_row(input, input.coeffs.len())?);
    }
    let mut visits = Vec::new();
    meter.reserve(&mut visits, 1)?;
    visits.push(Visit::Enter(certificate.conclusion));
    while let Some(visit) = visits.pop() {
        meter.tick(1)?;
        match visit {
            Visit::Enter(index) => match &certificate.nodes[index as usize] {
                OmegaBranchNode::Leaf { certificate } => {
                    // One cumulative meter covers every leaf's input binding,
                    // arithmetic replay, allocation and contradiction check.
                    super::super::certificate::check(&inputs, certificate, meter)?;
                }
                OmegaBranchNode::Split {
                    variable,
                    cut,
                    le,
                    gt,
                } => {
                    row_count(inputs.len().saturating_add(1), meter)?;
                    let row = scoped_row(dimensions, *variable, cut, false, meter)?;
                    meter.reserve(&mut inputs, 1)?;
                    inputs.push(row);
                    meter.reserve(&mut visits, 2)?;
                    visits.push(Visit::Greater {
                        variable: *variable,
                        cut: meter.copy_int(cut)?,
                        child: *gt,
                    });
                    visits.push(Visit::Enter(*le));
                }
            },
            Visit::Greater {
                variable,
                cut,
                child,
            } => {
                inputs.pop().ok_or(CertificateError::BranchShape)?;
                inputs.push(scoped_row(dimensions, variable, &cut, true, meter)?);
                meter.reserve(&mut visits, 2)?;
                visits.push(Visit::Leave);
                visits.push(Visit::Enter(child));
            }
            Visit::Leave => {
                inputs.pop().ok_or(CertificateError::BranchShape)?;
            }
        }
    }
    if inputs.len() != expected.len() {
        return Err(CertificateError::BranchShape);
    }
    Ok(())
}

/// Validate exact input binding, strict tree shape, every ordered case context
/// and every linear contradiction. This function grants no admission authority.
pub fn check_branch_certificate(
    expected: &[LinearConstraint],
    certificate: &OmegaBranchCertificate,
    limits: OmegaLimits,
) -> Checked<()> {
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

const MAGIC: &[u8; 8] = b"FLNOMBRN";

/// Encode a strict postorder tree with canonical V1 linear certificates as
/// length-delimited leaves. Arithmetic validity remains the checker's job.
pub fn encode_branch_certificate(
    certificate: &OmegaBranchCertificate,
    limits: OmegaLimits,
) -> Checked<Vec<u8>> {
    let mut never_cancel = || false;
    let mut meter = Meter {
        limits,
        used: 0,
        bytes: 0,
        cancelled: &mut never_cancel,
    };
    shape(certificate, &mut meter)?;
    let mut encoder = Encoder {
        output: Vec::new(),
        meter: &mut meter,
    };
    encoder.bytes(MAGIC)?;
    encoder.u32(certificate.version)?;
    encoder.u32(certificate.inputs.len() as u32)?;
    for input in &certificate.inputs {
        encoder.row(input)?;
    }
    encoder.u32(certificate.nodes.len() as u32)?;
    for node in &certificate.nodes {
        match node {
            OmegaBranchNode::Leaf { certificate } => {
                encoder.bytes(&[0])?;
                let bytes = super::super::certificate::encode(certificate, encoder.meter)?;
                encoder.u32(
                    u32::try_from(bytes.len())
                        .map_err(|_| CertificateError::Encoding("leaf length"))?,
                )?;
                encoder.bytes(&bytes)?;
            }
            OmegaBranchNode::Split {
                variable,
                cut,
                le,
                gt,
            } => {
                encoder.bytes(&[1])?;
                encoder.u32(*variable)?;
                encoder.int(cut)?;
                encoder.u32(*le)?;
                encoder.u32(*gt)?;
            }
        }
    }
    encoder.u32(certificate.conclusion)?;
    Ok(encoder.output)
}

/// Decode one bounded canonical tree. Child references, tree ownership and
/// cumulative leaf/node counts are validated; leaf arithmetic is not solved.
pub fn decode_branch_certificate(
    input: &[u8],
    limits: OmegaLimits,
) -> Checked<OmegaBranchCertificate> {
    if input.len() > limits.max_certificate_bytes {
        return Err(Meter::limit(
            OmegaResource::CertificateBytes,
            limits.max_certificate_bytes,
            input.len(),
        )
        .into());
    }
    let mut never_cancel = || false;
    let mut meter = Meter {
        limits,
        used: 0,
        bytes: 0,
        cancelled: &mut never_cancel,
    };
    let mut decoder = Decoder {
        input,
        position: 0,
        meter: &mut meter,
    };
    if decoder.bytes(8)? != MAGIC {
        return Err(CertificateError::Encoding("branch magic"));
    }
    let version = decoder.u32()?;
    if version != OMEGA_BRANCH_CERTIFICATE_VERSION {
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
    row_count(count, decoder.meter)?;
    let mut nodes = Vec::new();
    decoder.meter.reserve(&mut nodes, count)?;
    let mut rows = count;
    for _ in 0..count {
        let node = match decoder.byte()? {
            0 => {
                let length = decoder.u32()? as usize;
                // Span validation precedes every allocation from an untrusted
                // leaf length, and the same meter follows into the V1 decoder.
                let bytes = decoder.bytes(length)?;
                let certificate =
                    super::super::certificate::decode_after_rows(bytes, decoder.meter, rows)?;
                rows = rows.saturating_add(certificate.steps.len());
                row_count(rows, decoder.meter)?;
                OmegaBranchNode::Leaf { certificate }
            }
            1 => OmegaBranchNode::Split {
                variable: decoder.u32()?,
                cut: decoder.int()?,
                le: decoder.u32()?,
                gt: decoder.u32()?,
            },
            _ => return Err(CertificateError::Encoding("branch node tag")),
        };
        nodes.push(node);
    }
    let conclusion = decoder.u32()?;
    if decoder.position != input.len() {
        return Err(CertificateError::Encoding("trailing bytes"));
    }
    let certificate = OmegaBranchCertificate {
        version,
        inputs,
        nodes,
        conclusion,
    };
    shape(&certificate, decoder.meter)?;
    Ok(certificate)
}
