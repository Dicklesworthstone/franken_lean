//! Bounded DAG encoding for first-order triggers. Children precede parents;
//! malformed edges, holes, binders, noncanonical naturals and suffixes refuse.
use super::*;
use crate::instances::{read_name, write_name};
use fln_core::expr::{Literal, NatLit};
use std::collections::HashMap;

const MAX_NODES: usize = 16_384;
const MAX_LEVEL_DEPTH: usize = 128;
pub(super) const MAX_LEVEL_ARGUMENTS: usize = 256;

fn put_u32(value: usize, bytes: &mut Vec<u8>) -> Result<(), Error> {
    bytes.extend(
        u32::try_from(value)
            .map_err(|_| Error::Limit)?
            .to_le_bytes(),
    );
    Ok(())
}
fn take<'a>(bytes: &mut &'a [u8], count: usize) -> Result<&'a [u8], Error> {
    let (head, tail) = bytes.split_at_checked(count).ok_or(Error::Malformed)?;
    *bytes = tail;
    Ok(head)
}
fn u32_(bytes: &mut &[u8]) -> Result<u32, Error> {
    Ok(u32::from_le_bytes(
        take(bytes, 4)?.try_into().map_err(|_| Error::Malformed)?,
    ))
}

fn write_level(level: &Level, bytes: &mut Vec<u8>, depth: usize) -> Result<(), Error> {
    if depth >= MAX_LEVEL_DEPTH || bytes.len() > MAX_ENTRY_BYTES {
        return Err(Error::Limit);
    }
    match level.view() {
        LevelView::Zero => bytes.push(0),
        LevelView::Succ(inner) => {
            bytes.push(1);
            write_level(inner, bytes, depth + 1)?;
        }
        LevelView::Max(a, b) | LevelView::IMax(a, b) => {
            bytes.push(if matches!(level.view(), LevelView::Max(..)) {
                2
            } else {
                3
            });
            write_level(a, bytes, depth + 1)?;
            write_level(b, bytes, depth + 1)?;
        }
        LevelView::Param(name) => {
            bytes.push(4);
            write_name(name, bytes).map_err(codec_error)?;
        }
        LevelView::MVar(_) => return Err(Error::Malformed),
    }
    Ok(())
}
fn read_level(bytes: &mut &[u8], depth: usize) -> Result<Level, Error> {
    if depth >= MAX_LEVEL_DEPTH {
        return Err(Error::Limit);
    }
    Ok(match take(bytes, 1)?[0] {
        0 => Level::zero(),
        1 => read_level(bytes, depth + 1)?
            .succ()
            .map_err(|_| Error::Limit)?,
        tag @ (2 | 3) => {
            let a = read_level(bytes, depth + 1)?;
            let b = read_level(bytes, depth + 1)?;
            if tag == 2 {
                Level::max(a, b)
            } else {
                Level::imax(a, b)
            }
            .map_err(|_| Error::Limit)?
        }
        4 => Level::param(read_name(bytes).map_err(codec_error)?),
        _ => return Err(Error::Malformed),
    })
}

fn write_expr(root: &Expr, bytes: &mut Vec<u8>) -> Result<(), Error> {
    let mut indices = HashMap::new();
    let mut nodes = Vec::new();
    let mut stack = vec![(root, false)];
    let mut remaining = MAX_STEPS;
    while let Some((term, ready)) = stack.pop() {
        spend(&mut remaining)?;
        if indices.contains_key(&term.allocation_identity()) {
            continue;
        }
        if !ready {
            stack.push((term, true));
            match term.node() {
                ExprNode::App { f, a } => stack.extend([(a, false), (f, false)]),
                ExprNode::MData { expr, .. } if ground_pattern(term).is_some() => {
                    stack.push((expr, false));
                }
                _ => {}
            }
            continue;
        }
        if nodes.len() >= MAX_NODES {
            return Err(Error::Limit);
        }
        indices.insert(term.allocation_identity(), nodes.len());
        nodes.push(term);
    }
    put_u32(nodes.len(), bytes)?;
    for node in nodes {
        match node.node() {
            ExprNode::BVar { idx } => {
                bytes.push(0);
                bytes.extend(idx.to_le_bytes());
            }
            ExprNode::Sort { level } => {
                bytes.push(1);
                write_level(level, bytes, 0)?;
            }
            ExprNode::Const { name, levels } => {
                if levels.len() > MAX_LEVEL_ARGUMENTS {
                    return Err(Error::Limit);
                }
                bytes.push(2);
                write_name(name, bytes).map_err(codec_error)?;
                put_u32(levels.len(), bytes)?;
                for level in levels {
                    write_level(level, bytes, 0)?;
                }
            }
            ExprNode::App { f, a } => {
                bytes.push(3);
                for child in [f, a] {
                    put_u32(
                        *indices
                            .get(&child.allocation_identity())
                            .ok_or(Error::Malformed)?,
                        bytes,
                    )?;
                }
            }
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } => {
                bytes.push(4);
                put_u32(value.limbs_le().len(), bytes)?;
                for limb in value.limbs_le() {
                    bytes.extend(limb.to_le_bytes());
                }
            }
            ExprNode::Lit {
                literal: Literal::Str(value),
            } => {
                bytes.push(5);
                put_u32(value.len(), bytes)?;
                bytes.extend(value.as_bytes());
            }
            ExprNode::MData { expr, .. } if ground_pattern(node).is_some() => {
                bytes.push(6);
                put_u32(
                    *indices
                        .get(&expr.allocation_identity())
                        .ok_or(Error::Malformed)?,
                    bytes,
                )?;
            }
            _ => return Err(Error::Malformed),
        }
        if bytes.len() > MAX_ENTRY_BYTES {
            return Err(Error::Limit);
        }
    }
    Ok(())
}

fn read_expr(bytes: &mut &[u8]) -> Result<Expr, Error> {
    let count = u32_(bytes)? as usize;
    if count == 0 {
        return Err(Error::Malformed);
    }
    if count > MAX_NODES {
        return Err(Error::Limit);
    }
    let mut nodes = Vec::with_capacity(count.min(1024));
    for _ in 0..count {
        let term = match take(bytes, 1)?[0] {
            0 => Expr::bvar(u32_(bytes)?).map_err(|_| Error::Malformed)?,
            1 => Expr::sort(read_level(bytes, 0)?),
            2 => {
                let name = read_name(bytes).map_err(codec_error)?;
                let length = u32_(bytes)? as usize;
                if length > MAX_LEVEL_ARGUMENTS {
                    return Err(Error::Limit);
                }
                let mut levels = Vec::with_capacity(length);
                for _ in 0..length {
                    levels.push(read_level(bytes, 0)?);
                }
                Expr::const_(name, levels)
            }
            3 => {
                let function = nodes
                    .get(u32_(bytes)? as usize)
                    .cloned()
                    .ok_or(Error::Malformed)?;
                let argument = nodes
                    .get(u32_(bytes)? as usize)
                    .cloned()
                    .ok_or(Error::Malformed)?;
                Expr::app(function, argument)
            }
            4 => {
                let length = u32_(bytes)? as usize;
                let raw = take(bytes, length.checked_mul(8).ok_or(Error::Limit)?)?;
                let mut limbs = Vec::with_capacity(length);
                for limb in raw.as_chunks::<8>().0 {
                    limbs.push(u64::from_le_bytes(*limb));
                }
                if limbs.last() == Some(&0) {
                    return Err(Error::Malformed);
                }
                Expr::lit(Literal::Nat(NatLit::from_limbs_le(limbs)))
            }
            5 => {
                let length = u32_(bytes)? as usize;
                let value =
                    std::str::from_utf8(take(bytes, length)?).map_err(|_| Error::Malformed)?;
                Expr::lit(Literal::Str(value.to_owned()))
            }
            6 => {
                let inner = nodes
                    .get(u32_(bytes)? as usize)
                    .cloned()
                    .ok_or(Error::Malformed)?;
                mark_ground(inner)
            }
            _ => return Err(Error::Malformed),
        };
        nodes.push(term);
    }
    nodes.pop().ok_or(Error::Malformed)
}

pub(super) fn encode(row: &GrindPattern) -> Result<Vec<u8>, Error> {
    let mut bytes = if row.captured.is_some() {
        CAPTURED_MAGIC.to_vec()
    } else {
        MAGIC.to_vec()
    };
    write_name(&row.declaration, &mut bytes).map_err(codec_error)?;
    bytes.extend(row.num_params.to_le_bytes());
    bytes.extend(row.data_params.to_le_bytes());
    put_u32(row.patterns.len(), &mut bytes)?;
    for pattern in &row.patterns {
        write_expr(pattern, &mut bytes)?;
    }
    if let Some(capture) = &row.captured {
        put_u32(capture.patterns.len(), &mut bytes)?;
        for pattern in &capture.patterns {
            write_expr(pattern, &mut bytes)?;
        }
        put_u32(capture.symbols.len(), &mut bytes)?;
        for symbol in &capture.symbols {
            write_name(symbol, &mut bytes).map_err(codec_error)?;
        }
    }
    if bytes.len() > MAX_ENTRY_BYTES {
        return Err(Error::Limit);
    }
    Ok(bytes)
}
pub(super) fn decode(payload: &[u8]) -> Result<GrindPattern, Error> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(Error::Limit);
    }
    let (mut bytes, has_capture) = if let Some(bytes) = payload.strip_prefix(CAPTURED_MAGIC) {
        (bytes, true)
    } else {
        (payload.strip_prefix(MAGIC).ok_or(Error::Malformed)?, false)
    };
    let declaration = read_name(&mut bytes).map_err(codec_error)?;
    let num_params = u32_(&mut bytes)?;
    let data_params = u32_(&mut bytes)?;
    let count = u32_(&mut bytes)? as usize;
    if count > MAX_PATTERNS {
        return Err(Error::Limit);
    }
    let mut patterns = Vec::with_capacity(count);
    for _ in 0..count {
        patterns.push(read_expr(&mut bytes)?);
    }
    let captured = if has_capture {
        let count = u32_(&mut bytes)? as usize;
        if count > MAX_PATTERNS {
            return Err(Error::Limit);
        }
        let mut captured_patterns = Vec::with_capacity(count);
        for _ in 0..count {
            captured_patterns.push(read_expr(&mut bytes)?);
        }
        let count = u32_(&mut bytes)? as usize;
        if count > MAX_SYMBOLS {
            return Err(Error::Limit);
        }
        let mut symbols = Vec::with_capacity(count);
        for _ in 0..count {
            symbols.push(read_name(&mut bytes).map_err(codec_error)?);
        }
        Some(CapturedPatterns {
            patterns: captured_patterns,
            symbols,
        })
    } else {
        None
    };
    if !bytes.is_empty() {
        return Err(Error::Malformed);
    }
    let row = GrindPattern {
        declaration,
        num_params,
        data_params,
        patterns,
        captured,
    };
    // Reject disconnected nodes and alternate encodings instead of discarding
    // unvalidated fields from a supposedly understood extension.
    if encode(&row)? != payload {
        return Err(Error::Malformed);
    }
    Ok(row)
}
