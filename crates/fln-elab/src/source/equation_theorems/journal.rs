//! The equation information a definition by pattern matching leaves for its equation theorems,
//! as the pin's `Structural.eqnInfoExt` and its matchers keep theirs (vendored
//! `Lean/Elab/PreDefinition/Structural/Eqns.lean:166`, `Lean/Meta/Match/Match.lean:1082`).
//!
//! One row per definition: the match's discriminants and its alternatives as the pin's matcher
//! states them (fields, patterns, right-hand side), elaborated when the definition is. It is
//! untrusted elaboration metadata: every theorem built from it is checked by both checkers.
//! It is not written to `.olean` files, so a definition imported from one has no row.
use super::super::*;
use fln_core::expr::Literal;
use fln_core::level::LevelView;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::HashMap;

const MAGIC: &[u8] = b"FLNEQNS\x01";
/// Rows the journal holds; each definition by matching adds one.
pub const MAX_ROWS: usize = 1 << 16;
const MAX_ENTRY_BYTES: usize = 1 << 22;
const MAX_NODES: usize = 1 << 20;

/// The journal's name.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "equationInfo", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// The journal, which a module's artifacts carry nothing of: the pin's own equation
/// information lives in its matchers and `eqnInfoExt`, which this engine does not write.
pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

/// A definition's match, as its equation theorems need it.
#[derive(Debug, Clone, PartialEq)]
pub struct Record {
    pub declaration: Name,
    /// The definition's value lambdas the match is under.
    pub arity: usize,
    /// The parameter each discriminant is, by position.
    pub discriminants: Vec<usize>,
    /// The matcher motive's binder names, which name the generalized discriminants.
    pub motive_names: Vec<Name>,
    /// The match's shape up to variable names: equal shapes share one matcher at the pin.
    pub key: Expr,
    /// Each alternative closed over the parameters, then its fields (binder names are the
    /// matcher's): `fun params fields => pack pattern₁ … patternₖ rhs`.
    pub alternatives: Vec<Expr>,
}

fn malformed() -> NatDefinitionElabError {
    failure(SourceInferenceError::Scope)
}

/// The constant heading the packed record and each alternative; never declared.
pub(super) fn pack_name() -> Name {
    Name::from_components(["_fln_equations", "pack"])
}

fn pack(args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter()
        .fold(Expr::const_(pack_name(), Vec::new()), Expr::app)
}

pub(super) fn unpack(expr: &Expr) -> Option<Vec<Expr>> {
    let mut args = Vec::new();
    let mut head = expr;
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    matches!(head.node(), ExprNode::Const { name, .. } if *name == pack_name()).then_some(args)
}

fn nat(value: usize) -> Expr {
    Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value as u64)))
}

fn read_nat(expr: &Expr) -> Option<usize> {
    match expr.node() {
        ExprNode::Lit {
            literal: Literal::Nat(value),
        } => value.to_u64().and_then(|value| usize::try_from(value).ok()),
        _ => None,
    }
}

impl Record {
    fn to_expr(&self) -> Expr {
        let mut args = vec![
            nat(self.arity),
            nat(self.discriminants.len()),
            nat(self.alternatives.len()),
        ];
        args.extend(self.discriminants.iter().map(|&position| nat(position)));
        args.extend(
            self.motive_names
                .iter()
                .map(|name| Expr::const_(name.clone(), Vec::new())),
        );
        args.push(self.key.clone());
        args.extend(self.alternatives.iter().cloned());
        pack(args)
    }

    fn from_expr(declaration: Name, expr: &Expr) -> Option<Self> {
        let args = unpack(expr)?;
        let arity = read_nat(args.first()?)?;
        let columns = read_nat(args.get(1)?)?;
        let count = read_nat(args.get(2)?)?;
        if args.len() != 3 + 2 * columns + 1 + count {
            return None;
        }
        let discriminants = args[3..3 + columns]
            .iter()
            .map(read_nat)
            .collect::<Option<Vec<_>>>()?;
        let motive_names = args[3 + columns..3 + 2 * columns]
            .iter()
            .map(|name| match name.node() {
                ExprNode::Const { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let key = args[3 + 2 * columns].clone();
        let alternatives = args[4 + 2 * columns..].to_vec();
        Some(Self {
            declaration,
            arity,
            discriminants,
            motive_names,
            key,
            alternatives,
        })
    }
}

/// Append `record` to the environment's journal.
pub fn push(
    environment: &Environment,
    record: &Record,
) -> Result<Environment, NatDefinitionElabError> {
    let mut payload = MAGIC.to_vec();
    write_name(&record.declaration, &mut payload);
    write_expr(&record.to_expr(), &mut payload)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let descriptor = descriptor();
    let environment = match environment.extension(&descriptor.name) {
        None => environment
            .register_extension(descriptor.clone())
            .map_err(|_| malformed())?,
        Some(state) if state.descriptor != descriptor => return Err(malformed()),
        Some(state) if state.len() >= MAX_ROWS => {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        Some(_) => environment.clone(),
    };
    environment
        .push_extension_entry(&descriptor.name, payload)
        .map_err(|_| malformed())
}

/// Every row in journal order.
pub fn read(environment: &Environment) -> Result<Vec<Record>, NatDefinitionElabError> {
    let descriptor = descriptor();
    let Some(state) = environment.extension(&descriptor.name) else {
        return Ok(Vec::new());
    };
    if state.descriptor != descriptor || state.len() > MAX_ROWS {
        return Err(malformed());
    }
    let mut records = Vec::new();
    for entry in state.entries() {
        let mut bytes: &[u8] = entry.payload.strip_prefix(MAGIC).ok_or_else(malformed)?;
        let declaration = read_name(&mut bytes)?;
        let expr = read_expr(&mut bytes)?;
        if !bytes.is_empty() {
            return Err(malformed());
        }
        records.push(Record::from_expr(declaration, &expr).ok_or_else(malformed)?);
    }
    Ok(records)
}

/// `declaration`'s row, if it has one.
pub fn find(
    environment: &Environment,
    declaration: &Name,
) -> Result<Option<Record>, NatDefinitionElabError> {
    Ok(read(environment)?
        .into_iter()
        .find(|record| &record.declaration == declaration))
}

fn write_u64(value: u64, out: &mut Vec<u8>) {
    out.extend(value.to_le_bytes());
}

fn take<'a>(bytes: &mut &'a [u8], count: usize) -> Result<&'a [u8], NatDefinitionElabError> {
    if bytes.len() < count {
        return Err(malformed());
    }
    let (head, rest) = bytes.split_at(count);
    *bytes = rest;
    Ok(head)
}

fn read_u64(bytes: &mut &[u8]) -> Result<u64, NatDefinitionElabError> {
    Ok(u64::from_le_bytes(
        take(bytes, 8)?.try_into().map_err(|_| malformed())?,
    ))
}

fn read_usize(bytes: &mut &[u8]) -> Result<usize, NatDefinitionElabError> {
    usize::try_from(read_u64(bytes)?).map_err(|_| malformed())
}

fn write_str(text: &str, out: &mut Vec<u8>) {
    write_u64(text.len() as u64, out);
    out.extend(text.as_bytes());
}

fn read_str(bytes: &mut &[u8]) -> Result<String, NatDefinitionElabError> {
    let length = read_usize(bytes)?;
    String::from_utf8(take(bytes, length)?.to_vec()).map_err(|_| malformed())
}

fn write_name(name: &Name, out: &mut Vec<u8>) {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        parts.push(cursor.clone());
        cursor = cursor.parent();
    }
    write_u64(parts.len() as u64, out);
    for part in parts.into_iter().rev() {
        match part.leaf_view() {
            LeafView::Str(text) => {
                out.push(0);
                write_str(text, out);
            }
            LeafView::Num(value) => {
                out.push(1);
                write_u64(value, out);
            }
            LeafView::Anonymous => unreachable!("a non-anonymous component"),
        }
    }
}

fn read_name(bytes: &mut &[u8]) -> Result<Name, NatDefinitionElabError> {
    let count = read_usize(bytes)?;
    if count > 4096 {
        return Err(malformed());
    }
    let mut name = Name::anonymous();
    for _ in 0..count {
        name = match take(bytes, 1)?[0] {
            0 => Name::str(name, read_str(bytes)?),
            1 => Name::num(name, read_u64(bytes)?),
            _ => return Err(malformed()),
        };
    }
    Ok(name)
}

fn write_level(level: &Level, out: &mut Vec<u8>) -> Result<(), NatDefinitionElabError> {
    match level.view() {
        LevelView::Zero => out.push(0),
        LevelView::Succ(inner) => {
            out.push(1);
            write_level(inner, out)?;
        }
        LevelView::Max(left, right) => {
            out.push(2);
            write_level(left, out)?;
            write_level(right, out)?;
        }
        LevelView::IMax(left, right) => {
            out.push(3);
            write_level(left, out)?;
            write_level(right, out)?;
        }
        LevelView::Param(name) => {
            out.push(4);
            write_name(name, out);
        }
        LevelView::MVar(_) => return Err(malformed()),
    }
    Ok(())
}

fn read_level(bytes: &mut &[u8], depth: usize) -> Result<Level, NatDefinitionElabError> {
    if depth > 256 {
        return Err(malformed());
    }
    let too_deep = |_| malformed();
    Ok(match take(bytes, 1)?[0] {
        0 => Level::zero(),
        1 => read_level(bytes, depth + 1)?.succ().map_err(too_deep)?,
        2 => Level::max(read_level(bytes, depth + 1)?, read_level(bytes, depth + 1)?)
            .map_err(too_deep)?,
        3 => Level::imax(read_level(bytes, depth + 1)?, read_level(bytes, depth + 1)?)
            .map_err(too_deep)?,
        4 => Level::param(read_name(bytes)?),
        _ => return Err(malformed()),
    })
}

fn binder_tag(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn binder_info(tag: u8) -> Result<BinderInfo, NatDefinitionElabError> {
    Ok(match tag {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => return Err(malformed()),
    })
}

/// A closed expression as a DAG: every distinct node once, children before parents. Metadata
/// is dropped (no printer or checker reads it); free variables and holes are refused.
fn write_expr(root: &Expr, out: &mut Vec<u8>) -> Result<(), NatDefinitionElabError> {
    let mut index: HashMap<usize, u64> = HashMap::new();
    let mut nodes: Vec<Vec<u8>> = Vec::new();
    let mut stack: Vec<(&Expr, bool)> = vec![(root, false)];
    let child = |index: &HashMap<usize, u64>, expr: &Expr| -> Result<u64, NatDefinitionElabError> {
        let mut expr = expr;
        while let ExprNode::MData { expr: inner, .. } = expr.node() {
            expr = inner;
        }
        index
            .get(&expr.allocation_identity())
            .copied()
            .ok_or_else(malformed)
    };
    while let Some((expr, ready)) = stack.pop() {
        if let ExprNode::MData { expr: inner, .. } = expr.node() {
            stack.push((inner, ready));
            continue;
        }
        if index.contains_key(&expr.allocation_identity()) {
            continue;
        }
        let children: Vec<&Expr> = match expr.node() {
            ExprNode::App { f, a } => vec![f, a],
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => vec![binder_type, body],
            ExprNode::LetE {
                type_, value, body, ..
            } => vec![type_, value, body],
            ExprNode::Proj { expr, .. } => vec![expr],
            ExprNode::FVar { .. } | ExprNode::MVar { .. } => return Err(malformed()),
            _ => Vec::new(),
        };
        if !ready {
            stack.push((expr, true));
            stack.extend(children.into_iter().map(|child| (child, false)));
            continue;
        }
        if nodes.len() >= MAX_NODES {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut node = Vec::new();
        match expr.node() {
            ExprNode::BVar { idx } => {
                node.push(0);
                write_u64(u64::from(*idx), &mut node);
            }
            ExprNode::Sort { level } => {
                node.push(1);
                write_level(level, &mut node)?;
            }
            ExprNode::Const { name, levels } => {
                node.push(2);
                write_name(name, &mut node);
                write_u64(levels.len() as u64, &mut node);
                for level in levels {
                    write_level(level, &mut node)?;
                }
            }
            ExprNode::App { f, a } => {
                node.push(3);
                write_u64(child(&index, f)?, &mut node);
                write_u64(child(&index, a)?, &mut node);
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                node.push(if matches!(expr.node(), ExprNode::Lam { .. }) {
                    4
                } else {
                    5
                });
                write_name(binder_name, &mut node);
                node.push(binder_tag(*binder_info));
                write_u64(child(&index, binder_type)?, &mut node);
                write_u64(child(&index, body)?, &mut node);
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                node.push(6);
                write_name(decl_name, &mut node);
                node.push(u8::from(*non_dep));
                write_u64(child(&index, type_)?, &mut node);
                write_u64(child(&index, value)?, &mut node);
                write_u64(child(&index, body)?, &mut node);
            }
            ExprNode::Lit { literal } => match literal {
                Literal::Nat(value) => {
                    node.push(7);
                    write_u64(value.limbs_le().len() as u64, &mut node);
                    for limb in value.limbs_le() {
                        write_u64(*limb, &mut node);
                    }
                }
                Literal::Str(text) => {
                    node.push(8);
                    write_str(text, &mut node);
                }
            },
            ExprNode::Proj {
                struct_name,
                idx,
                expr: inner,
            } => {
                node.push(9);
                write_name(struct_name, &mut node);
                write_u64(*idx, &mut node);
                write_u64(child(&index, inner)?, &mut node);
            }
            ExprNode::MData { .. } | ExprNode::FVar { .. } | ExprNode::MVar { .. } => {
                return Err(malformed());
            }
        }
        index.insert(expr.allocation_identity(), nodes.len() as u64);
        nodes.push(node);
    }
    write_u64(nodes.len() as u64, out);
    for node in nodes {
        out.extend(node);
    }
    write_u64(child(&index, root)?, out);
    Ok(())
}

fn read_expr(bytes: &mut &[u8]) -> Result<Expr, NatDefinitionElabError> {
    let count = read_usize(bytes)?;
    if count > MAX_NODES {
        return Err(malformed());
    }
    let mut nodes: Vec<Expr> = Vec::with_capacity(count.min(4096));
    let get = |nodes: &Vec<Expr>, at: u64| -> Result<Expr, NatDefinitionElabError> {
        usize::try_from(at)
            .ok()
            .and_then(|at| nodes.get(at))
            .cloned()
            .ok_or_else(malformed)
    };
    for _ in 0..count {
        let expr = match take(bytes, 1)?[0] {
            0 => Expr::bvar(u32::try_from(read_u64(bytes)?).map_err(|_| malformed())?)
                .map_err(|_| malformed())?,
            1 => Expr::sort(read_level(bytes, 0)?),
            2 => {
                let name = read_name(bytes)?;
                let length = read_usize(bytes)?;
                if length > 256 {
                    return Err(malformed());
                }
                let mut levels = Vec::with_capacity(length);
                for _ in 0..length {
                    levels.push(read_level(bytes, 0)?);
                }
                Expr::const_(name, levels)
            }
            3 => {
                let f = get(&nodes, read_u64(bytes)?)?;
                let a = get(&nodes, read_u64(bytes)?)?;
                Expr::app(f, a)
            }
            tag @ (4 | 5) => {
                let name = read_name(bytes)?;
                let info = binder_info(take(bytes, 1)?[0])?;
                let binder_type = get(&nodes, read_u64(bytes)?)?;
                let body = get(&nodes, read_u64(bytes)?)?;
                if tag == 4 {
                    Expr::lam(name, binder_type, body, info)
                } else {
                    Expr::forall_e(name, binder_type, body, info)
                }
            }
            6 => {
                let name = read_name(bytes)?;
                let non_dep = match take(bytes, 1)?[0] {
                    0 => false,
                    1 => true,
                    _ => return Err(malformed()),
                };
                let type_ = get(&nodes, read_u64(bytes)?)?;
                let value = get(&nodes, read_u64(bytes)?)?;
                let body = get(&nodes, read_u64(bytes)?)?;
                Expr::let_e(name, type_, value, body, non_dep)
            }
            7 => {
                let length = read_usize(bytes)?;
                if length > 1 << 16 {
                    return Err(malformed());
                }
                let mut limbs = Vec::with_capacity(length);
                for _ in 0..length {
                    limbs.push(read_u64(bytes)?);
                }
                Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_limbs_le(limbs)))
            }
            8 => Expr::lit(Literal::Str(read_str(bytes)?)),
            9 => {
                let name = read_name(bytes)?;
                let idx = read_u64(bytes)?;
                let inner = get(&nodes, read_u64(bytes)?)?;
                Expr::proj(name, idx, inner)
            }
            _ => return Err(malformed()),
        };
        nodes.push(expr);
    }
    let root = read_u64(bytes)?;
    get(&nodes, root)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_round_trip_through_the_journal() {
        let n = |text: &str| Name::from_components(text.split('.'));
        let nat_type = Expr::const_(n("Nat"), Vec::new());
        let shared = Expr::app(
            Expr::const_(n("Nat.succ"), Vec::new()),
            Expr::bvar(0).unwrap(),
        );
        let alternative = Expr::lam(
            n("x"),
            nat_type.clone(),
            Expr::lam(
                n("n"),
                nat_type.clone(),
                pack([shared.clone(), Expr::app(shared.clone(), shared)]),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        );
        let record = Record {
            declaration: n("f"),
            arity: 1,
            discriminants: vec![0],
            motive_names: vec![Name::anonymous()],
            key: Expr::sort(Level::param(n("u")).succ().unwrap()),
            alternatives: vec![alternative.clone(), alternative],
        };
        let environment = push(&Environment::new(), &record).unwrap();
        let environment = push(
            &environment,
            &Record {
                declaration: n("g"),
                ..record.clone()
            },
        )
        .unwrap();
        let read = read(&environment).unwrap();
        assert_eq!(read.len(), 2);
        assert_eq!(read[0], record);
        assert_eq!(
            find(&environment, &n("g")).unwrap().unwrap().declaration,
            n("g")
        );
        let bad = environment
            .push_extension_entry(&journal_name(), b"FLNEQNS\x01junk".to_vec())
            .unwrap();
        assert!(super::read(&bad).is_err());
    }
}
