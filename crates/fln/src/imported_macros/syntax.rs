//! The bounded Syntax boundary for imported macros. Constructor layouts come
//! from the pinned compiler's IR, exercised by the macro fixture. Source spans
//! stay attached to the caller's exact source buffer: a foreign backing string
//! is refused instead of silently changing `Substring.Raw.str` on reinjection.

use fln_core::name::{LeafView, Name};
use fln_rt::convert::{Conversion, ConvertError, inject_name};
use fln_rt::obj::Obj;
use fln_rt::syntax_abi_generated as abi;
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo, SourceText};
use fln_syntax::tree::{Preresolved, Syntax};
use std::collections::HashSet;

/// Limits for one syntax conversion, including names and pre-resolved lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyntaxLimits {
    pub max_nodes: usize,
    /// Source bytes plus copied atom, name-component and field-name bytes.
    pub max_bytes: usize,
}

impl Default for SyntaxLimits {
    fn default() -> Self {
        Self {
            max_nodes: 1_000_000,
            max_bytes: 64 * 1024 * 1024,
        }
    }
}

/// Conversion failures carry no source-checking or declaration authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxConversionError {
    Malformed(&'static str),
    Limit {
        resource: &'static str,
        limit: usize,
        observed: usize,
    },
    Name(ConvertError),
    Allocation,
}

impl std::fmt::Display for SyntaxConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(reason) => write!(f, "unsupported macro syntax: {reason}"),
            Self::Limit {
                resource,
                limit,
                observed,
            } => {
                write!(
                    f,
                    "macro syntax exhausted {resource} allowance {limit} at {observed}"
                )
            }
            Self::Name(error) => write!(f, "macro syntax name: {error}"),
            Self::Allocation => f.write_str("macro syntax allocation failed"),
        }
    }
}

impl std::error::Error for SyntaxConversionError {}

type Result<T> = std::result::Result<T, SyntaxConversionError>;

struct Budget {
    limits: SyntaxLimits,
    nodes: usize,
    bytes: usize,
}

impl Budget {
    fn new(source: &SourceText, limits: SyntaxLimits) -> Result<Self> {
        let mut budget = Self {
            limits,
            nodes: 0,
            bytes: 0,
        };
        budget.text(source.len_bytes())?;
        Ok(budget)
    }

    fn nodes(&mut self, count: usize) -> Result<()> {
        self.nodes = self
            .nodes
            .checked_add(count)
            .ok_or(SyntaxConversionError::Limit {
                resource: "nodes",
                limit: self.limits.max_nodes,
                observed: usize::MAX,
            })?;
        if self.nodes > self.limits.max_nodes {
            return Err(SyntaxConversionError::Limit {
                resource: "nodes",
                limit: self.limits.max_nodes,
                observed: self.nodes,
            });
        }
        Ok(())
    }

    fn text(&mut self, count: usize) -> Result<()> {
        self.bytes = self
            .bytes
            .checked_add(count)
            .ok_or(SyntaxConversionError::Limit {
                resource: "text bytes",
                limit: self.limits.max_bytes,
                observed: usize::MAX,
            })?;
        if self.bytes > self.limits.max_bytes {
            return Err(SyntaxConversionError::Limit {
                resource: "text bytes",
                limit: self.limits.max_bytes,
                observed: self.bytes,
            });
        }
        Ok(())
    }

    fn name(&mut self, name: &Name) -> Result<Obj> {
        let mut current = name.clone();
        loop {
            self.nodes(1)?;
            match current.leaf_view() {
                LeafView::Anonymous => break,
                LeafView::Str(text) => self.text(text.len())?,
                LeafView::Num(_) => {}
            }
            current = current.parent();
        }
        Ok(inject_name(name))
    }

    fn string(&mut self, text: &str) -> Result<Obj> {
        self.nodes(1)?;
        self.text(text.len())?;
        Ok(Obj::mk_string(text))
    }
}

fn reserve<T>(values: &mut Vec<T>, additional: usize) -> Result<()> {
    values
        .try_reserve(additional)
        .map_err(|_| SyntaxConversionError::Allocation)
}

fn nat(value: usize) -> Obj {
    if value <= usize::MAX >> 1 {
        Obj::mk_nat(value)
    } else {
        Obj::mk_mpz(&[value as u64], false)
    }
}

fn position(value: &Obj) -> Result<BytePos> {
    if value.is_scalar() {
        return Ok(BytePos(value.unbox()));
    }
    let (_, size, limbs) = value
        .try_mpz_view()
        .ok_or(SyntaxConversionError::Malformed(
            "position is not a natural number",
        ))?;
    if size < 0 {
        return Err(SyntaxConversionError::Malformed("negative position"));
    }
    let value = match limbs {
        [] => 0,
        [value] => usize::try_from(*value)
            .map_err(|_| SyntaxConversionError::Malformed("position exceeds native range"))?,
        _ => {
            return Err(SyntaxConversionError::Malformed(
                "position exceeds native range",
            ));
        }
    };
    Ok(BytePos(value))
}

fn ctor(value: &Obj, tag: u8, fields: usize, scalar_bytes: usize) -> Result<()> {
    let word = std::mem::size_of::<usize>();
    let expected = (word + fields * word + scalar_bytes).div_ceil(word) * word;
    if value.is_scalar()
        || value.obj_tag() != usize::from(tag)
        || usize::from(value.header().other) != fields
        || value.byte_size() != expected
    {
        return Err(SyntaxConversionError::Malformed("constructor layout"));
    }
    Ok(())
}

fn layout(value: &Obj, expected: abi::CtorLayout) -> Result<()> {
    ctor(
        value,
        expected.tag,
        expected.object_fields,
        expected.scalar_bytes,
    )
}

fn child(value: &Obj, index: usize) -> Result<Obj> {
    value
        .try_ctor_child(index)
        .ok_or(SyntaxConversionError::Malformed(
            "missing constructor field",
        ))
}

fn string(value: &Obj) -> Result<&str> {
    let (_, _, chars, bytes) = value
        .try_borrow_string_view()
        .ok_or(SyntaxConversionError::Malformed("string layout"))?;
    let text = std::str::from_utf8(&bytes[..bytes.len() - 1])
        .map_err(|_| SyntaxConversionError::Malformed("string is not UTF-8"))?;
    if text.chars().count() != chars {
        return Err(SyntaxConversionError::Malformed("string character count"));
    }
    Ok(text)
}

fn span(source: &SourceText, start: BytePos, end: BytePos) -> Result<ByteSpan> {
    ByteSpan::new(start, end)
        .filter(|span| source.span_str(*span).is_some())
        .ok_or(SyntaxConversionError::Malformed(
            "source span is not a UTF-8 range",
        ))
}

fn inject_span(source: &SourceText, backing: &Obj, value: ByteSpan) -> Result<Obj> {
    span(source, value.start(), value.end())?;
    Ok(Obj::mk_ctor(
        abi::SUBSTRING_RAW.tag,
        vec![
            backing.clone_ref(),
            nat(value.start().0),
            nat(value.end().0),
        ],
        &[],
    ))
}

fn inject_info(source: &SourceText, backing: &Obj, info: SourceInfo) -> Result<Obj> {
    Ok(match info {
        SourceInfo::None => Obj::mk_nat(abi::SOURCE_NONE_TAG),
        SourceInfo::Synthetic {
            pos,
            end_pos,
            canonical,
        } => Obj::mk_ctor(
            abi::SOURCE_SYNTHETIC.tag,
            vec![nat(pos.0), nat(end_pos.0)],
            &[u8::from(canonical)],
        ),
        SourceInfo::Original {
            leading,
            pos,
            trailing,
            end_pos,
        } => {
            span(source, pos, end_pos)?;
            Obj::mk_ctor(
                abi::SOURCE_ORIGINAL.tag,
                vec![
                    inject_span(source, backing, leading)?,
                    nat(pos.0),
                    inject_span(source, backing, trailing)?,
                    nat(end_pos.0),
                ],
                &[],
            )
        }
    })
}

fn inject_preresolved(values: &[Preresolved], budget: &mut Budget) -> Result<Obj> {
    budget.nodes(values.len())?;
    let mut list = Obj::mk_nat(abi::LIST_NIL_TAG);
    for value in values.iter().rev() {
        let value = match value {
            Preresolved::Namespace { ns } => {
                Obj::mk_ctor(abi::PRERESOLVED_NAMESPACE.tag, vec![budget.name(ns)?], &[])
            }
            Preresolved::Decl { name, fields } => {
                budget.nodes(fields.len())?;
                let mut names = Obj::mk_nat(abi::LIST_NIL_TAG);
                for field in fields.iter().rev() {
                    names =
                        Obj::mk_ctor(abi::LIST_CONS.tag, vec![budget.string(field)?, names], &[]);
                }
                Obj::mk_ctor(
                    abi::PRERESOLVED_DECL.tag,
                    vec![budget.name(name)?, names],
                    &[],
                )
            }
        };
        list = Obj::mk_ctor(abi::LIST_CONS.tag, vec![value, list], &[]);
    }
    Ok(list)
}

/// Inject the full supported tree without borrowing native storage into the VM.
pub(super) fn inject(tree: &Syntax, source: &SourceText, limits: SyntaxLimits) -> Result<Obj> {
    enum Task<'a> {
        Visit(&'a Syntax),
        Node {
            info: SourceInfo,
            kind: &'a Name,
            first: usize,
        },
    }
    let mut budget = Budget::new(source, limits)?;
    let backing = Obj::mk_string(source.as_str());
    let mut tasks = vec![Task::Visit(tree)];
    let mut built = Vec::new();
    while let Some(task) = tasks.pop() {
        let value = match task {
            Task::Visit(tree) => {
                budget.nodes(1)?;
                match tree {
                    Syntax::Missing => Obj::mk_nat(abi::SYNTAX_MISSING_TAG),
                    Syntax::Node { info, kind, args } => {
                        // Charge queued children before reserving their work stack.
                        if args.len() > limits.max_nodes.saturating_sub(budget.nodes) {
                            return Err(SyntaxConversionError::Limit {
                                resource: "nodes",
                                limit: limits.max_nodes,
                                observed: budget.nodes.saturating_add(args.len()),
                            });
                        }
                        reserve(&mut tasks, args.len() + 1)?;
                        tasks.push(Task::Node {
                            info: *info,
                            kind,
                            first: built.len(),
                        });
                        tasks.extend(args.iter().rev().map(Task::Visit));
                        continue;
                    }
                    Syntax::Atom { info, val } => Obj::mk_ctor(
                        abi::SYNTAX_ATOM.tag,
                        vec![inject_info(source, &backing, *info)?, budget.string(val)?],
                        &[],
                    ),
                    Syntax::Ident {
                        info,
                        raw_val,
                        val,
                        preresolved,
                    } => Obj::mk_ctor(
                        abi::SYNTAX_IDENT.tag,
                        vec![
                            inject_info(source, &backing, *info)?,
                            inject_span(source, &backing, *raw_val)?,
                            budget.name(val)?,
                            inject_preresolved(preresolved, &mut budget)?,
                        ],
                        &[],
                    ),
                }
            }
            Task::Node { info, kind, first } => {
                let mut children = Vec::new();
                reserve(&mut children, built.len() - first)?;
                children.extend(built.drain(first..));
                Obj::mk_ctor(
                    abi::SYNTAX_NODE.tag,
                    vec![
                        inject_info(source, &backing, info)?,
                        budget.name(kind)?,
                        Obj::mk_array(children),
                    ],
                    &[],
                )
            }
        };
        reserve(&mut built, 1)?;
        built.push(value);
    }
    built
        .pop()
        .ok_or(SyntaxConversionError::Malformed("empty syntax traversal"))
}

struct Projection<'a> {
    source: &'a SourceText,
    budget: Budget,
    checked_sources: HashSet<usize>,
}

impl Projection<'_> {
    fn text(&mut self, value: &Obj) -> Result<String> {
        self.budget.nodes(1)?;
        let text = string(value)?;
        self.budget.text(text.len())?;
        let mut owned = String::new();
        owned
            .try_reserve_exact(text.len())
            .map_err(|_| SyntaxConversionError::Allocation)?;
        owned.push_str(text);
        Ok(owned)
    }

    fn name(&mut self, value: &Obj) -> Result<Name> {
        let mut current = value.clone_ref();
        loop {
            self.budget.nodes(1)?;
            if current.is_scalar() {
                if current.unbox() != 0 {
                    return Err(SyntaxConversionError::Malformed("anonymous name tag"));
                }
                break;
            }
            match current.obj_tag() {
                1 => {
                    ctor(&current, 1, 2, 8)?;
                    self.budget.text(string(&child(&current, 1)?)?.len())?;
                }
                2 => ctor(&current, 2, 2, 8)?,
                _ => return Err(SyntaxConversionError::Malformed("name constructor")),
            }
            current = child(&current, 0)?;
        }
        Conversion::new()
            .project_name(value)
            .map_err(SyntaxConversionError::Name)
    }

    fn span(&mut self, value: &Obj) -> Result<ByteSpan> {
        self.budget.nodes(1)?;
        layout(value, abi::SUBSTRING_RAW)?;
        let backing = child(value, 0)?;
        let identity = backing.identity_token();
        if !self.checked_sources.contains(&identity) {
            if string(&backing)? != self.source.as_str() {
                return Err(SyntaxConversionError::Malformed(
                    "foreign substring source buffer",
                ));
            }
            self.checked_sources
                .try_reserve(1)
                .map_err(|_| SyntaxConversionError::Allocation)?;
            self.checked_sources.insert(identity);
        }
        span(
            self.source,
            position(&child(value, 1)?)?,
            position(&child(value, 2)?)?,
        )
    }

    fn info(&mut self, value: &Obj) -> Result<SourceInfo> {
        self.budget.nodes(1)?;
        if value.is_scalar() {
            return if value.unbox() == abi::SOURCE_NONE_TAG {
                Ok(SourceInfo::None)
            } else {
                Err(SyntaxConversionError::Malformed("source info scalar tag"))
            };
        }
        match value.obj_tag() {
            tag if tag == usize::from(abi::SOURCE_ORIGINAL.tag) => {
                layout(value, abi::SOURCE_ORIGINAL)?;
                let leading = self.span(&child(value, 0)?)?;
                let pos = position(&child(value, 1)?)?;
                let trailing = self.span(&child(value, 2)?)?;
                let end_pos = position(&child(value, 3)?)?;
                span(self.source, pos, end_pos)?;
                Ok(SourceInfo::Original {
                    leading,
                    pos,
                    trailing,
                    end_pos,
                })
            }
            tag if tag == usize::from(abi::SOURCE_SYNTHETIC.tag) => {
                layout(value, abi::SOURCE_SYNTHETIC)?;
                let raw = value
                    .try_ctor_scalar_u32(
                        abi::SOURCE_SYNTHETIC.object_fields * std::mem::size_of::<usize>(),
                    )
                    .ok_or(SyntaxConversionError::Malformed(
                        "source info canonical flag",
                    ))?;
                let canonical = match raw.to_ne_bytes()[0] {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(SyntaxConversionError::Malformed(
                            "source info canonical flag",
                        ));
                    }
                };
                Ok(SourceInfo::Synthetic {
                    pos: position(&child(value, 0)?)?,
                    end_pos: position(&child(value, 1)?)?,
                    canonical,
                })
            }
            _ => Err(SyntaxConversionError::Malformed("source info constructor")),
        }
    }

    fn list(&mut self, value: &Obj) -> Result<Vec<Obj>> {
        let mut values = Vec::new();
        let mut current = value.clone_ref();
        loop {
            self.budget.nodes(1)?;
            if current.is_scalar() {
                if current.unbox() != abi::LIST_NIL_TAG {
                    return Err(SyntaxConversionError::Malformed("list nil tag"));
                }
                return Ok(values);
            }
            layout(&current, abi::LIST_CONS)?;
            reserve(&mut values, 1)?;
            values.push(child(&current, 0)?);
            current = child(&current, 1)?;
        }
    }

    fn preresolved(&mut self, value: &Obj) -> Result<Vec<Preresolved>> {
        let values = self.list(value)?;
        let mut result = Vec::new();
        reserve(&mut result, values.len())?;
        for value in values {
            self.budget.nodes(1)?;
            result.push(match value.obj_tag() {
                tag if tag == usize::from(abi::PRERESOLVED_NAMESPACE.tag) => {
                    layout(&value, abi::PRERESOLVED_NAMESPACE)?;
                    Preresolved::Namespace {
                        ns: self.name(&child(&value, 0)?)?,
                    }
                }
                tag if tag == usize::from(abi::PRERESOLVED_DECL.tag) => {
                    layout(&value, abi::PRERESOLVED_DECL)?;
                    let name = self.name(&child(&value, 0)?)?;
                    let fields = self.list(&child(&value, 1)?)?;
                    let mut strings = Vec::new();
                    reserve(&mut strings, fields.len())?;
                    for field in fields {
                        strings.push(self.text(&field)?);
                    }
                    Preresolved::Decl {
                        name,
                        fields: strings,
                    }
                }
                _ => {
                    return Err(SyntaxConversionError::Malformed(
                        "preresolution constructor",
                    ));
                }
            });
        }
        Ok(result)
    }
}

/// Project a result only when every original source substring retains its bytes.
pub(super) fn project(value: &Obj, source: &SourceText, limits: SyntaxLimits) -> Result<Syntax> {
    enum Task {
        Visit(Obj),
        Node {
            identity: usize,
            info: SourceInfo,
            kind: Name,
            first: usize,
        },
    }
    let mut projection = Projection {
        source,
        budget: Budget::new(source, limits)?,
        checked_sources: HashSet::new(),
    };
    let mut tasks = vec![Task::Visit(value.clone_ref())];
    let mut built = Vec::new();
    let mut ancestors = HashSet::new();
    while let Some(task) = tasks.pop() {
        let tree = match task {
            Task::Visit(value) => {
                projection.budget.nodes(1)?;
                if value.is_scalar() {
                    if value.unbox() != abi::SYNTAX_MISSING_TAG {
                        return Err(SyntaxConversionError::Malformed("syntax missing tag"));
                    }
                    Syntax::Missing
                } else {
                    match value.obj_tag() {
                        tag if tag == usize::from(abi::SYNTAX_NODE.tag) => {
                            layout(&value, abi::SYNTAX_NODE)?;
                            let identity = value.identity_token();
                            ancestors
                                .try_reserve(1)
                                .map_err(|_| SyntaxConversionError::Allocation)?;
                            if !ancestors.insert(identity) {
                                return Err(SyntaxConversionError::Malformed("cyclic syntax"));
                            }
                            let info = projection.info(&child(&value, 0)?)?;
                            let kind = projection.name(&child(&value, 1)?)?;
                            let array = child(&value, 2)?;
                            let (count, _) = array
                                .try_array_view()
                                .ok_or(SyntaxConversionError::Malformed("syntax argument array"))?;
                            if count > limits.max_nodes.saturating_sub(projection.budget.nodes) {
                                return Err(SyntaxConversionError::Limit {
                                    resource: "nodes",
                                    limit: limits.max_nodes,
                                    observed: projection.budget.nodes.saturating_add(count),
                                });
                            }
                            reserve(&mut tasks, count + 1)?;
                            tasks.push(Task::Node {
                                identity,
                                info,
                                kind,
                                first: built.len(),
                            });
                            tasks.extend(
                                (0..count)
                                    .rev()
                                    .map(|index| Task::Visit(array.array_child(index))),
                            );
                            continue;
                        }
                        tag if tag == usize::from(abi::SYNTAX_ATOM.tag) => {
                            layout(&value, abi::SYNTAX_ATOM)?;
                            Syntax::Atom {
                                info: projection.info(&child(&value, 0)?)?,
                                val: projection.text(&child(&value, 1)?)?,
                            }
                        }
                        tag if tag == usize::from(abi::SYNTAX_IDENT.tag) => {
                            layout(&value, abi::SYNTAX_IDENT)?;
                            Syntax::Ident {
                                info: projection.info(&child(&value, 0)?)?,
                                raw_val: projection.span(&child(&value, 1)?)?,
                                val: projection.name(&child(&value, 2)?)?,
                                preresolved: projection.preresolved(&child(&value, 3)?)?,
                            }
                        }
                        _ => return Err(SyntaxConversionError::Malformed("syntax constructor")),
                    }
                }
            }
            Task::Node {
                identity,
                info,
                kind,
                first,
            } => {
                ancestors.remove(&identity);
                let mut args = Vec::new();
                reserve(&mut args, built.len() - first)?;
                args.extend(built.drain(first..));
                Syntax::Node { info, kind, args }
            }
        };
        reserve(&mut built, 1)?;
        built.push(tree);
    }
    built
        .pop()
        .ok_or(SyntaxConversionError::Malformed("empty syntax traversal"))
}

#[cfg(test)]
mod tests;
