//! Native Arrays share the pin's existing declaration contracts.
//!
//! The inventories already used by Array iteration and native text operations
//! contain these logical models. Walk each selected operation's actual closure
//! against those immutable digests instead of requiring an unrelated text
//! module to be imported. A family name or an extern annotation alone grants
//! no representation authority. Runtime replacements and initializers are
//! checked separately, because declaration digests do not contain journals.
//!
//! `arrays/*.txt` adds missing declarations and execution metadata for the
//! actual Push/Set/Pop/modifyM closure. It includes rows formerly carrying only
//! a text-model hash, so companion presence and explicit replacements stay
//! bound. To reproduce all raw rows from the independent decoded pin fixture:
//! `FLN_DUMP_NATIVE_ARRAY_CONTRACTS=1 cargo test -p fln --lib
//! runtime::arrays::tests::actual_array_model_maps_storage_and_every_supported_primitive_without_kernel_changes
//! -- --nocapture`. Keep entries absent from the existing five-column Array
//! inventories; overlapping hashes must agree with the existing text models.
use super::*;
use fln_core::name::LeafView;
use fln_elab::implemented_by::ImplementedByTable;
use std::collections::BTreeMap;
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    FromList,
    ToList,
    Empty,
    MkEmpty,
    Push,
    Size,
    Get,
    Set,
    Pop,
}

impl Operation {
    pub(crate) const ALL: [Self; 9] = [
        Self::FromList,
        Self::ToList,
        Self::Empty,
        Self::MkEmpty,
        Self::Push,
        Self::Size,
        Self::Get,
        Self::Set,
        Self::Pop,
    ];

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::FromList => "Array.mk",
            Self::ToList => "Array.toList",
            Self::Empty => "Array.emptyWithCapacity",
            Self::MkEmpty => "Array.mkEmpty",
            Self::Push => "Array.push",
            Self::Size => "Array.size",
            Self::Get => "Array.getInternal",
            Self::Set => "Array.set",
            Self::Pop => "Array.pop",
        }
    }

    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|operation| requested == &name(operation.label()))
    }

    pub(crate) fn index(self) -> usize {
        self as usize
    }

    pub(crate) fn source_arity(self) -> usize {
        match self {
            Self::FromList
            | Self::ToList
            | Self::Empty
            | Self::MkEmpty
            | Self::Size
            | Self::Pop => 2,
            Self::Push => 3,
            Self::Get => 4,
            Self::Set => 5,
        }
    }
}

#[derive(Clone, Copy)]
struct Expected {
    digest: &'static str,
    /// The Array inventories additionally bind execution selection. The text
    /// inventories bind only declaration identity, so added replacements there
    /// are refused rather than silently inheriting the native model.
    execution: Option<(&'static str, &'static str, &'static str)>,
}

fn inventory() -> &'static BTreeMap<&'static str, Expected> {
    static INVENTORY: OnceLock<BTreeMap<&'static str, Expected>> = OnceLock::new();
    INVENTORY.get_or_init(|| {
        let mut rows = BTreeMap::new();
        for text in [
            include_str!("array_iteration/dependencies.txt"),
            include_str!("array_iteration/size_dependencies.txt"),
            include_str!("array_iteration/get_dependencies.txt"),
            include_str!("array_fold/dependencies.txt"),
            include_str!("arrays/dependencies.txt"),
            include_str!("arrays/modify_dependencies.txt"),
        ] {
            for line in text.lines() {
                let fields: Vec<_> = line.split('\t').collect();
                let [label, digest, implementation, native, companion] = fields.as_slice() else {
                    unreachable!("fixed Array dependency inventory width");
                };
                let expected = Expected {
                    digest,
                    execution: Some((implementation, native, companion)),
                };
                if let Some(previous) = rows.insert(*label, expected) {
                    assert_eq!(previous.digest, *digest, "one pinned declaration identity");
                    assert_eq!(
                        previous.execution, expected.execution,
                        "one pinned selection"
                    );
                }
            }
        }
        for text in [
            include_str!("string_append/dependencies.txt"),
            include_str!("string_bytes/dependencies.txt"),
        ] {
            for line in text.lines() {
                let (label, digest) = line.split_once('\t').expect("fixed text dependency row");
                let entry = rows.entry(label).or_insert(Expected {
                    digest,
                    execution: None,
                });
                assert_eq!(entry.digest, digest, "one pinned declaration identity");
            }
        }
        for line in include_str!("string_bootstrap/dependencies.txt").lines() {
            let (_, rest) = line.split_once('\t').expect("fixed text membership row");
            let (label, digest) = rest.split_once('\t').expect("fixed text dependency row");
            let entry = rows.entry(label).or_insert(Expected {
                digest,
                execution: None,
            });
            assert_eq!(entry.digest, digest, "one pinned declaration identity");
        }
        rows
    })
}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn encoded_name(
    label: &Name,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<String, IngressError> {
    let mut components = Vec::new();
    let mut current = label.clone();
    loop {
        charge_catalog_node(visited, limits)?;
        match current.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(text) => components.push(format!("s:{text}")),
            LeafView::Num(number) => components.push(format!("n:{number}")),
        }
        current = current.parent();
    }
    components.reverse();
    Ok(components.join("/"))
}

fn mismatch() -> IngressError {
    IngressError::UnsupportedNode {
        kind: "native Array differs from its complete pinned logical and execution contract",
    }
}

/// Only an authenticated pair of constructor and projection externs selects
/// native storage. Source-only records with the same spelling stay records.
pub(crate) fn family_matches(
    environment: &Environment,
    implementations: &ImplementedByTable,
    initializers: Option<&BTreeSet<Name>>,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    for label in ["Array.mk", "Array.toList"] {
        if !extern_attribute_matches(environment, &name(label), true, externs, visited, limits)? {
            return Ok(false);
        }
    }
    check_closure(
        environment,
        [
            name("Array.mk"),
            name("Array.toList"),
            name("Array.rec"),
            name("List.rec"),
        ],
        implementations,
        initializers,
        externs,
        visited,
        limits,
    )?;
    Ok(true)
}

pub(crate) fn operation_matches(
    environment: &Environment,
    operation: Operation,
    implementations: &ImplementedByTable,
    initializers: Option<&BTreeSet<Name>>,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let requested = name(operation.label());
    if !extern_attribute_matches(environment, &requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    check_closure(
        environment,
        [requested],
        implementations,
        initializers,
        externs,
        visited,
        limits,
    )?;
    Ok(true)
}

pub(crate) fn modify_matches(
    environment: &Environment,
    implementations: &ImplementedByTable,
    initializers: Option<&BTreeSet<Name>>,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    check_closure(
        environment,
        [name("Array.modifyM")],
        implementations,
        initializers,
        externs,
        visited,
        limits,
    )
}

fn mk_empty_matches(
    environment: &Environment,
    comparison: &mut Comparison<'_>,
) -> Result<bool, IngressError> {
    let (Some(ConstantInfo::Defn(actual)), Some(ConstantInfo::Defn(expected))) = (
        environment.find(&name("Array.mkEmpty")),
        environment.find(&name("Array.emptyWithCapacity")),
    ) else {
        return Ok(false);
    };
    Ok(actual.safety == DefinitionSafety::Safe
        && actual.all == [actual.base.name.clone()]
        && actual.base.level_params == expected.base.level_params
        && comparison.expression(&actual.base.type_, &expected.base.type_)?
        && comparison.expression(&actual.value, &expected.value)?)
}

fn check_closure(
    environment: &Environment,
    roots: impl IntoIterator<Item = Name>,
    implementations: &ImplementedByTable,
    initializers: Option<&BTreeSet<Name>>,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    let mut pending: Vec<_> = roots.into_iter().collect();
    let mut seen = HashSet::new();
    let mut seen_expressions = HashSet::new();
    while let Some(label) = pending.pop() {
        charge_catalog_node(visited, limits)?;
        if !seen.insert(label.clone()) {
            continue;
        }
        let key = encoded_name(&label, visited, limits)?;
        let expected = inventory().get(key.as_str());
        if label == name("Array.mkEmpty") {
            if !mk_empty_matches(environment, &mut Comparison { visited, limits })? {
                return Err(mismatch());
            }
            pending.push(name("Array.emptyWithCapacity"));
        } else if expected.is_none_or(|expected| {
            environment
                .entry(&label)
                .is_none_or(|entry| entry.digest().to_hex() != expected.digest)
        }) {
            return Err(mismatch());
        }
        if initializers.is_some_and(|names| names.contains(&label)) {
            return Err(mismatch());
        }
        let selected = implementations.get(&label);
        let expected_implementation = expected.and_then(|row| row.execution).map(|row| row.0);
        match (selected, expected_implementation) {
            (None, None | Some("-")) => {}
            (Some(actual), Some(expected))
                if encoded_name(actual, visited, limits)? == expected =>
            {
                pending.push(actual.clone());
            }
            _ => return Err(mismatch()),
        }
        check_selected_extern_attribute(environment, &label, externs, visited, limits)?;
        let has_extern = externs
            .as_ref()
            .is_some_and(|table| table.get(&label).is_some());
        if let Some((_, native, _)) = expected.and_then(|row| row.execution)
            && has_extern != (native == "extern")
        {
            return Err(mismatch());
        }
        let info = environment.find(&label).ok_or_else(mismatch)?;
        let has_body = matches!(info, ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe)
            || matches!(info, ConstantInfo::Opaque(value) if !value.is_unsafe);
        if has_body {
            let companion = Name::str(label.clone(), "_unsafe_rec");
            let actual_companion = environment.contains(&companion).then_some(companion);
            if let Some((_, _, expected)) = expected.and_then(|row| row.execution) {
                let actual = actual_companion
                    .as_ref()
                    .map(|name| encoded_name(name, visited, limits))
                    .transpose()?;
                if actual.as_deref() != (expected != "-").then_some(expected) {
                    return Err(mismatch());
                }
            }
            pending.extend(actual_companion);
        }
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.ctors.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
        }
        while let Some(expression) = expressions.pop() {
            charge_catalog_node(visited, limits)?;
            if !seen_expressions.insert(expression.allocation_identity()) {
                continue;
            }
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    Ok(())
}
