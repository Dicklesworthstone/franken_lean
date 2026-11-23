//! Checked declarations selected by the pin's `Lean.Meta.Symm.symmExt`.
//!
//! The stored discrimination paths are selection data, never proof authority.
//! Every use constructs an ordinary application and is checked by the normal
//! elaborator and admission seats. Paths are captured at registration time so
//! later reducibility changes cannot silently alter the registry's order.
use crate::instances::{InstanceRegistryError, discr_tree::Key, read_name, write_name};
use fln_core::{
    expr::{Expr, ExprNode},
    name::Name,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, ExtensionState, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;
use std::sync::Arc;

const MAGIC: &[u8] = b"FLNSYMM\x01";
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;
const MAX_SCOPE_BYTES: usize = 16 * 1024 * 1024;
const MAX_VALIDATION_STEPS: usize = 1_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymmLemma {
    pub declaration: Name,
    pub keys: Vec<Key>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymmEntry {
    pub lemma: SymmLemma,
    /// `None` is a global registration. Local entries live in `ActiveScopes`.
    pub namespace: Option<Name>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymmRegistryError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    InvalidLemma(Name),
    UnsupportedLemma(Name),
}

impl std::fmt::Display for SymmRegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native symmetry-lemma journal"),
            Self::Limit => f.write_str("native symmetry-lemma journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a symmetry-lemma entry names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::InvalidLemma(name) => write!(
                f,
                "invalid symmetry-lemma entry for {}",
                name.to_display_string()
            ),
            Self::UnsupportedLemma(name) => write!(
                f,
                "unsupported symmetry-lemma type normalization for {}",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for SymmRegistryError {}

fn codec(problem: InstanceRegistryError) -> SymmRegistryError {
    match problem {
        InstanceRegistryError::Limit => SymmRegistryError::Limit,
        _ => SymmRegistryError::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "symm", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

fn spend(remaining: &mut usize) -> Result<(), SymmRegistryError> {
    *remaining = remaining.checked_sub(1).ok_or(SymmRegistryError::Limit)?;
    Ok(())
}

fn scan(root: &Expr, remaining: &mut usize) -> Result<(), SymmRegistryError> {
    let mut pending = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(expr) = pending.pop() {
        spend(remaining)?;
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::ForallE {
                binder_type, body, ..
            }
            | ExprNode::Lam {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(())
}

/// A bounded header reduction is sufficient to discover additional telescope
/// binders. It never serves as a proof checker, nor guesses a stuck recursor's
/// result. Loose variables here denote the already-open declaration binders.
fn header_whnf(
    env: &Environment,
    name: &Name,
    expression: &Expr,
    remaining: &mut usize,
) -> Result<Expr, SymmRegistryError> {
    let mut head = expression.clone();
    let mut arguments = Vec::new();
    loop {
        spend(remaining)?;
        match head.node() {
            ExprNode::App { f, a } => {
                arguments.push(a.clone());
                head = f.clone();
            }
            ExprNode::MData { expr, .. } => head = expr.clone(),
            ExprNode::LetE { body, value, .. } => {
                scan(body, remaining)?;
                head = body
                    .subst_loose(0, std::slice::from_ref(value))
                    .map_err(|_| SymmRegistryError::Malformed)?;
            }
            ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                scan(body, remaining)?;
                let argument = arguments.pop().ok_or(SymmRegistryError::Malformed)?;
                head = body
                    .subst_loose(0, &[argument])
                    .map_err(|_| SymmRegistryError::Malformed)?;
            }
            ExprNode::Proj { .. } => return Err(SymmRegistryError::UnsupportedLemma(name.clone())),
            ExprNode::Const {
                name: head_name,
                levels,
            } => {
                let info = env
                    .find(head_name)
                    .ok_or_else(|| SymmRegistryError::UnknownDeclaration(head_name.clone()))?;
                match info {
                    ConstantInfo::Rec(_) | ConstantInfo::Quot(_) => {
                        return Err(SymmRegistryError::UnsupportedLemma(name.clone()));
                    }
                    ConstantInfo::Defn(definition) => {
                        if !arguments.is_empty()
                            && let Some(projection) = crate::records::projection::class_projection(
                                env,
                                definition,
                                || spend(remaining),
                            )?
                            && crate::instances::InstanceRegistry::read(env)
                                .map_err(codec)?
                                .is_class(&projection.structure)
                        {
                            return Err(SymmRegistryError::UnsupportedLemma(name.clone()));
                        }
                        let status = crate::reducibility::table(env)
                            .map_err(|error| match error {
                                crate::reducibility::ReducibilityError::Limit
                                | crate::reducibility::ReducibilityError::Instances(
                                    InstanceRegistryError::Limit,
                                ) => SymmRegistryError::Limit,
                                _ => SymmRegistryError::Malformed,
                            })?
                            .get(head_name);
                        let reducible = status
                            .map_or(definition.hints == ReducibilityHints::Abbrev, |status| {
                                status == crate::reducibility::Reducibility::Reducible
                            });
                        if !reducible {
                            break;
                        }
                        if definition.safety != DefinitionSafety::Safe
                            || env.contains(&Name::str(head_name.clone(), "_sunfold"))
                        {
                            return Err(SymmRegistryError::UnsupportedLemma(name.clone()));
                        }
                        head = crate::universe::parameters::instantiate(
                            || spend(remaining),
                            || SymmRegistryError::Malformed,
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?;
                    }
                    _ => break,
                }
            }
            _ => break,
        }
    }
    for argument in arguments.into_iter().rev() {
        head = Expr::app(head, argument);
    }
    Ok(head)
}

fn validate_header(
    env: &Environment,
    name: &Name,
    remaining: &mut usize,
) -> Result<(), SymmRegistryError> {
    let info = env
        .find(name)
        .ok_or_else(|| SymmRegistryError::UnknownDeclaration(name.clone()))?;
    let mut current = info.constant_val().type_.clone();
    let mut nonempty = false;
    let blocked_alias;
    loop {
        spend(remaining)?;
        if let ExprNode::ForallE { body, .. } = current.node() {
            nonempty = true;
            current = body.clone();
        } else {
            let reduced = header_whnf(env, name, &current, remaining)?;
            if matches!(reduced.node(), ExprNode::ForallE { .. }) {
                current = reduced;
            } else {
                let mut head = &reduced;
                loop {
                    spend(remaining)?;
                    match head.node() {
                        ExprNode::App { f, .. } => head = f,
                        ExprNode::MData { expr, .. } => head = expr,
                        _ => break,
                    }
                }
                blocked_alias = matches!(head.node(), ExprNode::Const { name, .. } if matches!(env.find(name), Some(ConstantInfo::Defn(_))));
                break;
            }
        }
    }
    // forallMetaTelescopeReducing keeps the ORIGINAL conclusion when WHNF
    // does not expose another forall (Lean/Meta/Basic.lean). Meta.reduce then
    // skips this checked type by default, even if it is an alias for Nat.
    if nonempty
        && matches!(current.node(), ExprNode::App { f, .. } if matches!(f.node(), ExprNode::App { .. }))
    {
        Ok(())
    } else if blocked_alias {
        // Imported artifacts preserve the key and final reducibility policy,
        // not the policy in effect when the tag was registered. A formerly
        // reducible telescope alias may be opaque now (the pin permits this
        // with allowUnsafeReducibility). Missing history is not evidence of
        // an invalid original registration. Native source additionally runs
        // the real current-context compiler before it reaches this gate.
        Err(SymmRegistryError::UnsupportedLemma(name.clone()))
    } else {
        Err(SymmRegistryError::InvalidLemma(name.clone()))
    }
}

fn validate(
    env: &Environment,
    lemma: &SymmLemma,
    remaining: &mut usize,
) -> Result<(), SymmRegistryError> {
    if lemma.declaration.is_anonymous() {
        return Err(SymmRegistryError::InvalidLemma(lemma.declaration.clone()));
    }
    if !env.contains(&lemma.declaration) {
        return Err(SymmRegistryError::UnknownDeclaration(
            lemma.declaration.clone(),
        ));
    }
    validate_header(env, &lemma.declaration, remaining)?;
    // One complete prefix-coded discrimination path. An exported declaration's
    // telescope is closed, so a path cannot depend on a lexical free variable.
    if lemma.keys.is_empty() || lemma.keys.len() > 4_096 {
        return Err(SymmRegistryError::InvalidLemma(lemma.declaration.clone()));
    }
    let mut pending = 1usize;
    for key in &lemma.keys {
        spend(remaining)?;
        pending = pending
            .checked_sub(1)
            .and_then(|pending| pending.checked_add(key.arity()))
            .ok_or(SymmRegistryError::Malformed)?;
        match key {
            Key::FVar(..) => return Err(SymmRegistryError::Malformed),
            Key::Const(name, _) | Key::Proj(name, _, _) if !env.contains(name) => {
                return Err(SymmRegistryError::UnknownDeclaration(name.clone()));
            }
            _ => {}
        }
    }
    if pending != 0 {
        return Err(SymmRegistryError::Malformed);
    }
    Ok(())
}

fn encode(entry: &SymmEntry) -> Result<Vec<u8>, SymmRegistryError> {
    let mut payload = MAGIC.to_vec();
    match &entry.namespace {
        None => payload.push(0),
        Some(namespace) if !namespace.is_anonymous() => {
            payload.push(1);
            write_name(namespace, &mut payload).map_err(codec)?;
        }
        Some(_) => return Err(SymmRegistryError::Malformed),
    }
    write_name(&entry.lemma.declaration, &mut payload).map_err(codec)?;
    crate::instances::discr_tree::write_keys(&entry.lemma.keys, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(SymmRegistryError::Limit);
    }
    Ok(payload)
}

fn decode(payload: &[u8]) -> Result<SymmEntry, SymmRegistryError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(SymmRegistryError::Limit);
    }
    let mut bytes = payload
        .strip_prefix(MAGIC)
        .ok_or(SymmRegistryError::Malformed)?;
    let Some((&kind, remaining)) = bytes.split_first() else {
        return Err(SymmRegistryError::Malformed);
    };
    bytes = remaining;
    let namespace = match kind {
        0 => None,
        1 => {
            let namespace = read_name(&mut bytes).map_err(codec)?;
            if namespace.is_anonymous() {
                return Err(SymmRegistryError::Malformed);
            }
            Some(namespace)
        }
        _ => return Err(SymmRegistryError::Malformed),
    };
    let declaration = read_name(&mut bytes).map_err(codec)?;
    let keys = crate::instances::discr_tree::read_keys(&mut bytes).map_err(codec)?;
    if !bytes.is_empty() {
        return Err(SymmRegistryError::Malformed);
    }
    Ok(SymmEntry {
        lemma: SymmLemma { declaration, keys },
        namespace,
    })
}

/// Append a checked registration. Repeated rows are retained: `symmExt.add`
/// appends them even when inserting the same name/path leaves its tree alone.
/// The registering module may tag an imported declaration at the pin.
pub fn register(env: &Environment, entry: SymmEntry) -> Result<Environment, SymmRegistryError> {
    let mut remaining = MAX_VALIDATION_STEPS;
    validate(env, &entry.lemma, &mut remaining)?;
    read(env)?;
    let payload = encode(&entry)?;
    let env = match env.extension(&journal_name()) {
        Some(state) if state.len() >= MAX_ROWS => return Err(SymmRegistryError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| SymmRegistryError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| SymmRegistryError::Malformed)
}

pub fn read(env: &Environment) -> Result<Vec<SymmEntry>, SymmRegistryError> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(Vec::new());
    };
    if extension.descriptor != descriptor() {
        return Err(SymmRegistryError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(SymmRegistryError::Limit);
    }
    let mut entries = Vec::new();
    let mut remaining = MAX_VALIDATION_STEPS;
    for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
        let entry = decode(&entry.payload)?;
        validate(validation, &entry.lemma, &mut remaining)?;
        entries.push(entry);
    }
    Ok(entries)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ActivationKind {
    Namespace(Name),
    Local(SymmLemma),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Activation {
    kind: ActivationKind,
    at: usize,
}

/// Lexical state anchored to the exact registration prefix that it observed.
/// Restoring a section snapshot removes local rows and namespace activations,
/// while declarations and later global journal entries remain available.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ActiveScopes {
    activations: Arc<Vec<Activation>>,
    anchor: Option<ExtensionState>,
    bytes: usize,
}

impl ActiveScopes {
    pub fn is_active(&self, namespace: &Name) -> bool {
        self.activations.iter().any(
            |entry| matches!(&entry.kind, ActivationKind::Namespace(name) if name == namespace),
        )
    }

    pub fn activate(
        &mut self,
        env: &Environment,
        namespace: &Name,
    ) -> Result<(), SymmRegistryError> {
        self.validate_prefix(env)?;
        read(env)?;
        if namespace.is_anonymous() || self.is_active(namespace) {
            return Ok(());
        }
        let mut encoded = Vec::new();
        write_name(namespace, &mut encoded).map_err(codec)?;
        self.push(
            env,
            ActivationKind::Namespace(namespace.clone()),
            encoded.len(),
        )
    }

    pub fn register_local(
        &mut self,
        env: &Environment,
        lemma: SymmLemma,
    ) -> Result<(), SymmRegistryError> {
        self.validate_prefix(env)?;
        read(env)?;
        let mut remaining = MAX_VALIDATION_STEPS;
        validate(env, &lemma, &mut remaining)?;
        let payload = encode(&SymmEntry {
            lemma: lemma.clone(),
            namespace: None,
        })?;
        self.push(env, ActivationKind::Local(lemma), payload.len())
    }

    fn push(
        &mut self,
        env: &Environment,
        kind: ActivationKind,
        bytes: usize,
    ) -> Result<(), SymmRegistryError> {
        let bytes = self
            .bytes
            .checked_add(bytes)
            .filter(|bytes| *bytes <= MAX_SCOPE_BYTES)
            .ok_or(SymmRegistryError::Limit)?;
        if self.activations.len() >= MAX_ROWS {
            return Err(SymmRegistryError::Limit);
        }
        let anchor = env.extension(&journal_name()).cloned();
        let at = anchor.as_ref().map_or(0, ExtensionState::len);
        Arc::make_mut(&mut self.activations).push(Activation { kind, at });
        self.anchor = anchor;
        self.bytes = bytes;
        Ok(())
    }

    fn validate_prefix(&self, env: &Environment) -> Result<(), SymmRegistryError> {
        if let Some(anchor) = &self.anchor {
            let current = env
                .extension(&journal_name())
                .ok_or(SymmRegistryError::Malformed)?;
            if current.descriptor != anchor.descriptor
                || current.len() < anchor.len()
                || !anchor.entries().zip(current.entries()).all(|(a, b)| a == b)
            {
                return Err(SymmRegistryError::Malformed);
            }
        }
        Ok(())
    }
}

/// Registration order in the currently active tree, before discrimination.
/// Activating a namespace inserts its earlier rows at the activation point;
/// later scoped rows enter immediately while that namespace remains active.
pub fn read_with_scopes(
    env: &Environment,
    scopes: &ActiveScopes,
) -> Result<Vec<SymmLemma>, SymmRegistryError> {
    scopes.validate_prefix(env)?;
    let entries = read(env)?;
    let mut active = BTreeSet::new();
    let mut visible: Vec<SymmLemma> = Vec::new();
    let mut remaining = MAX_VALIDATION_STEPS;
    let mut activation = scopes.activations.iter().peekable();
    let insert = |visible: &mut Vec<SymmLemma>, lemma: &SymmLemma| {
        if env.contains(&lemma.declaration) && !visible.contains(lemma) {
            visible.push(lemma.clone());
        }
    };
    for at in 0..=entries.len() {
        while activation
            .peek()
            .is_some_and(|activation| activation.at == at)
        {
            let item = activation.next().ok_or(SymmRegistryError::Malformed)?;
            match &item.kind {
                ActivationKind::Namespace(namespace) => {
                    if active.insert(namespace.clone()) {
                        for entry in &entries[..at] {
                            if entry.namespace.as_ref() == Some(namespace) {
                                insert(&mut visible, &entry.lemma);
                            }
                        }
                    }
                }
                ActivationKind::Local(lemma) => {
                    validate(env, lemma, &mut remaining)?;
                    insert(&mut visible, lemma);
                }
            }
        }
        if let Some(entry) = entries.get(at)
            && entry
                .namespace
                .as_ref()
                .is_none_or(|namespace| active.contains(namespace))
        {
            insert(&mut visible, &entry.lemma);
        }
    }
    if activation.next().is_some() {
        return Err(SymmRegistryError::Malformed);
    }
    Ok(visible)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::{expr::BinderInfo, level::Level};
    use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal};

    fn name(value: &str) -> Name {
        Name::from_components([value])
    }
    fn constant(value: &str) -> Expr {
        Expr::const_(name(value), Vec::new())
    }
    fn forall(domain: Expr, body: Expr) -> Expr {
        Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
    }
    fn relation(left: Expr, right: Expr) -> Expr {
        Expr::app(Expr::app(constant("R"), left), right)
    }
    fn axiom(env: Environment, label: &str, type_: Expr) -> Environment {
        env.add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name(label),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        }))
        .unwrap()
    }
    fn base() -> Environment {
        let env = axiom(Environment::new(), "Nat", Expr::sort(Level::one()));
        axiom(
            env,
            "R",
            forall(
                Expr::sort(Level::one()),
                forall(Expr::sort(Level::one()), Expr::sort(Level::zero())),
            ),
        )
    }
    fn add_lemma(env: Environment, label: &str) -> Environment {
        axiom(
            env,
            label,
            forall(
                Expr::sort(Level::one()),
                forall(
                    relation(Expr::bvar(0).unwrap(), Expr::bvar(0).unwrap()),
                    relation(Expr::bvar(1).unwrap(), Expr::bvar(1).unwrap()),
                ),
            ),
        )
    }
    fn lemma(label: &str) -> SymmLemma {
        SymmLemma {
            declaration: name(label),
            keys: vec![Key::Const(name("R"), 0)],
        }
    }
    fn entry(label: &str, scope: Option<&str>) -> SymmEntry {
        SymmEntry {
            lemma: lemma(label),
            namespace: scope.map(name),
        }
    }

    #[test]
    fn active_tree_replays_namespace_local_and_global_order_without_exporting_locals() {
        let mut env = base();
        for label in ["first", "scoped", "second", "local", "third"] {
            env = add_lemma(env, label);
        }
        env = register(&env, entry("first", None)).unwrap();
        env = register(&env, entry("scoped", Some("Group"))).unwrap();
        env = register(&env, entry("second", None)).unwrap();
        let mut scopes = ActiveScopes::default();
        scopes.activate(&env, &name("Group")).unwrap();
        scopes.register_local(&env, lemma("local")).unwrap();
        env = register(&env, entry("third", None)).unwrap();
        env = register(&env, entry("first", None)).unwrap();
        assert_eq!(
            read_with_scopes(&env, &scopes)
                .unwrap()
                .into_iter()
                .map(|lemma| lemma.declaration)
                .collect::<Vec<_>>(),
            ["first", "second", "scoped", "local", "third"].map(name)
        );
        assert_eq!(
            read_with_scopes(&env, &ActiveScopes::default())
                .unwrap()
                .into_iter()
                .map(|lemma| lemma.declaration)
                .collect::<Vec<_>>(),
            ["first", "second", "third"].map(name)
        );
        assert_eq!(
            read(&env).unwrap().len(),
            5,
            "duplicate journal entry retained, lexical row not exported"
        );
    }

    #[test]
    fn persisted_rows_require_nonempty_binary_types_without_assuming_converse_shape() {
        let env = add_lemma(base(), "keep");
        let env = axiom(
            env,
            "zeroBinders",
            relation(constant("Nat"), constant("Nat")),
        );
        let env = axiom(env, "nonBinary", forall(constant("Nat"), constant("Nat")));
        assert!(register(&env, entry("keep", None)).is_ok());
        for bad in ["zeroBinders", "nonBinary"] {
            assert_eq!(
                register(&env, entry(bad, None)),
                Err(SymmRegistryError::InvalidLemma(name(bad)))
            );
            let forged = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), encode(&entry(bad, None)).unwrap())
                .unwrap();
            assert_eq!(
                read(&forged),
                Err(SymmRegistryError::InvalidLemma(name(bad)))
            );
            assert!(
                env.extension(&journal_name()).is_none(),
                "failed registration leaves base unchanged"
            );
        }
    }

    #[test]
    fn header_keeps_final_alias_but_opens_an_alias_that_exposes_more_binders() {
        let mut env = base();
        for (label, value) in [
            ("ValueAlias", constant("Nat")),
            ("ArrowAlias", forall(constant("Nat"), constant("Nat"))),
        ] {
            env = env
                .add_decl(ConstantInfo::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: name(label),
                        level_params: Vec::new(),
                        type_: forall(
                            constant("Nat"),
                            forall(constant("Nat"), Expr::sort(Level::one())),
                        ),
                    },
                    value: Expr::lam(
                        Name::anonymous(),
                        constant("Nat"),
                        Expr::lam(
                            Name::anonymous(),
                            constant("Nat"),
                            value,
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    hints: ReducibilityHints::Abbrev,
                    safety: DefinitionSafety::Safe,
                    all: vec![name(label)],
                }))
                .unwrap();
            let result = Expr::app(
                Expr::app(constant(label), Expr::bvar(0).unwrap()),
                Expr::bvar(0).unwrap(),
            );
            env = axiom(
                env,
                &format!("{label}Lemma"),
                forall(constant("Nat"), result),
            );
        }
        let value = SymmEntry {
            lemma: SymmLemma {
                declaration: name("ValueAliasLemma"),
                keys: vec![Key::Const(name("ValueAlias"), 0)],
            },
            namespace: None,
        };
        assert!(
            register(&env, value).is_ok(),
            "pin accepts the original binary alias result even when it reduces to Nat"
        );
        assert_eq!(
            register(&env, entry("ArrowAliasLemma", None)),
            Err(SymmRegistryError::InvalidLemma(name("ArrowAliasLemma")))
        );
    }

    #[test]
    fn final_opaque_telescope_alias_is_missing_history_not_invalid_metadata() {
        let env = base();
        let alias = name("SymmetryType");
        let value = forall(
            Expr::sort(Level::one()),
            forall(
                relation(Expr::bvar(0).unwrap(), Expr::bvar(0).unwrap()),
                relation(Expr::bvar(1).unwrap(), Expr::bvar(1).unwrap()),
            ),
        );
        let env = env
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: alias.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![alias.clone()],
            }))
            .unwrap();
        let env = axiom(env, "aliasReverse", constant("SymmetryType"));
        let reducible = crate::reducibility::register(
            &env,
            &alias,
            crate::reducibility::Reducibility::Reducible,
        )
        .unwrap();
        assert!(register(&reducible, entry("aliasReverse", None)).is_ok());
        let final_view = crate::reducibility::register(
            &env,
            &alias,
            crate::reducibility::Reducibility::Irreducible,
        )
        .unwrap();
        assert_eq!(
            register(&final_view, entry("aliasReverse", None)),
            Err(SymmRegistryError::UnsupportedLemma(name("aliasReverse")))
        );
        assert!(final_view.extension(&journal_name()).is_none());
    }
}
