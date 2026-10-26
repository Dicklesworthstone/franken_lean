//! Native source instance registrations, stored in the immutable environment.
//!
//! This versioned journal is not the Reference's serialized instance extension.
//! It contains references to already admitted declarations, never declarations
//! or proof authority. No negative cache outlives a search. Reading a malformed
//! journal is a refusal, not an empty instance set.

pub mod coercions;
pub mod defaults;
pub mod discr_tree;
pub mod export;
pub mod imported;
pub mod numeric;
pub mod scoped;

use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantInfo, DefinitionSafety, ReducibilityHints};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, BTreeSet};

const MAGIC: &[u8] = b"FLNINST\x01";
const MAX_ROWS: usize = 16_384;
const MAX_ENTRY_BYTES: usize = 65_536;
const MAX_COMPONENTS: usize = 256;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstanceRegistryError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    InvalidClass(Name),
    /// The pin's `checkOutParam` (`Lean/Class.lean`): parameter `parameter` (1-based) is neither
    /// an `outParam` nor instance-implicit, yet its type mentions an earlier `outParam`.
    OutParamDependency {
        class: Name,
        parameter: u32,
    },
    UnknownClass(Name),
    InvalidInstance(Name),
    DuplicateInstance(Name),
    /// Erasure requires an instance active in the current lexical view.
    NotAnInstance(Name),
}

impl std::fmt::Display for InstanceRegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native source instance registry"),
            Self::Limit => f.write_str("native source instance registry resource limit"),
            Self::UnknownDeclaration(n) => {
                write!(f, "unknown instance declaration {}", n.to_display_string())
            }
            Self::InvalidClass(n) => write!(
                f,
                "{} is not a supported class declaration",
                n.to_display_string()
            ),
            Self::OutParamDependency { class, parameter } => write!(
                f,
                "invalid class {}, parameter #{parameter} depends on `outParam`, but it is not an \
                 `outParam`",
                class.to_display_string()
            ),
            Self::UnknownClass(n) => {
                write!(f, "{} is not registered as a class", n.to_display_string())
            }
            Self::InvalidInstance(n) => {
                write!(
                    f,
                    "{} is not a supported class instance",
                    n.to_display_string()
                )
            }
            Self::NotAnInstance(n) => write!(
                f,
                "`{}` does not have [instance] attribute",
                n.to_display_string()
            ),
            Self::DuplicateInstance(n) => write!(
                f,
                "instance {} is already registered",
                n.to_display_string()
            ),
        }
    }
}
impl std::error::Error for InstanceRegistryError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceEntry {
    pub declaration: Name,
    pub priority: u32,
    /// Monotone registration order. [`InstanceRegistry::candidates`] lists newer
    /// equal-priority entries first; instance search reorders the candidates the
    /// pin's index positions (`discr_tree`, bead `fln-vm35`).
    pub order: usize,
}

/// Each registered declaration's scope and slot in its candidate list.
type Positions = BTreeMap<Name, (Option<Name>, usize)>;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InstanceRegistry {
    classes: BTreeSet<Name>,
    instances: BTreeMap<Name, Vec<InstanceEntry>>,
    imported: imported::Metadata,
    /// Dormant namespace registrations, in their original journal order.
    scoped: BTreeMap<Name, BTreeMap<Name, Vec<InstanceEntry>>>,
    /// Last registration event and persistent scope of each journal instance.
    /// Priority updates preserve search order but still clear a prior lexical
    /// erasure, so their event position is distinct from `InstanceEntry::order`.
    updates: BTreeMap<Name, (usize, Option<Name>)>,
    /// Erased global/local rows retained only for `native_instances`: erasure
    /// changes candidate availability, never a declaration's reducibility.
    inactive: Vec<InstanceEntry>,
    /// Registration-time metadata of active local instances. Reducibility
    /// changes cannot replace these keys with a newly derived or fallback path.
    local_indices: BTreeMap<Name, std::sync::Arc<export::DerivedIndex>>,
    /// The pin's discrimination tree over `imported`, built on first use.
    index: discr_tree::IndexCell,
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceInstances", "v1"])
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: extension_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Syntactic result head, bounded and metadata-transparent. Alias class heads
/// require normalization by the elaborator, not a guess by the registry.
pub fn result_head(expr: &Expr) -> Option<Name> {
    let mut current = expr;
    for _ in 0..MAX_ENTRY_BYTES {
        match current.node() {
            ExprNode::ForallE { body, .. } | ExprNode::MData { expr: body, .. } => current = body,
            ExprNode::App { f, .. } => current = f,
            ExprNode::Const { name, .. } => return Some(name.clone()),
            _ => return None,
        }
    }
    None
}

/// An instance type's binder telescope and class, with safe abbreviations
/// unfolded at the head: the registry half of instance search's
/// `instance_type`, at the same `UnificationTransparency::Abbreviations`
/// (safe, `Abbrev` hints, matching level arity). The Reference derives both the
/// instance key and its synthesis order from `forallMetaTelescopeReducing`
/// (vendored Meta/Instances.lean:107, 171), so `instDecidableEqBool :
/// DecidableEq Bool` is a `Decidable` instance: `DecidableEq α` abbreviates
/// `(a b : α) → Decidable (a = b)` (Prelude.lean:1011). A regular definition
/// is not unfolded, so an instance keyed through one stays a typed refusal.
pub fn instance_telescope(env: &Environment, type_: &Expr) -> Option<(Vec<BinderInfo>, Name)> {
    let mut current = type_.clone();
    let mut binders = Vec::new();
    for _ in 0..MAX_ENTRY_BYTES {
        let next = match current.node() {
            ExprNode::ForallE {
                binder_info, body, ..
            } => {
                binders.push(*binder_info);
                body.clone()
            }
            ExprNode::MData { expr, .. } => expr.clone(),
            _ => {
                let mut head = &current;
                let mut args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    args.push(a.clone());
                    head = f;
                }
                args.reverse();
                match head.node() {
                    ExprNode::Const { name, levels } => match env.find(name) {
                        Some(ConstantInfo::Defn(definition))
                            if definition.safety == DefinitionSafety::Safe
                                && definition.hints == ReducibilityHints::Abbrev
                                && definition.base.level_params.len() == levels.len() =>
                        {
                            // Universe instantiation cannot change a head
                            // constant, so only the value's lambdas are applied.
                            beta(&definition.value, &args)?
                        }
                        _ => return Some((binders, name.clone())),
                    },
                    ExprNode::Lam { .. } if !args.is_empty() => beta(head, &args)?,
                    _ => return None,
                }
            }
        };
        current = next;
    }
    None
}

/// Apply `args` to `function`, substituting through as many leading lambdas as
/// there are arguments and re-applying the rest.
fn beta(function: &Expr, args: &[Expr]) -> Option<Expr> {
    let mut body = function;
    let mut taken = 0;
    while taken < args.len() {
        let ExprNode::Lam { body: inner, .. } = body.node() else {
            break;
        };
        body = inner;
        taken += 1;
    }
    let result = body.subst_loose(0, &args[..taken]).ok()?;
    Some(args[taken..].iter().cloned().fold(result, Expr::app))
}

impl InstanceRegistry {
    pub fn read(env: &Environment) -> Result<Self, InstanceRegistryError> {
        let (mut out, _) = Self::read_unsorted(env)?;
        for entries in out.instances.values_mut() {
            entries.sort_by(|a, b| {
                b.priority
                    .cmp(&a.priority)
                    .then_with(|| b.order.cmp(&a.order))
            });
        }
        Ok(out)
    }

    /// [`Self::read`] before candidates are put in search order, with the slot of
    /// every registered declaration: the state [`Self::apply_row`] extends.
    fn read_unsorted(env: &Environment) -> Result<(Self, Positions), InstanceRegistryError> {
        let Some(extension) = env.extension(&extension_name()) else {
            let metadata = imported::read(env)?;
            if !metadata.classes.is_empty() || !metadata.instances.is_empty() {
                return Err(InstanceRegistryError::Malformed);
            }
            return Ok((Self::default(), Positions::new()));
        };
        if extension.descriptor != descriptor() {
            return Err(InstanceRegistryError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(InstanceRegistryError::Limit);
        }
        let mut out = Self::default();
        // Keep a stable slot per declaration. Attribute updates replace its
        // priority in place, just as the Reference's DiscrTree.insertVal does;
        // re-registering an existing instance does not make it a newer peer.
        let mut positions = Positions::new();
        for (order, entry) in extension.entries().enumerate() {
            out.apply_row(env, &mut positions, order, &entry.payload)?;
        }
        out.imported = imported::read(env)?;
        for name in out.imported.classes.keys() {
            if !out.classes.contains(name) {
                return Err(InstanceRegistryError::UnknownClass(name.clone()));
            }
        }
        for (name, parameters) in &out.imported.instances {
            let class = validate_instance(env, name)?;
            if !out.classes.contains(&class) {
                return Err(InstanceRegistryError::UnknownClass(class));
            }
            let registered_scope = out.scoped.iter().find_map(|(scope, classes)| {
                classes.get(&class).and_then(|rows| {
                    rows.iter()
                        .any(|row| &row.declaration == name)
                        .then_some(scope)
                })
            });
            if registered_scope != parameters.scope.as_ref() {
                return Err(InstanceRegistryError::Malformed);
            }
        }
        Ok((out, positions))
    }

    /// Validate one journal row and fold it into the registry, as [`Self::read`]
    /// does for each row in journal order. `order` is the row's journal index.
    fn apply_row(
        &mut self,
        env: &Environment,
        positions: &mut Positions,
        order: usize,
        payload: &[u8],
    ) -> Result<(), InstanceRegistryError> {
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
        let mut bytes: &[u8] = payload;
        if take(&mut bytes, MAGIC.len())? != MAGIC {
            return Err(InstanceRegistryError::Malformed);
        }
        let tag = take(&mut bytes, 1)?[0];
        let class = read_name(&mut bytes)?;
        match tag {
            0 => {
                validate_class(env, &class)?;
                if !self.classes.insert(class) {
                    return Err(InstanceRegistryError::Malformed);
                }
            }
            // Tag 1 is the original strict registration operation. Tag 2
            // is a global attribute upsert; tag 3 is a namespace-scoped
            // upsert. Old readers refuse new tags instead of treating
            // dormant registrations as ordinary global instances.
            1..=3 => {
                let declaration = read_name(&mut bytes)?;
                let priority = u32::from_le_bytes(
                    take(&mut bytes, 4)?
                        .try_into()
                        .map_err(|_| InstanceRegistryError::Malformed)?,
                );
                if !self.classes.contains(&class) || validate_instance(env, &declaration)? != class
                {
                    return Err(InstanceRegistryError::Malformed);
                }
                let scope = if tag == 3 {
                    Some(read_name(&mut bytes)?)
                } else {
                    None
                };
                let entries = match &scope {
                    Some(scope) => self
                        .scoped
                        .entry(scope.clone())
                        .or_default()
                        .entry(class)
                        .or_default(),
                    None => self.instances.entry(class).or_default(),
                };
                self.updates
                    .insert(declaration.clone(), (order, scope.clone()));
                if let Some((previous_scope, slot)) = positions.get(&declaration) {
                    if tag == 1 || previous_scope != &scope {
                        return Err(InstanceRegistryError::Malformed);
                    }
                    let previous: &mut InstanceEntry = entries
                        .get_mut(*slot)
                        .ok_or(InstanceRegistryError::Malformed)?;
                    if previous.declaration != declaration {
                        return Err(InstanceRegistryError::Malformed);
                    }
                    previous.priority = priority;
                } else {
                    positions.insert(declaration.clone(), (scope, entries.len()));
                    entries.push(InstanceEntry {
                        declaration,
                        priority,
                        order,
                    });
                }
            }
            _ => return Err(InstanceRegistryError::Malformed),
        }
        if !bytes.is_empty() {
            return Err(InstanceRegistryError::Malformed);
        }
        Ok(())
    }
    pub fn is_class(&self, name: &Name) -> bool {
        self.classes.contains(name)
    }
    /// Whether this already validated view currently offers the declaration.
    /// Dormant scoped registrations, erased instances, and default-only
    /// candidates are not active ordinary instances.
    pub fn is_instance(&self, declaration: &Name) -> bool {
        self.instances
            .values()
            .flatten()
            .any(|row| &row.declaration == declaration)
    }

    pub fn candidates(&self, class: &Name) -> &[InstanceEntry] {
        self.instances.get(class).map_or(&[], Vec::as_slice)
    }
    /// The pin's discrimination tree over imported paths and supported native
    /// models. Derivation reads the admitted environment, spends caller work,
    /// and publishes the cache only after the complete active view succeeds.
    pub(crate) fn instance_index(
        &self,
        env: &Environment,
        work_left: &mut usize,
    ) -> Result<&discr_tree::InstanceIndex, InstanceRegistryError> {
        self.index.get(self, env, work_left)
    }
    pub fn imported_class_parameters(&self, class: &Name) -> Option<&imported::ClassParameters> {
        self.imported.classes.get(class)
    }
    pub(crate) fn local_instance_index(&self, declaration: &Name) -> Option<&export::DerivedIndex> {
        self.local_indices.get(declaration).map(AsRef::as_ref)
    }
    pub fn imported_instance_parameters(
        &self,
        name: &Name,
    ) -> Option<&imported::InstanceParameters> {
        self.imported.instances.get(name)
    }

    /// Instances declared here rather than activated from an import, scoped ones
    /// included. The pin's `instance` command marks each `implicitReducible`
    /// (vendored `src/Lean/Meta/Instances.lean`, `addInstance` for the command);
    /// an imported instance's status is its module's own `reducibilityCore` entry.
    pub fn native_instances(&self) -> impl Iterator<Item = &Name> {
        self.instances
            .values()
            .chain(self.scoped.values().flat_map(|classes| classes.values()))
            .flatten()
            .chain(self.inactive.iter())
            .map(|entry| &entry.declaration)
            .filter(|name| !self.imported.instances.contains_key(*name))
    }

    /// Namespaces with dormant instances. Opening names and activating scoped
    /// registrations are separate operations on the source-scope plane.
    pub fn instance_namespaces(&self) -> impl Iterator<Item = &Name> {
        self.scoped.keys()
    }

    fn is_scoped_instance(&self, declaration: &Name) -> bool {
        self.scoped.values().any(|classes| {
            classes.values().any(|entries| {
                entries
                    .iter()
                    .any(|entry| &entry.declaration == declaration)
            })
        })
    }
}

fn validate_class(env: &Environment, name: &Name) -> Result<(), InstanceRegistryError> {
    match env.find(name) {
        Some(ConstantInfo::Induct(value)) if !value.is_unsafe => Ok(()),
        Some(ConstantInfo::Axiom(value)) if !value.is_unsafe => Ok(()),
        _ => Err(InstanceRegistryError::InvalidClass(name.clone())),
    }
}
fn validate_instance(env: &Environment, name: &Name) -> Result<Name, InstanceRegistryError> {
    let info = env
        .find(name)
        .ok_or_else(|| InstanceRegistryError::UnknownDeclaration(name.clone()))?;
    if !instance_declaration_is_supported(info) {
        return Err(InstanceRegistryError::InvalidInstance(name.clone()));
    }
    instance_telescope(env, &info.constant_val().type_)
        .map(|(_, class)| class)
        .ok_or_else(|| InstanceRegistryError::InvalidInstance(name.clone()))
}

/// Shared by registration, journal replay and native/export index derivation.
fn instance_declaration_is_supported(info: &ConstantInfo) -> bool {
    // The pin's Meta.addInstance registers an admitted declaration by its
    // class-valued type, not by whether callers may use it in safe code.
    // Keep unsafe definitions as real candidates: silently skipping one could
    // change priority selection. Ordinary declaration admission still rejects
    // every safe consumer containing the selected unsafe dictionary. Partial
    // implementation companions and unsafe axioms/constructors remain outside
    // this registration door; no declaration is admitted or reclassified here.
    match info {
        ConstantInfo::Defn(value) => matches!(
            value.safety,
            DefinitionSafety::Safe | DefinitionSafety::Unsafe
        ),
        ConstantInfo::Thm(_) => true,
        ConstantInfo::Opaque(value) => !value.is_unsafe,
        ConstantInfo::Axiom(value) => !value.is_unsafe,
        // `class abbrev C := A` registers the constructor `C.mk` itself as the instance; at
        // the pin, `Std.Internal.Do.Assertion.mk` is one, so `import Std` carries it.
        ConstantInfo::Ctor(value) => !value.is_unsafe,
        _ => false,
    }
}

fn append(env: &Environment, payload: Vec<u8>) -> Result<Environment, InstanceRegistryError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(InstanceRegistryError::Limit);
    }
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| InstanceRegistryError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&extension_name())
        .is_some_and(|state| state.len() >= MAX_ROWS)
    {
        return Err(InstanceRegistryError::Limit);
    }
    env.push_extension_entry(&extension_name(), payload)
        .map_err(|_| InstanceRegistryError::Malformed)
}

/// One elaboration's view of the instance registry. [`InstanceRegistry::read`]
/// re-parses and re-validates every journal row and every imported instance. The
/// elaborator asks it on each numeric literal, operator and coercion, so under an
/// imported closure every such query paid for every imported instance (fln-uyuz's
/// profile of the implicit-Init import). Each view is bound to the immutable
/// environment it was read from, not just journal digests and a constant count:
/// speculative branches can have equal counts and different declarations. Exact
/// environment equality also binds extension descriptors and imported metadata.
/// Shared persistent-map roots make an unchanged snapshot's comparison O(1),
/// without hashing the whole environment. Unrelated changes may cause a harmless
/// extra read. A failed read is never kept.
#[derive(Clone, Default)]
pub(crate) struct RegistryCache {
    last: std::cell::RefCell<Option<(Environment, std::sync::Arc<InstanceRegistry>)>>,
    /// The last [`InstanceRegistry::read_with_scopes`] view, keyed also by the scopes it read.
    scoped: std::cell::RefCell<ScopedEntry>,
}

type ScopedEntry = Option<(
    Environment,
    scoped::ActiveScopes,
    std::sync::Arc<InstanceRegistry>,
)>;

/// Identity of the native row journal and the imported metadata journal only.
/// This does not identify the declarations against which rows are validated:
/// equal journal digests and constant counts can describe different branches.
/// A cached validated view must also be bound to its environment.
pub(crate) fn registry_identity(env: &Environment) -> (Option<[u8; 32]>, Option<[u8; 32]>) {
    (
        env.extension(&extension_name())
            .map(|extension| extension.content_digest().0),
        imported::journal_digest(env),
    )
}

impl RegistryCache {
    pub(crate) fn read(
        &self,
        env: &Environment,
    ) -> Result<std::sync::Arc<InstanceRegistry>, InstanceRegistryError> {
        if let Some((cached, registry)) = self.last.borrow().as_ref()
            && cached == env
        {
            return Ok(std::sync::Arc::clone(registry));
        }
        let registry = std::sync::Arc::new(InstanceRegistry::read(env)?);
        *self.last.borrow_mut() = Some((env.clone(), std::sync::Arc::clone(&registry)));
        Ok(registry)
    }

    /// [`InstanceRegistry::read_with_scopes`], read again only when what [`Self::read`] reads
    /// or the active scopes change. Elaborating one term reads the scoped view at every
    /// instance-resolution pass, and each read validated every imported instance row again.
    pub(crate) fn read_with_scopes(
        &self,
        env: &Environment,
        scopes: &scoped::ActiveScopes,
    ) -> Result<std::sync::Arc<InstanceRegistry>, InstanceRegistryError> {
        if let Some((cached, cached_scopes, registry)) = self.scoped.borrow().as_ref()
            && cached == env
            && cached_scopes == scopes
        {
            return Ok(std::sync::Arc::clone(registry));
        }
        let registry = InstanceRegistry::read_cached_with_scopes(self, env, scopes)?;
        *self.scoped.borrow_mut() = Some((
            env.clone(),
            scopes.clone(),
            std::sync::Arc::clone(&registry),
        ));
        Ok(registry)
    }
}

pub fn register_class(
    env: &Environment,
    class: &Name,
) -> Result<Environment, InstanceRegistryError> {
    let registry = InstanceRegistry::read(env)?;
    validate_class(env, class)?;
    if registry.is_class(class) {
        return Ok(env.clone());
    }
    // The pin's `addClass` runs `checkOutParam` on every new class.
    export::check_out_params(env, class)?;
    append(env, class_payload(class)?)
}

/// The journal row registering `class` (tag 0).
fn class_payload(class: &Name) -> Result<Vec<u8>, InstanceRegistryError> {
    let mut payload = MAGIC.to_vec();
    payload.push(0);
    write_name(class, &mut payload)?;
    Ok(payload)
}

/// A journal row registering `declaration` under `class`: tag 1 is the strict
/// registration, 2 the global upsert, 3 the namespace-scoped upsert (the only
/// tag that carries a scope).
fn instance_payload(
    tag: u8,
    class: &Name,
    declaration: &Name,
    priority: u32,
    scope: Option<&Name>,
) -> Result<Vec<u8>, InstanceRegistryError> {
    let mut payload = MAGIC.to_vec();
    payload.push(tag);
    write_name(class, &mut payload)?;
    write_name(declaration, &mut payload)?;
    payload.extend(priority.to_le_bytes());
    if let Some(scope) = scope {
        write_name(scope, &mut payload)?;
    }
    Ok(payload)
}

/// Register an already admitted declaration; never admit or execute it.
pub fn register_instance(
    env: &Environment,
    declaration: &Name,
    priority: u32,
) -> Result<Environment, InstanceRegistryError> {
    let registry = InstanceRegistry::read(env)?;
    let class = validate_instance(env, declaration)?;
    if !registry.is_class(&class) {
        return Err(InstanceRegistryError::UnknownClass(class));
    }
    if registry.is_scoped_instance(declaration)
        || registry
            .candidates(&class)
            .iter()
            .any(|row| &row.declaration == declaration)
    {
        return Err(InstanceRegistryError::DuplicateInstance(
            declaration.clone(),
        ));
    }
    append(
        env,
        instance_payload(1, &class, declaration, priority, None)?,
    )
}

/// Add or reprioritize an already admitted declaration for a global
/// `attribute [instance]` command. Unlike [`register_instance`], this operation
/// deliberately permits an existing registration. Its original equal-priority
/// tie-break position is preserved; no stale higher-priority copy survives.
///
/// The update is an append-only, validated journal event, so immutable snapshots
/// and the native module export/replay path retain their ordinary identities.
/// This does not implement scoped/local attributes or instance erasure, and it
/// never admits a declaration or changes its reducibility metadata.
pub fn set_instance(
    env: &Environment,
    declaration: &Name,
    priority: u32,
) -> Result<Environment, InstanceRegistryError> {
    let registry = InstanceRegistry::read(env)?;
    if registry.is_scoped_instance(declaration) {
        return Err(InstanceRegistryError::DuplicateInstance(
            declaration.clone(),
        ));
    }
    let class = validate_instance(env, declaration)?;
    if !registry.is_class(&class) {
        return Err(InstanceRegistryError::UnknownClass(class));
    }
    append(
        env,
        instance_payload(2, &class, declaration, priority, None)?,
    )
}

fn take<'a>(bytes: &mut &'a [u8], n: usize) -> Result<&'a [u8], InstanceRegistryError> {
    if n > bytes.len() {
        return Err(InstanceRegistryError::Malformed);
    }
    let (head, tail) = bytes.split_at(n);
    *bytes = tail;
    Ok(head)
}
pub(crate) fn write_name(name: &Name, out: &mut Vec<u8>) -> Result<(), InstanceRegistryError> {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        if parts.len() >= MAX_COMPONENTS {
            return Err(InstanceRegistryError::Limit);
        }
        parts.push(cursor.clone());
        cursor = cursor.parent();
    }
    if parts.is_empty() {
        return Err(InstanceRegistryError::Malformed);
    }
    out.extend(
        u16::try_from(parts.len())
            .map_err(|_| InstanceRegistryError::Limit)?
            .to_le_bytes(),
    );
    for part in parts.into_iter().rev() {
        match part.leaf_view() {
            LeafView::Str(s) => {
                if s.len() > MAX_ENTRY_BYTES {
                    return Err(InstanceRegistryError::Limit);
                }
                out.push(0);
                out.extend(
                    u32::try_from(s.len())
                        .map_err(|_| InstanceRegistryError::Limit)?
                        .to_le_bytes(),
                );
                out.extend(s.as_bytes());
            }
            LeafView::Num(v) => {
                out.push(if part.component_overflowed() { 2 } else { 1 });
                out.extend(v.to_le_bytes());
            }
            LeafView::Anonymous => return Err(InstanceRegistryError::Malformed),
        }
        if out.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
    }
    Ok(())
}
pub(crate) fn read_name(bytes: &mut &[u8]) -> Result<Name, InstanceRegistryError> {
    let count = usize::from(u16::from_le_bytes(
        take(bytes, 2)?
            .try_into()
            .map_err(|_| InstanceRegistryError::Malformed)?,
    ));
    if count == 0 || count > MAX_COMPONENTS {
        return Err(InstanceRegistryError::Malformed);
    }
    let mut name = Name::anonymous();
    for _ in 0..count {
        match take(bytes, 1)?[0] {
            0 => {
                let len = u32::from_le_bytes(
                    take(bytes, 4)?
                        .try_into()
                        .map_err(|_| InstanceRegistryError::Malformed)?,
                );
                let text = std::str::from_utf8(take(
                    bytes,
                    usize::try_from(len).map_err(|_| InstanceRegistryError::Malformed)?,
                )?)
                .map_err(|_| InstanceRegistryError::Malformed)?;
                name = Name::str(name, text);
            }
            1 => {
                name = Name::num(
                    name,
                    u64::from_le_bytes(
                        take(bytes, 8)?
                            .try_into()
                            .map_err(|_| InstanceRegistryError::Malformed)?,
                    ),
                )
            }
            2 => {
                name = Name::num_overflowing(
                    name,
                    u64::from_le_bytes(
                        take(bytes, 8)?
                            .try_into()
                            .map_err(|_| InstanceRegistryError::Malformed)?,
                    ),
                )
            }
            _ => return Err(InstanceRegistryError::Malformed),
        }
    }
    Ok(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn registry_name_codec_preserves_structural_identity() {
        let names = [
            Name::from_components(["a.b"]),
            Name::from_components(["a", "b"]),
            Name::from_components(["a", "2"]),
            Name::num(Name::from_components(["a"]), 2),
            Name::num_overflowing(Name::from_components(["a"]), 2),
        ];
        let mut encodings = BTreeSet::new();
        for name in names {
            let mut bytes = Vec::new();
            write_name(&name, &mut bytes).unwrap();
            let mut input = bytes.as_slice();
            assert_eq!(read_name(&mut input).unwrap(), name);
            assert!(input.is_empty());
            assert!(encodings.insert(bytes));
        }
    }
    #[test]
    fn malformed_or_foreign_registry_is_not_an_empty_candidate_set() {
        for payload in [Vec::new(), b"FLNINST\x02".to_vec(), [MAGIC, &[9]].concat()] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(InstanceRegistry::read(&env).is_err());
        }
        let mut wrong = descriptor();
        wrong.provenance = PayloadProvenance::Opaque;
        let env = Environment::new().register_extension(wrong).unwrap();
        assert_eq!(
            InstanceRegistry::read(&env),
            Err(InstanceRegistryError::Malformed)
        );
    }
    #[test]
    fn a_cached_registry_is_reread_exactly_when_what_it_reads_changes() {
        use fln_core::level::Level;
        use fln_env::constants::{AxiomVal, ConstantVal};
        let axiom = |name: &str| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: Name::from_components([name]),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            })
        };
        let class = Name::from_components(["C"]);
        let base = Environment::new().add_decl(axiom("C")).unwrap();
        let cache = RegistryCache::default();
        let before = cache.read(&base).unwrap();
        assert!(!before.is_class(&class));
        assert!(
            std::sync::Arc::ptr_eq(&before, &cache.read(&base).unwrap()),
            "an unchanged environment is not re-read"
        );
        // A new journal row, with no new constant, is seen.
        let registered = register_class(&base, &class).unwrap();
        assert_eq!(registered.len(), base.len());
        let after = cache.read(&registered).unwrap();
        assert!(after.is_class(&class));
        // The environment before the row (a rollback) is answered as it was.
        assert!(!cache.read(&base).unwrap().is_class(&class));
        // A new constant re-reads too, and every answer is a fresh read's.
        let grown = registered.add_decl(axiom("D")).unwrap();
        let again = cache.read(&grown).unwrap();
        assert!(!std::sync::Arc::ptr_eq(&after, &again));
        assert_eq!(*again, InstanceRegistry::read(&grown).unwrap());
        // A failed read is not kept: a malformed journal stays an error.
        let broken = registered
            .push_extension_entry(&extension_name(), b"FLNINST\x02".to_vec())
            .unwrap();
        assert!(cache.read(&broken).is_err());
        assert!(cache.read(&broken).is_err());
    }
    #[test]
    fn a_cached_scoped_view_is_reread_exactly_when_its_environment_or_scopes_change() {
        use fln_core::level::Level;
        use fln_env::constants::{AxiomVal, ConstantVal};
        let axiom = |name: &str| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: Name::from_components([name]),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            })
        };
        let class = Name::from_components(["C"]);
        let base = Environment::new().add_decl(axiom("C")).unwrap();
        let none = scoped::ActiveScopes::default();
        let cache = RegistryCache::default();
        let before = cache.read_with_scopes(&base, &none).unwrap();
        assert!(
            std::sync::Arc::ptr_eq(&before, &cache.read_with_scopes(&base, &none).unwrap()),
            "an unchanged environment and scope set is not re-read"
        );
        // A new journal row is seen, and a rollback is answered as it was.
        let registered = register_class(&base, &class).unwrap();
        let after = cache.read_with_scopes(&registered, &none).unwrap();
        assert!(after.is_class(&class));
        assert!(
            !cache
                .read_with_scopes(&base, &none)
                .unwrap()
                .is_class(&class)
        );
        // A different scope set over the same environment re-reads, and every answer is a
        // fresh read's.
        let mut opened = none.clone();
        opened
            .activate(&registered, &Name::from_components(["N"]))
            .unwrap();
        let scoped_view = cache.read_with_scopes(&registered, &opened).unwrap();
        assert!(!std::sync::Arc::ptr_eq(&after, &scoped_view));
        assert_eq!(
            *scoped_view,
            InstanceRegistry::read_with_scopes(&registered, &opened).unwrap()
        );
        // A failed read is not kept.
        let broken = registered
            .push_extension_entry(&extension_name(), b"FLNINST\x02".to_vec())
            .unwrap();
        assert!(cache.read_with_scopes(&broken, &none).is_err());
        assert!(cache.read_with_scopes(&broken, &none).is_err());
    }
    fn cache_test_axiom(name: &str, type_: Expr, is_unsafe: bool) -> ConstantInfo {
        use fln_env::constants::{AxiomVal, ConstantVal};
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components([name]),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe,
        })
    }

    #[test]
    fn registry_cache_revalidates_equal_sized_class_branches() {
        use fln_core::level::Level;
        use std::sync::Arc;

        let class = Name::from_components(["C"]);
        // Deliberately replay the same journal into several candidate branches.
        // Only the branch with a safe C declaration is a valid registry.
        let journal = append(&Environment::new(), class_payload(&class).unwrap()).unwrap();
        let valid = journal
            .add_decl(cache_test_axiom("C", Expr::sort(Level::one()), false))
            .unwrap();
        let missing = journal
            .add_decl(cache_test_axiom("D", Expr::sort(Level::one()), false))
            .unwrap();
        let unsafe_class = journal
            .add_decl(cache_test_axiom("C", Expr::sort(Level::one()), true))
            .unwrap();
        let cache = RegistryCache::default();
        let scopes = scoped::ActiveScopes::default();
        let before = cache.read(&valid).unwrap();
        let scoped_before = cache.read_with_scopes(&valid, &scopes).unwrap();

        // Context cloning carries caches into speculative branches.
        let branch_cache = cache.clone();
        for candidate in [&missing, &unsafe_class] {
            assert_eq!(valid.len(), candidate.len());
            assert_eq!(registry_identity(&valid), registry_identity(candidate));
            let expected = InstanceRegistryError::InvalidClass(class.clone());
            assert_eq!(InstanceRegistry::read(candidate), Err(expected.clone()));
            for cache in [&cache, &branch_cache] {
                for _ in 0..2 {
                    assert_eq!(cache.read(candidate), Err(expected.clone()));
                    assert_eq!(
                        cache.read_with_scopes(candidate, &scopes),
                        Err(expected.clone())
                    );
                }
                // Failed reads neither replace nor poison the last good view.
                assert!(Arc::ptr_eq(&before, &cache.read(&valid).unwrap()));
                assert!(Arc::ptr_eq(
                    &scoped_before,
                    &cache.read_with_scopes(&valid, &scopes).unwrap()
                ));
            }
        }
    }

    #[test]
    fn registry_cache_revalidates_changed_instance_type_and_safety() {
        use fln_core::level::Level;

        let class = Name::from_components(["C"]);
        let other = Name::from_components(["D"]);
        let instance = Name::from_components(["inst"]);
        let base = Environment::new()
            .add_decl(cache_test_axiom("C", Expr::sort(Level::one()), false))
            .unwrap()
            .add_decl(cache_test_axiom("D", Expr::sort(Level::one()), false))
            .unwrap();
        let base = register_class(&register_class(&base, &class).unwrap(), &other).unwrap();
        let journal = append(
            &base,
            instance_payload(1, &class, &instance, 1000, None).unwrap(),
        )
        .unwrap();
        let valid = journal
            .add_decl(cache_test_axiom(
                "inst",
                Expr::const_(class.clone(), Vec::new()),
                false,
            ))
            .unwrap();
        let wrong_class = journal
            .add_decl(cache_test_axiom(
                "inst",
                Expr::const_(other, Vec::new()),
                false,
            ))
            .unwrap();
        let unsafe_instance = journal
            .add_decl(cache_test_axiom(
                "inst",
                Expr::const_(class.clone(), Vec::new()),
                true,
            ))
            .unwrap();
        let cache = RegistryCache::default();
        let scopes = scoped::ActiveScopes::default();
        assert_eq!(cache.read(&valid).unwrap().candidates(&class).len(), 1);
        assert_eq!(
            cache
                .read_with_scopes(&valid, &scopes)
                .unwrap()
                .candidates(&class)
                .len(),
            1
        );
        for (candidate, expected) in [
            (&wrong_class, InstanceRegistryError::Malformed),
            (
                &unsafe_instance,
                InstanceRegistryError::InvalidInstance(instance),
            ),
        ] {
            assert_eq!(valid.len(), candidate.len());
            assert_eq!(registry_identity(&valid), registry_identity(candidate));
            assert_eq!(InstanceRegistry::read(candidate), Err(expected.clone()));
            assert_eq!(cache.read(candidate), Err(expected.clone()));
            assert_eq!(cache.read_with_scopes(candidate, &scopes), Err(expected));
        }
    }

    #[test]
    fn registry_cache_preserves_snapshot_hits_but_not_equal_sized_branch_hits() {
        use fln_core::level::Level;
        use std::sync::Arc;

        let class = Name::from_components(["C"]);
        let journal = append(&Environment::new(), class_payload(&class).unwrap()).unwrap();
        let first = journal
            .add_decl(cache_test_axiom("C", Expr::sort(Level::one()), false))
            .unwrap();
        let second = journal
            .add_decl(cache_test_axiom("C", Expr::sort(Level::zero()), false))
            .unwrap();
        assert_eq!(first.len(), second.len());
        assert_eq!(registry_identity(&first), registry_identity(&second));
        let cache = RegistryCache::default();
        let scopes = scoped::ActiveScopes::default();
        let first_view = cache.read(&first).unwrap();
        let first_scoped = cache.read_with_scopes(&first, &scopes).unwrap();
        // O(1) snapshots still hit, including after a Context/cache clone.
        let snapshot = first.clone();
        let cloned_cache = cache.clone();
        assert!(Arc::ptr_eq(
            &first_view,
            &cloned_cache.read(&snapshot).unwrap()
        ));
        assert!(Arc::ptr_eq(
            &first_scoped,
            &cloned_cache.read_with_scopes(&snapshot, &scopes).unwrap()
        ));
        // Both branches are readable and have the same names, counts and journal.
        // Their different types must not share a lazily derived instance index.
        let second_view = cache.read(&second).unwrap();
        let second_scoped = cache.read_with_scopes(&second, &scopes).unwrap();
        assert!(!Arc::ptr_eq(&first_view, &second_view));
        assert!(!Arc::ptr_eq(&first_scoped, &second_scoped));
        assert_eq!(*second_view, InstanceRegistry::read(&second).unwrap());
        assert_eq!(
            *second_scoped,
            InstanceRegistry::read_with_scopes(&second, &scopes).unwrap()
        );
        // Rollback recovers the original answer, not the newer branch's index.
        assert_eq!(*cache.read(&first).unwrap(), *first_view);
        assert_eq!(
            *cache.read_with_scopes(&first, &scopes).unwrap(),
            *first_scoped
        );
    }

    #[test]
    fn empty_or_unadmitted_registrations_cannot_supply_instances() {
        let env = Environment::new();
        let name = Name::from_components(["absent"]);
        assert!(register_class(&env, &name).is_err());
        assert!(register_instance(&env, &name, 1000).is_err());
        assert!(
            InstanceRegistry::read(&env)
                .unwrap()
                .candidates(&name)
                .is_empty()
        );
    }
}
