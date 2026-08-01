//! Dynamic registration, scopes, and the grammar epoch (plan §9; bead fln-okfb).
//!
//! ## Why the oracle for this module is the pinned binary
//!
//! Dynamic registration is where the thing being tested and the thing testing it are assembled
//! from the same parts. A "reparse from scratch" still builds its table with this registry, walks
//! it with this lookup, and resolves with this `longest_match` — so if the registry is last-wins
//! where the Reference is additive, both runs agree perfectly and the differential certifies the
//! mistake. On this module that is not a hazard, it is the default.
//!
//! So each law below is tied to an observation of the pinned `lean` binary, cited inline. The one
//! claim with no available observation — hook ordering — says so in its own doc comment rather
//! than borrowing credibility from the ones that do.
//!
//! ## The law that would have been got wrong: shadowing is ADDITIVE
//!
//! Observed: two `notation "dup"` declarations, then `#eval dup`, gives
//! `error: Ambiguous term`. The second declaration does **not** replace the first. Both parsers
//! stay registered and the parse becomes genuinely ambiguous.
//!
//! The obvious shape for a registry — a map from syntax to production — silently drops the first
//! and never reports the ambiguity. That shape is what I would have written. It is also why this
//! module's tables are **append-only lists per token**, and it is the registration-level source of
//! the `choice` nodes [`crate::state::longest_match`] preserves: the tie has to come from
//! somewhere, and this is where.
//!
//! ## Epochs make interleaving explicit
//!
//! Observed: `syntax "myfoo" : term` then `#check myfoo` is accepted; the same file with the
//! `#check` first gives `Unknown identifier 'myfoo'`. A registration takes effect for *later*
//! parses only, so a parse is against the grammar as of its own position — not the file's final
//! grammar.
//!
//! [`GrammarEpoch`] is that position, made a value. A lookup at epoch *n* sees exactly the
//! registrations made before *n*, which is what lets a parse be replayed against the grammar it
//! actually ran under rather than the one that exists now.

use crate::category::{Category, LeadingIdentBehavior};
use crate::state::{ParserDescriptor, Production};
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_hash::canon::Canonical;
use fln_hash::domain::{Digest, Domain, hash};
use fln_syntax::source::BytePos;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// A content-bound point in the registration history — upstream's parser state as of one command.
///
/// `revision` preserves the command-order boundary needed to replay a historical executable view.
/// `digest` is the host-independent content hash of every canonical grammar row active at that
/// revision. Keeping both is deliberate: a scope close may restore old content at a later command,
/// while two different revisions must still remain addressable for activation-boundary reasoning.
///
/// A digest is only an index. Authority additionally compares the complete canonical rows through
/// [`GrammarIdentity`], so an injected collision cannot cross-hit a memo entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GrammarEpoch {
    revision: u64,
    digest: Digest,
}

impl GrammarEpoch {
    fn from_root(revision: u64, root: &GrammarRoot) -> GrammarEpoch {
        GrammarEpoch {
            revision,
            digest: hash(Domain::CacheKey, root.0.as_bytes()),
        }
    }

    const fn placeholder(revision: u64) -> GrammarEpoch {
        GrammarEpoch {
            revision,
            digest: Digest([0; 32]),
        }
    }

    pub const fn revision(self) -> u64 {
        self.revision
    }

    pub const fn digest(self) -> Digest {
        self.digest
    }

    pub fn content_hex(self) -> String {
        self.digest.to_hex()
    }
}

/// Collision-safe authority for one grammar epoch.
///
/// Equality includes the complete canonical rows, not only the digest. The rows are shared because
/// memo entries and historical views may retain the same immutable identity for a long time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrammarIdentity {
    epoch: GrammarEpoch,
    canonical: Arc<str>,
}

impl GrammarIdentity {
    fn new(epoch: GrammarEpoch, root: GrammarRoot) -> GrammarIdentity {
        GrammarIdentity {
            epoch,
            canonical: Arc::from(root.0),
        }
    }

    pub const fn epoch(&self) -> GrammarEpoch {
        self.epoch
    }

    pub fn canonical(&self) -> &str {
        &self.canonical
    }

    pub const fn digest(&self) -> Digest {
        self.epoch.digest
    }
}

/// Whether a production is entered before a term or extends a parsed left-hand side.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParserPosition {
    Leading,
    Trailing,
}

/// One precise grammar input a parse product may have read.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum GrammarComponent {
    Category(Name),
    Syntax {
        category: Name,
        token: Name,
        position: ParserPosition,
    },
    Token(Name),
    Precedence {
        category: Name,
        parser: Name,
    },
    Scope,
    Macro(Name),
    Option(Name),
    Import(Name),
    WholeGrammar,
}

/// A typed summary of one grammar mutation.
///
/// Unknown callback semantics are never guessed. [`Self::OpaqueParserEffect`] is a valid fidelity
/// outcome, but it invalidates every suffix product and erects a distributed-parse barrier at the
/// transition's activation point.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParserEffect {
    AddsCategory {
        category: Name,
    },
    AddsSyntax {
        category: Name,
        token: Name,
        kind: Name,
        position: ParserPosition,
    },
    AddsToken {
        token: Name,
    },
    ChangesPrecedence {
        category: Name,
        parser: Name,
        precedence: u32,
    },
    OpensScope {
        depth: ScopeDepth,
    },
    ClosesScope {
        depth: ScopeDepth,
    },
    RegistersMacro {
        name: Name,
    },
    ChangesOption {
        name: Name,
    },
    ImportsGrammar {
        module: Name,
    },
    RemovesSyntax {
        category: Name,
        token: Name,
        kind: Name,
        position: ParserPosition,
    },
    OpaqueParserEffect {
        id: Name,
    },
}

impl ParserEffect {
    pub const fn is_opaque(&self) -> bool {
        matches!(self, ParserEffect::OpaqueParserEffect { .. })
    }

    fn affected_components(&self, out: &mut BTreeSet<GrammarComponent>) {
        match self {
            ParserEffect::AddsCategory { category } => {
                out.insert(GrammarComponent::Category(category.clone()));
            }
            ParserEffect::AddsSyntax {
                category,
                token,
                position,
                ..
            }
            | ParserEffect::RemovesSyntax {
                category,
                token,
                position,
                ..
            } => {
                out.insert(GrammarComponent::Syntax {
                    category: category.clone(),
                    token: token.clone(),
                    position: *position,
                });
                out.insert(GrammarComponent::Token(token.clone()));
            }
            ParserEffect::AddsToken { token } => {
                out.insert(GrammarComponent::Token(token.clone()));
            }
            ParserEffect::ChangesPrecedence {
                category, parser, ..
            } => {
                out.insert(GrammarComponent::Precedence {
                    category: category.clone(),
                    parser: parser.clone(),
                });
            }
            ParserEffect::OpensScope { .. } | ParserEffect::ClosesScope { .. } => {
                out.insert(GrammarComponent::Scope);
            }
            ParserEffect::RegistersMacro { name } => {
                out.insert(GrammarComponent::Macro(name.clone()));
            }
            ParserEffect::ChangesOption { name } => {
                out.insert(GrammarComponent::Option(name.clone()));
            }
            ParserEffect::ImportsGrammar { module } => {
                out.insert(GrammarComponent::Import(module.clone()));
            }
            ParserEffect::OpaqueParserEffect { .. } => {
                out.insert(GrammarComponent::WholeGrammar);
            }
        }
    }
}

/// One published, activation-bound grammar change.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrammarTransition {
    pub before: GrammarEpoch,
    pub after: GrammarEpoch,
    pub activation: BytePos,
    pub effects: Vec<ParserEffect>,
}

impl GrammarTransition {
    pub fn has_opaque_effect(&self) -> bool {
        self.effects.iter().any(ParserEffect::is_opaque)
    }

    pub fn affected_components(&self) -> BTreeSet<GrammarComponent> {
        let mut affected = BTreeSet::new();
        for effect in &self.effects {
            effect.affected_components(&mut affected);
        }
        affected
    }
}

/// A scope depth — one `section`/`namespace` level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopeDepth(pub usize);

/// Why a registration was refused.
///
/// Typed, and never a panic: registration runs on user input (a `syntax` command names a category
/// the user typed), so a malformed request is a diagnostic and not an invariant failure — FL-INV-07's
/// family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegisterError {
    /// The category does not exist. Observed at the pin as
    /// `error: unknown category 'nosuchcategory'` for `syntax "zz" : nosuchcategory`.
    UnknownCategory { name: Name },
    /// A category was declared twice.
    CategoryExists { name: Name },
    /// Two requests in one batch claimed the same canonical position.
    ///
    /// Additive shadowing makes production order semantic, so accepting an equal-key pair would
    /// let its arrival order choose the grammar root. The entire batch is refused instead.
    DuplicateRequestKey { key: (u64, String) },
    /// `pop_scope` with no scope open — a `end` without a `section`.
    NoScopeOpen,
}

impl RegisterError {
    /// The pin's wording where it has one, so ours cannot drift.
    pub fn message(&self) -> String {
        match self {
            RegisterError::UnknownCategory { name } => {
                format!("unknown category `{}`", name.to_display_string())
            }
            RegisterError::CategoryExists { name } => {
                format!(
                    "category `{}` has already been declared",
                    name.to_display_string()
                )
            }
            RegisterError::DuplicateRequestKey { key } => {
                format!("duplicate registry request key ({}, {:?})", key.0, key.1)
            }
            RegisterError::NoScopeOpen => "no open scope to close".to_string(),
        }
    }
}

/// A registration hook — upstream's `ParserAttributeHook.postAdd`, which receives the category and
/// the declaration a parser attribute was applied to.
type Hook = Box<dyn Fn(&Name, &Name) + Send + Sync>;

/// One registered production, with the epoch it appeared at and the scope that owns it.
struct Registered {
    production: Production,
    /// The epoch at which this became visible. A lookup at epoch `e` includes it when
    /// `registered_at <= e` — which is the interleaving law.
    registered_at: GrammarEpoch,
    /// The first epoch at which this is no longer visible. Scope exit retires a registration
    /// instead of deleting it so older epoch views remain stable and executable.
    retired_at: Option<GrammarEpoch>,
    /// `None` for a global registration; `Some(depth)` for one retired with its scope.
    scope: Option<ScopeDepth>,
}

impl Registered {
    fn is_live_at(&self, epoch: GrammarEpoch) -> bool {
        self.registered_at <= epoch && self.retired_at.is_none_or(|retired_at| epoch < retired_at)
    }
}

/// The dynamic grammar: categories, their productions, and the scope stack.
pub struct Registry {
    categories: BTreeMap<Name, CategoryState>,
    epoch: GrammarEpoch,
    depth: ScopeDepth,
    /// Hooks, in registration order. Run in **reverse** — see [`Registry::run_hooks`].
    hooks: Vec<Hook>,
}

struct CategoryState {
    name: Name,
    /// The first epoch at which the category exists.
    registered_at: GrammarEpoch,
    behavior: LeadingIdentBehavior,
    /// Append-only, per token. See the module docs: shadowing is additive.
    leading: BTreeMap<Name, Vec<Registered>>,
    trailing: BTreeMap<Name, Vec<Registered>>,
}

impl Registry {
    pub fn new() -> Registry {
        Registry {
            categories: BTreeMap::new(),
            epoch: GrammarEpoch(0),
            depth: ScopeDepth(0),
            hooks: Vec::new(),
        }
    }

    pub fn epoch(&self) -> GrammarEpoch {
        self.epoch
    }

    pub fn scope_depth(&self) -> ScopeDepth {
        self.depth
    }

    /// Declare a category. Refuses a duplicate rather than replacing it.
    pub fn declare_category(
        &mut self,
        name: Name,
        behavior: LeadingIdentBehavior,
    ) -> Result<GrammarEpoch, RegisterError> {
        if self.categories.contains_key(&name) {
            return Err(RegisterError::CategoryExists { name });
        }
        let epoch = self.epoch.next();
        self.categories.insert(
            name.clone(),
            CategoryState {
                name,
                registered_at: epoch,
                behavior,
                leading: BTreeMap::new(),
                trailing: BTreeMap::new(),
            },
        );
        self.epoch = epoch;
        Ok(self.epoch)
    }

    /// Register a leading production under `token` in `category`.
    ///
    /// **Appends.** A second production under the same token does not replace the first — see the
    /// module docs and the `Ambiguous term` observation. `scoped` ties it to the current scope, as
    /// `local notation` does.
    pub fn add_leading(
        &mut self,
        category: &Name,
        token: Name,
        production: Production,
        scoped: bool,
    ) -> Result<GrammarEpoch, RegisterError> {
        self.add(category, token, production, scoped, true)
    }

    /// Register a trailing production. Same appending rule.
    pub fn add_trailing(
        &mut self,
        category: &Name,
        token: Name,
        production: Production,
        scoped: bool,
    ) -> Result<GrammarEpoch, RegisterError> {
        self.add(category, token, production, scoped, false)
    }

    fn add(
        &mut self,
        category: &Name,
        token: Name,
        production: Production,
        scoped: bool,
        leading: bool,
    ) -> Result<GrammarEpoch, RegisterError> {
        if !self.categories.contains_key(category) {
            return Err(RegisterError::UnknownCategory {
                name: category.clone(),
            });
        }
        let epoch = self.epoch.next();
        let scope = scoped.then_some(self.depth);
        let kind = production.kind.clone();
        {
            let state = self.categories.get_mut(category).ok_or_else(|| {
                RegisterError::UnknownCategory {
                    name: category.clone(),
                }
            })?;
            let table = if leading {
                &mut state.leading
            } else {
                &mut state.trailing
            };
            table.entry(token).or_default().push(Registered {
                production,
                registered_at: epoch,
                retired_at: None,
                scope,
            });
        }
        self.epoch = epoch;
        self.run_hooks(category, &kind);
        Ok(epoch)
    }

    /// Open a scope — `section` or `namespace`.
    pub fn push_scope(&mut self) -> GrammarEpoch {
        self.depth = ScopeDepth(self.depth.0 + 1);
        self.epoch = self.epoch.next();
        self.epoch
    }

    /// Close the innermost scope, retiring exactly the registrations it owns.
    ///
    /// Observed at the pin: `local notation` inside `section ... end` is gone after `end`, and with
    /// sections nested, `end` on the inner one leaves the outer one's registrations in place.
    ///
    /// The comparison is equality on depth. I first wrote here that a `>=` would take the
    /// enclosing scope with it, and **that was wrong** — the plant proved it, by failing to fail.
    /// `>=` selects deeper-or-equal, and an active scoped registration can never be deeper than
    /// the current depth, so `>=` and `==` are the same function on every reachable state. The
    /// variant that actually breaks the outer scope is `<=`, which selects shallower-or-equal;
    /// that one is planted and caught. Recorded because a plausible-sounding claim about which
    /// comparison is dangerous is worth exactly as much as the plant that checks it.
    ///
    /// Retirement is stamped with the new epoch rather than physically removing the entry.
    /// Thus the grammar at every earlier epoch remains byte-identical after a later `end`, while
    /// the returned pop epoch observes the restored outer grammar.
    pub fn pop_scope(&mut self) -> Result<GrammarEpoch, RegisterError> {
        if self.depth.0 == 0 {
            return Err(RegisterError::NoScopeOpen);
        }
        let dying = self.depth;
        let epoch = self.epoch.next();
        for state in self.categories.values_mut() {
            for table in [&mut state.leading, &mut state.trailing] {
                for productions in table.values_mut() {
                    for entry in productions {
                        if entry.scope == Some(dying) && entry.retired_at.is_none() {
                            entry.retired_at = Some(epoch);
                        }
                    }
                }
            }
        }
        self.depth = ScopeDepth(self.depth.0 - 1);
        self.epoch = epoch;
        Ok(self.epoch)
    }

    /// Register a hook, called after every production registration.
    ///
    /// Hooks fire in **reverse registration order** — the last registered runs first.
    ///
    /// **This claim is transcribed, not observed.** `registerParserAttributeHook` prepends
    /// (`hook::hooks`, `Extension.lean:313`) and `runParserAttributeHooks` iterates the list as-is
    /// (`:315`), so the order follows. I could not construct a way to *observe* it: hooks are
    /// registered by `builtin_initialize` in compiled Lean, there is no surface syntax for
    /// registering two hooks with distinguishable effects, and the attributes that expose hook
    /// running fire all of them and report nothing about order. Graded on the bead as
    /// observed-by-reading rather than proved, so nobody reads the green bar as behavioural
    /// evidence.
    pub fn register_hook(&mut self, hook: impl Fn(&Name, &Name) + Send + Sync + 'static) {
        self.hooks.push(Box::new(hook));
    }

    fn run_hooks(&self, category: &Name, kind: &Name) {
        for hook in self.hooks.iter().rev() {
            hook(category, kind);
        }
    }

    /// Build the category as of `epoch` — the grammar a parse at that point ran under.
    ///
    /// This is the interleaving law as a function. Observed: a `#check` before its `syntax`
    /// declaration fails with `Unknown identifier`, so a parse cannot see registrations that came
    /// after it. Asking for an old epoch is therefore not a debugging convenience; it is the only
    /// way to replay a parse against the grammar it actually had.
    pub fn view_at(&self, category: &Name, epoch: GrammarEpoch) -> Option<Category> {
        let state = self.categories.get(category)?;
        if state.registered_at > epoch {
            return None;
        }
        let mut view = Category::new(state.name.clone(), state.behavior);
        // History is stored oldest-to-newest. TokenMap::insert prepends like the pin, so replaying
        // it in this order reconstructs the pin's newest-first candidate list at this epoch.
        for (token, productions) in &state.leading {
            for entry in productions.iter().filter(|entry| entry.is_live_at(epoch)) {
                view.leading.insert(token.clone(), entry.production.clone());
            }
        }
        for (token, productions) in &state.trailing {
            for entry in productions.iter().filter(|entry| entry.is_live_at(epoch)) {
                view.trailing
                    .insert(token.clone(), entry.production.clone());
            }
        }
        Some(view)
    }

    /// The kinds registered under `token` in `category` as of `epoch`, in registration order.
    ///
    /// The direct form of the additive-shadowing law: two registrations under one token yield two
    /// kinds here, and a registry that replaced would yield one.
    pub fn kinds_at(&self, category: &Name, token: &Name, epoch: GrammarEpoch) -> Vec<Name> {
        let Some(state) = self.categories.get(category) else {
            return Vec::new();
        };
        if state.registered_at > epoch {
            return Vec::new();
        }
        state
            .leading
            .get(token)
            .map(|productions| {
                productions
                    .iter()
                    .filter(|entry| entry.is_live_at(epoch))
                    .map(|entry| entry.production.kind.clone())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Whether `category` exists.
    pub fn has_category(&self, category: &Name) -> bool {
        self.categories.contains_key(category)
    }

    /// Every category name, in structural [`Name`] order.
    ///
    /// Determinism is a contract (FL-INV-01), which is why the underlying map has a defined
    /// structural order rather than a rendered-string projection or insertion order.
    pub fn category_names(&self) -> Vec<Name> {
        self.categories.keys().cloned().collect()
    }
}

impl Default for Registry {
    fn default() -> Registry {
        Registry::new()
    }
}

impl std::fmt::Debug for Registry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Registry")
            .field("categories", &self.category_names())
            .field("epoch", &self.epoch)
            .field("depth", &self.depth)
            .field("hooks", &self.hooks.len())
            .finish()
    }
}

/// A canonical projection of the active parser-table fields the current engine can encode.
///
/// A *string* rather than a hash, deliberately: when two roots differ the diff should expose the
/// differing input rather than only a digest. The format is versioned and length-framed, and names
/// embed the schema-headed canonical `fln-hash` bytes as hex. Punctuation in a token cannot forge
/// a record boundary, and a numeric name component cannot imitate a string component.
///
/// Categories and tokens use their defined map orders. Productions remain in **registration
/// order**, because additive shadowing makes that sequence semantic. Each production also binds
/// its leading/trailing position, priority, and scope ownership.
///
/// This is not yet complete registry identity: [`Production::run`] is an opaque closure with no
/// stable descriptor for its code or captured state, and the current scope-stack depth and hook
/// identities affect future mutations without changing an active lookup table. A future
/// content-hashed [`GrammarEpoch`] must add those effect-state descriptors and use the canonical
/// hash codec rather than treating this diagnostic projection as a durable artifact.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GrammarRoot(pub String);

const GRAMMAR_ROOT_SCHEMA: &str = "fln.grammar-root/2;";

fn push_decimal(out: &mut String, value: impl ToString) {
    out.push_str(&value.to_string());
    out.push(';');
}

fn push_hex(out: &mut String, bytes: &[u8]) {
    out.push_str(&bytes.len().to_string());
    out.push(':');
    for byte in bytes {
        for nibble in [byte >> 4, byte & 0x0f] {
            out.push(char::from(if nibble < 10 {
                b'0' + nibble
            } else {
                b'a' + nibble - 10
            }));
        }
    }
    out.push(';');
}

/// Append the schema-headed canonical `Name` bytes, rendered as hex so [`GrammarRoot`] remains a
/// string. The codec is owned by `fln-hash`; this module does not maintain a second structural
/// encoding that could drift from artifact identity.
fn push_name(out: &mut String, name: &Name) {
    out.push('N');
    push_hex(out, &name.to_canonical_bytes());
}

fn push_productions(
    out: &mut String,
    position: char,
    table: &BTreeMap<Name, Vec<Registered>>,
    epoch: GrammarEpoch,
) {
    for (token, productions) in table {
        for (order, entry) in productions
            .iter()
            .filter(|entry| entry.is_live_at(epoch))
            .enumerate()
        {
            out.push('P');
            out.push(position);
            out.push('T');
            push_name(out, token);
            out.push('K');
            push_name(out, &entry.production.kind);
            out.push('R');
            push_decimal(out, entry.production.priority);
            out.push('O');
            push_decimal(out, order);
            out.push('S');
            match entry.scope {
                None => out.push_str("0;"),
                Some(depth) => {
                    out.push_str("1;");
                    push_decimal(out, depth.0);
                }
            }
        }
    }
}

/// A registration request, carrying the key that decides its canonical position.
///
/// The key exists because registration order is **not** semantically free here — additive
/// shadowing means the order of productions under a token is part of the grammar. So concurrent
/// registration cannot be made schedule-independent by locking alone: a mutex gives *a* result,
/// not *the same* result. The batch is applied in key order, which is the registered tie-break the
/// determinism doctrine asks for (FL-INV-01, and franken_networkx's CGSE policy shape).
pub struct Request {
    /// The canonical key — in practice a declaration's source order or its name.
    ///
    /// Keys must be unique within one batch. Equal keys are refused before any request is
    /// published because stable sorting would otherwise preserve schedule-dependent arrival order.
    pub key: (u64, String),
    pub category: Name,
    pub token: Name,
    pub production: Production,
    pub scoped: bool,
}

/// A bound on how much a registry may hold.
///
/// Same shape and same law as `fln_syntax::run::LexBudget` (bead franken_lean-81oq): exceeding it
/// is **inconclusive, never a rejection**. A grammar too large to hold is not a malformed grammar,
/// and saying so would tell a user their correct file has an error in it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegistryBudget {
    pub max_categories: u64,
    pub max_productions: u64,
}

impl RegistryBudget {
    pub const fn generous() -> RegistryBudget {
        RegistryBudget {
            max_categories: 4096,
            max_productions: 1 << 20,
        }
    }
}

impl Registry {
    /// The canonical projection of the named, active registry fields as of `epoch`.
    pub fn grammar_root(&self, epoch: GrammarEpoch) -> GrammarRoot {
        let mut out = String::from(GRAMMAR_ROOT_SCHEMA);
        for (name, state) in &self.categories {
            if state.registered_at > epoch {
                continue;
            }
            out.push('C');
            push_name(&mut out, name);
            out.push('B');
            out.push(match state.behavior {
                LeadingIdentBehavior::Default => '0',
                LeadingIdentBehavior::Symbol => '1',
                LeadingIdentBehavior::Both => '2',
            });
            out.push(';');
            push_productions(&mut out, 'L', &state.leading, epoch);
            push_productions(&mut out, 'T', &state.trailing, epoch);
            out.push_str("E;");
        }
        GrammarRoot(out)
    }

    /// How many productions are registered, live at the current epoch.
    pub fn production_count(&self) -> u64 {
        let epoch = self.epoch;
        self.categories
            .values()
            .map(|state| {
                let count: usize = state
                    .leading
                    .values()
                    .chain(state.trailing.values())
                    .map(|productions| {
                        productions
                            .iter()
                            .filter(|entry| entry.is_live_at(epoch))
                            .count()
                    })
                    .sum();
                count as u64
            })
            .sum()
    }

    /// How many production records the registry retains across every epoch.
    ///
    /// Historical callbacks occupy memory even when they are no longer live. Resource admission
    /// therefore uses this count, while [`Self::production_count`] remains the public measure of
    /// the current grammar. Treating retired history as free would let repeated local scopes grow
    /// the registry without ever approaching `RegistryBudget::max_productions`.
    fn retained_production_count(&self) -> u64 {
        self.categories
            .values()
            .map(|state| {
                let count: usize = state
                    .leading
                    .values()
                    .chain(state.trailing.values())
                    .map(Vec::len)
                    .sum();
                count as u64
            })
            .sum()
    }

    /// Apply a batch of requests in **canonical key order**, whatever order they arrive in.
    ///
    /// This is what makes concurrent registration schedule-independent. Sorting by key rather than
    /// applying on arrival is the whole mechanism: because shadowing is additive, arrival order
    /// would otherwise change the sequence of productions under a token and therefore the grammar
    /// root itself.
    ///
    /// Validation is a preflight over the whole canonical batch. Duplicate keys and unknown
    /// categories are therefore typed refusals with no published prefix: the epoch, grammar root,
    /// retained callbacks, and hook observations all remain unchanged.
    pub fn apply_batch(&mut self, requests: Vec<Request>) -> Result<GrammarEpoch, RegisterError> {
        let requests = self.preflight_batch(requests)?;
        for request in requests {
            // Preflight checked every category against this same exclusively borrowed registry.
            // Registration cannot remove categories, so no typed failure remains reachable here.
            self.add_leading(
                &request.category,
                request.token,
                request.production,
                request.scoped,
            )?;
        }
        Ok(self.epoch)
    }

    fn preflight_batch(&self, mut requests: Vec<Request>) -> Result<Vec<Request>, RegisterError> {
        requests.sort_by(|a, b| a.key.cmp(&b.key));

        if let Some(pair) = requests.windows(2).find(|pair| pair[0].key == pair[1].key) {
            return Err(RegisterError::DuplicateRequestKey {
                key: pair[0].key.clone(),
            });
        }

        for request in &requests {
            if !self.categories.contains_key(&request.category) {
                return Err(RegisterError::UnknownCategory {
                    name: request.category.clone(),
                });
            }
        }

        Ok(requests)
    }

    /// Apply a batch under a budget. Exceeding it is `Inconclusive`, never a rejection.
    ///
    /// Resource preflight intentionally precedes request validation: lack of capacity says the
    /// registry did not inspect the whole batch, so FL-INV-07 keeps that result inconclusive rather
    /// than promoting a partial inspection to a user-input rejection.
    pub fn apply_batch_bounded(
        &mut self,
        requests: Vec<Request>,
        budget: RegistryBudget,
    ) -> Outcome<Result<GrammarEpoch, RegisterError>> {
        let categories = self.categories.len() as u64;
        if categories > budget.max_categories {
            return exhausted(
                StructuralUnit::ProducedNodes,
                budget.max_categories,
                categories,
            );
        }
        let projected = self.retained_production_count() + requests.len() as u64;
        if projected > budget.max_productions {
            // Checked BEFORE applying anything, so a refused batch leaves the grammar untouched —
            // the atomicity a caller needs to retry with a larger allowance.
            return exhausted(
                StructuralUnit::ProducedNodes,
                budget.max_productions,
                projected,
            );
        }
        Outcome::Complete(self.apply_batch(requests))
    }
}

fn exhausted(
    unit: StructuralUnit,
    allowed: u64,
    observed: u64,
) -> Outcome<Result<GrammarEpoch, RegisterError>> {
    Outcome::Inconclusive(Inconclusive::resource(ResourceUsage {
        reason: ResourceReason::StructuralBudget { unit },
        allowed,
        observed,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::category::LeadingToken;
    use crate::pratt::Lookup;
    use crate::state::{ParserState, Resolution, longest_match};
    use fln_syntax::source::{BytePos, SourceInfo};
    use fln_syntax::tree::Syntax;
    use std::sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    };

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn production(label: &str) -> Production {
        Production::new(name(label), 0, |_state| {})
    }

    fn request(key: (u64, &str), category: &Name, token: &str, kind: &str) -> Request {
        Request {
            key: (key.0, key.1.to_string()),
            category: category.clone(),
            token: name(token),
            production: production(kind),
            scoped: false,
        }
    }

    fn registry_with_term() -> (Registry, Name) {
        let mut registry = Registry::new();
        let term = name("term");
        registry
            .declare_category(term.clone(), LeadingIdentBehavior::Default)
            .expect("a fresh category declares");
        (registry, term)
    }

    fn run_leading(category: &Category, token: &str) -> (Resolution, ParserState) {
        let lookup = category.leading_at(&LeadingToken::Atom(token.to_string()));
        assert!(
            matches!(lookup, Lookup::Productions(_)),
            "a lexable atom must yield a production list"
        );
        let Lookup::Productions(productions) = lookup else {
            return (Resolution::None, ParserState::new(0));
        };
        let mut state = ParserState::new(0);
        let resolution = longest_match(&mut state, None, &productions);
        (resolution, state)
    }

    fn mutation_state(registry: &Registry) -> (GrammarEpoch, GrammarRoot, u64, u64) {
        (
            registry.epoch(),
            registry.grammar_root(registry.epoch()),
            registry.production_count(),
            registry.retained_production_count(),
        )
    }

    fn root_with_registered(kind: Name, priority: u32, scoped: bool, leading: bool) -> GrammarRoot {
        let (mut registry, term) = registry_with_term();
        if scoped {
            registry.push_scope();
        }
        let production = Production::new(kind, priority, |_state| {});
        if leading {
            registry
                .add_leading(&term, name("tok"), production, scoped)
                .expect("registers leading production");
        } else {
            registry
                .add_trailing(&term, name("tok"), production, scoped)
                .expect("registers trailing production");
        }
        registry.grammar_root(registry.epoch())
    }

    #[test]
    fn an_unknown_category_in_a_batch_is_refused_before_any_request_is_published() {
        for reverse_arrival in [false, true] {
            let (mut registry, term) = registry_with_term();
            registry
                .add_leading(&term, name("existing"), production("existing"), false)
                .expect("the control production registers");
            let hooks = Arc::new(AtomicUsize::new(0));
            let hook_count = Arc::clone(&hooks);
            registry.register_hook(move |_category, _kind| {
                hook_count.fetch_add(1, Ordering::SeqCst);
            });
            let before = mutation_state(&registry);
            let missing = name("missing");
            let mut batch = vec![
                request((10, "valid"), &term, "new", "valid"),
                request((20, "invalid"), &missing, "bad", "invalid"),
            ];
            if reverse_arrival {
                batch.reverse();
            }

            assert_eq!(
                registry.apply_batch(batch),
                Err(RegisterError::UnknownCategory {
                    name: missing.clone()
                }),
                "canonical validation must report the same refusal for either arrival order"
            );
            assert_eq!(
                mutation_state(&registry),
                before,
                "an invalid suffix must not publish the valid prefix"
            );
            assert_eq!(
                hooks.load(Ordering::SeqCst),
                0,
                "a batch that publishes nothing must fire no hooks"
            );
        }
    }

    #[test]
    fn duplicate_request_keys_are_refused_before_arrival_can_choose_production_order() {
        let duplicate_key = (7, "same".to_string());
        for reverse_arrival in [false, true] {
            let (mut registry, term) = registry_with_term();
            let before = mutation_state(&registry);
            let mut batch = vec![
                request((7, "same"), &term, "dup", "first"),
                request((7, "same"), &term, "dup", "second"),
            ];
            if reverse_arrival {
                batch.reverse();
            }

            assert_eq!(
                registry.apply_batch(batch),
                Err(RegisterError::DuplicateRequestKey {
                    key: duplicate_key.clone()
                })
            );
            assert_eq!(
                mutation_state(&registry),
                before,
                "neither equal-key arrival order may become semantic production order"
            );
        }

        assert_eq!(
            RegisterError::DuplicateRequestKey { key: duplicate_key }.message(),
            "duplicate registry request key (7, \"same\")"
        );

        let (mut registry, term) = registry_with_term();
        registry
            .apply_batch(vec![
                request((20, "second"), &term, "dup", "second"),
                request((10, "first"), &term, "dup", "first"),
            ])
            .expect("distinct keys are canonicalizable");
        assert_eq!(
            registry.kinds_at(&term, &name("dup"), registry.epoch()),
            vec![name("first"), name("second")],
            "distinct canonical keys, not arrival order, choose the production sequence"
        );
    }

    #[test]
    fn a_corrected_retry_after_batch_refusal_matches_a_clean_control() {
        let make_batch = |term: &Name, second_category: &Name| {
            vec![
                request((10, "first"), term, "tok", "first"),
                request((20, "second"), second_category, "tok", "second"),
            ]
        };

        let (mut retried, term) = registry_with_term();
        let missing = name("missing");
        assert!(matches!(
            retried.apply_batch(make_batch(&term, &missing)),
            Err(RegisterError::UnknownCategory { .. })
        ));
        retried
            .apply_batch(make_batch(&term, &term))
            .expect("the corrected retry applies");

        let (mut control, control_term) = registry_with_term();
        control
            .apply_batch(make_batch(&control_term, &control_term))
            .expect("the clean control applies");

        assert_eq!(
            mutation_state(&retried),
            mutation_state(&control),
            "a refused attempt must leave no state that a corrected retry can inherit"
        );
    }

    #[test]
    fn bounded_batches_keep_resource_preflight_ahead_of_input_validation() {
        let invalid_batch = |term: &Name| {
            vec![
                request((10, "valid"), term, "new", "valid"),
                request((20, "invalid"), &name("missing"), "bad", "invalid"),
            ]
        };
        let (mut registry, term) = registry_with_term();
        let hooks = Arc::new(AtomicUsize::new(0));
        let hook_count = Arc::clone(&hooks);
        registry.register_hook(move |_category, _kind| {
            hook_count.fetch_add(1, Ordering::SeqCst);
        });
        let before = mutation_state(&registry);

        let admitted = registry.apply_batch_bounded(
            invalid_batch(&term),
            RegistryBudget {
                max_categories: 1,
                max_productions: 2,
            },
        );
        assert!(matches!(
            admitted,
            Outcome::Complete(Err(RegisterError::UnknownCategory { .. }))
        ));
        assert_eq!(mutation_state(&registry), before);

        let exhausted = registry.apply_batch_bounded(
            invalid_batch(&term),
            RegistryBudget {
                max_categories: 1,
                max_productions: 1,
            },
        );
        assert!(
            matches!(exhausted, Outcome::Inconclusive(_)),
            "capacity exhaustion must remain inconclusive before the invalid request is inspected"
        );
        assert_eq!(mutation_state(&registry), before);
        assert_eq!(hooks.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn category_identity_is_structural_not_the_display_projection() {
        let lookalikes = [
            (
                Name::num(Name::anonymous(), 1),
                Name::str(Name::anonymous(), "1"),
            ),
            (
                Name::str(Name::anonymous(), "a.b"),
                Name::str(Name::str(Name::anonymous(), "a"), "b"),
            ),
        ];

        for (left, right) in lookalikes {
            assert_ne!(
                left, right,
                "the control names must be structurally distinct"
            );
            assert_eq!(
                left.to_display_string(),
                right.to_display_string(),
                "the control names must share their presentation"
            );

            let mut registry = Registry::new();
            registry
                .declare_category(left.clone(), LeadingIdentBehavior::Default)
                .expect("the first structural name declares");
            registry
                .declare_category(right.clone(), LeadingIdentBehavior::Default)
                .expect("an equal display string is not a duplicate category");
            registry
                .add_leading(&left, name("tok"), production("left"), false)
                .expect("the left category remains addressable");
            registry
                .add_leading(&right, name("tok"), production("right"), false)
                .expect("the right category remains addressable");

            assert_eq!(
                registry.kinds_at(&left, &name("tok"), registry.epoch()),
                vec![name("left")]
            );
            assert_eq!(
                registry.kinds_at(&right, &name("tok"), registry.epoch()),
                vec![name("right")]
            );
            assert_eq!(
                registry.category_names(),
                vec![left, right],
                "the identity inventory must retain both structural categories"
            );
        }
    }

    #[test]
    fn grammar_root_frames_lists_and_names_without_display_collisions() {
        let root_for_kinds = |kinds: &[&str]| {
            let (mut registry, term) = registry_with_term();
            for kind in kinds {
                registry
                    .add_leading(&term, name("tok"), production(kind), false)
                    .expect("registers");
            }
            registry.grammar_root(registry.epoch())
        };
        assert_ne!(
            root_for_kinds(&["first,second"]),
            root_for_kinds(&["first", "second"]),
            "one punctuated kind is not a two-production list"
        );

        let numeric = Name::num(Name::anonymous(), 1);
        let string = Name::str(Name::anonymous(), "1");
        assert_eq!(numeric.to_display_string(), string.to_display_string());
        assert_ne!(
            root_with_registered(numeric.clone(), 0, false, true),
            root_with_registered(string.clone(), 0, false, true),
            "a production kind's component tag is part of grammar identity"
        );

        let root_for_token = |token: Name| {
            let (mut registry, term) = registry_with_term();
            registry
                .add_leading(&term, token, production("same"), false)
                .expect("registers");
            registry.grammar_root(registry.epoch())
        };
        assert_ne!(
            root_for_token(numeric),
            root_for_token(string),
            "a token key's component tag is part of grammar identity"
        );
    }

    #[test]
    fn grammar_root_binds_priority_position_and_scope_ownership() {
        let baseline = root_with_registered(name("same"), 7, false, true);
        assert_ne!(
            baseline,
            root_with_registered(name("same"), 8, false, true),
            "priority participates in parser resolution"
        );
        assert_ne!(
            baseline,
            root_with_registered(name("same"), 7, false, false),
            "leading and trailing tables have different parser roles"
        );
        assert_ne!(
            baseline,
            root_with_registered(name("same"), 7, true, true),
            "scope exit treats a scoped registration differently"
        );
    }

    #[test]
    fn independently_built_equal_registry_states_have_equal_roots() {
        let kind = || Name::str(Name::str(Name::anonymous(), "a.b"), "c;d");
        assert_eq!(
            root_with_registered(kind(), 17, true, false),
            root_with_registered(kind(), 17, true, false),
            "allocation identity must not enter the grammar projection"
        );
    }

    /// **SHADOWING IS ADDITIVE.** Two productions under one token both stay registered.
    ///
    /// Observed at the pin: two `notation "dup"` declarations then `#eval dup` gives
    /// `error: Ambiguous term`. A registry shaped as a map from token to production — the obvious
    /// shape, and the one I would have written — keeps only the second and never reports the
    /// ambiguity. This is also where `longest_match`'s choice nodes come from.
    #[test]
    fn a_second_production_under_the_same_token_does_not_replace_the_first() {
        let (mut registry, term) = registry_with_term();
        registry
            .add_leading(&term, name("dup"), production("first"), false)
            .expect("registers");
        let epoch = registry
            .add_leading(&term, name("dup"), production("second"), false)
            .expect("registers");

        assert_eq!(
            registry.kinds_at(&term, &name("dup"), epoch),
            vec![name("first"), name("second")],
            "both productions must be live; replacing the first would drop an ambiguity the \
             elaborator is supposed to resolve"
        );
    }

    #[test]
    fn a_category_view_offers_newer_productions_first_at_each_epoch() {
        let (mut registry, term) = registry_with_term();
        let token = name("dup");
        let first = registry
            .add_leading(&term, token.clone(), production("first"), false)
            .expect("registers");
        let second = registry
            .add_leading(&term, token.clone(), production("second"), false)
            .expect("registers");

        let kinds = |epoch| {
            registry
                .view_at(&term, epoch)
                .expect("the category exists")
                .leading
                .get(&token)
                .expect("the token exists")
                .iter()
                .map(|production| production.kind.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(kinds(first), vec![name("first")]);
        assert_eq!(kinds(second), vec![name("second"), name("first")]);
    }

    /// **INTERLEAVING.** A lookup at an epoch sees only registrations made before it.
    ///
    /// Observed at the pin: `#check myfoo` before its `syntax` declaration gives
    /// `Unknown identifier 'myfoo'`; after it, the file is accepted.
    #[test]
    fn a_lookup_at_an_epoch_cannot_see_later_registrations() {
        let (mut registry, term) = registry_with_term();
        let before = registry.epoch();
        let after_first = registry
            .add_leading(&term, name("tok"), production("first"), false)
            .expect("registers");
        let after_second = registry
            .add_leading(&term, name("tok"), production("second"), false)
            .expect("registers");

        assert!(
            registry.kinds_at(&term, &name("tok"), before).is_empty(),
            "an epoch before any registration sees none — this is the `#check` before the \
             `syntax` declaration"
        );
        assert_eq!(
            registry.kinds_at(&term, &name("tok"), after_first),
            vec![name("first")],
            "the epoch after the first registration sees exactly it"
        );
        assert_eq!(
            registry.kinds_at(&term, &name("tok"), after_second),
            vec![name("first"), name("second")],
            "and the later epoch sees both"
        );
    }

    /// Every mutation advances the epoch, so no two grammars share one.
    #[test]
    fn every_mutation_advances_the_epoch() {
        let (mut registry, term) = registry_with_term();
        let mut seen = vec![registry.epoch()];
        seen.push(
            registry
                .add_leading(&term, name("a"), production("a"), false)
                .expect("registers"),
        );
        seen.push(registry.push_scope());
        seen.push(
            registry
                .add_leading(&term, name("b"), production("b"), true)
                .expect("registers"),
        );
        seen.push(registry.pop_scope().expect("pops"));
        seen.push(
            registry
                .declare_category(name("tactic"), LeadingIdentBehavior::Both)
                .expect("declares"),
        );

        let mut unique = seen.clone();
        unique.dedup();
        assert_eq!(
            unique.len(),
            seen.len(),
            "each mutation must produce a distinct epoch: {seen:?}"
        );
        assert!(
            seen.windows(2).all(|pair| pair[0] < pair[1]),
            "and epochs must increase monotonically: {seen:?}"
        );
    }

    /// **SCOPE RESTORE.** Closing a scope discards exactly its own registrations.
    ///
    /// Observed at the pin: `local notation` inside `section ... end` is unknown after `end`.
    #[test]
    fn closing_a_scope_discards_its_registrations() {
        let (mut registry, term) = registry_with_term();
        registry
            .add_leading(&term, name("global"), production("global"), false)
            .expect("registers");
        registry.push_scope();
        registry
            .add_leading(&term, name("local"), production("local"), true)
            .expect("registers");
        let inside = registry.epoch();
        assert_eq!(
            registry.kinds_at(&term, &name("local"), inside),
            vec![name("local")]
        );

        let outside = registry.pop_scope().expect("pops");
        assert!(
            registry.kinds_at(&term, &name("local"), outside).is_empty(),
            "the scoped registration must be gone after the scope closes"
        );
        assert_eq!(
            registry.kinds_at(&term, &name("global"), outside),
            vec![name("global")],
            "and the global one must survive"
        );
    }

    /// **NESTED SCOPES: `end` pops exactly one.**
    ///
    /// Observed at the pin with sections A and B nested: after `end B`, the outer `n1` still
    /// resolves and the inner `n2` does not. Discarding on `scope >= dying` instead of equality
    /// would take the enclosing scope's registrations too — and the single-scope test above would
    /// not notice, because there is nothing enclosing it.
    #[test]
    fn closing_the_inner_scope_leaves_the_outer_one_intact() {
        let (mut registry, term) = registry_with_term();
        registry.push_scope();
        registry
            .add_leading(&term, name("outer"), production("outer"), true)
            .expect("registers");
        registry.push_scope();
        registry
            .add_leading(&term, name("inner"), production("inner"), true)
            .expect("registers");

        let both = registry.epoch();
        assert_eq!(
            registry.kinds_at(&term, &name("outer"), both),
            vec![name("outer")]
        );
        assert_eq!(
            registry.kinds_at(&term, &name("inner"), both),
            vec![name("inner")]
        );

        let after_inner = registry.pop_scope().expect("pops the inner scope");
        assert!(
            registry
                .kinds_at(&term, &name("inner"), after_inner)
                .is_empty(),
            "the inner scope's registration is gone"
        );
        assert_eq!(
            registry.kinds_at(&term, &name("outer"), after_inner),
            vec![name("outer")],
            "the OUTER scope's registration must survive. The discard that breaks this is `<=` \
             on depth, not `>=`: `>=` cannot break it, because no registration is ever deeper than \
             the scope being closed."
        );

        let after_outer = registry.pop_scope().expect("pops the outer scope");
        assert!(
            registry
                .kinds_at(&term, &name("outer"), after_outer)
                .is_empty(),
            "and closing the outer scope discards it"
        );
    }

    /// An unscoped registration made inside a scope survives the scope, which is the difference
    /// between `notation` and `local notation`.
    #[test]
    fn an_unscoped_registration_made_inside_a_scope_survives_it() {
        let (mut registry, term) = registry_with_term();
        registry.push_scope();
        registry
            .add_leading(&term, name("tok"), production("notLocal"), false)
            .expect("registers");
        let after = registry.pop_scope().expect("pops");
        assert_eq!(
            registry.kinds_at(&term, &name("tok"), after),
            vec![name("notLocal")],
            "a plain `notation` inside a section outlives the section"
        );
    }

    /// **UNKNOWN CATEGORY IS A TYPED REFUSAL** with the pin's wording.
    ///
    /// Observed: `syntax "zz" : nosuchcategory` gives `error: unknown category 'nosuchcategory'`.
    #[test]
    fn registering_into_an_unknown_category_is_refused_with_the_pins_wording() {
        let (mut registry, _) = registry_with_term();
        let missing = name("nosuchcategory");
        let refused = registry.add_leading(&missing, name("zz"), production("zz"), false);
        assert_eq!(
            refused,
            Err(RegisterError::UnknownCategory {
                name: missing.clone()
            })
        );
        assert_eq!(
            RegisterError::UnknownCategory { name: missing }.message(),
            "unknown category `nosuchcategory`"
        );
        // And the refusal is inert: the epoch did not move, so a refused registration leaves no
        // trace for a later lookup to find.
        assert_eq!(
            registry.epoch(),
            GrammarEpoch(1),
            "a refused registration must not advance the epoch"
        );
    }

    /// A duplicate category declaration is refused rather than replacing the first, which would
    /// silently discard every production registered into it.
    #[test]
    fn declaring_a_category_twice_is_refused() {
        let (mut registry, term) = registry_with_term();
        registry
            .add_leading(&term, name("tok"), production("p"), false)
            .expect("registers");
        let refused = registry.declare_category(term.clone(), LeadingIdentBehavior::Both);
        assert_eq!(
            refused,
            Err(RegisterError::CategoryExists { name: term.clone() })
        );
        assert_eq!(
            registry.kinds_at(&term, &name("tok"), registry.epoch()),
            vec![name("p")],
            "and the existing productions are untouched"
        );
    }

    /// Closing a scope that was never opened is a typed refusal, not an underflow.
    #[test]
    fn closing_a_scope_that_was_never_opened_is_refused() {
        let (mut registry, _) = registry_with_term();
        assert_eq!(registry.pop_scope(), Err(RegisterError::NoScopeOpen));
        assert_eq!(registry.scope_depth(), ScopeDepth(0));
    }

    /// Hooks fire in reverse registration order — the last registered runs first.
    ///
    /// TRANSCRIBED from `Extension.lean:313` (`hook::hooks`, a prepend) and `:315`
    /// (`hooks.forM`), and **not observed**: see [`Registry::register_hook`] for why no
    /// observation was available. The assertion is here so the implementation cannot drift from
    /// the citation, not because the citation was measured.
    #[test]
    fn hooks_fire_in_reverse_registration_order() {
        let order = Arc::new(Mutex::new(Vec::new()));
        let (mut registry, term) = registry_with_term();

        for label in ["first", "second", "third"] {
            let order = Arc::clone(&order);
            let label = label.to_string();
            registry.register_hook(move |_category, _kind| {
                order.lock().expect("lock").push(label.clone());
            });
        }
        registry
            .add_leading(&term, name("tok"), production("p"), false)
            .expect("registers");

        assert_eq!(
            order.lock().expect("lock").as_slice(),
            &["third", "second", "first"],
            "the last hook registered runs first"
        );
    }

    /// A hook sees the category and the production kind it fired for.
    #[test]
    fn a_hook_receives_the_category_and_kind() {
        let seen = Arc::new(Mutex::new(Vec::new()));
        let (mut registry, term) = registry_with_term();
        let recorder = Arc::clone(&seen);
        registry.register_hook(move |category, kind| {
            recorder.lock().expect("lock").push(format!(
                "{}::{}",
                category.to_display_string(),
                kind.to_display_string()
            ));
        });
        registry
            .add_leading(&term, name("tok"), production("myProduction"), false)
            .expect("registers");
        assert_eq!(
            seen.lock().expect("lock").as_slice(),
            &["term::myProduction"]
        );
    }

    /// A refused registration fires no hooks. A hook that ran for a registration that did not
    /// happen would let an observer act on a grammar change that never occurred.
    #[test]
    fn a_refused_registration_fires_no_hooks() {
        let fired = Arc::new(Mutex::new(0usize));
        let (mut registry, _) = registry_with_term();
        let counter = Arc::clone(&fired);
        registry.register_hook(move |_c, _k| {
            *counter.lock().expect("lock") += 1;
        });
        registry
            .add_leading(&name("nosuchcategory"), name("zz"), production("zz"), false)
            .expect_err("refused");
        assert_eq!(*fired.lock().expect("lock"), 0);
    }

    /// The registry's identity inventory has a defined structural order because determinism is a
    /// contract (FL-INV-01).
    #[test]
    fn category_iteration_order_is_defined() {
        let mut registry = Registry::new();
        for label in ["term", "command", "tactic", "attr"] {
            registry
                .declare_category(name(label), LeadingIdentBehavior::Default)
                .expect("declares");
        }
        assert_eq!(
            registry.category_names(),
            vec![name("attr"), name("command"), name("tactic"), name("term")],
            "sorted, not insertion-ordered"
        );
    }

    /// A historical view retains the exact parser callback, not merely its kind and priority.
    ///
    /// The callback is exercised through the real category lookup and `longest_match` path. A
    /// metadata-only replacement can satisfy every inventory assertion while leaving the
    /// position, precedence, syntax and captured effect unchanged; this cell binds all four.
    #[test]
    fn a_view_at_an_epoch_replays_the_original_production() {
        let (mut registry, term) = registry_with_term();
        let before = registry.epoch();
        let fired = Arc::new(AtomicUsize::new(0));
        let callback_fired = Arc::clone(&fired);
        let after = registry
            .add_leading(
                &term,
                name("tok"),
                Production::new(name("replayed"), 7, move |state| {
                    callback_fired.fetch_add(1, Ordering::SeqCst);
                    state.set_pos(BytePos(3));
                    state.set_lhs_prec(41);
                    state.push(Syntax::atom(
                        SourceInfo::Synthetic {
                            pos: BytePos(0),
                            end_pos: BytePos(3),
                            canonical: false,
                        },
                        "replayed",
                    ));
                }),
                false,
            )
            .expect("registers");

        let old = registry
            .view_at(&term, before)
            .expect("the category already exists");
        assert!(
            old.leading.get(&name("tok")).is_none(),
            "the older view must not contain the later registration"
        );

        let current = registry.view_at(&term, after).expect("exists");
        let (resolution, state) = run_leading(&current, "tok");
        assert_eq!(resolution, Resolution::Unique);
        assert_eq!(state.pos(), BytePos(3));
        assert_eq!(state.lhs_prec(), 41);
        assert!(
            matches!(state.back(), Some(Syntax::Atom { val, .. }) if val == "replayed"),
            "the original callback must build its original syntax"
        );
        assert_eq!(
            fired.load(Ordering::SeqCst),
            1,
            "the historical view must invoke the captured callback exactly once"
        );
        assert_eq!(current.behavior, LeadingIdentBehavior::Default);
    }

    /// Trailing tables retain executable callbacks by the same law as leading tables.
    #[test]
    fn a_historical_view_replays_the_original_trailing_production() {
        let (mut registry, term) = registry_with_term();
        let fired = Arc::new(AtomicUsize::new(0));
        let callback_fired = Arc::clone(&fired);
        let epoch = registry
            .add_trailing(
                &term,
                name("+"),
                Production::new(name("plus"), 3, move |state| {
                    callback_fired.fetch_add(1, Ordering::SeqCst);
                    let left = state.pop().unwrap_or(Syntax::Missing);
                    state.set_pos(BytePos(4));
                    state.set_lhs_prec(29);
                    state.push(Syntax::node(name("plus"), vec![left]));
                }),
                false,
            )
            .expect("registers");
        let historical = registry.view_at(&term, epoch).expect("exists");
        let lookup = historical.trailing_at(&LeadingToken::Atom("+".to_string()));
        assert!(
            matches!(lookup, Lookup::Productions(_)),
            "a lexable atom must yield a production list"
        );
        let Lookup::Productions(productions) = lookup else {
            return;
        };
        let mut state = ParserState::new(0);
        let resolution = longest_match(&mut state, Some(Syntax::Missing), &productions);

        assert_eq!(resolution, Resolution::Unique);
        assert_eq!(state.pos(), BytePos(4));
        assert_eq!(state.lhs_prec(), 29);
        assert!(
            matches!(state.back(), Some(Syntax::Node { kind, args, .. }) if kind == &name("plus") && args == &[Syntax::Missing])
        );
        assert_eq!(fired.load(Ordering::SeqCst), 1);
    }

    /// Scope exit changes the grammar from the pop epoch onward; it must not rewrite history.
    #[test]
    fn scope_exit_preserves_the_inside_epoch_and_retires_only_the_future() {
        let (mut registry, term) = registry_with_term();
        registry.push_scope();
        let fired = Arc::new(AtomicUsize::new(0));
        let callback_fired = Arc::clone(&fired);
        let inside = registry
            .add_leading(
                &term,
                name("local"),
                Production::new(name("local"), 0, move |state| {
                    callback_fired.fetch_add(1, Ordering::SeqCst);
                    state.set_pos(BytePos(5));
                    state.push(Syntax::Missing);
                }),
                true,
            )
            .expect("registers");
        let inside_root = registry.grammar_root(inside);

        let outside = registry.pop_scope().expect("pops");

        assert_eq!(
            registry.grammar_root(inside),
            inside_root,
            "a later scope exit must not rewrite an earlier grammar root"
        );
        assert_eq!(
            registry.kinds_at(&term, &name("local"), inside),
            vec![name("local")],
            "the inside epoch retains the local production"
        );
        assert!(
            registry.kinds_at(&term, &name("local"), outside).is_empty(),
            "the pop epoch observes the restored grammar"
        );

        let historical = registry
            .view_at(&term, inside)
            .expect("the historical category exists");
        let (resolution, state) = run_leading(&historical, "local");
        assert_eq!(resolution, Resolution::Unique);
        assert_eq!(state.pos(), BytePos(5));
        assert_eq!(fired.load(Ordering::SeqCst), 1);

        let restored = registry
            .view_at(&term, outside)
            .expect("the category survives its local production");
        assert!(
            restored.leading.get(&name("local")).is_none(),
            "a current view must not expose a retired local production"
        );
    }

    /// Reusing one numeric depth for a later scope creates a new lifetime, not a continuation of
    /// the earlier scope.
    #[test]
    fn sequential_scopes_at_one_depth_have_disjoint_epoch_intervals() {
        let (mut registry, term) = registry_with_term();
        registry.push_scope();
        let first = registry
            .add_leading(&term, name("same"), production("first"), true)
            .expect("registers first");
        registry.pop_scope().expect("pops first");

        registry.push_scope();
        let second = registry
            .add_leading(&term, name("same"), production("second"), true)
            .expect("registers second");
        let after_second = registry.pop_scope().expect("pops second");

        assert_eq!(
            registry.kinds_at(&term, &name("same"), first),
            vec![name("first")]
        );
        assert_eq!(
            registry.kinds_at(&term, &name("same"), second),
            vec![name("second")],
            "the retired entry from the earlier scope must not revive when its depth is reused"
        );
        assert!(
            registry
                .kinds_at(&term, &name("same"), after_second)
                .is_empty(),
            "both local lifetimes are retired after the second pop"
        );
    }

    /// Category declarations are grammar mutations too, so a pre-declaration epoch cannot see
    /// the category merely because the registry object contains its later state.
    #[test]
    fn a_category_is_absent_before_its_declaration_epoch() {
        let mut registry = Registry::new();
        let term = name("term");
        let before = registry.epoch();
        let declared = registry
            .declare_category(term.clone(), LeadingIdentBehavior::Default)
            .expect("declares");

        assert!(registry.view_at(&term, before).is_none());
        let empty_root = GrammarRoot(GRAMMAR_ROOT_SCHEMA.to_string());
        assert_eq!(registry.grammar_root(before), empty_root);
        assert!(registry.view_at(&term, declared).is_some());
        assert_ne!(
            registry.grammar_root(declared),
            empty_root,
            "the declaration epoch activates the structurally encoded category"
        );
    }

    /// Retired history is absent from the current grammar but still consumes retained storage.
    #[test]
    fn current_and_retained_production_counts_have_distinct_resource_meanings() {
        let (mut registry, term) = registry_with_term();
        registry.push_scope();
        registry
            .add_leading(&term, name("old"), production("old"), true)
            .expect("registers");
        registry.pop_scope().expect("pops");
        assert_eq!(registry.production_count(), 0);

        let request = || Request {
            key: (0, "new".to_string()),
            category: term.clone(),
            token: name("new"),
            production: production("new"),
            scoped: false,
        };
        let refused = registry.apply_batch_bounded(
            vec![request()],
            RegistryBudget {
                max_categories: 1,
                max_productions: 1,
            },
        );
        assert!(
            matches!(refused, Outcome::Inconclusive(_)),
            "the retired callback is not live grammar, but it still occupies retained storage"
        );
        assert_eq!(
            registry.production_count(),
            0,
            "resource refusal must leave the current grammar unchanged"
        );

        let admitted = registry.apply_batch_bounded(
            vec![request()],
            RegistryBudget {
                max_categories: 1,
                max_productions: 2,
            },
        );
        assert!(
            matches!(admitted, Outcome::Complete(Ok(_))),
            "one retired and one live production fit a two-record storage budget"
        );
        assert_eq!(registry.production_count(), 1);
    }

    /// A current-grammar count does not accidentally include a retired callback merely because
    /// it remains available to old views.
    #[test]
    fn production_count_reports_only_the_current_epoch() {
        let (mut registry, term) = registry_with_term();
        registry
            .add_leading(&term, name("global"), production("global"), false)
            .expect("registers global");
        registry.push_scope();
        registry
            .add_leading(&term, name("local"), production("local"), true)
            .expect("registers local");
        assert_eq!(registry.production_count(), 2);
        registry.pop_scope().expect("pops");
        assert_eq!(registry.production_count(), 1);
        assert_eq!(
            registry.kinds_at(&term, &name("global"), registry.epoch()),
            vec![name("global")]
        );
        assert!(
            registry
                .kinds_at(&term, &name("local"), registry.epoch())
                .is_empty()
        );
    }
}
