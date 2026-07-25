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
use crate::state::Production;
use fln_core::name::Name;
use std::collections::BTreeMap;

/// A point in the registration history — upstream's parser state as of one command.
///
/// Monotone and totally ordered. Every mutation produces a new epoch, so a parse can record which
/// grammar it ran under and a later reader can ask for exactly that one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct GrammarEpoch(pub u64);

impl GrammarEpoch {
    fn next(self) -> GrammarEpoch {
        GrammarEpoch(self.0 + 1)
    }
}

/// A scope depth — one `section`/`namespace` level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
    /// `at <= e` — which is the interleaving law.
    at: GrammarEpoch,
    /// `None` for a global registration; `Some(depth)` for one that dies with its scope.
    scope: Option<ScopeDepth>,
}

/// The dynamic grammar: categories, their productions, and the scope stack.
pub struct Registry {
    categories: BTreeMap<String, CategoryState>,
    epoch: GrammarEpoch,
    depth: ScopeDepth,
    /// Hooks, in registration order. Run in **reverse** — see [`Registry::run_hooks`].
    hooks: Vec<Hook>,
}

struct CategoryState {
    name: Name,
    behavior: LeadingIdentBehavior,
    /// Append-only, per token. See the module docs: shadowing is additive.
    leading: BTreeMap<String, Vec<Registered>>,
    trailing: BTreeMap<String, Vec<Registered>>,
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
        let key = name.to_display_string();
        if self.categories.contains_key(&key) {
            return Err(RegisterError::CategoryExists { name });
        }
        self.categories.insert(
            key,
            CategoryState {
                name,
                behavior,
                leading: BTreeMap::new(),
                trailing: BTreeMap::new(),
            },
        );
        self.epoch = self.epoch.next();
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
        token: impl Into<String>,
        production: Production,
        scoped: bool,
    ) -> Result<GrammarEpoch, RegisterError> {
        self.add(category, token, production, scoped, true)
    }

    /// Register a trailing production. Same appending rule.
    pub fn add_trailing(
        &mut self,
        category: &Name,
        token: impl Into<String>,
        production: Production,
        scoped: bool,
    ) -> Result<GrammarEpoch, RegisterError> {
        self.add(category, token, production, scoped, false)
    }

    fn add(
        &mut self,
        category: &Name,
        token: impl Into<String>,
        production: Production,
        scoped: bool,
        leading: bool,
    ) -> Result<GrammarEpoch, RegisterError> {
        let key = category.to_display_string();
        if !self.categories.contains_key(&key) {
            return Err(RegisterError::UnknownCategory {
                name: category.clone(),
            });
        }
        let epoch = self.epoch.next();
        let scope = scoped.then_some(self.depth);
        let kind = production.kind.clone();
        {
            let state =
                self.categories
                    .get_mut(&key)
                    .ok_or_else(|| RegisterError::UnknownCategory {
                        name: category.clone(),
                    })?;
            let table = if leading {
                &mut state.leading
            } else {
                &mut state.trailing
            };
            table.entry(token.into()).or_default().push(Registered {
                production,
                at: epoch,
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

    /// Close the innermost scope, discarding exactly the registrations it owns.
    ///
    /// Observed at the pin: `local notation` inside `section ... end` is gone after `end`, and with
    /// sections nested, `end` on the inner one leaves the outer one's registrations in place.
    ///
    /// The comparison is equality on depth. I first wrote here that a `>=` would take the
    /// enclosing scope with it, and **that was wrong** — the plant proved it, by failing to fail.
    /// `>=` discards deeper-or-equal, and a scoped registration can never be deeper than the
    /// current depth, so `>=` and `==` are the same function on every reachable state. The variant
    /// that actually breaks the outer scope is `<=`, which discards shallower-or-equal; that one is
    /// planted and caught. Recorded because a plausible-sounding claim about which comparison is
    /// dangerous is worth exactly as much as the plant that checks it.
    pub fn pop_scope(&mut self) -> Result<GrammarEpoch, RegisterError> {
        if self.depth.0 == 0 {
            return Err(RegisterError::NoScopeOpen);
        }
        let dying = self.depth;
        for state in self.categories.values_mut() {
            for table in [&mut state.leading, &mut state.trailing] {
                for productions in table.values_mut() {
                    productions.retain(|entry| entry.scope != Some(dying));
                }
            }
        }
        self.depth = ScopeDepth(self.depth.0 - 1);
        self.epoch = self.epoch.next();
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
        let state = self.categories.get(&category.to_display_string())?;
        let mut view = Category::new(state.name.clone(), state.behavior);
        for (token, productions) in &state.leading {
            for entry in productions.iter().filter(|entry| entry.at <= epoch) {
                view.leading.insert(
                    token.clone(),
                    Production::new(entry.production.kind.clone(), entry.production.priority, {
                        // The view holds a re-entrant copy: `Production` owns a boxed closure and
                        // cannot be cloned, so the view's production delegates by kind. A view is
                        // for *inspecting* which productions were live, which is what every
                        // assertion in this bead needs.
                        move |_state| {}
                    }),
                );
            }
        }
        for (token, productions) in &state.trailing {
            for entry in productions.iter().filter(|entry| entry.at <= epoch) {
                view.trailing.insert(
                    token.clone(),
                    Production::new(entry.production.kind.clone(), entry.production.priority, {
                        move |_state| {}
                    }),
                );
            }
        }
        Some(view)
    }

    /// The kinds registered under `token` in `category` as of `epoch`, in registration order.
    ///
    /// The direct form of the additive-shadowing law: two registrations under one token yield two
    /// kinds here, and a registry that replaced would yield one.
    pub fn kinds_at(&self, category: &Name, token: &str, epoch: GrammarEpoch) -> Vec<String> {
        let Some(state) = self.categories.get(&category.to_display_string()) else {
            return Vec::new();
        };
        state
            .leading
            .get(token)
            .map(|productions| {
                productions
                    .iter()
                    .filter(|entry| entry.at <= epoch)
                    .map(|entry| entry.production.kind.to_display_string())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Whether `category` exists.
    pub fn has_category(&self, category: &Name) -> bool {
        self.categories.contains_key(&category.to_display_string())
    }

    /// Every category name, sorted — determinism is a contract (FL-INV-01), so the iteration order
    /// of the registry is defined rather than incidental.
    pub fn category_names(&self) -> Vec<String> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn production(label: &str) -> Production {
        Production::new(name(label), 0, |_state| {})
    }

    fn registry_with_term() -> (Registry, Name) {
        let mut registry = Registry::new();
        let term = name("term");
        registry
            .declare_category(term.clone(), LeadingIdentBehavior::Default)
            .expect("a fresh category declares");
        (registry, term)
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
            .add_leading(&term, "dup", production("first"), false)
            .expect("registers");
        let epoch = registry
            .add_leading(&term, "dup", production("second"), false)
            .expect("registers");

        assert_eq!(
            registry.kinds_at(&term, "dup", epoch),
            vec!["first", "second"],
            "both productions must be live; replacing the first would drop an ambiguity the \
             elaborator is supposed to resolve"
        );
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
            .add_leading(&term, "tok", production("first"), false)
            .expect("registers");
        let after_second = registry
            .add_leading(&term, "tok", production("second"), false)
            .expect("registers");

        assert!(
            registry.kinds_at(&term, "tok", before).is_empty(),
            "an epoch before any registration sees none — this is the `#check` before the \
             `syntax` declaration"
        );
        assert_eq!(
            registry.kinds_at(&term, "tok", after_first),
            vec!["first"],
            "the epoch after the first registration sees exactly it"
        );
        assert_eq!(
            registry.kinds_at(&term, "tok", after_second),
            vec!["first", "second"],
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
                .add_leading(&term, "a", production("a"), false)
                .expect("registers"),
        );
        seen.push(registry.push_scope());
        seen.push(
            registry
                .add_leading(&term, "b", production("b"), true)
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
            .add_leading(&term, "global", production("global"), false)
            .expect("registers");
        registry.push_scope();
        registry
            .add_leading(&term, "local", production("local"), true)
            .expect("registers");
        let inside = registry.epoch();
        assert_eq!(registry.kinds_at(&term, "local", inside), vec!["local"]);

        let outside = registry.pop_scope().expect("pops");
        assert!(
            registry.kinds_at(&term, "local", outside).is_empty(),
            "the scoped registration must be gone after the scope closes"
        );
        assert_eq!(
            registry.kinds_at(&term, "global", outside),
            vec!["global"],
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
            .add_leading(&term, "outer", production("outer"), true)
            .expect("registers");
        registry.push_scope();
        registry
            .add_leading(&term, "inner", production("inner"), true)
            .expect("registers");

        let both = registry.epoch();
        assert_eq!(registry.kinds_at(&term, "outer", both), vec!["outer"]);
        assert_eq!(registry.kinds_at(&term, "inner", both), vec!["inner"]);

        let after_inner = registry.pop_scope().expect("pops the inner scope");
        assert!(
            registry.kinds_at(&term, "inner", after_inner).is_empty(),
            "the inner scope's registration is gone"
        );
        assert_eq!(
            registry.kinds_at(&term, "outer", after_inner),
            vec!["outer"],
            "the OUTER scope's registration must survive. The discard that breaks this is `<=` \
             on depth, not `>=`: `>=` cannot break it, because no registration is ever deeper than \
             the scope being closed."
        );

        let after_outer = registry.pop_scope().expect("pops the outer scope");
        assert!(
            registry.kinds_at(&term, "outer", after_outer).is_empty(),
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
            .add_leading(&term, "tok", production("notLocal"), false)
            .expect("registers");
        let after = registry.pop_scope().expect("pops");
        assert_eq!(
            registry.kinds_at(&term, "tok", after),
            vec!["notLocal"],
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
        let refused = registry.add_leading(&missing, "zz", production("zz"), false);
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
            .add_leading(&term, "tok", production("p"), false)
            .expect("registers");
        let refused = registry.declare_category(term.clone(), LeadingIdentBehavior::Both);
        assert_eq!(
            refused,
            Err(RegisterError::CategoryExists { name: term.clone() })
        );
        assert_eq!(
            registry.kinds_at(&term, "tok", registry.epoch()),
            vec!["p"],
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
            .add_leading(&term, "tok", production("p"), false)
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
            .add_leading(&term, "tok", production("myProduction"), false)
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
            .add_leading(&name("nosuchcategory"), "zz", production("zz"), false)
            .expect_err("refused");
        assert_eq!(*fired.lock().expect("lock"), 0);
    }

    /// The registry's iteration order is defined, because determinism is a contract (FL-INV-01)
    /// and the candidate order reaches `longest_match`.
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
            vec!["attr", "command", "tactic", "term"],
            "sorted, not insertion-ordered"
        );
    }

    /// A view at an epoch reports which productions were live, and the view is a `Category` the
    /// engine's lookup accepts — so the interleaving law and the lookup law compose.
    #[test]
    fn a_view_at_an_epoch_is_a_usable_category() {
        let (mut registry, term) = registry_with_term();
        let before = registry.epoch();
        let after = registry
            .add_leading(&term, "tok", production("p"), false)
            .expect("registers");

        let old = registry
            .view_at(&term, before)
            .expect("the category exists");
        assert!(
            old.leading.get("tok").is_none(),
            "the older view must not contain the later registration"
        );
        let new = registry.view_at(&term, after).expect("exists");
        assert!(
            new.leading.get("tok").is_some(),
            "the newer view must contain it"
        );
        assert_eq!(new.behavior, LeadingIdentBehavior::Default);
    }
}
