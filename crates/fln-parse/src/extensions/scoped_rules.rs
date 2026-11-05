//! Namespace-scoped quoted clauses and activation-time precedence.
//!
//! The pin's ScopedEnvExtension adds an activated namespace after the current
//! rules, ignores a repeated activation, and adds later global/scoped entries
//! to each state where they are active. Registration order alone is not enough.
use super::*;

#[derive(Debug, Clone, Default)]
pub(super) struct RuleScope {
    pub namespace: Option<Name>,
    pub registered: usize,
}

/// One clause's precedence in an exact source grammar snapshot. A registration
/// and all its clauses share the same order. Lexicographic comparison gives
/// registration/activation chronology; ties retain the original clause order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TemplateClauseOrder {
    pub precedence: [usize; 3],
    /// Native import journals do not yet identify their position among
    /// independently imported MacroM registrations. A mixed dispatcher must
    /// refuse an unresolved tie instead of choosing an arbitrary winner.
    pub imported: bool,
}

/// Immutable source rules plus the chronology needed to merge them with
/// imported macros. This is invocation state, never serialized module data.
#[derive(Debug, Clone, Default)]
pub struct TemplateSnapshot {
    pub rules: Arc<BTreeMap<Name, Arc<NotationRule>>>,
    pub orders: BTreeMap<Name, Vec<TemplateClauseOrder>>,
    pub activations: BTreeMap<Name, [usize; 3]>,
    pub initially_active: BTreeSet<Name>,
}

impl FileGrammar {
    pub(super) fn prepended_rule_scopes(
        &self,
        kind: &Name,
        previous: usize,
        added: usize,
        namespace: Option<Name>,
    ) -> Result<Option<Vec<RuleScope>>, &'static str> {
        let older = self.rule_scopes.get(kind);
        if older.is_some_and(|scopes| scopes.len() != previous) {
            return Err("native scoped macro metadata does not match its clause chain");
        }
        let mut scopes = vec![
            RuleScope {
                namespace,
                registered: self.generation + 1
            };
            added
        ];
        match older {
            Some(older) => scopes.extend_from_slice(older),
            None => scopes.resize(added + previous, RuleScope::default()),
        }
        Ok(Some(scopes))
    }

    pub(super) fn imported_rule_scopes(
        &self,
        kind: &Name,
        previous: usize,
        own: usize,
        added: usize,
        incoming: Option<&Vec<Option<Name>>>,
    ) -> Result<Option<Vec<RuleScope>>, &'static str> {
        let older = self.rule_scopes.get(kind);
        if incoming.is_none() && older.is_none() {
            return Ok(None);
        }
        if own > previous || older.is_some_and(|scopes| scopes.len() != previous) {
            return Err("native scoped macro metadata does not match its import prefix");
        }
        let previous = older
            .cloned()
            .unwrap_or_else(|| vec![RuleScope::default(); previous]);
        let mut scopes = previous[..own].to_vec();
        scopes.extend((0..added).map(|index| RuleScope {
            namespace: incoming.and_then(|names| names[index].clone()),
            // Import order is already represented by the canonical clause chain.
            // An imported scoped rule only gains precedence upon activation.
            registered: 0,
        }));
        scopes.extend_from_slice(&previous[own..]);
        Ok(Some(scopes))
    }

    pub(super) fn exported_rule_scopes(
        &self,
        kind: &Name,
        count: usize,
    ) -> Result<Option<Vec<Option<Name>>>, &'static str> {
        let Some(scopes) = self.rule_scopes.get(kind) else {
            return Ok(None);
        };
        let rule = self
            .rules
            .get(kind)
            .ok_or("scoped macro metadata without a rule")?;
        if scopes.len() != rule.cases().count() {
            return Err("native scoped macro metadata does not match its exported chain");
        }
        let depths = self.local_rule_depths.get(kind);
        let names: Vec<_> = scopes
            .iter()
            .enumerate()
            .filter(|(index, _)| depths.is_none_or(|depths| depths[*index].is_none()))
            .take(count)
            .map(|(_, scope)| scope.namespace.clone())
            .collect();
        if names.len() != count {
            return Err("native scoped macro export has an incomplete prefix");
        }
        Ok(names.iter().any(Option::is_some).then_some(names))
    }

    /// Reconstruct an immutable active view without altering the exported rule
    /// chain or definition-site template indices. A namespace's activation rank
    /// precedes later registrations and follows every registration it observed.
    pub(super) fn active_rules(&self, trail: &[Trail]) -> Arc<BTreeMap<Name, Arc<NotationRule>>> {
        if self.rule_scopes.is_empty() {
            return Arc::clone(&self.rules);
        }
        let activations: BTreeMap<_, _> = trail
            .iter()
            .enumerate()
            .filter_map(|(position, entry)| match entry {
                Trail::Namespace(namespace, _, generation) => {
                    let rank = if self.initial_macro_scopes.contains(namespace) {
                        (0, 1, 0)
                    } else {
                        (*generation, 1, position)
                    };
                    Some((namespace, rank))
                }
                Trail::Decl(_) => None,
            })
            .collect();
        let mut rules = Arc::clone(&self.rules);
        for (kind, scopes) in &self.rule_scopes {
            let Some(rule) = self.rules.get(kind) else {
                continue;
            };
            if scopes.len() != rule.cases().count() {
                // Corrupt locality metadata cannot activate an unclassified rule.
                Arc::make_mut(&mut rules).remove(kind);
                continue;
            }
            let mut cases: Vec<_> = rule
                .cases()
                .zip(scopes)
                .filter_map(|(case, scope)| {
                    let registered = (scope.registered, 0, 0);
                    let rank = match &scope.namespace {
                        None => registered,
                        Some(namespace) => registered.max(*activations.get(namespace)?),
                    };
                    Some((rank, case))
                })
                .collect();
            // Stable ties keep each registration's top-to-bottom clause order
            // and the existing newest-first import/registration order.
            cases.sort_by_key(|(rank, _)| std::cmp::Reverse(*rank));
            let mut cases = cases.into_iter().map(|(_, case)| modules::flat_case(case));
            if let Some(mut head) = cases.next() {
                head.fallbacks = cases.collect();
                Arc::make_mut(&mut rules).insert(kind.clone(), Arc::new(head));
            } else {
                Arc::make_mut(&mut rules).remove(kind);
            }
        }
        rules
    }

    pub(super) fn template_snapshot(
        &self,
        trail: &[Trail],
    ) -> Result<TemplateSnapshot, &'static str> {
        let activations: BTreeMap<_, _> = trail
            .iter()
            .enumerate()
            .filter_map(|(position, entry)| match entry {
                Trail::Namespace(namespace, _, generation) => {
                    let rank = if self.initial_macro_scopes.contains(namespace) {
                        [0, 1, 0]
                    } else {
                        [*generation, 1, position]
                    };
                    Some((namespace.clone(), rank))
                }
                Trail::Decl(_) => None,
            })
            .collect();
        let mut rules = BTreeMap::new();
        let mut orders = BTreeMap::new();
        for (kind, rule) in self.rules.iter() {
            let scopes = self.rule_scopes.get(kind);
            if scopes.is_some_and(|scopes| scopes.len() != rule.cases().count()) {
                return Err("native scoped macro metadata does not match its clause chain");
            }
            let mut cases = Vec::new();
            for (index, case) in rule.cases().enumerate() {
                let scope = scopes.and_then(|scopes| scopes.get(index));
                let registered = scope.map_or(0, |scope| scope.registered);
                let mut precedence = [registered, 0, 0];
                if let Some(namespace) = scope.and_then(|scope| scope.namespace.as_ref()) {
                    let Some(activation) = activations.get(namespace) else {
                        continue;
                    };
                    precedence = precedence.max(*activation);
                }
                cases.push((
                    TemplateClauseOrder {
                        precedence,
                        imported: registered == 0,
                    },
                    case,
                ));
            }
            // This is the same stable order as active_rules: newer registrations
            // and later activations first, clauses within one registration intact.
            cases.sort_by_key(|(order, _)| std::cmp::Reverse(order.precedence));
            if cases.is_empty() {
                continue;
            }
            orders.insert(
                kind.clone(),
                cases.iter().map(|(order, _)| *order).collect(),
            );
            let mut cases = cases.into_iter().map(|(_, case)| modules::flat_case(case));
            let mut head = cases.next().expect("nonempty active macro clause chain");
            head.fallbacks = cases.collect();
            rules.insert(kind.clone(), Arc::new(head));
        }
        Ok(TemplateSnapshot {
            rules: Arc::new(rules),
            orders,
            activations,
            initially_active: self.initial_macro_scopes.clone(),
        })
    }
}

#[cfg(test)]
mod tests;
