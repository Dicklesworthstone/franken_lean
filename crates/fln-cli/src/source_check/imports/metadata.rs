//! Import-order planning and presentation, not a second metadata interpreter.
use super::*;
use fln::source_check::modules::imported::SourceOleanImportError;
use std::collections::BTreeSet;

/// Only previously bounded, validated source headers enter this walk. Every
/// source module and external root is visited once, in declared import order.
/// The ordinary module checker retains cycle and reachability authority.
pub(super) fn ordered_roots(graph: &BTreeMap<Name, Vec<Name>>, entries: &[Name]) -> Vec<Name> {
    let mut seen = BTreeSet::new();
    let mut pending: Vec<_> = entries.iter().rev().cloned().collect();
    let mut roots = Vec::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if let Some(imports) = graph.get(&name) {
            pending.extend(imports.iter().rev().cloned());
        } else {
            roots.push(name);
        }
    }
    roots
}

pub(super) fn failure(error: SourceOleanImportError) -> Failure {
    let (class, authority, exit) = match &error {
        SourceOleanImportError::Check(error) => check_olean_error_disposition(error),
        error if error.metadata_resource_exhausted() => ("resource", false, 3),
        SourceOleanImportError::Internal(_) => ("internal-fault", false, 4),
        _ => ("input", false, 1),
    };
    Failure {
        class,
        authority,
        exit,
        detail: format!("importing .olean modules: {error}"),
    }
}

impl OleanBase {
    /// Counts remain bounded by the imported artifact closure. Unknown names
    /// stay available in the library report; the CLI reports their count rather
    /// than allocating an unbounded diagnostic list or claiming full support.
    pub(in crate::source_check) fn json(&self) -> String {
        let mut classes = 0usize;
        let mut instances = 0usize;
        let mut defaults = 0usize;
        let mut scoped = 0usize;
        let mut uninterpreted = 0usize;
        for module in &self.metadata {
            classes += module.classes;
            instances += module.instances;
            defaults += module.defaults;
            scoped += module.scoped_instances;
            uninterpreted += module.uninterpreted.len();
        }
        format!(
            ",\"oleanImports\":{{{},\"modules\":{},\"declarations\":{}}},\"declarationLogicalRoot\":{},\"oleanMetadata\":{{\"classes\":{classes},\"instances\":{instances},\"defaultInstances\":{defaults},\"scopedInstances\":{scoped},\"uninterpretedExtensions\":{uninterpreted}}}",
            super::reuse::json_fields(&self.report),
            self.modules,
            self.declarations,
            json_string(&self.declaration_root.to_string()),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn n(s: &str) -> Name {
        Name::from_components([s])
    }
    #[test]
    fn dependency_order_is_not_breadth_first_or_alphabetical() {
        let graph = BTreeMap::from([
            (n("Main"), vec![n("Wrapper"), n("A")]),
            (n("Wrapper"), vec![n("B"), n("Common")]),
        ]);
        assert_eq!(
            ordered_roots(&graph, &[n("Main")]),
            [n("B"), n("Common"), n("A")]
        );
    }
    #[test]
    fn diamonds_and_cycles_are_finite_without_replaying_roots() {
        let graph = BTreeMap::from([
            (n("Main"), vec![n("Left"), n("Right"), n("A")]),
            (n("Left"), vec![n("B"), n("Main")]),
            (n("Right"), vec![n("B"), n("A")]),
        ]);
        assert_eq!(ordered_roots(&graph, &[n("Main")]), [n("B"), n("A")]);
    }
    #[test]
    fn metadata_budgets_and_internal_faults_are_not_input_rejections() {
        for error in [
            SourceOleanImportError::Limit("entries"),
            SourceOleanImportError::Capture {
                module: n("A"),
                error: fln::OleanRegionError::BudgetExhausted {
                    visited: 1,
                    budget: 0,
                },
            },
        ] {
            let failure = failure(error);
            assert_eq!(
                (failure.class, failure.authority, failure.exit),
                ("resource", false, 3)
            );
        }
        let failure = failure(SourceOleanImportError::Internal("test"));
        assert_eq!(
            (failure.class, failure.authority, failure.exit),
            ("internal-fault", false, 4)
        );
    }
}
