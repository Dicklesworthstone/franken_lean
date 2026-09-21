//! Bounded dependency observations from the real editor resolver, not wire telemetry.
use super::*;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

const MAX_PATH_BYTES: usize = 4 * 1024 * 1024;
const MAX_PATHS: usize = 16_384;

enum Watch {
    /// An incomplete load may hide more imports. Recheck conservatively rather
    /// than preserving a stale answer or losing recovery when a missing file opens.
    Unknown,
    Known(BTreeSet<PathBuf>),
}

pub(super) struct Dependencies {
    entries: BTreeMap<String, Watch>,
    max_bytes: usize,
    max_paths: usize,
}
impl Default for Dependencies {
    fn default() -> Self {
        Self {
            entries: BTreeMap::new(),
            max_bytes: MAX_PATH_BYTES,
            max_paths: MAX_PATHS,
        }
    }
}
impl Dependencies {
    fn prune(&mut self, documents: &[OpenDocumentSource<'_>]) {
        let open: BTreeSet<_> = documents.iter().map(|d| d.uri).collect();
        self.entries.retain(|uri, _| open.contains(uri.as_str()));
    }
    pub(super) fn begin(&mut self, uri: &str, documents: &[OpenDocumentSource<'_>]) {
        self.prune(documents);
        // Protocol membership owns lifetime and URI budgets; unavailable source
        // still counts as open. No separate mutable text store is introduced.
        if documents.iter().any(|d| d.uri == uri) {
            self.entries.insert(uri.to_owned(), Watch::Unknown);
        }
    }
    pub(super) fn no_imports(&mut self, uri: &str) {
        self.remember(uri, BTreeSet::new());
    }
    pub(super) fn loaded(&mut self, uri: &str, source_uris: &[String]) {
        let mut paths = BTreeSet::new();
        let mut bytes = 0usize;
        for imported in source_uris.iter().skip(1) {
            let Ok(path) = editor::document_path(imported) else {
                return;
            };
            bytes = bytes.saturating_add(path.as_os_str().len());
            if bytes > self.max_bytes || paths.len() >= self.max_paths {
                return;
            }
            paths.insert(path);
        }
        self.remember(uri, paths);
    }
    fn remember(&mut self, uri: &str, paths: BTreeSet<PathBuf>) {
        let Some(entry) = self.entries.get_mut(uri) else {
            return;
        };
        *entry = Watch::Unknown;
        let mut count = paths.len();
        let mut bytes = paths
            .iter()
            .fold(0usize, |n, p| n.saturating_add(p.as_os_str().len()));
        for watch in self.entries.values() {
            if let Watch::Known(existing) = watch {
                count = count.saturating_add(existing.len());
                bytes = existing
                    .iter()
                    .fold(bytes, |n, p| n.saturating_add(p.as_os_str().len()));
            }
        }
        // A retention ceiling changes precision, never correctness or check
        // eligibility: Unknown is an explicit conservative dependency set.
        if count <= self.max_paths && bytes <= self.max_bytes {
            self.entries.insert(uri.to_owned(), Watch::Known(paths));
        }
    }
    fn select(&self, paths: &BTreeSet<PathBuf>, uncertain: bool) -> Vec<String> {
        self.entries
            .iter()
            .filter(|(_, watch)| match watch {
                Watch::Unknown => true,
                Watch::Known(dependencies) => {
                    !dependencies.is_empty()
                        && (uncertain
                            || dependencies
                                .iter()
                                .any(|p| paths.iter().any(|changed| p.starts_with(changed))))
                }
            })
            .map(|(uri, _)| uri.clone())
            .collect()
    }
    pub(super) fn affected(
        &mut self,
        changed: &[String],
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        self.prune(documents);
        let mut local = false;
        let mut uncertain = false;
        let mut paths = BTreeSet::new();
        for uri in changed.iter().filter(|uri| uri.starts_with("file://")) {
            local = true;
            match editor::document_path(uri) {
                Ok(path) => {
                    paths.insert(path);
                }
                // Deletion, symlink replacement or unavailable parent cannot
                // erase an already recorded edge by making normalization fail.
                Err(_) => uncertain = true,
            }
        }
        if local {
            self.select(&paths, uncertain)
        } else {
            Vec::new()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn paths(names: &[&str]) -> BTreeSet<PathBuf> {
        names.iter().map(PathBuf::from).collect()
    }
    fn known(names: &[&str]) -> Watch {
        Watch::Known(paths(names))
    }
    fn fixture() -> Dependencies {
        Dependencies {
            entries: BTreeMap::from([
                ("Main".to_owned(), known(&["Base", "Left", "Right"])),
                ("Left".to_owned(), known(&["Base"])),
                ("Right".to_owned(), known(&["Base"])),
                ("Other".to_owned(), known(&[])),
            ]),
            ..Dependencies::default()
        }
    }
    #[test]
    fn transitive_diamonds_select_each_consumer_once_not_unrelated_siblings() {
        let watches = fixture();
        assert_eq!(
            watches.select(&paths(&["Base"]), false),
            ["Left", "Main", "Right"]
        );
        assert_eq!(watches.select(&paths(&["Left"]), false), ["Main"]);
        assert!(watches.select(&paths(&["Other"]), false).is_empty());
    }
    #[test]
    fn failed_discovery_and_unresolvable_events_cannot_hide_dependencies() {
        let mut watches = fixture();
        watches.entries.insert("Missing".to_owned(), Watch::Unknown);
        assert_eq!(watches.select(&paths(&["New"]), false), ["Missing"]);
        assert_eq!(
            watches.select(&paths(&[]), true),
            ["Left", "Main", "Missing", "Right"]
        );
    }
    #[test]
    fn path_count_and_byte_pressure_fall_back_to_conservative_observation() {
        let mut watches = fixture();
        watches.max_paths = 1;
        watches.remember("Main", paths(&["Base", "New"]));
        assert!(matches!(watches.entries["Main"], Watch::Unknown));
        assert_eq!(watches.select(&paths(&["unrelated"]), false), ["Main"]);
        watches.max_paths = MAX_PATHS;
        watches.max_bytes = 1;
        watches.remember("Main", paths(&["Base"]));
        assert!(matches!(watches.entries["Main"], Watch::Unknown));
    }
    #[test]
    fn successful_rediscovery_replaces_removed_import_edges() {
        let mut watches = fixture();
        watches.remember("Main", paths(&["New"]));
        assert_eq!(watches.select(&paths(&["Base"]), false), ["Left", "Right"]);
        assert_eq!(watches.select(&paths(&["New"]), false), ["Main"]);
        watches.no_imports("Main");
        assert!(watches.select(&paths(&["New"]), false).is_empty());
    }
    #[test]
    fn directory_events_invalidate_descendants_not_string_prefix_neighbors() {
        let watches = Dependencies {
            entries: BTreeMap::from([
                ("Main".to_owned(), known(&["Lib/A.lean", "Lib/B.lean"])),
                ("Other".to_owned(), known(&["Library/A.lean"])),
            ]),
            ..Dependencies::default()
        };
        assert_eq!(watches.select(&paths(&["Lib"]), false), ["Main"]);
        assert_eq!(watches.select(&paths(&["Lib/A.lean"]), false), ["Main"]);
        assert!(watches.select(&paths(&["Li"]), false).is_empty());
    }
    #[test]
    fn closes_release_observations_but_unavailable_open_sources_do_not() {
        let mut watches = fixture();
        let docs = [OpenDocumentSource {
            uri: "Main",
            version: 2,
            text: None,
        }];
        watches.prune(&docs);
        assert_eq!(watches.entries.len(), 1);
        assert_eq!(watches.select(&paths(&["Base"]), false), ["Main"]);
        watches.prune(&[]);
        assert!(watches.entries.is_empty());
    }
}
