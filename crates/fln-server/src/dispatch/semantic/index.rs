//! Immutable native editor annotations, bound to one workspace revision.
//!
//! This index supplies no elaboration or proof authority. Native providers record
//! resolved answers; source spellings are never used to invent bindings. The
//! dispatch adapter renews the revision on checking and dependency invalidation,
//! including same-version saves, close/reopen and watched-file changes.

use super::{Answer, Query, QueryKind};
use crate::dispatch::OpenDocumentSource;
use std::ops::Range;
use std::sync::Arc;

#[cfg(test)]
mod tests;

const MAX_ANNOTATIONS: usize = 4096;
const MAX_PAYLOAD_BYTES: usize = 8 * 1024 * 1024;
const MAX_BUILD_WORK: usize = 64 * 1024 * 1024;
const MAX_URI_BYTES: usize = 16 * 1024;

/// Process-local cache identity, not a serialized ID or admission credential.
/// Only the dispatcher creates revisions. Retained clones prevent allocation
/// reuse from making an old index current; there is no wrapping counter.
#[derive(Debug, Clone)]
pub struct Revision(Arc<()>);

impl Revision {
    pub(in crate::dispatch) fn new() -> Self {
        Self(Arc::new(()))
    }
}

impl PartialEq for Revision {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for Revision {}

/// The source interval in which a native answer applies. Endpoints are included
/// for editor cursors; an empty interval denotes exactly one position. Narrower
/// intervals take precedence; equally narrow records use the later input row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    pub selection: Range<usize>,
    pub answer: Answer,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexRefusal {
    ContentModified,
    InvalidAnnotation,
    ResourceLimit,
}

impl std::fmt::Display for IndexRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::ContentModified => "semantic index belongs to a superseded editor world",
            Self::InvalidAnnotation => "native semantic annotation is invalid for this source",
            Self::ResourceLimit => "native semantic index exceeded its resource budget",
        })
    }
}
impl std::error::Error for IndexRefusal {}

#[derive(Debug)]
struct Entry {
    annotation: Annotation,
    order: usize,
}

/// An immutable interval index. It retains no copy of the queried source.
/// Definition answers retain their bounded target snapshots because the current
/// wire adapter requires those exact bytes to validate navigation coordinates.
#[derive(Debug)]
pub struct SemanticIndex {
    revision: Revision,
    uri: String,
    version: i64,
    source_len: usize,
    entries: Vec<Entry>,
    max_end: Vec<usize>,
}

fn kind(answer: &Answer) -> QueryKind {
    match answer {
        Answer::Goals { .. } => QueryKind::Goals,
        Answer::Hover { .. } => QueryKind::Hover,
        Answer::Definition { .. } => QueryKind::Definition,
        Answer::Completion { .. } => QueryKind::Completion,
    }
}

fn add(total: &mut usize, amount: usize, limit: usize) -> Result<(), IndexRefusal> {
    *total = total
        .checked_add(amount)
        .filter(|value| *value <= limit)
        .ok_or(IndexRefusal::ResourceLimit)?;
    Ok(())
}

fn payload_bytes(answer: &Answer) -> Result<usize, IndexRefusal> {
    let mut total = 0;
    match answer {
        Answer::Goals { goals } => {
            if goals.len() > super::MAX_GOALS {
                return Err(IndexRefusal::ResourceLimit);
            }
            for goal in goals {
                add(&mut total, goal.len(), MAX_PAYLOAD_BYTES)?;
            }
        }
        Answer::Hover { contents, .. } => {
            add(&mut total, contents.len(), MAX_PAYLOAD_BYTES)?;
        }
        Answer::Definition { uri, source, .. } => {
            add(&mut total, uri.len(), MAX_PAYLOAD_BYTES)?;
            add(&mut total, source.len(), MAX_PAYLOAD_BYTES)?;
        }
        Answer::Completion { items, .. } => {
            if items.len() > 256 {
                return Err(IndexRefusal::ResourceLimit);
            }
            for item in items {
                add(&mut total, item.label.len(), MAX_PAYLOAD_BYTES)?;
                add(&mut total, item.replacement.len(), MAX_PAYLOAD_BYTES)?;
            }
        }
    }
    Ok(total)
}

fn exact_range(text: &str, range: &Range<usize>) -> Result<(), IndexRefusal> {
    if range.start > range.end {
        return Err(IndexRefusal::InvalidAnnotation);
    }
    for offset in [range.start, range.end] {
        let position = super::position(text, offset)
            .map_err(|_| IndexRefusal::InvalidAnnotation)?;
        let round_trip = super::super::json::byte_offset(text, position)
            .map_err(|_| IndexRefusal::InvalidAnnotation)?;
        if round_trip != offset {
            return Err(IndexRefusal::InvalidAnnotation);
        }
    }
    Ok(())
}

impl SemanticIndex {
    /// Validate the entire native product before exposing an index. A malformed
    /// later row never produces a partial index or a successful empty answer.
    pub fn new(
        query: Query<'_>,
        revision: &Revision,
        annotations: Vec<Annotation>,
    ) -> Result<Self, IndexRefusal> {
        if annotations.len() > MAX_ANNOTATIONS || query.uri.len() > MAX_URI_BYTES {
            return Err(IndexRefusal::ResourceLimit);
        }
        if query.uri.is_empty()
            || query.uri.chars().any(char::is_control)
            || !query.text.is_char_boundary(query.offset)
        {
            return Err(IndexRefusal::InvalidAnnotation);
        }
        let mut payload = query.uri.len();
        let mut work = 0;
        let mut entries = Vec::with_capacity(annotations.len());
        for (order, annotation) in annotations.into_iter().enumerate() {
            let bytes = payload_bytes(&annotation.answer)?;
            add(&mut payload, bytes, MAX_PAYLOAD_BYTES)?;
            // Charge before coordinate scans, result cloning or wire validation.
            // This conservatively covers both source/target round trips and JSON
            // expansion, so a large document times many annotations is bounded.
            let cost = query.text.len().checked_add(bytes)
                .and_then(|size| size.checked_mul(16))
                .ok_or(IndexRefusal::ResourceLimit)?;
            add(&mut work, cost, MAX_BUILD_WORK)?;
            exact_range(query.text, &annotation.selection)?;
            match &annotation.answer {
                Answer::Hover { range, .. } | Answer::Completion { range, .. } => {
                    if range.start > annotation.selection.start
                        || range.end < annotation.selection.end
                    {
                        return Err(IndexRefusal::InvalidAnnotation);
                    }
                    exact_range(query.text, range)?;
                }
                Answer::Goals { .. } | Answer::Definition { .. } => {}
            }
            let sample = Query {
                kind: kind(&annotation.answer),
                offset: annotation.selection.start,
                ..query
            };
            super::result_json(annotation.answer.clone(), sample)
                .map_err(|_| IndexRefusal::InvalidAnnotation)?;
            entries.push(Entry { annotation, order });
        }
        entries.sort_by_key(|entry| (entry.annotation.selection.start, entry.order));
        let mut maximum = 0;
        let max_end = entries.iter().map(|entry| {
            maximum = maximum.max(entry.annotation.selection.end);
            maximum
        }).collect();
        Ok(Self {
            revision: revision.clone(),
            uri: query.uri.to_owned(),
            version: query.version,
            source_len: query.text.len(),
            entries,
            max_end,
        })
    }

    /// Use only with the revision and accepted query supplied together by
    /// `WorkspaceChecker::query_with_revision`. Re-labeling an old native product
    /// with a new revision is not valid cache reuse. Open target snapshots are
    /// checked again before returning a definition answer.
    pub fn query(
        &self,
        query: Query<'_>,
        revision: &Revision,
        documents: &[OpenDocumentSource<'_>],
    ) -> Result<Option<Answer>, IndexRefusal> {
        if &self.revision != revision
            || self.uri != query.uri
            || self.version != query.version
            || self.source_len != query.text.len()
        {
            return Err(IndexRefusal::ContentModified);
        }
        if !query.text.is_char_boundary(query.offset) {
            return Err(IndexRefusal::InvalidAnnotation);
        }
        let mut end = self.entries.partition_point(|entry| {
            entry.annotation.selection.start <= query.offset
        });
        let mut best: Option<&Entry> = None;
        while end > 0 {
            if self.max_end[end - 1] < query.offset {
                break;
            }
            end -= 1;
            let entry = &self.entries[end];
            let annotation = &entry.annotation;
            if annotation.selection.end < query.offset || kind(&annotation.answer) != query.kind {
                continue;
            }
            let width = annotation.selection.end - annotation.selection.start;
            if best.is_none_or(|previous| {
                let old_width = previous.annotation.selection.end - previous.annotation.selection.start;
                width < old_width || (width == old_width && entry.order > previous.order)
            }) {
                best = Some(entry);
            }
        }
        let Some(entry) = best else { return Ok(None); };
        super::validate_target_source(&entry.annotation.answer, documents)
            .map_err(|_| IndexRefusal::ContentModified)?;
        let answer = entry.annotation.answer.clone();
        // Validate against the actual cursor, not just the construction sample.
        super::result_json(answer.clone(), query)
            .map_err(|_| IndexRefusal::InvalidAnnotation)?;
        Ok(Some(answer))
    }
}
