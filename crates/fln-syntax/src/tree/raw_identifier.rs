//! The exact `Substring.Raw` backing retained by a syntax identifier.
//!
//! Parser identifiers borrow the surrounding source by span. Quotations may
//! instead carry a different immutable string; its offsets are relative to
//! that string, never relocated into the caller's source.

use crate::source::{ByteSpan, SourceText};
use std::{fmt, sync::Arc};

#[derive(Clone, PartialEq, Eq)]
pub enum RawIdentifier {
    Source(ByteSpan),
    Owned(Arc<OwnedIdentifier>),
}

/// An owned backing and a validated UTF-8 substring within it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnedIdentifier {
    backing: Arc<str>,
    span: ByteSpan,
}

impl RawIdentifier {
    pub fn owned(backing: Arc<str>, span: ByteSpan) -> Option<Self> {
        backing.get(span.start().0..span.end().0)?;
        Some(Self::Owned(Arc::new(OwnedIdentifier { backing, span })))
    }

    pub fn span(&self) -> ByteSpan {
        match self {
            Self::Source(span) => *span,
            Self::Owned(owned) => owned.span,
        }
    }

    /// A source-relative span only when the caller's source owns the bytes.
    pub fn source_span(&self) -> Option<ByteSpan> {
        match self {
            Self::Source(span) => Some(*span),
            Self::Owned(_) => None,
        }
    }

    pub fn owned_backing(&self) -> Option<&str> {
        match self {
            Self::Source(_) => None,
            Self::Owned(owned) => Some(&owned.backing),
        }
    }

    pub fn backing<'a>(&'a self, source: &'a SourceText) -> &'a str {
        match self {
            Self::Source(_) => source.as_str(),
            Self::Owned(owned) => &owned.backing,
        }
    }

    pub fn text<'a>(&'a self, source: &'a SourceText) -> Option<&'a str> {
        let span = self.span();
        self.backing(source).get(span.start().0..span.end().0)
    }
}

impl From<ByteSpan> for RawIdentifier {
    fn from(span: ByteSpan) -> Self {
        Self::Source(span)
    }
}

impl Default for RawIdentifier {
    fn default() -> Self {
        Self::Source(ByteSpan::default())
    }
}

impl fmt::Debug for RawIdentifier {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Keep the ordinary parser tree's diagnostic representation stable.
            Self::Source(span) => span.fmt(formatter),
            Self::Owned(owned) => formatter.debug_tuple("Owned").field(owned).finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::BytePos;

    #[test]
    fn owned_identifier_keeps_backing_and_validates_substring_boundaries() {
        let source = SourceText::from_utf8(b"caller").unwrap();
        let span = ByteSpan::new(BytePos(2), BytePos(4)).unwrap();
        let owned = RawIdentifier::owned(Arc::from("aβz"), span);
        assert!(owned.is_none(), "the start lies inside a UTF-8 scalar");
        let span = ByteSpan::new(BytePos(1), BytePos(3)).unwrap();
        let owned = RawIdentifier::owned(Arc::from("aβz"), span).unwrap();
        assert_eq!(owned.backing(&source), "aβz");
        assert_eq!(owned.text(&source), Some("β"));
        assert_eq!(owned.span(), span);
        assert_eq!(owned.source_span(), None);
        assert!(
            RawIdentifier::owned(
                Arc::from("short"),
                ByteSpan::new(BytePos(0), BytePos(6)).unwrap(),
            )
            .is_none()
        );
        let borrowed = RawIdentifier::from(span);
        assert_eq!(borrowed.text(&source), Some("al"));
        assert_eq!(borrowed.source_span(), Some(span));
    }
}
