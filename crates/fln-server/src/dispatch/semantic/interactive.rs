//! Structured native observations for the read-only RPC procedures.
//! References retain these provisional presentations, not admission credentials.
use super::{Answer, Query};
use std::ops::Range;

/// A native expression presentation and its semantic annotations. These are
/// provisional observations, never certificates. Ranges address UTF-8 bytes in
/// `text`; atomic subexpressions are disjoint and ordered from left to right.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Code {
    pub text: String,
    pub info: Option<ExpressionInfo>,
    pub subexpressions: Vec<SubexpressionInfo>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExpressionInfo {
    pub type_: Option<String>,
    /// None means the origin pass was unavailable; Some([]) means the actual
    /// expression has no supported source destination, as for a local binder.
    pub definition: Option<Vec<NavigationLocation>>,
    pub type_definition: Option<Vec<NavigationLocation>>,
}

/// A source-validated, immutable LSP LocationLink. Keep only coordinates and
/// URI, not another copy of a potentially large imported source per tag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NavigationLocation {
    uri: String,
    range: [super::super::json::Position; 2],
    selection: [super::super::json::Position; 2],
}

impl NavigationLocation {
    /// Convert original byte ranges once, while their checked source snapshot
    /// is available. Invalid UTF-8/CRLF boundaries cannot become wire locations.
    pub fn new(
        uri: String,
        source: &str,
        range: Range<usize>,
        selection: Range<usize>,
    ) -> Result<Self, &'static str> {
        Self::from_symbols(
            &uri,
            source,
            &[super::DocumentSymbol {
                name: String::new(),
                range,
                selection_range: selection,
            }],
        )?
        .pop()
        .ok_or("navigation source did not produce its location")
    }

    /// Convert a source-ordered batch in one source traversal. This shares the
    /// exact outline boundary validator instead of rescanning a module for each
    /// declaration, which would make normal large files quadratic to present.
    pub fn from_symbols(
        uri: &str,
        source: &str,
        symbols: &[super::DocumentSymbol],
    ) -> Result<Vec<Self>, &'static str> {
        if uri.is_empty()
            || uri.len() > 16 * 1024
            || uri.chars().any(char::is_control)
            || source.len() > 1024 * 1024
            || symbols.len() > 4096
            || symbols
                .len()
                .checked_mul(64 + uri.len())
                .is_none_or(|bytes| bytes > 1024 * 1024)
        {
            return Err("navigation location exceeds its source bounds");
        }
        let coordinates = super::symbols::coordinates(source, symbols, 1024 * 1024)?;
        Ok(coordinates
            .into_iter()
            .map(|[start, end, selection_start, selection_end]| Self {
                uri: uri.to_owned(),
                range: [start, end],
                selection: [selection_start, selection_end],
            })
            .collect())
    }

    pub fn payload_bytes(&self) -> usize {
        64 + self.uri.len()
    }

    pub(in crate::dispatch) fn wire(&self) -> String {
        let range = |points: [super::super::json::Position; 2]| {
            format!(
                "{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}",
                points[0].line, points[0].character, points[1].line, points[1].character
            )
        };
        format!(
            "{{\"targetUri\":{},\"targetRange\":{},\"targetSelectionRange\":{}}}",
            crate::json_string(&self.uri),
            range(self.range),
            range(self.selection),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubexpressionInfo {
    pub range: Range<usize>,
    /// Internal Lean.SubExpr.Pos: root 1, children append base-four coordinates.
    /// The wire representation is the pin's slash path, never a JSON number.
    pub position: u64,
    pub info: ExpressionInfo,
}

impl From<String> for Code {
    fn from(text: String) -> Self {
        Self {
            text,
            info: None,
            subexpressions: Vec::new(),
        }
    }
}
impl From<&str> for Code {
    fn from(text: &str) -> Self {
        text.to_owned().into()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hypothesis {
    pub name: String,
    pub fvar_id: String,
    pub type_: Code,
    pub value: Option<Code>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Goal {
    pub mvar_id: String,
    pub user_name: Option<String>,
    pub hypotheses: Vec<Hypothesis>,
    pub target: Code,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermGoal {
    pub hypotheses: Vec<Hypothesis>,
    pub target: Code,
    pub range: Range<usize>,
}

/// Charge all strings and row overhead before cloning or serializing a result.
/// Many empty rows must not evade the retained-memory or output limits.
pub(in crate::dispatch) fn payload_bytes(answer: &Answer) -> Result<usize, &'static str> {
    use std::collections::BTreeSet;
    fn add(total: &mut usize, bytes: usize) -> Result<(), &'static str> {
        *total = total
            .checked_add(bytes)
            .filter(|n| *n <= 64 * 1024)
            .ok_or("interactive observation exceeds its payload budget")?;
        Ok(())
    }
    fn info(total: &mut usize, info: &ExpressionInfo) -> Result<(), &'static str> {
        add(total, 80)?;
        if let Some(type_) = &info.type_ {
            add(total, type_.len())?;
        }
        for locations in [&info.definition, &info.type_definition]
            .into_iter()
            .flatten()
        {
            if locations.len() > 256 {
                return Err("interactive expression has too many navigation destinations");
            }
            for location in locations {
                add(total, location.payload_bytes())?;
            }
        }
        Ok(())
    }
    fn code(total: &mut usize, code: &Code) -> Result<(), &'static str> {
        add(total, 160)?;
        add(total, code.text.len())?;
        if let Some(root) = &code.info {
            if code.text.is_empty() {
                return Err("interactive expression information has no expression");
            }
            info(total, root)?;
        }
        if code.subexpressions.len() > 4096 {
            return Err("interactive code has too many subexpressions");
        }
        let mut previous_end = 0;
        let mut positions = BTreeSet::new();
        for subexpression in &code.subexpressions {
            let mut root = subexpression.position;
            while root >= 4 {
                root /= 4;
            }
            if subexpression.range.start < previous_end
                || subexpression.range.is_empty()
                || code.text.get(subexpression.range.clone()).is_none()
                || subexpression.position < 4
                || root != 1
                || !positions.insert(subexpression.position)
            {
                return Err("interactive code has invalid subexpression annotations");
            }
            previous_end = subexpression.range.end;
            add(total, 32)?;
            info(total, &subexpression.info)?;
        }
        Ok(())
    }
    fn context(total: &mut usize, hyps: &[Hypothesis], target: &Code) -> Result<(), &'static str> {
        if hyps.len() > 4096 {
            return Err("interactive observation has too many hypotheses");
        }
        code(total, target)?;
        let mut seen = BTreeSet::new();
        for hyp in hyps {
            if hyp.fvar_id.is_empty() || !seen.insert(&hyp.fvar_id) {
                return Err("interactive observation has invalid local identities");
            }
            add(total, 64)?;
            for text in [&hyp.name, &hyp.fvar_id] {
                add(total, text.len())?;
            }
            code(total, &hyp.type_)?;
            if let Some(value) = &hyp.value {
                code(total, value)?;
            }
        }
        Ok(())
    }
    let mut total = 64;
    match answer {
        Answer::InteractiveGoals { goals } => {
            if goals.len() > 256 {
                return Err("interactive observation has too many goals");
            }
            let mut seen = BTreeSet::new();
            for goal in goals {
                if goal.mvar_id.is_empty() || !seen.insert(&goal.mvar_id) {
                    return Err("interactive observation has invalid goal identities");
                }
                add(&mut total, 64)?;
                add(&mut total, goal.mvar_id.len())?;
                if let Some(name) = &goal.user_name {
                    add(&mut total, name.len())?;
                }
                context(&mut total, &goal.hypotheses, &goal.target)?;
            }
        }
        Answer::InteractiveTermGoal(goal) => context(&mut total, &goal.hypotheses, &goal.target)?,
        _ => return Err("interactive provider returned another answer kind"),
    }
    Ok(total)
}

pub(in crate::dispatch) fn validate(
    answer: &Answer,
    query: Query<'_>,
) -> Result<usize, &'static str> {
    let bytes = payload_bytes(answer)?;
    if let Answer::InteractiveTermGoal(goal) = answer {
        if goal.range.start >= goal.range.end || !goal.range.contains(&query.offset) {
            return Err("interactive term range does not contain the requested position");
        }
        for offset in [goal.range.start, goal.range.end] {
            let position = super::position(query.text, offset)?;
            if super::super::json::byte_offset(query.text, position)? != offset {
                return Err("interactive term range has no exact LSP coordinate mapping");
            }
        }
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn navigation_links_preserve_unicode_crlf_and_contained_selection_ranges() {
        let source = "-- 😀\r\ndef «😀» : Nat := 1\r\n";
        let start = source.find("def").unwrap();
        let selection = start + 4..source.find(" :").unwrap();
        let location = NavigationLocation::new(
            "file:///Unicode.lean".into(),
            source,
            start..source.len() - 2,
            selection,
        )
        .unwrap();
        assert!(location.wire().contains(r#""targetSelectionRange":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}}"#));
        for (range, selection) in [
            (start..source.len() - 1, start + 4..start + 5), // CRLF interior.
            (start..source.len() - 2, start + 5..start + 6), // UTF-8 interior.
            (start..start + 3, start + 4..start + 5),
            (start..start, start..start),
        ] {
            assert!(
                NavigationLocation::new("file:///Invalid.lean".into(), source, range, selection)
                    .is_err()
            );
        }
        assert!(
            NavigationLocation::new(
                "file:///bad\n.lean".into(),
                source,
                start..source.len() - 2,
                start..start + 3
            )
            .is_err()
        );
    }

    #[test]
    fn navigation_batches_bound_uri_copies_before_allocating_them() {
        let symbol = super::super::DocumentSymbol {
            name: String::new(),
            range: 0..1,
            selection_range: 0..1,
        };
        assert!(
            NavigationLocation::from_symbols(
                &"x".repeat(16 * 1024),
                "x",
                &vec![symbol.clone(); 64]
            )
            .is_err()
        );
        let locations =
            NavigationLocation::from_symbols("file:///Batch.lean", "x", &vec![symbol; 4096])
                .unwrap();
        assert_eq!(locations.len(), 4096);
    }
}
