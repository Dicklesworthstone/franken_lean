//! Byte positions and the line/column model, exactly as upstream computes them
//! (plan §1.1: wire-visible through diagnostics and LSP).
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin):
//! * `String.Pos.Raw` — src/Init/Prelude.lean:3557-3567: a raw UTF-8 **byte** index;
//! * `Lean.Position` — src/Lean/Data/Position.lean:15-19: 1-based `line`,
//!   0-based `column` counted in **codepoints**;
//! * `FileMap` — Position.lean:39-99: `positions` holds the byte offset of each line
//!   start (first entry always 0; a trailing newline's index appears twice),
//!   `toPosition` binary-searches line starts then counts codepoints, and synthetic
//!   past-the-end positions report the **byte** distance from the last line start —
//!   a deliberate upstream asymmetry, preserved.

/// `String.Pos.Raw`: a byte index into the UTF-8 encoding.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawPos {
    pub byte_idx: usize,
}

impl RawPos {
    pub const fn new(byte_idx: usize) -> RawPos {
        RawPos { byte_idx }
    }
}

/// `Lean.Position`: 1-based line, 0-based codepoint column.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

/// `Lean.FileMap`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileMap {
    source: String,
    /// Byte offsets of line starts; see `FileMap.positions` (Position.lean:41-45).
    positions: Vec<RawPos>,
}

impl FileMap {
    /// `FileMap.ofString` (Position.lean:65-73).
    pub fn of_string(source: impl Into<String>) -> FileMap {
        let source = source.into();
        let mut positions = vec![RawPos::new(0)];
        for (idx, c) in source.char_indices() {
            if c == '\n' {
                positions.push(RawPos::new(idx + c.len_utf8()));
            }
        }
        positions.push(RawPos::new(source.len()));
        // Reproduce the upstream shape exactly: ofString pushes the end index
        // unconditionally, so a trailing newline's start appears twice; a file that
        // does NOT end in a newline records [0, ..., len]. The one divergence to
        // avoid: ofString never double-pushes 0 for empty input — it pushes the end
        // index (0) onto [0], giving [0, 0]. Keep that.
        FileMap { source, positions }
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn positions(&self) -> &[RawPos] {
        &self.positions
    }

    /// `FileMap.getLastLine` (Position.lean:54-55).
    pub fn last_line(&self) -> usize {
        self.positions.len().saturating_sub(1)
    }

    /// `FileMap.getLine` (Position.lean:61-62): 1-based, clamped to the last line.
    fn line_of_index(&self, index: usize) -> usize {
        (index + 1).min(self.last_line())
    }

    /// `FileMap.toPosition` (Position.lean:75-99).
    pub fn to_position(&self, pos: RawPos) -> Position {
        let ps = &self.positions;
        if ps.len() >= 2 && pos <= *ps.last().expect("non-empty") {
            // Binary search: find b with ps[b] <= pos < ps[b+1].
            let (mut b, mut e) = (0usize, ps.len() - 1);
            loop {
                if e == b + 1 {
                    let line_start = ps[b];
                    return Position {
                        line: self.line_of_index(b),
                        column: self.column_from(line_start, pos),
                    };
                }
                let m = (b + e) / 2;
                if pos == ps[m] {
                    return Position {
                        line: self.line_of_index(m),
                        column: 0,
                    };
                } else if pos > ps[m] {
                    b = m;
                } else {
                    e = m;
                }
            }
        } else if ps.is_empty() {
            Position { line: 0, column: 0 }
        } else {
            // Synthetic / past-EOF: byte distance, not codepoints (upstream asymmetry).
            let last = *ps.last().expect("non-empty");
            Position {
                line: self.last_line(),
                column: pos.byte_idx.saturating_sub(last.byte_idx),
            }
        }
    }

    /// `toColumn`: codepoints between the line start and `pos`, stopping at EOF.
    fn column_from(&self, line_start: RawPos, pos: RawPos) -> usize {
        let mut count = 0;
        let mut idx = line_start.byte_idx;
        for c in self.source[line_start.byte_idx..].chars() {
            if idx == pos.byte_idx {
                break;
            }
            idx += c.len_utf8();
            count += 1;
        }
        count
    }

    /// `FileMap.lineStart` (Position.lean:117-124): byte start of a 1-based line.
    pub fn line_start(&self, line: usize) -> RawPos {
        let index = line.saturating_sub(1);
        self.positions
            .get(index)
            .or(self.positions.last())
            .copied()
            .unwrap_or_default()
    }

    /// `FileMap.ofPosition` (Position.lean:101-110): line start plus `column`
    /// codepoints, clamped at EOF.
    pub fn of_position(&self, pos: Position) -> RawPos {
        let start = self.line_start(pos.line);
        let mut idx = start.byte_idx;
        let mut remaining = pos.column;
        for c in self.source[start.byte_idx..].chars() {
            if remaining == 0 {
                break;
            }
            idx += c.len_utf8();
            remaining -= 1;
        }
        RawPos::new(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_starts_match_of_string_semantics() {
        let m = FileMap::of_string("ab\ncd\n");
        // [0, 3, 6, 6]: line starts 0 and 3, newline-at-end start 6, end index 6 again.
        assert_eq!(
            m.positions(),
            &[
                RawPos::new(0),
                RawPos::new(3),
                RawPos::new(6),
                RawPos::new(6)
            ]
        );
        let n = FileMap::of_string("ab");
        assert_eq!(n.positions(), &[RawPos::new(0), RawPos::new(2)]);
        let empty = FileMap::of_string("");
        assert_eq!(empty.positions(), &[RawPos::new(0), RawPos::new(0)]);
    }

    #[test]
    fn to_position_is_one_based_lines_and_codepoint_columns() {
        let m = FileMap::of_string("ab\ncd\n");
        assert_eq!(
            m.to_position(RawPos::new(0)),
            Position { line: 1, column: 0 }
        );
        assert_eq!(
            m.to_position(RawPos::new(1)),
            Position { line: 1, column: 1 }
        );
        assert_eq!(
            m.to_position(RawPos::new(3)),
            Position { line: 2, column: 0 }
        );
        assert_eq!(
            m.to_position(RawPos::new(4)),
            Position { line: 2, column: 1 }
        );
    }

    #[test]
    fn columns_count_codepoints_not_bytes() {
        // 'é' is 2 bytes, '€' is 3 bytes.
        let m = FileMap::of_string("é€x\ny");
        assert_eq!(
            m.to_position(RawPos::new(2)),
            Position { line: 1, column: 1 }
        );
        assert_eq!(
            m.to_position(RawPos::new(5)),
            Position { line: 1, column: 2 }
        );
        assert_eq!(
            m.to_position(RawPos::new(7)),
            Position { line: 2, column: 0 }
        );
        // Round trip through of_position.
        let p = Position { line: 1, column: 2 };
        assert_eq!(m.of_position(p), RawPos::new(5));
        assert_eq!(m.to_position(m.of_position(p)), p);
    }

    #[test]
    fn synthetic_past_eof_positions_use_byte_distance() {
        let m = FileMap::of_string("ab");
        // pos 10 > end (2): line = last line, column = byte distance from last start.
        let p = m.to_position(RawPos::new(10));
        assert_eq!(p.line, m.last_line());
        assert_eq!(p.column, 8);
    }

    #[test]
    fn line_start_clamps_and_of_position_clamps_at_eof() {
        let m = FileMap::of_string("ab\ncd");
        assert_eq!(m.line_start(1), RawPos::new(0));
        assert_eq!(m.line_start(2), RawPos::new(3));
        assert_eq!(m.line_start(99), *m.positions().last().expect("non-empty"));
        assert_eq!(
            m.of_position(Position {
                line: 2,
                column: 99
            }),
            RawPos::new(5),
            "column walk stops at EOF"
        );
    }
}
