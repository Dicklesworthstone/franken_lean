//! Depth-independent `Debug` rendering for the recursive term-plane types.
//!
//! `Formatter::debug_struct`/`debug_tuple` render a nested value by *calling its
//! own* `Debug`, so a tree renders with one stack frame per node: formatting a
//! deep [`crate::expr::Expr`] or [`crate::level::Level`] — in a panic message, a
//! log line, or an `assert_eq!` — aborts the process long before the value is
//! large enough to be interesting (bead franken_lean-canon-stack-safe-drop-6gy).
//!
//! [`FlatDebug`] replaces the nesting with an explicit task stack owned by the
//! caller while reproducing the derived output **byte for byte**, in both `{:?}`
//! and `{:#?}` modes, so the change is invisible to every consumer. Leaves are
//! still rendered through their own `Debug`; that costs one frame per leaf, which
//! is why the payload types reachable from a term (`Name`, `Level`, `KVMap`,
//! `Literal`) are themselves depth-independent.
//!
//! The pretty-mode rules reproduced here are `std`'s: a field or tuple entry per
//! line, four spaces per level, a trailing comma on every entry, and nested
//! multi-line values re-indented to their parent's level.

use std::fmt::{Debug, Formatter, Result, Write};

const INDENT: &str = "    ";

/// A flat, stack-free re-implementation of the `Debug` builders.
///
/// The caller drives it with an explicit worklist: `open_struct`/`field`/`close`
/// and `open_tuple`/`entry`/`close` bracket the composite it is currently
/// emitting, and `leaf` writes a value that renders without descending into this
/// type again.
pub(crate) struct FlatDebug<'a, 'b> {
    formatter: &'a mut Formatter<'b>,
    alternate: bool,
    /// One entry per open composite: whether it has emitted an entry yet, and
    /// whether it is a tuple (parenthesized) rather than a braced struct.
    open: Vec<Frame>,
    /// A field name or tuple entry has been announced and its value has not been
    /// written yet, so the value must not emit a second separator.
    pending: bool,
}

struct Frame {
    filled: bool,
    tuple: bool,
}

impl<'a, 'b> FlatDebug<'a, 'b> {
    pub(crate) fn new(formatter: &'a mut Formatter<'b>) -> FlatDebug<'a, 'b> {
        let alternate = formatter.alternate();
        FlatDebug {
            formatter,
            alternate,
            open: Vec::new(),
            pending: false,
        }
    }

    fn indent(&mut self) -> Result {
        for _ in 0..self.open.len() {
            self.formatter.write_str(INDENT)?;
        }
        Ok(())
    }

    /// Emit the separator that precedes the next entry of the innermost
    /// composite: `", "` in plain mode, a newline plus indentation in pretty mode
    /// (where the opening delimiter is followed by a newline as well).
    fn separate(&mut self) -> Result {
        let Some(frame) = self.open.last_mut() else {
            return Ok(());
        };
        let first = !frame.filled;
        let tuple = frame.tuple;
        frame.filled = true;
        if self.alternate {
            if first {
                self.formatter.write_char('\n')?;
            }
            self.indent()
        } else if first {
            if tuple {
                Ok(())
            } else {
                self.formatter.write_char(' ')
            }
        } else {
            self.formatter.write_str(", ")
        }
    }

    /// `Name {` — a braced composite with named fields.
    pub(crate) fn open_struct(&mut self, name: &str) -> Result {
        self.separate_for_open()?;
        self.formatter.write_str(name)?;
        self.formatter.write_str(" {")?;
        self.open.push(Frame {
            filled: false,
            tuple: false,
        });
        Ok(())
    }

    /// `Name(` — a tuple composite.
    pub(crate) fn open_tuple(&mut self, name: &str) -> Result {
        self.separate_for_open()?;
        self.formatter.write_str(name)?;
        self.formatter.write_char('(')?;
        self.open.push(Frame {
            filled: false,
            tuple: true,
        });
        Ok(())
    }

    /// A composite with no payload renders as its bare name (`Zero`), matching a
    /// derived unit variant.
    pub(crate) fn unit(&mut self, name: &str) -> Result {
        self.separate_for_open()?;
        self.formatter.write_str(name)
    }

    /// A composite opened as the value of a pending field or entry has already
    /// been separated by [`FlatDebug::field`]/[`FlatDebug::entry`]; one opened
    /// directly as an entry of its parent still needs the separator.
    fn separate_for_open(&mut self) -> Result {
        if self.pending {
            self.pending = false;
            Ok(())
        } else {
            self.separate()
        }
    }

    /// `name: ` — announce the next struct field; the value follows.
    pub(crate) fn field(&mut self, name: &str) -> Result {
        self.separate()?;
        self.formatter.write_str(name)?;
        self.formatter.write_str(": ")?;
        self.pending = true;
        Ok(())
    }

    /// Announce the next tuple entry; the value follows.
    pub(crate) fn entry(&mut self) -> Result {
        self.separate()?;
        self.pending = true;
        Ok(())
    }

    /// Write a value that renders without re-entering the walked type. Its own
    /// multi-line pretty output is re-indented to the current level, exactly as
    /// `std`'s builders indent a nested value.
    pub(crate) fn leaf(&mut self, value: &dyn Debug) -> Result {
        self.separate_for_open()?;
        if !self.alternate {
            return write!(self.formatter, "{value:?}");
        }
        let mut rendered = String::new();
        write!(&mut rendered, "{value:#?}")?;
        let depth = self.open.len();
        let mut lines = rendered.split('\n');
        if let Some(first) = lines.next() {
            self.formatter.write_str(first)?;
        }
        for line in lines {
            self.formatter.write_char('\n')?;
            for _ in 0..depth {
                self.formatter.write_str(INDENT)?;
            }
            self.formatter.write_str(line)?;
        }
        Ok(())
    }

    /// Close the innermost composite: `}` or `)`, with the pretty-mode trailing
    /// comma and closing indentation.
    pub(crate) fn close(&mut self) -> Result {
        let Some(frame) = self.open.pop() else {
            return Ok(());
        };
        if self.alternate {
            if frame.filled {
                self.formatter.write_str(",\n")?;
                self.indent()?;
            }
        } else if frame.filled && !frame.tuple {
            self.formatter.write_char(' ')?;
        }
        self.formatter
            .write_char(if frame.tuple { ')' } else { '}' })
    }
}
