//! The pin's `Std.Format` and its renderer (vendored `Init/Data/Format/Basic.lean`), ported
//! so that printed terms break their lines where the pin's do. Widths count characters, as
//! the pin's `String.length` does. Tags are not ported: `Format.pretty` ignores them.

/// `Format.FlattenBehavior`: a group whose lines all break or none do, or one that breaks
/// as few lines as it can (`fill`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Behavior {
    AllOrNone,
    Fill,
}

/// `Std.Format`, without tags.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Format {
    Nil,
    /// A space when flattened, otherwise a newline.
    Line,
    /// Align to the current indentation, even when flattened if forced.
    Align(bool),
    Text(String),
    Nest(i64, Box<Format>),
    Append(Box<Format>, Box<Format>),
    Group(Box<Format>, Behavior),
}

/// Bounds for rendering an already constructed format. Widths count Unicode
/// characters; the output allowance counts UTF-8 bytes, including indentation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FormatRenderLimits {
    /// Worklist visits, insertions and copies, and bytes scanned or emitted.
    /// Lookahead and unsuccessful fill trials spend this same allowance.
    pub max_work: u64,
    pub max_output_bytes: usize,
}

/// A renderer stop returns no partial output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormatRenderError {
    WorkLimit { limit: u64 },
    OutputLimit { limit: usize, requested: usize },
    ArithmeticOverflow,
    AllocationFailure,
}

impl std::fmt::Display for FormatRenderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WorkLimit { limit } => write!(f, "format rendering exceeded {limit} work units"),
            Self::OutputLimit { limit, requested } => write!(
                f,
                "format rendering requested {requested} output bytes, exceeding {limit}"
            ),
            Self::ArithmeticOverflow => f.write_str("format rendering arithmetic overflow"),
            Self::AllocationFailure => f.write_str("format rendering allocation failed"),
        }
    }
}

impl std::error::Error for FormatRenderError {}

type RenderResult<T> = Result<T, FormatRenderError>;

impl Format {
    pub fn text(text: impl Into<String>) -> Format {
        Format::Text(text.into())
    }

    /// `f₁ ++ f₂`.
    pub fn then(self, other: Format) -> Format {
        match (self, other) {
            (Format::Nil, other) => other,
            (this, Format::Nil) => this,
            (this, other) => Format::Append(Box::new(this), Box::new(other)),
        }
    }

    pub fn nest(self, indent: i64) -> Format {
        Format::Nest(indent, Box::new(self))
    }

    pub fn group(self) -> Format {
        Format::Group(Box::new(self), Behavior::AllOrNone)
    }

    pub fn fill(self) -> Format {
        Format::Group(Box::new(self), Behavior::Fill)
    }

    /// `Format.pretty f width`, starting at column 0.
    pub fn pretty(&self, width: usize) -> String {
        self.try_pretty(
            width,
            FormatRenderLimits {
                max_work: u64::MAX,
                max_output_bytes: usize::MAX,
            },
        )
        .expect("native Format rendering failed")
    }

    /// The same layout as [`Self::pretty`], with bounded work and output and
    /// fallible allocation. The input is only borrowed: traversal and fill
    /// trials never clone or recursively destroy its owned format tree.
    pub fn try_pretty(
        &self,
        width: usize,
        limits: FormatRenderLimits,
    ) -> Result<String, FormatRenderError> {
        let mut renderer = Renderer::new(limits);
        renderer.render(self, width)?;
        Ok(renderer.out)
    }
}

#[derive(Clone, Copy, Default, Debug)]
struct SpaceResult {
    found_line: bool,
    found_flattened_hard_line: bool,
    space: usize,
}

struct Meter {
    limits: FormatRenderLimits,
    work: u64,
}

impl Meter {
    fn work(&mut self, amount: u64) -> RenderResult<()> {
        self.work = self
            .work
            .checked_add(amount)
            .filter(|work| *work <= self.limits.max_work)
            .ok_or(FormatRenderError::WorkLimit {
                limit: self.limits.max_work,
            })?;
        Ok(())
    }

    fn size(&mut self, amount: usize) -> RenderResult<()> {
        let amount = u64::try_from(amount).map_err(|_| FormatRenderError::WorkLimit {
            limit: self.limits.max_work,
        })?;
        self.work(amount)
    }

    /// Charge the new worklist entries before admitting their storage.
    fn reserve<T>(&mut self, values: &mut Vec<T>, added: usize) -> RenderResult<()> {
        self.size(added)?;
        values
            .try_reserve(added)
            .map_err(|_| FormatRenderError::AllocationFailure)
    }

    fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> RenderResult<()> {
        self.reserve(values, 1)?;
        values.push(value);
        Ok(())
    }

    fn copy<T: Copy>(&mut self, values: &[T]) -> RenderResult<Vec<T>> {
        let mut copied = Vec::new();
        self.reserve(&mut copied, values.len())?;
        copied.extend_from_slice(values);
        Ok(copied)
    }
}

/// Scan a text only as far as the next hard line. A borrowed suffix keeps a
/// many-line String from being copied afresh at every newline and fill trial.
fn text_prefix<'a>(
    text: &'a str,
    meter: &mut Meter,
) -> RenderResult<(&'a str, Option<&'a str>, usize)> {
    let mut columns = 0_usize;
    for (index, character) in text.char_indices() {
        meter.work(character.len_utf8() as u64)?;
        if character == '\n' {
            return Ok((&text[..index], Some(&text[index + 1..]), columns));
        }
        columns = columns
            .checked_add(1)
            .ok_or(FormatRenderError::ArithmeticOverflow)?;
    }
    Ok((text, None, columns))
}

/// `spaceUptoLine` of a text.
fn text_space(text: &str, flatten: bool, meter: &mut Meter) -> RenderResult<SpaceResult> {
    let (_, rest, space) = text_prefix(text, meter)?;
    let newline = rest.is_some();
    Ok(SpaceResult {
        found_line: newline,
        found_flattened_hard_line: flatten && newline,
        space,
    })
}

/// `spaceUptoLine` accumulated over a sequence as nested `merge`s are: each leaf is measured
/// against the width left after everything before it, and measuring stops at the first line
/// break or once the space exceeds the width.
struct Measure {
    used: usize,
    width: usize,
}

impl Measure {
    fn remaining(&self) -> RenderResult<usize> {
        self.width
            .checked_sub(self.used)
            .ok_or(FormatRenderError::ArithmeticOverflow)
    }

    /// Add one leaf's result; `Some` carries a completed short-circuit result.
    fn add(&mut self, r: SpaceResult) -> RenderResult<Option<SpaceResult>> {
        self.used = self
            .used
            .checked_add(r.space)
            .ok_or(FormatRenderError::ArithmeticOverflow)?;
        if r.found_line {
            return Ok(Some(SpaceResult {
                space: self.used,
                ..r
            }));
        }
        if self.used > self.width {
            return Ok(Some(SpaceResult {
                space: self.used,
                ..SpaceResult::default()
            }));
        }
        Ok(None)
    }

    fn walk(
        &mut self,
        f: &Format,
        flatten: bool,
        m: i128,
        meter: &mut Meter,
    ) -> RenderResult<Option<SpaceResult>> {
        let mut stack = Vec::new();
        meter.push(&mut stack, (f, flatten, m))?;
        while let Some((f, flatten, m)) = stack.pop() {
            meter.work(1)?;
            let r = match f {
                Format::Nest(n, inner) => {
                    let m = m
                        .checked_sub(i128::from(*n))
                        .ok_or(FormatRenderError::ArithmeticOverflow)?;
                    meter.push(&mut stack, (inner, flatten, m))?;
                    continue;
                }
                Format::Group(inner, _) => {
                    meter.push(&mut stack, (inner, true, m))?;
                    continue;
                }
                Format::Append(a, b) => {
                    meter.reserve(&mut stack, 2)?;
                    stack.push((b, flatten, m));
                    stack.push((a, flatten, m));
                    continue;
                }
                Format::Nil => SpaceResult::default(),
                Format::Line if flatten => SpaceResult {
                    space: 1,
                    ..SpaceResult::default()
                },
                Format::Line => SpaceResult {
                    found_line: true,
                    ..SpaceResult::default()
                },
                Format::Align(force) => {
                    let w = i128::try_from(self.remaining()?)
                        .map_err(|_| FormatRenderError::ArithmeticOverflow)?;
                    if flatten && !*force {
                        SpaceResult::default()
                    } else if w < m {
                        let space = m
                            .checked_sub(w)
                            .and_then(|space| usize::try_from(space).ok())
                            .ok_or(FormatRenderError::ArithmeticOverflow)?;
                        SpaceResult {
                            space,
                            ..SpaceResult::default()
                        }
                    } else {
                        SpaceResult {
                            found_line: true,
                            ..SpaceResult::default()
                        }
                    }
                }
                Format::Text(text) => text_space(text, flatten, meter)?,
            };
            if let Some(result) = self.add(r)? {
                return Ok(Some(result));
            }
        }
        Ok(None)
    }
}

/// `spaceUptoLine'` over `groups` (outermost first), at column `col` with width `w`.
fn space_groups<'a: 'g, 'g>(
    groups: impl IntoIterator<Item = &'g WorkGroup<'a>>,
    col: usize,
    w: usize,
    meter: &mut Meter,
) -> RenderResult<SpaceResult> {
    let mut measure = Measure { used: 0, width: w };
    for group in groups {
        meter.work(1)?;
        let flatten = group.fla.should_flatten();
        for item in group.items.iter().rev() {
            meter.work(1)?;
            // Width is a Nat at the pin. Wider intermediates keep the full
            // usize width distinct from signed indentation, without saturation.
            let m = i128::try_from(measure.remaining()?)
                .ok()
                .and_then(|remaining| remaining.checked_add(i128::try_from(col).ok()?))
                .and_then(|total| total.checked_sub(i128::from(item.indent)))
                .ok_or(FormatRenderError::ArithmeticOverflow)?;
            let outcome = match &item.f {
                Item::Format(f) => measure.walk(f, flatten, m, meter)?,
                Item::Rest(text) => measure.add(text_space(text, flatten, meter)?)?,
            };
            if let Some(result) = outcome {
                return Ok(result);
            }
        }
    }
    Ok(SpaceResult {
        space: measure.used,
        ..SpaceResult::default()
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Allowability {
    Allow(bool),
    Disallow,
}

impl Allowability {
    fn should_flatten(self) -> bool {
        self == Allowability::Allow(true)
    }
}

#[derive(Clone, Copy, Debug)]
enum Item<'a> {
    Format(&'a Format),
    /// What follows a hard line break inside a text.
    Rest(&'a str),
}

#[derive(Clone, Copy, Debug)]
struct WorkItem<'a> {
    f: Item<'a>,
    indent: i64,
}

#[derive(Debug)]
struct WorkGroup<'a> {
    fla: Allowability,
    flb: Behavior,
    /// The head is last.
    items: Vec<WorkItem<'a>>,
}

struct Renderer {
    out: String,
    column: usize,
    meter: Meter,
}

impl Renderer {
    fn new(limits: FormatRenderLimits) -> Self {
        Self {
            out: String::new(),
            column: 0,
            meter: Meter { limits, work: 0 },
        }
    }

    fn render(&mut self, format: &Format, width: usize) -> RenderResult<()> {
        let mut items = Vec::new();
        self.meter.push(
            &mut items,
            WorkItem {
                f: Item::Format(format),
                indent: 0,
            },
        )?;
        let mut groups = Vec::new();
        self.meter.push(
            &mut groups,
            WorkGroup {
                fla: Allowability::Disallow,
                flb: Behavior::AllOrNone,
                items,
            },
        )?;
        self.be(width, groups)
    }

    /// Scanning source text and emitting its bytes are separate work. Output
    /// bytes themselves are charged exactly once, before reserving or writing.
    fn reserve_output(&mut self, added: usize) -> RenderResult<()> {
        let requested = self
            .out
            .len()
            .checked_add(added)
            .ok_or(FormatRenderError::ArithmeticOverflow)?;
        if requested > self.meter.limits.max_output_bytes {
            return Err(FormatRenderError::OutputLimit {
                limit: self.meter.limits.max_output_bytes,
                requested,
            });
        }
        self.meter.size(added)?;
        self.out
            .try_reserve(added)
            .map_err(|_| FormatRenderError::AllocationFailure)
    }

    fn push_output(&mut self, text: &str, columns: usize) -> RenderResult<()> {
        let column = self
            .column
            .checked_add(columns)
            .ok_or(FormatRenderError::ArithmeticOverflow)?;
        self.reserve_output(text.len())?;
        self.out.push_str(text);
        self.column = column;
        Ok(())
    }

    fn push_newline(&mut self, indent: i64) -> RenderResult<()> {
        let indent =
            usize::try_from(indent.max(0)).map_err(|_| FormatRenderError::ArithmeticOverflow)?;
        let added = indent
            .checked_add(1)
            .ok_or(FormatRenderError::ArithmeticOverflow)?;
        self.reserve_output(added)?;
        self.out.push('\n');
        for _ in 0..indent {
            self.out.push(' ');
        }
        self.column = indent;
        Ok(())
    }

    fn pad_to(&mut self, column: usize) -> RenderResult<()> {
        let added = column
            .checked_sub(self.column)
            .ok_or(FormatRenderError::ArithmeticOverflow)?;
        self.reserve_output(added)?;
        for _ in 0..added {
            self.out.push(' ');
        }
        self.column = column;
        Ok(())
    }

    fn copy_groups<'a>(&mut self, groups: &[WorkGroup<'a>]) -> RenderResult<Vec<WorkGroup<'a>>> {
        let mut copied = Vec::new();
        self.meter.reserve(&mut copied, groups.len())?;
        for group in groups {
            copied.push(WorkGroup {
                fla: group.fla,
                flb: group.flb,
                items: self.meter.copy(&group.items)?,
            });
        }
        Ok(copied)
    }

    /// `pushGroup`: whether the new group, with everything after it, fits on this line. For
    /// `fill`, only up to its next line break is measured.
    fn push_group<'a>(
        &mut self,
        flb: Behavior,
        items: Vec<WorkItem<'a>>,
        mut gs: Vec<WorkGroup<'a>>,
        w: usize,
    ) -> RenderResult<Vec<WorkGroup<'a>>> {
        let k = self.column;
        let available = w.saturating_sub(k);
        let mut group = WorkGroup {
            fla: Allowability::Allow(flb == Behavior::AllOrNone),
            flb,
            items,
        };
        let r = space_groups(std::iter::once(&group), k, available, &mut self.meter)?;
        let total = if r.space > available || r.found_line {
            r
        } else {
            let r2 = space_groups(gs.iter().rev(), k, available - r.space, &mut self.meter)?;
            SpaceResult {
                space: r
                    .space
                    .checked_add(r2.space)
                    .ok_or(FormatRenderError::ArithmeticOverflow)?,
                ..r2
            }
        };
        group.fla = Allowability::Allow(!r.found_flattened_hard_line && total.space <= available);
        self.meter.push(&mut gs, group)?;
        Ok(gs)
    }

    /// A text item: up to a hard line break it is output; after one, the group's remaining
    /// items are re-measured (`be`'s `text` case).
    fn text<'a>(
        &mut self,
        text: &'a str,
        indent: i64,
        mut gs: Vec<WorkGroup<'a>>,
        w: usize,
    ) -> RenderResult<Vec<WorkGroup<'a>>> {
        let (first, rest, columns) = text_prefix(text, &mut self.meter)?;
        self.push_output(first, columns)?;
        let Some(rest) = rest else {
            return Ok(gs);
        };
        self.push_newline(indent)?;
        let mut current = gs.pop().expect("a current group");
        self.meter.push(
            &mut current.items,
            WorkItem {
                f: Item::Rest(rest),
                indent,
            },
        )?;
        if current.fla == Allowability::Disallow {
            self.meter.push(&mut gs, current)?;
            Ok(gs)
        } else {
            self.push_group(current.flb, current.items, gs, w)
        }
    }

    fn be<'a>(&mut self, w: usize, mut gs: Vec<WorkGroup<'a>>) -> RenderResult<()> {
        loop {
            self.meter.work(1)?;
            let Some(group) = gs.last_mut() else {
                return Ok(());
            };
            let Some(item) = group.items.pop() else {
                gs.pop();
                continue;
            };
            let (fla, flb, indent) = (group.fla, group.flb, item.indent);
            let format = match item.f {
                Item::Rest(text) => {
                    gs = self.text(text, indent, gs, w)?;
                    continue;
                }
                Item::Format(format) => format,
            };
            match format {
                Format::Nil => {}
                Format::Append(a, b) => {
                    self.meter.reserve(&mut group.items, 2)?;
                    group.items.push(WorkItem {
                        f: Item::Format(b),
                        indent,
                    });
                    group.items.push(WorkItem {
                        f: Item::Format(a),
                        indent,
                    });
                }
                Format::Nest(n, inner) => {
                    let indent = indent
                        .checked_add(*n)
                        .ok_or(FormatRenderError::ArithmeticOverflow)?;
                    self.meter.push(
                        &mut group.items,
                        WorkItem {
                            f: Item::Format(inner),
                            indent,
                        },
                    )?;
                }
                Format::Text(text) => gs = self.text(text, indent, gs, w)?,
                Format::Line => match flb {
                    Behavior::AllOrNone if fla.should_flatten() => self.push_output(" ", 1)?,
                    Behavior::AllOrNone => self.push_newline(indent)?,
                    Behavior::Fill => {
                        let current = gs.pop().expect("a current group");
                        // If the preceding fill item fit on its line, try to fit the next one.
                        let trial = if fla.should_flatten() {
                            let items = self.meter.copy(&current.items)?;
                            let groups = self.copy_groups(&gs)?;
                            Some(self.push_group(
                                Behavior::Fill,
                                items,
                                groups,
                                w.saturating_sub(1),
                            )?)
                        } else {
                            None
                        };
                        match trial {
                            Some(trial) if trial.last().is_some_and(|g| g.fla.should_flatten()) => {
                                self.push_output(" ", 1)?;
                                gs = trial;
                            }
                            _ => {
                                self.push_newline(indent)?;
                                gs = self.push_group(Behavior::Fill, current.items, gs, w)?;
                            }
                        }
                    }
                },
                Format::Align(force) => {
                    if !(fla.should_flatten() && !force) {
                        let target = usize::try_from(indent.max(0))
                            .map_err(|_| FormatRenderError::ArithmeticOverflow)?;
                        if self.column < target {
                            self.pad_to(target)?;
                        } else {
                            self.push_newline(indent)?;
                        }
                    }
                }
                Format::Group(inner, behavior) => {
                    let inner = WorkItem {
                        f: Item::Format(inner),
                        indent,
                    };
                    if fla.should_flatten() {
                        self.meter.push(&mut group.items, inner)?;
                    } else {
                        let mut items = Vec::new();
                        self.meter.push(&mut items, inner)?;
                        gs = self.push_group(*behavior, items, gs, w)?;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(s: &str) -> Format {
        Format::text(s)
    }

    fn cat(parts: Vec<Format>) -> Format {
        parts.into_iter().fold(Format::Nil, Format::then)
    }

    /// Each expected string is the pinned v4.32.0's `Format.pretty` of the same `Format`
    /// (measured 2026-10-10 with `#eval IO.println (Std.Format.pretty f w)`).
    #[test]
    fn renders_as_the_pins_format_pretty() {
        let words = |n: usize| {
            let mut f = t("w0");
            for i in 1..n {
                f = f.then(Format::Line).then(t(&format!("w{i}")));
            }
            f
        };
        let line = || Format::Line;
        for (format, width, expected) in [
            (words(5).group(), 120, "w0 w1 w2 w3 w4"),
            (words(5).group(), 8, "w0\nw1\nw2\nw3\nw4"),
            (words(5).fill(), 8, "w0 w1 w2\nw3 w4"),
            (words(5).nest(2).group(), 8, "w0\n  w1\n  w2\n  w3\n  w4"),
            (
                cat(vec![
                    t("a"),
                    line(),
                    cat(vec![t("bbbb"), line(), t("c")]).group(),
                ])
                .nest(2)
                .group(),
                6,
                "a\n  bbbb\n  c",
            ),
            (cat(vec![t("x\ny"), line(), t("z")]).group(), 120, "x\ny z"),
            (
                words(12).nest(2).fill(),
                20,
                "w0 w1 w2 w3 w4 w5 w6\n  w7 w8 w9 w10 w11",
            ),
            (
                cat(vec![
                    t("f"),
                    line(),
                    words(6).nest(2).fill(),
                    line(),
                    t("end"),
                ])
                .nest(2)
                .group(),
                14,
                "f\n  w0 w1 w2 w3\n    w4 w5\n  end",
            ),
            (
                cat(vec![
                    t("ab"),
                    line(),
                    cat(vec![t("cd"), line(), t("ef")]).group(),
                    line(),
                    t("gh"),
                ])
                .fill(),
                6,
                "ab\ncd ef\ngh",
            ),
            (
                cat(vec![t("ab"), Format::Align(false), t("c")]),
                120,
                "ab\nc",
            ),
            (
                cat(vec![t("ab"), Format::Align(true), t("c")]).nest(4),
                120,
                "ab  c",
            ),
        ] {
            assert_eq!(format.pretty(width), expected, "{format:?}");
            assert_eq!(
                format.try_pretty(
                    width,
                    FormatRenderLimits {
                        max_work: 1_000_000,
                        max_output_bytes: expected.len(),
                    },
                ),
                Ok(expected.to_owned()),
                "bounded rendering of the pinned fixture: {format:?}"
            );
        }
    }
}

#[cfg(test)]
mod limits_tests;
