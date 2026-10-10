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
        let mut renderer = Renderer {
            out: String::new(),
            column: 0,
        };
        renderer.be(
            width,
            vec![WorkGroup {
                fla: Allowability::Disallow,
                flb: Behavior::AllOrNone,
                items: vec![WorkItem {
                    f: Item::Format(self),
                    indent: 0,
                }],
            }],
        );
        renderer.out
    }
}

#[derive(Clone, Copy, Default, Debug)]
struct SpaceResult {
    found_line: bool,
    found_flattened_hard_line: bool,
    space: usize,
}

/// `spaceUptoLine` of a text.
fn text_space(text: &str, flatten: bool) -> SpaceResult {
    let newline = text.contains('\n');
    SpaceResult {
        found_line: newline,
        found_flattened_hard_line: flatten && newline,
        space: text.chars().take_while(|c| *c != '\n').count(),
    }
}

/// `spaceUptoLine` accumulated over a sequence as nested `merge`s are: each leaf is measured
/// against the width left after everything before it, and measuring stops at the first line
/// break or once the space exceeds the width.
struct Measure {
    used: usize,
    width: usize,
}

impl Measure {
    fn remaining(&self) -> usize {
        self.width - self.used
    }

    /// Add one leaf's result; `Err` carries the final result once measuring stops.
    fn add(&mut self, r: SpaceResult) -> Result<(), SpaceResult> {
        if r.found_line {
            return Err(SpaceResult {
                space: self.used + r.space,
                ..r
            });
        }
        self.used += r.space;
        if self.used > self.width {
            return Err(SpaceResult {
                space: self.used,
                ..SpaceResult::default()
            });
        }
        Ok(())
    }

    fn walk(&mut self, f: &Format, flatten: bool, m: i64) -> Result<(), SpaceResult> {
        let mut stack = vec![(f, flatten, m)];
        while let Some((f, flatten, m)) = stack.pop() {
            let r = match f {
                Format::Nest(n, inner) => {
                    stack.push((inner, flatten, m - n));
                    continue;
                }
                Format::Group(inner, _) => {
                    stack.push((inner, true, m));
                    continue;
                }
                Format::Append(a, b) => {
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
                    let w = i64::try_from(self.remaining()).unwrap_or(i64::MAX);
                    if flatten && !*force {
                        SpaceResult::default()
                    } else if w < m {
                        SpaceResult {
                            space: usize::try_from(m - w).unwrap_or(0),
                            ..SpaceResult::default()
                        }
                    } else {
                        SpaceResult {
                            found_line: true,
                            ..SpaceResult::default()
                        }
                    }
                }
                Format::Text(text) => text_space(text, flatten),
            };
            self.add(r)?;
        }
        Ok(())
    }
}

/// `spaceUptoLine'` over `groups` (outermost first), at column `col` with width `w`.
fn space_groups(groups: &[&WorkGroup<'_>], col: usize, w: usize) -> SpaceResult {
    let mut measure = Measure { used: 0, width: w };
    for group in groups {
        let flatten = group.fla.should_flatten();
        for item in group.items.iter().rev() {
            let m = i64::try_from(measure.remaining() + col).unwrap_or(i64::MAX) - item.indent;
            let outcome = match &item.f {
                Item::Format(f) => measure.walk(f, flatten, m),
                Item::Rest(text) => measure.add(text_space(text, flatten)),
            };
            if let Err(result) = outcome {
                return result;
            }
        }
    }
    SpaceResult {
        space: measure.used,
        ..SpaceResult::default()
    }
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

#[derive(Clone, Debug)]
enum Item<'a> {
    Format(&'a Format),
    /// What follows a hard line break inside a text.
    Rest(String),
}

#[derive(Clone, Debug)]
struct WorkItem<'a> {
    f: Item<'a>,
    indent: i64,
}

#[derive(Clone, Debug)]
struct WorkGroup<'a> {
    fla: Allowability,
    flb: Behavior,
    /// The head is last.
    items: Vec<WorkItem<'a>>,
}

struct Renderer {
    out: String,
    column: usize,
}

impl Renderer {
    fn push_output(&mut self, text: &str) {
        self.out.push_str(text);
        self.column += text.chars().count();
    }

    fn push_newline(&mut self, indent: i64) {
        let indent = usize::try_from(indent).unwrap_or(0);
        self.out.push('\n');
        self.out.extend(std::iter::repeat_n(' ', indent));
        self.column = indent;
    }

    /// `pushGroup`: whether the new group, with everything after it, fits on this line. For
    /// `fill`, only up to its next line break is measured.
    fn push_group<'a>(
        &self,
        flb: Behavior,
        items: Vec<WorkItem<'a>>,
        mut gs: Vec<WorkGroup<'a>>,
        w: usize,
    ) -> Vec<WorkGroup<'a>> {
        let k = self.column;
        let available = w.saturating_sub(k);
        let mut group = WorkGroup {
            fla: Allowability::Allow(flb == Behavior::AllOrNone),
            flb,
            items,
        };
        let r = space_groups(&[&group], k, available);
        let total = if r.space > available || r.found_line {
            r
        } else {
            let rest: Vec<&WorkGroup<'_>> = gs.iter().rev().collect();
            let r2 = space_groups(&rest, k, available - r.space);
            SpaceResult {
                space: r.space + r2.space,
                ..r2
            }
        };
        group.fla = Allowability::Allow(!r.found_flattened_hard_line && total.space <= available);
        gs.push(group);
        gs
    }

    /// A text item: up to a hard line break it is output; after one, the group's remaining
    /// items are re-measured (`be`'s `text` case).
    fn text<'a>(
        &mut self,
        text: &str,
        indent: i64,
        mut gs: Vec<WorkGroup<'a>>,
        w: usize,
    ) -> Vec<WorkGroup<'a>> {
        let Some((first, rest)) = text.split_once('\n') else {
            self.push_output(text);
            return gs;
        };
        self.push_output(first);
        self.push_newline(indent);
        let mut current = gs.pop().expect("a current group");
        current.items.push(WorkItem {
            f: Item::Rest(rest.to_owned()),
            indent,
        });
        if current.fla == Allowability::Disallow {
            gs.push(current);
            gs
        } else {
            self.push_group(current.flb, current.items, gs, w)
        }
    }

    fn be<'a>(&mut self, w: usize, mut gs: Vec<WorkGroup<'a>>) {
        loop {
            let Some(group) = gs.last_mut() else {
                return;
            };
            let Some(item) = group.items.pop() else {
                gs.pop();
                continue;
            };
            let (fla, flb, indent) = (group.fla, group.flb, item.indent);
            let format = match item.f {
                Item::Rest(text) => {
                    gs = self.text(&text, indent, gs, w);
                    continue;
                }
                Item::Format(format) => format,
            };
            match format {
                Format::Nil => {}
                Format::Append(a, b) => {
                    group.items.push(WorkItem {
                        f: Item::Format(b),
                        indent,
                    });
                    group.items.push(WorkItem {
                        f: Item::Format(a),
                        indent,
                    });
                }
                Format::Nest(n, inner) => group.items.push(WorkItem {
                    f: Item::Format(inner),
                    indent: indent + n,
                }),
                Format::Text(text) => gs = self.text(text, indent, gs, w),
                Format::Line => match flb {
                    Behavior::AllOrNone if fla.should_flatten() => self.push_output(" "),
                    Behavior::AllOrNone => self.push_newline(indent),
                    Behavior::Fill => {
                        let current = gs.pop().expect("a current group");
                        // If the preceding fill item fit on its line, try to fit the next one.
                        let trial = fla.should_flatten().then(|| {
                            self.push_group(
                                Behavior::Fill,
                                current.items.clone(),
                                gs.clone(),
                                w.saturating_sub(1),
                            )
                        });
                        match trial {
                            Some(trial) if trial.last().is_some_and(|g| g.fla.should_flatten()) => {
                                self.push_output(" ");
                                gs = trial;
                            }
                            _ => {
                                self.push_newline(indent);
                                gs = self.push_group(Behavior::Fill, current.items, gs, w);
                            }
                        }
                    }
                },
                Format::Align(force) => {
                    if !(fla.should_flatten() && !force) {
                        let target = usize::try_from(indent).unwrap_or(0);
                        if self.column < target {
                            let pad = " ".repeat(target - self.column);
                            self.push_output(&pad);
                        } else {
                            self.push_newline(indent);
                        }
                    }
                }
                Format::Group(inner, behavior) => {
                    let inner = WorkItem {
                        f: Item::Format(inner),
                        indent,
                    };
                    if fla.should_flatten() {
                        group.items.push(inner);
                    } else {
                        gs = self.push_group(*behavior, vec![inner], gs, w);
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
        }
    }
}
