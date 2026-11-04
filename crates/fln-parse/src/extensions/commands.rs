//! A command operand parsed from its original bounded source interval.
//! Reentry shares the descriptor budget; child spans return to the enclosing
//! normalized source before any macro receives the resulting tree.
use super::*;

impl Run<'_> {
    pub(super) fn command_operand(&self, at: usize, end: usize) -> Option<Syntax> {
        if at >= end {
            return None;
        }
        categories::bounded(|| {
            // Bound the native parser's input before reentry, including a
            // builtin command whose syntax contains no descriptor nodes.
            for _ in at..end {
                if !categories::tick() {
                    return None;
                }
            }
            // Full leaf spans preserve exactly the trivia owned by this
            // operand. The wrapper's delimiters keep their own trivia.
            let start = self.leaves.leaf(at).ok()?.info().full_span()?.start();
            let stop = self.leaves.leaf(end - 1).ok()?.info().full_span()?.end();
            let span = ByteSpan::new(start, stop)?;
            let source = self.view.normalized().span_str(span)?;
            let mut syntax = crate::parse_source_command(source.as_bytes()).ok()?.syntax;

            let shift_pos = |pos: BytePos| {
                let shifted = pos.0.checked_add(start.0)?;
                (shifted <= stop.0).then_some(BytePos(shifted))
            };
            let shift_span =
                |span: ByteSpan| ByteSpan::new(shift_pos(span.start())?, shift_pos(span.end())?);
            let shift_info = |info: &mut SourceInfo| -> Option<()> {
                match info {
                    SourceInfo::Original {
                        leading,
                        pos,
                        trailing,
                        end_pos,
                    } => {
                        *leading = shift_span(*leading)?;
                        *pos = shift_pos(*pos)?;
                        *trailing = shift_span(*trailing)?;
                        *end_pos = shift_pos(*end_pos)?;
                    }
                    SourceInfo::Synthetic { pos, end_pos, .. } => {
                        *pos = shift_pos(*pos)?;
                        *end_pos = shift_pos(*end_pos)?;
                    }
                    SourceInfo::None => {}
                }
                Some(())
            };
            let mut pending = vec![&mut syntax];
            while let Some(node) = pending.pop() {
                if !categories::tick() {
                    return None;
                }
                match node {
                    Syntax::Node { info, args, .. } => {
                        shift_info(info)?;
                        pending.extend(args.iter_mut());
                    }
                    Syntax::Atom { info, .. } => shift_info(info)?,
                    Syntax::Ident { info, raw_val, .. } => {
                        shift_info(info)?;
                        if let Some(source) = raw_val.source_span() {
                            *raw_val = shift_span(source)?.into();
                        }
                    }
                    Syntax::Missing => {}
                }
            }
            Some(syntax)
        })
    }
}

#[cfg(test)]
mod tests;
