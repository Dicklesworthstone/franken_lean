//! Zero-recursion heap-stack execution engine for [`BuiltinInterpreter`].
//!
//! Runs every [`ParserOp`] combinator on an explicit heap `Vec<Frame>` instead
//! of the native Rust call stack, so deep syntax chains (e.g. 3,000 nested
//! `forall` binders on a 96 KiB thread stack) never overflow the host stack
//! while non-tail recursion still enforces `st.max_depth` (`FL-INV-07`).

use super::*;
use std::rc::Rc;

const MAX_VM_FRAMES: usize = 524_288;

#[derive(Clone)]
enum VmInterp<'a> {
    Borrowed(&'a BuiltinInterpreter),
    Owned(Rc<BuiltinInterpreter>),
}

impl<'a> VmInterp<'a> {
    #[inline]
    fn get(&self) -> &BuiltinInterpreter {
        match self {
            Self::Borrowed(interp) => interp,
            Self::Owned(interp) => interp.as_ref(),
        }
    }
}

enum SepByPhase {
    WaitElem { sz: usize, pos: usize, p_opt: bool },
    WaitSep { sz: usize, pos: usize },
}

enum OrElseCorePhase {
    Lhs,
    RhsAfterErr(InterpError),
    RhsAfterAntiquot(VmNode, usize),
}

enum OrElseChainPhase {
    First,
    AltAfterErr {
        next_idx: usize,
        err1: InterpError,
    },
    AltAfterAntiquot {
        next_idx: usize,
        p_back: VmNode,
        p_pos: usize,
    },
}

enum SplicePhase {
    WaitBody,
    WaitSuffix { ini_sz: usize, ini_pos: usize },
}

enum RecoverPhase {
    WaitParser,
    WaitHandler {
        msg: InterpError,
        saved_pos: usize,
        saved_stack_len: usize,
        saved_lhs: u32,
    },
}

enum PrattAntiPhase {
    WaitAntiquot,
    WaitLeading(InterpError),
}

struct LongestMatchPrev {
    prev_prio: u32,
    prev_score: (usize, u8, u32),
    prev_err: Option<InterpError>,
    prev_pos: usize,
    prev_sz: usize,
    prev_lhs: u32,
    cur_prio: u32,
}

enum Frame<'i, 's> {
    PopDepth,
    Seq {
        steps: Arc<ParserOp>,
        next_idx: usize,
    },
    Node {
        kind: Name,
        ini_sz: usize,
    },
    TrailingNodeAux {
        kind: Name,
        ini_sz: usize,
    },
    Atomic {
        ini_pos: usize,
    },
    Optional {
        ini_sz: usize,
        ini_pos: usize,
    },
    Many {
        inner: Arc<ParserOp>,
        outer_ini_sz: usize,
        iter_ini_sz: usize,
        iter_ini_pos: usize,
        first_of_many1: bool,
        unbox: bool,
    },
    SepBy {
        elem: Arc<ParserOp>,
        sep: Arc<ParserOp>,
        allow_trailing: bool,
        outer_ini_sz: usize,
        phase: SepByPhase,
    },
    Lookahead {
        ini_sz: usize,
        ini_pos: usize,
    },
    NotFollowedBy {
        ini_sz: usize,
        ini_pos: usize,
        msg: String,
    },
    WithCache {
        key: ParserCacheKey,
        init_raw_sz: usize,
        old_drop: usize,
    },
    WithResetCache {
        old_drop: usize,
        saved_cache: HashMap<ParserCacheKey, ParserCacheEntry>,
    },
    WithOpenRestore {
        prev_interp: VmInterp<'i>,
        old_drop: usize,
        saved_cache: HashMap<ParserCacheKey, ParserCacheEntry>,
        saved_ctx: Option<(
            &'s BuiltinInterpreter,
            &'s crate::extensions::FileGrammar,
            crate::extensions::FileScope,
        )>,
    },
    OrElseChain {
        alts: Arc<ParserOp>,
        ini_sz: usize,
        ini_pos: usize,
        phase: OrElseChainPhase,
    },
    OrElseCore {
        rhs: Arc<ParserOp>,
        behavior: OrElseAntiquotBehavior,
        ini_sz: usize,
        ini_pos: usize,
        phase: OrElseCorePhase,
    },
    TokenWithAntiquot,
    TokenAntiquotSuffix {
        ini_sz: usize,
        ini_pos: usize,
    },
    WithAntiquotSuffixSplice {
        kind: Name,
        suffix: Arc<ParserOp>,
        phase: SplicePhase,
    },
    SetExpected {
        expected: Vec<String>,
    },
    RestoreSavedPos {
        saved: Option<usize>,
    },
    RestoreCtx {
        saved: CacheableCtx,
    },
    RestoreVerso {
        docs: bool,
        module_docs: bool,
    },
    Recover {
        handler: Arc<ParserOp>,
        phase: RecoverPhase,
    },
    InterpolatedStr {
        inner: Arc<ParserOp>,
        stack_sz: usize,
        saved_pos_ctx: Option<usize>,
    },
    CategoryFinish {
        key: ParserCacheKey,
        init_raw_sz: usize,
        old_drop: usize,
        saved_prec: u32,
    },
    PrattAfterAntiquot {
        cat_name: Name,
        ini_sz: usize,
        ini_pos: usize,
        phase: PrattAntiPhase,
    },
    PrattLeadingFinish {
        cat_name: Name,
        ini_sz: usize,
    },
    PrattTrailing {
        cat_name: Name,
        ini_sz: usize,
        ini_pos: usize,
        left: VmNode,
    },
    LongestMatch {
        left: Option<VmNode>,
        candidates: Vec<(usize, u32)>,
        next_idx: usize,
        start_sz: usize,
        start_lhs: u32,
        start_pos: usize,
        cur_run_start_sz: usize,
        prev: Option<LongestMatchPrev>,
    },
}

/// True when every frame between the current point and the enclosing category
/// is a pure post-wrapper that consumes no additional tokens after the inner
/// category returns (e.g. tail-position `term` in `forall`, `dbg_trace`,
/// `assert!`, sequential `let` body). Bracketed forms such as `(` `term` `)`
/// still have a `Frame::Seq` on the stack for the closing token and therefore
/// count toward `st.depth`.
fn is_tail_category_call(frames: &[Frame<'_, '_>]) -> bool {
    let mut saw_enclosing_category = false;
    for frame in frames.iter().rev() {
        match frame {
            Frame::Node { .. }
            | Frame::TrailingNodeAux { .. }
            | Frame::WithCache { .. }
            | Frame::WithResetCache { .. }
            | Frame::WithOpenRestore { .. }
            | Frame::RestoreSavedPos { .. }
            | Frame::RestoreCtx { .. }
            | Frame::RestoreVerso { .. }
            | Frame::SetExpected { .. }
            | Frame::Atomic { .. }
            | Frame::PopDepth => {}
            Frame::LongestMatch {
                candidates,
                next_idx,
                ..
            } if *next_idx >= candidates.len() => {}
            Frame::PrattLeadingFinish { .. } | Frame::CategoryFinish { .. } => {
                saw_enclosing_category = true;
                break;
            }
            _ => return false,
        }
    }
    saw_enclosing_category
}

impl BuiltinInterpreter {
    pub(super) fn exec_op<'i, 's>(&'i self, op: &ParserOp, st: &mut RuntimeState<'s>) {
        self.exec_op_vm(Arc::new(op.clone()), st);
    }

    pub(super) fn exec_longest_match_vm<'i, 's>(
        &'i self,
        left: Option<&VmNode>,
        candidates: &[(usize, u32)],
        st: &mut RuntimeState<'s>,
    ) {
        let mut frames: Vec<Frame<'i, 's>> = Vec::new();
        let cur_interp = VmInterp::Borrowed(self);
        let next_op = start_longest_match(
            cur_interp.get(),
            left.cloned(),
            candidates.to_vec(),
            st,
            &mut frames,
        );
        run_vm(cur_interp, next_op, st, frames);
    }

    fn exec_op_vm<'i, 's>(&'i self, initial_op: Arc<ParserOp>, st: &mut RuntimeState<'s>) {
        run_vm(VmInterp::Borrowed(self), Some(initial_op), st, Vec::new());
    }
}

fn start_longest_match<'i, 's>(
    interp: &BuiltinInterpreter,
    left: Option<VmNode>,
    candidates: Vec<(usize, u32)>,
    st: &mut RuntimeState<'s>,
    frames: &mut Vec<Frame<'i, 's>>,
) -> Option<Arc<ParserOp>> {
    let Some(&(first_id, first_prio)) = candidates.first() else {
        st.mk_error("longestMatch: empty list");
        return None;
    };
    let start_sz = st.stack_size();
    let start_lhs = st.lhs_prec;
    let start_pos = st.pos;
    st.lhs_prec = if left.is_some() { start_lhs } else { MAX_PREC };
    if let Some(ref l) = left {
        st.push(l.clone());
    }
    let first_op = Arc::clone(&interp.defs[first_id].op);
    frames.push(Frame::LongestMatch {
        left,
        candidates,
        next_idx: 1,
        start_sz,
        start_lhs,
        start_pos,
        cur_run_start_sz: start_sz,
        prev: Some(LongestMatchPrev {
            prev_prio: first_prio,
            prev_score: (0, 0, 0),
            prev_err: None,
            prev_pos: 0,
            prev_sz: 0,
            prev_lhs: 0,
            cur_prio: first_prio,
        }),
    });
    Some(first_op)
}

fn finish_longest_match_run(start_sz: usize, st: &mut RuntimeState<'_>) {
    if st.stack_size() == start_sz + 1 {
        return;
    }
    if st.has_error() {
        st.shrink(start_sz);
        st.push(VmNode::missing());
    } else {
        st.mk_error("longestMatch parsers must generate exactly one Syntax node");
    }
}

fn start_leading_parser<'i, 's>(
    interp: &BuiltinInterpreter,
    cat_name: Name,
    st: &mut RuntimeState<'s>,
    frames: &mut Vec<Frame<'i, 's>>,
) -> Option<Arc<ParserOp>> {
    let Some(cat) = interp.categories.get(&cat_name) else {
        st.mk_unexpected_error(
            format!("unknown parser category '{}'", cat_name.to_display_string()),
            Vec::new(),
            true,
        );
        return None;
    };
    let ini_sz = st.stack_size();
    let indexed = interp.indexed_lookup(&cat.leading_table, cat.behavior, st);
    if st.has_error() {
        return None;
    }
    let mut candidates = cat.leading_unindexed.clone();
    candidates.extend(indexed);
    if candidates.is_empty() {
        let expected = vec![cat.name.to_display_string()];
        let ini_pos = st.pos;
        interp.token_fn(&expected, st);
        if st.has_error() {
            return None;
        }
        st.mk_unexpected_token_errors(&expected, Some(ini_pos));
        return None;
    }
    frames.push(Frame::PrattLeadingFinish { cat_name, ini_sz });
    start_longest_match(interp, None, candidates, st, frames)
}

fn start_pratt_trailing<'i, 's>(
    interp: &BuiltinInterpreter,
    cat_name: Name,
    st: &mut RuntimeState<'s>,
    frames: &mut Vec<Frame<'i, 's>>,
) -> Option<Arc<ParserOp>> {
    if st.has_error() || !st.tick() {
        return None;
    }
    let cat = interp.categories.get(&cat_name)?;
    let ini_sz = st.stack_size();
    let ini_pos = st.pos;
    let indexed = interp.indexed_lookup(&cat.trailing_table, LeadingIdentBehavior::Default, st);
    if st.has_error() {
        st.restore(ini_sz, ini_pos);
        return None;
    }
    if indexed.is_empty() && cat.trailing_unindexed.is_empty() {
        return None;
    }
    let left = st.pop()?;
    let mut candidates = indexed;
    candidates.extend_from_slice(&cat.trailing_unindexed);
    let left_clone = left.clone();
    frames.push(Frame::PrattTrailing {
        cat_name,
        ini_sz,
        ini_pos,
        left,
    });
    start_longest_match(interp, Some(left_clone), candidates, st, frames)
}

fn start_category_parser<'i, 's>(
    interp: &BuiltinInterpreter,
    cat: &Name,
    prec: u32,
    st: &mut RuntimeState<'s>,
    frames: &mut Vec<Frame<'i, 's>>,
) -> Option<Arc<ParserOp>> {
    let saved_prec = st.ctx.prec;
    st.ctx.prec = prec;
    let canonical_cat = if cat.to_display_string() == "syntax" {
        Name::from_components(["stx"])
    } else {
        cat.clone()
    };
    let key = ParserCacheKey {
        ctx: st.ctx.clone(),
        parser_name: canonical_cat.clone(),
        pos: st.pos,
    };
    if let Some(entry) = st.parser_cache.get(&key).cloned() {
        st.push(entry.stx);
        st.lhs_prec = entry.lhs_prec;
        st.pos = entry.new_pos;
        st.error = entry.error;
        st.ctx.prec = saved_prec;
        return None;
    }
    if !st.active_cache_keys.insert(key.clone()) {
        st.depth_exhausted = true;
        st.mk_unexpected_error(
            format!(
                "left-recursive cycle in category {} at byte {}",
                canonical_cat.to_display_string(),
                st.pos
            ),
            Vec::new(),
            true,
        );
        st.ctx.prec = saved_prec;
        return None;
    }
    let init_raw_sz = st.raw_stack_len();
    let old_drop = st.stack_drop;
    st.stack_drop = init_raw_sz;
    st.lhs_prec = 0;
    st.error = None;
    frames.push(Frame::CategoryFinish {
        key,
        init_raw_sz,
        old_drop,
        saved_prec,
    });

    let Some(cat_dispatch) = interp.categories.get(&canonical_cat) else {
        st.mk_unexpected_error(
            format!(
                "unknown parser category '{}'",
                canonical_cat.to_display_string()
            ),
            Vec::new(),
            true,
        );
        return None;
    };
    if st.source.as_bytes().get(st.pos) == Some(&b'$') {
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        let antiquot = Arc::clone(&cat_dispatch.antiquot_parser);
        frames.push(Frame::PrattAfterAntiquot {
            cat_name: canonical_cat,
            ini_sz,
            ini_pos,
            phase: PrattAntiPhase::WaitAntiquot,
        });
        Some(antiquot)
    } else {
        start_leading_parser(interp, canonical_cat, st, frames)
    }
}

fn step_interpolated_str<'i, 's>(
    interp: &BuiltinInterpreter,
    inner: Arc<ParserOp>,
    stack_sz: usize,
    mut chunk_start: usize,
    saved_pos_ctx: Option<usize>,
    st: &mut RuntimeState<'s>,
    frames: &mut Vec<Frame<'i, 's>>,
) -> Option<Arc<ParserOp>> {
    loop {
        if !st.tick() {
            return None;
        }
        let i = st.pos;
        if i >= st.source.len_bytes() {
            st.mk_error("unterminated string literal");
            st.mk_node(interp.interpolated_str_kind.clone(), stack_sz);
            return None;
        }
        let ch = st.source.as_str()[i..].chars().next().unwrap_or('\0');
        st.pos = i + ch.len_utf8();
        if ch == '"' {
            interp.push_node_token(
                interp.interpolated_str_lit_kind.clone(),
                chunk_start,
                true,
                st,
            );
            st.mk_node(interp.interpolated_str_kind.clone(), stack_sz);
            return None;
        } else if ch == '\\' {
            if !skip_quoted_char_for_interp(st) {
                st.mk_node(interp.interpolated_str_kind.clone(), stack_sz);
                return None;
            }
        } else if ch == '{' {
            interp.push_node_token(
                interp.interpolated_str_lit_kind.clone(),
                chunk_start,
                true,
                st,
            );
            if st.has_error() {
                return None;
            }
            st.ctx.saved_pos = None;
            frames.push(Frame::InterpolatedStr {
                inner: Arc::clone(&inner),
                stack_sz,
                saved_pos_ctx,
            });
            return Some(inner);
        }
        // Keep compiler happy about mutability on the next hole continuation.
        let _ = &mut chunk_start;
    }
}

fn run_vm<'i, 's>(
    mut cur_interp: VmInterp<'i>,
    mut next_op: Option<Arc<ParserOp>>,
    st: &mut RuntimeState<'s>,
    mut frames: Vec<Frame<'i, 's>>,
) {
    loop {
        if let Some(mut op) = next_op.take() {
            // Iterative transparent wrapper dereferencing.
            let mut hops = 0usize;
            let mut stopped = false;
            loop {
                if !st.tick() {
                    stopped = true;
                    break;
                }
                let next_wrapped = match op.as_ref() {
                    ParserOp::Ref(id) => {
                        hops += 1;
                        if hops >= st.max_op_depth {
                            cur_interp.get().exec_depth_exceeded(st);
                            stopped = true;
                            break;
                        }
                        Some(Arc::clone(&cur_interp.get().defs[*id].op))
                    }
                    ParserOp::WithoutInfo(inner) => Some(Arc::clone(inner)),
                    ParserOp::Seq(steps) if steps.len() == 1 => Some(Arc::clone(&steps[0])),
                    ParserOp::IfVerso {
                        module_docs,
                        verso,
                        plain,
                    } => {
                        let enabled = if *module_docs {
                            st.ctx.verso_module_docs
                        } else {
                            st.ctx.verso_docs
                        };
                        Some(Arc::clone(if enabled { verso } else { plain }))
                    }
                    ParserOp::WithAntiquot { body, .. }
                        if st.source.as_bytes().get(st.pos) != Some(&b'$') =>
                    {
                        Some(Arc::clone(body))
                    }
                    _ => None,
                };
                if let Some(w) = next_wrapped {
                    op = w;
                } else {
                    break;
                }
            }
            if stopped {
                continue;
            }

            if frames.len() >= MAX_VM_FRAMES {
                cur_interp.get().exec_depth_exceeded(st);
                continue;
            }

            let counts_recursive_depth = matches!(
                op.as_ref(),
                ParserOp::CategoryParser { .. } | ParserOp::ParserOfStack { .. }
            );
            if counts_recursive_depth && !is_tail_category_call(&frames) {
                if st.depth >= st.max_depth {
                    cur_interp.get().exec_depth_exceeded(st);
                    continue;
                }
                st.depth += 1;
                frames.push(Frame::PopDepth);
            }

            let interp = cur_interp.get();
            match op.as_ref() {
                ParserOp::Ref(_)
                | ParserOp::WithoutInfo(_)
                | ParserOp::IfVerso { .. }
                | ParserOp::Skip
                | ParserOp::InhabitedDefault => {}
                ParserOp::PushNone => interp.exec_push_none(st),
                ParserOp::Eoi => interp.exec_eoi(st),
                ParserOp::Symbol(sym) => interp.exec_symbol(sym, st),
                ParserOp::NonReservedSymbol { sym, .. } => interp.exec_non_reserved_symbol(sym, st),
                ParserOp::UnicodeSymbol { sym, ascii_sym } => {
                    interp.exec_unicode_symbol(sym, ascii_sym, st);
                }
                ParserOp::RawCh { ch, trailing_ws } => interp.exec_raw_ch(*ch, *trailing_ws, st),
                ParserOp::Ident => interp.expect_token_kind(&interp.ident_kind, "identifier", st),
                ParserOp::RawIdent => interp.raw_ident_fn(st),
                ParserOp::NumLit => interp.expect_token_kind(&interp.num_lit_kind, "numeral", st),
                ParserOp::HexNum => interp.hexnum_fn(st),
                ParserOp::ScientificLit => {
                    interp.expect_token_kind(&interp.scientific_lit_kind, "scientific number", st);
                }
                ParserOp::StrLit => {
                    interp.expect_token_kind(&interp.str_lit_kind, "string literal", st);
                }
                ParserOp::CharLit => {
                    interp.expect_token_kind(&interp.char_lit_kind, "character literal", st);
                }
                ParserOp::NameLit => {
                    interp.expect_token_kind(&interp.name_lit_kind, "Name literal", st);
                }
                ParserOp::FieldIdx => interp.field_idx_fn(st),
                ParserOp::HygieneInfo => interp.hygiene_info_fn(st),
                ParserOp::CommentBody => interp.comment_body_fn(st),
                ParserOp::VersoCommentBody => interp.verso_comment_body_fn(st),
                ParserOp::CheckPrec(_)
                | ParserOp::CheckLhsPrec(_)
                | ParserOp::SetLhsPrec(_)
                | ParserOp::CheckColEq(_)
                | ParserOp::CheckColGe(_)
                | ParserOp::CheckColGt(_)
                | ParserOp::CheckLineEq(_)
                | ParserOp::CheckWsBefore(_)
                | ParserOp::CheckNoWsBefore(_)
                | ParserOp::CheckLinebreakBefore(_)
                | ParserOp::CheckNoImmediateColon => interp.exec_check_leaf(op.as_ref(), st),
                ParserOp::CheckStackTop { pred, msg } => {
                    interp.exec_check_stack_top(*pred, msg, st)
                }
                ParserOp::SkipUntil(pred) => interp.exec_skip_until(pred, st),
                ParserOp::ErrorAtSavedPos { msg, delta } => {
                    interp.exec_error_at_saved_pos(msg, *delta, st);
                }
                ParserOp::WithoutVersoSyntax(inner) => {
                    let (docs, module_docs) = (st.ctx.verso_docs, st.ctx.verso_module_docs);
                    st.ctx.verso_docs = false;
                    st.ctx.verso_module_docs = false;
                    frames.push(Frame::RestoreVerso { docs, module_docs });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::InterpolatedStr(inner) => {
                    let stack_sz = st.stack_size();
                    let start_pos = st.pos;
                    if start_pos >= st.source.len_bytes() {
                        st.mk_eoi_error(&[]);
                    } else if st.source.as_bytes().get(start_pos) != Some(&b'"') {
                        st.mk_error("interpolated string");
                    } else {
                        st.pos = start_pos + 1;
                        let saved_pos_ctx = st.ctx.saved_pos;
                        next_op = step_interpolated_str(
                            interp,
                            Arc::clone(inner),
                            stack_sz,
                            start_pos,
                            saved_pos_ctx,
                            st,
                            &mut frames,
                        );
                    }
                }
                ParserOp::Seq(steps) => {
                    if let Some(first) = steps.first() {
                        let first = Arc::clone(first);
                        if steps.len() > 1 {
                            frames.push(Frame::Seq {
                                steps: Arc::clone(&op),
                                next_idx: 1,
                            });
                        }
                        next_op = Some(first);
                    }
                }
                ParserOp::OrElse(alts) => {
                    if let Some((first, rest)) = alts.split_first() {
                        let first = Arc::clone(first);
                        if !rest.is_empty() {
                            frames.push(Frame::OrElseChain {
                                alts: Arc::clone(&op),
                                ini_sz: st.stack_size(),
                                ini_pos: st.pos,
                                phase: OrElseChainPhase::First,
                            });
                        }
                        next_op = Some(first);
                    }
                }
                ParserOp::Node(kind, inner) => {
                    frames.push(Frame::Node {
                        kind: kind.clone(),
                        ini_sz: st.stack_size(),
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::TrailingNodeAux(kind, inner) => {
                    frames.push(Frame::TrailingNodeAux {
                        kind: kind.clone(),
                        ini_sz: st.stack_size(),
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::Atomic(inner) => {
                    frames.push(Frame::Atomic { ini_pos: st.pos });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::Optional(inner) => {
                    frames.push(Frame::Optional {
                        ini_sz: st.stack_size(),
                        ini_pos: st.pos,
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::Many(inner) => {
                    let outer_ini_sz = st.stack_size();
                    if st.tick() {
                        frames.push(Frame::Many {
                            inner: Arc::clone(inner),
                            outer_ini_sz,
                            iter_ini_sz: outer_ini_sz,
                            iter_ini_pos: st.pos,
                            first_of_many1: false,
                            unbox: false,
                        });
                        next_op = Some(Arc::clone(inner));
                    } else {
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    }
                }
                ParserOp::Many1(inner) => {
                    let outer_ini_sz = st.stack_size();
                    frames.push(Frame::Many {
                        inner: Arc::clone(inner),
                        outer_ini_sz,
                        iter_ini_sz: outer_ini_sz,
                        iter_ini_pos: st.pos,
                        first_of_many1: true,
                        unbox: false,
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::Many1Unbox(inner) => {
                    let outer_ini_sz = st.stack_size();
                    frames.push(Frame::Many {
                        inner: Arc::clone(inner),
                        outer_ini_sz,
                        iter_ini_sz: outer_ini_sz,
                        iter_ini_pos: st.pos,
                        first_of_many1: true,
                        unbox: true,
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::SepBy {
                    elem,
                    sep,
                    allow_trailing,
                } => {
                    let outer_ini_sz = st.stack_size();
                    if st.tick() {
                        frames.push(Frame::SepBy {
                            elem: Arc::clone(elem),
                            sep: Arc::clone(sep),
                            allow_trailing: *allow_trailing,
                            outer_ini_sz,
                            phase: SepByPhase::WaitElem {
                                sz: outer_ini_sz,
                                pos: st.pos,
                                p_opt: true,
                            },
                        });
                        next_op = Some(Arc::clone(elem));
                    } else {
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    }
                }
                ParserOp::SepBy1 {
                    elem,
                    sep,
                    allow_trailing,
                } => {
                    let outer_ini_sz = st.stack_size();
                    if st.tick() {
                        frames.push(Frame::SepBy {
                            elem: Arc::clone(elem),
                            sep: Arc::clone(sep),
                            allow_trailing: *allow_trailing,
                            outer_ini_sz,
                            phase: SepByPhase::WaitElem {
                                sz: outer_ini_sz,
                                pos: st.pos,
                                p_opt: false,
                            },
                        });
                        next_op = Some(Arc::clone(elem));
                    } else {
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    }
                }
                ParserOp::Lookahead(inner) => {
                    frames.push(Frame::Lookahead {
                        ini_sz: st.stack_size(),
                        ini_pos: st.pos,
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::NotFollowedBy(inner, msg) => {
                    frames.push(Frame::NotFollowedBy {
                        ini_sz: st.stack_size(),
                        ini_pos: st.pos,
                        msg: msg.clone(),
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::WithCache(name, inner) => {
                    let key = ParserCacheKey {
                        ctx: st.ctx.clone(),
                        parser_name: name.clone(),
                        pos: st.pos,
                    };
                    if let Some(entry) = st.parser_cache.get(&key).cloned() {
                        st.push(entry.stx);
                        st.lhs_prec = entry.lhs_prec;
                        st.pos = entry.new_pos;
                        st.error = entry.error;
                    } else if !st.active_cache_keys.insert(key.clone()) {
                        st.depth_exhausted = true;
                        st.mk_unexpected_error(
                            format!(
                                "left-recursive cycle in parser {} at byte {}",
                                name.to_display_string(),
                                st.pos
                            ),
                            Vec::new(),
                            true,
                        );
                    } else {
                        let init_raw_sz = st.raw_stack_len();
                        let old_drop = st.stack_drop;
                        st.stack_drop = init_raw_sz;
                        st.lhs_prec = 0;
                        st.error = None;
                        frames.push(Frame::WithCache {
                            key,
                            init_raw_sz,
                            old_drop,
                        });
                        next_op = Some(Arc::clone(inner));
                    }
                }
                ParserOp::WithResetCache(inner) => {
                    let old_drop = st.stack_drop;
                    let saved_cache = std::mem::take(&mut st.parser_cache);
                    st.stack_drop = 0;
                    frames.push(Frame::WithResetCache {
                        old_drop,
                        saved_cache,
                    });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::WithAntiquot {
                    antiquot,
                    body,
                    is_cat,
                } => {
                    if st.source.as_bytes().get(st.pos) == Some(&b'$') {
                        let behavior = if *is_cat {
                            OrElseAntiquotBehavior::AcceptLhs
                        } else {
                            OrElseAntiquotBehavior::TakeLongest
                        };
                        frames.push(Frame::OrElseCore {
                            rhs: Arc::clone(body),
                            behavior,
                            ini_sz: st.stack_size(),
                            ini_pos: st.pos,
                            phase: OrElseCorePhase::Lhs,
                        });
                        next_op = Some(Arc::clone(antiquot));
                    } else {
                        next_op = Some(Arc::clone(body));
                    }
                }
                ParserOp::TokenWithAntiquot(inner) => {
                    frames.push(Frame::TokenWithAntiquot);
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::WithAntiquotSuffixSplice { kind, body, suffix } => {
                    frames.push(Frame::WithAntiquotSuffixSplice {
                        kind: kind.clone(),
                        suffix: Arc::clone(suffix),
                        phase: SplicePhase::WaitBody,
                    });
                    next_op = Some(Arc::clone(body));
                }
                ParserOp::SetExpected { expected, body } => {
                    frames.push(Frame::SetExpected {
                        expected: expected.clone(),
                    });
                    next_op = Some(Arc::clone(body));
                }
                ParserOp::WithPosition(inner) => {
                    let saved = st.ctx.saved_pos;
                    st.ctx.saved_pos = Some(st.pos);
                    frames.push(Frame::RestoreSavedPos { saved });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::WithPositionAfterLinebreak(inner) => {
                    let saved = st.ctx.saved_pos;
                    if st
                        .back()
                        .is_some_and(|prev| check_tail_linebreak(st.source, prev))
                    {
                        st.ctx.saved_pos = Some(st.pos);
                    }
                    frames.push(Frame::RestoreSavedPos { saved });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::AdaptContext(transform, inner) => {
                    let saved = st.ctx.clone();
                    match transform {
                        ContextTransform::WithoutPosition => st.ctx.saved_pos = None,
                        ContextTransform::WithForbidden(tk) => {
                            st.ctx.forbidden_tk = Some(tk.clone());
                        }
                        ContextTransform::WithoutForbidden => st.ctx.forbidden_tk = None,
                        ContextTransform::SuppressInsideQuot => {
                            if st.ctx.quot_depth == 0 {
                                st.ctx.suppress_inside_quot = true;
                            }
                        }
                        ContextTransform::AddQuotDepth(delta) => {
                            st.ctx.quot_depth =
                                (st.ctx.quot_depth as i64 + i64::from(*delta)).max(0) as u32;
                        }
                    }
                    frames.push(Frame::RestoreCtx { saved });
                    next_op = Some(Arc::clone(inner));
                }
                ParserOp::WithOpen(inner) | ParserOp::WithOpenDecl(inner) => {
                    let expect_open_cmd = matches!(op.as_ref(), ParserOp::WithOpen(_));
                    let open_decl = st.stack.last().and_then(|top| {
                        if expect_open_cmd {
                            if let VmSyntax::Node { kind, args, .. } = &**top
                                && *kind
                                    == Name::from_components(["Lean", "Parser", "Command", "open"])
                            {
                                args.get(1)
                            } else {
                                None
                            }
                        } else {
                            Some(top)
                        }
                    });
                    let activation = open_decl.and_then(|decl| {
                        let VmSyntax::Node { kind, args, .. } = &**decl else {
                            return None;
                        };
                        if *kind
                            == Name::from_components(["Lean", "Parser", "Command", "openSimple"])
                        {
                            let VmSyntax::Node { args: items, .. } = &**args.first()? else {
                                return None;
                            };
                            let names: Vec<Name> = items
                                .iter()
                                .filter_map(|item| match &**item {
                                    VmSyntax::Ident { val, .. } => Some(val.clone()),
                                    _ => None,
                                })
                                .collect();
                            (!names.is_empty()).then_some((names, true))
                        } else if *kind
                            == Name::from_components(["Lean", "Parser", "Command", "openScoped"])
                        {
                            let VmSyntax::Node { args: items, .. } = &**args.get(1)? else {
                                return None;
                            };
                            let names: Vec<Name> = items
                                .iter()
                                .filter_map(|item| match &**item {
                                    VmSyntax::Ident { val, .. } => Some(val.clone()),
                                    _ => None,
                                })
                                .collect();
                            (!names.is_empty()).then_some((names, false))
                        } else {
                            None
                        }
                    });
                    let mut switched = false;
                    if let Some((names, simple)) = activation
                        && let Some((base, fg, snap)) = st.open_context.clone()
                    {
                        let next_snap = fg.activate_snapshot(&snap, &names, simple);
                        let next_grammar = fg.grammar_for_snapshot(&next_snap);
                        if let Ok(next_interp) = next_grammar.generated_interpreter(base) {
                            let old_drop = st.stack_drop;
                            let saved_cache = std::mem::take(&mut st.parser_cache);
                            let saved_ctx = st.open_context.replace((base, fg, next_snap));
                            st.token_cache = None;
                            st.stack_drop = 0;
                            let prev_interp =
                                std::mem::replace(&mut cur_interp, VmInterp::Owned(next_interp));
                            frames.push(Frame::WithOpenRestore {
                                prev_interp,
                                old_drop,
                                saved_cache,
                                saved_ctx,
                            });
                            next_op = Some(Arc::clone(inner));
                            switched = true;
                        }
                    }
                    if !switched {
                        let old_drop = st.stack_drop;
                        let saved_cache = std::mem::take(&mut st.parser_cache);
                        st.stack_drop = 0;
                        frames.push(Frame::WithResetCache {
                            old_drop,
                            saved_cache,
                        });
                        next_op = Some(Arc::clone(inner));
                    }
                }
                ParserOp::CategoryParser { cat, prec } => {
                    next_op = start_category_parser(interp, cat, *prec, st, &mut frames);
                }
                ParserOp::ParserOfStack { offset, prec } => {
                    let sz = st.stack_size();
                    if sz < *offset + 1 {
                        st.mk_unexpected_error(
                            "failed to determine parser using syntax stack, stack is too small",
                            Vec::new(),
                            true,
                        );
                    } else if let Some(VmSyntax::Ident { val, .. }) =
                        st.get_visible(sz - *offset - 1).map(Deref::deref)
                    {
                        let name = val.clone();
                        let canonical_cat = if name.to_display_string() == "syntax" {
                            Name::from_components(["stx"])
                        } else {
                            name.clone()
                        };
                        if interp.categories.contains_key(&canonical_cat) {
                            next_op = start_category_parser(
                                interp,
                                &canonical_cat,
                                *prec,
                                st,
                                &mut frames,
                            );
                        } else {
                            let census = crate::extensions::extension_census();
                            let mut resolved_op: Option<Arc<ParserOp>> = None;
                            if let Some((_, fg, snap)) = st.open_context.as_ref() {
                                if let Some(descr) = fg.resolve_abbreviation_in(snap, &name)
                                    && let Ok(compiled) =
                                        interp.compile_descr_op(descr, &census.alias_declarations)
                                {
                                    resolved_op = Some(compiled);
                                } else if let Some(resolved) =
                                    fg.resolve_name_in(snap, &name, |n| {
                                        interp.def_index.contains_key(n)
                                    })
                                    && let Some(&id) = interp.def_index.get(&resolved)
                                {
                                    resolved_op = Some(Arc::clone(&interp.defs[id].op));
                                }
                            }
                            if resolved_op.is_none()
                                && let Some(&id) = interp.def_index.get(&name)
                            {
                                resolved_op = Some(Arc::clone(&interp.defs[id].op));
                            }
                            if resolved_op.is_none() {
                                let alias_key = name.to_display_string();
                                if census.alias_declarations.contains_key(&alias_key)
                                    && let Ok(compiled) =
                                        interp.compile_alias_op(&name, &census.alias_declarations)
                                {
                                    resolved_op = Some(compiled);
                                }
                            }
                            if let Some(resolved) = resolved_op {
                                next_op = Some(resolved);
                            } else {
                                next_op =
                                    start_category_parser(interp, &name, *prec, st, &mut frames);
                            }
                        }
                    } else {
                        st.mk_unexpected_error(
                            "failed to determine parser using syntax stack, the specified element on the stack is not an identifier",
                            Vec::new(),
                            true,
                        );
                    }
                }
                ParserOp::Recover { parser, handler } => {
                    frames.push(Frame::Recover {
                        handler: Arc::clone(handler),
                        phase: RecoverPhase::WaitParser,
                    });
                    next_op = Some(Arc::clone(parser));
                }
            }
            continue;
        }

        let Some(frame) = frames.pop() else {
            break;
        };
        let interp = cur_interp.get();
        match frame {
            Frame::PopDepth => {
                st.depth = st.depth.saturating_sub(1);
            }
            Frame::Seq { steps, next_idx } => {
                if !st.has_error()
                    && let ParserOp::Seq(vec) = steps.as_ref()
                    && next_idx < vec.len()
                {
                    let step = Arc::clone(&vec[next_idx]);
                    if next_idx + 1 < vec.len() {
                        frames.push(Frame::Seq {
                            steps,
                            next_idx: next_idx + 1,
                        });
                    }
                    next_op = Some(step);
                }
            }
            Frame::Node { kind, ini_sz } => {
                st.mk_node(kind, ini_sz);
            }
            Frame::TrailingNodeAux { kind, ini_sz } => {
                st.mk_trailing_node(kind, ini_sz);
            }
            Frame::Atomic { ini_pos } => {
                if st.has_error() {
                    st.pos = ini_pos;
                }
            }
            Frame::Optional { ini_sz, ini_pos } => {
                if st.has_error() && st.pos == ini_pos && !st.is_exhausted() {
                    st.restore(ini_sz, ini_pos);
                }
                st.mk_node(interp.null_kind.clone(), ini_sz);
            }
            Frame::Many {
                inner,
                outer_ini_sz,
                iter_ini_sz,
                iter_ini_pos,
                first_of_many1,
                unbox,
            } => {
                let mut finish = false;
                if first_of_many1 {
                    if st.has_error() || st.is_exhausted() {
                        finish = true;
                    } else if st.tick() {
                        let next_sz = st.stack_size();
                        let next_pos = st.pos;
                        frames.push(Frame::Many {
                            inner: Arc::clone(&inner),
                            outer_ini_sz,
                            iter_ini_sz: next_sz,
                            iter_ini_pos: next_pos,
                            first_of_many1: false,
                            unbox,
                        });
                        next_op = Some(inner);
                    } else {
                        finish = true;
                    }
                } else if st.has_error() {
                    if st.pos == iter_ini_pos && !st.is_exhausted() {
                        st.restore(iter_ini_sz, iter_ini_pos);
                    }
                    finish = true;
                } else if st.is_exhausted() {
                    finish = true;
                } else if st.pos == iter_ini_pos {
                    st.mk_unexpected_error(
                        "invalid 'many' parser combinator application, parser did not consume anything",
                        Vec::new(),
                        true,
                    );
                    finish = true;
                } else {
                    if st.stack_size() > iter_ini_sz + 1 {
                        st.mk_node(interp.null_kind.clone(), iter_ini_sz);
                    }
                    if st.tick() {
                        let next_sz = st.stack_size();
                        let next_pos = st.pos;
                        frames.push(Frame::Many {
                            inner: Arc::clone(&inner),
                            outer_ini_sz,
                            iter_ini_sz: next_sz,
                            iter_ini_pos: next_pos,
                            first_of_many1: false,
                            unbox,
                        });
                        next_op = Some(inner);
                    } else {
                        finish = true;
                    }
                }
                if finish {
                    st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    if unbox
                        && !st.has_error()
                        && let Some(popped) = st.pop()
                    {
                        if let VmSyntax::Node { args, .. } = &*popped
                            && args.len() == 1
                        {
                            st.push(args[0].clone());
                        } else {
                            st.push(popped);
                        }
                    }
                }
            }
            Frame::SepBy {
                elem,
                sep,
                allow_trailing,
                outer_ini_sz,
                phase,
            } => match phase {
                SepByPhase::WaitElem { sz, pos, p_opt } => {
                    if st.has_error() {
                        if st.pos == pos && p_opt && !st.is_exhausted() {
                            st.restore(sz, pos);
                            st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                        } else {
                            st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                        }
                    } else if st.is_exhausted() {
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    } else if st.pos == pos {
                        st.mk_unexpected_error(
                            "invalid 'sepBy' parser combinator application, parser did not consume anything",
                            Vec::new(),
                            true,
                        );
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    } else {
                        if st.stack_size() > sz + 1 {
                            st.mk_node(interp.null_kind.clone(), sz);
                        }
                        let sep_sz = st.stack_size();
                        let sep_pos = st.pos;
                        frames.push(Frame::SepBy {
                            elem,
                            sep: Arc::clone(&sep),
                            allow_trailing,
                            outer_ini_sz,
                            phase: SepByPhase::WaitSep {
                                sz: sep_sz,
                                pos: sep_pos,
                            },
                        });
                        next_op = Some(sep);
                    }
                }
                SepByPhase::WaitSep { sz, pos } => {
                    if st.has_error() {
                        if !st.is_exhausted() {
                            st.restore(sz, pos);
                        }
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    } else if st.is_exhausted() {
                        st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                    } else {
                        if st.stack_size() > sz + 1 {
                            st.mk_node(interp.null_kind.clone(), sz);
                        }
                        if st.tick() {
                            let elem_sz = st.stack_size();
                            let elem_pos = st.pos;
                            frames.push(Frame::SepBy {
                                elem: Arc::clone(&elem),
                                sep,
                                allow_trailing,
                                outer_ini_sz,
                                phase: SepByPhase::WaitElem {
                                    sz: elem_sz,
                                    pos: elem_pos,
                                    p_opt: allow_trailing,
                                },
                            });
                            next_op = Some(elem);
                        } else {
                            st.mk_node(interp.null_kind.clone(), outer_ini_sz);
                        }
                    }
                }
            },
            Frame::Lookahead { ini_sz, ini_pos } => {
                if !st.has_error() {
                    st.restore(ini_sz, ini_pos);
                }
            }
            Frame::NotFollowedBy {
                ini_sz,
                ini_pos,
                msg,
            } => {
                if st.is_exhausted() {
                    // Resource exhaustion is sticky (FL-INV-07).
                } else if st.has_error() {
                    st.restore(ini_sz, ini_pos);
                } else {
                    st.restore(ini_sz, ini_pos);
                    st.mk_unexpected_error(format!("unexpected {msg}"), Vec::new(), true);
                }
            }
            Frame::WithCache {
                key,
                init_raw_sz,
                old_drop,
            } => {
                st.stack_drop = old_drop;
                st.active_cache_keys.remove(&key);
                if !st.is_exhausted()
                    && st.raw_stack_len() == init_raw_sz + 1
                    && let Some(top) = st.back_cloned()
                {
                    st.parser_cache.insert(
                        key,
                        ParserCacheEntry {
                            stx: top,
                            lhs_prec: st.lhs_prec,
                            new_pos: st.pos,
                            error: st.error.clone(),
                        },
                    );
                }
            }
            Frame::WithResetCache {
                old_drop,
                saved_cache,
            } => {
                st.stack_drop = old_drop;
                st.parser_cache = saved_cache;
            }
            Frame::WithOpenRestore {
                prev_interp,
                old_drop,
                saved_cache,
                saved_ctx,
            } => {
                cur_interp = prev_interp;
                st.open_context = saved_ctx;
                st.stack_drop = old_drop;
                st.parser_cache = saved_cache;
                st.token_cache = None;
            }
            Frame::OrElseChain {
                alts,
                ini_sz,
                ini_pos,
                phase,
            } => {
                let ParserOp::OrElse(vec) = alts.as_ref() else {
                    continue;
                };
                let next_idx = match phase {
                    OrElseChainPhase::First => 1,
                    OrElseChainPhase::AltAfterErr { next_idx, err1 } => {
                        if st.pos == ini_pos
                            && let Some(err2) = st.error.take()
                        {
                            st.error = Some(err1.merge(&err2));
                        }
                        next_idx
                    }
                    OrElseChainPhase::AltAfterAntiquot {
                        next_idx,
                        p_back,
                        p_pos,
                    } => {
                        if st.has_error() {
                            st.restore(ini_sz, p_pos);
                            st.push(p_back);
                        } else if st.pos > p_pos {
                            // Keep the longer match from alt.
                        } else if st.pos < p_pos
                            || st.stack_size() != ini_sz + 1
                            || !st
                                .back()
                                .is_some_and(|b| is_antiquots(b, &interp.choice_kind))
                        {
                            st.restore(ini_sz, p_pos);
                            st.push(p_back);
                        } else {
                            let q_back = st.pop_or_missing();
                            interp.push_flattened_antiquots(p_back, st);
                            interp.push_flattened_antiquots(q_back, st);
                            st.mk_node(interp.choice_kind.clone(), ini_sz);
                        }
                        next_idx
                    }
                };
                if next_idx >= vec.len() || st.is_exhausted() {
                    continue;
                }
                if let Some(err1) = st.error.take() {
                    if st.pos == ini_pos {
                        st.restore(ini_sz, ini_pos);
                        let alt = Arc::clone(&vec[next_idx]);
                        frames.push(Frame::OrElseChain {
                            alts,
                            ini_sz,
                            ini_pos,
                            phase: OrElseChainPhase::AltAfterErr {
                                next_idx: next_idx + 1,
                                err1,
                            },
                        });
                        next_op = Some(alt);
                    } else {
                        st.error = Some(err1);
                    }
                } else if st.stack_size() == ini_sz + 1
                    && st
                        .back()
                        .is_some_and(|b| is_antiquots(b, &interp.choice_kind))
                {
                    let p_back = st.pop_or_missing();
                    let p_pos = st.pos;
                    st.restore(ini_sz, ini_pos);
                    let alt = Arc::clone(&vec[next_idx]);
                    frames.push(Frame::OrElseChain {
                        alts,
                        ini_sz,
                        ini_pos,
                        phase: OrElseChainPhase::AltAfterAntiquot {
                            next_idx: next_idx + 1,
                            p_back,
                            p_pos,
                        },
                    });
                    next_op = Some(alt);
                }
            }
            Frame::OrElseCore {
                rhs,
                behavior,
                ini_sz,
                ini_pos,
                phase,
            } => match phase {
                OrElseCorePhase::Lhs => {
                    if st.is_exhausted() {
                        // Resource exhaustion is sticky (FL-INV-07).
                    } else if let Some(err1) = st.error.take() {
                        if st.pos == ini_pos {
                            st.restore(ini_sz, ini_pos);
                            frames.push(Frame::OrElseCore {
                                rhs: Arc::clone(&rhs),
                                behavior,
                                ini_sz,
                                ini_pos,
                                phase: OrElseCorePhase::RhsAfterErr(err1),
                            });
                            next_op = Some(rhs);
                        } else {
                            st.error = Some(err1);
                        }
                    } else if behavior != OrElseAntiquotBehavior::AcceptLhs
                        && st.stack_size() == ini_sz + 1
                        && st
                            .back()
                            .is_some_and(|b| is_antiquots(b, &interp.choice_kind))
                    {
                        let p_back = st.pop_or_missing();
                        let p_pos = st.pos;
                        st.restore(ini_sz, ini_pos);
                        frames.push(Frame::OrElseCore {
                            rhs: Arc::clone(&rhs),
                            behavior,
                            ini_sz,
                            ini_pos,
                            phase: OrElseCorePhase::RhsAfterAntiquot(p_back, p_pos),
                        });
                        next_op = Some(rhs);
                    }
                }
                OrElseCorePhase::RhsAfterErr(err1) => {
                    if st.pos == ini_pos
                        && let Some(err2) = st.error.take()
                    {
                        st.error = Some(err1.merge(&err2));
                    }
                }
                OrElseCorePhase::RhsAfterAntiquot(p_back, p_pos) => {
                    if st.is_exhausted() {
                        // Resource exhaustion is sticky (FL-INV-07).
                    } else if st.has_error() {
                        st.restore(ini_sz, p_pos);
                        st.push(p_back);
                    } else if st.pos > p_pos {
                        // Keep rhs.
                    } else if st.pos < p_pos
                        || behavior != OrElseAntiquotBehavior::Merge
                        || st.stack_size() != ini_sz + 1
                        || !st
                            .back()
                            .is_some_and(|b| is_antiquots(b, &interp.choice_kind))
                    {
                        st.restore(ini_sz, p_pos);
                        st.push(p_back);
                    } else {
                        let q_back = st.pop_or_missing();
                        interp.push_flattened_antiquots(p_back, st);
                        interp.push_flattened_antiquots(q_back, st);
                        st.mk_node(interp.choice_kind.clone(), ini_sz);
                    }
                }
            },
            Frame::TokenWithAntiquot => {
                if !st.has_error() && st.source.as_bytes().get(st.pos) == Some(&b'%') {
                    let ini_sz = st.stack_size();
                    let ini_pos = st.pos;
                    if st
                        .pick_non_none(&interp.null_kind)
                        .is_some_and(check_tail_no_ws)
                    {
                        interp.satisfy_symbol(|s| s == "%", &["'%'".to_owned()], st);
                        if st.has_error() {
                            st.restore(ini_sz, ini_pos);
                            continue;
                        }
                        interp.satisfy_symbol(|s| s == "$", &["'$'".to_owned()], st);
                        if st.has_error()
                            || !st
                                .pick_non_none(&interp.null_kind)
                                .is_some_and(check_tail_no_ws)
                        {
                            st.restore(ini_sz, ini_pos);
                            continue;
                        }
                        frames.push(Frame::TokenAntiquotSuffix { ini_sz, ini_pos });
                        next_op = Some(Arc::clone(&interp.antiquot_expr_op));
                    }
                }
            }
            Frame::TokenAntiquotSuffix { ini_sz, ini_pos } => {
                if st.has_error() {
                    st.restore(ini_sz, ini_pos);
                } else {
                    st.mk_node(interp.token_antiquot_kind.clone(), ini_sz.saturating_sub(1));
                }
            }
            Frame::WithAntiquotSuffixSplice {
                kind,
                suffix,
                phase,
            } => match phase {
                SplicePhase::WaitBody => {
                    if !st.has_error()
                        && st
                            .back()
                            .is_some_and(|s| is_antiquots(s, &interp.choice_kind))
                    {
                        let ini_sz = st.stack_size();
                        let ini_pos = st.pos;
                        frames.push(Frame::WithAntiquotSuffixSplice {
                            kind,
                            suffix: Arc::clone(&suffix),
                            phase: SplicePhase::WaitSuffix { ini_sz, ini_pos },
                        });
                        next_op = Some(suffix);
                    }
                }
                SplicePhase::WaitSuffix { ini_sz, ini_pos } => {
                    if st.has_error() {
                        st.restore(ini_sz, ini_pos);
                    } else {
                        let splice_kind = Name::str(kind, "antiquot_suffix_splice");
                        let target_sz = st.stack_size().saturating_sub(2);
                        st.mk_node(splice_kind, target_sz);
                    }
                }
            },
            Frame::SetExpected { expected } => {
                if let Some(err) = &mut st.error {
                    err.expected = expected;
                }
            }
            Frame::RestoreSavedPos { saved } => {
                st.ctx.saved_pos = saved;
            }
            Frame::RestoreCtx { saved } => {
                st.ctx = saved;
            }
            Frame::RestoreVerso { docs, module_docs } => {
                st.ctx.verso_docs = docs;
                st.ctx.verso_module_docs = module_docs;
            }
            Frame::Recover { handler, phase } => match phase {
                RecoverPhase::WaitParser => {
                    if let Some(msg) = st.error.take() {
                        let saved_pos = st.pos;
                        let saved_stack_len = st.raw_stack_len();
                        let saved_lhs = st.lhs_prec;
                        frames.push(Frame::Recover {
                            handler: Arc::clone(&handler),
                            phase: RecoverPhase::WaitHandler {
                                msg,
                                saved_pos,
                                saved_stack_len,
                                saved_lhs,
                            },
                        });
                        next_op = Some(handler);
                    }
                }
                RecoverPhase::WaitHandler {
                    msg,
                    saved_pos,
                    saved_stack_len,
                    saved_lhs,
                } => {
                    if st.has_error() {
                        st.pos = saved_pos;
                        st.truncate_raw(saved_stack_len);
                        st.lhs_prec = saved_lhs;
                        st.error = Some(msg);
                    } else {
                        st.recovered_errors.push(msg);
                    }
                }
            },
            Frame::InterpolatedStr {
                inner,
                stack_sz,
                saved_pos_ctx,
            } => {
                st.ctx.saved_pos = saved_pos_ctx;
                if st.has_error() {
                    continue;
                }
                let brace_pos = st.pos;
                if st.source.as_bytes().get(brace_pos) == Some(&b'}') {
                    st.pos = brace_pos + 1;
                    next_op = step_interpolated_str(
                        interp,
                        inner,
                        stack_sz,
                        brace_pos,
                        saved_pos_ctx,
                        st,
                        &mut frames,
                    );
                } else {
                    st.mk_error("'}'");
                    st.mk_node(interp.interpolated_str_kind.clone(), stack_sz);
                }
            }
            Frame::CategoryFinish {
                key,
                init_raw_sz,
                old_drop,
                saved_prec,
            } => {
                st.stack_drop = old_drop;
                st.active_cache_keys.remove(&key);
                if !st.is_exhausted()
                    && st.raw_stack_len() == init_raw_sz + 1
                    && let Some(top) = st.back_cloned()
                {
                    st.parser_cache.insert(
                        key,
                        ParserCacheEntry {
                            stx: top,
                            lhs_prec: st.lhs_prec,
                            new_pos: st.pos,
                            error: st.error.clone(),
                        },
                    );
                }
                st.ctx.prec = saved_prec;
            }
            Frame::PrattAfterAntiquot {
                cat_name,
                ini_sz,
                ini_pos,
                phase,
            } => match phase {
                PrattAntiPhase::WaitAntiquot => {
                    if st.is_exhausted() {
                        // Resource exhaustion is sticky (FL-INV-07).
                    } else if let Some(err1) = st.error.take() {
                        if st.pos == ini_pos {
                            st.restore(ini_sz, ini_pos);
                            frames.push(Frame::PrattAfterAntiquot {
                                cat_name: cat_name.clone(),
                                ini_sz,
                                ini_pos,
                                phase: PrattAntiPhase::WaitLeading(err1),
                            });
                            next_op = start_leading_parser(interp, cat_name, st, &mut frames);
                        } else {
                            st.error = Some(err1);
                        }
                    } else {
                        next_op = start_pratt_trailing(interp, cat_name, st, &mut frames);
                    }
                }
                PrattAntiPhase::WaitLeading(err1) => {
                    if !st.is_exhausted()
                        && st.pos == ini_pos
                        && let Some(err2) = st.error.take()
                    {
                        st.error = Some(err1.merge(&err2));
                    }
                    // Note: `start_leading_parser` already enters `PrattTrailing` via
                    // `PrattLeadingFinish` when it succeeds; if it failed we are done.
                }
            },
            Frame::PrattLeadingFinish { cat_name, ini_sz } => {
                if st.stack_size() != ini_sz + 1 {
                    st.mk_node(interp.null_kind.clone(), ini_sz);
                }
                if !st.is_exhausted() {
                    next_op = start_pratt_trailing(interp, cat_name, st, &mut frames);
                }
            }
            Frame::PrattTrailing {
                cat_name,
                ini_sz,
                ini_pos,
                left,
            } => {
                if st.is_exhausted() {
                    // Resource exhaustion is sticky (FL-INV-07): never restore `left`.
                } else if st.has_error() {
                    if st.pos == ini_pos {
                        st.restore(ini_sz.saturating_sub(1), ini_pos);
                        st.push(left);
                    }
                } else if st.pos != ini_pos {
                    next_op = start_pratt_trailing(interp, cat_name, st, &mut frames);
                }
            }
            Frame::LongestMatch {
                left,
                candidates,
                next_idx,
                start_sz,
                start_lhs,
                start_pos,
                cur_run_start_sz,
                prev,
            } => {
                finish_longest_match_run(cur_run_start_sz, st);
                if st.is_exhausted() {
                    // Resource exhaustion is sticky (FL-INV-07): never discard it in favor of
                    // an earlier cheaper alternative and never try remaining candidates.
                    st.keep_top(start_sz);
                    continue;
                }
                let mut prev = prev.expect("LongestMatch prev state");
                if next_idx > 1 {
                    let cur_score = (st.pos, u8::from(!st.has_error()), prev.cur_prio);
                    match prev.prev_score.cmp(&cur_score) {
                        std::cmp::Ordering::Less => {
                            st.keep_top(start_sz);
                            prev.prev_prio = prev.cur_prio;
                        }
                        std::cmp::Ordering::Greater => {
                            st.shrink(prev.prev_sz);
                            st.lhs_prec = prev.prev_lhs;
                            st.pos = prev.prev_pos;
                            st.error = prev.prev_err.take();
                        }
                        std::cmp::Ordering::Equal => match prev.prev_err.take() {
                            None => {
                                st.lhs_prec = st.lhs_prec.min(prev.prev_lhs);
                                prev.prev_prio = prev.cur_prio;
                            }
                            Some(old_err) => {
                                st.shrink(prev.prev_sz);
                                if let Some(cur_err) = &st.error
                                    && *cur_err != old_err
                                {
                                    st.error = Some(old_err.merge(cur_err));
                                }
                                prev.prev_prio = prev.cur_prio;
                            }
                        },
                    }
                }
                if !st.depth_exhausted && !st.budget_exhausted && next_idx < candidates.len() {
                    let (def_id, prio) = candidates[next_idx];
                    let prev_score = (st.pos, u8::from(!st.has_error()), prev.prev_prio);
                    let prev_err = st.error.clone();
                    let prev_pos = st.pos;
                    let prev_sz = st.stack_size();
                    let prev_lhs = st.lhs_prec;

                    st.restore(prev_sz, start_pos);
                    st.lhs_prec = if left.is_some() { start_lhs } else { MAX_PREC };
                    let run_start_sz = st.stack_size();
                    if let Some(ref l) = left {
                        st.push(l.clone());
                    }
                    let op = Arc::clone(&interp.defs[def_id].op);
                    frames.push(Frame::LongestMatch {
                        left,
                        candidates,
                        next_idx: next_idx + 1,
                        start_sz,
                        start_lhs,
                        start_pos,
                        cur_run_start_sz: run_start_sz,
                        prev: Some(LongestMatchPrev {
                            prev_prio: prev.prev_prio,
                            prev_score,
                            prev_err,
                            prev_pos,
                            prev_sz,
                            prev_lhs,
                            cur_prio: prio,
                        }),
                    });
                    next_op = Some(op);
                } else if st.stack_size() > start_sz + 1 {
                    st.mk_node(interp.choice_kind.clone(), start_sz);
                }
            }
        }
    }
}
