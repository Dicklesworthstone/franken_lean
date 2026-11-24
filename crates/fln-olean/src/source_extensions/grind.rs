//! The supported global user-pattern rows of the pin's grind journal.
//!
//! Other rows stay deferred. In particular, recognizing this extension name
//! does not grant authority to inferred rules, local scopes, constraints,
//! injectivity, extensionality or congruence metadata.
use super::*;

/// One global `grind_pattern` group in the pin's already normalized wire form.
/// The proof is the original declaration constant with its universe arguments.
/// Ground annotations and don't-care expressions are preserved verbatim; a
/// checked importer must bind the declaration and validate their semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrindPatternEntry {
    pub declaration: Name,
    pub proof: Expr,
    /// The whole syntactic forall telescope, including trailing proof binders.
    pub num_params: u32,
    /// One simultaneous group, not a collection of alternative groups.
    pub patterns: Vec<Expr>,
    /// Ordered distinct `HeadIndex.const` symbols, never a sorted set.
    pub symbols: Vec<Name>,
}

impl GrindPatternEntry {
    pub(crate) fn validate(&self) -> Result<(), &'static str> {
        if self.declaration.is_anonymous()
            || !matches!(self.proof.node(), ExprNode::Const { name, .. } if name == &self.declaration)
            || self.proof.has_level_mvar()
        {
            return Err("grind proof does not name its declaration origin");
        }
        if self.patterns.is_empty()
            || self.patterns.iter().any(|pattern| {
                pattern.has_expr_mvar()
                    || pattern.has_level_mvar()
                    || pattern.has_fvar()
                    || pattern.loose_bvar_range() > self.num_params
            })
        {
            return Err("empty or unbound persistent grind patterns");
        }
        let mut seen = BTreeSet::new();
        if self.symbols.is_empty()
            || self
                .symbols
                .iter()
                .any(|symbol| symbol.is_anonymous() || !seen.insert(symbol))
        {
            return Err("empty, anonymous or duplicate grind symbols");
        }
        Ok(())
    }
}

fn list_is_empty(obj: &Obj) -> Result<bool, DecodeError> {
    if obj.is_scalar() {
        return if obj.unbox() == usize::from(format::LIST_NIL) {
            Ok(true)
        } else {
            Err(shape("invalid grind list terminator"))
        };
    }
    constructor(obj, format::LIST_CONS, format::LIST_CONS_POINTERS)?;
    Ok(false)
}

fn list_next(obj: &Obj, entries_left: &mut usize) -> Result<Option<(Obj, Obj)>, DecodeError> {
    if list_is_empty(obj)? {
        return Ok(None);
    }
    *entries_left = entries_left
        .checked_sub(1)
        .ok_or_else(|| limit("entries"))?;
    Ok(Some((
        field(obj, format::LIST_CONS_HEAD)?,
        field(obj, format::LIST_CONS_TAIL)?,
    )))
}

impl Reader {
    fn grind_expr(&mut self, obj: &Obj) -> Result<Expr, DecodeError> {
        let mut heap = NativeHeap::new();
        let expression = self
            .conversion
            .project_expr(&mut heap, obj)
            .map_err(DecodeError::Conversion)?;
        heap.get(expression)
            .cloned()
            .map_err(|_| shape("projected grind expression is missing"))
    }

    pub(super) fn grind(
        &mut self,
        obj: &Obj,
        entries_left: &mut usize,
    ) -> Result<Option<GrindPatternEntry>, DecodeError> {
        if obj.is_scalar() {
            return Err(shape("grind entry lacks its scope wrapper"));
        }
        let entry = match obj.obj_tag() as u8 {
            format::SCOPE_GLOBAL => {
                constructor(obj, format::SCOPE_GLOBAL, format::PARSER_SCOPE_GLOBAL_POINTERS)?;
                field(obj, format::PARSER_SCOPE_GLOBAL_ENTRY)?
            }
            format::SCOPE_SCOPED => {
                constructor(obj, format::SCOPE_SCOPED, format::PARSER_SCOPE_SCOPED_POINTERS)?;
                // The opaque payload remains attached to its module. A future
                // scope-aware consumer may activate it; this reader does not.
                return Ok(None);
            }
            _ => return Err(shape("unknown grind scope tag")),
        };
        if entry.is_scalar() {
            return Err(shape("grind entry has no payload"));
        }
        match entry.obj_tag() as u8 {
            format::GRIND_ENTRY_EXT
            | format::GRIND_ENTRY_FUN_CC
            | format::GRIND_ENTRY_CASES
            | format::GRIND_ENTRY_INJ => return Ok(None),
            format::GRIND_ENTRY_EMATCH => constructor(
                &entry,
                format::GRIND_ENTRY_EMATCH,
                format::GRIND_ENTRY_EMATCH_POINTERS,
            )?,
            _ => return Err(shape("unknown grind entry tag")),
        }
        let theorem = field(&entry, format::GRIND_ENTRY_EMATCH_THM)?;
        constructor(&theorem, 0, format::GRIND_THM_POINTERS)?;
        let kind = field(&theorem, format::GRIND_THM_KIND)?;
        if !kind.is_scalar() {
            if kind.obj_tag() == usize::from(format::GRIND_KIND_USER) {
                return Err(shape("grind user kind has unexpected payload"));
            }
            return Ok(None);
        }
        if kind.unbox() != usize::from(format::GRIND_KIND_USER) {
            return Ok(None);
        }
        let min_indexable = theorem
            .try_ctor_scalar_u64(
                format::GRIND_THM_POINTERS * 8 + format::GRIND_THM_MIN_INDEXABLE_SCALAR,
            )
            .ok_or_else(|| shape("missing grind minimal-indexable flag"))?
            as u8;
        match min_indexable {
            0 => {}
            1 => return Ok(None),
            _ => return Err(shape("invalid grind minimal-indexable flag")),
        }
        if array_length(&field(&theorem, format::GRIND_THM_LEVEL_PARAMS)?)? != 0
            || !list_is_empty(&field(&theorem, format::GRIND_THM_CNSTRS)?)?
        {
            return Ok(None);
        }
        let origin = field(&theorem, format::GRIND_THM_ORIGIN)?;
        if origin.is_scalar() {
            return Err(shape("grind theorem origin has no payload"));
        }
        if origin.obj_tag() != usize::from(format::GRIND_ORIGIN_DECL) {
            return Ok(None);
        }
        constructor(
            &origin,
            format::GRIND_ORIGIN_DECL,
            format::GRIND_ORIGIN_DECL_POINTERS,
        )?;
        let declaration = self.name(&field(&origin, format::GRIND_ORIGIN_DECL_DECL_NAME)?)?;
        let proof = self.grind_expr(&field(&theorem, format::GRIND_THM_PROOF)?)?;
        if !matches!(proof.node(), ExprNode::Const { .. }) {
            return Ok(None);
        }
        let mut symbols = Vec::new();
        let mut rest = field(&theorem, format::GRIND_THM_SYMBOLS)?;
        while let Some((symbol, tail)) = list_next(&rest, entries_left)? {
            self.keys_left = self.keys_left.checked_sub(1).ok_or_else(|| limit("grind symbols"))?;
            if symbol.is_scalar() || symbol.obj_tag() != usize::from(format::GRIND_HEAD_CONST) {
                return Ok(None);
            }
            constructor(
                &symbol,
                format::GRIND_HEAD_CONST,
                format::GRIND_HEAD_CONST_POINTERS,
            )?;
            symbols.push(self.name(&field(&symbol, format::GRIND_HEAD_CONST_CONST_NAME)?)?);
            rest = tail;
        }
        let mut patterns = Vec::new();
        let mut rest = field(&theorem, format::GRIND_THM_PATTERNS)?;
        while let Some((pattern, tail)) = list_next(&rest, entries_left)? {
            patterns.push(self.grind_expr(&pattern)?);
            rest = tail;
        }
        let row = GrindPatternEntry {
            declaration,
            proof,
            num_params: natural(&field(&theorem, format::GRIND_THM_NUM_PARAMS)?)?,
            patterns,
            symbols,
        };
        row.validate().map_err(shape)?;
        Ok(Some(row))
    }
}
