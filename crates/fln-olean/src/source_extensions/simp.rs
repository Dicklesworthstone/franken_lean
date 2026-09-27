//! The default simp journal is data, not a proof checker. In particular the
//! `rfl`/permutation flags and discrimination keys never authorize a reduction.
//! The consumer must use an admitted proof and explicitly account for unsupported
//! phases, scopes or proof forms. Preprocessed proofs can name auxiliary lemmas
//! different from their origin; reversing that proof again would be incorrect.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpEntry {
    pub scope: Option<Name>,
    pub kind: SimpKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpKind {
    Theorem(SimpTheorem),
    Unfold(Name),
    UnfoldTheorems {
        declaration: Name,
        theorems: Vec<Name>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpTheorem {
    /// Already oriented, possibly preprocessed proof. Not necessarily `origin`.
    pub proof: Expr,
    pub level_params: Vec<Name>,
    pub origin: Name,
    /// Orientation of the *origin*, not a request to reverse `proof` again.
    pub origin_reverse: bool,
    pub priority: u32,
    pub post: bool,
    pub permutation: bool,
    pub reflexive: bool,
    pub backward_reflexive: bool,
    /// The native simplifier rebuilds selection from checked types.
    pub key_count: usize,
}

fn boolean(obj: &Obj, pointers: usize, index: usize) -> Result<bool, DecodeError> {
    let flags = obj
        .try_ctor_scalar_u64(pointers * 8)
        .ok_or_else(|| shape("missing simp scalar flags"))?;
    match (flags >> (index * 8)) & 0xff {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(shape("invalid simp Boolean flag")),
    }
}

impl Reader {
    fn simp_array_size(&mut self, obj: &Obj) -> Result<usize, DecodeError> {
        let size = array_length(obj)?;
        self.indices_left = self
            .indices_left
            .checked_sub(size)
            .ok_or_else(|| limit("index cells"))?;
        Ok(size)
    }

    fn simp_names(&mut self, obj: &Obj) -> Result<Vec<Name>, DecodeError> {
        let size = self.simp_array_size(obj)?;
        let mut names = Vec::with_capacity(size);
        let mut seen = BTreeSet::new();
        for i in 0..size {
            let name = self.name(&obj.array_child(i))?;
            if !seen.insert(name.clone()) {
                return Err(shape("duplicate simp name"));
            }
            names.push(name);
        }
        Ok(names)
    }

    fn simp_theorem(&mut self, obj: &Obj) -> Result<SimpTheorem, DecodeError> {
        constructor(obj, 0, format::SIMP_THM_POINTERS)?;
        let post = boolean(obj, format::SIMP_THM_POINTERS, format::SIMP_THM_POST_SCALAR)?;
        let origin = field(obj, format::SIMP_THM_ORIGIN)?;
        constructor(
            &origin,
            format::SIMP_ORIGIN_DECL,
            format::SIMP_ORIGIN_DECL_POINTERS,
        )?;
        if boolean(
            &origin,
            format::SIMP_ORIGIN_DECL_POINTERS,
            format::SIMP_ORIGIN_DECL_POST_SCALAR,
        )? != post
        {
            return Err(shape("simp phase disagrees with declaration origin"));
        }
        let mut heap = NativeHeap::new();
        let proof = self
            .conversion
            .project_expr(&mut heap, &field(obj, format::SIMP_THM_PROOF)?)
            .map_err(DecodeError::Conversion)?;
        let proof = heap
            .get(proof)
            .map_err(|_| shape("projected simp proof is missing"))?
            .clone();
        if proof.has_expr_mvar()
            || proof.has_level_mvar()
            || proof.has_fvar()
            || proof.has_loose_bvars()
        {
            return Err(shape("persistent simp proof is not closed"));
        }
        Ok(SimpTheorem {
            proof,
            level_params: self.simp_names(&field(obj, format::SIMP_THM_LEVEL_PARAMS)?)?,
            origin: self.name(&field(&origin, format::SIMP_ORIGIN_DECL_NAME)?)?,
            origin_reverse: boolean(
                &origin,
                format::SIMP_ORIGIN_DECL_POINTERS,
                format::SIMP_ORIGIN_DECL_INV_SCALAR,
            )?,
            priority: natural(&field(obj, format::SIMP_THM_PRIORITY)?)?,
            post,
            permutation: boolean(obj, format::SIMP_THM_POINTERS, format::SIMP_THM_PERM_SCALAR)?,
            reflexive: boolean(obj, format::SIMP_THM_POINTERS, format::SIMP_THM_RFL_SCALAR)?,
            backward_reflexive: boolean(
                obj,
                format::SIMP_THM_POINTERS,
                format::SIMP_THM_BACKWARD_RFL_SCALAR,
            )?,
            key_count: self.simp_array_size(&field(obj, format::SIMP_THM_KEYS)?)?,
        })
    }

    pub(super) fn simp(&mut self, obj: &Obj) -> Result<SimpEntry, DecodeError> {
        if obj.is_scalar() {
            return Err(shape("simp entry lacks its scope wrapper"));
        }
        let (scope, entry) = match obj.obj_tag() as u8 {
            format::SCOPE_GLOBAL => {
                constructor(obj, format::SCOPE_GLOBAL, 1)?;
                (None, field(obj, 0)?)
            }
            format::SCOPE_SCOPED => {
                constructor(obj, format::SCOPE_SCOPED, 2)?;
                (Some(self.name(&field(obj, 0)?)?), field(obj, 1)?)
            }
            _ => return Err(shape("unknown simp scope tag")),
        };
        if entry.is_scalar() {
            return Err(shape("simp entry has no payload"));
        }
        let kind = match entry.obj_tag() as u8 {
            format::SIMP_ENTRY_THM => {
                constructor(&entry, format::SIMP_ENTRY_THM, 1)?;
                SimpKind::Theorem(self.simp_theorem(&field(&entry, 0)?)?)
            }
            format::SIMP_ENTRY_TO_UNFOLD => {
                constructor(&entry, format::SIMP_ENTRY_TO_UNFOLD, 1)?;
                SimpKind::Unfold(self.name(&field(&entry, 0)?)?)
            }
            format::SIMP_ENTRY_TO_UNFOLD_THMS => {
                constructor(&entry, format::SIMP_ENTRY_TO_UNFOLD_THMS, 2)?;
                SimpKind::UnfoldTheorems {
                    declaration: self.name(&field(&entry, 0)?)?,
                    theorems: self.simp_names(&field(&entry, 1)?)?,
                }
            }
            _ => return Err(shape("unknown simp entry tag")),
        };
        Ok(SimpEntry { scope, kind })
    }
}
