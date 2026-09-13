//! Compact literal decisions within the ordered constructor-pattern matrix.
//!
//! A Boolean comparison never produces an equality witness. Original subject
//! types remain unchanged; dependent refinements still need the checked index
//! equation backend. Where a constructor split or structural root needs Nat's
//! fields, expose only one constructor layer and keep the predecessor compact.
use super::*;
use fln_bignum::nat::BigNat;
use fln_core::expr::{Literal, NatLit};

pub(super) struct LiteralPattern<'a> {
    value: Literal,
    syntax: Cow<'a, Syntax>,
}

impl Context {
    pub(super) fn decode_pattern_literal<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Option<LiteralPattern<'a>>, NatDefinitionElabError> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        let natural = kind == &Name::from_components(["num"]);
        if !natural && kind != &Name::from_components(["str"]) {
            return Ok(None);
        }
        // The current source String is opaque. Its executable comparison has
        // no checked definition, so do not invent a kernel conversion rule.
        if !natural {
            return Err(invalid());
        }
        let [Syntax::Atom { val, .. }] = args.as_slice() else {
            return Err(invalid());
        };
        // Charge input size before decoding, including raw spelling and escapes.
        for _ in val.as_bytes() {
            self.tick()?;
        }
        let value = decode_natural(val)?;
        Ok(Some(LiteralPattern {
            value,
            syntax: Cow::Borrowed(syntax),
        }))
    }

    fn same_pattern_literal(
        &mut self,
        a: &Literal,
        b: &Literal,
    ) -> Result<bool, NatDefinitionElabError> {
        match (a, b) {
            (Literal::Nat(a), Literal::Nat(b)) => {
                if a.limbs_le().len() != b.limbs_le().len() {
                    return Ok(false);
                }
                for (a, b) in a.limbs_le().iter().zip(b.limbs_le()) {
                    self.tick()?;
                    if a != b {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Err(invalid()),
        }
    }

    fn compact_predecessor(
        &mut self,
        value: &NatLit,
    ) -> Result<LiteralPattern<'static>, NatDefinitionElabError> {
        for _ in value.limbs_le() {
            self.tick()?;
        }
        let value = BigNat::from_limbs_le(value.limbs_le().to_vec()).sub(&BigNat::from_u64(1));
        let mut spelling = String::from("0x");
        if value.limbs_le().is_empty() {
            spelling.push('0');
        }
        for (position, limb) in value.limbs_le().iter().rev().enumerate() {
            self.tick()?;
            use std::fmt::Write;
            if position == 0 {
                write!(&mut spelling, "{limb:x}").expect("String write");
            } else {
                write!(&mut spelling, "{limb:016x}").expect("String write");
            }
        }
        Ok(LiteralPattern {
            value: Literal::Nat(NatLit::from_limbs_le(value.limbs_le().to_vec())),
            syntax: Cow::Owned(Syntax::node(
                Name::from_components(["num"]),
                vec![atom(&spelling)],
            )),
        })
    }

    /// Either prepare one constructor layer in place, or return a typed Boolean
    /// decision's ordered hit/miss matrices. No branch is selected by evaluating
    /// a user discriminant during elaboration.
    #[allow(clippy::type_complexity)]
    pub(super) fn literal_matrix_split<'a>(
        &mut self,
        matrix: &mut Matrix<'a>,
        subject: &Name,
        arena: &mut Vec<Pattern<'a>>,
    ) -> Result<Option<(Syntax, Matrix<'a>, Matrix<'a>)>, NatDefinitionElabError> {
        let mut selected = None;
        let mut constructors = matrix.recursive_root;
        for row in &matrix.rows {
            self.tick()?;
            match &arena[row.patterns[0]] {
                Pattern::Literal(_) => {
                    selected.get_or_insert(row.patterns[0]);
                }
                Pattern::Constructor(_) => constructors = true,
                Pattern::Bind(_) => {}
            }
        }
        let Some(selected) = selected else {
            return Ok(None);
        };
        let Pattern::Literal(literal) = &arena[selected] else {
            unreachable!()
        };
        let value = literal.value.clone();
        let syntax = self.copy_pattern_syntax(&literal.syntax)?;
        // A mixed-typed literal column must not become a silently dead branch.
        for row in &matrix.rows {
            self.tick()?;
            if let Pattern::Literal(other) = &arena[row.patterns[0]]
                && std::mem::discriminant(&value) != std::mem::discriminant(&other.value)
            {
                return Err(invalid());
            }
        }
        if constructors {
            if !matches!(value, Literal::Nat(_)) {
                return Err(invalid());
            }
            let mut expanded = HashMap::new();
            for row in &mut matrix.rows {
                self.tick()?;
                let pattern = row.patterns[0];
                if let Some(index) = expanded.get(&pattern) {
                    row.patterns[0] = *index;
                    continue;
                }
                let Pattern::Literal(LiteralPattern {
                    value: Literal::Nat(number),
                    ..
                }) = &arena[pattern]
                else {
                    continue;
                };
                let zero = number.limbs_le().is_empty();
                let fields = if zero {
                    Vec::new()
                } else {
                    let predecessor = self.compact_predecessor(number)?;
                    let index = arena.len();
                    arena.push(Pattern::Literal(predecessor));
                    vec![index]
                };
                let name = Name::from_components(["Nat", if zero { "zero" } else { "succ" }]);
                let index = arena.len();
                arena.push(Pattern::Constructor(Constructor {
                    head: Head {
                        relative: false,
                        name: name.clone(),
                    },
                    syntax: Cow::Owned(identifier(name)),
                    fields,
                }));
                expanded.insert(pattern, index);
                row.patterns[0] = index;
            }
            return Ok(None);
        }
        let mut hit = Vec::new();
        let mut miss = Vec::new();
        for row in &matrix.rows {
            self.tick()?;
            let mut accepted = row.clone();
            match &arena[accepted.patterns.remove(0)] {
                Pattern::Literal(other) => {
                    if self.same_pattern_literal(&value, &other.value)? {
                        hit.push(accepted);
                    } else {
                        miss.push(row.clone());
                    }
                }
                Pattern::Bind(name) => {
                    if let Some(name) = name {
                        accepted.bindings.push((name.clone(), subject.clone()));
                    }
                    hit.push(accepted);
                    miss.push(row.clone());
                }
                Pattern::Constructor(_) => return Err(invalid()),
            }
        }
        // Nat is an infinite domain. A finite literal-only decision
        // cannot justify erasing its uncovered branch, even for a closed input.
        if miss.is_empty() {
            return Err(invalid());
        }
        let comparator = Name::from_components(["Nat", "beq"]);
        let test = Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![
                identifier(comparator),
                null(vec![identifier(subject.clone()), syntax]),
            ],
        );
        let mut miss_subjects = vec![subject.clone()];
        miss_subjects.extend(matrix.subjects.iter().cloned());
        Ok(Some((
            test,
            Matrix {
                recursive_root: false,
                subjects: matrix.subjects.clone(),
                rows: hit,
            },
            Matrix {
                recursive_root: false,
                subjects: miss_subjects,
                rows: miss,
            },
        )))
    }
}
