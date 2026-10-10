//! Adapt the checked Char object to the existing native String.push row.
//!
//! Char keeps its ordinary logical UInt32/BitVec/Fin fields. Only this private
//! call reads their scalar value, after the complete source contract matches.
//! The native primitive independently validates the Unicode scalar range.

use super::*;
use crate::source_intrinsics::string_push;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

const PRIMITIVE: &str = "_fln_runtime_string_push_abi";

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    primitive: Option<(IntrinsicBinding, Expr)>,
    character: Option<CharacterLayout>,
}

#[derive(Clone)]
struct CharacterLayout {
    projections: [Name; 4],
    constructors: [Name; 4],
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("String.push adapter binder scope"))
}

impl Preparation<'_> {
    pub(crate) fn string_push_intrinsic_binding(
        &self,
        requested: &Name,
    ) -> Option<IntrinsicBinding> {
        self.string_push
            .primitive
            .as_ref()
            .filter(|(binding, _)| &binding.name == requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn string_push_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.string_push
            .primitive
            .as_ref()
            .filter(|(binding, _)| &binding.name == requested)
            .map(|(_, type_)| type_.clone())
    }

    fn string_push_adapter_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.string_push.next_adapter;
        self.string_push.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("String.push adapter identity"))?;
        let name = Name::num(name("_fln_runtime_string_push_scope"), serial);
        if self.environment.contains(&name) {
            return Err(unsupported("String.push adapter name collision"));
        }
        Ok(name)
    }

    fn string_push_record(
        &mut self,
        source: Expr,
        fields: usize,
    ) -> Result<(Name, Name, Vec<Expr>), IngressError> {
        let source = self.erase_runtime_type(&source)?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported(
                "String.push requires the checked Char object layout",
            ));
        }
        let shape = self
            .record_shape(&source)?
            .ok_or_else(|| unsupported("String.push checked character field layout"))?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("String.push checked character structure"));
        };
        if constructor.tag != 0 || constructor.fields.len() != fields {
            return Err(unsupported("String.push checked character field count"));
        }
        Ok((
            shape.projection(constructor),
            constructor.name.clone(),
            constructor.fields.clone(),
        ))
    }

    /// Reuse the ordinary checked Char representation across native String
    /// adapters. Callers establish their own complete source contract first;
    /// deriving these field views registers no native operation by itself.
    pub(super) fn native_character_projections(&mut self) -> Result<[Name; 4], IngressError> {
        Ok(self.native_character_layout()?.projections)
    }

    fn native_character_layout(&mut self) -> Result<CharacterLayout, IngressError> {
        if let Some(character) = &self.string_push.character {
            return Ok(character.clone());
        }
        let (character, character_ctor, character_fields) =
            self.string_push_record(c("Char"), 2)?;
        if character_fields != [c("UInt32"), proofs::erased_type()] {
            return Err(unsupported("String.push logical character fields"));
        }
        let (word, word_ctor, word_fields) =
            self.string_push_record(character_fields[0].clone(), 1)?;
        let (bits, bits_ctor, bits_fields) = self.string_push_record(word_fields[0].clone(), 1)?;
        let (finite, finite_ctor, finite_fields) =
            self.string_push_record(bits_fields[0].clone(), 2)?;
        if finite_fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("String.push logical finite-word fields"));
        }
        let character = CharacterLayout {
            projections: [character, word, bits, finite],
            constructors: [character_ctor, word_ctor, bits_ctor, finite_ctor],
        };
        self.string_push.character = Some(character.clone());
        Ok(character)
    }

    /// Native String traversal supplies a validated Unicode scalar. Rebuild
    /// the source callback's ordinary checked Char representation using those
    /// exact registered constructors; proof fields keep their usual inert slots.
    pub(super) fn native_character_from_scalar(
        &mut self,
        scalar: Expr,
    ) -> Result<Expr, IngressError> {
        let [character, word, bits, finite] = self.native_character_layout()?.constructors;
        let mut result = Expr::app(
            Expr::app(Expr::const_(finite, vec![]), scalar),
            proofs::erased_value(),
        );
        for constructor in [bits, word] {
            self.tick()?;
            result = Expr::app(Expr::const_(constructor, vec![]), result);
        }
        Ok(Expr::app(
            Expr::app(Expr::const_(character, vec![]), result),
            proofs::erased_value(),
        ))
    }

    fn string_push_bind(&mut self) -> Result<[Name; 4], IngressError> {
        let projections = self.native_character_projections()?;
        if self.string_push.primitive.is_some() {
            return Ok(projections);
        }
        let primitive = name(PRIMITIVE);
        if self.environment.contains(&primitive) {
            return Err(unsupported("String.push primitive name collision"));
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == "extern:String.push")
            .ok_or_else(|| unsupported("String.push generated primitive row"))?;
        if row.name != "String.push"
            || row.kind != "defn"
            || row.levels != 0
            || row.arity != 2
            || row.effect != "pure"
            || row.ownership != "abi((s: owned_arg, c: value) -> owned_res)"
        {
            return Err(unsupported("String.push generated primitive contract"));
        }
        self.string_push.primitive = Some((
            IntrinsicBinding {
                name: primitive,
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments: vec![ValueType::String, ValueType::Nat],
                argument_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Scalar],
                result: ValueType::String,
                result_ownership: ResultOwnership::Owned,
                effect: EffectClass::Pure,
            },
            function(&[c("String"), c("Nat")], c("String")),
        ));
        Ok(projections)
    }

    /// Preserve ordinary first-class and partially applied source functions.
    /// The private wrapper is closed and typed; source arguments remain outside
    /// its binding, retaining their scopes and ordinary evaluation order.
    pub(super) fn string_push_call(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: requested,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if requested != &string_push::source_name() || !levels.is_empty() {
            return Ok(None);
        }
        self.tick()?;
        if self.string_push.primitive.is_none()
            && !string_push::contract_matches(
                self.environment,
                requested,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        if arguments.len() > 2 {
            return Ok(None);
        }
        let projections = self.string_push_bind()?;
        let mut codepoint = b(0)?;
        for projection in projections {
            self.tick()?;
            codepoint = Expr::proj(projection, 0, codepoint);
        }
        let body = Expr::app(Expr::app(c(PRIMITIVE), b(1)?), codepoint);
        let value = Expr::lam(
            self.string_push_adapter_name()?,
            c("String"),
            Expr::lam(
                self.string_push_adapter_name()?,
                c("Char"),
                body,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let wrapper = Expr::let_e(
            self.string_push_adapter_name()?,
            function(&[c("String"), c("Char")], c("String")),
            value,
            b(0)?,
            false,
        );
        Ok(Some(arguments.iter().cloned().fold(wrapper, Expr::app)))
    }
}

#[cfg(test)]
mod tests;
