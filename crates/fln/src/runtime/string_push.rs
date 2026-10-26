//! Adapt checked Char objects at the native String and character boundaries.
//!
//! Char keeps its ordinary logical UInt32/BitVec/Fin fields. Only this private
//! call reads their scalar value, after the complete source contract matches.
//! The native primitive independently validates the Unicode scalar range.

use super::*;
use crate::source_intrinsics::string_push;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};

const PRIMITIVE: &str = "_fln_runtime_string_push_abi";
const CHAR_OF_NAT: &str = "_fln_runtime_char_ofNatAux";
const CHAR_OF_NAT_PRIMITIVE: &str = "_fln_runtime_char_ofNatAux_abi";

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    primitive: Option<(IntrinsicBinding, Expr)>,
    character_primitive: Option<(IntrinsicBinding, Expr)>,
    character_adapter: Option<Name>,
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
        [
            self.string_push.primitive.as_ref(),
            self.string_push.character_primitive.as_ref(),
        ]
        .into_iter()
        .flatten()
        .find(|(binding, _)| &binding.name == requested)
        .map(|(binding, _)| binding.clone())
    }

    pub(super) fn string_push_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        [
            self.string_push.primitive.as_ref(),
            self.string_push.character_primitive.as_ref(),
        ]
        .into_iter()
        .flatten()
        .find(|(binding, _)| &binding.name == requested)
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

    /// The ABI erases the validity proof and returns a UInt32 scalar. Rebuild
    /// the existing logical Char fields around that scalar only after matching
    /// the entire admitted definition and its executable dependency closure.
    pub(super) fn native_char_of_nat_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        if requested != &name("Char.ofNatAux") {
            return Ok(None);
        }
        if let Some(target) = &self.string_push.character_adapter {
            let target = target.clone();
            self.tick()?;
            return Ok(Some(target));
        }
        if !self.has_extern_attribute(requested)? {
            return Ok(None);
        }
        self.implementations()?;
        string_push::char_of_nat_matches(
            self.environment,
            self.implementations
                .as_ref()
                .expect("checked implementation journal"),
            self.runtime_initializers,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let primitive = name(CHAR_OF_NAT_PRIMITIVE);
        if self.environment.contains(&primitive) || self.has_private_callable(&primitive) {
            return Err(unsupported("Char.ofNatAux primitive name collision"));
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == "extern:Char.ofNatAux")
            .ok_or_else(|| unsupported("Char.ofNatAux generated primitive row"))?;
        if row.name != "Char.ofNatAux"
            || row.kind != "defn"
            || row.levels != 0
            || row.arity != 2
            || row.symbol != "lean_uint32_of_nat"
            || row.effect != "pure"
            || row.ownership != "abi((a: borrowed_arg) -> value)"
        {
            return Err(unsupported("Char.ofNatAux generated primitive contract"));
        }
        let Some(ConstantInfo::Defn(original)) = self.environment.find(requested) else {
            return Err(unsupported("Char.ofNatAux checked interface"));
        };
        let mut definition = original.clone();
        let mut telescope = definition.base.type_.clone();
        let mut binders = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = telescope.node()
        {
            self.tick()?;
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            telescope = body.clone();
        }
        if !definition.base.level_params.is_empty() || binders.len() != 2 || telescope != c("Char")
        {
            return Err(unsupported("Char.ofNatAux checked telescope"));
        }
        let mut value = self.native_character_from_scalar(Expr::app(
            Expr::const_(primitive.clone(), vec![]),
            b(1)?,
        ))?;
        for (binder_name, binder_type, binder_info) in binders.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(binder_name, binder_type, value, binder_info);
        }
        definition.base.name = name(CHAR_OF_NAT);
        definition.value = value;
        definition.hints = fln_env::constants::ReducibilityHints::Abbrev;
        definition.all.clear();
        self.remember_native_scalar_adapter_definition(definition)?;
        self.string_push.character_primitive = Some((
            IntrinsicBinding {
                name: primitive,
                universe_arity: 0,
                row: row.id.to_owned(),
                arguments: vec![ValueType::Nat],
                argument_ownership: vec![ArgumentOwnership::Borrowed],
                // The UInt32 handler's scalar is an ordinary bounded Nat in
                // the private Fin field, never a logical UInt32 constructor.
                result: ValueType::Nat,
                result_ownership: ResultOwnership::Scalar,
                effect: EffectClass::Pure,
            },
            function(&[c("Nat")], c("Nat")),
        ));
        let target = name(CHAR_OF_NAT);
        self.string_push.character_adapter = Some(target.clone());
        Ok(Some(target))
    }

    pub(super) fn char_of_nat_call(
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
        if requested != &name("Char.ofNatAux") || !levels.is_empty() {
            return Ok(None);
        }
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        Ok(self.native_char_of_nat_target(requested)?.map(|target| {
            arguments
                .iter()
                .cloned()
                .fold(Expr::const_(target, vec![]), Expr::app)
        }))
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
