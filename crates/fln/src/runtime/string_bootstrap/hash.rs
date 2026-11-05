//! Hash mixing over the checked UInt64/BitVec/Fin representation.
//!
//! Only the pinned opaque and its selected extern authorize the adapter.
//! Public words remain records; private scalar conversions preserve all bits.
//! The logical fallback is never evaluated and source operands remain strict.

use super::*;

const MIX: &str = "_fln_runtime_hash_mix";
const OF_NAT: &str = "_fln_runtime_hash_word_of_nat";

#[derive(Default)]
pub(super) struct Store {
    checked: bool,
    pub(super) bindings: [Option<(IntrinsicBinding, Expr)>; 2],
    projections: Option<[Name; 3]>,
}

impl Preparation<'_> {
    pub(in crate::runtime) fn hash_mixer_contract(
        &mut self,
        requested: &Name,
    ) -> Result<bool, IngressError> {
        if requested != &name("mixHash") {
            return Ok(false);
        }
        self.tick()?;
        if self.string_bootstrap.hash.checked {
            return Ok(true);
        }
        if !source_intrinsics::hash::matches(
            self.environment,
            requested,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )? {
            return Ok(false);
        }
        self.string_bootstrap.hash.checked = true;
        Ok(true)
    }

    fn hash_mixer_bind(&mut self) -> Result<(), IngressError> {
        if self.string_bootstrap.hash.projections.is_some() {
            return Ok(());
        }
        self.string_bootstrap_word64()?;
        if self.environment.contains(&name(MIX)) || self.environment.contains(&name(OF_NAT)) {
            return Err(unsupported("hash mixer private primitive name collision"));
        }
        let mut projections = Vec::new();
        let mut source = c("UInt64");
        for fields in [1, 1, 2] {
            self.tick()?;
            let shape = self.io_checked_shape(source)?;
            let [constructor] = shape.constructors.as_slice() else {
                return Err(unsupported("hash mixer checked word structure"));
            };
            if constructor.tag != 0 || constructor.fields.len() != fields {
                return Err(unsupported("hash mixer checked word fields"));
            }
            projections.push(shape.projection(constructor));
            source = constructor.fields[0].clone();
        }
        if source != c("Nat") {
            return Err(unsupported("hash mixer checked word payload"));
        }
        let mut mixer = generated_runtime_intrinsic_binding(
            &name("mixHash"),
            vec![ValueType::UInt64, ValueType::UInt64],
            ValueType::UInt64,
            None,
        )
        .ok_or_else(|| unsupported("hash mixer generated native contract"))?;
        if mixer.row != "extern:mixHash"
            || mixer.argument_ownership != [ArgumentOwnership::Scalar; 2]
            || mixer.result_ownership != ResultOwnership::Scalar
        {
            return Err(unsupported("hash mixer generated scalar ownership"));
        }
        let mut of_nat = generated_source_intrinsic_binding(&name("UInt64.ofNat"))
            .ok_or_else(|| unsupported("hash mixer generated word conversion"))?;
        if of_nat.row != "extern:UInt64.ofNat"
            || of_nat.arguments != [ValueType::Nat]
            || of_nat.argument_ownership != [ArgumentOwnership::Borrowed]
            || of_nat.result != ValueType::UInt64
            || of_nat.result_ownership != ResultOwnership::Scalar
            || of_nat.effect != EffectClass::Pure
        {
            return Err(unsupported("hash mixer generated word conversion contract"));
        }
        mixer.name = name(MIX);
        of_nat.name = name(OF_NAT);
        self.string_bootstrap.hash.bindings = [
            Some((
                mixer,
                function(&[c(NATIVE_WORD64), c(NATIVE_WORD64)], c(NATIVE_WORD64)),
            )),
            Some((of_nat, function(&[c("Nat")], c(NATIVE_WORD64)))),
        ];
        self.string_bootstrap.hash.projections = Some(
            projections
                .try_into()
                .map_err(|_| unsupported("hash mixer word projection count"))?,
        );
        Ok(())
    }

    fn hash_mixer_pack(&mut self, mut value: Expr) -> Result<Expr, IngressError> {
        let projections = self
            .string_bootstrap
            .hash
            .projections
            .clone()
            .expect("validated hash mixer layout");
        for projection in projections {
            self.tick()?;
            value = Expr::proj(projection, 0, value);
        }
        Ok(Expr::app(c(OF_NAT), value))
    }

    pub(super) fn hash_mixer_call(
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
        if requested != &name("mixHash") || !levels.is_empty() || arguments.len() > 2 {
            return Ok(None);
        }
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        if !self.hash_mixer_contract(requested)? {
            return Ok(None);
        }
        self.hash_mixer_bind()?;
        let left = self.hash_mixer_pack(b(1)?)?;
        let right = self.hash_mixer_pack(b(0)?)?;
        let mixed = Expr::app(Expr::app(c(MIX), left), right);
        let mut body = self.string_bootstrap_word64_from_native(mixed)?;
        // Preserve the typed residual closure for a partially supplied mixer.
        // The supplied first operand is evaluated once in its outer strict let.
        let prefix = usize::from(arguments.len() == 1);
        let remaining = 2 - prefix;
        for _ in 0..remaining {
            body = Expr::lam(
                self.string_bootstrap_adapter_name()?,
                c("UInt64"),
                body,
                BinderInfo::Default,
            );
        }
        let type_ = function(&vec![c("UInt64"); remaining], c("UInt64"));
        let wrapper = Expr::let_e(
            self.string_bootstrap_adapter_name()?,
            type_,
            body,
            b(0)?,
            false,
        );
        if prefix == 1 {
            return Ok(Some(Expr::let_e(
                self.string_bootstrap_adapter_name()?,
                c("UInt64"),
                arguments[0].clone(),
                wrapper,
                false,
            )));
        }
        Ok(Some(arguments.iter().cloned().fold(wrapper, Expr::app)))
    }
}

#[cfg(test)]
mod tests;
