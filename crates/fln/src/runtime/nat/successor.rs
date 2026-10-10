//! Canonical Nat construction and elimination operate on native naturals
//! independently of public arithmetic. A recursive Nat.add implementation may
//! use Nat.succ, and Nat.pred may use Nat.rec; routing those structural steps
//! back through the public functions makes their implementations cyclic.
use super::*;

const ADD: &str = "_fln_runtime_nat_constructor_add";
const PRED: &str = "_fln_runtime_nat_recursor_pred";

#[derive(Clone, Copy)]
enum Primitive {
    Add,
    Predecessor,
}

impl Primitive {
    fn names(self) -> (&'static str, &'static str) {
        match self {
            Self::Add => (ADD, "Nat.add"),
            Self::Predecessor => (PRED, "Nat.pred"),
        }
    }
}

impl Preparation<'_> {
    pub(crate) fn nat_primitive_intrinsic_binding(
        &self,
        requested: &Name,
    ) -> Option<IntrinsicBinding> {
        self.nat_primitives
            .iter()
            .flatten()
            .find(|binding| &binding.name == requested)
            .cloned()
    }

    pub(in crate::runtime) fn nat_primitive_intrinsic_type(
        &self,
        requested: &Name,
    ) -> Option<Expr> {
        let binding = self
            .nat_primitives
            .iter()
            .flatten()
            .find(|binding| &binding.name == requested)?;
        let nat = Expr::const_(name("Nat"), vec![]);
        Some(binding.arguments.iter().fold(nat.clone(), |body, _| {
            Expr::forall_e(Name::anonymous(), nat.clone(), body, BinderInfo::Default)
        }))
    }

    /// A program can use both checked native public arithmetic and private
    /// structural operations. FIR requires one declaration per intrinsic row.
    /// Preserve both callable names through an ordinary typed forwarding body;
    /// do not relax ingress's duplicate-row or ownership validation.
    pub(crate) fn nat_primitive_intrinsic_alias(
        &mut self,
        binding: &IntrinsicBinding,
        intrinsics: &[IntrinsicBinding],
        functions: &mut Vec<FunctionBinding>,
    ) -> Result<bool, IngressError> {
        let Some(private) = self
            .nat_primitives
            .iter()
            .flatten()
            .find(|private| binding.row == private.row)
        else {
            return Ok(false);
        };
        let private_name = private.name.clone();
        for known in intrinsics {
            self.tick()?;
            if known.row != binding.row
                || (known.name != private_name && binding.name != private_name)
            {
                continue;
            }
            let mut renamed = binding.clone();
            renamed.name = known.name.clone();
            if &renamed != known {
                return Err(unsupported("Nat structural arithmetic aliases disagree"));
            }
            reserve(functions, self.limits.fir.max_functions.saturating_sub(1))?;
            let mut body = Expr::const_(known.name.clone(), vec![]);
            for index in (0..binding.arguments.len()).rev() {
                self.tick()?;
                body = Expr::app(body, variable(index)?);
            }
            functions.push(FunctionBinding {
                name: binding.name.clone(),
                universe_arity: binding.universe_arity,
                parameters: binding.arguments.clone(),
                parameter_ownership: binding.argument_ownership.clone(),
                result: binding.result,
                result_ownership: result_ownership(binding.result),
                body,
            });
            return Ok(true);
        }
        Ok(false)
    }

    fn nat_primitive(&mut self, primitive: Primitive) -> Result<Name, IngressError> {
        self.check_nat_family()?;
        self.tick()?;
        let (private, public) = primitive.names();
        let private = name(private);
        if self.environment.contains(&private) {
            return Err(unsupported("Nat structural primitive name collision"));
        }
        if self.nat_primitives[primitive as usize].is_none() {
            // The authority is the exact admitted inductive family and the
            // generated native arithmetic contract. No public arithmetic body or
            // extension journal participates in this compiler-owned operation.
            let mut binding = generated_source_intrinsic_binding(&name(public))
                .ok_or_else(|| unsupported("native Nat structural arithmetic contract"))?;
            binding.name = private.clone();
            self.nat_primitives[primitive as usize] = Some(binding);
        }
        Ok(private)
    }

    pub(super) fn nat_predecessor(&mut self, major: Expr) -> Result<Expr, IngressError> {
        let primitive = self.nat_primitive(Primitive::Predecessor)?;
        Ok(Expr::app(Expr::const_(primitive, vec![]), major))
    }

    pub(in crate::runtime) fn nat_successor_call(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if !matches!(head.node(), ExprNode::Const { name: requested, levels }
            if requested == &name("Nat.succ") && levels.is_empty())
            || arguments.len() > 1
        {
            return Ok(None);
        }
        // Applied heads normally resolve this before dispatch. Bare values
        // need the same priority before their ordinary strict eta wrapper.
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        let primitive = self.nat_primitive(Primitive::Add)?;
        let increment = |argument| {
            Expr::app(
                Expr::app(Expr::const_(primitive.clone(), vec![]), argument),
                literal(1),
            )
        };
        if let [argument] = arguments {
            return Ok(Some(increment(argument.clone())));
        }
        let nat = scalar(ValueType::Nat)?;
        let type_ = Expr::forall_e(
            Name::anonymous(),
            nat.clone(),
            nat.clone(),
            BinderInfo::Default,
        );
        let lambda = Expr::lam(
            Name::anonymous(),
            nat,
            increment(variable(0)?),
            BinderInfo::Default,
        );
        // Let registration gives the escaping constructor the same checked
        // closure interface and ownership rules as any ordinary local function.
        Ok(Some(Expr::let_e(
            name("_fln_runtime_nat_successor"),
            type_,
            lambda,
            variable(0)?,
            false,
        )))
    }
}
