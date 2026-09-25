//! Erase canonical Nat elimination to native, capture-aware recursive closures.
//! The original recursor and its branches have already passed both checkers.
//! No kernel term is changed, and no arbitrary family is selected by spelling.
use super::*;
use fln_core::expr::{FVarId, NatLit};
use fln_core::level::Level;

pub(super) struct Recursion {
    pub lambda: Expr,
    pub parameters: Vec<ValueType>,
    pub result: ValueType,
}

struct Motive {
    parameters: Vec<ValueType>,
    domains: Vec<Expr>,
    result: ValueType,
    result_type: Expr,
}

pub(super) fn literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn scalar(value: ValueType) -> Result<Expr, IngressError> {
    let spelling = match value {
        ValueType::Nat => "Nat",
        ValueType::Bool => "Bool",
        ValueType::String => "String",
        _ => return Err(unsupported("Nat recursor result representation")),
    };
    Ok(Expr::const_(name(spelling), vec![]))
}

fn variable(index: usize) -> Result<Expr, IngressError> {
    let index = u32::try_from(index).map_err(|_| unsupported("Nat recursor binder count"))?;
    Expr::bvar(index).map_err(|_| unsupported("Nat recursor binder scope"))
}

fn call(spelling: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments
        .into_iter()
        .fold(Expr::const_(name(spelling), vec![]), Expr::app)
}

impl Preparation<'_> {
    pub(super) fn check_nat_family(&mut self) -> Result<(), IngressError> {
        if self.nat_family_checked {
            return Ok(());
        }
        let Declaration::Inductive(block) = fln_elab::seed::nat_inductive_seed_declaration() else {
            return Err(unsupported("Nat inductive seed"));
        };
        for expected in &block.types {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Induct(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical Nat family"));
            }
        }
        for expected in &block.ctors {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Ctor(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical Nat constructor"));
            }
        }
        for expected in &block.recursors {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Rec(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical Nat recursor"));
            }
        }
        self.nat_family_checked = true;
        Ok(())
    }

    /// A motive can return data or a first-order data function. Normalize the
    /// static motive through the same uniform-layout erasure as other indexed
    /// eliminators. Only an absent runtime index binder may be removed: using
    /// its raw body would leave that index referring to a new closure binder.
    /// The resulting function telescope becomes extra recursive arguments.
    fn nat_motive(&mut self, motive: &Expr) -> Result<Motive, IngressError> {
        let family = scalar(ValueType::Nat)?;
        let normalized = self
            .indexed_motive(motive, &[], &family)?
            .ok_or_else(|| unsupported("dependent Nat recursor motive"))?;
        let mut body = &normalized;
        let mut parameters = vec![ValueType::Nat];
        let mut domains = vec![family];
        loop {
            self.tick()?;
            match body.node() {
                ExprNode::MData { expr, .. } => body = expr,
                ExprNode::ForallE {
                    binder_type,
                    body: inner,
                    ..
                } => {
                    let parameter = self
                        .value_type(binder_type)?
                        .ok_or_else(|| unsupported("dependent Nat recursor parameter"))?;
                    reserve(&mut domains, self.limits.max_context_depth)?;
                    domains.push(binder_type.clone());
                    reserve(&mut parameters, self.limits.max_context_depth)?;
                    parameters.push(parameter);
                    body = inner;
                }
                _ => break,
            }
        }
        let result = self
            .value_type(body)?
            .ok_or_else(|| unsupported("dependent Nat recursor result"))?;
        Ok(Motive {
            parameters,
            domains,
            result,
            result_type: body.clone(),
        })
    }

    /// Apply only explicit beta redexes before branch preparation. In
    /// particular, an unused induction hypothesis disappears rather than
    /// eagerly evaluating every predecessor of a plain, nonrecursive match.
    pub(super) fn minor_apply(
        &mut self,
        mut function: Expr,
        argument: Expr,
    ) -> Result<Expr, IngressError> {
        loop {
            self.tick()?;
            match function.node() {
                ExprNode::MData { expr, .. } => function = expr.clone(),
                ExprNode::LetE { value, body, .. } => {
                    // Source recursion retains the current constructor in a
                    // checked local let around generalized arguments. Open it
                    // before applying those arguments; admission already
                    // checked even an unused local type and value.
                    function = body
                        .subst_loose(0, std::slice::from_ref(value))
                        .map_err(|_| unsupported("Nat minor let scope"))?;
                }
                ExprNode::Lam { body, .. } => {
                    return body
                        .subst_loose(0, &[argument])
                        .map_err(|_| unsupported("Nat minor substitution scope"));
                }
                _ => return Ok(Expr::app(function, argument)),
            }
        }
    }

    pub(super) fn nat_recursion(&mut self, args: &[Expr]) -> Result<Recursion, IngressError> {
        if args.len() < 4 {
            return Err(unsupported("Nat recursor arity"));
        }
        self.check_nat_family()?;
        let Motive {
            parameters,
            domains,
            result,
            result_type,
        } = self.nat_motive(&args[0])?;
        let extra = parameters.len() - 1;
        let depth = parameters.len().saturating_add(1); // native self + runtime arguments
        if depth > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: depth,
            });
        }
        let lift = u32::try_from(depth).map_err(|_| unsupported("Nat recursor scope"))?;
        let mut zero = args[1]
            .lift_loose(0, lift)
            .map_err(|_| unsupported("Nat zero branch scope"))?;
        let mut step = args[2]
            .lift_loose(0, lift)
            .map_err(|_| unsupported("Nat successor branch scope"))?;
        let id = self.next_nat;
        self.next_nat = id
            .checked_add(1)
            .ok_or_else(|| unsupported("Nat recursor identity"))?;
        let marker = FVarId(Name::num(name("_fln_runtime_nat_ih"), id));
        let major = variable(extra)?;
        let predecessor = call("Nat.pred", [major.clone()]);
        let hypothesis = Expr::app(variable(extra + 1)?, predecessor.clone());
        step = self.minor_apply(step, predecessor)?;
        step = self.minor_apply(step, Expr::fvar(marker.clone()))?;
        for index in (0..extra).rev() {
            let argument = variable(index)?;
            zero = self.minor_apply(zero, argument.clone())?;
            step = self.minor_apply(step, argument)?;
        }
        if step.has_fvar() {
            // Share the recursive result when it is used more than once. An
            // unused IH was eliminated by beta reduction above, so ordinary
            // matching on a huge Nat still needs only one predecessor step.
            let mut hypothesis_type = result_type.clone();
            for domain in domains[1..].iter().rev() {
                self.tick()?;
                hypothesis_type = Expr::forall_e(
                    Name::anonymous(),
                    domain.clone(),
                    hypothesis_type,
                    BinderInfo::Default,
                );
            }
            let body = step
                .lift_loose(0, 1)
                .and_then(|body| body.abstract_fvar(&marker, 0))
                .map_err(|_| unsupported("Nat hypothesis scope"))?;
            step = Expr::let_e(marker.0, hypothesis_type, hypothesis, body, false);
        }
        let motive = Expr::lam(
            Name::anonymous(),
            scalar(ValueType::Bool)?,
            result_type.clone(),
            BinderInfo::Default,
        );
        // The ordinary Boolean preparation creates lazy branch closures before
        // visiting their bodies, preserving every nested capture's indices.
        let mut body = [motive, step, zero, call("Nat.beq", [major, literal(0)])]
            .into_iter()
            .fold(
                Expr::const_(name("Bool.rec"), vec![Level::one()]),
                Expr::app,
            );
        let mut self_type = result_type;
        for domain in domains.iter().rev() {
            self.tick()?;
            let domain = domain.clone();
            body = Expr::lam(Name::anonymous(), domain.clone(), body, BinderInfo::Default);
            self_type = Expr::forall_e(Name::anonymous(), domain, self_type, BinderInfo::Default);
        }
        let lambda = Expr::lam(
            Name::num(name("_fln_runtime_nat_rec"), id),
            self_type,
            body,
            BinderInfo::Default,
        );
        Ok(Recursion {
            lambda,
            parameters,
            result,
        })
    }

    pub(super) fn register_recursion(
        &mut self,
        lambda: Expr,
        parameters: Vec<ValueType>,
        result: ValueType,
    ) -> Result<Expr, IngressError> {
        reserve(&mut self.lambdas, self.limits.max_lambda_bindings)?;
        self.lambdas.push(LambdaBinding {
            lambda: lambda.clone(),
            parameter_ownership: borrowed_runtime_parameters(parameters.len())?,
            parameters,
            result,
            result_ownership: result_ownership(result),
            recursion: LambdaRecursion::SelfBinder,
        });
        Ok(lambda)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_without_the_exact_admitted_family_never_select_scalar_erasure() {
        let environment = Environment::new();
        let input = Expr::const_(name("Nat.zero"), vec![]);
        assert!(matches!(
            Preparation::new(&environment, IngressLimits::default()).expression(&input),
            Err(IngressError::UnsupportedNode {
                kind: "noncanonical Nat family"
            })
        ));
        let application = call("Nat.succ", [literal(0)]);
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .expression(&application)
                .is_err()
        );
    }

    #[test]
    fn dependent_results_are_refused_and_callback_parameters_are_typed() {
        let environment = Environment::new();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        let dependent = Expr::lam(
            Name::anonymous(),
            scalar(ValueType::Nat).unwrap(),
            variable(0).unwrap(),
            BinderInfo::Default,
        );
        assert!(preparation.nat_motive(&dependent).is_err());
        let function = Expr::forall_e(
            Name::anonymous(),
            scalar(ValueType::Nat).unwrap(),
            scalar(ValueType::Nat).unwrap(),
            BinderInfo::Default,
        );
        let higher_order = Expr::lam(
            Name::anonymous(),
            scalar(ValueType::Nat).unwrap(),
            Expr::forall_e(
                Name::anonymous(),
                function,
                scalar(ValueType::Nat).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let motive = preparation.nat_motive(&higher_order).unwrap();
        assert_eq!(motive.parameters.len(), 2);
        assert_eq!(motive.parameters[0], ValueType::Nat);
        assert!(matches!(motive.parameters[1], ValueType::Closure(_)));
        assert_eq!(motive.result, ValueType::Nat);
    }

    #[test]
    fn motive_telescope_walk_is_metered() {
        let environment = Environment::new();
        let limits = IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        };
        let motive = Expr::lam(
            Name::anonymous(),
            scalar(ValueType::Nat).unwrap(),
            scalar(ValueType::Nat).unwrap(),
            BinderInfo::Default,
        );
        assert!(matches!(
            Preparation::new(&environment, limits).nat_motive(&motive),
            Err(IngressError::ResourceLimit { .. })
        ));
    }

    #[test]
    fn static_beta_and_let_motives_use_the_same_erased_telescope() {
        let environment = Environment::new();
        let family = scalar(ValueType::Nat).unwrap();
        let type_ = Expr::forall_e(
            Name::anonymous(),
            family.clone(),
            Expr::sort(Level::one()),
            BinderInfo::Default,
        );
        let literal = Expr::lam(
            Name::anonymous(),
            family.clone(),
            family.clone(),
            BinderInfo::Default,
        );
        let identity = Expr::lam(
            Name::anonymous(),
            type_.clone(),
            variable(0).unwrap(),
            BinderInfo::Default,
        );
        let motives = [
            literal.clone(),
            Expr::app(identity, literal.clone()),
            Expr::let_e(Name::anonymous(), type_, literal, variable(0).unwrap(), false),
        ];
        for expression in motives {
            let mut preparation = Preparation::new(&environment, IngressLimits::default());
            let motive = preparation.nat_motive(&expression).unwrap();
            assert_eq!(motive.parameters, vec![ValueType::Nat]);
            assert_eq!(motive.domains, vec![family.clone()]);
            assert_eq!(motive.result, ValueType::Nat);
            assert_eq!(motive.result_type, family);
        }
    }
}
