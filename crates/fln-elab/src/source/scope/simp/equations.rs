//! Checked-source candidates for the pin's nonrecursive, split-free `eq_1`.
//!
//! This module never publishes a declaration. `prepare` returns an ordinary
//! theorem candidate; the engine must admit it through both checkers before
//! `finish` records realization and selection metadata. Definition-time facts
//! are frozen separately, so a later attribute cannot reinterpret visibility
//! or the options under which the definition was elaborated.
use super::super::super::*;
use super::SimpSetError;
use fln_core::name::LeafView;
use fln_core::options::DataValue;
use fln_env::constants::{ConstantInfo, DefinitionSafety, DefinitionVal, TheoremVal};
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, HashSet};

const MAGIC: &[u8] = b"FLNEQNS\x01";
const MAX_ROWS: usize = 1 << 16;
const MAX_BYTES: usize = 16 * 1024;
const MAX_WORK: usize = 1 << 20;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Policy {
    exposed: bool,
    nonrecursive: bool,
    deep_recursive_split: bool,
    use_backward: bool,
}

#[derive(Debug, Default)]
struct State {
    definitions: BTreeMap<Name, Policy>,
    generated: BTreeMap<Name, bool>,
}

/// Native realization facts, not a portable declaration or a trusted proof.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceEquations", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

fn failure_set(error: SimpSetError) -> NatDefinitionElabError {
    failure(SourceInferenceError::SimpSet(error))
}

fn codec(error: crate::instances::InstanceRegistryError) -> SimpSetError {
    match error {
        crate::instances::InstanceRegistryError::Limit => SimpSetError::Limit,
        _ => SimpSetError::Malformed,
    }
}

fn charge(remaining: &mut usize, amount: usize) -> Result<(), SimpSetError> {
    *remaining = remaining.checked_sub(amount).ok_or(SimpSetError::Limit)?;
    Ok(())
}

fn read(env: &Environment, remaining: &mut usize) -> Result<State, SimpSetError> {
    let mut result = State::default();
    let expected = descriptor();
    let Some(state) = env.extension(&expected.name) else {
        return Ok(result);
    };
    if state.descriptor != expected {
        return Err(SimpSetError::Malformed);
    }
    if state.len() > MAX_ROWS || state.payload_bytes() > (MAX_ROWS * MAX_BYTES) as u128 {
        return Err(SimpSetError::Limit);
    }
    for row in state.entries() {
        if row.payload.len() > MAX_BYTES {
            return Err(SimpSetError::Limit);
        }
        charge(remaining, 1 + row.payload.len())?;
        let mut bytes = row
            .payload
            .strip_prefix(MAGIC)
            .ok_or(SimpSetError::Malformed)?;
        let (&operation, rest) = bytes.split_first().ok_or(SimpSetError::Malformed)?;
        bytes = rest;
        let origin = crate::instances::read_name(&mut bytes).map_err(codec)?;
        let Some(ConstantInfo::Defn(_)) = env.find(&origin) else {
            return Err(SimpSetError::UnknownDeclaration(origin));
        };
        let [flags] = bytes else {
            return Err(SimpSetError::Malformed);
        };
        match operation {
            0 if *flags & !15 == 0 => {
                let policy = Policy {
                    exposed: flags & 1 != 0,
                    nonrecursive: flags & 2 != 0,
                    deep_recursive_split: flags & 4 != 0,
                    use_backward: flags & 8 != 0,
                };
                if result.definitions.insert(origin, policy).is_some() {
                    return Err(SimpSetError::Malformed);
                }
            }
            1 if *flags <= 1 => {
                let Some(policy) = result.definitions.get(&origin) else {
                    return Err(SimpSetError::Malformed);
                };
                let theorem = Name::str(origin.clone(), "eq_1");
                if !policy.exposed
                    || !policy.nonrecursive
                    || !matches!(env.find(&origin), Some(ConstantInfo::Defn(d))
                        if d.safety == DefinitionSafety::Safe)
                    || !matches!(env.find(&theorem), Some(ConstantInfo::Thm(t))
                        if t.all.as_slice() == std::slice::from_ref(&theorem))
                    || result.generated.insert(origin, *flags == 1).is_some()
                {
                    return Err(SimpSetError::Malformed);
                }
            }
            _ => return Err(SimpSetError::Malformed),
        }
    }
    Ok(result)
}

/// Validate a native realization journal before persisting/projecting it.
/// No declaration authority or portable simp event is inferred from this row.
pub fn validate(env: &Environment, max_work: usize) -> Result<(), SimpSetError> {
    let mut remaining = max_work;
    read(env, &mut remaining).map(|_| ())
}

fn scan_bounded(expression: &Expr, remaining: &mut usize) -> Result<(), SimpSetError> {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        charge(remaining, 1)?;
        if !seen.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(())
}

/// Compare the generated shape independently of the cached record. The Eq
/// carrier and universe come from the already admitted theorem; typing those
/// fields is the checkers' job. Every name, binder, side and proof constructor
/// must otherwise agree exactly with the original definition.
fn exact_shape(
    env: &Environment,
    definition: &DefinitionVal,
    theorem: &TheoremVal,
    remaining: &mut usize,
) -> Result<bool, SimpSetError> {
    let name = Name::str(definition.base.name.clone(), "eq_1");
    if theorem.base.name != name
        || theorem.base.level_params != definition.base.level_params
        || theorem.all.as_slice() != std::slice::from_ref(&name)
        || definition.safety != DefinitionSafety::Safe
        || definition.all.as_slice() != std::slice::from_ref(&definition.base.name)
    {
        return Ok(false);
    }
    if !split_free(env, definition, || charge(remaining, 1))? {
        return Ok(false);
    }
    for term in [&definition.value, &theorem.base.type_, &theorem.value] {
        scan_bounded(term, remaining)?;
    }
    let mut rhs = definition.value.clone();
    let mut type_ = &theorem.base.type_;
    let mut value = &theorem.value;
    let mut binders = 0u32;
    while let ExprNode::Lam {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = rhs.node()
    {
        charge(remaining, 1)?;
        let ExprNode::ForallE {
            binder_name: type_name,
            binder_type: domain,
            body: target,
            binder_info: type_info,
        } = type_.node()
        else {
            return Ok(false);
        };
        let ExprNode::Lam {
            binder_name: proof_name,
            binder_type: proof_domain,
            body: proof,
            binder_info: proof_info,
        } = value.node()
        else {
            return Ok(false);
        };
        let cleaned = cleanup_annotations(binder_type.clone(), || charge(remaining, 1))?;
        if type_name != binder_name
            || proof_name != binder_name
            || *domain != cleaned
            || *proof_domain != cleaned
            || type_info != binder_info
            || proof_info != binder_info
        {
            return Ok(false);
        }
        rhs = body.clone();
        type_ = target;
        value = proof;
        binders = binders.checked_add(1).ok_or(SimpSetError::Limit)?;
    }
    loop {
        charge(remaining, 1)?;
        match rhs.node() {
            ExprNode::LetE { value, body, .. } => {
                scan_bounded(body, remaining)?;
                rhs = body
                    .subst_loose(0, std::slice::from_ref(value))
                    .map_err(|_| SimpSetError::Limit)?;
            }
            ExprNode::MData { expr, .. } => rhs = expr.clone(),
            _ => break,
        }
    }
    let mut arguments = Vec::new();
    let mut head = type_;
    while let ExprNode::App { f, a } = head.node() {
        charge(remaining, 1)?;
        arguments.push(a);
        head = f;
    }
    let ExprNode::Const {
        name: equality,
        levels,
    } = head.node()
    else {
        return Ok(false);
    };
    if equality != &Name::from_components(["Eq"]) || levels.len() != 1 || arguments.len() != 3 {
        return Ok(false);
    }
    let mut lhs = Expr::const_(
        definition.base.name.clone(),
        definition
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect(),
    );
    for index in (0..binders).rev() {
        charge(remaining, 1)?;
        lhs = Expr::app(lhs, Expr::bvar(index).map_err(|_| SimpSetError::Limit)?);
    }
    if arguments[0] != &rhs || arguments[1] != &lhs {
        return Ok(false);
    }
    let expected = [arguments[2].clone(), lhs].into_iter().fold(
        Expr::const_(Name::from_components(["Eq", "refl"]), levels.clone()),
        Expr::app,
    );
    Ok(value == &expected)
}

fn generated_shape(
    env: &Environment,
    origin: &Name,
    remaining: &mut usize,
) -> Result<(), SimpSetError> {
    let theorem = Name::str(origin.clone(), "eq_1");
    let (Some(ConstantInfo::Defn(definition)), Some(ConstantInfo::Thm(equation))) =
        (env.find(origin), env.find(&theorem))
    else {
        return Err(SimpSetError::Malformed);
    };
    if !exact_shape(env, definition, equation, remaining)? {
        return Err(SimpSetError::Malformed);
    }
    Ok(())
}

fn from_elab(error: NatDefinitionElabError) -> SimpSetError {
    match error {
        NatDefinitionElabError::Inference(SourceInferenceError::SimpSet(error)) => error,
        NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit) => {
            SimpSetError::Limit
        }
        _ => SimpSetError::Malformed,
    }
}

/// Check portable meaning and return charged work. The pin's eqnOptionsExt is
/// persistent and stores nondefaults; until its codec exists we must refuse
/// such rows even when no simp attribute requested their equations. Defaults
/// produce no pin row. Its eqnsExt inverse map is nonpersistent: imported
/// getEqnsFor? reconstructs it from the real f.eq_1,... declarations instead.
pub fn validate_export(env: &Environment, max_work: usize) -> Result<usize, SimpSetError> {
    let mut remaining = max_work;
    let state = read(env, &mut remaining)?;
    for (name, policy) in &state.definitions {
        charge(&mut remaining, 1)?;
        if !policy.nonrecursive || !policy.deep_recursive_split || policy.use_backward {
            return Err(SimpSetError::UnsupportedDeclaration(name.clone()));
        }
    }
    let strict = super::defeq::read(env, || charge(&mut remaining, 1).map_err(failure_set))
        .map_err(from_elab)?;
    let backward =
        super::defeq::read_backward(env, || charge(&mut remaining, 1).map_err(failure_set))
            .map_err(from_elab)?;
    for (origin, reflexive) in &state.generated {
        generated_shape(env, origin, &mut remaining)?;
        let theorem = Name::str(origin.clone(), "eq_1");
        if strict.contains(&theorem) != *reflexive || !backward.contains(&theorem) {
            return Err(SimpSetError::Malformed);
        }
    }
    Ok(max_work - remaining)
}

fn append(
    env: &Environment,
    origin: &Name,
    operation: u8,
    flags: u8,
) -> Result<Environment, SimpSetError> {
    let mut payload = MAGIC.to_vec();
    payload.push(operation);
    crate::instances::write_name(origin, &mut payload).map_err(codec)?;
    payload.push(flags);
    if payload.len() > MAX_BYTES {
        return Err(SimpSetError::Limit);
    }
    let expected = descriptor();
    let env = match env.extension(&expected.name) {
        Some(state) if state.descriptor != expected => return Err(SimpSetError::Malformed),
        Some(state) if state.len() >= MAX_ROWS => return Err(SimpSetError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(expected.clone())
            .map_err(|_| SimpSetError::Malformed)?,
    };
    env.push_extension_entry(&expected.name, payload)
        .map_err(|_| SimpSetError::Malformed)
}

fn option(
    scope: &SourceScope,
    options: &KVMap,
    label: &str,
    default: bool,
) -> Result<bool, NatDefinitionElabError> {
    let name = Name::from_components(label.split('.'));
    match scope.options.find(&name).or_else(|| options.find(&name)) {
        Some(DataValue::OfBool(value)) => Ok(*value),
        None => Ok(default),
        Some(_) => Err(failure_set(SimpSetError::Malformed)),
    }
}

/// Freeze exactly once on the successor of the primary definition's admission.
/// The lexical options override embedding options, as source elaboration does.
pub fn freeze_definition(
    env: &Environment,
    name: &Name,
    scope: &SourceScope,
    options: &KVMap,
    _kernel: Budget,
) -> Result<Environment, NatDefinitionElabError> {
    if !matches!(env.find(name), Some(ConstantInfo::Defn(_))) {
        return Ok(env.clone());
    }
    let mut remaining = MAX_WORK;
    let state = read(env, &mut remaining).map_err(failure_set)?;
    // Reusing the first definition-time policy is deliberate: a later source
    // command's options/section defaults cannot overwrite realization facts.
    if state.definitions.contains_key(name) {
        return Ok(env.clone());
    }
    let exposed =
        scope.private_module.is_none() || scope.public_declarations && scope.expose_definitions;
    let policy = Policy {
        exposed,
        nonrecursive: option(scope, options, "backward.eqns.nonrecursive", true)?,
        deep_recursive_split: option(scope, options, "backward.eqns.deepRecursiveSplit", true)?,
        use_backward: option(scope, options, "backward.defeqAttrib.useBackward", false)?,
    };
    let flags = u8::from(policy.exposed)
        | u8::from(policy.nonrecursive) << 1
        | u8::from(policy.deep_recursive_split) << 2
        | u8::from(policy.use_backward) << 3;
    // The pin persists only nondefault options. Avoid adding native-only
    // state to every ordinary library's logical root; the engine may authorize
    // default realization separately for a definition this source owns.
    if flags == 7 {
        return Ok(env.clone());
    }
    append(env, name, 0, flags).map_err(failure_set)
}

/// A complete untrusted proof candidate. An existing theorem is reusable only
/// after both the realization record and its exact declaration have matched.
#[derive(Debug, Clone, PartialEq)]
pub struct Candidate {
    pub declaration: Declaration,
    pub existing: bool,
    pub origin: Name,
    policy: Policy,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Preparation {
    NotRequired,
    Unsupported,
    Ready(Candidate),
}

/// A conservative boundary for `mkEqnTypes`: native pattern matches and
/// recursion currently lower to eliminators instead of the pin's named
/// matchers. Such terms must not be mistaken for a single unsplit equation.
fn split_free<E>(
    env: &Environment,
    definition: &DefinitionVal,
    mut tick: impl FnMut() -> Result<(), E>,
) -> Result<bool, E> {
    if definition.all.as_slice() != std::slice::from_ref(&definition.base.name)
        || definition.value.has_fvar()
        || definition.value.has_expr_mvar()
        || definition.value.has_level_mvar()
        || definition.value.has_loose_bvars()
    {
        return Ok(false);
    }
    let mut pending = vec![&definition.value, &definition.base.type_];
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        tick()?;
        if !seen.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::Const { name, .. } => {
                let auxiliary = matches!(name.leaf_view(), LeafView::Str(suffix)
                    if suffix.starts_with("match_") || matches!(suffix, "brecOn" | "brecOn.go" | "casesOn" | "recOn"));
                if name == &definition.base.name
                    || auxiliary
                    || name == &Name::from_components(["WellFounded", "fix"])
                    || matches!(env.find(name), Some(ConstantInfo::Rec(_)))
                {
                    return Ok(false);
                }
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                ..
            } => {
                if recursion::structural_obligation_parameters(decl_name).is_some() {
                    return Ok(false);
                }
                pending.extend([type_, value, body]);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(true)
}

fn cleanup_annotations<E>(
    mut expression: Expr,
    mut tick: impl FnMut() -> Result<(), E>,
) -> Result<Expr, E> {
    loop {
        tick()?;
        if let ExprNode::MData { expr, .. } = expression.node() {
            expression = expr.clone();
            continue;
        }
        let mut head = &expression;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            tick()?;
            arguments.push(a.clone());
            head = f;
        }
        if let ExprNode::Const { name, .. } = head.node() {
            if arguments.len() == 2
                && ["optParam", "autoParam"]
                    .iter()
                    .any(|label| name == &Name::from_components([*label]))
            {
                expression = arguments[1].clone();
                continue;
            }
            if arguments.len() == 1
                && ["outParam", "semiOutParam"]
                    .iter()
                    .any(|label| name == &Name::from_components([*label]))
            {
                expression = arguments[0].clone();
                continue;
            }
        }
        return Ok(expression);
    }
}

fn build(
    env: &Environment,
    definition: &DefinitionVal,
    kernel: Budget,
) -> Result<Option<TheoremVal>, NatDefinitionElabError> {
    let mut remaining = MAX_WORK;
    if !split_free(env, definition, || charge(&mut remaining, 1)).map_err(failure_set)? {
        return Ok(None);
    }
    let Some(candidate) = super::super::super::equation_theorems::simple_equation_candidate(
        env,
        &definition.base.name,
        kernel,
    )?
    else {
        return Ok(None);
    };
    let Declaration::Thm(theorem) = candidate else {
        return Err(failure_set(SimpSetError::Malformed));
    };
    if !exact_shape(env, definition, &theorem, &mut remaining).map_err(failure_set)? {
        return Err(failure_set(SimpSetError::Malformed));
    }
    Ok(Some(theorem))
}

/// Prepare one real proof without changing the environment. Unsupported static
/// shapes preserve ordinary source simp's existing fallback; errors never do.
pub fn prepare(
    env: &Environment,
    origin: &Name,
    kernel: Budget,
) -> Result<Preparation, NatDefinitionElabError> {
    prepare_inner(env, origin, kernel, false)
}

/// The source engine proves that this declaration belongs to the current file
/// (or was just admitted). Only that boundary may interpret absent sparse
/// policy as the source-time default. Imported definitions use `prepare`.
pub fn prepare_owned(
    env: &Environment,
    origin: &Name,
    kernel: Budget,
) -> Result<Preparation, NatDefinitionElabError> {
    prepare_inner(env, origin, kernel, true)
}

/// Default, source-owned nonrecursive matches use their checked pattern
/// equations too. These candidates never acquire simple-equation provenance:
/// the persistent writer still has to account for their distinct shape.
pub fn prepare_pattern_owned(
    env: &Environment,
    origin: &Name,
    kernel: Budget,
) -> Result<Vec<(Declaration, bool)>, NatDefinitionElabError> {
    let mut meter = super::export::Meter {
        remaining: MAX_WORK,
        bytes: 0,
    };
    let state = read(env, &mut meter.remaining).map_err(failure_set)?;
    // Nondefault definition-time policies need their own pattern producer.
    // An unsupported simple preparation must not erase one of those policies.
    if state.definitions.contains_key(origin)
        || state.generated.contains_key(origin)
        || super::export::known_status(env, origin, &mut meter).map_err(failure_set)?
            == Some(crate::reducibility::Reducibility::Irreducible)
    {
        return Ok(Vec::new());
    }
    let Some(candidates) =
        crate::source::equation_theorems::pattern_equation_candidates(env, origin, kernel)?
    else {
        return Ok(Vec::new());
    };
    let mut prepared = Vec::new();
    for candidate in candidates {
        charge(&mut meter.remaining, 1).map_err(failure_set)?;
        let Declaration::Thm(theorem) = &candidate else {
            return Err(failure_set(SimpSetError::Malformed));
        };
        let existing = match env.find(&theorem.base.name) {
            None => false,
            Some(ConstantInfo::Thm(actual)) if actual.base == theorem.base => true,
            Some(_) => {
                return Err(failure_set(SimpSetError::UnsupportedDeclaration(
                    theorem.base.name.clone(),
                )));
            }
        };
        prepared.push((candidate, existing));
    }
    Ok(prepared)
}

fn prepare_inner(
    env: &Environment,
    origin: &Name,
    kernel: Budget,
    owned: bool,
) -> Result<Preparation, NatDefinitionElabError> {
    let Some(info) = env.find(origin) else {
        return Err(failure_set(SimpSetError::UnknownDeclaration(
            origin.clone(),
        )));
    };
    let ConstantInfo::Defn(definition) = info else {
        return Ok(Preparation::NotRequired);
    };
    if definition.safety != DefinitionSafety::Safe {
        return Ok(Preparation::Unsupported);
    }
    let mut meter = super::export::Meter {
        remaining: MAX_WORK,
        bytes: 0,
    };
    match super::export::definition_type_is_proposition(env, &definition.base.type_, &mut meter) {
        Ok(true) => return Ok(Preparation::NotRequired),
        Ok(false) => {}
        // An unsupported type reconstruction cannot establish that this is a
        // data-valued definition. Preserve source fallback without a guessed
        // equation; resource and malformed-state errors remain nonanswers.
        Err(SimpSetError::UnsupportedDeclaration(_)) => return Ok(Preparation::Unsupported),
        Err(error) => return Err(failure_set(error)),
    }
    let status = super::export::known_status(env, origin, &mut meter).map_err(failure_set)?;
    if status == Some(crate::reducibility::Reducibility::Reducible)
        || super::export::registered_projection(env, origin, &mut meter).map_err(failure_set)?
    {
        return Ok(Preparation::NotRequired);
    }
    let state = read(env, &mut meter.remaining).map_err(failure_set)?;
    // At first realization an irreducible function needs deltaLHS and an id
    // checkpoint in the pin's proof, rather than the bare Eq.refl below. A
    // later change must not invalidate a theorem already realized earlier.
    if status == Some(crate::reducibility::Reducibility::Irreducible)
        && !state.generated.contains_key(origin)
    {
        return Ok(Preparation::Unsupported);
    }
    let default = Policy {
        exposed: true,
        nonrecursive: true,
        deep_recursive_split: true,
        use_backward: false,
    };
    let Some(policy) = state
        .definitions
        .get(origin)
        .copied()
        .or(owned.then_some(default))
    else {
        return Ok(Preparation::Unsupported);
    };
    // Non-default nonrecursive=false selects mkSimpleEqThm/letToHave instead
    // of mkEqnTypes. That distinct statement transformation is not guessed.
    if !policy.exposed || !policy.nonrecursive {
        return Ok(Preparation::Unsupported);
    }
    if !env.contains(&Name::from_components(["Eq"]))
        || !env.contains(&Name::from_components(["Eq", "refl"]))
    {
        return Ok(Preparation::Unsupported);
    }
    let theorem_name = Name::str(origin.clone(), "eq_1");
    let (theorem, existing) = if state.generated.contains_key(origin) {
        match env.find(&theorem_name) {
            None => return Err(failure_set(SimpSetError::Malformed)),
            Some(ConstantInfo::Thm(actual)) => {
                if !exact_shape(env, definition, actual, &mut meter.remaining)
                    .map_err(failure_set)?
                {
                    return Err(failure_set(SimpSetError::Malformed));
                }
                (actual.clone(), true)
            }
            Some(_) => {
                return Err(failure_set(SimpSetError::UnsupportedDeclaration(
                    theorem_name,
                )));
            }
        }
    } else {
        // Matcher and recursive equations can already have been realized by
        // the source equation producer. Their existence must not turn this
        // simple-equation boundary's ordinary unsupported fallback into a
        // collision error. Classify the owner before claiming its eq_1 name.
        let Some(theorem) = build(env, definition, kernel)? else {
            return Ok(Preparation::Unsupported);
        };
        // For a supported simple owner, a same-named theorem still provides
        // no authority to adopt an independently admitted declaration.
        if env.contains(&theorem_name) {
            return Err(failure_set(SimpSetError::UnsupportedDeclaration(
                theorem_name,
            )));
        }
        (theorem, false)
    };
    Ok(Preparation::Ready(Candidate {
        declaration: Declaration::Thm(theorem),
        existing,
        origin: origin.clone(),
        policy,
    }))
}

/// Record a completed, checked candidate; never creates or replaces constants.
pub fn finish(
    env: &Environment,
    candidate: &Candidate,
    kernel: Budget,
) -> Result<Environment, NatDefinitionElabError> {
    let Declaration::Thm(theorem) = &candidate.declaration else {
        return Err(failure_set(SimpSetError::Malformed));
    };
    if !matches!(env.find(&theorem.base.name), Some(ConstantInfo::Thm(actual)) if actual == theorem)
    {
        return Err(failure_set(SimpSetError::Malformed));
    }
    let mut remaining = MAX_WORK;
    let state = read(env, &mut remaining).map_err(failure_set)?;
    let policy = state
        .definitions
        .get(&candidate.origin)
        .copied()
        .unwrap_or(candidate.policy);
    if policy != candidate.policy {
        return Err(failure_set(SimpSetError::Malformed));
    }
    if !policy.exposed || !policy.nonrecursive {
        return Err(failure_set(SimpSetError::Malformed));
    }
    let Some(ConstantInfo::Defn(definition)) = env.find(&candidate.origin) else {
        return Err(failure_set(SimpSetError::Malformed));
    };
    if !exact_shape(env, definition, theorem, &mut remaining).map_err(failure_set)?
        || candidate.existing != state.generated.contains_key(&candidate.origin)
    {
        return Err(failure_set(SimpSetError::Malformed));
    }
    let mut env = if state.definitions.contains_key(&candidate.origin) {
        env.clone()
    } else {
        append(env, &candidate.origin, 0, 7).map_err(failure_set)?
    };
    if !candidate.existing {
        // The same generated-theorem inference serves lazy eq_1 references,
        // rw[f], matcher equations and simp realization. Existing tags remain
        // sticky when later reducibility changes affect conversion.
        env = super::defeq::infer_generated(&env, &theorem.base.name, kernel)?;
    }
    let mut context = Context::new(&env, kernel);
    let strict = super::defeq::read(&env, || context.tick())?;
    let backward = super::defeq::read_backward(&env, || context.tick())?;
    let reflexive = strict.contains(&theorem.base.name);
    if !backward.contains(&theorem.base.name)
        || state
            .generated
            .get(&candidate.origin)
            .is_some_and(|recorded| *recorded != reflexive)
    {
        return Err(failure_set(SimpSetError::Malformed));
    }
    if !candidate.existing {
        env = append(&env, &candidate.origin, 1, u8::from(reflexive)).map_err(failure_set)?;
    }
    Ok(env)
}

/// Export may unfold an ordinary definition only after actual realization.
pub(super) fn generated(
    env: &Environment,
    origin: &Name,
    meter: &mut super::export::Meter,
) -> Result<bool, SimpSetError> {
    let state = read(env, &mut meter.remaining)?;
    if !state.generated.contains_key(origin) {
        return Ok(false);
    }
    generated_shape(env, origin, &mut meter.remaining)?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use fln_env::constants::ReducibilityHints;

    fn n(label: &str) -> Name {
        Name::from_components(label.split('.'))
    }

    fn fixture() -> (DefinitionVal, TheoremVal) {
        let u = Level::param(n("u"));
        let alpha = Expr::bvar(1).unwrap();
        let x = Expr::bvar(0).unwrap();
        let lhs = [alpha.clone(), x.clone()]
            .into_iter()
            .fold(Expr::const_(n("wrap"), vec![u.clone()]), Expr::app);
        let telescope = |body, lambda| {
            let binder = |name, type_, body, info| {
                if lambda {
                    Expr::lam(name, type_, body, info)
                } else {
                    Expr::forall_e(name, type_, body, info)
                }
            };
            binder(
                n("A"),
                Expr::sort(u.clone()),
                binder(n("x"), Expr::bvar(0).unwrap(), body, BinderInfo::Default),
                BinderInfo::Implicit,
            )
        };
        let definition = DefinitionVal {
            base: ConstantVal {
                name: n("wrap"),
                level_params: vec![n("u")],
                type_: telescope(alpha.clone(), false),
            },
            value: telescope(
                Expr::let_e(
                    n("y"),
                    alpha.clone(),
                    x.clone(),
                    Expr::bvar(0).unwrap(),
                    false,
                ),
                true,
            ),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![n("wrap")],
        };
        let target = [alpha.clone(), lhs.clone(), x]
            .into_iter()
            .fold(Expr::const_(n("Eq"), vec![u.clone()]), Expr::app);
        let proof = [alpha, lhs]
            .into_iter()
            .fold(Expr::const_(n("Eq.refl"), vec![u.clone()]), Expr::app);
        let theorem = TheoremVal {
            base: ConstantVal {
                name: n("wrap.eq_1"),
                level_params: vec![n("u")],
                type_: telescope(target, false),
            },
            value: telescope(proof, true),
            all: vec![n("wrap.eq_1")],
        };
        (definition, theorem)
    }

    #[test]
    fn exact_shape_keeps_dependent_universes_and_zeta_reduces_rhs_lets() {
        let (definition, theorem) = fixture();
        let mut remaining = MAX_WORK;
        assert_eq!(
            exact_shape(&Environment::new(), &definition, &theorem, &mut remaining),
            Ok(true)
        );
    }

    #[test]
    fn equivalent_but_different_reflexivity_body_is_not_generated_provenance() {
        let (definition, mut theorem) = fixture();
        // This is also a kernel-valid proof of the equality, but it is not the
        // pinned generated proof Eq.refl (wrap A x). Proof irrelevance must not
        // launder an arbitrary existing theorem into realization provenance.
        let u = Level::param(n("u"));
        let proof = [Expr::bvar(1).unwrap(), Expr::bvar(0).unwrap()]
            .into_iter()
            .fold(Expr::const_(n("Eq.refl"), vec![u.clone()]), Expr::app);
        theorem.value = Expr::lam(
            n("A"),
            Expr::sort(u),
            Expr::lam(n("x"), Expr::bvar(0).unwrap(), proof, BinderInfo::Default),
            BinderInfo::Implicit,
        );
        let mut remaining = MAX_WORK;
        assert_eq!(
            exact_shape(&Environment::new(), &definition, &theorem, &mut remaining),
            Ok(false)
        );
    }

    #[test]
    fn provenance_scan_exhaustion_is_a_nonanswer() {
        let (definition, theorem) = fixture();
        assert_eq!(
            exact_shape(&Environment::new(), &definition, &theorem, &mut 1),
            Err(SimpSetError::Limit)
        );
    }
}
