//! Compiler prerequisites of source function entry signatures.
//!
//! The pinned compiler projects proofs and type formers to lcErased and
//! abstract runtime carriers to lcAny (LCNF/Types.lean, MonoTypes.lean).
//! ToImpureType visits direct carriers through hasTrivialImpureStructure?,
//! which reads their declarations. Function-valued parameters are closures:
//! their nested domains/results do not require those marker declarations.
//!
//! This is a bounded prerequisite check over admitted types, not an execution
//! of definition bodies or a replacement for the ordinary runtime compiler.
//! Source checking still admits valid logical definitions without codegen.

use super::*;
use std::collections::BTreeSet;

/// Types with builtin runtime support that are never unboxed as trivial
/// single-field structures (`Lean/Compiler/LCNF/Util.lean:40-53`).
fn is_runtime_builtin_type(decl: &Name) -> bool {
    matches!(
        decl.to_display_string().as_str(),
        "String"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "USize"
            | "Float"
            | "Float32"
            | "Thunk"
            | "Task"
            | "Array"
            | "ByteArray"
            | "FloatArray"
            | "Nat"
            | "Int"
    )
}

struct TrivialStructureField {
    ctor_type: Expr,
    ctor_level_params: Vec<Name>,
    num_params: usize,
    field_index: usize,
}

#[derive(Clone, Copy)]
enum Marker {
    Any,
    Erased,
}

impl Marker {
    fn name(self) -> Name {
        name(match self {
            Self::Any => "lcAny",
            Self::Erased => "lcErased",
        })
    }
}

pub(crate) fn check(
    environment: &Environment,
    admission: &DeclarationBatchAdmission,
    limits: IngressLimits,
    noncomputable_section: bool,
) -> Result<Vec<usize>, EngineExecutionError> {
    // Ordinary imported Prelude worlds already provide both declarations.
    // Read this command's immutable world, never a global name/grammar cache.
    if environment.contains(&name("lcAny")) && environment.contains(&name("lcErased")) {
        return Ok(Vec::new());
    }
    let mut noncomputable = Vec::new();
    let mut preparation = Preparation::new(environment, limits);
    // LCNF/Types.lean normalizes types with transparency `all`, including
    // unsafe aliases. Fix the mode before any inference or memoized query;
    // this preparation never compiles or evaluates executable values.
    preparation.compiler_signature_type_aliases = true;
    let auxiliaries = preparation
        .compiler_aux_recursors()
        .map_err(EngineExecutionError::Ingress)?;
    let uncompiled_structure_helpers = preparation
        .uncompiled_structure_helpers(admission)
        .map_err(EngineExecutionError::Ingress)?;
    for (index, admitted) in admission.admissions.iter().enumerate() {
        if let Declaration::Inductive(block) = &admitted.declaration {
            // `compileInductives` runs unconditionally in `PassManager.run`
            // before `shouldGenerateCode`, even for `Prop` inductives and
            // inside `noncomputable section` (`LCNF/Main.lean:130-138`,
            // `LCNF/ToImpureType.lean:190-302`).
            if let Some(marker) = preparation
                .missing_inductive_compiler_constant(block)
                .map_err(EngineExecutionError::Ingress)?
            {
                return Err(EngineExecutionError::MissingCompilerConstant {
                    name: marker.name(),
                });
            }
            continue;
        }
        let base = match &admitted.declaration {
            Declaration::Defn(definition) => &definition.base,
            Declaration::Opaque(definition) => &definition.base,
            Declaration::Axiom(axiom)
                if preparation
                    .has_extern_attribute(&axiom.base.name)
                    .map_err(EngineExecutionError::Ingress)? =>
            {
                &axiom.base
            }
            _ => continue,
        };
        // The pin does not compile generated recOn/casesOn wrappers when
        // introducing their inductive, nor structure field projections, flat
        // constructors, or default helpers (`Meta/Structure.lean:104-113`,
        // `Elab/Structure.lean:1240,1385`). Copied non-subobject parent
        // projections (`Elab/Structure.lean:1429`) are still compiled.
        if auxiliaries.contains(&base.name) || uncompiled_structure_helpers.contains(&base.name) {
            continue;
        }
        if let Some(marker) = preparation
            .missing_compiler_signature_constant(base)
            .map_err(EngineExecutionError::Ingress)?
        {
            if noncomputable_section {
                // Only this established compiler failure is suppressible.
                // Metadata errors and resource stops above remain errors.
                reserve(&mut noncomputable, limits.max_nodes)
                    .map_err(EngineExecutionError::Ingress)?;
                noncomputable.push(index);
            } else {
                return Err(EngineExecutionError::MissingCompilerConstant {
                    name: marker.name(),
                });
            }
        }
    }
    Ok(noncomputable)
}

impl Preparation<'_> {
    /// Whether an already admitted declaration has no computational result at
    /// the pin's `shouldGenerateCode` boundary. Use a fresh type-only query so
    /// compiler transparency cannot change an executable preparation's caches.
    /// The returned work is charged to the caller's compilation budget even
    /// when the declaration needs no executable entry.
    pub(crate) fn computationally_irrelevant_header(
        environment: &Environment,
        type_: &Expr,
        limits: IngressLimits,
    ) -> Result<(bool, usize), IngressError> {
        let mut preparation = Preparation::new(environment, limits);
        preparation.compiler_signature_type_aliases = true;
        let irrelevant = preparation.compiler_irrelevant_type(type_)?;
        Ok((irrelevant, preparation.visited))
    }

    fn compiler_irrelevant_type(&mut self, type_: &Expr) -> Result<bool, IngressError> {
        Ok(self.type_parameter(type_)? || self.proposition_type(type_, &[])?)
    }

    fn uncompiled_structure_helpers(
        &mut self,
        admission: &DeclarationBatchAdmission,
    ) -> Result<BTreeSet<Name>, IngressError> {
        let mut helpers = BTreeSet::new();
        let has_inductive = admission
            .admissions
            .iter()
            .any(|admitted| matches!(admitted.declaration, Declaration::Inductive(_)));
        if !has_inductive {
            return Ok(helpers);
        }
        let structures = fln_elab::records::imported::ImportedStructures::read(self.environment)
            .map_err(|error| match error {
                fln_elab::records::RecordError::ResourceLimit => {
                    IngressError::MetadataResourceExhausted {
                        kind: "native imported-structures journal capacity",
                    }
                }
                _ => unsupported("malformed native imported-structures journal"),
            })?;
        let defaults = fln_elab::records::defaults::RecordDefaults::read(self.environment)
            .map_err(|error| match error {
                fln_elab::records::RecordError::ResourceLimit => {
                    IngressError::MetadataResourceExhausted {
                        kind: "native record-defaults journal capacity",
                    }
                }
                _ => unsupported("malformed native record-defaults journal"),
            })?;
        for admitted in &admission.admissions {
            let Declaration::Inductive(block) = &admitted.declaration else {
                continue;
            };
            for inductive in &block.types {
                let Some(entry) = structures.get(&inductive.base.name) else {
                    continue;
                };
                for (field_idx, field) in entry.fields.iter().enumerate() {
                    self.tick()?;
                    helpers.insert(field.projection.clone());
                    if let Ok(index) = u32::try_from(field_idx)
                        && let Some(default_helper) = defaults.helper(&inductive.base.name, index)
                    {
                        helpers.insert(default_helper.clone());
                    }
                }
                if let Some(ctor) = inductive.ctors.first() {
                    helpers.insert(Name::str(ctor.clone(), "_flat_ctor"));
                }
            }
        }
        Ok(helpers)
    }

    fn missing_inductive_compiler_constant(
        &mut self,
        block: &fln_kernel::InductiveBlock,
    ) -> Result<Option<Marker>, IngressError> {
        for inductive in &block.types {
            for ctor_name in &inductive.ctors {
                let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(ctor_name) else {
                    continue;
                };
                let mut context = Vec::new();
                let mut current = ctor.base.type_.clone();
                let total_binders = (ctor.num_params as usize)
                    .checked_add(ctor.num_fields as usize)
                    .ok_or_else(|| unsupported("constructor binder count overflow"))?;
                for binder_index in 0..total_binders {
                    self.tick()?;
                    let normal = self.type_head(&current)?;
                    let ExprNode::ForallE {
                        binder_type, body, ..
                    } = normal.node()
                    else {
                        break;
                    };
                    if binder_index >= ctor.num_params as usize
                        && let Some(marker) = self
                            .compiler_carrier_marker(binder_type, &context, 0)?
                            .filter(|marker| !self.environment.contains(&marker.name()))
                    {
                        return Ok(Some(marker));
                    }
                    self.proof_context_depth(context.len().saturating_add(1))?;
                    reserve(&mut context, self.limits.max_context_depth)?;
                    context.push(binder_type.clone());
                    current = body.clone();
                }
            }
        }
        Ok(None)
    }

    fn missing_compiler_signature_constant(
        &mut self,
        base: &fln_env::constants::ConstantVal,
    ) -> Result<Option<Marker>, IngressError> {
        // shouldGenerateCode does not compile proofs/type formers. The
        // original telescope is retained so local proposition carriers are
        // classified by their checked types, rather than identifier spelling.
        if self.is_noncomputable_name(&base.name)? || self.compiler_irrelevant_type(&base.type_)? {
            return Ok(None);
        }
        let external = self.has_extern_attribute(&base.name)?;
        if !external
            && (self.compiler_macro_inline(&base.name)?
                || self.implementations()?.get(&base.name).is_some())
        {
            return Ok(None);
        }
        let mut context = Vec::new();
        let mut current = base.type_.clone();
        let mut parameter_missing = None;
        loop {
            self.tick()?;
            let normal = self.type_head(&current)?;
            match normal.node() {
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let marker = self.compiler_carrier_marker(binder_type, &context, 0)?;
                    if parameter_missing.is_none() {
                        parameter_missing =
                            marker.filter(|marker| !self.environment.contains(&marker.name()));
                    }
                    self.proof_context_depth(context.len().saturating_add(1))?;
                    reserve(&mut context, self.limits.max_context_depth)?;
                    context.push(binder_type.clone());
                    current = body.clone();
                }
                _ => {
                    let result_missing = self
                        .compiler_carrier_marker(&normal, &context, 0)?
                        .filter(|marker| !self.environment.contains(&marker.name()));
                    // The polymorphic identity's reduced entry needs lcAny
                    // before its wrapper's erased parameter. Concrete-return
                    // entries retain the first missing parameter prerequisite.
                    return Ok(if external {
                        // Externs have their declared parameter array directly,
                        // without a reduced native entry preceding a wrapper.
                        parameter_missing.or(result_missing)
                    } else {
                        result_missing.or(parameter_missing)
                    });
                }
            }
        }
    }

    fn trivial_structure_relevant_field(
        &mut self,
        inductive: &fln_env::constants::InductiveVal,
    ) -> Result<Option<TrivialStructureField>, IngressError> {
        if is_runtime_builtin_type(&inductive.base.name)
            || inductive.is_unsafe
            || inductive.is_rec
            || inductive.ctors.len() != 1
        {
            return Ok(None);
        }
        if matches!(
            self.type_parameter_sort(&inductive.base.type_)?,
            Some(level) if level == fln_core::level::Level::zero()
        ) {
            return Ok(None);
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(&inductive.ctors[0]) else {
            return Ok(None);
        };
        let ctor_type = ctor.base.type_.clone();
        let ctor_level_params = ctor.base.level_params.clone();
        let num_params = ctor.num_params as usize;
        let mut context = Vec::new();
        let mut current = ctor_type.clone();
        let mut relevant: Option<usize> = None;
        let total_binders = num_params
            .checked_add(ctor.num_fields as usize)
            .ok_or_else(|| unsupported("constructor binder count overflow"))?;
        for binder_index in 0..total_binders {
            self.tick()?;
            let normal = self.type_head(&current)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if binder_index >= num_params {
                let irrelevant = self.type_parameter(binder_type)?
                    || self.proposition_type(binder_type, &context)?;
                if !irrelevant {
                    if relevant.is_some() {
                        return Ok(None);
                    }
                    relevant = Some(binder_index - num_params);
                }
            }
            self.proof_context_depth(context.len().saturating_add(1))?;
            reserve(&mut context, self.limits.max_context_depth)?;
            context.push(binder_type.clone());
            current = body.clone();
        }
        Ok(relevant.map(|field_index| TrivialStructureField {
            ctor_type,
            ctor_level_params,
            num_params,
            field_index,
        }))
    }

    fn compiler_carrier_marker(
        &mut self,
        type_: &Expr,
        context: &[Expr],
        unbox_depth: usize,
    ) -> Result<Option<Marker>, IngressError> {
        const MAX_UNBOX_DEPTH: usize = 32;
        if self.type_parameter(type_)? || self.proposition_type(type_, context)? {
            return Ok(Some(Marker::Erased));
        }
        let normal = self.type_head(type_)?;
        if matches!(normal.node(), ExprNode::ForallE { .. }) {
            // ToImpureType maps an arrow to a closure representation without
            // inspecting the runtime representation of its arguments.
            return Ok(None);
        }
        let (head, args) = self.spine(&normal)?;
        if let ExprNode::Const { name, levels } = head.node()
            && let Some(ConstantInfo::Induct(inductive)) = self.environment.find(name)
        {
            // ToImpureType unboxes trivial single-constructor single-relevant-field
            // structures (`LCNF/ToImpureType.lean:152-158`), so `Wrap Type` inspects
            // its unboxed field type (`Type` -> `lcErased`).
            if unbox_depth < MAX_UNBOX_DEPTH
                && let Some(trivial) = self.trivial_structure_relevant_field(inductive)?
                && args.len() >= trivial.num_params
            {
                let mut instantiated =
                    self.universe_instance(&trivial.ctor_type, &trivial.ctor_level_params, levels)?;
                let mut valid = true;
                for arg in args.iter().take(trivial.num_params) {
                    self.tick()?;
                    let head = self.type_head(&instantiated)?;
                    let ExprNode::ForallE { body, .. } = head.node() else {
                        valid = false;
                        break;
                    };
                    instantiated = self.substitution(body, arg)?;
                }
                if valid {
                    let mut field_context = context.to_vec();
                    let mut unboxed = None;
                    for step in 0..=trivial.field_index {
                        self.tick()?;
                        let head = self.type_head(&instantiated)?;
                        let ExprNode::ForallE {
                            binder_type, body, ..
                        } = head.node()
                        else {
                            break;
                        };
                        if step == trivial.field_index {
                            unboxed = Some(binder_type.clone());
                            break;
                        }
                        self.proof_context_depth(field_context.len().saturating_add(1))?;
                        reserve(&mut field_context, self.limits.max_context_depth)?;
                        field_context.push(binder_type.clone());
                        instantiated = body.clone();
                    }
                    if let Some(field_type) = unboxed {
                        return self.compiler_carrier_marker(
                            &field_type,
                            &field_context,
                            unbox_depth + 1,
                        );
                    }
                }
            }
            return Ok(None);
        }
        // A local type variable, abstract type axiom, stuck type projection,
        // or a type-family application has lost its dependency in mono code.
        Ok(Some(Marker::Any))
    }

    fn compiler_aux_recursors(
        &mut self,
    ) -> Result<fln_elab::aux_recursors::AuxRecursors, IngressError> {
        self.compiler_metadata_work(&fln_elab::aux_recursors::journal_name())?;
        fln_elab::aux_recursors::AuxRecursors::read(self.environment).map_err(|error| match error {
            fln_elab::aux_recursors::AuxRecursorError::Limit => {
                IngressError::MetadataResourceExhausted {
                    kind: "native auxiliary-recursor journal capacity",
                }
            }
            _ => unsupported("malformed native auxiliary-recursor journal"),
        })
    }

    fn compiler_macro_inline(&mut self, declaration: &Name) -> Result<bool, IngressError> {
        if self.macro_inline.is_none() {
            self.compiler_metadata_work(&fln_elab::macro_inline::journal_name())?;
            self.macro_inline = Some(fln_elab::macro_inline::read(self.environment).map_err(
                |error| match error {
                    fln_elab::macro_inline::MacroInlineError::Limit => {
                        IngressError::MetadataResourceExhausted {
                            kind: "native macro_inline journal capacity",
                        }
                    }
                    _ => unsupported("malformed native macro_inline journal"),
                },
            )?);
        }
        Ok(self
            .macro_inline
            .as_ref()
            .is_some_and(|names| names.contains(declaration)))
    }

    fn compiler_metadata_work(&mut self, journal: &Name) -> Result<(), IngressError> {
        if let Some(state) = self.environment.extension(journal) {
            for entry in state.entries() {
                let observed = self
                    .visited
                    .saturating_add(1)
                    .saturating_add(entry.payload.len());
                if observed > self.limits.max_nodes {
                    return Err(IngressError::ResourceLimit {
                        resource: IngressResource::Nodes,
                        limit: self.limits.max_nodes,
                        observed,
                    });
                }
                self.visited = observed;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;
    use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};

    #[test]
    fn compiler_type_transparency_is_isolated_and_resource_bounded() {
        let proposition = Expr::sort(Level::zero());
        let mut environment = Environment::new();
        for (label, safety, value) in [
            ("UnsafeAlias", DefinitionSafety::Unsafe, proposition.clone()),
            (
                "PartialAlias",
                DefinitionSafety::Partial,
                proposition.clone(),
            ),
            (
                "RecursiveAlias",
                DefinitionSafety::Unsafe,
                Expr::const_(name("RecursiveAlias"), Vec::new()),
            ),
        ] {
            environment = environment
                .add_decl(ConstantInfo::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: name(label),
                        level_params: Vec::new(),
                        type_: Expr::sort(Level::one()),
                    },
                    value,
                    hints: ReducibilityHints::Opaque,
                    safety,
                    all: Vec::new(),
                }))
                .unwrap();
        }
        let alias = Expr::const_(name("UnsafeAlias"), Vec::new());
        let partial = Expr::const_(name("PartialAlias"), Vec::new());
        let mut ordinary = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(ordinary.type_head(&alias).unwrap(), alias);
        let mut signature = Preparation::new(&environment, IngressLimits::default());
        signature.compiler_signature_type_aliases = true;
        assert_eq!(signature.type_head(&alias).unwrap(), proposition);
        assert_eq!(signature.type_head(&partial).unwrap(), partial);
        // Neither the admitted world nor an existing ordinary memo table was
        // changed by the more transparent signature query.
        assert_eq!(ordinary.type_head(&alias).unwrap(), alias);
        assert_eq!(
            Preparation::new(&environment, IngressLimits::default())
                .type_head(&alias)
                .unwrap(),
            alias,
        );

        let mut bounded = Preparation::new(
            &environment,
            IngressLimits {
                max_nodes: 64,
                ..IngressLimits::default()
            },
        );
        bounded.compiler_signature_type_aliases = true;
        assert!(matches!(
            bounded.type_head(&Expr::const_(name("RecursiveAlias"), Vec::new())),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            }),
        ));
    }
}
