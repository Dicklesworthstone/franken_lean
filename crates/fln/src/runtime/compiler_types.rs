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
    let auxiliaries = preparation
        .compiler_aux_recursors()
        .map_err(EngineExecutionError::Ingress)?;
    for (index, admitted) in admission.admissions.iter().enumerate() {
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
        // introducing their inductive. Only their admitted metadata grants
        // this exemption; a user's identically suffixed function still compiles.
        if auxiliaries.contains(&base.name) {
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
    fn missing_compiler_signature_constant(
        &mut self,
        base: &fln_env::constants::ConstantVal,
    ) -> Result<Option<Marker>, IngressError> {
        // shouldGenerateCode does not compile proofs/type formers. The
        // original telescope is retained so local proposition carriers are
        // classified by their checked types, rather than identifier spelling.
        if self.is_noncomputable_name(&base.name)?
            || self.type_parameter(&base.type_)?
            || self.proposition_type(&base.type_, &[])?
        {
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
                    let marker = self.compiler_carrier_marker(binder_type, &context)?;
                    if parameter_missing.is_none() {
                        parameter_missing = marker.filter(|marker| {
                            !self.environment.contains(&marker.name())
                        });
                    }
                    self.proof_context_depth(context.len().saturating_add(1))?;
                    reserve(&mut context, self.limits.max_context_depth)?;
                    context.push(binder_type.clone());
                    current = body.clone();
                }
                _ => {
                    let result_missing = self
                        .compiler_carrier_marker(&normal, &context)?
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

    fn compiler_carrier_marker(
        &mut self,
        type_: &Expr,
        context: &[Expr],
    ) -> Result<Option<Marker>, IngressError> {
        if self.type_parameter(type_)? || self.proposition_type(type_, context)? {
            return Ok(Some(Marker::Erased));
        }
        let normal = self.type_head(type_)?;
        if matches!(normal.node(), ExprNode::ForallE { .. }) {
            // ToImpureType maps an arrow to a closure representation without
            // inspecting the runtime representation of its arguments.
            return Ok(None);
        }
        let (head, _) = self.spine(&normal)?;
        if let ExprNode::Const { name, .. } = head.node()
            && matches!(self.environment.find(name), Some(ConstantInfo::Induct(_)))
        {
            // A checked inductive has a concrete carrier. Its constructor
            // fields and any unboxing remain the data compiler's concern.
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
            self.macro_inline = Some(
                fln_elab::macro_inline::read(self.environment).map_err(|error| match error {
                    fln_elab::macro_inline::MacroInlineError::Limit => {
                        IngressError::MetadataResourceExhausted {
                            kind: "native macro_inline journal capacity",
                        }
                    }
                    _ => unsupported("malformed native macro_inline journal"),
                })?,
            );
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
